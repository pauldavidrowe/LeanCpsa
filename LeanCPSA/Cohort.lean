/-
LeanCPSA.Cohort

Port of CPSA.Cohort (MITRE cpsa).

Copyright (c) 2026 Paul D. Rowe

Computes the cohort associated with a skeleton or its generalization.

Copyright (c) 2009 The MITRE Corporation

This program is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.
-/

import LeanCPSA.Algebra
import LeanCPSA.Channel
import LeanCPSA.Protocol
import LeanCPSA.Operation
import LeanCPSA.Strand

namespace LeanCPSA.Cohort

open LeanCPSA.Algebra
open LeanCPSA.Channel
open LeanCPSA.Protocol
open LeanCPSA.Operation (Direction Cause Node Pair Sid getStrandMap)
open LeanCPSA.Strand
open LeanCPSA.Lib (RBSet assertError adjoin)

-- ── Compile-time flags ────────────────────────────────────────────────────────

/-- Include the escape set in the set of target terms. -/
private def useEscapeSetInTargetTerms : Bool := false

/-- Filter a cohort for skeletons that solve the test. -/
private def useSolvedFilter : Bool := true

/-- Use thinning during generalization. -/
private def useThinningDuringGeneralization : Bool := false

/-- A sanity check for cohort members, normally left off. -/
private def usePovCheck : Bool := true

/-- Minimum priority to solve. -/
private def minPriority : Int := 1

-- ── Set helpers ───────────────────────────────────────────────────────────────

/-- Set difference for `RBSet`. -/
private def rbDifference {α : Type} [Ord α] (s1 s2 : RBSet α) : RBSet α :=
  RBSet.fold (fun x acc => if RBSet.member x s2 then acc else RBSet.insert x acc)
    RBSet.empty s1

/-- True when the `RBSet` is empty. -/
private def rbNull {α : Type} [Ord α] (s : RBSet α) : Bool :=
  (RBSet.toList s).isEmpty

/-- Remove pairs with the same second element (`Subst`).
    Mirrors `nubSnd :: Eq b => [(a, b)] -> [(a, b)]`. -/
private def nubSnd {α : Type} (substs : List (α × Subst)) : List (α × Subst) :=
  substs.foldl (fun acc p =>
    if acc.any (fun q => q.2 == p.2) then acc else acc ++ [p]) []

-- ── Graph vertex helpers ───────────────────────────────────────────────────────

/-- Collect sending vertices before `v` (those reachable via `preds` that send).
    Mirrors `addSendingBefore :: Set Vertex -> Vertex -> Set Vertex`.
    Uses `RBSet Node` (keyed by `(strandId, pos)`) in place of `Set Vertex`. -/
partial def addSendingBefore (k : Preskel) (s : RBSet Node) (v : GraphNode) : RBSet Node :=
  v.preds.foldl (fun s predNode =>
    if RBSet.member predNode s then s
    else
      let pred := vertex k predNode
      let s' := match outbnd pred.event with
                | some _ => RBSet.insert predNode s
                | none   => s
      addSendingBefore k s' pred) s

/-- Channel messages at all nodes in `ns`.
    Mirrors `cmsInNodes :: Set Vertex -> Set ChMsg`. -/
def cmsInNodes (k : Preskel) (ns : RBSet Node) : RBSet ChMsg :=
  RBSet.fold (fun n acc => RBSet.insert (evtCm (vertex k n).event) acc) RBSet.empty ns

/-- Public messages at nodes in `ns` (excludes confidential channels).
    Mirrors `termsInNodes :: Preskel -> Set Vertex -> Set Term`. -/
def termsInNodes (k : Preskel) (ns : RBSet Node) : TermSet :=
  RBSet.map cmTerm (RBSet.filter (fun cm => !confCm k cm) (cmsInNodes k ns))

/-- Confidential channel messages at nodes in `ns`.
    Mirrors `confsInNodes :: Preskel -> Set Vertex -> Set ChMsg`. -/
def confsInNodes (k : Preskel) (ns : RBSet Node) : RBSet ChMsg :=
  RBSet.filter (fun cm => confCm k cm) (cmsInNodes k ns)

-- ── avoid ─────────────────────────────────────────────────────────────────────

/-- Atoms that cannot be guessed, and uniquely originating/generating terms.
    Mirrors `avoid :: Preskel -> (Set Term, [Term])`. -/
def avoid (k : Preskel) : TermSet × List Term :=
  let p := k.kpnon
  let u := uniqOrig k
  let g := uniqGen k
  (RBSet.fromList (k.knon ++ p ++ u ++ g), (p ++ u ++ g).eraseDups)

-- ── derivable ─────────────────────────────────────────────────────────────────

/-- Penetrator derivable predicate.
    Mirrors `derivable :: Set Term -> Set Term -> Term -> Bool`. -/
def derivable (avoid_ sent : TermSet) (term : Term) : Bool :=
  let (knowns, unknowns) := decompose sent avoid_
  buildable knowns unknowns term

-- ── unrealized ────────────────────────────────────────────────────────────────

/-- Nodes in the preskeleton that are not realized.
    Mirrors `unrealized :: Preskel -> [Node]`. -/
def unrealized (k : Preskel) : List Node :=
  let (a, _) := avoid k
  k.strands.foldl (fun acc s =>
    (s.nodes.foldl (fun (pair : List Node × RBSet Node) v =>
      let (acc', ns) := pair
      match inbnd v.event with
      | none   => (acc', ns)
      | some t =>
        let ns' := addSendingBefore k ns v
        let ts  := termsInNodes k ns'
        if RBSet.member t (cmsInNodes k ns') then
          (acc', ns')
        else if authCm k t then
          (graphNode v :: acc', ns')
        else if derivable a ts (cmTerm t) then
          (acc', ns')
        else
          (graphNode v :: acc', ns')) (acc, RBSet.empty)).1) []

-- ── excludeConf ───────────────────────────────────────────────────────────────

/-- Map `CMT` set to `Term` set, excluding confidential channel messages.
    Mirrors `excludeConf :: Preskel -> Set CMT -> Set Term`. -/
private def excludeConf (k : Preskel) (cm : RBSet CMT) : TermSet :=
  RBSet.map cmtTerm (RBSet.filter (fun cmt =>
    match cmt with
    | .CM c => !confCm k c
    | .TM _ => true) cm)

-- ── isAncestorInSet / carriedOnlyWithin ──────────────────────────────────────

/-- True when some ancestor of `source` at `position` is in `set`.
    Mirrors `isAncestorInSet :: Set CMT -> ChMsg -> Place -> Bool`. -/
def isAncestorInSet (set : RBSet CMT) (source : ChMsg) (position : Place) : Bool :=
  (cmtAncestors source position).any (fun a => RBSet.member a set)

/-- True when `target` is carried only within `escape` in `source`.
    Mirrors `carriedOnlyWithin :: CMT -> Set CMT -> ChMsg -> Bool`. -/
def carriedOnlyWithin (target : CMT) (escape : RBSet CMT) (source : ChMsg) : Bool :=
  (cmtCarriedPlaces target source).all (isAncestorInSet escape source)

-- ── targetTerms ───────────────────────────────────────────────────────────────

/-- Terms considered for binding with carried terms in an outbound term.
    Mirrors `targetTerms :: CMT -> Set CMT -> Set CMT`. -/
def targetTerms (ct : CMT) (escape : RBSet CMT) : RBSet CMT :=
  let f (cmt : CMT) (ts : RBSet CMT) : RBSet CMT :=
    match cmt with
    | .CM t =>
        ((cmtCarriedPlaces ct t).flatMap (cmtAncestors t)).foldl
          (fun acc a => RBSet.insert a acc) ts
    | .TM t =>
        match ct with
        | .CM _ => ts
        | .TM ct' =>
            ((carriedPlaces ct' t).flatMap (ancestors t)).foldl
              (fun acc a => RBSet.insert (.TM a) acc) ts
  let targetTermsWithEscape := RBSet.fold f (RBSet.singleton ct) escape
  if useEscapeSetInTargetTerms then targetTermsWithEscape
  else rbDifference targetTermsWithEscape escape

-- ── solved / maybeSolved / povCheck ──────────────────────────────────────────

/-- Test whether a position is solved in a child skeleton.
    Mirrors `solved :: CMT -> Place -> [Term] -> Set CMT ->
               Preskel -> Node -> Subst -> [(Term,Term)] -> Bool`. -/
def solved (ct : CMT) (pos : Place) (eks : List Term) (escape : RBSet CMT)
    (k : Preskel) (n : Node) (subst : Subst) (absent : List (Term × Term)) : Bool :=
  let v       := vertex k n
  let t       := evtCm v.event
  let ct'     := cmtSubstitute subst ct
  let escape' := RBSet.map (cmtSubstitute subst) escape
  let mappedTargetTerms := RBSet.map (cmtSubstitute subst) (targetTerms ct escape)
  let targetTermsDiff   := rbDifference (targetTerms ct' escape') mappedTargetTerms
  let vs      := addSendingBefore k RBSet.empty v
  let ts      := termsInNodes k vs
  let (a, _)  := avoid k
  let encs    := RBSet.fold (fun cmt acc =>
    match cmt with
    | .TM t_ => RBSet.insert t_ acc
    | .CM _  => acc) RBSet.empty escape'
  -- Condition 1
  isAncestorInSet escape' t pos ||
  -- Condition 1a (DH)
  derivable a (excludeConf k escape') (cmtTerm ct') ||
  -- Condition 2
  (RBSet.toList (cmsInNodes k vs)).any (fun cm => !carriedOnlyWithin ct' escape' cm) ||
  -- Condition 3
  (!k.shared.prot.varsAllAtoms && !rbNull targetTermsDiff) ||
  -- Condition 4
  (RBSet.toList encs).any (fun e =>
    match decryptionKey e with
    | some dk => derivable a ts dk
    | none    => false) ||
  -- Condition 5
  eks.any (fun ek => derivable a ts (substitute subst ek)) ||
  -- Condition 6
  derivable a ts (cmtTerm ct') ||
  -- Condition 7
  k.kabsent.length > absent.length

/-- Sanity check: a cohort member should refine the skeleton's point of view.
    Mirrors `povCheck :: Preskel -> Bool`. -/
private def povCheck (k : Preskel) : Bool :=
  match k.pov with
  | none     => true
  | some k0  => !(homomorphism k0 k k.prob).isEmpty

/-- `solved` gated by the `useSolvedFilter` and `usePovCheck` flags.
    Mirrors `maybeSolved`. -/
def maybeSolved (ct : CMT) (pos : Place) (eks : List Term) (escape : RBSet CMT)
    (k : Preskel) (n : Node) (subst : Subst) (absent : List (Term × Term)) : Bool :=
  !useSolvedFilter ||
  (solved ct pos eks escape k n subst absent && (!usePovCheck || povCheck k))

-- ── Mode / ReduceRes ──────────────────────────────────────────────────────────

/-- Mode flags controlling the search order.
    Mirrors `data Mode = Mode { noGeneralization, nonceFirstOrder,
                                visitOldStrandsFirst, reverseNodeOrder }`. -/
structure Mode where
  noGeneralization     : Bool
  nonceFirstOrder      : Bool
  visitOldStrandsFirst : Bool
  reverseNodeOrder     : Bool
  deriving Repr

/-- Result of a reduction step.
    Mirrors `data ReduceRes = Stable | Crt [Preskel] | Gnl [Preskel]`. -/
inductive ReduceRes where
  | Stable : ReduceRes
  | Crt    : List Preskel → ReduceRes
  | Gnl    : List Preskel → ReduceRes

-- ── priority / nodeOrder ──────────────────────────────────────────────────────

/-- Priority of node `n` in preskeleton `k`.
    Mirrors `priority :: Preskel -> Node -> Int`. -/
def priority (k : Preskel) (n : Node) : Int :=
  match k.kpriority.lookup n with
  | some p => p
  | none   =>
    let inst := k.insts.getD n.1.toNat default
    (inst.role.rpriority.getD n.2.toNat 0 : Int)

/-- Order strands for visiting.
    Mirrors `strandVisitOrder :: Mode -> [a] -> [a]`. -/
private def strandVisitOrder (mode : Mode) (ss : List GraphStrand) : List GraphStrand :=
  if mode.visitOldStrandsFirst then ss else ss.reverse

/-- Order nodes within a strand for visiting.
    Mirrors `nodeVisitOrder :: Mode -> Strand -> [Vertex]`. -/
private def nodeVisitOrder (mode : Mode) (s : GraphStrand) : List GraphNode :=
  if mode.reverseNodeOrder == s.inst.role.rsearch then s.nodes
  else s.nodes.reverse

/-- All vertices in visit order.
    Mirrors `nodeOrder :: Mode -> Preskel -> [Vertex]`. -/
private def nodeOrder (mode : Mode) (k : Preskel) : List GraphNode :=
  (strandVisitOrder mode k.strands).flatMap (nodeVisitOrder mode)

/-- Sort vertices by descending priority, filtering out those below `minPriority`.
    Mirrors `prioritizeVertices :: Preskel -> [Vertex] -> [Vertex]`. -/
private def prioritizeVertices (k : Preskel) (vs : List GraphNode) : List GraphNode :=
  let paired := vs.map fun v => (v, priority k (v.strandId, v.pos))
  let sorted := paired.mergeSort fun a b => a.2 >= b.2
  (sorted.filter fun p => p.2 >= minPriority).map Prod.fst

-- ── mgs / composeFactors / perms ─────────────────────────────────────────────

/-- Generate permutations that factor `p` through `p'`.
    Mirrors `perms :: [(Int,Int)] -> [Int] -> [Int] -> [[Int]]`. -/
partial def perms (alist : List (Int × Int)) (range : List Int) : List Int → List (List Int)
  | []           => [[]]
  | s :: domain  =>
    match alist.lookup s with
    | some s' => (perms alist range domain).map (s' :: ·)
    | none    => range.flatMap fun s' => (perms alist range domain).map (s' :: ·)

/-- Permutations `p''` such that `p'' ∘ p' = p`, filtered to injective ones.
    Mirrors `composeFactors :: [Int] -> [Int] -> [Int] -> [Int] -> [[Int]]`. -/
def composeFactors (r r' p p' : List Int) : List (List Int) :=
  (perms (p'.zip p) r r').filter fun phi => phi.eraseDups == phi

/-- Keep only the most-general skeletons in a cohort.
    Mirrors `mgs :: [(Preskel, [Sid])] -> [Preskel]`. -/
def mgs (cohort : List (Preskel × List Sid)) : List Preskel :=
  let dominated (kphi : Preskel × List Sid) (others : List (Preskel × List Sid)) : Bool :=
    others.any fun (k', phi') =>
      (composeFactors kphi.1.strandids k'.strandids kphi.2 phi').any fun perm =>
        !(homomorphism k' kphi.1 perm).isEmpty
  let rec loop : List (Preskel × List Sid) → List (Preskel × List Sid) →
                 List (Preskel × List Sid)
    | [], acc            => acc
    | kphi :: rest, acc  =>
      if dominated kphi rest || dominated kphi acc then loop rest acc
      else loop rest (kphi :: acc)
  (loop cohort []).reverse.map fun (k, phi) => updateStrandMap phi k

-- ── Critical-term helpers ─────────────────────────────────────────────────────

/-- Potential critical messages at term `t`.
    Mirrors `potentialCriticalMessages`. -/
private def potentialCriticalMessages (mode : Mode) (u : List Term) (ts a : TermSet)
    (t : Term) : List (Term × List Term) :=
  let fnum (nums : List (Term × List Term)) (t' : Term) : List (Term × List Term) :=
    if isNum t' && !buildable ts a t' then nums ++ [(t', [])] else nums
  let nonces : List (Term × List Term) :=
    (u.filter (fun ct => carriedBy ct t)).map (fun ct => (ct, [])) ++
    foldCarriedTerms fnum [] t
  let encs : List (Term × List Term) :=
    (encryptions t).map (fun (ct, eks) => (ct, eks.filter (fun ek => !buildable ts a ek)))
      |>.filter (fun p => !p.2.isEmpty)
  if mode.nonceFirstOrder then nonces ++ encs else encs ++ nonces

-- ── solve helpers ─────────────────────────────────────────────────────────────

/-- Enumerate matching (gen, subst) pairs from the escape set and ancestors.
    Mirrors `solve :: Set CMT -> [CMT] -> (Gen, Subst) -> [(Gen, Subst)]`. -/
private def solveCMTs (escape : RBSet CMT) (ancs : List CMT) (gs : GenSubst) : List GenSubst :=
  (RBSet.toList escape).flatMap fun e =>
    ancs.flatMap fun a =>
      cmtUnify a e gs

/-- Unify `cmtTerm ct` with each constant of the same sort.
    Mirrors `constSolve :: (Gen, Subst) -> CMT -> [(Gen, Subst)]`. -/
private def constSolve (gs : GenSubst) (ct : CMT) : List GenSubst :=
  (consts (cmtTerm ct)).flatMap fun c =>
    unify (cmtTerm ct) c gs

/-- Direction: `Nonce` if no encryption keys, else `Encryption`.
    Mirrors `dir :: [a] -> Direction`. -/
private def dir {α : Type} (xs : List α) : Direction :=
  if xs.isEmpty then .Nonce else .Encryption

/-- Apply a substitution to both sides and check carried-only-within.
    Mirrors `carriedOnlyWithinAtSubst`. -/
private def carriedOnlyWithinAtSubst (ct : CMT) (escape : RBSet CMT) (t : ChMsg)
    (gs : GenSubst) : Bool :=
  let ct'     := cmtSubstitute gs.2 ct
  let escape' := RBSet.map (cmtSubstitute gs.2) escape
  let t'      := cmSubstitute gs.2 t
  carriedOnlyWithin ct' escape' t'

/-- Refine substitutions so that `ct` is carried only within `escape` in `t`.
    Mirrors `fold :: CMT -> Set CMT -> ChMsg -> (Gen, Subst) -> [(Gen, Subst)]`. -/
private def foldSubst (ct : CMT) (escape : RBSet CMT) (t : ChMsg) (gs : GenSubst) : List GenSubst :=
  let ct'     := cmtSubstitute gs.2 ct
  let escape' := RBSet.map (cmtSubstitute gs.2) escape
  let t'      := cmSubstitute gs.2 t
  let result  := (cmtCarriedPlaces ct' t').foldl (fun acc p =>
    acc.flatMap fun gs' => solveCMTs escape' (cmtAncestors t' p) gs')
    [(gs.1, emptySubst)]
  result.map fun (gen', subst') => (gen', compose subst' gs.2)

/-- Apply fold to each message in the trace.
    Mirrors `foldn :: CMT -> Set CMT -> Trace -> [(Gen, Subst)] -> [(Gen, Subst)]`. -/
private def foldn (ct : CMT) (escape : RBSet CMT) : Trace → List GenSubst → List GenSubst
  | [], substs        => substs
  | evt :: c, substs  =>
    foldn ct escape c (substs.flatMap (foldSubst ct escape (evtCm evt)))

-- ── cowt ─────────────────────────────────────────────────────────────────────

/-- Ensure `ct` is carried only within `escape` for every trace event, and
    refine substitutions accordingly.
    Mirrors `cowt` / `cowt0` from the Haskell source.
    `cowt0` is inlined as a local helper so no mutual block is needed. -/
private partial def cowt (ct : CMT) (escape : RBSet CMT) (c : Trace)
    (substs : List GenSubst) : List GenSubst :=
  let cowt0 (gs : GenSubst) : List GenSubst :=
    if c.all (fun evt => carriedOnlyWithinAtSubst ct escape (evtCm evt) gs) then [gs]
    else cowt ct escape c (foldn ct escape c [gs])
  nubSnd (substs.flatMap cowt0)

-- ── targetTerms / carriedBindings / maybeAug ─────────────────────────────────

/-- Bindings from carried subterms of `outbound` to target terms.
    Mirrors `carriedBindings :: [CMT] -> ChMsg -> (Gen, Subst) -> [(Gen, Subst)]`. -/
private def carriedBindings (targets : List CMT) (outbound : ChMsg) (gs : GenSubst) : List GenSubst :=
  let subterms := cmFoldCarriedTerms (fun acc x => RBSet.insert x acc) RBSet.empty outbound
  (RBSet.toList subterms).flatMap fun subterm =>
    targets.flatMap fun target =>
      cmtUnify subterm target gs

/-- If the outbound term is not carried only within escape, add a candidate
    augmentation to the accumulator.
    Mirrors `maybeAug`. -/
private def maybeAug (ct : CMT) (escape : RBSet CMT) (role : Role) (ht : Nat)
    (substs : List GenSubst) (acc : List (GenSubst × Instance)) (t : ChMsg)
    : List (GenSubst × Instance) :=
  substs.foldl (fun acc gs =>
    if carriedOnlyWithin (cmtSubstitute gs.2 ct)
         (RBSet.map (cmtSubstitute gs.2) escape)
         (cmSubstitute gs.2 t) then acc
    else
      let itrace := (role.rtrace.take ht).map (evtMap (substitute gs.2))
      match bldInstance role itrace gs.1 with
      | (gen, inst) :: _ => ((gen, gs.2), inst) :: acc
      | []               => acc) acc

-- ── transformingNode / cloneRoleVars ─────────────────────────────────────────

/-- Build a fresh set of role variables by cloning.
    Mirrors `cloneRoleVars :: Gen -> Role -> (Gen, Subst)`. -/
private def cloneRoleVars (gen : Gen) (role : Role) : GenSubst :=
  let rec grow : List Term → Gen → Env → GenSubst
    | [], g, env      => (g, substitution env)
    | t :: ts, g, env =>
      let (g', t') := clone g t
      match termMatch t t' (g', env) with
      | (g'', env') :: _ => grow ts g'' env'
      | []               => assertError "Cohort.cloneRoleVars: Internal error"
  grow role.rvars gen emptyEnv

/-- Find role positions that transform `ct` outside `escape`.
    Mirrors `transformingNode`. -/
private def transformingNode (ct : CMT) (escape : RBSet CMT) (targets : List CMT)
    (role : Role) (gs : GenSubst) : List (GenSubst × Instance) :=
  let rec loop (ht : Nat) (past : Trace) (acc : List (GenSubst × Instance))
      : Trace → List (GenSubst × Instance)
    | []              => acc
    | .In t :: c      => loop (ht + 1) (.In t :: past) acc c
    | .Out t :: c     =>
      let substs  := carriedBindings targets t gs
      let substs' := cowt ct escape past substs
      let acc'    := maybeAug ct escape role (ht + 1) substs' acc t
      loop (ht + 1) (.Out t :: past) acc' c
  loop 0 [] [] role.rtrace

-- ── augmentations ────────────────────────────────────────────────────────────

/-- Per-role augmentations.
    Mirrors `roleAugs`. -/
private def roleAugs (k : Preskel) (ct : CMT) (pos : Place) (eks : List Term) (n : Node)
    (escape : RBSet CMT) (cause : Cause) (targets : List CMT) (role : Role)
    : List (Preskel × List Sid) :=
  let gs := cloneRoleVars k.gen role
  (transformingNode ct escape targets role gs).flatMap fun (gs', inst) =>
    (augment k n cause role gs' inst).flatMap fun (k', n', phi, subst') =>
      if maybeSolved ct pos eks escape k' n' subst' k.kabsent then [(k', phi)] else []

/-- All role augmentations for the critical term.
    Mirrors `augmentations`. -/
private def augmentations (k : Preskel) (ct : CMT) (pos : Place) (eks : List Term) (n : Node)
    (escape : RBSet CMT) (cause : Cause) : List (Preskel × List Sid) :=
  let targets := RBSet.toList (targetTerms ct escape)
  k.shared.prot.roles.flatMap (roleAugs k ct pos eks n escape cause targets)

-- ── contractions ─────────────────────────────────────────────────────────────

/-- Contractions: apply a unifying substitution and contract.
    Mirrors `contractions`. -/
private def contractions (k : Preskel) (ct : CMT) (pos : Place) (eks : List Term) (n : Node)
    (t : ChMsg) (escape : RBSet CMT) (cause : Cause) : List (Preskel × List Sid) :=
  let anc    := cmtAncestors t pos
  let substs := solveCMTs escape anc (k.gen, emptySubst) ++
                constSolve (k.gen, emptySubst) ct
  substs.flatMap fun gs =>
    (contract k n cause gs).flatMap fun (k', n', phi, subst') =>
      if maybeSolved ct pos eks escape k' n' subst' k.kabsent then [(k', phi)] else []

-- ── escapeKeys / addListeners ─────────────────────────────────────────────────

/-- Decryption keys for escape-set members plus the given eks.
    Mirrors `escapeKeys :: [Term] -> Set CMT -> Set Term`. -/
private def escapeKeys (eks : List Term) (escape : RBSet CMT) : TermSet :=
  RBSet.fold (fun cmt acc =>
    match cmt with
    | .TM e => match decryptionKey e with
               | some dk => RBSet.insert dk acc
               | none    => acc
    | .CM _ => acc)
    (RBSet.fromList eks) escape

/-- Listener augmentations for keys in the escape set.
    Mirrors `addListeners`. -/
private def addListeners (k : Preskel) (ct : CMT) (pos : Place) (eks : List Term) (n : Node)
    (t : ChMsg) (escape : RBSet CMT) (cause : Cause) : List (Preskel × List Sid) :=
  let keys := RBSet.toList (escapeKeys eks escape)
  (keys.filter fun t' =>
    match t with
    | .ChMsg _ _ _ => true
    | .Plain tP  => tP != t').flatMap fun t' =>
    (addListener k n cause t').flatMap fun (k', n', phi, subst') =>
      if maybeSolved ct pos eks escape k' n' subst' k.kabsent then [(k', phi)] else []

-- ── DH subcohort ─────────────────────────────────────────────────────────────

/-- Base DH subcohort.
    Mirrors `baseDHSubcohort`. -/
private def baseDHSubcohort (k : Preskel) (ct : CMT) (pos : Place) (eks : List Term) (n : Node)
    (escape : RBSet CMT) (cause : Cause) : List (Preskel × List Sid) :=
  if k.kprecur.contains n then []
  else
    (addBaseListener k n cause (cmtTerm ct)).flatMap fun (k', n', phi, subst') =>
      if maybeSolved ct pos eks escape k' n' subst' k.kabsent then [(k', phi)] else []

/-- Expression DH subcohort.
    Mirrors `exprDHSubcohort`. -/
private def exprDHSubcohort (k : Preskel) (a : TermSet) (ct : CMT) (pos : Place)
    (eks : List Term) (n : Node) (escape : RBSet CMT) (cause : Cause)
    : List (Preskel × List Sid) :=
  if isRndx (cmtTerm ct) then []
  else
    (exprVars (cmtTerm ct)).flatMap fun x =>
      if !RBSet.member x a then []
      else
        (addAbsence k n cause x (cmtTerm ct)).flatMap (fun (k', n', phi, subst') =>
          if maybeSolved ct pos eks escape k' n' subst' k.kabsent then [(k', phi)] else []) ++
        (addListener k n cause x).flatMap (fun (k', n', phi, subst') =>
          if maybeSolved ct pos eks escape k' n' subst' k.kabsent then [(k', phi)] else [])

/-- DH subcohort dispatcher.
    Mirrors `theDHSubcohort`. -/
private def theDHSubcohort (k : Preskel) (a : TermSet) (ct : CMT) (pos : Place)
    (eks : List Term) (n : Node) (escape : RBSet CMT) (cause : Cause)
    : List (Preskel × List Sid) :=
  if isBase (cmtTerm ct) then baseDHSubcohort k ct pos eks n escape cause
  else if isExpr (cmtTerm ct) then exprDHSubcohort k a ct pos eks n escape cause
  else []

-- ── solveNode / chanSolveNode ─────────────────────────────────────────────────

/-- Solve critical message `ct` at place `pos` at node `n`.
    Mirrors `solveNode`. -/
private def solveNode (k : Preskel) (a : TermSet) (ct : CMT) (pos : Place) (eks : List Term)
    (n : Node) (t : ChMsg) (escape : RBSet CMT) : List Preskel :=
  let cause := ({ direction := dir eks, node := n, cmt := ct, cmts := escape } : Cause)
  mgs (contractions k ct pos eks n t escape cause ++
       augmentations k ct pos eks n escape cause ++
       addListeners k ct pos eks n t escape cause ++
       theDHSubcohort k a ct pos eks n escape cause)

/-- Solve an authenticated channel message (the critical value is the channel message).
    Mirrors `chanSolveNode`. -/
private def chanSolveNode (k : Preskel) (n : Node) (t : ChMsg) : List Preskel :=
  let ct     : CMT        := .CM t
  let pos    : Place      := ⟨[]⟩
  let eks    : List Term  := []
  let escape : RBSet CMT  := RBSet.empty
  let cause  : Cause      := { direction := .Channel, node := n, cmt := ct, cmts := escape }
  mgs (augmentations k ct pos eks n escape cause)

-- ── testNode / findTest ───────────────────────────────────────────────────────

/-- Look for a critical term that makes this node a test node.
    Mirrors `testNode`. -/
private def testNode (mode : Mode) (k : Preskel) (u : List Term) (cms : RBSet ChMsg)
    (ts a : TermSet) (n : Node) (cm : ChMsg) : List Preskel :=
  let rec loop : List (Term × List Term) → List Preskel
    | []               =>
      assertError s!"Cohort.testNode: missing test at node {n.1},{n.2}"
    | (ct, eks) :: cts =>
      match escapeSet ts a ct with
      | none     => loop cts
      | some esc =>
        let escapeTM := RBSet.map (fun t => CMT.TM t) esc
        let escapeCM := RBSet.map (fun c => CMT.CM c)
                          (RBSet.filter (fun c => carriedBy ct (cmTerm c)) cms)
        let escape   := RBSet.unions [escapeTM, escapeCM]
        let places   := cmtCarriedPlaces (.TM ct) cm
        let rec placesLoop : List Place → List Preskel
          | []      => loop cts
          | p :: ps =>
            if isAncestorInSet escape cm p then placesLoop ps
            else solveNode k a (.TM ct) p eks n cm escape
        placesLoop places
  loop (potentialCriticalMessages mode u ts a (cmTerm cm))

/-- Find a test node and return the cohort for it, or `none` if all nodes are realized.
    Mirrors `findTest :: Mode -> Preskel -> [Term] -> Set Term -> Maybe [Preskel]`. -/
private def findTest (mode : Mode) (k : Preskel) (u : List Term) (a : TermSet)
    : Option (List Preskel) :=
  let rec loop : List GraphNode → Option (List Preskel)
    | []         => none
    | v :: rest  =>
      match inbnd v.event with
      | none   => loop rest
      | some t =>
        let ns  := addSendingBefore k RBSet.empty v
        let ts  := termsInNodes k ns
        let cms := confsInNodes k ns
        let (ts', a') := decompose ts a
        if RBSet.member t (cmsInNodes k ns) then loop rest
        else if authCm k t then
          some (chanSolveNode k (graphNode v) t)
        else if buildable ts' a' (cmTerm t) then loop rest
        else
          some (testNode mode k u cms ts' a' (graphNode v) t)
  loop (prioritizeVertices k (nodeOrder mode k))

-- ── filterSame / specialization / maximize / reduce ──────────────────────────

/-- Filter out skeletons isomorphic to `k`.
    Mirrors `filterSame :: Preskel -> [Preskel] -> [Preskel]`. -/
def filterSame (k : Preskel) (ks : List Preskel) : List Preskel :=
  ks.filter fun k' => !isomorphic (gist k) (gist k')

/-- Test whether realized skeleton `k` is a specialization of `k'` via `mapping`.
    Mirrors `specialization :: Preskel -> Preskel -> [Sid] -> [Preskel]`. -/
def specialization (k k' : Preskel) (mapping : List Sid) : List Preskel :=
  if !preskelWellFormed k' then []
  else
    (toSkeleton useThinningDuringGeneralization k').flatMap fun k'' =>
      let realized : Bool := (unrealized k'').isEmpty
      let refines  : Preskel → Option Preskel → List Sid → Bool
        | _,  none,    _   => assertError "Cohort.specialization: cannot find point of view"
        | k0, some k0', mp => !(homomorphism k0' k0 mp).isEmpty
      if realized && !isomorphic (gist k) (gist k'') &&
         refines k'' k''.pov k''.prob &&
         refines k (some k'') mapping
      then [k'']
      else []

/-- Maximize: find generalization(s) of a realized skeleton.
    Mirrors `maximize :: Preskel -> [Preskel]`. -/
def maximize (k : Preskel) : List Preskel :=
  let candidates := (generalize k).flatMap fun (k', sm) =>
    simplify (updateStrandMap sm k')
  let rec iter : List Preskel → List Preskel
    | []         => []
    | k' :: rest =>
      let mapping := getStrandMap k'.operation
      match specialization k k' mapping with
      | []  => iter rest
      | ks  => ks
  iter candidates

/-- Try to generalize, or return `Stable` if no generalization applies.
    Mirrors `reduceNoTest`. -/
def reduceNoTest (mode : Mode) (k : Preskel) : ReduceRes :=
  if mode.noGeneralization then .Stable
  else
    match maximize k with
    | []  => .Stable
    | ks  => .Gnl ks

/-- One reduction step: find a test node and compute the cohort, or generalize.
    Mirrors `reduce :: Mode -> Preskel -> ReduceRes`. -/
def reduce (mode : Mode) (k : Preskel) : ReduceRes :=
  let (a, u) := avoid k
  match findTest mode k u a with
  | none    => reduceNoTest mode k
  | some ks =>
    .Crt (filterSame k (factorIsomorphicPreskels
      (ks.foldr (fun k' soFar => simplify k' ++ soFar) [])))

end LeanCPSA.Cohort
