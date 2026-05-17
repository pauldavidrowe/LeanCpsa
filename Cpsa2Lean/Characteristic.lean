/-
Cpsa2Lean.Characteristic

Port of CPSA.Characteristic (MITRE cpsa v4.4.8).
Makes the characteristic skeleton of a security goal.
-/

import Cpsa2Lean.Algebra
import Cpsa2Lean.Protocol
import Cpsa2Lean.Operation
import Cpsa2Lean.Strand

namespace Cpsa2Lean.Characteristic

open Cpsa2Lean.Algebra
open Cpsa2Lean.Protocol
open Cpsa2Lean.Operation (Node Pair Sid)
open Cpsa2Lean.Strand
open Cpsa2Lean.Lib (SExpr Pos assertError adjoin)

-- ── Helpers ───────────────────────────────────────────────────────────────────

/-- True when the antecedent formula is an `Equals` atom.
    Mirrors `isEquals :: (Pos, AForm) -> Bool`. -/
private def isEquals : Pos × AForm → Bool
  | (_, .Equals _ _) => true
  | _                => false

/-- True when the formula is an instance formula (Length or Param).
    Mirrors `instForm :: (Pos, AForm) -> Bool`. -/
private def instForm : Pos × AForm → Bool
  | (_, .Length _ _ _)     => true
  | (_, .Param _ _ _ _ _) => true
  | _                      => false

-- ── strdRoleLength ────────────────────────────────────────────────────────────

/-- Compute a map from strand-variable terms to (role, height) pairs.
    Mirrors `strdRoleLength :: MonadFail m => Conj -> m [(Term, (Role, Int))]`. -/
private def strdRoleLength (as_ : Conj) : Except String (List (Term × (Role × Int))) :=
  as_.foldlM (fun srl pa =>
    match pa with
    | (pos, .Length r z ht) =>
        match indxLookup emptyEnv ht with
        | none   => throw s!"{pos}Index is variable, not integer"
        | some h =>
            match srl.lookup z with
            | none           => pure ((z, (r, h)) :: srl)
            | some (r', h')  =>
                if r'.rname != r.rname then
                  throw s!"{pos}Strand occurs in more than one role length atom"
                else if h <= h' then pure srl          -- keep larger height
                else pure ((z, (r, h)) :: srl)         -- shadow with larger
    | _ => pure srl) []

-- ── mkMaplet ─────────────────────────────────────────────────────────────────

/-- Add one maplet to the environment from a Param formula.
    Mirrors `mkMaplet :: MonadFail m => Role -> Term -> (Gen, Env) ->
                         (Pos, AForm) -> m (Gen, Env)`. -/
private def mkMaplet (role : Role) (z : Term) (ge : GenEnv)
    (pa : Pos × AForm) : Except String GenEnv :=
  match pa with
  | (pos, .Param r v _ z' t) =>
      if z == z' then
        if role.rname == r.rname then
          match termMatch v t ge with
          | ge' :: _ => pure ge'
          | []        => throw s!"{pos}Domain does not match range"
        else throw s!"{pos}Role in parameter pred differs from role position pred"
      else pure ge
  | _ => pure ge

-- ── mkInst ───────────────────────────────────────────────────────────────────

/-- Construct one instance from the formulas associated with a strand.
    Mirrors `mkInst :: MonadFail m => Gen -> Conj -> Term -> Role -> Int -> m (Gen, Instance)`. -/
private def mkInst (g : Gen) (as_ : Conj) (z : Term) (r : Role) (h : Int)
    : Except String (Gen × Instance) := do
  let ge ← as_.foldlM (mkMaplet r z) (g, emptyEnv)
  pure (mkInstance ge.1 r ge.2 h)

-- ── foldInsts ────────────────────────────────────────────────────────────────

/-- Construct instances for all (strand, role, height) triples.
    Mirrors `foldInsts :: MonadFail m => Gen -> Conj -> [(Term,(Role,Int))] ->
                          m (Gen, [Instance])`. -/
private def foldInsts (g : Gen) (as_ : Conj) (srl : List (Term × (Role × Int)))
    : Except String (Gen × List Instance) := do
  let (g', insts) ← srl.foldlM (fun (g, insts) (z, (r, h)) => do
    let (g', inst) ← mkInst g as_ z r h
    pure (g', inst :: insts)) (g, [])
  pure (g', insts.reverse)

-- ── mkInsts ───────────────────────────────────────────────────────────────────

/-- Build all instances and the strand→Sid map.
    Mirrors `mkInsts :: MonadFail m => Gen -> Conj -> m ([(Term,Sid)], Gen, [Instance])`. -/
private def mkInsts (g : Gen) (as_ : Conj)
    : Except String (List (Term × Sid) × Gen × List Instance) := do
  let srl         ← strdRoleLength as_
  let (g', insts) ← foldInsts g as_ srl
  -- Build strand map: pair each strand-variable with its position index.
  let strdMap     := (srl.map Prod.fst).zip (List.range srl.length |>.map Int.ofNat)
  pure (strdMap, g', insts)

-- ── nMapLookup ───────────────────────────────────────────────────────────────

/-- Look up a concrete node from the strand map.
    Mirrors `nMapLookup :: NodeTerm -> [(Term, Sid)] -> Node`. -/
private def nMapLookup (n : NodeTerm) (nmap : List (Term × Sid)) : Node :=
  match nmap.lookup n.1, indxLookup emptyEnv n.2 with
  | some s, some i => (s, i)
  | none,   _      => assertError "Characteristic.nMapLookup: Bad lookup"
  | _,      none   => assertError "Characteristic.nMapLookup: Bad height term"

-- ── addInstOrigs ─────────────────────────────────────────────────────────────

/-- Collect origination data inherited from all instances.
    Mirrors `addInstOrigs`. -/
private def addInstOrigs
    (acc : List Term × List Term × List Term × List Term ×
           List Term × List Term × List (Term × Term))
    (i : Instance)
    : List Term × List Term × List Term × List Term ×
      List Term × List Term × List (Term × Term) :=
  let (nr, ar, ur, ug, cf, au, ab) := acc
  ((inheritRnon i).foldl    (fun xs x => adjoin x xs) nr,
   (inheritRpnon i).foldl   (fun xs x => adjoin x xs) ar,
   (inheritRunique i).foldl  (fun xs x => adjoin x xs) ur,
   (inheritRuniqgen i).foldl (fun xs x => adjoin x xs) ug,
   (inheritRconf i).foldl    (fun xs x => adjoin x xs) cf,
   (inheritRauth i).foldl    (fun xs x => adjoin x xs) au,
   (inheritRabsent i).foldl  (fun xs x => adjoin x xs) ab)

-- ── mk* folding helpers ───────────────────────────────────────────────────────

/-- Extract ordering pairs from the antecedent.
    Mirrors `mkPrec`. -/
private def mkPrec (nmap : List (Term × Sid)) (pa : Pos × AForm) (o : List Pair) : List Pair :=
  match pa with
  | (_, .Prec n n') => (nMapLookup n nmap, nMapLookup n' nmap) :: o
  | _               => o

/-- Extract non-origination terms.  Mirrors `mkNon`. -/
private def mkNon (pa : Pos × AForm) (ts : List Term) : List Term :=
  match pa with
  | (_, .Non t) => t :: ts
  | _           => ts

/-- Extract pen-non-origination terms.  Mirrors `mkPnon`. -/
private def mkPnon (pa : Pos × AForm) (ts : List Term) : List Term :=
  match pa with
  | (_, .Pnon t) => t :: ts
  | _            => ts

/-- Extract unique-origination terms.  Mirrors `mkUniq`. -/
private def mkUniq (pa : Pos × AForm) (ts : List Term) : List Term :=
  match pa with
  | (_, .Uniq t)     => t :: ts
  | (_, .UniqAt t _) => t :: ts
  | _                => ts

/-- Extract unique-generation terms.  Mirrors `mkUgen`. -/
private def mkUgen (pa : Pos × AForm) (ts : List Term) : List Term :=
  match pa with
  | (_, .Ugen t)     => t :: ts
  | (_, .UgenAt t _) => t :: ts
  | _                => ts

/-- Extract gen-state terms.  Mirrors `mkGenSt`. -/
private def mkGenSt (pa : Pos × AForm) (ts : List Term) : List Term :=
  match pa with
  | (_, .GenStV t) => t :: ts
  | _              => ts

/-- Extract conf terms.  Mirrors `mkConf`. -/
private def mkConf (pa : Pos × AForm) (ts : List Term) : List Term :=
  match pa with
  | (_, .Conf t) => t :: ts
  | _            => ts

/-- Extract auth terms.  Mirrors `mkAuth`. -/
private def mkAuth (pa : Pos × AForm) (ts : List Term) : List Term :=
  match pa with
  | (_, .Auth t) => t :: ts
  | _            => ts

/-- Build facts from AFact formulas.  Mirrors `mkFact`. -/
private def mkFact (nmap : List (Term × Sid)) (pa : Pos × AForm)
    (ts : List Fact) : List Fact :=
  match pa with
  | (_, .AFact name fs) =>
      { name  := name,
        terms := fs.map fun t =>
          match nmap.lookup t with
          | some s => .FSid s
          | none   => .ofTerm t } :: ts
  | _ => ts

-- ── checkUniqAt / checkUgenAt ────────────────────────────────────────────────

/-- Verify that the `UniqAt` constraint is satisfied.
    Mirrors `checkUniqAt`. -/
private def checkUniqAt (nmap : List (Term × Sid)) (k : Preskel)
    (pa : Pos × AForm) : Except String Unit :=
  match pa with
  | (pos, .UniqAt t n) =>
      match k.korig.lookup t with
      | none    => throw s!"{pos}Atom not unique at node"
      | some ns =>
          if ns.contains (nMapLookup n nmap) then pure ()
          else throw s!"{pos}Atom not unique at node"
  | _ => pure ()

/-- Verify that the `UgenAt` constraint is satisfied.
    Mirrors `checkUgenAt`. -/
private def checkUgenAt (nmap : List (Term × Sid)) (k : Preskel)
    (pa : Pos × AForm) : Except String Unit :=
  match pa with
  | (pos, .UgenAt t n) =>
      match k.kugen.lookup t with
      | none    => throw s!"{pos}Atom not uniq gen at node"
      | some ns =>
          if ns.contains (nMapLookup n nmap) then pure ()
          else throw s!"{pos}Atom not uniq gen at node"
  | _ => pure ()

-- ── mkSkel ───────────────────────────────────────────────────────────────────

/-- Assemble the preskeleton from instances and skeleton formulas.
    Mirrors `mkSkel :: MonadFail m => Pos -> Prot -> [Goal] -> [(Term,Sid)] ->
                       Gen -> [Instance] -> Conj -> [SExpr ()] -> m Preskel`. -/
private def mkSkel (pos : Pos) (p : Prot) (goals : List Goal)
    (nmap : List (Term × Sid)) (g : Gen) (insts : List Instance)
    (as_ : Conj) (comment : List (SExpr Unit)) : Except String Preskel := do
  let o   := as_.foldr (mkPrec nmap) []
  let nr  := as_.foldr mkNon  []
  let ar  := as_.foldr mkPnon []
  let ur  := as_.foldr mkUniq []
  let ug  := as_.foldr mkUgen []
  let gs  := as_.foldr mkGenSt []
  let cf  := as_.foldr mkConf []
  let au  := as_.foldr mkAuth []
  let (nr', ar', ur', ug', cf', au', ab') :=
        insts.foldl addInstOrigs (nr, ar, ur, ug, cf, au, [])
  let fs  := as_.foldr (mkFact nmap) []
  let k   := mkPreskel g p goals insts o nr' ar' ur' ug' ab' []
               gs cf' au' fs [] comment
  as_.forM (checkUniqAt nmap k)
  as_.forM (checkUgenAt nmap k)
  if !termsWellFormed (nr' ++ ar' ++ ur' ++ ug' ++ kterms k) then
    throw s!"{pos}Terms in skeleton not well formed"
  match verbosePreskelWellFormed k with
  | .ok ()   => pure k
  | .error msg => throw s!"{pos}Skeleton not well formed: {msg}"

-- ── splitForm ────────────────────────────────────────────────────────────────

/-- Split antecedent into instance formulas and skeleton formulas, then build.
    Mirrors `splitForm`. -/
private def splitForm (pos : Pos) (prot : Prot) (goals : List Goal) (g : Gen)
    (as_ : Conj) (comment : List (SExpr Unit)) : Except String Preskel := do
  let (is, ks) := as_.partition instForm
  let (nmap, g', insts) ← mkInsts g is
  mkSkel pos prot goals nmap g' insts ks comment

-- ── characteristic ───────────────────────────────────────────────────────────

/-- Entry point: build the characteristic preskeleton of a security goal.
    Mirrors `characteristic :: MonadFail m => Pos -> Prot -> [Goal] -> Gen ->
                               Conj -> [SExpr ()] -> m Preskel`. -/
def characteristic (pos : Pos) (prot : Prot) (goals : List Goal) (g : Gen)
    (antec : Conj) (comment : List (SExpr Unit)) : Except String Preskel :=
  if antec.any isEquals then
    throw s!"{pos}Equals not allowed in antecedent"
  else
    splitForm pos prot goals g antec comment

end Cpsa2Lean.Characteristic
