/-
LeanCPSA.LoadFormulas

Port of CPSA.LoadFormulas (MITRE cpsa).

Copyright (c) 2026 Paul D. Rowe

Loads formulas from S-expressions as part of the CPSA loader process.

Copyright (c) 2009 The MITRE Corporation

This program is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.
-/

/-
All functions that return `MonadFail m => m a` in Haskell are ported as
`Except String`.  Error messages mirror the Haskell originals using the
`Pos` ToString instance (`s!"{pos}..."`) so position prefixes are preserved.
-/

import LeanCPSA.Algebra
import LeanCPSA.Protocol

namespace LeanCPSA.LoadFormulas

open LeanCPSA.Algebra
open LeanCPSA.Protocol
open LeanCPSA.Signature (Sig)
open LeanCPSA.Lib (SExpr Pos)

-- ── Helpers ───────────────────────────────────────────────────────────────────

/-- Render a term as a display string for use in error messages.
    Mirrors the local `showst :: Term -> ShowS`. -/
private def showTerm (t : Term) : String :=
  toString (displayTerm (addToContext emptyContext [t]) t)

/-- Sort a `Conj` by constructor order of its `AForm` fields.
    Mirrors `L.sortBy (\(_,x) (_,y) -> aFormOrder x y)`.
    Uses the original index as a tiebreaker to make the sort stable,
    matching Haskell's `Data.List.sortBy` which is a stable sort. -/
private def sortConj (c : Conj) : Conj :=
    ((LeanCPSA.Lib.enum c).toArray.qsort (fun (i, (_, x)) (j, (_, y)) =>
    match aFormOrder x y with
    | .lt => true
    | .eq => i < j
    | .gt => false)).toList.map Prod.snd

-- ── Variable construction ──────────────────────────────────────────────────────

/-- Build a list of fresh variables of sort `sortName`, one per name in `names`.
    Mirrors `sortedVarsOfNames :: Sig -> Gen -> String -> [String] -> (Gen, [Term])`. -/
def sortedVarsOfNames (sig : Sig) (g : Gen) (sortName : String)
    (names : List String) : Gen × List Term :=
  names.foldr (fun name (g', vs) =>
    let (g'', v) := newVar sig g' name sortName
    (g'', v :: vs)) (g, [])

/-- Build fresh variables from a `VarListSpec` (list of (sort, names) pairs).
    Mirrors `sortedVarsOfStrings :: Sig -> Gen -> VarListSpec -> (Gen, [Term])`. -/
def sortedVarsOfStrings (sig : Sig) (g : Gen) (spec : VarListSpec) : Gen × List Term :=
  spec.foldr (fun (s, varnames) (g', soFar) =>
    let (g'', vars) := sortedVarsOfNames sig g' s varnames
    (g'', vars ++ soFar)) (g, [])

/-- Collect all variables occurring in `t` (in traversal order).
    Mirrors `varsInTerm :: Term -> [Term]`. -/
def varsInTerm (t : Term) : List Term :=
  foldVars (fun vs v => v :: vs) [] t

-- ── Term loaders ──────────────────────────────────────────────────────────────

/-- Load a list of terms from S-expressions.
    Mirrors `loadTerms :: MonadFail m => Sig -> [Term] -> [SExpr Pos] -> m [Term]`. -/
def loadTerms (sig : Sig) (vars : List Term)
    (xs : List (SExpr Pos)) : Except String (List Term) :=
  xs.mapM (loadTerm sig vars false)

/-- Load a single `(name, [term])` fact.
    Mirrors `loadAFact :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m (String, [Term])`. -/
private def loadAFact (sig : Sig) (vars : List Term)
    (x : SExpr Pos) : Except String (String × List Term) :=
  match x with
  | .lst _ (.sym _ name :: fs) => do
      let fs' ← fs.mapM (loadTerm sig vars false)
      .ok (name, fs')
  | _ => .error s!"{x.annotation}Malformed fact"

/-- Load a list of `(name, [term])` facts.
    Mirrors `loadFactList`. -/
def loadFactList (sig : Sig) (vars : List Term)
    (xs : List (SExpr Pos)) : Except String (List (String × List Term)) :=
  xs.mapM (loadAFact sig vars)

-- ── Role lookup ───────────────────────────────────────────────────────────────

/-- Find a role by name in a protocol.  Empty name returns the listener role.
    Mirrors `lookupRole :: MonadFail m => Pos -> Prot -> String -> m Role`. -/
def lookupRole (pos : Pos) (p : Prot) (role : String) : Except String Role :=
  if role == "" then .ok p.listenerRole
  else
    match p.roles.find? (fun r => role == r.rname) with
    | none   => .error s!"{pos}Role {role} not found in {p.pname}"
    | some r => .ok r

-- ── Mode ──────────────────────────────────────────────────────────────────────

/-- Controls how tightly a conjunction is checked for binding completeness.
    Mirrors `data Mode = RoleSpec | UnusedVars | Liberal`. -/
inductive Mode where
  | RoleSpec  : Mode
  | UnusedVars : Mode
  | Liberal   : Mode

-- ── Typed term loaders ────────────────────────────────────────────────────────

/-- Load a term that must not be of sort strd, indx, locn, or chan.
    Mirrors `loadAlgTerm`. -/
private def loadAlgTerm (sig : Sig) (ts : List Term)
    (x : SExpr Pos) : Except String Term := do
  let t ← loadTerm sig ts false x
  if isStrdVar t || isIndxVar t || isIndxConst t then
    .error s!"{x.annotation}Expecting an algebra term"
  else .ok t

/-- Load a term that must not be of sort strd or indx (channels allowed).
    Mirrors `loadAlgChanTerm`. -/
private def loadAlgChanTerm (sig : Sig) (ts : List Term)
    (x : SExpr Pos) : Except String Term := do
  let t ← loadTerm sig ts false x
  if isStrdVar t || isIndxVar t || isIndxConst t then
    .error s!"{x.annotation}Expecting an algebra term or a channel"
  else .ok t

/-- Load a term that must have sort chan.
    Mirrors `loadChanTerm`. -/
private def loadChanTerm (sig : Sig) (ts : List Term)
    (x : SExpr Pos) : Except String Term := do
  let t ← loadTerm sig ts false x
  if isChan t then .ok t
  else .error s!"{x.annotation}Expecting a channel variable"

/-- Load a term that must have sort strd.
    Mirrors `loadStrdTerm`. -/
private def loadStrdTerm (sig : Sig) (ts : List Term)
    (x : SExpr Pos) : Except String Term := do
  let t ← loadTerm sig ts false x
  if isStrdVar t then .ok t
  else .error s!"{x.annotation}Expecting a strand variable"

/-- Load a term that must have sort indx (variable or constant).
    Mirrors `loadIndxTerm`. -/
private def loadIndxTerm (sig : Sig) (ts : List Term)
    (x : SExpr Pos) : Except String Term := do
  let t ← loadTerm sig ts false x
  if isIndxVar t || isIndxConst t then .ok t
  else .error s!"{x.annotation}Expecting an indx variable"

/-- Load a node term `(strand, index)` from two S-expressions.
    Mirrors `loadNodeTerm`. -/
private def loadNodeTerm (sig : Sig) (ts : List Term)
    (x v : SExpr Pos) : Except String NodeTerm := do
  let t ← loadStrdTerm sig ts x
  match v with
  | .num _ i =>
    if i >= 0 then .ok (t, indxOfInt i)
    else do let t' ← loadIndxTerm sig ts v; .ok (t, t')
  | _ => do let t' ← loadIndxTerm sig ts v; .ok (t, t')

-- ── Role-specificity check ────────────────────────────────────────────────────

private def termVars (t : Term) : List Term := addVars [] t

private def allBound (unbound : List Term) (t : Term) : Bool :=
  (termVars t).all (fun v => !unbound.contains v)

/-- Remove from `unbound` the message variables bound by a fact.
    Mirrors `factSpecific`. -/
private def factSpecific (unbound : List Term) : Pos × AForm → List Term
  | (_, .AFact _ fs) =>
    let bound := (fs.filter (fun t => !isStrdVar t)).foldl addVars []
    unbound.filter (fun v => !bound.contains v)
  | _ => unbound

/-- Check a single formula for role-specificity; remove newly bound variables.
    Mirrors `roleSpecific :: MonadFail m => [Term] -> (Pos, AForm) -> m [Term]`. -/
private def roleSpecific (unbound : List Term) : Pos × AForm → Except String (List Term)
  | (_, .Length _ z _) =>
      .ok (unbound.erase z)
  | (pos, .Param _ _ _ z t) =>
      if !unbound.contains z then
        let bound := termVars t
        .ok (unbound.filter (fun v => !bound.contains v))
      else .error s!"{pos}Unbound variable in parameter predicate"
  | (pos, .Prec (z, _) (z', _)) =>
      if !unbound.contains z && !unbound.contains z' then .ok unbound
      else .error s!"{pos}Unbound variable in prec"
  | (pos, .Non t) =>
      if allBound unbound t then .ok unbound
      else .error s!"{pos}Unbound variable in non"
  | (pos, .Pnon t) =>
      if allBound unbound t then .ok unbound
      else .error s!"{pos}Unbound variable in pnon"
  | (pos, .Uniq t) =>
      if allBound unbound t then .ok unbound
      else .error s!"{pos}Unbound variable in uniq"
  | (pos, .UniqAt t (z, _)) =>
      if allBound unbound t && !unbound.contains z then .ok unbound
      else .error s!"{pos}Unbound variable in uniq-at"
  | (pos, .Ugen t) =>
      if allBound unbound t then .ok unbound
      else .error s!"{pos}Unbound variable in ugen"
  | (pos, .UgenAt t (z, _)) =>
      if allBound unbound t && !unbound.contains z then .ok unbound
      else .error s!"{pos}Unbound variable in ugen-at"
  | (pos, .GenStV t) =>
      if allBound unbound t then .ok unbound
      else .error s!"{pos}Unbound variable in gen-st"
  | (pos, .Conf t) =>
      if allBound unbound t then .ok unbound
      else .error s!"{pos}Unbound variable in conf"
  | (pos, .Auth t) =>
      if allBound unbound t then .ok unbound
      else .error s!"{pos}Unbound variable in auth"
  | (pos, .AFact _ fs) =>
      if fs.all (allBound unbound) then .ok unbound
      else .error s!"{pos}Unbound variable in fact"
  | (pos, .Commpair (z, _) (z', _)) =>
      if !unbound.contains z && !unbound.contains z' then .ok unbound
      else .error s!"{pos}Unbound variable in comm-pr"
  | (pos, .LeadsTo (z, _) (z', _)) =>
      if !unbound.contains z && !unbound.contains z' then .ok unbound
      else .error s!"{pos}Unbound variable in leads-to"
  | (pos, .StateNode (z, _)) =>
      if !unbound.contains z then .ok unbound
      else .error s!"{pos}Unbound variable in state-node"
  | (pos, .Trans (z, _)) =>
      if !unbound.contains z then .ok unbound
      else .error s!"{pos}Unbound variable in trans"
  | (pos, .SameLocn (z, i) (z', i')) =>
      if !unbound.contains z && !unbound.contains z' &&
         !unbound.contains i && !unbound.contains i' then .ok unbound
      else .error s!"{pos}Unbound variable in same-locn"
  | (pos, .Equals t t') =>
      if isStrdVar t && isStrdVar t' then
        if !unbound.contains t && !unbound.contains t' then .ok unbound
        else .error s!"{pos}Unbound variable in equals"
      else if isStrdVar t || isStrdVar t' then
        .error s!"{pos}Type mismatch in equals"
      else if allBound unbound t && allBound unbound t' then .ok unbound
      else .error s!"{pos}Unbound variable in equals"
  | (pos, .Component t t') =>
      if isStrdVar t && isStrdVar t' then
        if !unbound.contains t && !unbound.contains t' then .ok unbound
        else .error s!"{pos}Unbound variable in component"
      else if isStrdVar t || isStrdVar t' then
        .error s!"{pos}Type mismatch in component"
      else if allBound unbound t && allBound unbound t' then .ok unbound
      else .error s!"{pos}Unbound variable in component"

-- ── Atomic formula loader ─────────────────────────────────────────────────────

/-- Load a single atomic formula.
    Mirrors `loadPrimary`. -/
private def loadPrimary (sig : Sig) (top : Pos) (p : Prot)
    (kvars : List Term) (x : SExpr Pos) : Except String (Pos × AForm) :=
  match x with
  | .lst pos [.sym _ "=", a, b] => do
      let t  ← loadTerm sig kvars false a
      let t' ← loadTerm sig kvars false b
      if isStrdVar t == isStrdVar t' then .ok (pos, .Equals t t')
      else .error s!"{pos}Sort mismatch in equality"
  | .lst pos [.sym _ "component", a, b] => do
      let t  ← loadTerm sig kvars false a
      let t' ← loadTerm sig kvars false b
      if isStrdVar t || isStrdVar t' then
        .error s!"{pos}Strand variable in component formula"
      else .ok (pos, .Component t t')
  | .lst pos [.sym _ "non", a] => do
      let t ← loadAlgTerm sig kvars a; .ok (pos, .Non t)
  | .lst pos [.sym _ "pnon", a] => do
      let t ← loadAlgTerm sig kvars a; .ok (pos, .Pnon t)
  | .lst pos [.sym _ "uniq", a] => do
      let t ← loadAlgTerm sig kvars a; .ok (pos, .Uniq t)
  | .lst pos [.sym _ "uniq-at", a, b, c] => do
      let t  ← loadAlgTerm sig kvars a
      let nt ← loadNodeTerm sig kvars b c
      .ok (pos, .UniqAt t nt)
  | .lst pos [.sym _ "ugen", a] => do
      let t ← loadAlgTerm sig kvars a; .ok (pos, .Ugen t)
  | .lst pos [.sym _ "ugen-at", a, b, c] => do
      let t  ← loadAlgTerm sig kvars a
      let nt ← loadNodeTerm sig kvars b c
      .ok (pos, .UgenAt t nt)
  | .lst pos [.sym _ "gen-st", a] => do
      let t ← loadAlgTerm sig kvars a; .ok (pos, .GenStV t)
  | .lst pos [.sym _ "conf", a] => do
      let t ← loadChanTerm sig kvars a; .ok (pos, .Conf t)
  | .lst pos [.sym _ "auth", a] => do
      let t ← loadChanTerm sig kvars a; .ok (pos, .Auth t)
  | .lst pos (.sym _ "fact" :: .sym _ name :: fs) => do
      let ts ← loadTerms sig kvars fs; .ok (pos, .AFact name ts)
  | .lst pos [.sym _ "comm-pr", w, a, b, c] => do
      let nt  ← loadNodeTerm sig kvars w a
      let nt' ← loadNodeTerm sig kvars b c
      .ok (pos, .Commpair nt nt')
  | .lst pos [.sym _ "same-locn", w, a, b, c] => do
      let nt  ← loadNodeTerm sig kvars w a
      let nt' ← loadNodeTerm sig kvars b c
      .ok (pos, .SameLocn nt nt')
  | .lst pos [.sym _ "state-node", w, a] => do
      let nt ← loadNodeTerm sig kvars w a; .ok (pos, .StateNode nt)
  | .lst pos [.sym _ "trans", w, a] => do
      let nt ← loadNodeTerm sig kvars w a; .ok (pos, .Trans nt)
  | .lst pos [.sym _ "leads-to", w, a, b, c] => do
      let nt  ← loadNodeTerm sig kvars w a
      let nt' ← loadNodeTerm sig kvars b c
      .ok (pos, .LeadsTo nt nt')
  | .lst pos [.sym _ "prec", w, a, b, c] => do
      let nt  ← loadNodeTerm sig kvars w a
      let nt' ← loadNodeTerm sig kvars b c
      if nt.1 == nt'.1 then .error s!"{pos}Malformed pair -- nodes in same strand"
      else .ok (pos, .Prec nt nt')
  | .lst pos [.sym _ "p", .str _ name, a, .num _ h] => do
      let r ← lookupRole pos p name
      let t ← loadStrdTerm sig kvars a
      if h <= 0 || h > r.rtrace.length then .error s!"{pos}Bad length"
      else .ok (pos, .Length r t (indxOfInt h))
  | .lst pos [.sym _ "p", .str _ name, a, ht] => do
      let r ← lookupRole pos p name
      let t ← loadStrdTerm sig kvars a
      let h ← loadTerm sig kvars false ht
      .ok (pos, .Length r t h)
  | .lst pos [.sym _ "p", .str _ name, .str var rv, b, c] => do
      let r ← lookupRole pos p name
      let v ← loadAlgChanTerm sig r.rvars (.sym var rv)
      let s ← loadStrdTerm sig kvars b
      let t ← loadAlgChanTerm sig kvars c
      if !isVar v then .error s!"{pos}Bad parameter -- not a variable {showTerm v}"
      else match firstOccurs v r with
        | some i => .ok (pos, .Param r v (i + 1) s t)
        | none   => .error s!"{pos}parameter {rv} not in role {name}"
  | .lst pos (.sym _ "p" :: .str _ name :: _) =>
      .error s!"{pos}Bad protocol specific formula for role {name}"
  | .lst pos (.sym _ pred :: _) =>
      .error s!"{pos}Bad formula for predicate {pred}"
  | _ => .error s!"{top}Bad formula"

-- ── Variable maps ─────────────────────────────────────────────────────────────

/-- Load the parameter-variable mapping entries in a strand formula.
    Mirrors `loadVMaps`. -/
private def loadVMaps (sig : Sig) (top : Pos) (p : Prot) (kvars : List Term)
    (r : Role) (s : Term) (h : Int) : List (SExpr Pos) → Except String Conj
  | [] => .ok []
  | .lst pos [.sym var rv, sv] :: vmaps => do
      let v ← loadAlgChanTerm sig r.rvars (.sym var rv)
      let t ← loadAlgChanTerm sig kvars sv
      if !isVar v then .error s!"{pos}Bad parameter -- not a variable {showTerm v}"
      else match firstOccurs v r with
        | some i => do
            let rest ← loadVMaps sig pos p kvars r s h vmaps
            .ok ((pos, .Param r v (i + 1) s t) :: rest)
        | none => .error s!"{pos}parameter {rv} not in role {r.rname}"
  | _ => .error s!"{top}Bad variable map"

-- ── Strand and listener formula loaders ──────────────────────────────────────

/-- Load a `strand` formula into a list of `Length`/`Param` atoms.
    Mirrors `loadStrand`. -/
private def loadStrand (sig : Sig) (top : Pos) (p : Prot)
    (kvars : List Term) (ss : List (SExpr Pos)) : Except String Conj :=
  match ss with
  | .sym pos name :: x :: .num _ h :: vmaps => do
      let r ← lookupRole pos p name
      let s ← loadStrdTerm sig kvars x
      if h <= 0 || h > r.rtrace.length then .error s!"{pos}Bad length"
      else do
        let params ← loadVMaps sig pos p kvars r s h vmaps
        .ok ((pos, .Length r s (indxOfInt h)) :: params)
  | _ => .error s!"{top}Bad strand formula"

/-- Load a `listener` formula into a `Length` and `Param` atom pair.
    Mirrors `loadListener`. -/
private def loadListener (sig : Sig) (pos : Pos) (p : Prot)
    (kvars : List Term) (ss : List (SExpr Pos)) : Except String Conj :=
  match ss with
  | [.sym pos1 x, z] => do
      let r  := p.listenerRole
      let v  ← loadAlgChanTerm sig r.rvars (.sym pos "x")
      let s  ← loadStrdTerm sig kvars (.sym pos1 x)
      let t  ← loadAlgTerm sig kvars z
      .ok [(pos1, .Length r s (indxOfInt 2)),
           (z.annotation, .Param r v 2 s t)]
  | _ => .error s!"{pos}Bad listener formula"

-- ── Conjunction loaders ───────────────────────────────────────────────────────

/-- Load a conjunction of atomic formulas (sorted by constructor order).
    Mirrors `loadConjunction` / `loadConjuncts`. -/
private def loadConjunction (sig : Sig) (top : Pos) (p : Prot)
    (kvars : List Term) (x : SExpr Pos) : Except String Conj := do
  let xs := match x with
    | .lst _ (.sym _ "and" :: items) => items
    | _                              => [x]
  let conj ← xs.foldlM (fun (acc : Conj) item =>
    match item with
    | .lst pos (.sym _ "strand"   :: ss) => do
        let posas ← loadStrand   sig pos p kvars ss
        .ok (posas ++ acc)
    | .lst pos (.sym _ "listener" :: ss) => do
        let posas ← loadListener sig pos p kvars ss
        .ok (posas ++ acc)
    | _ => do
        let pa ← loadPrimary sig top p kvars item
        .ok (pa :: acc)) []
  .ok (sortConj conj)

/-- Load a conjunction in role-specific mode (all universals must be bound).
    Mirrors `loadRoleSpecific`. -/
private def loadRoleSpecific (sig : Sig) (pos : Pos) (p : Prot)
    (vars unbound : List Term) (x : SExpr Pos) : Except String Conj := do
  let as' ← loadConjunction sig pos p vars x
  let unbound' := as'.foldl factSpecific unbound
  let unbound'' ← as'.foldlM roleSpecific unbound'
  match unbound'' with
  | []     => .ok as'
  | v :: _ => .error s!"{x.annotation}{showTerm v} not used"

/-- Load a conjunction, checking only that every declared variable is used.
    Mirrors `loadUsedVars`. -/
private def loadUsedVars (sig : Sig) (pos : Pos) (p : Prot)
    (vars unbound : List Term) (x : SExpr Pos) : Except String Conj := do
  let as' ← loadConjunction sig pos p vars x
  let bound := as'.foldl (fun acc (_, form) => aFreeVars acc form) []
  match unbound.filter (fun v => !bound.contains v) with
  | []     => .ok as'
  | v :: _ => .error s!"{x.annotation}{showTerm v} not used"

/-- Load a conjunction without variable-binding checks.
    Mirrors `loadLiberalVars`. -/
private def loadLiberalVars (sig : Sig) (pos : Pos) (p : Prot)
    (vars _ : List Term) (x : SExpr Pos) : Except String Conj :=
  loadConjunction sig pos p vars x

/-- Dispatch to the mode-specific conjunction loader.
    Mirrors `loadCheckedConj`. -/
private def loadCheckedConj (sig : Sig) (md : Mode) (pos : Pos) (p : Prot)
    (vars unbound : List Term) (x : SExpr Pos) : Except String Conj :=
  match md with
  | .RoleSpec   => loadRoleSpecific sig pos p vars unbound x
  | .UnusedVars => loadUsedVars     sig pos p vars unbound x
  | .Liberal    => loadLiberalVars  sig pos p vars unbound x

-- ── Existential and disjunct loaders ─────────────────────────────────────────

/-- Load an existentially-quantified disjunct.
    Mirrors `loadExistential`. -/
private def loadExistential (sig : Sig) (pos : Pos) (p : Prot) (g : Gen)
    (vars : List Term) (x : SExpr Pos) : Except String (Gen × (List Term × Conj)) :=
  match x with
  | .lst pos' [.sym _ "exists", .lst _ vs, body] => do
      let (g', evars) ← loadVars sig g vs
      let as' ← loadCheckedConj sig .Liberal pos' p (evars ++ vars) evars body
      .ok (g', (evars, as'))
  | _ => do
      let as' ← loadCheckedConj sig .RoleSpec pos p vars [] x
      .ok (g, ([], as'))

/-- Load a sequence of disjuncts, accumulating into `acc`.
    Mirrors `loadDisjuncts`. -/
def loadDisjuncts (sig : Sig) (pos : Pos) (p : Prot) (g : Gen)
    (vars : List Term) (xs : List (SExpr Pos))
    (acc : List (List Term × Conj)) : Except String (Gen × List (List Term × Conj)) := do
  xs.foldlM (fun (g', rest) item => do
    let (g'', a) ← loadExistential sig pos p g' vars item
    .ok (g'', a :: rest)) (g, acc) >>= fun (g', res) =>
  .ok (g', res.reverse)

/-- Load the conclusion of a security goal (a disjunction of existentials).
    Mirrors `loadConclusion`. -/
def loadConclusion (sig : Sig) (pos : Pos) (p : Prot) (g : Gen)
    (vars : List Term) (x : SExpr Pos)
    : Except String (Gen × List (List Term × Conj)) :=
  match x with
  | .lst _ [.sym _ "false"]          => .ok (g, [])
  | .lst pos' (.sym _ "or" :: xs)    => loadDisjuncts sig pos' p g vars xs []
  | _ => do
      let (g', a) ← loadExistential sig pos p g vars x
      .ok (g', [a])

/-- Load multiple conclusions from a list of S-expressions.
    Mirrors `loadConclusions`. -/
def loadConclusions (sig : Sig) (p : Prot) (g : Gen) (vars : List Term)
    (xs : List (SExpr Pos))
    : Except String (Gen × List (List (List Term × Conj))) := do
  xs.foldlM (fun (g', acc) item => do
    let (g'', c) ← loadConclusion sig item.annotation p g' vars item
    .ok (g'', acc ++ [c])) (g, [])

-- ── Top-level sentence loader ─────────────────────────────────────────────────

/-- Load the top-level implication of a security goal.
    Mirrors `loadImplication`. -/
private def loadImplication (sig : Sig) (md : Mode) (pos : Pos) (p : Prot)
    (g : Gen) (vars : List Term) (x : SExpr Pos)
    : Except String (Gen × Goal × Conj) :=
  match x with
  | .lst pos' [.sym _ "implies", a, c] => do
      let antec ← loadCheckedConj sig md pos' p vars vars a
      let (g', vc) ← loadConclusion sig pos' p g vars c
      let consq := vc.map (fun (evars, form) => (evars, form.map Prod.snd))
      let goal : Goal :=
        { uvars := vars,
          antec := antec.map Prod.snd,
          consq := consq,
          concl := consq.map Prod.snd }
      .ok (g', goal, antec)
  | _ => .error s!"{pos}Bad goal implication"

/-- Load a universally-quantified security goal from an S-expression.
    Mirrors `loadSentence`. -/
def loadSentence (sig : Sig) (md : Mode) (pos : Pos) (p : Prot)
    (g : Gen) (x : SExpr Pos) : Except String (Gen × Goal × Conj) :=
  match x with
  | .lst _ [.sym _ "forall", .lst _ vs, body] => do
      let (g', vars) ← loadVars sig g vs
      loadImplication sig md pos p g' vars body
  | _ => .error s!"{pos}Bad goal sentence:  No forall"

end LeanCPSA.LoadFormulas
