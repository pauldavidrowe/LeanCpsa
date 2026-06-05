/-
LeanCPSA.GenRules

Port of CPSA.GenRules (MITRE cpsa v4.4.8).

Copyright (c) 2026 Paul D. Rowe

Generates rules when loading protocols from S-expressions.

Copyright (c) 2009 The MITRE Corporation

This program is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.
-/

import LeanCPSA.Signature
import LeanCPSA.Algebra
import LeanCPSA.Channel
import LeanCPSA.Protocol
import LeanCPSA.LoadFormulas

namespace LeanCPSA.GenRules

open LeanCPSA.Signature (Sig)
open LeanCPSA.Algebra
open LeanCPSA.Channel (ChMsg)
open LeanCPSA.Protocol
open LeanCPSA.Lib (assertError)
open LeanCPSA.LoadFormulas

-- ── Type aliases ──────────────────────────────────────────────────────────────

/-- A conjunction of atomic formulas (without position annotations).
    Mirrors `type Conjunction = [AForm]`. -/
abbrev Conjunction := List AForm

/-- Strip position annotations from a `Conj`.
    Mirrors `conjunctionOfConj :: Conj -> Conjunction`. -/
def conjunctionOfConj (c : Conj) : Conjunction := c.map Prod.snd

-- ── Core rule builder ─────────────────────────────────────────────────────────

/-- Build a `Rule` from its components.
    Mirrors `ruleOfClauses :: Sig -> Gen -> String -> [Term] -> Conjunction
             -> [([Term],Conjunction)] -> (Gen,Rule)`. -/
def ruleOfClauses (_ : Sig) (g : Gen) (rn : String)
    (fvs : List Term) (antecedent : Conjunction)
    (evarDisjuncts : List (List Term × Conjunction)) : Gen × Rule :=
  let (g', env, uvars) := renamerAndNewVars fvs g
  let disjuncts := evarDisjuncts.map fun (evars, c) =>
    (evars, c.map (instantiateAForm env))
  (g', { rlname    := rn,
          rlgoal    := { uvars := uvars,
                         antec := antecedent.map (instantiateAForm env),
                         consq := disjuncts,
                         concl := disjuncts.map Prod.snd },
          rlcomment := [] })

-- ── Utility combinators ───────────────────────────────────────────────────────

private def applyToSoleEntry {α β : Type} [Inhabited β](f : α → β) (errMsg : String) : List α → β
  | [a] => f a
  | _   => assertError errMsg

private def applyToThreeEntries {α β : Type} [Inhabited β] (f : α → α → α → β) (errMsg : String) : List α → β
  | [a1, a2, a3] => f a1 a2 a3
  | _            => assertError errMsg

private def applyToStrandVarAndParams {α β : Type} [Inhabited β] (f : α → List α → β) : List α → String → β
  | [],         errMsg => assertError errMsg
  | a :: rest,  _     => f a rest

-- ── neqRules ──────────────────────────────────────────────────────────────────

/-- Generate not-equal rules for standard sorts.
    Mirrors `neqRules :: Sig -> Gen -> (Gen, [Rule])`. -/
def neqRules (sig : Sig) (g : Gen) : Gen × List Rule :=
  ["indx", "strd", "mesg"].foldr (fun sortName (g, rs) =>
    let (g', v)  := newVar sig g "x" sortName
    let (g'', r) := ruleOfClauses sig g' ("neqRl_" ++ sortName)
                      [v] [.AFact "neq" [v, v]] []
    (g'', r :: rs)) (g, [])

-- ── transRls ──────────────────────────────────────────────────────────────────

/-- Generate transition rules for a role at given index pairs.
    Mirrors `transRls :: Sig -> Gen -> Role -> [(Int,Int)] -> (Gen, [Rule])`. -/
def transRls (sig : Sig) (g : Gen) (rl : Role) (pairs : List (Int × Int)) : Gen × List Rule :=
  pairs.foldl (fun (g, rs) (i, j) =>
    let (g', z)  := newVar sig g "z" "strd"
    let (g'', r) := ruleOfClauses sig g'
                      ("trRl_" ++ rl.rname ++ "-at-" ++ toString i)
                      [z]
                      [.Length rl z (indxOfInt (j + 1))]
                      [([], [.Trans (z, indxOfInt i)])]
    (g'', r :: rs)) (g, [])

-- ── lastRecvOrFirstSendInCS ───────────────────────────────────────────────────

instance : Inhabited (Sum Int Int) := ⟨.inl 0⟩

/-- Find the last receive or first store event in a critical section.
    Returns `Sum.inl lastRecv` or `Sum.inr firstStor`.
    Mirrors `lastRecvOrFirstSendInCS :: Role -> Int -> Int -> Either Int Int`. -/
private def lastRecvOrFirstSendInCS (rl : Role) (start : Int) (endIdx : Int)
    : Sum Int Int :=
  let rec loopLeft (i : Int) : List Event → Sum Int Int
    | .In (.ChMsg ct _ _) :: c =>
        if i <= endIdx && ct == .Locn then loopLeft (i + 1) c else .inl i
    | _ => .inl i
  match rl.rtrace.drop start.toNat with
  | .In (.ChMsg ct _ _) :: c =>
      if start <= endIdx && ct == .Locn then loopLeft start c
      else assertError s!"lastRecvOrFirstSendInCS: {rl.rname} at {start} should be a state event"
  | .Out (.ChMsg ct _ _) :: _ =>
      if start <= endIdx && ct == .Locn then .inr start
      else assertError s!"lastRecvOrFirstSendInCS: {rl.rname} at {start} should be a state event"
  | _ =>
      assertError s!"lastRecvOrFirstSendInCS: {rl.rname} at {start} should be a state event"

-- ── csRules ───────────────────────────────────────────────────────────────────

private def csCauseRule (sig : Sig) (g : Gen) (rl : Role) (start : Int) (ind : Int)
    : Gen × Rule :=
  let (g', z)   := newVar sig g "z" "strd"
  let (g'', z1) := newVar sig g' "z1" "strd"
  let (g''', i) := newVar sig g'' "i" "indx"
  ruleOfClauses sig g''' ("cau-" ++ rl.rname ++ "-" ++ toString ind)
    [z, z1, i]
    [.Length rl z (indxOfInt (ind + 1)), .Prec (z1, i) (z, indxOfInt ind)]
    [([], [.Equals z z1]),
     ([], [.Prec (z1, i) (z, indxOfInt start)])]

private def csEffectRule (sig : Sig) (g : Gen) (rl : Role) (endIdx : Int) (ind : Int)
    : Gen × Rule :=
  let (g', z)   := newVar sig g "z" "strd"
  let (g'', z1) := newVar sig g' "z1" "strd"
  let (g''', i) := newVar sig g'' "i" "indx"
  ruleOfClauses sig g''' ("eff-" ++ rl.rname ++ "-" ++ toString ind)
    [z, z1, i]
    [.Length rl z (indxOfInt (ind + 1)), .Prec (z, indxOfInt ind) (z1, i)]
    [([], [.Equals z z1]),
     ([], [.Length rl z (indxOfInt (endIdx + 1)), .Prec (z, indxOfInt endIdx) (z1, i)])]

/-- Generate cause/effect rules for critical sections in a role.
    Mirrors `csRules :: Sig -> Gen -> Role -> [(Int,Int)] -> (Gen, [Rule])`. -/
def csRules (sig : Sig) (g : Gen) (rl : Role) (pairs : List (Int × Int)) : Gen × List Rule :=
  pairs.foldl (fun (g, rs) (start, endIdx) =>
    match lastRecvOrFirstSendInCS rl start endIdx with
    | .inr firstStor =>
        if firstStor == endIdx then (g, rs)
        else
          let (g', re) := csEffectRule sig g rl endIdx firstStor
          (g', re :: rs)
    | .inl lastRecv =>
        let (g', crules) :=
          if start == lastRecv then (g, [])
          else
            let (g', rc) := csCauseRule sig g rl start lastRecv
            (g', [rc])
        let (g'', erules) :=
          if lastRecv + 1 == endIdx then (g', [])
          else
            let (g'', re) := csEffectRule sig g' rl endIdx (lastRecv + 1)
            (g'', [re])
        (g'', crules ++ erules ++ rs)) (g, [])

-- ── FoundAt ───────────────────────────────────────────────────────────────────

/-- Result of searching for variable heights in a role trace.
    Mirrors `data FoundAt = FoundAt Int | Missing Term`. -/
inductive FoundAt where
  | foundAt : Int  → FoundAt
  | missing : Term → FoundAt

-- ── varsUsedHeight ────────────────────────────────────────────────────────────

/-- Smallest height in `rl`'s trace at which all `vars` have occurred.
    Mirrors `varsUsedHeight :: Role -> [Term] -> FoundAt`. -/
def varsUsedHeight (rl : Role) (vars : List Term) : FoundAt :=
  let rec loop (i : Int) : List Term → FoundAt
    | []        => .foundAt (1 + i)
    | v :: rest =>
        match firstOccurs v rl with
        | none   => .missing v
        | some j => loop (max i j) rest
  loop 0 vars

-- ── VarListSpec helpers ───────────────────────────────────────────────────────

/-- Collect all bound variable names from a `VarListSpec`.
    Mirrors `boundVarNamesOfVarListSpec :: VarListSpec -> [String]`. -/
def boundVarNamesOfVarListSpec (spec : VarListSpec) : List String :=
  (spec.flatMap Prod.snd).eraseDups

-- ── freeVarsInConjLists ───────────────────────────────────────────────────────

/-- Free variables in a list of (existential-vars, conj) pairs (positions stripped).
    Mirrors `freeVarsInConjLists :: [([Term], Conj)] -> [Term]`. -/
def freeVarsInConjLists (vcs : List (List Term × Conj)) : List Term :=
  vcs.flatMap fun (vars, conj) =>
    (conj.foldr (fun (_, af) soFar => aFreeVars soFar af) []).filter (fun v => !vars.contains v)

-- ── freeVarsSubsetByName ──────────────────────────────────────────────────────

/-- Subset of `fvars` whose names appear among `pvars`.
    Mirrors `freeVarsSubsetByName :: [Term] -> [Term] -> [Term]`. -/
def freeVarsSubsetByName (fvars pvars : List Term) : List Term :=
  let pvarNames := pvars.map varName
  fvars.filter (fun fv => pvarNames.contains (varName fv))

-- ── conclHeight ───────────────────────────────────────────────────────────────

/-- Height needed to satisfy all variables in a conclusion.
    Mirrors `conclHeight :: Role -> [([Term], Conj)] -> FoundAt`. -/
def conclHeight (rl : Role) : List (List Term × Conj) → FoundAt
  | []          => .foundAt 1
  | disj :: rest =>
      match conclHeight rl rest with
      | .missing v => .missing v
      | .foundAt j =>
          match varsUsedHeight rl (freeVarsInConjLists [disj]) with
          | .missing v => .missing v
          | .foundAt i => .foundAt (max i j)

-- ── renameApart ───────────────────────────────────────────────────────────────

/-- Choose a fresh name not already used by any variable in `vars`.
    Mirrors `renameApart :: String -> [Term] -> String`. -/
private def renameApart (pfx : String) (vars : List Term) : String :=
  let vns := vars.map varName
  if !vns.contains pfx then pfx
  else
    -- There are only finitely many names in `vns`.  By pigeonhole, some i in
    -- 0..vns.length is unused.  Search that finite range to ensure termination.
    let max := vns.length
    let candidates := List.range (max + 1) |>.map fun i => pfx ++ "-" ++ toString i
    match candidates.find? fun c => !vns.contains c with
    | some c => c
    | none => pfx ++ "-0" -- fallback (shouldn't happen)

-- ── ruleOfDisjAtHeight ────────────────────────────────────────────────────────

/-- Build a rule for a role at a specific height, extracting parameters.
    Mirrors `ruleOfDisjAtHeight :: Sig -> Gen -> Role -> String
             -> [([Term],[AForm])] -> Int -> (Gen, Rule)`. -/
def ruleOfDisjAtHeight (sig : Sig) (g : Gen) (rl : Role) (rulename : String)
    (disj : List (List Term × Conjunction)) (ht : Int) : Gen × Rule :=
  let fvs := fvsConsq disj
  let rvs := fvs.filter (fun t => rl.rvars.contains t)
  let (g', z) := newVar sig g "z" "strd"
  ruleOfClauses sig g' rulename
    (fvs ++ [z])
    (.Length rl z (indxOfInt ht) ::
      rvs.map fun v =>
        match firstOccurs v rl with
        | none   => assertError s!"ruleOfDisjAtHeight: Parameter {varName v} not found."
        | some i =>
            if i < ht then .Param rl v (i + 1) z v
            else assertError
              s!"ruleOfDisjAtHeight: Parameter {varName v} introduced too high in role \
                 {rl.rname}: {i} not below {ht} in {rulename}.")
    disj

-- ── genOneAssumeRl / genAssumeRls ─────────────────────────────────────────────

/-- Generate one assume rule for a role.
    Mirrors `genOneAssumeRl :: Sig -> Gen -> Role -> Int -> [([Term], Conj)] -> (Gen, Rule)`. -/
def genOneAssumeRl (sig : Sig) (g : Gen) (rl : Role) (n : Int)
    (disjs : List (List Term × Conj)) : Gen × Rule :=
  match conclHeight rl disjs with
  | .missing v =>
      assertError s!"genOneAssumeRl: Variable not in role {rl.rname}: {varName v}"
  | .foundAt ht =>
      let disjuncts := disjs.map fun (vs, cs) => (vs, cs.map Prod.snd)
      ruleOfDisjAtHeight sig g rl ("assume-" ++ rl.rname ++ "-" ++ toString n) disjuncts ht

/-- Generate assume rules for a role from a list of disjunct groups.
    Mirrors `genAssumeRls :: Sig -> Gen -> Role -> [[([Term], Conj)]] -> (Gen, [Rule])`. -/
def genAssumeRls (sig : Sig) (g : Gen) (rl : Role)
    (disjs : List (List (List Term × Conj))) : Gen × List Rule :=
  let (g', rls, _) := disjs.foldr (fun ds (g, rs, n) =>
    let (g', new_rule) := genOneAssumeRl sig g rl n ds
    (g', new_rule :: rs, n + 1)) (g, [], (0 : Int))
  (g', rls)

-- ── genOneRelyGuarRl ──────────────────────────────────────────────────────────

/-- Generate one rely/guarantee rule for a role at a fixed height.
    Mirrors `genOneRelyGuarRl :: Sig -> Gen -> Role -> Int -> String
             -> [([Term], Conj)] -> (Gen, Rule)`. -/
def genOneRelyGuarRl (sig : Sig) (g : Gen) (rl : Role) (ht : Int) (kind : String)
    (disjs : List (List Term × Conj)) : Gen × Rule :=
  match conclHeight rl disjs with
  | .missing v =>
      assertError s!"genOneRelyGuarRl: Variable not in role {rl.rname}: {varName v}"
  | .foundAt fndHt =>
      if fndHt <= ht then
        let disjuncts := disjs.map fun (vs, cs) => (vs, cs.map Prod.snd)
        ruleOfDisjAtHeight sig g rl (kind ++ "-" ++ rl.rname ++ "-" ++ toString ht) disjuncts ht
      else
        assertError s!"genOneRelyGuarRl: Variable found above ht {ht} in {rl.rname}"

-- ── genStateRls ───────────────────────────────────────────────────────────────

/-- Generate gen-st rules for each state term.
    Mirrors `genStateRls :: Sig -> Gen -> Role -> [Term] -> (Gen, [Rule])`. -/
def genStateRls (sig : Sig) (g : Gen) (rl : Role) (ts : List Term) : Gen × List Rule :=
  let (g', rls, _) := ts.foldr (fun t (g, rs, n) =>
    match varsUsedHeight rl (varsInTerm t) with
    | .missing v =>
        assertError s!"genStateRls: In gen-st of {rl.rname}: no occurrence of {varName v}"
    | .foundAt ht =>
        let (g', new_rule) := ruleOfDisjAtHeight sig g rl
          ("gen-st-" ++ rl.rname ++ "-" ++ toString n)
          [([], [.GenStV t])] ht
        (g', new_rule :: rs, n + 1)) (g, [], (0 : Int))
  (g', rls)

-- ── genFactRls ────────────────────────────────────────────────────────────────

/-- Generate fact rules for each (predicate, args) pair.
    Mirrors `genFactRls :: Sig -> Gen -> Role -> [(String,[Term])] -> (Gen, [Rule])`. -/
def genFactRls (sig : Sig) (g : Gen) (rl : Role) (predarglists : List (String × List Term))
    : Gen × List Rule :=
  let (g', rls, _) := predarglists.foldr (fun (pred, args) (g, rs, n) =>
    match varsUsedHeight rl (args.flatMap varsInTerm) with
    | .missing v =>
        assertError s!"genFactRls: In fact of {rl.rname}: no occurrence of {varName v}"
    | .foundAt ht =>
        let (g', new_rule) := ruleOfDisjAtHeight sig g rl
          ("fact-" ++ rl.rname ++ "-" ++ pred ++ toString n)
          [([], [.AFact pred args])] ht
        (g', new_rule :: rs, n + 1)) (g, [], (0 : Int))
  (g', rls)

-- ── theVacuousRule ────────────────────────────────────────────────────────────

/-- A vacuous rule with empty antecedent and false conclusion.
    Mirrors `theVacuousRule :: Rule`. -/
def theVacuousRule : Rule :=
  { rlname    := "vacuity",
    rlgoal    := { uvars := [], antec := [], consq := [([], [])], concl := [[]] },
    rlcomment := [] }

-- ── Named state-splitting rules ───────────────────────────────────────────────

/-- The scissors rule: two strands leading to the same state must be equal.
    Mirrors `scissorsRule :: Sig -> Gen -> (Gen, Rule)`. -/
def scissorsRule (sig : Sig) (g : Gen) : Gen × Rule :=
  match sortedVarsOfNames sig g "strd" ["z0", "z1", "z2"] with
  | (g, [z0, z1, z2]) =>
      match sortedVarsOfNames sig g "indx" ["i0", "i1", "i2"] with
      | (g, [i0, i1, i2]) =>
          (g, { rlname    := "scissorsRule",
                rlgoal    := { uvars := [z0, z1, z2, i0, i1, i2],
                               antec := [.Trans (z0, i0), .Trans (z1, i1), .Trans (z2, i2),
                                         .LeadsTo (z0, i0) (z1, i1),
                                         .LeadsTo (z0, i0) (z2, i2)],
                               consq := [([], [.Equals z1 z2, .Equals i1 i2])],
                               concl := [[.Equals z1 z2, .Equals i1 i2]] },
                rlcomment := [] })
      | (g, _) => (g, theVacuousRule)
  | (g, _) => (g, theVacuousRule)

/-- The discrete-after (shears) rule.
    Mirrors `shearsRule :: Sig -> Gen -> (Gen, Rule)`. -/
def shearsRule (sig : Sig) (g : Gen) : Gen × Rule :=
  match sortedVarsOfNames sig g "strd" ["z0", "z1", "z2"] with
  | (g, [z0, z1, z2]) =>
      match sortedVarsOfNames sig g "indx" ["i0", "i1", "i2"] with
      | (g, [i0, i1, i2]) =>
          (g, { rlname    := "discreteAfter",
                rlgoal    := { uvars := [z0, z1, z2, i0, i1, i2],
                               antec := [.Trans (z0, i0), .Trans (z2, i2),
                                         .LeadsTo (z0, i0) (z1, i1),
                                         .SameLocn (z0, i0) (z2, i2),
                                         .Prec (z0, i0) (z2, i2)],
                               consq := [([], [.Equals z1 z2, .Equals i1 i2]),
                                         ([], [.Prec (z1, i1) (z2, i2)])],
                               concl := [[.Equals z1 z2, .Equals i1 i2],
                                         [.Prec (z1, i1) (z2, i2)]] },
                rlcomment := [] })
      | (g, _) => (g, theVacuousRule)
  | (g, _) => (g, theVacuousRule)

/-- The discrete-before (inverse shears) rule.
    Mirrors `invShearsRule :: Sig -> Gen -> (Gen, Rule)`. -/
def invShearsRule (sig : Sig) (g : Gen) : Gen × Rule :=
  match sortedVarsOfNames sig g "strd" ["z0", "z1", "z2"] with
  | (g, [z0, z1, z2]) =>
      match sortedVarsOfNames sig g "indx" ["i0", "i1", "i2"] with
      | (g, [i0, i1, i2]) =>
          (g, { rlname    := "discreteBefore",
                rlgoal    := { uvars := [z0, z1, z2, i0, i1, i2],
                               antec := [.Trans (z0, i0), .Trans (z1, i1),
                                         .SameLocn (z0, i0) (z1, i1),
                                         .LeadsTo (z1, i1) (z2, i2),
                                         .Prec (z0, i0) (z2, i2)],
                               consq := [([], [.Equals z0 z1, .Equals i0 i1]),
                                         ([], [.Prec (z0, i0) (z1, i1)])],
                               concl := [[.Equals z0 z1, .Equals i0 i1],
                                         [.Prec (z0, i0) (z1, i1)]] },
                rlcomment := [] })
      | (g, _) => (g, theVacuousRule)
  | (g, _) => (g, theVacuousRule)

/-- The no-interruption rule.
    Mirrors `uninterruptibleRule :: Sig -> Gen -> (Gen, Rule)`. -/
def uninterruptibleRule (sig : Sig) (g : Gen) : Gen × Rule :=
  match sortedVarsOfNames sig g "strd" ["z0", "z1", "z2"] with
  | (g, [z0, z1, z2]) =>
      match sortedVarsOfNames sig g "indx" ["i0", "i1", "i2"] with
      | (g, [i0, i1, i2]) =>
          (g, { rlname    := "no-interruption",
                rlgoal    := { uvars := [z0, z1, z2, i0, i1, i2],
                               antec := [.LeadsTo (z0, i0) (z2, i2), .Trans (z1, i1),
                                         .SameLocn (z0, i0) (z1, i1),
                                         .Prec (z0, i0) (z1, i1),
                                         .Prec (z1, i1) (z2, i2)],
                               consq := [],
                               concl := [] },
                rlcomment := [] })
      | (g, _) => (g, theVacuousRule)
  | (g, _) => (g, theVacuousRule)

/-- The cake rule (two leads-to with ordering implies False).
    Mirrors `cakeRule :: Sig -> Gen -> (Gen, Rule)`. -/
def cakeRule (sig : Sig) (g : Gen) : Gen × Rule :=
  match sortedVarsOfNames sig g "strd" ["z0", "z1", "z2"] with
  | (g, [z0, z1, z2]) =>
      match sortedVarsOfNames sig g "indx" ["i0", "i1", "i2"] with
      | (g, [i0, i1, i2]) =>
          (g, { rlname    := "cakeRule",
                rlgoal    := { uvars := [z0, z1, z2, i0, i1, i2],
                               antec := [.Trans (z0, i0), .Trans (z1, i1),
                                         .LeadsTo (z0, i0) (z1, i1),
                                         .LeadsTo (z0, i0) (z2, i2),
                                         .Prec (z1, i1) (z2, i2)],
                               consq := [],
                               concl := [] },
                rlcomment := [] })
      | (g, _) => (g, theVacuousRule)
  | (g, _) => (g, theVacuousRule)

end LeanCPSA.GenRules
