/-
LeanCPSA.Loader

Port of CPSA.Loader (MITRE cpsa v4.4.8).

Copyright (c) 2026 Paul D. Rowe

Loads protocols and preskeletons from S-expressions.

Copyright (c) 2009 The MITRE Corporation

This program is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.
-/

import LeanCPSA.Algebra
import LeanCPSA.Protocol
import LeanCPSA.Operation
import LeanCPSA.Strand
import LeanCPSA.Characteristic
import LeanCPSA.LoadFormulas
import LeanCPSA.GenRules

namespace LeanCPSA.Loader

open LeanCPSA.Algebra
open LeanCPSA.Protocol
open LeanCPSA.Operation (Node Pair Sid)
open LeanCPSA.Strand
open LeanCPSA.Characteristic
open LeanCPSA.LoadFormulas
open LeanCPSA.GenRules
open LeanCPSA.Signature (Sig loadSig)
open LeanCPSA.Lib (SExpr Pos adjoin assertError)

-- ── S-expression association-list helpers ─────────────────────────────────────

/-- Collect all values associated with `key` in an association list.
    Mirrors `assoc :: String -> [SExpr a] -> [SExpr a]`. -/
private def assoc {α : Type} (key : String) (alist : List (SExpr α)) : List (SExpr α) :=
  alist.flatMap fun x =>
    match x with
    | .lst _ (.sym _ head :: rest) => if head == key then rest else []
    | _ => []

/-- True when any element of the association list has the given key.
    Mirrors `hasKey :: String -> [SExpr a] -> Bool`. -/
private def hasKey {α : Type} (key : String) (alist : List (SExpr α)) : Bool :=
  alist.any fun x =>
    match x with
    | .lst _ (.sym _ head :: _) => head == key
    | _ => false

/-- Error if any top-level element has one of the given keys at a disallowed position.
    Mirrors `badKey :: MonadFail m => [String] -> [SExpr Pos] -> m ()`. -/
private def badKey (keys : List String) (xs : List (SExpr Pos)) : Except String Unit :=
  xs.foldlM (fun _ x =>
    match x with
    | .lst _ (.sym pos key :: _) =>
        if keys.contains key then
          .error s!"{pos}{key} declaration too late in enclosing form"
        else .ok ()
    | _ => .ok ()) ()

/-- Strip positions from an S-expression.
    Mirrors `strip :: SExpr a -> SExpr ()`. -/
private partial def strip {α : Type} (x : SExpr α) : SExpr Unit :=
  match x with
  | .sym _ s => .sym () s
  | .str _ s => .str () s
  | .num _ n => .num () n
  | .lst _ l => .lst () (l.map strip)

/-- Convert an association list into a comment, dropping the given keys.
    Mirrors `alist :: MonadFail m => [String] -> [SExpr Pos] -> m [SExpr ()]`. -/
private def alistComment (keys : List String) (xs : List (SExpr Pos))
    : Except String (List (SExpr Unit)) :=
  xs.foldlM (fun acc x =>
    match x with
    | .lst _ (.sym _ key :: _) =>
        if keys.contains key then .ok acc
        else .ok (acc ++ [strip x])
    | _ => .error s!"{x.annotation}Malformed association list") []

/-- Build a comment entry from a key-value pair.
    Mirrors `loadComment :: String -> [SExpr Pos] -> [SExpr ()]`. -/
private def loadComment (key : String) (comment : List (SExpr Pos)) : List (SExpr Unit) :=
  if comment.isEmpty then []
  else [.lst () (.sym () key :: comment.map strip)]

/-- Separate goals (forall-forms) from the rest of an association list.
    Mirrors `findAlist :: [SExpr Pos] -> ([SExpr Pos], [SExpr Pos])`. -/
private def findAlist (xs : List (SExpr Pos)) : List (SExpr Pos) × List (SExpr Pos) :=
  let rec loop (goals rest : List (SExpr Pos)) : List (SExpr Pos) → List (SExpr Pos) × List (SExpr Pos)
    | [] => (goals.reverse, rest.reverse)
    | x@(.lst _ (.sym _ "forall" :: _)) :: more => loop (x :: goals) rest more
    | xs => (goals.reverse, rest.reverse ++ xs)
  loop [] [] xs

-- ── PreRules ─────────────────────────────────────────────────────────────────

/-- Collected per-role pre-rule data, used to drive rule generation.
    Mirrors `data PreRules = PreRules { preruleCs, ... }`. -/
structure PreRules where
  preruleCs      : List (Int × Int)
  preruleTrans   : List (Int × Int)
  preruleFacts   : List (SExpr Pos)
  preruleGensts  : List (SExpr Pos)
  preruleAssumes : List (SExpr Pos)
  preruleRelies  : List (Int × SExpr Pos)
  preruleGuars   : List (Int × SExpr Pos)
  preruleCheqs   : List (Int × Pos × Term × Term)

/-- The empty PreRules record.  Mirrors `emptyPreRules`. -/
private def emptyPreRules : PreRules :=
  { preruleCs      := [],
    preruleTrans   := [],
    preruleFacts   := [],
    preruleGensts  := [],
    preruleAssumes := [],
    preruleRelies  := [],
    preruleGuars   := [],
    preruleCheqs   := [] }

private def preRulesAddRely (pr : PreRules) (new : Int × SExpr Pos) : PreRules :=
  { pr with preruleRelies := new :: pr.preruleRelies }

private def preRulesAddGuar (pr : PreRules) (new : Int × SExpr Pos) : PreRules :=
  { pr with preruleGuars := new :: pr.preruleGuars }

private def preRulesAddCheq (pr : PreRules) (new : Int × Pos × Term × Term) : PreRules :=
  { pr with preruleCheqs := new :: pr.preruleCheqs }

-- ── roleWellFormed ───────────────────────────────────────────────────────────

/-- Render a term for error messages. -/
private def showst (t : Term) : String :=
  toString (displayTerm (addToContext emptyContext [t]) t)

/-- Fail if the boolean is false.
    Mirrors `failwith :: MonadFail m => String -> Bool -> m ()`. -/
private def failwith (msg : String) (b : Bool) : Except String Unit :=
  if b then .ok () else .error msg

/-- Check that all vars of t occur in vs. -/
private def varsSeen (vs : List Term) (t : Term) : Bool :=
  (addVars [] t).all (fun v => vs.contains v)

/-- Channels used in the trace of a role. -/
private def chansUsed (rl : Role) : List Term :=
  rl.rtrace.foldl (fun soFar e =>
    match evtChan e with
    | some ch => adjoin ch soFar
    | none    => soFar) []

/-- Check that a channel declared conf/auth is actually used.
    Mirrors `checkChanDecl`. -/
private def checkChanDecl (str : String) (rl : Role) (ch : Term)
    : Except String Unit :=
  failwith s!"{showst ch} declared {str} but not used in role {rl.rname}"
    ((chansUsed rl).contains ch)

/-- Is the trace a prefix of a listener (In t : Out t' : ...  where t == t')?
    Mirrors `notListenerPrefix`. -/
private def notListenerPrefix : Trace → Bool
  | .In t :: .Out t' :: _ => t != t'
  | _ => true

/-- Check that no locn is loaded more than once in the same direction.
    Mirrors `locnsUnique :: Trace -> Bool`. -/
private def locnsUnique : Trace → Bool
  | [] => true
  | .In (.ChMsg ch _) :: c' =>
      if isLocn ch then
        let rec checkLoads (seen : List Term) : Trace → Bool
          | .In (.ChMsg ch _) :: c'' =>
              if isLocn ch then !seen.contains ch && checkLoads (ch :: seen) c''
              else locnsUnique c''
          | c'' => locnsUnique c''
        checkLoads [ch] c'
      else locnsUnique c'
  | .Out (.ChMsg ch _) :: c' =>
      if isLocn ch then
        let rec checkStores (seen : List Term) : Trace → Bool
          | .Out (.ChMsg ch _) :: c'' =>
              if isLocn ch then !seen.contains ch && checkStores (ch :: seen) c''
              else locnsUnique c''
          | c'' => locnsUnique c''
        checkStores [ch] c'
      else locnsUnique c'
  | _ :: c' => locnsUnique c'

/-- Check well-formedness of a role.
    Mirrors `roleWellFormed :: MonadFail m => Role -> m ()`. -/
private def roleWellFormed (role : Role) : Except String Unit := do
  let terms := tterms role.rtrace
  failwith "a variable in non-orig is not in trace"
    (varSubset (role.rnon.map Prod.snd) terms)
  failwith "a variable in pen-non-orig is not in trace"
    (varSubset (role.rpnon.map Prod.snd) terms)
  -- nonCheck
  for (_, t) in role.rnon do
    failwith s!"non-orig {showst t} carried"
      (terms.all (fun t' => !carriedBy t t'))
  -- lenCheck
  let lenCheck (p : Option Int × Term) : Except String Unit :=
    match p with
    | (none, _) => .ok ()
    | (some len, _) =>
        if len >= role.rtrace.length then
          .error s!"invalid position {len}"
        else .ok ()
  for pa in role.rnon do lenCheck pa
  for pa in role.rpnon do lenCheck pa
  -- uniqueCheck
  for t in role.runique do
    failwith s!"uniq-orig {showst t} doesn't originate"
      (originates t role.rtrace)
  -- uniqgenCheck
  for t in role.runiqgen do
    failwith s!"uniq-gen {showst t} doesn't generate"
      (generates t role.rtrace)
  -- origVarCheck
  for v in role.rvars do
    failwith s!"variable {showst v} not acquired"
      (!isAcquiredVar v || (acquiredPos v role.rtrace).isSome)
  -- channel checks
  for ch in role.rconf do
    checkChanDecl "conf" role ch
  for ch in role.rauth do
    checkChanDecl "auth" role ch
  failwith "role trace is a prefix of a listener"
    (notListenerPrefix role.rtrace)
  failwith "role trace has multiple loads or stors on same locn"
    (locnsUnique role.rtrace)

-- ── Trace utilities ───────────────────────────────────────────────────────────

/-- Given a trace, return the indices of state transitions.
    Mirrors `transitionIndices :: Trace -> [(Int, Int)]`. -/
private def transitionIndices (c : Trace) : List (Int × Int) :=
  let rec subseqSend (j : Int) (ch : Term) : Trace → Option Int
    | [] => none
    | .In _ :: c' => subseqSend (j + 1) ch c'
    | .Out (.ChMsg ch' _) :: c' =>
        if ch == ch' then some j
        else if isLocn ch' then subseqSend (j + 1) ch c'
        else none
    | _ :: _ => none
  let rec loop (soFar : List (Int × Int)) (i : Int) : Trace → List (Int × Int)
    | [] => soFar.reverse
    | .Out (.ChMsg ch _) :: c' =>
        if isLocn ch then loop ((i, i) :: soFar) (i + 1) c'
        else loop soFar (i + 1) c'
    | .In (.ChMsg ch _) :: c' =>
        if isLocn ch then
          match subseqSend (i + 1) ch c' with
          | some j => loop ((i, j) :: soFar) (i + 1) c'
          | none   => loop soFar (i + 1) c'
        else loop soFar (i + 1) c'
    | _ :: c' => loop soFar (i + 1) c'
  loop [] 0 c

-- ── stateSegments helpers (mutual partial) ───────────────────────────────────

mutual

partial def stateSegs_findLower
    (soFar : List (Int × Int)) (i j : Int) : Trace → List (Int × Int)
  | .In (.ChMsg ch _) :: c' =>
      if isLocn ch then stateSegs_findLower soFar i (j + 1) c'
      else stateSegs_findSegments ((i, j - 1) :: soFar) (j + 1) c'
  | .In _ :: c' => stateSegs_findSegments ((i, j - 1) :: soFar) (j + 1) c'
  | c'@(.Out _ :: _) => stateSegs_findUpper soFar i j c'
  | [] => (i, j - 1) :: soFar

partial def stateSegs_findUpper
    (soFar : List (Int × Int)) (i j : Int) : Trace → List (Int × Int)
  | .Out (.ChMsg ch _) :: c' =>
      if isLocn ch then stateSegs_findUpper soFar i (j + 1) c'
      else stateSegs_findSegments ((i, j - 1) :: soFar) (j + 1) c'
  | .Out _ :: c' => stateSegs_findSegments ((i, j - 1) :: soFar) (j + 1) c'
  | c'@(.In _ :: _) => stateSegs_findSegments ((i, j - 1) :: soFar) j c'
  | [] => (i, j - 1) :: soFar

partial def stateSegs_findSegments
    (soFar : List (Int × Int)) (i : Int) : Trace → List (Int × Int)
  | [] => soFar
  | .In (.ChMsg ch _) :: c' =>
      if isLocn ch then stateSegs_findLower soFar i (i + 1) c'
      else stateSegs_findSegments soFar (i + 1) c'
  | .Out (.ChMsg ch _) :: c' =>
      if isLocn ch then stateSegs_findUpper soFar i (i + 1) c'
      else stateSegs_findSegments soFar (i + 1) c'
  | _ :: c' => stateSegs_findSegments soFar (i + 1) c'

end

/-- Compute state segments from a trace.
    Mirrors `stateSegments :: Trace -> [(Int,Int)]`. -/
private def stateSegments (c : Trace) : List (Int × Int) :=
  stateSegs_findSegments [] 0 c

/-- Load a list of critical-section index pairs.
    Mirrors `loadCritSecs :: MonadFail m => [SExpr Pos] -> m [(Int,Int)]`. -/
private def loadCritSecs (xs : List (SExpr Pos)) : Except String (List (Int × Int)) :=
  xs.foldlM (fun acc x =>
    match x with
    | .lst pos [.num _ i, .num _ j] =>
        if j < i then .error s!"{pos}loadCritSecs:  Bad int pair out of order"
        else .ok (acc ++ [(i, j)])
    | _ => .error s!"loadCritSecs:  Malformed int pairs") []

-- ── badGroupMemberOccurrences / badOrigNotGen ─────────────────────────────────

/-- Check for group variables that first appear in an In event when they
    should first appear in an Out (for rndxs) or vice versa.
    Mirrors `badGroupMemberOccurrences :: [Term] -> Trace -> Maybe ([Term], Int)`. -/
private def badGroupMemberOccurrences (vars : List Term) (events : Trace)
    : Option (List Term × Int) :=
  let groupVars := vars.filter isVarExpr
  let checkGroupVar (e : Event) (v : Term) : Bool :=
    match e with
    | .Out _ => isRndx v
    | .In _ => true  -- IMPORTANT: per Haskell comment, not enforced
  let rec loop (gvs : List Term) (evts : Trace) (i : Int)
      : Option (List Term × Int) :=
    match evts with
    | [] => none
    | e :: rest =>
        let (fsts, remaining) := gvs.partition (fun v => occursIn v (evtTerm e))
        match fsts.filter (fun v => !checkGroupVar e v) with
        | []  => loop remaining rest (i + 1)
        | bad => some (bad, i)
  loop groupVars events 0

/-- Identify group variables that originate (first carried out) but do not
    generate (first occur in).
    Mirrors `badOrigNotGen :: [Term] -> Trace -> [(Term,Int)]`. -/
private def badOrigNotGen (vars : List Term) (events : Trace) : List (Term × Int) :=
  let groupVars := vars.filter isVarExpr
  groupVars.filterMap (fun v =>
    if originates v events && !generates v events then
      firstOccursPos v events |>.map (fun p => (v, p))
    else none)

-- ── loadChan / loadLocn ───────────────────────────────────────────────────────

/-- Load a channel term from an S-expression.
    Mirrors `loadChan :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term`. -/
private def loadChan (sig : Sig) (vars : List Term) (x : SExpr Pos)
    : Except String Term := do
  let ch ← loadTerm sig vars false x
  if isChan ch then .ok ch
  else .error s!"{x.annotation}Expecting a channel"

/-- Load a location term from an S-expression.
    Mirrors `loadLocn :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term`. -/
private def loadLocn (sig : Sig) (vars : List Term) (x : SExpr Pos)
    : Except String Term := do
  let ch ← loadTerm sig vars false x
  if isLocn ch then .ok ch
  else .error s!"{x.annotation}Expecting a location"

-- ── loadBaseTerms / loadPosBaseTerms ──────────────────────────────────────────

/-- Load a single base (atom) term.
    Mirrors `loadBaseTerm`. -/
private def loadBaseTerm (sig : Sig) (vars : List Term) (x : SExpr Pos)
    : Except String Term := do
  let t ← loadTerm sig vars true x
  if isAtom t then .ok t
  else .error s!"{x.annotation}Expecting an atom"

/-- Load a list of base terms.
    Mirrors `loadBaseTerms`. -/
private def loadBaseTerms (sig : Sig) (vars : List Term) (xs : List (SExpr Pos))
    : Except String (List Term) :=
  xs.foldrM (fun x acc => do
    let t ← loadBaseTerm sig vars x
    .ok (adjoin t acc)) []

/-- Load a single base term with optional position.
    Mirrors `loadPosBaseTerm`. -/
private def loadPosBaseTerm (sig : Sig) (vars : List Term) (x : SExpr Pos)
    : Except String (Option Int × Term) :=
  match x with
  | .lst _ [.num _ opos, inner] =>
      if opos < 0 then
        .error s!"{x.annotation}Expecting a non-negative non-origination position"
      else do
        let t ← loadBaseTerm sig vars inner
        .ok (some opos, t)
  | _ => do
      let t ← loadTerm sig vars true x
      if isAtom t then .ok (none, t)
      else .error s!"{x.annotation}Expecting an atom"

/-- Load a list of positional base terms.
    Mirrors `loadPosBaseTerms`. -/
private def loadPosBaseTerms (sig : Sig) (vars : List Term) (xs : List (SExpr Pos))
    : Except String (List (Option Int × Term)) :=
  xs.mapM (loadPosBaseTerm sig vars)

/-- Load an absent pair: (var-expr-term, expr-term).
    Mirrors `loadAbsent`. -/
private def loadAbsent (sig : Sig) (vars : List Term) (x : SExpr Pos)
    : Except String (Term × Term) :=
  match x with
  | .lst _ [a, b] => do
      let x ← do
        let t ← loadTerm sig vars true a
        if isVarExpr t then .ok t
        else .error s!"{a.annotation}Expecting an exponent variable"
      let y ← do
        let t ← loadTerm sig vars false b
        if isExpr t then .ok t
        else .error s!"{b.annotation}Expecting an exponent"
      .ok (x, y)
  | _ => .error s!"{x.annotation}Expecting a pair of terms"

-- ── loadTrace ────────────────────────────────────────────────────────────────

/-- Load a role trace from S-expressions.
    Mirrors `loadTrace :: MonadFail m => Sig -> String -> Gen -> [Term]
                        -> [SExpr Pos] -> m (Gen, [Term], [Term], PreRules, Trace)`. -/
private def loadTrace (sig : Sig) (name : String) (gen : Gen) (vars : List Term)
    (xs : List (SExpr Pos))
    : Except String (Gen × List Term × List Term × PreRules × Trace) :=
  let rec loadTraceLoop (gen : Gen) (newVars uniqs : List Term) (pr : PreRules)
      (events : List Event) (rest : List (SExpr Pos))
      : Except String (Gen × List Term × List Term × PreRules × Trace) :=
    match rest with
    | [] =>
        let events' := events.reverse
        match badGroupMemberOccurrences vars events' with
        | some (_, i) =>
            .error s!"Expts must first be received, rndxs first sent:  at event {i} in role {name}"
        | none =>
            match badOrigNotGen vars events' with
            | (v, p) :: _ =>
                .error s!"Var received non-carried in role {name}, then sent carried:  {showst v} at event {p}"
            | [] =>
                .ok (gen, vars ++ newVars.reverse, uniqs.reverse, pr, events')
    -- recv (plain)
    | .lst _ [.sym _ "recv", t] :: more => do
        let t ← loadTerm sig vars false t
        loadTraceLoop gen newVars uniqs pr (.In (.Plain t) :: events) more
    -- send (plain)
    | .lst _ [.sym _ "send", t] :: more => do
        let t ← loadTerm sig vars true t
        loadTraceLoop gen newVars uniqs pr (.Out (.Plain t) :: events) more
    -- recv (channel)
    | .lst _ [.sym _ "recv", ch, t] :: more => do
        let ch ← loadChan sig vars ch
        let t  ← loadTerm sig vars false t
        loadTraceLoop gen newVars uniqs pr (.In (.ChMsg ch t) :: events) more
    -- send (channel)
    | .lst _ [.sym _ "send", ch, t] :: more => do
        let ch ← loadChan sig vars ch
        let t  ← loadTerm sig vars true t
        loadTraceLoop gen newVars uniqs pr (.Out (.ChMsg ch t) :: events) more
    -- load (state)
    | .lst _ [.sym pos "load", ch, t] :: more => do
        let ch ← loadLocn sig vars ch
        let t  ← loadTerm sig vars false t
        let (gen', pt, pt_t) ← loadLocnTerm sig gen (.sym pos "pt") (.sym pos "pval") t
        loadTraceLoop gen' (pt :: newVars) uniqs pr
          (.In (.ChMsg ch pt_t) :: events) more
    -- stor (state)
    | .lst _ [.sym pos "stor", ch, t] :: more => do
        let ch ← loadLocn sig vars ch
        let t  ← loadTerm sig vars true t
        let (gen', pt, pt_t) ← loadLocnTerm sig gen (.sym pos "pt") (.sym pos "pval") t
        loadTraceLoop gen' (pt :: newVars) (pt :: uniqs) pr
          (.Out (.ChMsg ch pt_t) :: events) more
    -- rely
    | .lst _ [.sym pos "rely", form] :: more =>
        match events with
        | [] => .error s!"{pos}Rely precedes first event in role {name}:  {form}"
        | .In _ :: _ =>
            loadTraceLoop gen newVars uniqs
              (preRulesAddRely pr (events.length, form))
              events more
        | _ => .error s!"{pos}Rely must follow recv or load in role {name}:  {form}"
    -- guar
    | .lst _ [.sym pos "guar", form] :: more =>
        match more with
        | [] => .error s!"{pos}Guarantee follows last event in role {name}:  {form}"
        | .lst _ (.sym _ "stor" :: _) :: _ =>
            loadTraceLoop gen newVars uniqs
              (preRulesAddGuar pr (1 + events.length, form))
              events more
        | .lst _ (.sym _ "send" :: _) :: _ =>
            loadTraceLoop gen newVars uniqs
              (preRulesAddGuar pr (1 + events.length, form))
              events more
        | _ => .error s!"{pos}Guarantee must precede send or stor in role {name}:  {form}"
    -- cheq
    | .lst _ [.sym pos "cheq", src, tgt] :: more =>
        match more with
        | [] => .error s!"{pos}cheq must precede some event in role {name}:  {src}, {tgt}"
        | _ => do
            let src ← loadTerm sig vars false src
            let tgt ← loadTerm sig vars false tgt
            loadTraceLoop gen newVars uniqs
              (preRulesAddCheq pr (1 + events.length, pos, src, tgt))
              events more
    -- unrecognized direction
    | .lst _ [.sym pos dir, _, _] :: _ =>
        .error s!"{pos}Unrecognized direction in role {name} {dir}"
    -- malformed event
    | x :: _ => .error s!"{x.annotation}Malformed event in role {name}"
  loadTraceLoop gen [] [] emptyPreRules [] xs

-- ── loadRolePriority ─────────────────────────────────────────────────────────

/-- Load one role priority entry.
    Mirrors `loadRolePriority :: MonadFail m => Int -> SExpr Pos -> m (Int, Int)`. -/
private def loadRolePriority (n : Int) (x : SExpr Pos) : Except String (Int × Int) :=
  match x with
  | .lst _ [.num _ i, .num _ p] =>
      if 0 <= i && i < n then .ok (i, p)
      else .error s!"{x.annotation}Malformed priority"
  | _ => .error s!"{x.annotation}Malformed priority"

-- ── loadLang ─────────────────────────────────────────────────────────────────

/-- Optionally load a `lang` field and update the signature.
    Mirrors `loadLang :: MonadFail m => Pos -> Sig -> [SExpr Pos] -> m Sig`. -/
private def loadLang (pos : Pos) (sig : Sig) (xs : List (SExpr Pos)) : Except String Sig :=
  if hasKey "lang" xs then loadSig pos (assoc "lang" xs)
  else .ok sig

-- ── mkListenerRole ───────────────────────────────────────────────────────────

/-- Create the listener role (the only role with an empty name).
    Mirrors `mkListenerRole :: MonadFail m => Sig -> Pos -> Gen -> m (Gen, Role)`. -/
private def mkListenerRole (sig : Sig) (pos : Pos) (g : Gen) : Except String (Gen × Role) := do
  let (g', xs) ← loadVars sig g [.lst pos [.sym pos "x", .sym pos "mesg"]]
  match xs with
  | [x] =>
      .ok (g', mkRole "" [x] [.In (.Plain x), .Out (.Plain x)]
             [] [] [] [] [] [] [] [] [] false)
  | _ => .error s!"{pos}mkListenerRole: expecting one variable"

-- ── hasLocn ──────────────────────────────────────────────────────────────────

/-- True if the role uses any location channel.
    Mirrors `hasLocn :: Role -> Bool`. -/
private def hasLocn (rl : Role) : Bool :=
  (tchans rl.rtrace).any isLocn

-- ── varsUsedBy ───────────────────────────────────────────────────────────────

/-- Check that all `vars` are bound in role `rl` by height `bound`.
    Mirrors `varsUsedBy :: MonadFail m => Role -> [Term] -> Int -> Pos -> m ()`. -/
private def varsUsedBy (rl : Role) (vars : List Term) (bound : Int) (pos : Pos)
    : Except String Unit :=
  match varsUsedHeight rl vars with
  | .missing v =>
      .error s!"{pos} var {varName v} not bound by height {bound}"
  | .foundAt ht =>
      if ht <= bound then .ok ()
      else .error s!"{pos} variables not bound until height {ht}"

-- ── iterPreRules ─────────────────────────────────────────────────────────────

/-- Fold a PreRules-consuming function over all (Role, PreRules) pairs.
    Mirrors `iterPreRules`. -/
private def iterPreRules
    (f : Sig → Gen → Prot → Role → PreRules → Except String (Gen × List Rule))
    (sig : Sig) (gen : Gen) (prot : Prot) (rlPreRules : List (Role × PreRules))
    : Except String (Gen × List Rule) :=
  rlPreRules.foldrM (fun (rl, prs) (g, rules) => do
    let (g', newRules) ← f sig g prot rl prs
    .ok (g', newRules ++ rules)) (gen, [])

-- ── initPreRule* ─────────────────────────────────────────────────────────────

private def initPreRuleCS (sig : Sig) (gen : Gen) (_ : Prot) (rl : Role)
    (pr : PreRules) : Except String (Gen × List Rule) :=
  .ok (csRules sig gen rl pr.preruleCs)

private def initPreRulesTrans (sig : Sig) (gen : Gen) (_ : Prot) (rl : Role)
    (pr : PreRules) : Except String (Gen × List Rule) :=
  .ok (transRls sig gen rl pr.preruleTrans)

private def initPreRulesFacts (sig : Sig) (gen : Gen) (_ : Prot) (rl : Role)
    (pr : PreRules) : Except String (Gen × List Rule) := do
  let facts ← loadFactList sig rl.rvars pr.preruleFacts
  .ok (genFactRls sig gen rl facts)

private def initPreRulesGensts (sig : Sig) (gen : Gen) (_ : Prot) (rl : Role)
    (pr : PreRules) : Except String (Gen × List Rule) := do
  let ts ← loadTerms sig rl.rvars pr.preruleGensts
  .ok (genStateRls sig gen rl ts)

private def initPreRulesAssumes (sig : Sig) (gen : Gen) (prot : Prot) (rl : Role)
    (pr : PreRules) : Except String (Gen × List Rule) := do
  let ((g, rls), _) ← pr.preruleAssumes.foldrM
    (fun (sexpr : SExpr Pos) (state : (Gen × List Rule) × Int) => do
      let ((g, rules), n) := state
      let (g', varConjs) ← loadConclusion sig sexpr.annotation prot g rl.rvars sexpr
      let (g'', newRule) := genOneAssumeRl sig g' rl n varConjs
      pure ((g'', newRule :: rules), n + 1))
    ((gen, []), 0)
  .ok (g, rls)

private def initRelyGuars (sig : Sig) (gen : Gen) (prot : Prot) (rl : Role)
    (kind : String) (pairs : List (Int × SExpr Pos))
    : Except String (Gen × List Rule) :=
  pairs.foldrM (fun (ht, sexpr) (g, rules) => do
    let (g', varConjs) ← loadConclusion sig sexpr.annotation prot g rl.rvars sexpr
    varsUsedBy rl (freeVarsInConjLists varConjs) ht sexpr.annotation
    let (g'', newRule) := genOneRelyGuarRl sig g' rl ht kind varConjs
    .ok (g'', newRule :: rules)) (gen, [])

private def initPreRulesRelies (sig : Sig) (gen : Gen) (prot : Prot) (rl : Role)
    (pr : PreRules) : Except String (Gen × List Rule) :=
  initRelyGuars sig gen prot rl "rely" pr.preruleRelies

private def initPreRulesGuars (sig : Sig) (gen : Gen) (prot : Prot) (rl : Role)
    (pr : PreRules) : Except String (Gen × List Rule) :=
  initRelyGuars sig gen prot rl "guar" pr.preruleGuars

private def initPreRulesCheqs (sig : Sig) (gen : Gen) (_ : Prot) (rl : Role)
    (pr : PreRules) : Except String (Gen × List Rule) :=
  pr.preruleCheqs.foldrM (fun (ht, pos, v, t) (g, rules) => do
    varsUsedBy rl (varsInTerms [t]) ht pos
    let (g', newRule) := genOneRelyGuarRl sig g rl ht "cheq"
      [([], [(pos, .Equals v t)])]
    .ok (g', newRule :: rules)) (gen, [])

-- ── initRules ────────────────────────────────────────────────────────────────

/-- Build all initial protocol rules from per-role PreRules data.
    Mirrors `initRules :: MonadFail m => Sig -> Gen -> Prot -> [(Role,PreRules)]
             -> m (Gen, [Rule], [Rule])`. -/
private def initRules (sig : Sig) (g : Gen) (prot : Prot)
    (prs : List (Role × PreRules)) : Except String (Gen × List Rule × List Rule) := do
  let anyState := prs.any (fun (rl, _) => hasLocn rl)
  let (g', neqs) := neqRules sig g
  let (g, fixedStateRls) :=
    if anyState then
      [scissorsRule sig, cakeRule sig, uninterruptibleRule sig,
       shearsRule sig, invShearsRule sig].foldr
        (fun f (g, rules) => let (g', r) := f g; (g', r :: rules)) (g', [])
    else (g', [])
  let (g, fcRls) ← iterPreRules initPreRulesFacts sig g prot prs
  let (g, asRls) ← iterPreRules initPreRulesAssumes sig g prot prs
  let (g, rlRls) ← iterPreRules initPreRulesRelies sig g prot prs
  let (g, grRls) ← iterPreRules initPreRulesGuars sig g prot prs
  let (g, cqRls) ← iterPreRules initPreRulesCheqs sig g prot prs
  let (g, trRls) ← iterPreRules initPreRulesTrans sig g prot prs
  let (g, csRls) ← iterPreRules initPreRuleCS sig g prot prs
  let (g, gsRls) ← iterPreRules initPreRulesGensts sig g prot prs
  .ok (g,
       neqs ++ fixedStateRls ++ fcRls ++ asRls ++ trRls ++ csRls ++ gsRls,
       rlRls ++ grRls ++ cqRls)

-- ── loadRole ─────────────────────────────────────────────────────────────────

/-- Load a single role from its S-expression body.
    Mirrors `loadRole :: MonadFail m => Sig -> Gen -> Pos -> [SExpr Pos]
             -> m (Gen, Role, PreRules)`. -/
private def loadRole (sig : Sig) (gen : Gen) (pos : Pos) (xs : List (SExpr Pos))
    : Except String (Gen × Role × PreRules) :=
  match xs with
  | .sym _ name :: .lst _ (.sym _ "vars" :: varDecls) ::
    .lst _ (.sym _ "trace" :: evt :: c) :: rest => do
      let (gen, vars) ← loadVars sig gen varDecls
      let (gen, vars', pt_u, pr_t, c') ←
          loadTrace sig name gen vars (evt :: c)
      let n   ← loadPosBaseTerms sig vars' (assoc "non-orig"     rest)
      let a   ← loadPosBaseTerms sig vars' (assoc "pen-non-orig" rest)
      let u   ← loadBaseTerms    sig vars' (assoc "uniq-orig"    rest)
      let gts ← loadBaseTerms    sig vars' (assoc "uniq-gen"     rest)
      let b   ← (assoc "absent" rest).mapM (loadAbsent sig vars')
      let d   ← loadBaseTerms    sig vars' (assoc "conf"         rest)
      let h   ← loadBaseTerms    sig vars' (assoc "auth"         rest)
      let cs  ← loadCritSecs (assoc "critical-sections" rest)
      let genstates := assoc "gen-st"  rest
      let facts     := assoc "facts"   rest
      let assumes   := assoc "assume"  rest
      let keys := ["non-orig", "pen-non-orig", "uniq-orig",
                   "uniq-gen", "absent", "conf", "auth"]
      let _comment ← alistComment keys rest
      let reverseSearch := hasKey "reverse-search" rest
      let ts := tterms c'
      let bs := b.flatMap (fun (x, y) => [x, y])
      if !termsWellFormed (n.map Prod.snd ++ a.map Prod.snd ++ u ++ gts ++ bs ++ ts) then
        .error s!"{pos}Terms in role not well formed"
      if !(d ++ h).all isChan then
        .error s!"{pos}Bad channel in role"
      let f v := ts.any (occursIn v) || (tchans c').any (· == v)
      let vs  := vars'.filter f
      let ns  := n.filter  (fun (_, t) => varsSeen vs t)
      let as' := a.filter  (fun (_, t) => varsSeen vs t)
      let us  := (u ++ pt_u).filter (varsSeen vs)
      let gs  := gts.filter (varsSeen vs)
      let prios ← (assoc "priority" rest).mapM (loadRolePriority c'.length)
      let stateSegs := stateSegments c'
      match cs with
      | [] => pure ()
      | _  => .error s!"{pos}Critical sections in role are no longer needed;  all state segments are now critical sections"
      let r := mkRole name vs c' ns as' us gs b d h [] prios reverseSearch
      let pr := { pr_t with
                  preruleCs      := stateSegs,
                  preruleTrans   := transitionIndices c',
                  preruleFacts   := facts,
                  preruleGensts  := genstates,
                  preruleAssumes := assumes }
      match roleWellFormed r with
      | .ok ()    => .ok (gen, r, pr)
      | .error msg => .error s!"{pos}Role not well formed: {msg}"
  | _ => .error s!"{pos}Malformed role"

-- ── loadRoles ────────────────────────────────────────────────────────────────

/-- Load all role definitions from the protocol body.
    Mirrors `loadRoles :: MonadFail m => Sig -> Gen -> [SExpr Pos]
             -> m (Gen, [(Role, PreRules)], [SExpr Pos])`. -/
private def loadRoles (sig : Sig) (gen : Gen) (xs : List (SExpr Pos))
    : Except String (Gen × List (Role × PreRules) × List (SExpr Pos)) :=
  match xs with
  | .lst pos (.sym _ "defrole" :: body) :: rest => do
      let (gen', r, pr) ← loadRole sig gen pos body
      let (gen'', rps, comment) ← loadRoles sig gen' rest
      .ok (gen'', (r, pr) :: rps, comment)
  | comment => .ok (gen, [], comment)

-- ── loadRule / loadRules ──────────────────────────────────────────────────────

/-- Load a single defrule.
    Mirrors `loadRule :: MonadFail m => Sig -> Prot -> Gen -> Pos
             -> [SExpr Pos] -> m (Gen, Rule)`. -/
private def loadRule (sig : Sig) (prot : Prot) (g : Gen) (pos : Pos)
    (xs : List (SExpr Pos)) : Except String (Gen × Rule) :=
  match xs with
  | .sym _ name :: x :: rest => do
      let (g', goal, _) ← loadSentence sig .UnusedVars pos prot g x
      let _comment ← alistComment [] rest
      .ok (g', { rlname := name, rlgoal := goal, rlcomment := [] })
  | _ => .error s!"{pos}Malformed rule"

/-- Load all defrule forms from the protocol body.
    Mirrors `loadRules :: MonadFail m => Sig -> Prot -> Gen -> [SExpr Pos]
             -> m (Gen, [Rule], [SExpr ()])`. -/
private def loadRules (sig : Sig) (prot : Prot) (g : Gen) (xs : List (SExpr Pos))
    : Except String (Gen × List Rule × List (SExpr Unit)) :=
  match xs with
  | .lst pos (.sym _ "defrule" :: body) :: rest => do
      let (g', r) ← loadRule sig prot g pos body
      let (g'', rs, comment) ← loadRules sig prot g' rest
      .ok (g'', r :: rs, comment)
  | .lst _ (.sym pos name :: _) :: _ =>
      if name == "defrole" then
        .error s!"{pos}defrole {name} misplaced"
      else do
        badKey ["defrole", "defrule"] xs
        let comment ← alistComment [] xs
        .ok (g, [], comment)
  | _ => do
      badKey ["defrole", "defrule"] xs
      let comment ← alistComment [] xs
      .ok (g, [], comment)

-- ── loadProt ─────────────────────────────────────────────────────────────────

/-- Validate that no two roles share the same name, and check for store-segment
    divergence.  Mirrors the `validate` local in `loadProt`. -/
private def validateProt (pos : Pos) (name : String) (prot : Prot)
    (rs : List Role) : Except String Prot :=
  match rs with
  | [] =>
      match checkForDivergenceInStoreSegments prot with
      | none => .ok prot
      | some (n, n', i) =>
          .error s!"checkForDivergenceInStoreSegments:  Roles {n} and {n'} agree up to step {i} but diverge in a store segment.   Distinguish them prior to second event in store segment"
  | r :: rest =>
      match rest.find? (fun r' => r.rname == r'.rname) with
      | some _ => .error s!"{pos}Duplicate role {r.rname} in protocol {name}"
      | none   => validateProt pos name prot rest

/-- Load a protocol from its S-expression body.
    Mirrors `loadProt :: MonadFail m => Sig -> String -> Gen -> Pos
             -> [SExpr Pos] -> m Prot`. -/
private def loadProt (sig : Sig) (_ : String) (origin : Gen) (pos : Pos)
    (xs : List (SExpr Pos)) : Except String Prot :=
  match xs with
  | .sym _ name :: .sym _ alg :: x :: rest => do
      -- PDR: These aren't needed because we check for a good alg
      --if alg != nom then
      --  .error s!"{pos}Expecting terms in algebra {nom}"
      let sig' ← loadLang pos sig rest
      let (gen, rolesAndPreRules, remaining) ← loadRoles sig' origin (x :: rest)
      let (gen', r) ← mkListenerRole sig' pos gen
      let rs := rolesAndPreRules.map Prod.fst
      let fakeProt := mkProt name alg gen' sig' rs r [] [] [] []
      let (gen'', forgettableRls, memorableRls) ← initRules sig' gen' fakeProt rolesAndPreRules
      let (gen''', newRls, comment) ← loadRules sig' fakeProt gen'' remaining
      let allRls := newRls ++ forgettableRls ++ memorableRls
      let writtenRls := newRls ++ memorableRls
      let generatedRls := forgettableRls
      let prot := mkProt name alg gen''' sig' rs r allRls writtenRls generatedRls comment
      validateProt pos name prot rs
  | _ => .error s!"{pos}Malformed protocol"

-- ── Preskel loading helpers ───────────────────────────────────────────────────

/-- Add origination data inherited from instances.
    Mirrors `addInstOrigs` in Loader.hs — NOTE: ordering is (nr, ar, ur, ug, ab, cn, au). -/
private def addInstOrigs
    (acc : List Term × List Term × List Term × List Term ×
           List (Term × Term) × List Term × List Term)
    (i : Instance)
    : List Term × List Term × List Term × List Term ×
      List (Term × Term) × List Term × List Term :=
  let (nr, ar, ur, ug, ab, cn, au) := acc
  ((inheritRnon i).foldl    (fun xs x => adjoin x xs) nr,
   (inheritRpnon i).foldl   (fun xs x => adjoin x xs) ar,
   (inheritRunique i).foldl  (fun xs x => adjoin x xs) ur,
   (inheritRuniqgen i).foldl (fun xs x => adjoin x xs) ug,
   (inheritRabsent i).foldl  (fun xs x => adjoin x xs) ab,
   (inheritRconf i).foldl    (fun xs x => adjoin x xs) cn,
   (inheritRauth i).foldl    (fun xs x => adjoin x xs) au)

/-- Load a maplet (domain → range environment entry).
    Mirrors `loadMaplet :: MonadFail m => Sig -> [Term] -> [Term]
             -> (Gen, Env) -> SExpr Pos -> m (Gen, Env)`. -/
private def loadMaplet (sig : Sig) (kvars vars : List Term) (env : Gen × Env)
    (x : SExpr Pos) : Except String (Gen × Env) :=
  match x with
  | .lst pos [domain, range] => do
      let t  ← loadTerm sig vars false domain
      let t' ← loadTerm sig kvars false range
      match termMatch t t' env with
      | env' :: _ => .ok env'
      | []        => .error s!"{pos}Domain does not match range"
  | _ => .error s!"{x.annotation}Malformed maplet"

/-- Load a defstrand instance.
    Mirrors `loadInst`. -/
private def loadInst (sig : Sig) (pos : Pos) (p : Prot) (kvars : List Term)
    (gen : Gen) (role : String) (height : Int) (env : List (SExpr Pos))
    : Except String (Gen × Instance) := do
  let r ← lookupRole pos p role
  if height < 1 || height > r.rtrace.length then
    .error s!"{pos}Bad height"
  let vars := r.rvars
  let (gen', env') ← env.foldlM (loadMaplet sig kvars vars) (gen, emptyEnv)
  .ok (mkInstance gen' r env' height)

/-- Load a defstrandmax instance (full-height defstrand).
    Mirrors `loadInstMax`. -/
private def loadInstMax (sig : Sig) (pos : Pos) (p : Prot) (kvars : List Term)
    (gen : Gen) (role : String) (env : List (SExpr Pos))
    : Except String (Gen × Instance) := do
  let r ← lookupRole pos p role
  let height := r.rtrace.length
  let vars := r.rvars
  let (gen', env') ← env.foldlM (loadMaplet sig kvars vars) (gen, emptyEnv)
  .ok (mkInstance gen' r env' height)

/-- Load a deflistener instance.
    Mirrors `loadListener`. -/
private def loadListener (sig : Sig) (p : Prot) (kvars : List Term)
    (gen : Gen) (x : SExpr Pos) : Except String (Gen × Instance) := do
  let t ← loadTerm sig kvars true x
  .ok (mkListener p gen t)

-- ── loadNode / loadPair / loadOrderings ──────────────────────────────────────

/-- Load a node from an S-expression `(strand pos)`.
    Mirrors `loadNode`. -/
private def loadNode (heights : List Int) (x : SExpr Pos) : Except String Node :=
  match x with
  | .lst pos [.num _ s, .num _ p] =>
      if s < 0 then .error s!"{pos}Negative strand in node"
      else if p < 0 then .error s!"{pos}Negative position in node"
      else
        let rec height : List Int → Int → Option Int
          | [],      _ => none
          | h :: _,  0 => some h
          | _ :: hs, n => height hs (n - 1)
        match height heights s with
        | none   => .error s!"{pos}Bad strand in node"
        | some h =>
            if p < h then .ok (s, p)
            else .error s!"{pos}Bad position in node"
  | _ => .error s!"{x.annotation}Malformed node"

/-- Load an ordering pair.
    Mirrors `loadPair`. -/
private def loadPair (heights : List Int) (x : SExpr Pos) : Except String Pair :=
  match x with
  | .lst _ [x0, x1] => do
      let n0 ← loadNode heights x0
      let n1 ← loadNode heights x1
      .ok (n0, n1)
  | _ => .error s!"{x.annotation}Malformed pair"

/-- Load a list of ordering pairs.
    Mirrors `loadOrderings`. -/
private def loadOrderings (heights : List Int) (xs : List (SExpr Pos))
    : Except String (List Pair) :=
  xs.foldlM (fun ns x => do
    let np ← loadPair heights x
    .ok (adjoin np ns)) []

-- ── loadFact / loadFterm ──────────────────────────────────────────────────────

/-- Load a fact term: strand index or algebra term.
    Mirrors `loadFterm`. -/
private def loadFterm (sig : Sig) (heights : List Int) (vars : List Term)
    (x : SExpr Pos) : Except String FTerm :=
  match x with
  | .num pos s =>
      if 0 <= s && s < heights.length then .ok (.FSid s)
      else .error s!"{pos}Bad strand in fact: {s}"
  | _ => do
      let t ← loadTerm sig vars false x
      .ok (.ofTerm t)

/-- Load a fact.
    Mirrors `loadFact`. -/
private def loadFact (sig : Sig) (heights : List Int) (vars : List Term)
    (x : SExpr Pos) : Except String Fact :=
  match x with
  | .lst _ (.sym _ name :: fs) => do
      let fs' ← fs.mapM (loadFterm sig heights vars)
      .ok { name := name, terms := fs' }
  | _ => .error s!"{x.annotation}Malformed fact"

-- ── loadPriorities ────────────────────────────────────────────────────────────

/-- Load a priority entry: (node, priority).
    Mirrors `loadPriorities`. -/
private def loadPriorities (heights : List Int) (x : SExpr Pos)
    : Except String (Node × Int) :=
  match x with
  | .lst _ [n, .num _ p] => do
      let nd ← loadNode heights n
      .ok (nd, p)
  | _ => .error s!"{x.annotation}Malformed priority"

-- ── loadGoals ────────────────────────────────────────────────────────────────

/-- Load a sequence of security goals.
    Mirrors `loadGoals :: MonadFail m => Sig -> Pos -> Prot -> Gen
             -> [SExpr Pos] -> m (Gen, [Goal])`. -/
private def loadGoals (sig : Sig) (pos : Pos) (prot : Prot) (g : Gen)
    (xs : List (SExpr Pos)) : Except String (Gen × List Goal) :=
  xs.foldlM (fun (g', goals) x => do
    let (g'', goal, _) ← loadSentence sig .RoleSpec pos prot g' x
    .ok (g'', goals ++ [goal])) (g, [])

-- ── loadRest ─────────────────────────────────────────────────────────────────

/-- Assemble the preskeleton from instances and skeleton-level annotations.
    Mirrors `loadRest :: MonadFail m => Sig -> Pos -> [Term] -> Prot -> Gen
             -> [Goal] -> [Instance] -> ...  -> m Preskel`. -/
private def loadRest (sig : Sig) (pos : Pos) (vars : List Term) (p : Prot)
    (gen : Gen) (gs : List Goal) (insts : List Instance)
    (orderings nr ar ur ug ab pr cn au fs pl leads genSts : List (SExpr Pos))
    (comment : List (SExpr Unit)) : Except String Preskel := do
  if insts.isEmpty then .error s!"{pos}No strands"
  let heights := insts.map (fun i => i.height)
  let o    ← loadOrderings heights orderings
  let nr'  ← loadBaseTerms sig vars nr
  let ar'  ← loadBaseTerms sig vars ar
  let ur'  ← loadBaseTerms sig vars ur
  let ug'  ← loadBaseTerms sig vars ug
  let ab'  ← ab.mapM (loadAbsent sig vars)
  let pr'  ← pr.mapM (loadNode heights)
  let cn'  ← loadBaseTerms sig vars cn
  let au'  ← loadBaseTerms sig vars au
  let fs'  ← fs.mapM (loadFact sig heights vars)
  let lds  ← loadOrderings heights leads
  let genSts' ← loadTerms sig vars genSts
  let (nr'', ar'', ur'', ug'', ab'', cn'', au'') :=
        insts.foldl addInstOrigs (nr', ar', ur', ug', ab', cn', au')
  let prios ← pl.mapM (loadPriorities heights)
  let k0 := mkPreskel gen p gs insts o nr'' ar'' ur'' ug'' ab'' pr' genSts' cn'' au'' fs' prios comment
  let ab_flat := ab''.flatMap (fun (x, y) => [x, y])
  let k := { k0 with pov := some k0 }
  if !termsWellFormed (nr'' ++ ar'' ++ ur'' ++ ug'' ++ ab_flat ++ kterms k) then
    .error s!"{pos}Terms in skeleton not well formed"
  if !(cn'' ++ au'').all isChan then
    .error s!"{pos}Bad channel in role"
  match verbosePreskelWellFormed k with
  | .ok ()    => .ok (applyLeadsTo k lds)
  | .error msg => .error s!"{pos}Skeleton not well formed: {msg}"

-- ── loadInsts ────────────────────────────────────────────────────────────────

/-- Load all strand instances from an S-expression list, then call loadRest.
    Mirrors `loadInsts :: MonadFail m => Sig -> Pos -> Prot -> [Term] -> Gen
             -> [Instance] -> [SExpr Pos] -> m Preskel`. -/
private def loadInsts (sig : Sig) (top : Pos) (p : Prot) (kvars : List Term)
    (gen : Gen) (insts : List Instance) (xs : List (SExpr Pos))
    : Except String Preskel :=
  match xs with
  | .lst pos (.sym _ "defstrand" :: body) :: rest =>
      match body with
      | .sym _ role :: .num _ height :: env => do
          let (gen', i) ← loadInst sig pos p kvars gen role height env
          loadInsts sig top p kvars gen' (i :: insts) rest
      | _ => .error s!"{pos}Malformed defstrand"
  | .lst pos (.sym _ "defstrandmax" :: body) :: rest =>
      match body with
      | .sym _ role :: env => do
          let (gen', i) ← loadInstMax sig pos p kvars gen role env
          loadInsts sig top p kvars gen' (i :: insts) rest
      | _ => .error s!"{pos}Malformed defstrandmax"
  | .lst pos (.sym _ "deflistener" :: body) :: rest =>
      match body with
      | [term] => do
          let (gen', i) ← loadListener sig p kvars gen term
          loadInsts sig top p kvars gen' (i :: insts) rest
      | _ => .error s!"{pos}Malformed deflistener"
  | xs => do
      badKey ["defstrand", "deflistener"] xs
      let _ ← alistComment [] xs  -- syntax check
      let (gen', gs) ← loadGoals sig top p gen (assoc "goals" xs)
      loadRest sig top kvars p gen' gs (insts.reverse)
        (assoc "precedes"  xs)
        (assoc "non-orig"  xs)
        (assoc "pen-non-orig" xs)
        (assoc "uniq-orig" xs)
        (assoc "uniq-gen"  xs)
        (assoc "absent"    xs)
        (assoc "precur"    xs)
        (assoc "conf"      xs)
        (assoc "auth"      xs)
        (assoc "facts"     xs)
        (assoc "priority"  xs)
        (assoc "leads-to"  xs)
        (assoc "gen-st"    xs)
        (loadComment "goals"   (assoc "goals"   xs) ++
         loadComment "comment" (assoc "comment" xs))

-- ── loadPreskel ──────────────────────────────────────────────────────────────

/-- Load a preskeleton from its S-expression body.
    Mirrors `loadPreskel :: MonadFail m => Sig -> Pos -> Prot -> [SExpr Pos] -> m Preskel`. -/
private def loadPreskel (sig : Sig) (pos : Pos) (p : Prot) (xs : List (SExpr Pos))
    : Except String Preskel :=
  match xs with
  | .lst _ (.sym _ "vars" :: varDecls) :: rest => do
      let (gen, kvars) ← loadVars sig p.pgen varDecls
      loadInsts sig pos p kvars gen [] rest
  | _ => .error s!"{pos}Malformed skeleton"

-- ── findPreskel / findGoal ────────────────────────────────────────────────────

/-- Find the named protocol and load a preskeleton.
    Mirrors `findPreskel :: MonadFail m => Pos -> [Prot] -> [SExpr Pos] -> m Preskel`. -/
private def findPreskel (pos : Pos) (ps : List Prot) (xs : List (SExpr Pos))
    : Except String Preskel :=
  match xs with
  | .sym _ name :: rest =>
      match ps.find? (fun p => name == p.pname) with
      | none   => .error s!"{pos}Protocol {name} unknown"
      | some p => loadPreskel p.psig pos p rest
  | _ => .error s!"{pos}Malformed skeleton"

/-- Find the named protocol and load a security-goal preskeleton.
    Mirrors `findGoal :: MonadFail m => Pos -> [Prot] -> [SExpr Pos] -> m Preskel`. -/
private def findGoal (pos : Pos) (ps : List Prot) (xs : List (SExpr Pos))
    : Except String Preskel :=
  match xs with
  | .sym _ name :: x :: rest =>
      match ps.find? (fun p => name == p.pname) with
      | none   => .error s!"{pos}Protocol {name} unknown"
      | some p => do
          let sig := p.psig
          let (g, goal, antec) ← loadSentence sig .RoleSpec pos p p.pgen x
          let (gs, xs') := findAlist rest
          let (g', goals) ← loadGoals sig pos p g gs
          let _ ← alistComment [] xs'  -- syntax check
          let kcomment :=
            loadComment "goals"   (x :: gs) ++
            loadComment "comment" (assoc "comment" xs')
          characteristic pos p (goal :: goals) g' antec kcomment
  | _ => .error s!"{pos}Malformed goal"

-- ── loadSExpr / loadSExprs ────────────────────────────────────────────────────

/-- Load one top-level S-expression form.
    Mirrors `loadSExpr`. -/
private def loadSExpr (sig : Sig) (nom : String) (origin : Gen)
    (state : List Prot × List Preskel) (x : SExpr Pos)
    : Except String (List Prot × List Preskel) :=
  let (ps, ks) := state
  match x with
  | .lst pos (.sym _ "defprotocol" :: xs) => do
      let p ← loadProt sig nom origin pos xs
      .ok (p :: ps, ks)
  | .lst pos (.sym _ "defskeleton" :: xs) => do
      let k ← findPreskel pos ps xs
      .ok (ps, k :: ks)
  | .lst pos (.sym _ "defgoal" :: xs) => do
      let k ← findGoal pos ps xs
      .ok (ps, k :: ks)
  | .lst _ (.sym _ "comment" :: _) => .ok (ps, ks)
  | .lst _ (.sym _ "herald"  :: _) => .ok (ps, ks)
  | _ => .error s!"{x.annotation}Malformed input"

/-- Load all top-level forms and return the list of preskeletons.
    Mirrors `loadSExprs :: MonadFail m => Sig -> String -> Gen
             -> [SExpr Pos] -> m [Preskel]`. -/
def loadSExprs (sig : Sig) (nom : String) (origin : Gen)
    (xs : List (SExpr Pos)) : Except String (List Preskel) := do
  let (_, ks) ← xs.foldlM (loadSExpr sig nom origin) ([], [])
  .ok ks.reverse

end LeanCPSA.Loader
