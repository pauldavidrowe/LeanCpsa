/-
Cpsa2Lean.Protocol

Port of CPSA.Protocol (MITRE cpsa v4.4.8).
This file is built in six stages; each stage is delimited by a header comment.

Stage 1: Event type and basic operations.
Stage 2: Trace position functions.
Stage 3: Role structure and mkRole.
Stage 4: Divergence analysis.
Stage 5: AForm, Goal, Conj, and formula operations.
Stage 6: Rule classification and Protocol structure. [TODO]
-/

import Cpsa2Lean.Algebra
import Cpsa2Lean.Channel
import Cpsa2Lean.Lib.SExpr
import Cpsa2Lean.Lib.RBMap
import Cpsa2Lean.Lib.Utilities

namespace Cpsa2Lean.Protocol

open Cpsa2Lean.Algebra
open Cpsa2Lean.Channel
open Cpsa2Lean.Lib (adjoin nats union RBSet)

-- ════════════════════════════════════════════════════════════════════════════
-- Stage 1: Event type and basic operations
-- ════════════════════════════════════════════════════════════════════════════

-- ── Variable utilities ────────────────────────────────────────────────────────

/-- Accumulate into `ts` every variable that appears in `t`.
    Mirrors `addVars :: [Term] -> Term -> [Term]`. -/
def addVars (ts : List Term) (t : Term) : List Term :=
  foldVars (fun acc v => adjoin v acc) ts t

/-- Collect all variables appearing in any term in `ts`.
    Mirrors `varsInTerms :: [Term] -> [Term]`. -/
def varsInTerms (ts : List Term) : List Term :=
  ts.foldl addVars []

/-- True when every variable of `ts` also appears in `ts'`.
    Mirrors `varSubset :: [Term] -> [Term] -> Bool`. -/
def varSubset (ts ts' : List Term) : Bool :=
  (varsInTerms ts).all (varsInTerms ts').contains

-- ── Event ─────────────────────────────────────────────────────────────────────

/-- A protocol event: an inbound or outbound channel message.
    Mirrors `data Event = In !ChMsg | Out !ChMsg`. -/
inductive Event where
  | In  : ChMsg → Event
  | Out : ChMsg → Event
  deriving Repr

instance : BEq Event where
  beq
    | .In  t, .In  t' => t == t'
    | .Out t, .Out t' => t == t'
    | _,      _       => false

instance : Ord Event where
  compare
    | .In  t, .In  t' => compare t t'
    | .In  _, .Out _  => .lt
    | .Out _, .In  _  => .gt
    | .Out t, .Out t' => compare t t'

-- ── Trace ─────────────────────────────────────────────────────────────────────

/-- A trace is a list of events in causal order.
    Mirrors `type Trace = [Event]`. -/
abbrev Trace := List Event

-- ── Event accessors ───────────────────────────────────────────────────────────

/-- Extract the channel message from an event.
    Mirrors `evtCm :: Event -> ChMsg`. -/
def evtCm : Event → ChMsg
  | .In  t => t
  | .Out t => t

/-- Dispatch on direction, applying the chosen function to the payload term.
    Mirrors `evt :: (Term -> a) -> (Term -> a) -> Event -> a`. -/
def evt {α : Type} (inDir outDir : Term → α) : Event → α
  | .In  t => inDir  (cmTerm t)
  | .Out t => outDir (cmTerm t)

/-- Extract the payload term from an event.
    Mirrors `evtTerm :: Event -> Term`. -/
def evtTerm : Event → Term
  | .In  t => cmTerm t
  | .Out t => cmTerm t

/-- Extract the channel component from an event, if any.
    Mirrors `evtChan :: Event -> Maybe Term`. -/
def evtChan : Event → Option Term
  | .In  t => cmChan t
  | .Out t => cmChan t

/-- Apply `f` to the terms inside the channel message of an event.
    Mirrors `evtMap :: (Term -> Term) -> Event -> Event`. -/
def evtMap (f : Term → Term) : Event → Event
  | .In  t => .In  (cmMap f t)
  | .Out t => .Out (cmMap f t)

/-- Extract the channel message if the event is inbound.
    Mirrors `inbnd :: Event -> Maybe ChMsg`. -/
def inbnd : Event → Option ChMsg
  | .In t => some t
  | _     => none

/-- Extract the channel message if the event is outbound.
    Mirrors `outbnd :: Event -> Maybe ChMsg`. -/
def outbnd : Event → Option ChMsg
  | .Out t => some t
  | _      => none

-- ── Event classifiers ─────────────────────────────────────────────────────────

/-- True when the event is a location load (inbound channel-message with a location channel).
    Mirrors `evtIsLoad :: Event -> Bool`. -/
def evtIsLoad : Event → Bool
  | .In (.ChMsg ch _) => isLocn ch
  | _                 => false

/-- True when the event is a location store (outbound channel-message with a location channel).
    Mirrors `evtIsStor :: Event -> Bool`. -/
def evtIsStor : Event → Bool
  | .Out (.ChMsg ch _) => isLocn ch
  | _                  => false

/-- True when the event is a state event (load or store).
    Mirrors `evtIsState :: Event -> Bool`. -/
def evtIsState (e : Event) : Bool :=
  evtIsLoad e || evtIsStor e

-- ── Trace basics ──────────────────────────────────────────────────────────────

/-- The set of payload terms occurring in a trace.
    Mirrors `tterms :: Trace -> [Term]`. -/
def tterms (c : Trace) : List Term :=
  c.foldl (fun ts e => adjoin (evtTerm e) ts) []

/-- The distinct channels referenced in a trace.
    Mirrors `tchans :: Trace -> [Term]`. -/
def tchans (c : Trace) : List Term :=
  (c.filterMap evtChan).eraseDups

-- ════════════════════════════════════════════════════════════════════════════
-- Stage 2: Trace position functions
-- ════════════════════════════════════════════════════════════════════════════

-- ── originates / originationPos ───────────────────────────────────────────────

/-- True when `t` is first carried by an outbound event (i.e. originates here).
    Mirrors `originates :: Term -> Trace -> Bool`. -/
def originates (t : Term) : Trace → Bool
  | []            => false
  | .Out t' :: c  => carriedBy t (cmTerm t') || originates t c
  | .In  t' :: c  => !carriedBy t (cmTerm t') && originates t c

private def originationPos_loop (t : Term) : Int → Trace → Option Int
  | _,   []           => none
  | pos, .Out t' :: c =>
      if carriedBy t (cmTerm t') then some pos
      else originationPos_loop t (pos + 1) c
  | pos, .In  t' :: c =>
      if carriedBy t (cmTerm t') then none
      else originationPos_loop t (pos + 1) c

/-- Position at which `t` originates in the trace, or `none`.
    Mirrors `originationPos :: Term -> Trace -> Maybe Int`. -/
def originationPos (t : Term) (c : Trace) : Option Int :=
  originationPos_loop t 0 c

-- ── generates / generationPos ─────────────────────────────────────────────────

/-- True when `t` is first a constituent of an outbound event.
    Mirrors `generates :: Term -> Trace -> Bool`. -/
def generates (t : Term) : Trace → Bool
  | []            => false
  | .Out t' :: c  => constituent t (cmTerm t') || generates t c
  | .In  t' :: c  => !constituent t (cmTerm t') && generates t c

private def generationPos_loop (t : Term) (maybeInv : Option Term) : Int → Trace → Option Int
  | _,   []           => none
  | pos, .Out t' :: c =>
      let ct := cmTerm t'
      if constituent t ct || (maybeInv.map (constituent · ct)).getD false then some pos
      else generationPos_loop t maybeInv (pos + 1) c
  | pos, .In  t' :: c =>
      let ct := cmTerm t'
      if constituent t ct || (maybeInv.map (constituent · ct)).getD false then none
      else generationPos_loop t maybeInv (pos + 1) c

/-- Position at which `t` generates in the trace, or `none`.
    Mirrors `generationPos :: Term -> Trace -> Maybe Int`. -/
def generationPos (t : Term) (c : Trace) : Option Int :=
  generationPos_loop t (invertKey t) 0 c

-- ── firstOccursPos ────────────────────────────────────────────────────────────

private def firstOccursPos_loop (t : Term) (maybeInv : Option Term) : Int → Trace → Option Int
  | _,   []           => none
  | pos, .Out t' :: c =>
      let ct := cmTerm t'
      if occursIn t ct || (maybeInv.map (occursIn · ct)).getD false then some pos
      else firstOccursPos_loop t maybeInv (pos + 1) c
  | pos, .In  t' :: c =>
      let ct := cmTerm t'
      if occursIn t ct || (maybeInv.map (occursIn · ct)).getD false then some pos
      else firstOccursPos_loop t maybeInv (pos + 1) c

/-- Position of the first occurrence of `t` (or its inverse) in the trace.
    Mirrors `firstOccursPos :: Term -> Trace -> Maybe Int`. -/
def firstOccursPos (t : Term) (c : Trace) : Option Int :=
  firstOccursPos_loop t (invertKey t) 0 c

-- ── acquiredPos ───────────────────────────────────────────────────────────────

private def acquiredPos_loop (t : Term) : Int → Trace → Option Int
  | _,   []           => none
  | pos, .In  t' :: c =>
      let ct := cmTerm t'
      if carriedBy t ct then some pos
      else if occursIn t ct then none
      else acquiredPos_loop t (pos + 1) c
  | pos, .Out t' :: c =>
      if occursIn t (cmTerm t') then none
      else acquiredPos_loop t (pos + 1) c

/-- Position at which `t` is first acquired (carried inbound), or `none`.
    Mirrors `acquiredPos :: Term -> Trace -> Maybe Int`. -/
def acquiredPos (t : Term) (c : Trace) : Option Int :=
  acquiredPos_loop t 0 c

-- ── gainedPos ─────────────────────────────────────────────────────────────────

private def gainedPos_loop (t : Term) : Int → Trace → Option Int
  | _,   []           => none
  | pos, .Out t' :: c =>
      if carriedBy t (cmTerm t') then none
      else gainedPos_loop t (pos + 1) c
  | pos, .In  t' :: c =>
      if carriedBy t (cmTerm t') then some pos
      else gainedPos_loop t (pos + 1) c

/-- Position at which `t` is first gained (carried inbound, never outbound first).
    Mirrors `gainedPos :: Term -> Trace -> Maybe Int`. -/
def gainedPos (t : Term) (c : Trace) : Option Int :=
  gainedPos_loop t 0 c

-- ── genGainedPos ──────────────────────────────────────────────────────────────

private def genGainedPos_loop (t : Term) : Int → Trace → Option Int
  | _,   []           => none
  | pos, .Out t' :: c =>
      if constituent t (cmTerm t') then none
      else genGainedPos_loop t (pos + 1) c
  | pos, .In  t' :: c =>
      if constituent t (cmTerm t') then some pos
      else genGainedPos_loop t (pos + 1) c

/-- Position at which `t` first appears as a constituent of an inbound event.
    Mirrors `genGainedPos :: Term -> Trace -> Maybe Int`. -/
def genGainedPos (t : Term) (c : Trace) : Option Int :=
  genGainedPos_loop t 0 c

-- ── usedPos ───────────────────────────────────────────────────────────────────

private def usedPos_loop : Int → List Term → Trace → Option Int
  | _,   _,    []      => none
  | pos, vars, e :: c  =>
      let vars' := vars.filter (fun x => !(varsInTerms [evtTerm e]).contains x)
      if vars'.isEmpty then some pos
      else usedPos_loop (pos + 1) vars' c

/-- Position at which all variables of `t` have appeared in the trace, or `none`.
    Mirrors `usedPos :: Term -> Trace -> Maybe Int`. -/
def usedPos (t : Term) (c : Trace) : Option Int :=
  usedPos_loop 0 (varsInTerms [t]) c

-- ── chanPos (private) ─────────────────────────────────────────────────────────

private def chanPos_loop (t : Term) : Int → Trace → Option Int
  | _,   []           => none
  | pos, .Out t' :: c =>
      if some t == cmChan t' then some pos
      else chanPos_loop t (pos + 1) c
  | pos, .In  t' :: c =>
      if some t == cmChan t' then some pos
      else chanPos_loop t (pos + 1) c

/-- Position at which channel `t` first appears in the trace, or `none`.
    Private: used only by `mkRole`. -/
private def chanPos (t : Term) (c : Trace) : Option Int :=
  chanPos_loop t 0 c

-- ── insPrecedeOuts ────────────────────────────────────────────────────────────

private def insPrecedeOuts_loopOuts : Int → Trace → Bool
  | _, []           => false
  | _, .In  _ :: _  => false
  | u, .Out _ :: c  => if u == 0 then true else insPrecedeOuts_loopOuts (u - 1) c

private def insPrecedeOuts_loopIns : Int → Trace → Bool
  | _, []           => false
  | u, .In  _ :: c  => if u == 0 then true else insPrecedeOuts_loopIns (u - 1) c
  | u, .Out _ :: c  => if u == 0 then true else insPrecedeOuts_loopOuts (u - 1) c

/-- True when a window `[lower, upper)` of the trace consists of ins followed by outs.
    Mirrors `insPrecedeOuts :: Int -> Int -> Trace -> Bool`. -/
def insPrecedeOuts (lower upper : Int) (c : Trace) : Bool :=
  insPrecedeOuts_loopIns (upper - lower) (c.drop lower.toNat)

-- ════════════════════════════════════════════════════════════════════════════
-- Stage 3: Role structure and mkRole
-- ════════════════════════════════════════════════════════════════════════════

-- ── Role ─────────────────────────────────────────────────────────────────────

/-- The static description of a protocol role.
    Mirrors `data Role = Role { rname, rvars, rtrace, ... }`. -/
structure Role where
  rname     : String
  rvars     : List Term
  rtrace    : Trace
  rnon      : List (Option Int × Term)
  rpnon     : List (Option Int × Term)
  runique   : List Term
  runiqgen  : List Term
  rabsent   : List (Term × Term)
  rconf     : List Term
  rauth     : List Term
  rcomment  : List (Cpsa2Lean.Lib.SExpr Unit)
  rsearch   : Bool
  rnorig    : List (Term × Int)
  rpnorig   : List (Term × Int)
  ruorig    : List (Term × Int)
  rugen     : List (Term × Int)
  rabs      : List (Term × Term × Int)
  rpconf    : List (Term × Int)
  rpauth    : List (Term × Int)
  rpriority : List Int
  deriving Repr

private def defaultPriority : Int := 5

-- ── firstOccursAt ─────────────────────────────────────────────────────────────

private def firstOccursAt_loop (t : Term) : Int → Trace → Option Int
  | _, []      => none
  | i, e :: c  =>
      if (cmTerms (evtCm e)).any (occursIn t) then some i
      else firstOccursAt_loop t (i + 1) c

/-- Index of the first event at which `t` occurs, or `none`.
    Mirrors `firstOccursAt :: Term -> Trace -> Maybe Int`. -/
private def firstOccursAt (t : Term) (c : Trace) : Option Int :=
  firstOccursAt_loop t 0 c

-- ── traceAbsent ───────────────────────────────────────────────────────────────

/-- For each numeric `uniqgen` variable, pair it with every numeric subterm
    that appears in the trace before its generation point.
    Mirrors `traceAbsent :: Trace -> [Term] -> [(Term, Term)]`. -/
private def traceAbsent (trace : Trace) (ugens : List Term) : List (Term × Term) :=
  let numsUpTo (p : Int) : List Term :=
    let s := RBSet.unions ((trace.take p.toNat).map (fun evt => subNums (evtTerm evt)))
    RBSet.toList s
  let indz_ininsts_var (v : Term) (p : Int) : List (Term × Term) :=
    (numsUpTo p).map (fun t => (v, t))
  let indz_ininsts (v : Term) : List (Term × Term) :=
    match generationPos v trace with
    | none   => indz_ininsts_var v 0
    | some p => indz_ininsts_var v p
  (ugens.filter isNum).flatMap indz_ininsts

-- ── mkRole ────────────────────────────────────────────────────────────────────

/-- Construct a `Role`, computing all derived position fields.
    Mirrors `mkRole :: String -> [Term] -> Trace -> ... -> Bool -> Role`. -/
def mkRole (name : String) (vars : List Term) (trace : Trace)
    (non pnon : List (Option Int × Term)) (unique uniqgen : List Term)
    (absent : List (Term × Term)) (conf auth : List Term)
    (comment : List (Cpsa2Lean.Lib.SExpr Unit))
    (priority : List (Int × Int)) (rev : Bool) : Role :=
  let uniqgen' := uniqgen.eraseDups
  let absent'  := (traceAbsent trace uniqgen' ++ absent).eraseDups
  let addUniqueOrig (t : Term) : Term × Int :=
    match originationPos t trace with
    | some p => (t, p)
    | none   => Cpsa2Lean.Lib.assertError "Protocol.mkRole: Atom does not uniquely originate"
  let addUniqueGen (t : Term) : Term × Int :=
    match generationPos t trace with
    | some p => (t, p)
    | none   => Cpsa2Lean.Lib.assertError "Protocol.mkRole: Atom does not uniquely generate"
  let addNonOrig : Option Int × Term → Term × Int
    | (len, t) =>
      match usedPos t trace with
      | none   => Cpsa2Lean.Lib.assertError "Protocol.mkRole: Atom variables not in trace"
      | some p =>
        match len with
        | none       => (t, p)
        | some len   => if len >= p then (t, len)
                        else Cpsa2Lean.Lib.assertError
                               "Protocol.mkRole: Position for atom too early in trace"
  let addAbsentPos : Term × Term → Term × Term × Int
    | (x, y) =>
      match usedPos x trace, usedPos y trace with
      | some xp, some yp => (x, y, max xp yp)
      | _,       _       =>
          Cpsa2Lean.Lib.assertError "Protocol.mkRole: Absence variable not in trace"
  let addChanPos (t : Term) : Term × Int :=
    match chanPos t trace with
    | some p => (t, p)
    | none   => Cpsa2Lean.Lib.assertError "Protocol.mkRole: Channel not in trace"
  let nonNub (nons : List (Option Int × Term)) : List (Option Int × Term) :=
    (nons.foldl (fun acc non =>
      if acc.any (fun x => non.2 == x.2) then acc else non :: acc) []).reverse
  let addDefaultPrio (pr : List (Int × Int)) : List Int :=
    (nats trace.length).map (fun n =>
      match pr.lookup (Int.ofNat n) with
      | some p => p
      | none   => defaultPriority)
  { rname     := name,
    rvars     := vars.eraseDups,
    rtrace    := trace,
    rnon      := non,
    rpnon     := pnon,
    runique   := unique.eraseDups,
    runiqgen  := uniqgen',
    rabsent   := absent',
    rconf     := conf.eraseDups,
    rauth     := auth.eraseDups,
    rcomment  := comment,
    rsearch   := rev,
    rnorig    := (nonNub non).map addNonOrig,
    rpnorig   := (nonNub pnon).map addNonOrig,
    ruorig    := unique.eraseDups.map addUniqueOrig,
    rugen     := uniqgen'.map addUniqueGen,
    rabs      := absent'.map addAbsentPos,
    rpconf    := conf.eraseDups.map addChanPos,
    rpauth    := auth.eraseDups.map addChanPos,
    rpriority := addDefaultPrio priority }

-- ── Role query functions ───────────────────────────────────────────────────────

/-- Index of the first event in role `r` at which `v` occurs, or `none`.
    Mirrors `firstOccurs :: Term -> Role -> Maybe Int`. -/
def firstOccurs (v : Term) (r : Role) : Option Int :=
  firstOccursAt v r.rtrace

/-- Find the role variable whose name matches `name`, if any.
    Mirrors `paramOfName :: String -> Role -> Maybe Term`. -/
def paramOfName (name : String) (rl : Role) : Option Term :=
  rl.rvars.find? (fun v => name == varName v)

/-- Pair each variable in `vars` with its corresponding role parameter.
    Mirrors `paramVarPairs :: Role -> [Term] -> [(Term, Term)]`. -/
private def paramVarPairs (rl : Role) (vars : List Term) : List (Term × Term) :=
  vars.foldl (fun soFar v =>
    match paramOfName (varName v) rl with
    | none   => soFar
    | some p => (p, v) :: soFar) []

/-- Build the environment that maps role parameters to `vars`.
    Mirrors `envsRoleParams :: Role -> [Term] -> Env`. -/
def envsRoleParams (rl : Role) (vars : List Term) : Env :=
  envOfParamVarPairs (paramVarPairs rl vars)

-- ════════════════════════════════════════════════════════════════════════════
-- Stage 4: Divergence analysis
-- ════════════════════════════════════════════════════════════════════════════

-- ── AgreeData ─────────────────────────────────────────────────────────────────

/-- Classification of how two events agree on store/non-store structure.
    Mirrors `data AgreeData = Disagree | NonStore | HalfStore | FullStore`. -/
inductive AgreeData where
  | Disagree  : AgreeData
  | NonStore  : AgreeData
  | HalfStore : AgreeData
  | FullStore : AgreeData

-- ── Agreement classifiers ─────────────────────────────────────────────────────

private def divergeAgreeStore : Event → AgreeData
  | .Out (.ChMsg ch2 _) => if isLocn ch2 then .FullStore else .HalfStore
  | _                   => .HalfStore

private def divergeAgreeOutChan : Event → AgreeData
  | .Out (.ChMsg ch2 _) => if isLocn ch2 then .HalfStore else .NonStore
  | _                   => .Disagree

private def divergeAgreeOutPlain : Event → AgreeData
  | .Out (.ChMsg ch2 _) => if isLocn ch2 then .HalfStore else .Disagree
  | .Out (.Plain _)     => .NonStore
  | _                   => .Disagree

private def divergeAgreeInChan : Event → AgreeData
  | .Out (.ChMsg ch2 _) => if isLocn ch2 then .HalfStore else .Disagree
  | .Out (.Plain _)     => .Disagree
  | .In  (.ChMsg _ _)   => .NonStore
  | _                   => .Disagree

private def divergeAgreeInPlain : Event → AgreeData
  | .Out (.ChMsg ch2 _) => if isLocn ch2 then .HalfStore else .Disagree
  | .In  (.Plain _)     => .NonStore
  | _                   => .Disagree

/-- Classify whether two events agree, from the perspective of the first event.
    Mirrors `divergeEventsAgree :: Event -> Event -> AgreeData`. -/
def divergeEventsAgree : Event → Event → AgreeData
  | .Out (.ChMsg ch1 _), e2 => if isLocn ch1 then divergeAgreeStore e2 else divergeAgreeOutChan e2
  | .Out _,              e2 => divergeAgreeOutPlain e2
  | .In  (.ChMsg _ _),   e2 => divergeAgreeInChan e2
  | .In  _,              e2 => divergeAgreeInPlain e2

-- ── VarTrail and helpers ──────────────────────────────────────────────────────

/-- A list of distinct sorted variables.
    Mirrors `type VarTrail = [Term]`. -/
abbrev VarTrail := List Term

/-- Collect all sorted variables from every term in an event's channel message.
    Mirrors `eventVars :: Event -> [Term]`. -/
def eventVars (e : Event) : VarTrail :=
  (cmTerms (evtCm e)).foldr (fun t acc => union (sortedVarsIn t) acc) []

/-- Apply a substitution to a var trail, returning `none` if the result
    is not injective on variables.
    Mirrors `substVarTrail :: Gen -> Subst -> VarTrail -> Maybe VarTrail`. -/
def substVarTrail (gen : Gen) (subst : Subst) (varList : VarTrail) : Option VarTrail := do
  let image ← varList.mapM (substInvertibly gen subst)
  if image.eraseDups.length < image.length then none
  else if image.any (fun t => !isVar t) then none
  else pure image

-- ── DivergeOutcome ────────────────────────────────────────────────────────────

/-- Outcome of divergence check: safe, or unsafe at position `i`.
    Mirrors `data DivergeOutcome = Safe | Unsafe Int`. -/
inductive DivergeOutcome where
  | Safe   : DivergeOutcome
  | Unsafe : Int → DivergeOutcome

instance : Inhabited DivergeOutcome := ⟨.Safe⟩

/-- Combine a list of outcomes, returning the first `Unsafe` found.
    Mirrors `combineOutcomes :: [DivergeOutcome] -> DivergeOutcome`. -/
def combineOutcomes : List DivergeOutcome → DivergeOutcome
  | []              => .Safe
  | .Unsafe i :: _  => .Unsafe i
  | .Safe     :: rest => combineOutcomes rest

-- ── Diverge loop (mutually recursive) ────────────────────────────────────────

mutual

  /-- Check if two traces diverge within a store segment.
      Mirrors `divergeLoop :: [Event] -> [Event] -> DivergeRest`. -/
  partial def divergeLoop
      (tr1 tr2 : Trace) (vars : VarTrail) (g : Gen)
      (inStore : Bool) (i : Int) : DivergeOutcome :=
    match tr1, tr2 with
    | [],        []        => .Safe
    | [],        _         => if inStore then .Unsafe i else .Safe
    | _,         []        => if inStore then .Unsafe i else .Safe
    | e1 :: r1,  e2 :: r2  =>
      match divergeEventsAgree e1 e2 with
      | .HalfStore => if inStore then .Unsafe i else .Safe
      | .Disagree  => .Safe
      | .NonStore  => divergeDescend e1 e2 r1 r2 vars g false i
      | .FullStore =>
        if inStore then divergeDescendSensitive e1 e2 r1 r2 vars g true i
        else            divergeDescend          e1 e2 r1 r2 vars g true i

  /-- Descend into unified subtrees, substituting vars.
      Mirrors `divergeDescend :: Event -> Event -> [Event] -> [Event] -> DivergeRest`. -/
  partial def divergeDescend
      (e1 e2 : Event) (rest1 rest2 : Trace) (vars : VarTrail) (g : Gen)
      (inStore : Bool) (i : Int) : DivergeOutcome :=
    let gsubsts := cmUnify (evtCm e1) (evtCm e2) (g, emptySubst)
    let eVars (f : Term → Term) (e : Event) : List Term :=
      ((eventVars e).map f).eraseDups
    combineOutcomes (gsubsts.map (fun (g', s) =>
      let sub    := substitute s
      let newVars := union (eVars sub e1) (union (eVars sub e2) (vars.map sub))
      divergeLoop (rest1.map (evtMap sub)) (rest2.map (evtMap sub)) newVars g' inStore (i + 1)))

  /-- Descend, but first verify the substitution acts as a renaming on `vars`.
      Mirrors `divergeDescendSensitive :: Event -> Event -> [Event] -> [Event] -> DivergeRest`. -/
  partial def divergeDescendSensitive
      (e1 e2 : Event) (rest1 rest2 : Trace) (vars : VarTrail) (g : Gen)
      (_ : Bool) (i : Int) : DivergeOutcome :=
    let gsubsts := cmUnify (evtCm e1) (evtCm e2) (g, emptySubst)
    let eVars (f : Term → Term) (e : Event) : List Term :=
      ((eventVars e).map f).eraseDups
    match gsubsts.mapM (fun (g', subst) => substVarTrail g' subst vars) with
    | none          => .Unsafe i
    | some varLists =>
      combineOutcomes ((gsubsts.zip varLists).map (fun ((g', s), vs) =>
        let sub     := substitute s
        let newVars := union (eVars sub e1) (union (eVars sub e2) vs)
        divergeLoop (rest1.map (evtMap sub)) (rest2.map (evtMap sub)) newVars g' true (i + 1)))

end

-- ── Role-level divergence check ───────────────────────────────────────────────

/-- Check whether two roles diverge within a store segment.
    Mirrors `rolesDivergeInStoreSeg :: Role -> Role -> Gen -> DivergeOutcome`. -/
def rolesDivergeInStoreSeg (r1 r2 : Role) (g : Gen) : DivergeOutcome :=
  divergeLoop r1.rtrace r2.rtrace [] g false 0

-- `checkForDivergenceInStoreSegments` depends on `Prot` (Stage 6) and is
-- deferred to that stage.

-- ════════════════════════════════════════════════════════════════════════════
-- Stage 5: AForm, Goal, Conj, and formula operations
-- ════════════════════════════════════════════════════════════════════════════

-- ── NodeTerm ──────────────────────────────────────────────────────────────────

/-- A (strand, position) pair used in atomic formulas.
    Mirrors `type NodeTerm = (Term, Term)`. -/
abbrev NodeTerm := Term × Term

-- ── AForm ─────────────────────────────────────────────────────────────────────

/-- Atomic security-goal formula.
    Mirrors `data AForm = Length ... | Param ... | ...`. -/
inductive AForm where
  | Length    : Role → Term → Term → AForm
  | Param     : Role → Term → Int → Term → Term → AForm
  | Prec      : NodeTerm → NodeTerm → AForm
  | Non       : Term → AForm
  | Pnon      : Term → AForm
  | Uniq      : Term → AForm
  | UniqAt    : Term → NodeTerm → AForm
  | Ugen      : Term → AForm
  | UgenAt    : Term → NodeTerm → AForm
  | GenStV    : Term → AForm
  | Conf      : Term → AForm
  | Auth      : Term → AForm
  | Commpair  : NodeTerm → NodeTerm → AForm
  | SameLocn  : NodeTerm → NodeTerm → AForm
  | StateNode : NodeTerm → AForm
  | Trans     : NodeTerm → AForm
  | LeadsTo   : NodeTerm → NodeTerm → AForm
  | AFact     : String → List Term → AForm
  | Equals    : Term → Term → AForm
  | Component : Term → Term → AForm
  deriving Repr, Inhabited

-- ── Goal and Conj ─────────────────────────────────────────────────────────────

/-- A universally-quantified security goal.
    Mirrors `data Goal = Goal { uvars, antec, consq, concl }`. -/
structure Goal where
  uvars : List Term
  antec : List AForm
  consq : List (List Term × List AForm)
  concl : List (List AForm)
  deriving Repr, Inhabited

/-- A conjunction of positioned atomic formulas.
    Mirrors `type Conj = [(Pos, AForm)]`. -/
abbrev Conj := List (Cpsa2Lean.Lib.Pos × AForm)

-- ── AForm ordering ────────────────────────────────────────────────────────────

/-- Constructor index used for ordering `AForm` values.
    Mirrors `indexOfAForm :: AForm -> Int`. -/
def indexOfAForm : AForm → Int
  | .Length    _ _ _       => 0
  | .Param     _ _ _ _ _   => 1
  | .Prec      _ _         => 2
  | .Non       _           => 3
  | .Pnon      _           => 4
  | .Uniq      _           => 5
  | .UniqAt    _ _         => 6
  | .GenStV    _           => 7
  | .Conf      _           => 8
  | .Auth      _           => 9
  | .Commpair  _ _         => 10
  | .SameLocn  _ _         => 11
  | .StateNode _           => 12
  | .Trans     _           => 13
  | .LeadsTo   _ _         => 14
  | .AFact     _ _         => 15
  | .Equals    _ _         => 16
  | .Component _ _         => 17
  | .Ugen      _           => 18
  | .UgenAt    _ _         => 19

/-- Order `AForm` values by constructor index.
    Mirrors `aFormOrder :: AForm -> AForm -> Ordering`. -/
def aFormOrder (f f' : AForm) : Ordering :=
  compare (indexOfAForm f) (indexOfAForm f')

-- ── Free-variable accumulation ────────────────────────────────────────────────

/-- Accumulate into `vars` every variable occurring in `af`.
    Mirrors `aFreeVars :: [Term] -> AForm -> [Term]`. -/
def aFreeVars (vars : List Term) : AForm → List Term
  | .Length    _ z _           => addVars vars z
  | .Param     _ _ _ z t       => addVars (addVars vars z) t
  | .Prec      (x, i) (y, j)   => addVars (addVars (addVars (addVars vars x) y) i) j
  | .Non       t               => addVars vars t
  | .Pnon      t               => addVars vars t
  | .Uniq      t               => addVars vars t
  | .UniqAt    t (z, i)        => addVars (addVars (addVars vars t) z) i
  | .Ugen      t               => addVars vars t
  | .UgenAt    t (z, i)        => addVars (addVars (addVars vars t) z) i
  | .GenStV    t               => addVars vars t
  | .Conf      t               => addVars vars t
  | .Auth      t               => addVars vars t
  | .AFact     _ ft            => ft.foldl addVars vars
  | .Equals    x y             => addVars (addVars vars x) y
  | .Component x y             => addVars (addVars vars x) y
  | .Commpair  (s, t) (s', t') => addVars (addVars (addVars (addVars vars s) t) s') t'
  | .SameLocn  (s, t) (s', t') => addVars (addVars (addVars (addVars vars s) t) s') t'
  | .StateNode (s, t)          => addVars (addVars vars s) t
  | .Trans     (s, t)          => addVars (addVars vars s) t
  | .LeadsTo   (s, t) (s', t') => addVars (addVars (addVars (addVars vars s) t) s') t'

-- ── Instantiation ─────────────────────────────────────────────────────────────

/-- Apply environment `e` to every term in an atomic formula.
    Mirrors `instantiateAForm :: Env -> AForm -> AForm`. -/
def instantiateAForm (e : Env) : AForm → AForm
  | .Length    rl z v           => .Length    rl (instantiate e z) (instantiate e v)
  | .Param     rl p i z t       => .Param     rl p i (instantiate e z) (instantiate e t)
  | .Prec      (x, i) (y, j)    => .Prec      (instantiate e x, instantiate e i)
                                               (instantiate e y, instantiate e j)
  | .Non       t                => .Non       (instantiate e t)
  | .Pnon      t                => .Pnon      (instantiate e t)
  | .Uniq      t                => .Uniq      (instantiate e t)
  | .UniqAt    t (z, i)         => .UniqAt    (instantiate e t)
                                               (instantiate e z, instantiate e i)
  | .Ugen      t                => .Ugen      (instantiate e t)
  | .UgenAt    t (z, i)         => .UgenAt    (instantiate e t)
                                               (instantiate e z, instantiate e i)
  | .GenStV    t                => .GenStV    (instantiate e t)
  | .Conf      t                => .Conf      (instantiate e t)
  | .Auth      t                => .Auth      (instantiate e t)
  | .AFact     pred ft          => .AFact     pred (ft.map (instantiate e))
  | .Equals    x y              => .Equals    (instantiate e x) (instantiate e y)
  | .Component x y              => .Component (instantiate e x) (instantiate e y)
  | .Commpair  (s, t) (s', t')  => .Commpair  (instantiate e s, instantiate e t)
                                               (instantiate e s', instantiate e t')
  | .SameLocn  (s, t) (s', t')  => .SameLocn  (instantiate e s, instantiate e t)
                                               (instantiate e s', instantiate e t')
  | .StateNode (s, t)           => .StateNode (instantiate e s, instantiate e t)
  | .Trans     (s, t)           => .Trans     (instantiate e s, instantiate e t)
  | .LeadsTo   (s, t) (s', t')  => .LeadsTo   (instantiate e s, instantiate e t)
                                               (instantiate e s', instantiate e t')

/-- Apply environment `e` to every atomic formula in a conjunction.
    Mirrors `instantiateConj :: Env -> Conj -> Conj`. -/
def instantiateConj (e : Env) (c : Conj) : Conj :=
  c.map (fun (p, a) => (p, instantiateAForm e a))

-- ── Free variables ────────────────────────────────────────────────────────────

/-- Sorted variables free in an atomic formula.
    Mirrors `fvsAForm :: AForm -> [Term]`. -/
def fvsAForm : AForm → List Term
  | .Length    _ z l            => (sortedVarsIn z ++ sortedVarsIn l).eraseDups
  | .Param     _ _ _ z v        => (sortedVarsIn z ++ sortedVarsIn v).eraseDups
  | .Prec      (z1, i1) (z2, i2) =>
      (sortedVarsIn z1 ++ sortedVarsIn i1 ++ sortedVarsIn z2 ++ sortedVarsIn i2).eraseDups
  | .Non       t                => (sortedVarsIn t).eraseDups
  | .Pnon      t                => (sortedVarsIn t).eraseDups
  | .Uniq      t                => (sortedVarsIn t).eraseDups
  | .Ugen      t                => (sortedVarsIn t).eraseDups
  | .UniqAt    t (z1, i1)       =>
      (sortedVarsIn t ++ sortedVarsIn z1 ++ sortedVarsIn i1).eraseDups
  | .UgenAt    t (z1, i1)       =>
      (sortedVarsIn t ++ sortedVarsIn z1 ++ sortedVarsIn i1).eraseDups
  | .GenStV    t                => (sortedVarsIn t).eraseDups
  | .Conf      t                => (sortedVarsIn t).eraseDups
  | .Auth      t                => (sortedVarsIn t).eraseDups
  | .Commpair  (z1, i1) (z2, i2) =>
      (sortedVarsIn z1 ++ sortedVarsIn i1 ++ sortedVarsIn z2 ++ sortedVarsIn i2).eraseDups
  | .SameLocn  (z1, i1) (z2, i2) =>
      (sortedVarsIn z1 ++ sortedVarsIn i1 ++ sortedVarsIn z2 ++ sortedVarsIn i2).eraseDups
  | .LeadsTo   (z1, i1) (z2, i2) =>
      (sortedVarsIn z1 ++ sortedVarsIn i1 ++ sortedVarsIn z2 ++ sortedVarsIn i2).eraseDups
  | .StateNode (z1, i1)         => (sortedVarsIn z1 ++ sortedVarsIn i1).eraseDups
  | .Trans     (z1, i1)         => (sortedVarsIn z1 ++ sortedVarsIn i1).eraseDups
  | .Equals    t1 t2            => (sortedVarsIn t1 ++ sortedVarsIn t2).eraseDups
  | .Component t1 t2            => (sortedVarsIn t1 ++ sortedVarsIn t2).eraseDups
  | .AFact     _ ts             => (ts.flatMap sortedVarsIn).eraseDups

/-- Free variables of a conjunction.
    Mirrors `fvsConj :: Conj -> [Term]`. -/
def fvsConj (c : Conj) : List Term :=
  (c.flatMap (fun (_, a) => fvsAForm a)).eraseDups

/-- Free variables of an antecedent.
    Mirrors `fvsAntec :: [AForm] -> [Term]`. -/
def fvsAntec (afs : List AForm) : List Term :=
  (afs.flatMap fvsAForm).eraseDups

/-- Free variables of a consequent (existential variables subtracted).
    Mirrors `fvsConsq :: [([Term], [AForm])] -> [Term]`. -/
def fvsConsq (exs : List (List Term × List AForm)) : List Term :=
  (exs.flatMap (fun (evs, c) => (fvsAntec c).filter (fun v => !evs.contains v))).eraseDups

-- ════════════════════════════════════════════════════════════════════════════
-- Stage 6: Rule classification and Protocol structure
-- ════════════════════════════════════════════════════════════════════════════

-- ── Rule ──────────────────────────────────────────────────────────────────────

/-- A named security-goal rule.
    Mirrors `data Rule = Rule { rlname, rlgoal, rlcomment }`. -/
structure Rule where
  rlname    : String
  rlgoal    : Goal
  rlcomment : List (Cpsa2Lean.Lib.SExpr Unit)
  deriving Repr, Inhabited

-- ── RuleKind ──────────────────────────────────────────────────────────────────

/-- Classification of a rule by its conclusion structure.
    Mirrors `data RuleKind = NullaryRule | UnaryRule | GeneralRule`. -/
inductive RuleKind where
  | NullaryRule : RuleKind
  | UnaryRule   : RuleKind
  | GeneralRule : RuleKind

/-- Classify a rule by the shape of its consequent.
    Mirrors `classifyRule :: Rule -> RuleKind`. -/
def classifyRule (r : Rule) : RuleKind :=
  match r.rlgoal.consq with
  | []            => .NullaryRule
  | [([], _)]     => .UnaryRule
  | _             => .GeneralRule

/-- Partition rules into (nullary, unary, general) lists.
    Mirrors `classifyRules :: [Rule] -> ([Rule],[Rule],[Rule])`. -/
private def classifyRules (rs : List Rule) : List Rule × List Rule × List Rule :=
  rs.foldl (fun (ns, us, gs) rl =>
    match classifyRule rl with
    | .NullaryRule => (rl :: ns, us, gs)
    | .UnaryRule   => (ns, rl :: us, gs)
    | .GeneralRule => (ns, us, rl :: gs))
  ([], [], [])

-- ── Prot ──────────────────────────────────────────────────────────────────────

/-- A fully-constructed CPSA protocol.
    Mirrors `data Prot = Prot { pname, alg, pgen, psig, roles, ... }`. -/
structure Prot where
  pname          : String
  alg            : String
  pgen           : Gen
  psig           : Cpsa2Lean.Signature.Sig
  roles          : List Role
  listenerRole   : Role
  nullaryrules   : List Rule
  unaryrules     : List Rule
  generalrules   : List Rule
  userrules      : List Rule
  generatedrules : List Rule
  varsAllAtoms   : Bool
  pcomment       : List (Cpsa2Lean.Lib.SExpr Unit)
  deriving Repr

/-- Construct a `Prot`, classifying `rules` into the three sublists.
    Mirrors `mkProt :: String -> String -> Gen -> Sig -> [Role] -> Role ->
                       [Rule] -> [Rule] -> [Rule] -> [SExpr ()] -> Prot`. -/
def mkProt (name alg : String) (gen : Gen) (sig : Cpsa2Lean.Signature.Sig)
    (roleList : List Role) (lrole : Role)
    (allRules written generated : List Rule)
    (comment : List (Cpsa2Lean.Lib.SExpr Unit)) : Prot :=
  let (nrs, urs, grs) := classifyRules allRules
  { pname          := name,
    alg            := alg,
    pgen           := gen,
    psig           := sig,
    roles          := roleList,
    listenerRole   := lrole,
    nullaryrules   := nrs,
    unaryrules     := urs,
    generalrules   := grs,
    userrules      := written,
    generatedrules := generated,
    pcomment       := comment,
    varsAllAtoms   := roleList.all (fun role => role.rvars.all isAtom) }

/-- All rules of a protocol (nullary ++ unary ++ general).
    Mirrors `rules :: Prot -> [Rule]`. -/
def rules (p : Prot) : List Rule :=
  p.nullaryrules ++ p.unaryrules ++ p.generalrules

-- ── Divergence check (deferred from Stage 4) ──────────────────────────────────

/-- Find the first pair of roles that diverge in a store segment, if any.
    Mirrors `checkForDivergenceInStoreSegments :: Prot -> Maybe (String, String, Int)`. -/
def checkForDivergenceInStoreSegments (p : Prot) : Option (String × String × Int) :=
  let rec subloop (r : Role) : List Role → Option (String × String × Int)
    | []        => none
    | r' :: rest =>
      match rolesDivergeInStoreSeg r r' p.pgen with
      | .Unsafe i => some (r.rname, r'.rname, i)
      | .Safe     => subloop r rest
  let rec loop : List Role → Option (String × String × Int)
    | []        => none
    | r :: rest =>
      match subloop r rest with
      | some res => some res
      | none     => loop rest
  loop p.roles.reverse

end Cpsa2Lean.Protocol
