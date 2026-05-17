/-
Cpsa2Lean.Reduction

Port of CPSA.Reduction (MITRE cpsa v4.4.8).
Implements the top-level CPSA search loop (term reduction on skeletons).

The Haskell original threads `n` (step counter), `seen` (isomorphism history),
`p` (options), and `h` (output handle) through every function.  In this port
all four live in `SolveState`, carried by the `SolveM = StateT SolveState IO`
monad.

The only exported entry point is `runSolver`.
-/

import Cpsa2Lean.Lib.Entry
import Cpsa2Lean.Algebra
import Cpsa2Lean.Protocol
import Cpsa2Lean.Operation
import Cpsa2Lean.Strand
import Cpsa2Lean.Cohort
import Cpsa2Lean.Displayer
import Cpsa2Lean.Options

namespace Cpsa2Lean.Reduction

open Cpsa2Lean.Algebra
open Cpsa2Lean.Protocol
open Cpsa2Lean.Operation (Sid Operation Node)
open Cpsa2Lean.Strand
open Cpsa2Lean.Cohort (Mode ReduceRes unrealized reduce)
open Cpsa2Lean.Displayer
open Cpsa2Lean.Options (Options)
open Cpsa2Lean.Lib (SExpr comment writeLnSExpr)

-- ── Module constants ──────────────────────────────────────────────────────────

/-- If true, flush the output handle after every emitted S-expression.
    Mirrors `useFlush = True` in Reduction.hs.  Change only inside `emit`. -/
def useFlush : Bool := true

/-- If true, a generalization step kills the search branch instead of
    being treated as a cohort reduction.  Left at the Haskell default (false)
    for all normal use.  Mirrors `dieOnGeneralization = False`. -/
def dieOnGeneralization : Bool := false

-- ── Domain types ──────────────────────────────────────────────────────────────

/-- A labeled and parent-linked preskeleton.
    Mirrors `data LPreskel = LPreskel { content, label, depth, parent }`.

    NOTE: The Haskell `parent :: Maybe LPreskel` is self-referential.
    In Lean 4 a struct cannot directly contain an `Option` of itself because
    that would require an infinite-sized layout.  The only use of `parent` in
    the Haskell source is `label p`, so we store the parent's label directly. -/
structure LPreskel where
  content     : Preskel
  label       : Int
  depth       : Int
  parentLabel : Option Int   -- label of the parent skeleton, or none

/-- Construct a child LPreskel from a parent.
    Mirrors `withParent :: Preskel -> Int -> LPreskel -> LPreskel`. -/
private def withParent (k : Preskel) (lbl : Int) (parentLk : LPreskel) : LPreskel :=
  { content     := k,
    label       := lbl,
    depth       := parentLk.depth + 1,
    parentLabel := some parentLk.label }

/-- A skeleton that has been seen before, keyed by its label.
    Mirrors `type IPreskel = (Preskel, Int)`. -/
abbrev IPreskel := Preskel × Int

/-- The isomorphism history: a list of (skeleton, label) pairs.
    Mirrors `newtype Seen = Seen [IPreskel]`. -/
structure Seen where
  entries : List IPreskel

/-- Singleton seen history. -/
private def hist (ik : IPreskel) : Seen := { entries := [ik] }

/-- Add an entry to the seen history. -/
private def remember (ik : IPreskel) (s : Seen) : Seen :=
  { entries := ik :: s.entries }

/-- Empty seen history. -/
private def void : Seen := { entries := [] }

/-- Merge two seen histories. -/
private def merge (s t : Seen) : Seen :=
  { entries := s.entries ++ t.entries }

/-- A seen-skeleton reference: (label of the seen duplicate, the skeleton). -/
abbrev SeenSkel := Int × Preskel

/-- Result of expanding one branch of the derivation tree.
    Mirrors `data Reduct t g s e = ReductStable | Reduct | Genlz`.

    NOTE: `Reduct` as a constructor would clash with the type name; renamed:
      ReductStable → Stable
      Reduct       → Cohort
      Genlz        → Genl -/
inductive Reduct where
  | Stable : LPreskel → Reduct
  | Cohort : LPreskel → Int → List Preskel → List SeenSkel → Reduct
  | Genl   : LPreskel → Int → List Preskel → List SeenSkel → Reduct

/-- Output annotation: how to display a preskeleton.
    Mirrors `data Kind = Ordinary | Shape | Fringe | Aborted`. -/
inductive Kind where
  | Ordinary | Shape | Fringe | Aborted
  deriving BEq

/-- Extra skeleton annotation.
    Mirrors `data Anno = Nada | Preskeleton | SatisfiesAll | Dead`. -/
inductive Anno where
  | Nada | Preskeleton | SatisfiesAll | Dead

-- ── Pure helper functions ─────────────────────────────────────────────────────

/-- Find a strand map that is an isomorphism from k1 to k2, additionally
    preserving the unrealized-node set.
    Mirrors `stronglyIsomorphic :: Preskel -> Preskel -> [Sid]`. -/
private def stronglyIsomorphic (k1 k2 : Preskel) : List Sid :=
  let translateNode (sm : List Sid) (n : Node) : Node :=
    (sm.getD n.1.toNat 0, n.2)
  let setsEq (as_ bs : List Node) :=
    as_.all (· ∈ bs) && bs.all (· ∈ as_)
  let unrealizedInvariant (sm : List Sid) :=
    setsEq ((unrealized k1).map (translateNode sm)) (unrealized k2)
  let rec loop : List (GenEnv × GenEnv × List Sid) → List Sid
    | []                    => []
    | (_, _, sm) :: rest    =>
        if unrealizedInvariant sm then sm else loop rest
  loop (findIsomorphisms (gist k1) (gist k2))

/-- Check whether the skeleton was produced by a generalization step.
    Mirrors `generalized :: Preskel -> Bool`. -/
private def generalized (k : Preskel) : Bool :=
  match k.operation with
  | .Generalized _ _ => true
  | _                => false

/-- Look up `k` in the seen history.  Returns the label and strand map if
    a strongly-isomorphic skeleton is found.
    Mirrors `recall :: Preskel -> Seen -> Maybe (Int, [Sid])`. -/
private def recall (k : Preskel) (s : Seen) : Option (Int × List Sid) :=
  s.entries.findSome? fun (k', n) =>
    let (k1, k2) := if generalized k then (k', k) else (k, k')
    match stronglyIsomorphic k1 k2 with
    | []  => none
    | sm  => some (n, sm)

/-- Stub: adjust a preskeleton's strand map.
    The full implementation is commented out in the Haskell source.
    Mirrors `fixStrandMap :: Preskel -> [Sid] -> Preskel`. -/
private def fixStrandMap (k : Preskel) (_ : List Sid) : Preskel := k

/-- Check whether kid has been seen; accumulate into unseen/dups.
    Mirrors `duplicates :: Seen -> ([Preskel],[SeenSkel]) -> Preskel -> ...`.
    The inner `maybeAdd` keeps the dups list sorted by label. -/
private def duplicates (seen : Seen) (acc : List Preskel × List SeenSkel)
    (kid : Preskel) : List Preskel × List SeenSkel :=
  let (unseen, dups) := acc
  match recall kid seen with
  | some (lbl, sm) =>
      let rec maybeAdd (i : Int) (k : Preskel) : List SeenSkel → List SeenSkel
        | []               => [(i, k)]
        | (j, k') :: rest  =>
            if i < j then (i, k) :: (j, k') :: rest
            else if i == j then (j, k') :: rest
            else (j, k') :: maybeAdd i k rest
      (unseen, maybeAdd lbl (fixStrandMap kid sm) dups)
  | none => (kid :: unseen, dups)

/-- Build the `Mode` record from the runtime options.
    Mirrors `mkMode :: Options -> Mode`. -/
private def mkMode (p : Options) : Mode :=
  { noGeneralization     := p.optNoIsoChk,
    nonceFirstOrder      := p.optCheckNoncesFirst,
    visitOldStrandsFirst := p.optTryOldStrandsFirst,
    reverseNodeOrder     := p.optTryYoungNodesFirst }

/-- Collect all LPreskels from a list of Reducts plus todo/toobig lists.
    Used to build the argument to `dump` when aborting.
    Mirrors `mktodo :: [Reduct t g s e] -> [LPreskel] -> [LPreskel] -> [LPreskel]`. -/
private def mktodo (reducts : List Reduct) (todo toobig : List LPreskel)
    : List LPreskel :=
  let fromReducts := reducts.foldl (fun acc r =>
    match r with
    | .Stable lk        => lk :: acc
    | .Cohort lk _ _ _  => lk :: acc
    | .Genl   lk _ _ _  => lk :: acc) []
  fromReducts ++ todo.reverse ++ toobig.reverse

/-- True when the preskeleton has security goals.
    Mirrors `goalsPresent :: LPreskel -> Bool`. -/
private def goalsPresent (lk : LPreskel) : Bool :=
  !(kgoals lk.content).isEmpty

/-- True when no security goal has a counter-example.
    Mirrors `noCounterExamples :: LPreskel -> Bool`. -/
private def noCounterExamples (lk : LPreskel) : Bool :=
  (goalCounterExamples lk.content).isEmpty

-- ── Pure display functions ────────────────────────────────────────────────────

/-- Add a key-values pair to an S-expression field list.
    Mirrors `addKeyValues :: String -> [SExpr ()] -> [SExpr ()] -> [SExpr ()]`. -/
private def addKeyValues (key : String) (values : List (SExpr Unit))
    (rest : List (SExpr Unit)) : List (SExpr Unit) :=
  .lst () (.sym () key :: values) :: rest

/-- Conditionally add a key-values pair.
    Mirrors `condAddKeyValues`. -/
private def condAddKeyValues (key : String) (cond : Bool)
    (values : List (SExpr Unit)) (rest : List (SExpr Unit)) : List (SExpr Unit) :=
  if cond then addKeyValues key values rest else rest

/-- Add a key-values pair when the value is present.
    Mirrors `maybeAddVKeyValues`. -/
private def maybeAddVKeyValues {α : Type} (key : String) (f : α → List (SExpr Unit))
    (v : Option α) (rest : List (SExpr Unit)) : List (SExpr Unit) :=
  match v with
  | none   => rest
  | some x => addKeyValues key (f x) rest

/-- Annotate a field list with the shape/fringe/aborted key.
    Mirrors `addKindKey :: Kind -> [SExpr ()] -> [SExpr ()]`. -/
private def addKindKey (kind : Kind) (xs : List (SExpr Unit)) : List (SExpr Unit) :=
  match kind with
  | .Ordinary => xs
  | .Shape    => addKeyValues "shape"   [] xs
  | .Fringe   => addKeyValues "fringe"  [] xs
  | .Aborted  => addKeyValues "aborted" [] xs

/-- True for Shape and Fringe, false for Ordinary and Aborted.
    Mirrors `isFringe :: Kind -> Bool`. -/
private def isFringe : Kind → Bool
  | .Ordinary | .Aborted => false
  | .Shape    | .Fringe  => true

/-- Annotate a field list with the anno key.
    Mirrors `addAnnoKey :: Anno -> [SExpr ()] -> [SExpr ()]`. -/
private def addAnnoKey (anno : Anno) (xs : List (SExpr Unit)) : List (SExpr Unit) :=
  match anno with
  | .Nada        => xs
  | .Preskeleton => addKeyValues "preskeleton"   [] xs
  | .SatisfiesAll=> addKeyValues "satisfies-all" [] xs
  | .Dead        => addKeyValues "dead"          [] xs

/-- Display a seen-skeleton reference.
    Mirrors `displaySeen :: SeenSkel -> SExpr ()`. -/
private def displaySeen (ss : SeenSkel) : SExpr Unit :=
  let (lbl, k) := ss
  let vars := k.kfvars ++ kvars k
  let ctx  := varsContext vars
  .lst () (.num () lbl :: displayOperation k ctx (displayStrandMap k []))

/-- Report goal satisfaction for a shape.
    Mirrors `reportSatisfies :: Preskel -> [SExpr ()]`. -/
private def reportSatisfies (k : Preskel) : List (SExpr Unit) :=
  let ctx (ts : List Term) := addToContext emptyContext ts
  let evars (g : Goal) := g.consq.flatMap Prod.fst
  match goalCounterExamples k with
  | []      => [.sym () "yes"]
  | goalGEs => goalGEs.map fun (g, ges) =>
      match ges with
      | []       =>
          -- This case should not arise (goalCounterExamples guarantees non-empty).
          .lst () [.sym () "no"]
      | ge :: _  =>
          .lst () (.sym () "no" ::
            (unSatReport k g ge).map
              (displayForm (ctx (g.uvars ++ evars g ++ kvars k))) ++
            displayEnv (ctx g.uvars) (ctx (kvars k)) ge.2)

/-- Display structure-preserving maps (homomorphisms).
    Mirrors `maps :: Preskel -> [SExpr ()]`. -/
private def maps (k : Preskel) : List (SExpr Unit) :=
  let vars := kvars k
  let ctx (k0 : Preskel) := addToContext emptyContext (kvars k0 ++ k0.kfvars)
  let strands := k.prob.map (.num () ·)
  match k.pov with
  | none    => []
  | some k' =>
      let envMaps :=
        (homomorphism k' k k.prob).map fun ge =>
          displayEnvSansPts vars (ctx k') (ctx k) ge.2
      envMaps.map fun env => .lst () [.lst () strands, .lst () env]

/-- Display origination nodes.
    Mirrors `origs :: Preskel -> [SExpr ()]`. -/
private def origs (k : Preskel) : List (SExpr Unit) :=
  let ctx := addToContext emptyContext (kvars k)
  k.korig.reverse.flatMap fun (t, ns) => --reverse to match Haskell order. Maybe change haskell order.
    ns.map fun n => .lst () [displayTerm ctx t, displayNode n]

/-- Display unique-generation nodes.
    Mirrors `gens :: Preskel -> [SExpr ()]`. -/
private def gens (k : Preskel) : List (SExpr Unit) :=
  let ctx := addToContext emptyContext (kvars k)
  k.kugen.flatMap fun (t, ns) =>
    ns.map fun n => .lst () [displayTerm ctx t, displayNode n]

/-- Assemble the full annotated preskeleton S-expression.
    Mirrors `commentPreskel :: LPreskel -> [SeenSkel] -> [Node] -> Kind ->
                               Anno -> String -> SExpr ()`. -/
private def commentPreskel (lk : LPreskel) (seen_ : List SeenSkel)
    (unrealized_ : List Node) (kind : Kind) (anno : Anno) (msg : String)
    : SExpr Unit :=
  let k          := lk.content
  let sortedSeen := seen_.mergeSort (fun a b => Ord.compare a.1 b.1 != .gt)
  let fringe     := isFringe kind
  let starter    := match k.pov with
                    | none    => true
                    | some k' => nstrands k == nstrands k'
  let realToken  := if unrealized_.isEmpty then "realized" else "unrealized"
  -- Build the field list from bottom to top (matching the Haskell `$` chain).
  let rest : List (SExpr Unit) :=
    (match msg with | "" => [] | _ => [comment msg])
  let rest := condAddKeyValues "ugens"
                (!(gens k).isEmpty && (starter || fringe)) (gens k) rest
  let rest := condAddKeyValues "origs"
                (starter || fringe) (origs k) rest
  let rest := condAddKeyValues "maps" true (maps k) rest
  let rest := condAddKeyValues "satisfies"
                (kind == .Shape && !(kgoals k).isEmpty) (reportSatisfies k) rest
  let rest := addAnnoKey anno rest
  let rest := addKindKey kind rest
  let rest := addKeyValues realToken (displayNodes unrealized_) rest
  let rest := condAddKeyValues "seen-ops"
                (!sortedSeen.isEmpty) (sortedSeen.map displaySeen) rest
  let rest := condAddKeyValues "seen"
                (!sortedSeen.isEmpty) (sortedSeen.map fun ss => .num () ss.1) rest
  let rest := maybeAddVKeyValues "parent" (fun p => [.num () p]) lk.parentLabel rest
  let rest := addKeyValues "label" [.num () lk.label] rest
  displayPreskel k rest

-- ── SolveState / SolveM ───────────────────────────────────────────────────────

/-- Mutable state threaded through the search loop.
    - `stepN`     : current global step counter (labels each new preskeleton)
    - `stepLimit` : step limit for the current problem (= initial n + optLimit)
    - `seen`      : isomorphism history for the current breadth level
    - `handle`    : output stream (file or stdout)
    - `opts`      : runtime options (read-only in practice) -/
structure SolveState where
  stepN      : Int
  stepLimit  : Int
  seen       : Seen
  handle     : IO.FS.Stream
  opts       : Options

/-- The search monad: IO with mutable SolveState. -/
abbrev SolveM := StateT SolveState IO

-- ── SolveM helpers ────────────────────────────────────────────────────────────

/-- Emit one S-expression to the output handle.
    This is the SINGLE point controlling all output and flushing.
    To change flushing behavior, edit only this function. -/
private def emit (sx : SExpr Unit) : SolveM Unit := do
  let s ← get
  let line := writeLnSExpr s.opts.optMargin sx
  liftM (s.handle.putStr line)
  if useFlush then liftM s.handle.flush else pure ()

private def getOpts : SolveM Options := do return (← get).opts
private def getStep : SolveM Int     := do return (← get).stepN

private def getSeen  : SolveM Seen   := do return (← get).seen
private def setSeen (s : Seen) : SolveM Unit :=
  modify fun st => { st with seen := s }

-- ── Pure search helpers ───────────────────────────────────────────────────────

/-- Update step/seen/todo/dups for one new child preskeleton.
    Pure: called inside `foldl` in the search loop.
    Mirrors `next :: LPreskel -> Next -> Preskel -> Next`. -/
private def nextK (parent : LPreskel)
    (acc : Int × Seen × List LPreskel × List SeenSkel) (k : Preskel)
    : Int × Seen × List LPreskel × List SeenSkel :=
  let (n, seen_, todo, dups) := acc
  match recall k seen_ with
  | some (lbl, sm) => (n, seen_, todo, (lbl, fixStrandMap k sm) :: dups)
  | none           =>
      let lk := withParent k n parent
      (n + 1, remember (k, n) seen_, lk :: todo, dups)

/-- Update step count and todo for one child in the `fast` (no-iso) path.
    Pure: called inside `foldl` in `fast`.
    Mirrors `children :: LPreskel -> (Int, [LPreskel]) -> Preskel -> (Int, [LPreskel])`. -/
private def children (parent : LPreskel) (acc : Int × List LPreskel) (k : Preskel)
    : Int × List LPreskel :=
  let (n, todo) := acc
  (n + 1, withParent k n parent :: todo)

/-- Expand one branch of the derivation tree.
    Pure: called via `List.map` from `breadth`.
    Mirrors `branch :: Options -> Seen -> LPreskel -> Reduct t g s e`. -/
private def branch (opts : Options) (seen_ : Seen) (lk : LPreskel) : Reduct :=
  match reduce (mkMode opts) lk.content with
  | .Stable    => .Stable lk
  | .Crt kids  =>
      let (unseen, dups) := kids.foldl (duplicates seen_) ([], [])
      .Cohort lk kids.length unseen.reverse dups
  | .Gnl kids  =>
      let (unseen, dups) := kids.foldl (duplicates seen_) ([], [])
      .Genl   lk kids.length unseen.reverse dups

-- ── Search loop (mutual partial defs) ────────────────────────────────────────
-- All functions are `partial` (no structural recursion proof).
-- `dump`, `fast`, `step`, `breadth`, `mode`, `search`, `begin`, `solve`
-- are mutually recursive and therefore grouped in one `mutual` block.
-- NOTE: `private` is not allowed on individual defs inside a `mutual` block.

mutual

/-- Emit all remaining preskeletons as "aborted" and return.
    Mirrors `dump :: Options -> Handle -> [LPreskel] -> String -> IO ()`.

    NOTE: The Haskell version calls `hClose h` and `abort msg` at the end.
    In Lean there is no `System.Exit`; we simply return after emitting.
    The caller can check the emitted S-expressions or use `IO.Process.exit`
    if hard termination is needed. -/
partial def dump (lks : List LPreskel) (msg : String) : SolveM Unit :=
  match lks with
  | []        => pure ()
  | lk :: rest => do
      let ns := unrealized lk.content
      emit (commentPreskel lk [] ns .Aborted .Nada "aborted")
      dump rest msg

/-- Reduction without isomorphism checks.
    Mirrors `fast :: Options -> Handle -> [Preskel] -> Int -> Int -> [LPreskel] -> IO ()`. -/
partial def fast (ks : List Preskel) (todo : List LPreskel) : SolveM Unit := do
  match todo with
  | [] =>
      emit (comment "Nothing left to do")
      solve ks
  | lk :: rest =>
      let n    ← getStep
      let m    := (← get).stepLimit
      let opts ← getOpts
      if n > m then do
        emit (comment "Step limit exceeded--aborting run")
        dump todo "Step limit exceeded"
      else if nstrands lk.content >= opts.optBound then do
        emit (comment "Strand bound exceeded--aborting run")
        dump todo "Strand bound exceeded"
      else do
        let ns  := unrealized lk.content
        let red := reduce (mkMode opts) lk.content
        let (len, ks') := match red with
          | .Stable   => (0, [])
          | .Crt kids => (kids.length, kids)
          | .Gnl kids => (kids.length, kids)
        let shape := match red with
          | .Stable => Kind.Shape
          | .Crt _  => Kind.Ordinary
          | .Gnl _  => Kind.Ordinary
        let msg := s!"{len} in cohort"
        emit (commentPreskel lk [] ns shape .Nada msg)
        let (n', todo') := ks'.foldl (children lk) (n, [])
        modify fun s => { s with stepN := n' }
        fast ks (rest ++ todo'.reverse)

/-- Process one complete level of the breadth-first derivation tree.
    Mirrors `step :: Options -> Handle -> [Preskel] -> Int -> Seen -> Int ->
                    Seen -> [LPreskel] -> [LPreskel] -> [Reduct t g s e] -> IO ()`.

    Parameters not in SolveState:
    - `ks`      : remaining problem list (passed through to `breadth`/`solve`)
    - `oseen`   : outer (previous-level) seen, merged back at the end of a level
    - `todo`    : accumulating list of child preskeletons for the next level
    - `toobig`  : preskeletons that exceeded the strand bound
    - `reducts` : remaining results from `branch` to process -/
partial def step (ks : List Preskel) (oseen : Seen) (todo toobig : List LPreskel)
    (reducts : List Reduct) : SolveM Unit := do
  let opts ← getOpts
  match reducts with
  | [] =>
      -- Level exhausted: merge inner seen with outer seen, process next level.
      let seenNow ← getSeen
      setSeen (merge seenNow oseen)
      breadth ks todo.reverse toobig
  | r :: rest =>
      let n := (← get).stepN
      let m := (← get).stepLimit
      if n > m then do
        emit (comment "Step limit exceeded--aborting run")
        dump (mktodo (r :: rest) todo toobig) "Step limit exceeded"
      else
      match r with
      | .Genl lk size kids dups =>
          -- Generalization result: die or treat as cohort.
          if dieOnGeneralization then do
            let ns := unrealized lk.content
            emit (commentPreskel lk [] ns .Ordinary .Dead "died of generalization")
            step ks oseen todo toobig rest
          else
            step ks oseen todo toobig (.Cohort lk size kids dups :: rest)
      | .Stable lk =>
          -- Shape: check if already seen at this level; emit if new.
          let seenNow ← getSeen
          match recall lk.content seenNow with
          | some _ => step ks oseen todo toobig rest
          | none   => do
              emit (commentPreskel lk [] [] .Shape .Nada "")
              step ks oseen todo toobig rest
      | .Cohort lk size kids dups =>
          -- Cohort result: multiple guards, checked in order.
          if nstrands lk.content >= opts.optBound then
            -- Strand bound exceeded: add to toobig and continue.
            step ks oseen todo (lk :: toobig) rest
          else if opts.optGoalsSat && goalsPresent lk && noCounterExamples lk then do
            -- Goals satisfied mode: stop expanding this branch.
            let ns    := unrealized lk.content
            let shape := if ns.isEmpty then Kind.Shape else Kind.Fringe
            emit (commentPreskel lk [] ns shape .SatisfiesAll "satisfies all")
            step ks oseen todo toobig rest
          else if size <= 0 then do
            -- Empty cohort: nothing to expand.
            let ns := unrealized lk.content
            emit (commentPreskel lk [] ns .Ordinary .Dead "empty cohort")
            step ks oseen todo toobig rest
          else if opts.optDepth > 0 && lk.depth >= opts.optDepth then do
            -- Depth bound: mark as fringe and stop.
            let ns := unrealized lk.content
            emit (commentPreskel lk [] ns .Fringe .Nada "")
            step ks oseen todo toobig rest
          else do
            -- Normal case: expand kids into todo, updating step count and seen.
            let seenNow ← getSeen
            let (n', seenNew, todo', dups') := kids.foldl (nextK lk) (n, seenNow, todo, dups)
            modify fun s => { s with stepN := n', seen := seenNew }
            let ns  := unrealized lk.content
            let u   := size - dups'.length
            let msg := s!"{size} in cohort - {u} not yet seen"
            emit (commentPreskel lk dups'.reverse ns .Ordinary .Nada msg)
            step ks oseen todo' toobig rest

/-- Process one complete breadth-first level.
    Mirrors `breadth :: Options -> Handle -> [Preskel] -> Int -> Int -> Seen ->
                       [LPreskel] -> [LPreskel] -> IO ()`.

    `SolveState.seen` is the INNER seen for this level (reset to void at the
    start of each level by `breadth`, accumulated by `step`, and merged with
    the outer seen at the end of the level). -/
partial def breadth (ks : List Preskel) (todo toobig : List LPreskel) : SolveM Unit := do
  match (todo, toobig) with
  | ([], []) =>
      emit (comment "Nothing left to do")
      solve ks
  | ([], _) =>
      emit (comment "Strand bound exceeded--aborting run")
      dump toobig.reverse "Strand bound exceeded"
  | _ =>
      let seenNow ← getSeen
      let opts    ← getOpts
      -- Map branch over the todo list (Haskell: parMap -- Lean: plain map).
      let reducts := todo.map (branch opts seenNow)
      -- Reset inner seen so that step accumulates fresh entries.
      setSeen void
      step ks seenNow [] toobig reducts

/-- Select the reduction mode (with or without isomorphism checks).
    Mirrors `mode :: Options -> Handle -> [Preskel] -> Int -> Int -> Seen ->
                    [LPreskel] -> IO ()`. -/
partial def mode (ks : List Preskel) (todo : List LPreskel) : SolveM Unit := do
  let opts ← getOpts
  if opts.optNoIsoChk then fast ks todo
  else breadth ks todo []

/-- Apply collapse until all possibilities are exhausted, building the
    breadth-level todo list.
    Mirrors `search :: ... -> [LPreskel] -> [LPreskel] -> IO ()`.

    - `todo` : preskeletons still to collapse
    - `done` : preskeletons already collapsed (accumulated in reverse) -/
partial def search (ks : List Preskel) (todo done : List LPreskel) : SolveM Unit := do
  match todo with
  | [] => mode ks done.reverse
  | lk :: rest =>
      let kids := (collapse lk.content).flatMap simplify
      let n       ← getStep
      let seenNow ← getSeen
      let (n', seen', todo', _) := kids.foldl (nextK lk) (n, seenNow, rest, [])
      modify fun s => { s with stepN := n', seen := seen' }
      search ks todo' (lk :: done)

/-- Apply rewrite rules before handing off to search.
    Mirrors `begin :: Options -> Handle -> [Preskel] -> Int -> Int -> Seen ->
                     LPreskel -> IO ()`. -/
partial def begin (ks : List Preskel) (lk : LPreskel) : SolveM Unit := do
  let k := lk.content
  match rewrite k with
  | none      => search ks [lk] []
  | some kids => do
      emit (commentPreskel lk [] (unrealized k) .Ordinary .Nada
             "Not closed under rules")
      let n       ← getStep
      let seenNow ← getSeen
      let (n', seen', todo', _) := kids.foldl (nextK lk) (n, seenNow, [], [])
      modify fun s => { s with stepN := n', seen := seen' }
      search ks todo'.reverse []

/-- Top-level loop: process one problem at a time.
    Mirrors `solve :: Options -> Handle -> [Preskel] -> Int -> IO ()`.

    Steps:
    1. Display the protocol.
    2. Call `firstSkeleton` to skeletonize the input.
    3. If the input was already a skeleton, hand off to `begin` directly.
    4. If not, emit it as a preskeleton annotation, then hand off to `begin`.
    5. Recurse on the remaining problems. -/
partial def solve (ks : List Preskel) : SolveM Unit := do
  match ks with
  | [] => pure ()   -- Done; caller is responsible for closing the handle.
  | k :: rest =>
      emit (displayProt (protocol k))
      let n    ← getStep
      let opts ← getOpts
      match firstSkeleton k with
      | [] =>
          -- Cannot be made into a skeleton.
          let lk : LPreskel := { content := k, label := n, depth := 0,
                                  parentLabel := none }
          emit (commentPreskel lk [] (unrealized k) .Ordinary .Dead
                 "Input cannot be made into a skeleton--nothing to do")
          modify fun s => { s with stepN := n + 1 }
          solve rest
      | [k'] =>
          if isomorphic (gist k) (gist k') then do
            -- Input was already a skeleton.
            let lk' : LPreskel := { content := k', label := n, depth := 0,
                                     parentLabel := none }
            modify fun s => { s with stepN     := n + 1,
                                     seen      := hist (k', n),
                                     stepLimit := n + opts.optLimit }
            begin rest lk'
          else do
            -- Input was not yet a skeleton.
            let lk  : LPreskel := { content := k,  label := n,     depth := -1,
                                     parentLabel := none }
            let lk' : LPreskel := { content := k', label := n + 1, depth := 0,
                                     parentLabel := some n }
            emit (commentPreskel lk [] (unrealized k) .Ordinary .Preskeleton
                   "Not a skeleton")
            modify fun s => { s with stepN     := n + 2,
                                     seen      := hist (k', n + 1),
                                     stepLimit := n + opts.optLimit }
            begin rest lk'
      | _ => panic! "Reduction.solve: can't handle more than one skeleton"

end  -- mutual

-- ── IO entry point ────────────────────────────────────────────────────────────

/-- Run the CPSA reduction loop.
    Mirrors the top-level call `solve opts h preskeletons 0` in the Haskell source.

    The caller is responsible for opening and closing `handle`; `runSolver`
    does NOT close it (unlike the Haskell which calls `hClose h` at the end
    of `solve`). -/
def runSolver (opts : Options) (handle : IO.FS.Stream)
    (ks : List Preskel) : IO Unit := do
  let initState : SolveState :=
    { stepN      := 0,
      stepLimit  := opts.optLimit,
      seen       := void,
      handle     := handle,
      opts       := opts }
  let _ ← StateT.run (solve ks) initState
  pure ()

end Cpsa2Lean.Reduction
