/-
LeanCPSA.Strand

Port of CPSA.Strand (MITRE cpsa).

Copyright (c) 2026 Paul D. Rowe

Instance and preskeleton data structures and support functions.

Copyright (c) 2009 The MITRE Corporation

This program is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.
-/

/-
Defines instances (role instantiations), preskeletons, strands, vertices,
and the full bundle-analysis machinery.

Stage 1: Compile-time switches, Instance structure, grow, bldInstance,
         mkListener, addIvars, instVars, listenerTerm.
Stage 2: FTerm/Fact types, graph infrastructure (GraphNode, GraphStrand, Graph,
         graph, graphEdges, graphClose, nodeGraphCloseAll), Shared, Gist,
         Preskel structure, and basic preskeleton accessors.
-/

import LeanCPSA.Protocol
import LeanCPSA.Channel
import LeanCPSA.Operation

namespace LeanCPSA.Strand

open LeanCPSA.Algebra
open LeanCPSA.Channel
open LeanCPSA.Protocol
open LeanCPSA.Operation (Operation Sid Node Pair Cause)
open LeanCPSA.Lib (assertError RBSet nats adjoin)

-- ── Compile-time switches ─────────────────────────────────────────────────────

-- Do not do multistrand thinning.
def useSingleStrandThinning : Bool := false

-- Sanity check: ensure no role variable occurs in a skeleton.
def useCheckVars : Bool := false

def useThinningDuringCollapsing : Bool := false

def useThinningWhileSolving : Bool := true

def useNoOrigPreservation : Bool := false

-- Use Pruning instead of thinning.
def usePruning : Bool := false

-- When using pruning use strong version.
def useStrongPruning : Bool := true

-- Check terms in preskeletons, should be off by default.
def useWellFormedTerms : Bool := false

-- Don't do variable separation if False.
def useVariableSeparation : Bool := true

-- Should we do the full node deletion?
def generalizeOnlyByDeletion : Bool := false

-- When doing deletion, should we delete *only* listener strands?
def generalizeDeleteOnlyListeners : Bool := false

-- Maximum number of variable-separation candidates to consider.
def separateVariablesLimit : Nat := 1024

-- ── Instance ──────────────────────────────────────────────────────────────────

/-- An instance of a role: a role with variables replaced by concrete terms.
    The trace may be shorter than the role's trace (truncated from the end).
    Mirrors `data Instance = Instance { role, env, trace, height }`. -/
structure Instance where
  role   : Role
  env    : Env
  trace  : Trace
  height : Int
  deriving Repr

-- Required for assertError in functions that return Gen × Instance.
private instance : Inhabited Role :=
  ⟨{ rname     := "",
     rvars     := [],
     rtrace    := [],
     rnon      := [],
     rpnon     := [],
     runique   := [],
     runiqgen  := [],
     rabsent   := [],
     rconf     := [],
     rauth     := [],
     rcomment  := [],
     rsearch   := false,
     rnorig    := [],
     rpnorig   := [],
     ruorig    := [],
     rugen     := [],
     rabs      := [],
     rpconf    := [],
     rpauth    := [],
     rpriority := [] }⟩

instance : Inhabited Instance :=
  ⟨{ role := default, env := emptyEnv, trace := [], height := 0 }⟩

-- Required for foldVars calls with TermSet accumulator.
private instance : Inhabited TermSet := ⟨RBSet.empty⟩

-- ── makeInstance ──────────────────────────────────────────────────────────────

private def makeInstance (role : Role) (env : Env) (trace : Trace) : Instance :=
  { role   := role,
    env    := env,
    trace  := trace,
    height := Int.ofNat trace.length }

-- ── grow ──────────────────────────────────────────────────────────────────────

/-- For each term that matches itself in the environment, extend the mapping
    so that the term maps to one with a fresh set of variables.
    Mirrors `grow :: [Term] -> Gen -> Env -> (Gen, Env)`. -/
private def grow : List Term → Gen → Env → Gen × Env
  | [],      gen, env => (gen, env)
  | t :: ts, gen, env =>
    match termMatch t t (gen, env) with
    | [] => grow ts gen env
    | _  =>
      let (gen', t') := clone gen t
      match termMatch t t' (gen', env) with
      | (gen'', env') :: _ => grow ts gen'' env'
      | []                 => assertError "Strand.grow: Internal error"

-- ── bldInstance ───────────────────────────────────────────────────────────────

/-- Inner loop for `bldInstance`: zip-match role events against instance events,
    building an environment. Haskell list-monad `do` maps to `flatMap`.
    Mirrors `loop` inside `bldInstance`. -/
private partial def bldInstance_loop
    (role : Role) (instTrace : Trace)
    : List Event → List Event → GenEnv → List (Gen × Instance)
  | _,              [],              ge =>
      [(ge.1, makeInstance role ge.2 instTrace)]
  | .In  t :: c,   .In  t' :: c',  ge =>
      (cmMatch t t' ge).flatMap (fun ge' => bldInstance_loop role instTrace c c' ge')
  | .Out t :: c,   .Out t' :: c',  ge =>
      (cmMatch t t' ge).flatMap (fun ge' => bldInstance_loop role instTrace c c' ge')
  | _,              _,              _  => []

/-- Build an instance from a role and a trace.
    Returns the empty list if the trace is not an instance of the given role.
    Mirrors `bldInstance :: Role -> Trace -> Gen -> [(Gen, Instance)]`. -/
def bldInstance (role : Role) (trace : Trace) (gen : Gen) : List (Gen × Instance) :=
  if trace.isEmpty then
    assertError "Strand.bldInstance: Bad trace"
  else
    bldInstance_loop role trace role.rtrace trace (gen, emptyEnv)

-- ── mkInstance ────────────────────────────────────────────────────────────────

/-- Create a fresh instance of the given height.  The environment specifies how
    to map some variables in the role's trace; unmapped variables are
    instantiated with fresh variables to avoid naming conflicts.
    Mirrors `mkInstance :: Gen -> Role -> Env -> Int -> (Gen, Instance)`. -/
def mkInstance (gen : Gen) (role : Role) (env : Env) (height : Int) : Gen × Instance :=
  let rheight := Int.ofNat role.rtrace.length
  if height < 1 || height > rheight then
    assertError "Strand.mkInstance: Bad strand height"
  else
    let (gen', env') := grow role.rvars gen env
    let trace'       := (role.rtrace.take height.toNat).map (evtMap (instantiate env'))
    match bldInstance role trace' gen' with
    | (gen'', inst) :: _ => (gen'', inst)
    | []                 => assertError "Strand.mkInstance: Not an instance"

-- ── mkListener ────────────────────────────────────────────────────────────────

/-- Create a listener instance for the given term.
    Mirrors `mkListener :: Prot -> Gen -> Term -> (Gen, Instance)`. -/
def mkListener (p : Prot) (gen : Gen) (term : Term) : Gen × Instance :=
  match bldInstance p.listenerRole [.In (.Plain term), .Out (.Plain term)] gen with
  | [x] => x
  | _   => assertError "Strand.mkListener: Cannot build an instance of a listener"

-- ── maybeShowInstance ─────────────────────────────────────────────────────────

/-- Show an instance if its role name is in the given list (debugging helper).
    Mirrors `maybeShowInstance :: [String] -> Instance -> Maybe String`. -/
private def maybeShowInstance (rolenames : List String) (inst : Instance) : Option String :=
  if rolenames.contains inst.role.rname then
    some s!"({inst.role.rname} {inst.height})"
  else
    none

-- ── addIvars / instVars ───────────────────────────────────────────────────────

/-- Add to `s` the variables that are in the range of instance `i`.
    Mirrors `addIvars :: Set Term -> Instance -> Set Term`. -/
def addIvars (s : TermSet) (i : Instance) : TermSet :=
  (reify i.role.rvars i.env).foldl
    (fun acc (_, t) => foldVars (fun a x => RBSet.insert x a) acc t)
    s

/-- All variables in the ranges of the given instances.
    Mirrors `instVars :: [Instance] -> [Term]`. -/
private def instVars (insts : List Instance) : List Term :=
  RBSet.toList (insts.foldl addIvars RBSet.empty)

-- ── listenerTerm ──────────────────────────────────────────────────────────────

/-- Extract the payload term of a listener strand's first event, if any.
    Returns `none` for non-listener strands or channel messages.
    Mirrors `listenerTerm :: Instance -> Maybe Term`. -/
def listenerTerm (inst : Instance) : Option Term :=
  if inst.role.rname == "" then
    match inst.trace.head? with
    | none     => none
    | some evt =>
      match inbnd evt with
      | some (.Plain t) => some t
      | _               => none
  else
    none

-- ── Stage 2 ───────────────────────────────────────────────────────────────────

-- ── FTerm / Fact ──────────────────────────────────────────────────────────────

/-- A fact term: either a strand identifier or a term.
    Mirrors `data FTerm = FSid Sid | FTerm Term`. -/
inductive FTerm where
  | FSid   : Sid  → FTerm
  | ofTerm : Term → FTerm   -- named `ofTerm`; mirrors Haskell constructor `FTerm`
  deriving BEq, Repr

instance : Inhabited FTerm := ⟨.FSid 0⟩

/-- A named fact with a list of fact-terms.
    Mirrors `data Fact = Fact String [FTerm]`. -/
structure Fact where
  name  : String
  terms : List FTerm
  deriving BEq, Repr

instance : Inhabited Fact := ⟨{ name := "", terms := [] }⟩

def substFTerm (s : Subst) : FTerm → FTerm
  | .ofTerm t => .ofTerm (substitute s t)
  | f         => f

def substFact (s : Subst) (fact : Fact) : Fact :=
  { fact with terms := fact.terms.map (substFTerm s) }

def instFTerm (env : Env) : FTerm → FTerm
  | .ofTerm t => .ofTerm (instantiate env t)
  | f         => f

def instFact (env : Env) (fact : Fact) : Fact :=
  { fact with terms := fact.terms.map (instFTerm env) }

def updateFTerm (f : Sid → Sid) : FTerm → FTerm
  | .FSid s => .FSid (f s)
  | ft      => ft

def updateFact (f : Sid → Sid) (fact : Fact) : Fact :=
  { fact with terms := fact.terms.map (updateFTerm f) }

def instUpdateFTerm (env : Env) (f : Sid → Sid) : FTerm → FTerm
  | .FSid s   => .FSid (f s)
  | .ofTerm t => .ofTerm (instantiate env t)

def instUpdateFact (env : Env) (f : Sid → Sid) (fact : Fact) : Fact :=
  { fact with terms := fact.terms.map (instUpdateFTerm env f) }

private def addFvars (vs : TermSet) (fact : Fact) : TermSet :=
  fact.terms.foldl (fun acc ft =>
    match ft with
    | .FSid _   => acc
    | .ofTerm t => foldVars (fun a x => RBSet.insert x a) acc t)
    vs

/-- Variables in facts that do not appear in any instance range.
    Mirrors `factVars :: [Instance] -> [Fact] -> [Term]`. -/
def factVars (insts : List Instance) (facts : List Fact) : List Term :=
  let ivars := insts.foldl addIvars RBSet.empty
  let fvars := facts.foldl addFvars RBSet.empty
  (RBSet.toList fvars).filter (fun t => !ivars.contains t)

-- ── GraphNode / GraphStrand ───────────────────────────────────────────────────

-- Required for the default event in graph-node construction.
private instance : Inhabited ChMsg := ⟨.Plain default⟩
private instance : Inhabited Event := ⟨.In default⟩

/-- A node in the preskeleton graph.  Predecessors are stored as `Node` indices
    rather than pointers to avoid circular references (Lean is strict).
    Mirrors `data GraphNode e i = GraphNode { event, preds, strand, pos }`. -/
structure GraphNode where
  event      : Event
  preds      : List Node   -- predecessor nodes by (Sid, Int) index
  strandId   : Sid         -- which strand this node belongs to (field; cf. accessor `strand`)
  pos        : Int

instance : Inhabited GraphNode :=
  ⟨{ event := default, preds := [], strandId := 0, pos := 0 }⟩

instance : BEq GraphNode where
  beq n0 n1 := n0.strandId == n1.strandId && n0.pos == n1.pos

instance : Ord GraphNode where
  compare n0 n1 :=
    match compare n0.strandId n1.strandId with
    | .eq => compare n0.pos n1.pos
    | o   => o

/-- A strand in the preskeleton graph.
    Mirrors `data GraphStrand e i = GraphStrand { inst, nodes, sid }`. -/
structure GraphStrand where
  inst  : Instance
  nodes : List GraphNode
  sid   : Sid

instance : Inhabited GraphStrand :=
  ⟨{ inst := default, nodes := [], sid := 0 }⟩

instance : BEq GraphStrand where
  beq s0 s1 := s0.sid == s1.sid

instance : Ord GraphStrand where
  compare s0 s1 := compare s0.sid s1.sid

-- Exported accessor names matching Haskell field names.
def GraphNode.strand (n : GraphNode) : Sid := n.strandId

/-- Extract the `Node` identifier from a graph node.
    Mirrors `graphNode :: GraphNode e i -> Node`. -/
def graphNode (n : GraphNode) : Node := (n.strandId, n.pos)

/-- An ordering edge between two graph nodes.  Mirrors `type GraphEdge e i`. -/
abbrev GraphEdge := GraphNode × GraphNode

/-- Extract a `Pair` from a graph edge.  Mirrors `graphPair`. -/
def graphPair (e : GraphEdge) : Pair := (graphNode e.1, graphNode e.2)

/-- The graph of a preskeleton.  Mirrors `data Graph e i = Graph { gstrands, gedges }`. -/
structure Graph where
  gstrands : List GraphStrand
  gedges   : List GraphEdge

-- ── graph ─────────────────────────────────────────────────────────────────────

/-- Build a preskeleton graph from a list of instances and ordering pairs.
    Strand-succession edges are embedded in each node's `preds` list.
    Specialised to `Event`/`Instance` (the only instantiation used in CPSA).
    Mirrors `graph :: (i -> [d]) -> (i -> Int) -> [i] -> [Pair] -> Graph d i`. -/
private def buildGraph (insts : List Instance) (pairs : List Pair) : Graph :=
  let mkPreds (n : Node) : List Node :=
    let direct := pairs.filterMap (fun (n0, n1) => if n1 == n then some n0 else none)
    if n.2 > 0 then (n.1, n.2 - 1) :: direct else direct
  let strands : List GraphStrand :=
    (List.zip (List.range insts.length) insts).map (fun (sidNat, inst) =>
      let sid  := Int.ofNat sidNat
      let h    := inst.height.toNat
      let evts := inst.trace
      let nodes : List GraphNode := (List.range h).map (fun posNat =>
        { event    := (evts.get? posNat).getD default,
          preds    := mkPreds (sid, Int.ofNat posNat),
          strandId := sid,
          pos      := Int.ofNat posNat })
      { inst := inst, sid := sid, nodes := nodes })
  let getNode (n : Node) : Option GraphNode :=
    strands.get? n.1.toNat >>= (fun s => s.nodes.get? n.2.toNat)
  let edges : List GraphEdge :=
    pairs.filterMap (fun (n0, n1) =>
      match getNode n0, getNode n1 with
      | some v0, some v1 => some (v0, v1)
      | _, _             => none)
  { gstrands := strands, gedges := edges }

-- ── Graph edge helpers ────────────────────────────────────────────────────────

/-- All edges in the graph including strand-succession edges encoded in preds.
    Mirrors `graphEdges :: [GraphStrand e i] -> [GraphEdge e i]`. -/
def graphEdges (strands : List GraphStrand) : List GraphEdge :=
  let getNode (n : Node) : Option GraphNode :=
    strands.get? n.1.toNat >>= (fun s => s.nodes.get? n.2.toNat)
  strands.flatMap (fun s =>
    s.nodes.flatMap (fun src =>
      src.preds.filterMap (fun predNode =>
        getNode predNode |>.map (fun dst => (dst, src)))))

/-- All edges as pairs of nodes.
    Mirrors `nodeGraphEdges :: [GraphStrand e i] -> [Pair]`. -/
def nodeGraphEdges (strands : List GraphStrand) : List Pair :=
  strands.flatMap (fun s =>
    s.nodes.flatMap (fun src =>
      src.preds.map (fun dst => (dst, graphNode src))))

-- ── graphPrecedes ─────────────────────────────────────────────────────────────

/-- Does `start` precede `end_` in the graph?
    Looks up predecessors by node index using the given `getNode` function.
    Mirrors `graphPrecedes :: GraphNode e i -> GraphNode e i -> Bool`. -/
private partial def graphPrecedes
    (getNode : Node → Option GraphNode) (start : GraphNode) : GraphNode → Bool
  | end_ =>
    let predecessors := end_.preds.filterMap getNode
    predecessors.any (· == start) || predecessors.any (graphPrecedes getNode start)

-- ── graphReduce ───────────────────────────────────────────────────────────────

private partial def graphReduce_loop
    (getNode : Node → Option GraphNode) (dst : GraphNode)
    : List GraphNode → List GraphNode → Bool
  | [],      _    => true
  | n :: ns, seen =>
    if n == dst then false
    else if seen.contains n then graphReduce_loop getNode dst ns seen
    else
      let preds := n.preds.filterMap getNode
      graphReduce_loop getNode dst (preds ++ ns) (n :: seen)

/-- Remove edges implied by other edges (transitive reduction).
    Mirrors `graphReduce :: [GraphEdge e i] -> [GraphEdge e i]`. -/
private def graphReduce (getNode : Node → Option GraphNode) (orderings : List GraphEdge)
    : List GraphEdge :=
  orderings.filter (fun (dst, src) =>
    let preds := src.preds.filterMap getNode
    graphReduce_loop getNode dst (preds.erase dst) [src])

-- ── graphClose ────────────────────────────────────────────────────────────────

/-- Compute the transitive closure of edges, omitting same-strand pairs.
    Uses a fixed-point iteration rather than Haskell's knot-tying mutual recursion.
    Mirrors `graphClose :: [GraphEdge e i] -> [GraphEdge e i]`. -/
private partial def graphClose
    (getNode : Node → Option GraphNode) (orderings : List GraphEdge)
    : List GraphEdge :=
  let sameStrands (e : GraphEdge) := e.1.strandId == e.2.strandId
  let step (ords : List GraphEdge) : Bool × List GraphEdge :=
    ords.foldl (fun (changed, acc) (n0, n1) =>
      let newEdges := n0.preds.filterMap (fun predNode =>
        getNode predNode |>.map (fun n => (n, n1)))
      newEdges.foldl (fun (ch, acc) p =>
        if acc.contains p then (ch, acc) else (true, p :: acc))
        (changed, acc))
      (false, ords)
  let rec fixpoint (ords : List GraphEdge) : List GraphEdge :=
    let (changed, ords') := step ords
    if changed then fixpoint ords' else ords
  (fixpoint orderings).filter (not ∘ sameStrands)

-- ── nodeGraphCloseAll ─────────────────────────────────────────────────────────

/-- Compute the full transitive closure of node-pair orderings (including
    same-strand pairs).  Mirrors `nodeGraphCloseAll :: [Pair] -> [Pair]`. -/
private partial def nodeGraphCloseAll_loop
    (initOrd : List Pair) : List Pair → Bool → List Pair → List Pair
  | ords, false, [] => ords
  | ords, true,  [] => nodeGraphCloseAll_loop initOrd ords false ords
  | ords, rpt, (n0, n1) :: pairs =>
    let direct := initOrd.filterMap (fun (a, b) => if b == n0 then some a else none)
    let myPreds := if n0.2 == 0 then direct else adjoin (n0.1, n0.2 - 1) direct
    let rec inner (ords : List Pair) (rpt : Bool) : List Node → List Pair
      | [] => nodeGraphCloseAll_loop initOrd ords rpt pairs
      | n :: rest =>
        if ords.contains (n, n1) then inner ords rpt rest
        else inner ((n, n1) :: ords) true rest
    inner ords rpt myPreds

/-- Compute the full transitive closure of node-pair orderings.
    Mirrors `nodeGraphCloseAll :: [Pair] -> [Pair]`. -/
def nodeGraphCloseAll (orderings : List Pair) : List Pair :=
  nodeGraphCloseAll_loop orderings orderings false orderings

-- ── Shared ────────────────────────────────────────────────────────────────────

/-- The shared (immutable) part of a preskeleton.
    Mirrors `data Shared = Shared { prot, goals, comments }`. -/
structure Shared where
  prot     : Prot
  goals    : List Goal
  comments : List (LeanCPSA.Lib.SExpr Unit)
  deriving Repr

-- ── Gist ──────────────────────────────────────────────────────────────────────

/-- A compact summary of a preskeleton used for isomorphism checking.
    Mirrors `data Gist = Gist { ggen, gtraces, gorderings, gnon, ... }`. -/
structure Gist where
  ggen       : Gen
  gtraces    : List (Int × Trace)
  gorderings : List Pair
  gnon       : List Term
  gpnon      : List Term
  gunique    : List Term
  guniqgen   : List Term
  gabsent    : List (Term × Term)
  ggenSt     : List Term
  gfacts     : List Fact
  gfvars     : List Term
  nvars      : Int
  ntraces    : Int
  briefs     : List (Int × Int)
  norderings : Int
  nnon       : Int
  npnon      : Int
  nunique    : Int
  nuniqgen   : Int
  nabsent    : Int
  ngenSt     : Int
  nfacts     : Int
  nfvars     : Int

instance : Inhabited Gist :=
  ⟨{ ggen := default, gtraces := [], gorderings := [], gnon := [], gpnon := [],
     gunique := [], guniqgen := [], gabsent := [], ggenSt := [], gfacts := [],
     gfvars := [], nvars := 0, ntraces := 0, briefs := [], norderings := 0,
     nnon := 0, npnon := 0, nunique := 0, nuniqgen := 0, nabsent := 0,
     ngenSt := 0, nfacts := 0, nfvars := 0 }⟩

-- ── Preskel ───────────────────────────────────────────────────────────────────

/-- A preskeleton: a partially-ordered collection of role instances.
    Mirrors `data Preskel = Preskel { gen, shared, insts, strands, ... }`.
    Note: `pov : Option Preskel` is a self-referential field (allowed because
    `Preskel` appears strictly positively under `Option`). -/
structure Preskel where
  gen        : Gen
  shared     : Shared
  insts      : List Instance
  strands    : List GraphStrand   -- type alias Strand = GraphStrand
  orderings  : List Pair
  kgpOrds    : List Pair
  kgpOrdsAll : List Pair
  edges      : List GraphEdge     -- type alias Edge = GraphEdge
  knon       : List Term
  kpnon      : List Term
  kunique    : List Term
  kuniqgen   : List Term
  kabsent    : List (Term × Term)
  kprecur    : List Node
  kgenSt     : List Term
  kconf      : List Term
  kauth      : List Term
  kfacts     : List Fact
  kfvars     : List Term
  kpriority  : List (Node × Int)
  korig      : List (Term × List Node)
  kugen      : List (Term × List Node)
  pov        : Option Preskel
  strandids  : List Sid
  tc         : List Pair
  tcComputed : Bool           -- true once addExpensiveFields has been called
  kgist      : Gist
  operation  : Operation
  krules     : List String
  pprob      : List Sid
  prob       : List Sid

-- ── Inhabited instances required for assertError ───────────────────────────────

private instance : Inhabited Goal :=
  ⟨{ uvars := [], antec := [], consq := [], concl := [] }⟩

private instance : Inhabited Rule :=
  ⟨{ rlname := "", rlgoal := default, rlcomment := [] }⟩

private instance : Inhabited Prot :=
  ⟨{ pname := "", alg := "", pgen := default,
     psig := LeanCPSA.Signature.defaultSig,
     roles := [], listenerRole := default,
     nullaryrules := [], unaryrules := [], generalrules := [],
     userrules := [], generatedrules := [],
     varsAllAtoms := false, pcomment := [] }⟩

private instance : Inhabited Shared :=
  ⟨{ prot := default, goals := [], comments := [] }⟩

private instance : Inhabited Operation := ⟨.New⟩

instance : Inhabited Preskel :=
  ⟨{ gen := default, shared := default, insts := [], strands := [],
     orderings := [], kgpOrds := [], kgpOrdsAll := [], edges := [],
     knon := [], kpnon := [], kunique := [], kuniqgen := [], kabsent := [],
     kprecur := [], kgenSt := [], kconf := [], kauth := [], kfacts := [],
     kfvars := [], kpriority := [], korig := [], kugen := [],
     pov := none, strandids := [], tc := [], tcComputed := false, kgist := default,
     operation := .New, krules := [], pprob := [], prob := [] }⟩

-- Type aliases matching the Haskell source (defined after Preskel to avoid
-- ambiguity between the `Strand` alias and the `LeanCPSA.Strand` namespace).
abbrev KStrand := GraphStrand   -- mirrors `type Strand = GraphStrand Event Instance`
abbrev Vertex  := GraphNode     -- mirrors `type Vertex = GraphNode Event Instance`
abbrev Edge    := GraphEdge     -- mirrors `type Edge   = GraphEdge Event Instance`

-- ── Preskel accessors ─────────────────────────────────────────────────────────

def protocol (k : Preskel) : Prot      := k.shared.prot
def kgoals   (k : Preskel) : List Goal := k.shared.goals
def kcomment (k : Preskel) : List (LeanCPSA.Lib.SExpr Unit) := k.shared.comments

def updateStrandMap (sm : List Sid) (k : Preskel) : Preskel :=
  { k with operation := LeanCPSA.Operation.addStrandMap sm k.operation }

def strandInst (k : Preskel) (s : Sid) : Instance :=
  if s.toNat < k.insts.length then k.insts.get! s.toNat
  else assertError s!"strandInst: index {s} is too big for insts: {repr k.operation}"

def nstrands (k : Preskel) : Int := Int.ofNat k.strandids.length

def vertex (k : Preskel) (n : Node) : Vertex :=
  match k.strands.get? n.1.toNat with
  | none   => assertError s!"vertex: strand {n.1} out of range"
  | some s =>
    match s.nodes.get? n.2.toNat with
    | none   => assertError s!"vertex: position {n.2} out of range"
    | some v => v

-- ── Origination/generation node helpers ───────────────────────────────────────

def originationNodes (strands : List GraphStrand) (u : Term) : Term × List Node :=
  (u, strands.reverse.flatMap (fun s =>
    (originationPos u s.inst.trace).toList.map (fun p => (s.sid, p))))

def generationNodes (strands : List GraphStrand) (u : Term) : Term × List Node :=
  (u, strands.reverse.flatMap (fun s =>
    (generationPos u s.inst.trace).toList.map (fun p => (s.sid, p))))

def uniqOrig (k : Preskel) : List Term :=
  k.korig.reverse.filterMap (fun (t, ns) => match ns with | [_] => some t | _ => none)

def uniqGen (k : Preskel) : List Term :=
  k.kugen.reverse.filterMap (fun (t, ns) => match ns with | [_] => some t | _ => none)

-- ── Term / channel accessors ──────────────────────────────────────────────────

/-- All unique terms in a list of instance traces.
    Mirrors `iterms :: [Instance] -> [Term]`. -/
def iterms (insts : List Instance) : List Term :=
  (insts.flatMap (fun i => i.trace.map evtTerm)).eraseDups

/-- The terms used in the preskeleton strands.
    Mirrors `kterms :: Preskel -> [Term]`. -/
def kterms (k : Preskel) : List Term := iterms k.insts

/-- All unique channels used in a list of instance traces.
    Mirrors `ichans :: [Instance] -> [Term]`. -/
def ichans (insts : List Instance) : List Term :=
  (insts.flatMap (fun i => i.trace.filterMap evtChan)).eraseDups

/-- The channels used in the preskeleton strands.
    Mirrors `kchans :: Preskel -> [Term]`. -/
def kchans (k : Preskel) : List Term := ichans k.insts

/-- Variables in the preskeleton (ranges of instance environments).
    Mirrors `kvars :: Preskel -> [Term]`. -/
def kvars (k : Preskel) : List Term := instVars k.insts

-- ── Gist construction ─────────────────────────────────────────────────────────

/-- Summarise a trace as a single integer (encodes the in/out pattern).
    Mirrors `brief :: Trace -> Int`. -/
private def brief : Trace → Int
  | []           => 0
  | .In  _ :: c => 1 + 3 * brief c
  | .Out _ :: c => 2 + 3 * brief c

/-- Convert a list of integers into a sorted multiset representation.
    Mirrors `multiset :: [Int] -> [(Int, Int)]`. -/
private def multiset (brf : List Int) : List (Int × Int) :=
  let rec insert : List (Int × Int) → Int → List (Int × Int)
    | [],              b => [(b, 1)]
    | (k, n) :: rest, b =>
      if k == b then (k, n + 1) :: rest
      else if k > b then (b, 1) :: (k, n) :: rest
      else (k, n) :: insert rest b
  brf.foldl insert []

/-- Build the gist from a preskeleton.
    Mirrors `mkGist :: Preskel -> Gist`. -/
def mkGist (k : Preskel) : Gist :=
  let gtraces    := k.insts.map (fun i => (brief i.trace, i.trace))
  let gorderings := k.orderings
  let gnon       := k.knon
  let gpnon      := k.kpnon
  let gunique    := k.kunique
  let guniqgen   := k.kuniqgen
  let gabsent    := k.kabsent
  let ggenSt     := k.kgenSt
  let gfacts     := k.kfacts
  let gfvars     := k.kfvars
  { ggen       := k.gen,
    gtraces    := gtraces,
    gorderings := gorderings,
    gnon       := gnon,
    gpnon      := gpnon,
    gunique    := gunique,
    guniqgen   := guniqgen,
    gabsent    := gabsent,
    ggenSt     := ggenSt,
    gfacts     := gfacts,
    gfvars     := gfvars,
    nvars      := Int.ofNat (kvars k).length,
    ntraces    := Int.ofNat gtraces.length,
    briefs     := multiset (gtraces.map Prod.fst),
    norderings := Int.ofNat gorderings.length,
    nnon       := Int.ofNat gnon.length,
    npnon      := Int.ofNat gpnon.length,
    nunique    := Int.ofNat gunique.length,
    nuniqgen   := Int.ofNat guniqgen.length,
    nabsent    := Int.ofNat gabsent.length,
    ngenSt     := Int.ofNat ggenSt.length,
    nfacts     := Int.ofNat gfacts.length,
    nfvars     := Int.ofNat gfvars.length }

/-- Return the cached gist of a preskeleton.  Mirrors `gist :: Preskel -> Gist`. -/
def gist (k : Preskel) : Gist := k.kgist

-- ── Stage 3 ───────────────────────────────────────────────────────────────────

-- ── Edge direction check ──────────────────────────────────────────────────────

/-- True when the edge goes from an Out-event to an In-event (well-formed direction).
    Mirrors `pairWellOrdered :: Edge -> Bool`. -/
def pairWellOrdered (e : GraphEdge) : Bool :=
  match e.1.event, e.2.event with
  | .Out _, .In _ => true
  | _,      _     => false

/-- True when every edge in the preskeleton is well-ordered (Out→In).
    Mirrors `wellOrdered :: Preskel -> Bool`. -/
def wellOrdered (k : Preskel) : Bool :=
  k.edges.all pairWellOrdered

-- ── Acyclicity ────────────────────────────────────────────────────────────────

/-- True when the node-ordering relation is acyclic.
    Uses a DFS postorder numbering; a back edge witnesses a cycle.
    Mirrors `acyclicOrder :: Preskel -> Bool`. -/
def acyclicOrder (k : Preskel) : Bool :=
  let strands := k.strands
  let getNode (n : Node) :=
    strands.get? n.1.toNat >>= fun s => s.nodes.get? n.2.toNat
  let allNodes := strands.flatMap (fun s => s.nodes)
  let adj (n : GraphNode) := n.preds.filterMap getNode
  LeanCPSA.Lib.isAcyclic compare adj allNodes

-- ── Role origination / generation checks ─────────────────────────────────────

/-- Every role unique-origination assumption mapped by an instance must
    originate on that instance's strand.
    Mirrors `roleOrigCheck :: Preskel -> Bool`. -/
def roleOrigCheck (k : Preskel) : Bool :=
  k.strands.all fun strand =>
    (strand.inst.role.ruorig).all fun (ru, pos) =>
      if pos < strand.inst.height then
        let t := instantiate strand.inst.env ru
        match k.korig.lookup t with
        | none    => true
        | some ns => ns.any fun (s, i) => strand.sid == s && i == pos
      else true

/-- Every role unique-generation assumption mapped by an instance must
    generate on that instance's strand.
    Mirrors `roleGenCheck :: Preskel -> Bool`. -/
def roleGenCheck (k : Preskel) : Bool :=
  k.strands.all fun strand =>
    (strand.inst.role.rugen.filter fun (u, _) => !isNum u).all fun (ru, pos) =>
      if pos < strand.inst.height then
        let t := instantiate strand.inst.env ru
        match k.kugen.lookup t with
        | none    => true
        | some ns => ns.any fun (s, i) => strand.sid == s && i == pos
      else true

-- ── Constituent + key-inverse helper ─────────────────────────────────────────

/-- True when `atom` is a constituent of `t`, or when the inverse of `atom`
    is a constituent of `t`.
    Mirrors `constituentModInv :: Term -> Term -> Bool`. -/
def constituentModInv (atom t : Term) : Bool :=
  constituent atom t ||
  match invertKey atom with
  | none    => false
  | some ik => constituent ik t

-- ── Well-formedness predicate ─────────────────────────────────────────────────

/-- Full well-formedness check for a preskeleton.
    Mirrors `preskelWellFormed :: Preskel -> Bool`. -/
def preskelWellFormed (k : Preskel) : Bool :=
  let terms := kterms k
  let vs    := kvars k
  varSubset k.knon terms &&
  varSubset k.kpnon terms &&
  k.knon.all    (fun t => terms.all (fun t' => !carriedBy t t')) &&
  k.kunique.all (fun t => terms.any (carriedBy t)) &&
  k.kuniqgen.all (fun t => terms.any (constituentModInv t)) &&
  k.kabsent.all  (fun (x, y) => varSubset [x, y] vs && x != y) &&
  k.kgenSt.all   (fun t => foldVars (fun b v => b && vs.contains v) true t) &&
  k.kconf.all    (fun c => foldVars (fun b v => b && vs.contains v) true c) &&
  k.kauth.all    (fun c => foldVars (fun b v => b && vs.contains v) true c) &&
  wellOrdered k && acyclicOrder k &&
  roleOrigCheck k &&
  roleGenCheck k

/-- True when all terms in the preskeleton's traces are well-formed
    (controlled by the `useWellFormedTerms` flag).
    Mirrors `traceWellFormed :: Preskel -> Bool`. -/
def traceWellFormed (k : Preskel) : Bool :=
  !useWellFormedTerms || termsWellFormed (kterms k)

-- ── checkVars ─────────────────────────────────────────────────────────────────

/-- Panic if any role variable from an instance also appears in the skeleton
    variables (controlled by `useCheckVars`).
    Mirrors `checkVars :: Preskel -> Preskel`. -/
def checkVars (k : Preskel) : Preskel :=
  let skelvars := kvars k
  let rolevars := k.insts.flatMap (fun i => i.role.rvars)
  rolevars.foldl (fun k v =>
    if skelvars.contains v
    then assertError s!"Strand.checkVars: role var {repr v} in skel"
    else k) k

-- ── newPreskel / newPreskelBasic / addExpensiveFields ────────────────────────

/-- Build a preskeleton with all *cheap* derived fields, but leave the
    expensive transitive-closure fields (`kgpOrds`, `kgpOrdsAll`, `tc`) empty.
    Callers that immediately feed the result to `wellFormedPreskel` should use
    this variant; `wellFormedPreskel` calls `addExpensiveFields` on success, so
    preskels that are rejected never pay the O(n²–n³) closure cost.
    Callers that need the full preskel immediately should use `newPreskel`. -/
private def newPreskelBasic (gen : Gen) (shared : Shared) (insts : List Instance)
    (orderings : List Pair) (non pnon unique uniqgen : List Term)
    (absent : List (Term × Term)) (precur : List Node) (genSt conf auth : List Term)
    (facts : List Fact) (prio : List (Node × Int))
    (oper : Operation) (rules : List String) (pprob prob : List Sid)
    (pov : Option Preskel) : Preskel :=
  let orderings' := orderings.eraseDups
  let unique'    := unique.eraseDups
  let uniqgen'   := uniqgen.eraseDups
  let facts'     := facts.eraseDups
  let g          := buildGraph insts orderings'
  let strands    := g.gstrands
  let edges      := g.gedges
  let orig       := unique'.map (originationNodes strands)
  let ugen       := uniqgen'.map (generationNodes strands)
  let strandids  := (nats insts.length).map Int.ofNat
  let k : Preskel := {
    gen        := gen,
    shared     := shared,
    insts      := insts,
    strands    := strands,
    orderings  := orderings',
    kgpOrds    := [],       -- filled in by addExpensiveFields
    kgpOrdsAll := [],       -- filled in by addExpensiveFields
    edges      := edges,
    knon       := non.eraseDups,
    kpnon      := pnon.eraseDups,
    kunique    := unique',
    kuniqgen   := uniqgen',
    kabsent    := absent.eraseDups,
    kprecur    := precur.eraseDups,
    kgenSt     := genSt.eraseDups,
    kconf      := conf.eraseDups,
    kauth      := auth.eraseDups,
    kfacts     := facts',
    kfvars     := factVars insts facts',
    kpriority  := prio,
    korig      := orig,
    kugen      := ugen,
    pov        := pov,
    strandids  := strandids,
    tc         := [],       -- filled in by addExpensiveFields
    tcComputed := false,    -- set to true by addExpensiveFields
    kgist      := default,
    operation  := oper,
    krules     := rules,
    pprob      := pprob,
    prob       := prob }
  let k := { k with kgist := mkGist k }
  if useCheckVars then checkVars k else k

/-- Compute and attach the expensive transitive-closure fields (`kgpOrds`,
    `kgpOrdsAll`, `tc`).  Idempotent: if `k.tcComputed` is already true the
    preskel is returned unchanged.  Call sites that need TC (e.g. `toSkeleton`,
    before `simplify`) invoke this explicitly; `wellFormedPreskel` no longer does
    so, keeping the hull-loop intermediates TC-free until truly needed. -/
def addExpensiveFields (k : Preskel) : Preskel :=
  if k.tcComputed then k
  else
    let strands  := k.strands
    let getNode (n : Node) :=
      strands.get? n.1.toNat >>= fun s => s.nodes.get? n.2.toNat
    let gpOrdsAll := nodeGraphCloseAll (nodeGraphEdges strands)
    let gpOrds    := gpOrdsAll.filter (fun (p : Pair) => p.1.1 != p.2.1)
    let tcEdges   := (graphClose getNode (graphEdges strands)).filter pairWellOrdered
    { k with kgpOrdsAll := gpOrdsAll, kgpOrds := gpOrds,
             tc := tcEdges.map graphPair, tcComputed := true }

/-- Well-formedness check returning the preskeleton in a list (success) or
    an empty list (failure).  Replaces the Haskell `MonadFail` constraint.
    Does NOT attach TC fields — callers that need them must call
    `addExpensiveFields` explicitly (e.g. `toSkeleton`, before `simplify`).
    Keeping `wellFormedPreskel` TC-free means hull intermediates avoid paying
    the O(n²–n³) closure cost; only the final surviving preskel pays it.
    Does NOT attach the expensive TC fields — that is deferred to the pipeline
    exit gate `homomorphismFilter`, so hull/skeletonize INTERMEDIATES (which call
    `wellFormedPreskel` on every step) never pay the O(n²–n³) closure cost.  Only
    the surviving outputs that pass through `homomorphismFilter` get TC.
    Mirrors `wellFormedPreskel :: MonadFail m => Preskel -> m Preskel`. -/
def wellFormedPreskel (k : Preskel) : List Preskel :=
  if preskelWellFormed k && traceWellFormed k then [k] else []

/-- Build a preskeleton, computing all derived fields (graph, origination nodes,
    transitive closure, gist).  This is the internal constructor.
    Mirrors `newPreskel :: Gen -> Shared -> [Instance] -> [Pair] -> ...`. -/
def newPreskel (gen : Gen) (shared : Shared) (insts : List Instance)
    (orderings : List Pair) (non pnon unique uniqgen : List Term)
    (absent : List (Term × Term)) (precur : List Node) (genSt conf auth : List Term)
    (facts : List Fact) (prio : List (Node × Int))
    (oper : Operation) (rules : List String) (pprob prob : List Sid)
    (pov : Option Preskel) : Preskel :=
  addExpensiveFields (newPreskelBasic gen shared insts orderings non pnon unique uniqgen
    absent precur genSt conf auth facts prio oper rules pprob prob pov)

-- ── renewPreskel ─────────────────────────────────────────────────────────────

/-- Rebuild all derived fields without TC.  Used for generalization candidates
    where TC is deferred to `Cohort.maximize` (before `simplify`). -/
private def renewPreskelBasic (k : Preskel) : Preskel :=
  newPreskelBasic k.gen k.shared k.insts k.orderings
    k.knon k.kpnon k.kunique k.kuniqgen
    k.kabsent k.kprecur k.kgenSt k.kconf k.kauth
    k.kfacts k.kpriority k.operation k.krules
    k.pprob k.prob k.pov

/-- Rebuild all derived fields of a preskeleton from its free-varying fields.
    Mirrors `renewPreskel :: Preskel -> Preskel`. -/
def renewPreskel (k : Preskel) : Preskel :=
  newPreskel k.gen k.shared k.insts k.orderings
    k.knon k.kpnon k.kunique k.kuniqgen
    k.kabsent k.kprecur k.kgenSt k.kconf k.kauth
    k.kfacts k.kpriority k.operation k.krules
    k.pprob k.prob k.pov

-- ── mkPreskel ────────────────────────────────────────────────────────────────

/-- Create a preskeleton from loader data.  The `prob` and `pprob` fields are
    initialised from the resulting `strandids`.
    Mirrors `mkPreskel :: Gen -> Prot -> [Goal] -> [Instance] -> [Pair] -> ...`. -/
def mkPreskel (gen : Gen) (protocol : Prot) (gs : List Goal)
    (insts : List Instance) (orderings : List Pair)
    (non pnon unique uniqgen : List Term)
    (absent : List (Term × Term)) (precur : List Node) (genSt conf auth : List Term)
    (facts : List Fact) (prio : List (Node × Int))
    (comment : List (LeanCPSA.Lib.SExpr Unit)) : Preskel :=
  let shared : Shared := { prot := protocol, goals := gs, comments := comment }
  let k := newPreskel gen shared insts orderings non pnon unique uniqgen
              absent precur genSt conf auth facts prio
              .New [] [] [] none
  { k with pprob := k.strandids, prob := k.strandids }

-- ── genNodes ─────────────────────────────────────────────────────────────────

/-- All nodes of the preskeleton as a list of `Node` pairs.
    Mirrors `genNodes :: Preskel -> [Node]`. -/
def genNodes (k : Preskel) : List Node :=
  k.strands.flatMap fun s =>
    (List.range s.nodes.length).map fun j => (s.sid, Int.ofNat j)

-- ── Gen-orig helpers ──────────────────────────────────────────────────────────

/-- True when two nodes are on the same strand (used as a sanity check).
    Mirrors `genOrigMatch :: Term -> Node -> Node -> Bool`. -/
def genOrigMatch (_ : Term) (n n' : Node) : Bool :=
  n.1 == n'.1

/-- The ugen terms paired with their generation nodes, also including key
    inverses when they exist.
    Mirrors `ugensPlusInverses :: Preskel -> [(Term, [Node])]`. -/
def ugensPlusInverses (k : Preskel) : List (Term × List Node) :=
  k.kugen.flatMap fun (u, gNodes) =>
    match invertKey u with
    | none    => [(u, gNodes)]
    | some u' => [(u, gNodes), (u', gNodes)]

/-- True when every ugen atom originates (if at all) on the same strand as it
    generates.
    Mirrors `ugenGoodOrig :: Preskel -> Bool`. -/
def ugenGoodOrig (k : Preskel) : Bool :=
  (ugensPlusInverses k).all fun (u, gNodes) =>
    let origs := (originationNodes k.strands u).2
    gNodes.all fun gNode =>
      origs.all fun oNode => genOrigMatch u gNode oNode

-- ── Stage 4: Isomorphism checking ────────────────────────────────────────────

-- ── jibeTraces ────────────────────────────────────────────────────────────────

/-- Match two traces event-by-event, threading the environment.
    Mirrors `jibeTraces :: Trace -> Trace -> (Gen, Env) -> [(Gen, Env)]`. -/
private partial def jibeTraces : Trace → Trace → GenEnv → List GenEnv
  | [],              [],              ge => [ge]
  | .In  t :: c,    .In  t' :: c',   ge =>
      (cmMatch t t' ge).flatMap (fun ge' => jibeTraces c c' ge')
  | .Out t :: c,    .Out t' :: c',   ge =>
      (cmMatch t t' ge).flatMap (fun ge' => jibeTraces c c' ge')
  | _,               _,              _  => []

-- ── permutations helpers ──────────────────────────────────────────────────────

/-- Recursive loop for `permutations`.  Extends the permutation and
    substitutions one strand at a time (in reverse order).
    Mirrors the `perms` helper inside `permutations`. -/
private partial def permsLoop (g' : Gist)
    : GenEnv → GenEnv → List (Int × Trace) → List Sid
      → List (GenEnv × GenEnv × List Sid)
  | env, renv, [],              []  => [(env, renv, [])]
  | env, renv, (h, c) :: hcs,  xs  =>
      xs.flatMap fun x =>
        match g'.gtraces.get? x.toNat with
        | none           => []
        | some (h', c') =>
          if h != h' then []
          else
            (jibeTraces c c' env).flatMap fun env' =>
            (jibeTraces c' c renv).flatMap fun renv' =>
            (permsLoop g' env' renv' hcs (xs.erase x)).map fun (env'', renv'', ys) =>
              (env'', renv'', x :: ys)
  | _,   _,     _,              _  =>
      assertError "Strand.permsLoop: lists not same length"

/-- Recursive loop for `fperms`.  Extends the fact-variable permutation and
    substitutions one variable at a time.
    Mirrors the `perms` helper inside `fperms`. -/
private partial def fpermsLoop (g' : Gist)
    : GenEnv → GenEnv → List Term → List Nat
      → List (GenEnv × GenEnv × List Nat)
  | env, renv, [],      []  => [(env, renv, [])]
  | env, renv, t :: ts, xs  =>
      xs.flatMap fun x =>
        match g'.gfvars.get? x with
        | none     => []
        | some t'  =>
            (termMatch t t' env).flatMap fun env' =>
            (termMatch t' t renv).flatMap fun renv' =>
            (fpermsLoop g' env' renv' ts (xs.erase x)).map fun (env'', renv'', ys) =>
              (env'', renv'', x :: ys)
  | _,   _,     _,      _  =>
      assertError "Strand.fpermsLoop: lists not same length"

-- ── checkOrig / checkAbs ─────────────────────────────────────────────────────

/-- Try all bijections between two term lists under a shared environment.
    Mirrors `checkOrig :: (Gen, Env) -> [Term] -> [Term] -> [(Gen, Env)]`. -/
private partial def checkOrig : GenEnv → List Term → List Term → List GenEnv
  | env, [],      []   => [env]
  | env, t :: ts, ts'  =>
      ts'.flatMap fun t' =>
        (termMatch t t' env).flatMap fun env' =>
          checkOrig env' ts (ts'.erase t')
  | _,   _,       _    => assertError "Strand.checkOrig: lists not same length"

/-- Try all bijections between two absent-pair lists under a shared environment.
    Mirrors `checkAbs :: (Gen, Env) -> [(Term,Term)] -> [(Term,Term)] -> [(Gen, Env)]`. -/
private partial def checkAbs
    : GenEnv → List (Term × Term) → List (Term × Term) → List GenEnv
  | env, [],               []   => [env]
  | env, (t1, t2) :: ts,  ts'  =>
      ts'.flatMap fun (t1', t2') =>
        (termMatch t1 t1' env).flatMap fun env' =>
        (termMatch t2 t2' env').flatMap fun env'' =>
          checkAbs env'' ts (ts'.erase (t1', t2'))
  | _,   _,                _    => assertError "Strand.checkAbs: lists not same length"

-- ── sameSkyline ───────────────────────────────────────────────────────────────

/-- Quick structural size test used before computing permutations.
    Mirrors `sameSkyline :: Gist -> Gist -> Bool`. -/
def sameSkyline (g g' : Gist) : Bool :=
  g.ntraces    == g'.ntraces    &&
  g.briefs     == g'.briefs     &&
  g.norderings == g'.norderings &&
  g.nnon       == g'.nnon       &&
  g.npnon      == g'.npnon      &&
  g.nunique    == g'.nunique    &&
  g.nuniqgen   == g'.nuniqgen   &&
  g.nabsent    == g'.nabsent    &&
  g.ngenSt     == g'.ngenSt     &&
  g.nfacts     == g'.nfacts     &&
  g.nfvars     == g'.nfvars

-- ── permutations / fperms ────────────────────────────────────────────────────

/-- All valid strand permutations of `g` into `g'`, paired with the forward and
    reverse substitutions that witness each permutation.
    Mirrors `permutations :: Gist -> Gist -> [((Gen,Env),(Gen,Env),[Sid])]`. -/
def permutations (g g' : Gist) : List (GenEnv × GenEnv × List Sid) :=
  let gg      := gmerge g.ggen g'.ggen
  let initEnv : GenEnv := (gg, emptyEnv)
  let hcs     := g.gtraces.reverse
  let xs      := ((nats g.ntraces.toNat).reverse).map Int.ofNat
  (permsLoop g' initEnv initEnv hcs xs).map fun (env, renv, ys) =>
    (env, renv, ys.reverse)

/-- All valid fact-variable permutations, paired with the forward and reverse
    substitutions that witness each permutation.
    Mirrors `fperms :: Gist -> Gist -> (Gen,Env) -> (Gen,Env) -> [...]`. -/
def fperms (g g' : Gist) (env renv : GenEnv) : List (GenEnv × GenEnv × List Nat) :=
  fpermsLoop g' env renv g.gfvars (nats g.nfvars.toNat)

-- ── Permutation utilities ─────────────────────────────────────────────────────

/-- Inverse of a strand permutation.
    Mirrors `invperm :: [Int] -> [Int]`. -/
def invperm (p : List Sid) : List Sid :=
  let indexed := (LeanCPSA.Lib.enum p).map fun (i, s) => (s, Int.ofNat i)
  (indexed.mergeSort fun a b => a.1 < b.1).map Prod.snd

/-- Apply a strand permutation to a node.
    Mirrors `permuteNode :: [Sid] -> Node -> Node`. -/
def permuteNode (perm : List Sid) (n : Node) : Node :=
  (perm.getD n.1.toNat 0, n.2)

/-- Apply a strand permutation to an ordering pair.
    Mirrors `permutePair :: [Sid] -> Pair -> Pair`. -/
def permutePair (perm : List Sid) (p : Pair) : Pair :=
  (permuteNode perm p.1, permuteNode perm p.2)

/-- True when every element of `ys`, after applying `f`, is in `xs`.
    Mirrors `containsMapped :: Eq a => (a -> a) -> [a] -> [a] -> Bool`. -/
def containsMapped {α : Type} [BEq α] (f : α → α) (xs ys : List α) : Bool :=
  ys.all fun y => xs.contains (f y)

-- ── checkFacts / tryFacts ─────────────────────────────────────────────────────

/-- Check that every fact in `g`, instantiated and strand-permuted, appears in `g'`.
    Mirrors `checkFacts :: Gist -> Gist -> (Gen,Env) -> [Sid] -> Bool`. -/
def checkFacts (g g' : Gist) (env : GenEnv) (perm : List Sid) : Bool :=
  let (_, e) := env
  let f := fun (i : Sid) => perm.getD i.toNat 0
  g.gfacts.all fun fact => g'.gfacts.contains (instUpdateFact e f fact)

/-- Check facts in both directions under a strand permutation and its inverse.
    Mirrors `tryFacts :: Gist -> Gist -> [Sid] -> [Sid] -> ... -> Bool`. -/
def tryFacts (g g' : Gist) (perm invp : List Sid)
    (t : GenEnv × GenEnv × List Nat) : Bool :=
  let (env, renv, _) := t
  checkFacts g g' env perm && checkFacts g' g renv invp

-- ── checkOrigs / checkGenSt ───────────────────────────────────────────────────

/-- Check that non/pnon/unique/uniqgen/absent lists match under `env`.
    Mirrors `checkOrigs :: Gist -> Gist -> (Gen,Env) -> Bool`. -/
def checkOrigs (g g' : Gist) (env : GenEnv) : Bool :=
  !((checkOrig env g.gnon g'.gnon).flatMap fun env' =>
    (checkOrig env' g.gpnon g'.gpnon).flatMap fun env'' =>
    (checkOrig env'' g.gunique g'.gunique).flatMap fun env''' =>
    (checkOrig env''' g.guniqgen g'.guniqgen).flatMap fun env'''' =>
    checkAbs env'''' g.gabsent g'.gabsent).isEmpty

/-- Check that every gen-st term in `g` maps into `g'` under `env`.
    Mirrors `checkGenSt :: Gist -> Gist -> (Gen,Env) -> Bool`. -/
def checkGenSt (g g' : Gist) (env : GenEnv) : Bool :=
  let (_, e) := env
  g.ggenSt.all fun gs => g'.ggenSt.contains (instantiate e gs)

-- ── tryPerm / tryPermProb ─────────────────────────────────────────────────────

/-- Check that a specific strand permutation constitutes an isomorphism.
    Mirrors `tryPerm :: Gist -> Gist -> ((Gen,Env),(Gen,Env),[Sid]) -> Bool`. -/
def tryPerm (g g' : Gist) (t : GenEnv × GenEnv × List Sid) : Bool :=
  let (env, renv, perm) := t
  checkOrigs g  g' env  &&
  checkOrigs g' g  renv &&
  checkGenSt g  g' env  &&
  checkGenSt g' g  renv &&
  (fperms g g' env renv).any (tryFacts g g' perm (invperm perm)) &&
  containsMapped (permutePair perm) g'.gorderings g.gorderings

/-- Like `tryPerm` but also checks that `prob` is mapped correctly.
    Mirrors `tryPermProb :: Gist -> Gist -> [Sid] -> [Sid] -> ... -> Bool`. -/
def tryPermProb (g g' : Gist) (prob prob' : List Sid)
    (t : GenEnv × GenEnv × List Sid) : Bool :=
  let (_, _, perm) := t
  (List.range prob.length).all (fun n =>
    match prob.get? n, prob'.get? n with
    | some ps, some ps' => perm.getD ps.toNat 0 == ps'
    | _,       _        => false) &&
  tryPerm g g' t

-- ── isomorphic / findIsomorphisms / probIsomorphic ───────────────────────────

/-- True when two preskeletons (represented as gists) are isomorphic.
    Mirrors `isomorphic :: Gist -> Gist -> Bool`. -/
def isomorphic (g g' : Gist) : Bool :=
  sameSkyline g g' && (permutations g g').any (tryPerm g g')

/-- Return all isomorphisms between two gists.
    Mirrors `findIsomorphisms :: Gist -> Gist -> [((Gen,Env),(Gen,Env),[Sid])]`. -/
def findIsomorphisms (g g' : Gist) : List (GenEnv × GenEnv × List Sid) :=
  if sameSkyline g g' then (permutations g g').filter (tryPerm g g') else []

/-- Isomorphism check that also requires the `prob` strand maps to align.
    Mirrors `probIsomorphic :: Preskel -> Preskel -> Bool`. -/
def probIsomorphic (k k' : Preskel) : Bool :=
  let g  := k.kgist
  let g' := k'.kgist
  sameSkyline g g' &&
  (permutations g g').any (tryPermProb g g' k.prob k'.prob)

-- ── Stage 5: Preskeleton Reduction System ────────────────────────────────────

-- ── PRS type ──────────────────────────────────────────────────────────────────

/-- The PRS tuple: parent preskel, candidate preskel, test-node image,
    strand map, and substitution accumulator.
    Mirrors `type PRS = (Preskel, Preskel, Node, [Sid], Subst)`. -/
abbrev PRS := Preskel × Preskel × Node × List Sid × Subst

private instance : Inhabited Subst := ⟨emptySubst⟩

/-- Extract the candidate preskeleton from a PRS.
    Mirrors `skel :: PRS -> Preskel`. -/
def skel (prs : PRS) : Preskel := prs.2.1

/-- Answer type extracted from a PRS.
    Mirrors `type Ans = (Preskel, Node, [Sid], Subst)`. -/
abbrev Ans := Preskel × Node × List Sid × Subst

/-- Extract the `Ans` from a PRS.  Mirrors `ans :: PRS -> Ans`. -/
def ans (prs : PRS) : Ans :=
  let (_, k, n, phi, subst) := prs; (k, n, phi, subst)

-- ── foldMapM ──────────────────────────────────────────────────────────────────

/-- Thread an accumulator through a list, right-to-left, collecting results.
    Mirrors `foldMapM :: Monad m => (a -> b -> m (a, c)) -> a -> [b] -> m (a, [c])`. -/
private def foldMapM {α β γ : Type}
    (f : α → β → List (α × γ)) (acc : α) : List β → List (α × List γ)
  | [] => [(acc, [])]
  | x :: xs =>
      (foldMapM f acc xs).flatMap fun (acc', ys) =>
      (f acc' x).map fun (acc'', y) => (acc'', y :: ys)

-- ── soothePreskel ─────────────────────────────────────────────────────────────

/-- Remove origination assumptions that no longer hold after a substitution.
    Mirrors `soothePreskel :: Preskel -> Preskel`. -/
def soothePreskel (k : Preskel) : Preskel :=
  let vs    := kvars k
  let terms := kterms k
  let chans := kchans k
  -- Use newPreskelBasic: soothePreskel is only called immediately before
  -- wellFormedPreskel, which adds the expensive fields on success.
  newPreskelBasic k.gen k.shared k.insts k.orderings
    (k.knon.filter    fun t => varSubset [t] terms)
    (k.kpnon.filter   fun t => varSubset [t] terms)
    (k.kunique.filter fun t => terms.any (carriedBy t))
    (k.kuniqgen.filter fun t => varSubset [t] terms)
    (k.kabsent.filter  fun (x, y) => varSubset [x, y] vs)
    k.kprecur
    (k.kgenSt.filter   fun t => foldVars (fun b v => b && vs.contains v) true t)
    (k.kconf.filter    fun t => varSubset [t] chans)
    (k.kauth.filter    fun t => varSubset [t] chans)
    k.kfacts k.kpriority k.operation k.krules k.pprob k.prob k.pov

-- ── substInst / substOper / substCause / ksubst ───────────────────────────────

/-- Apply a substitution to an instance by rebuilding it.
    Mirrors `substInst :: Subst -> Gen -> Instance -> [(Gen, Instance)]`. -/
private def substInst (subst : Subst) (gen : Gen) (i : Instance)
    : List (Gen × Instance) :=
  bldInstance i.role (i.trace.map (evtMap (substitute subst))) gen

/-- Apply a substitution to a Cause.
    Mirrors `substCause :: Subst -> Cause -> Cause`. -/
private def substCause (subst : Subst) (c : Cause) : Cause :=
  { c with
    cmt  := cmtSubstitute subst c.cmt,
    cmts := LeanCPSA.Lib.RBSet.map (cmtSubstitute subst) c.cmts }

/-- Apply a substitution to an Operation.
    Mirrors `substOper :: Subst -> Operation -> Operation`. -/
private def substOper (subst : Subst) : Operation → Operation
  | .New                         => .New
  | .Contracted sm s cause       => .Contracted sm (compose subst s) (substCause subst cause)
  | .Displaced sm n1 n2 r h c   => .Displaced sm n1 n2 r h c
  | .AddedStrand sm r h cause    => .AddedStrand sm r h (substCause subst cause)
  | .AddedListener sm t cause    => .AddedListener sm (substitute subst t) (substCause subst cause)
  | .AddedAbsence sm t1 t2 cause => .AddedAbsence sm (substitute subst t1)
                                                      (substitute subst t2)
                                                      (substCause subst cause)
  | .Generalized sm m            => .Generalized sm m
  | .Collapsed sm n1 n2          => .Collapsed sm n1 n2
  | .AppliedRules sm             => .AppliedRules sm

/-- Apply a `(Gen, Subst)` to every instance, then rebuild the preskel.
    Mirrors `ksubst :: PRS -> (Gen, Subst) -> [PRS]`. -/
def ksubst (prs : PRS) (gs : Gen × Subst) : List PRS :=
  let (k0, k, n, phi, hsubst) := prs
  let (gen, subst) := gs
  (foldMapM (substInst subst) gen k.insts).flatMap fun (gen', insts') =>
    let non'    := k.knon.map    (substitute subst)
    let pnon'   := k.kpnon.map   (substitute subst)
    let unique' := k.kunique.map (substitute subst)
    let uniqgen' := k.kuniqgen.map (substitute subst)
    let absent' := k.kabsent.map fun (x, y) => (substitute subst x, substitute subst y)
    let genSt'  := k.kgenSt.map (substitute subst)
    let conf'   := k.kconf.map   (substitute subst)
    let auth'   := k.kauth.map   (substitute subst)
    let facts'  := k.kfacts.map  (substFact subst)
    let oper'   := substOper subst k.operation
    -- Use newPreskelBasic: result goes to soothePreskel → wellFormedPreskel,
    -- which adds expensive fields only for preskels that survive.
    let k'      := newPreskelBasic gen' k.shared insts' k.orderings
                    non' pnon' unique' uniqgen' absent' k.kprecur genSt' conf' auth'
                    facts' k.kpriority oper' k.krules k.pprob k.prob k.pov
    (wellFormedPreskel (soothePreskel k')).map fun k'' =>
      (k0, k'', n, phi, compose subst hsubst)

-- ── Permutation helpers ───────────────────────────────────────────────────────

/-- Map `old` → `new`, decrement ids above `old`.
    Mirrors `updateStrand :: Int -> Int -> Sid -> Sid`. -/
def updateStrand (old new i : Sid) : Sid :=
  let j := if old == i then new else i
  if j > old then j - 1 else j

/-- Apply `updateStrand` to the strand component of a node.
    Mirrors `updateNode :: Int -> Int -> Node -> Node`. -/
def updateNode (old new : Sid) (nd : Node) : Node :=
  (updateStrand old new nd.1, nd.2)

/-- Build the permutation that eliminates strand `old`, merging it into `new`.
    Mirrors `updatePerm :: Int -> Int -> [Sid] -> [Sid]`. -/
def updatePerm (old new : Sid) (perm : List Sid) : List Sid :=
  perm.map (updateStrand old new)

/-- Apply a strand permutation to a list of ordering pairs.
    Mirrors `permuteOrderings :: [Sid] -> [Pair] -> [Pair]`. -/
def permuteOrderings (perm : List Sid) (orderings : List Pair) : List Pair :=
  orderings.map (permutePair perm)

/-- Remap `prob` through a permutation.
    Mirrors `updateProb :: [Sid] -> [Sid] -> [Sid]`. -/
def updateProb (mapping prob : List Sid) : List Sid :=
  prob.map fun s => mapping.getD s.toNat 0

/-- Remap the node-priority list through a permutation.
    Mirrors `updatePriority :: [Sid] -> [(Node,Int)] -> [(Node,Int)]`. -/
def updatePriority (mapping : List Sid) (prio : List (Node × Int)) : List (Node × Int) :=
  prio.map fun (nd, i) => (permuteNode mapping nd, i)

/-- Remove intrastrand orderings; fail (return []) on reverse intrastrand ordering
    when `validate` is true.
    Mirrors `normalizeOrderings :: Bool -> [Pair] -> [[Pair]]`. -/
def normalizeOrderings (validate : Bool) (orderings : List Pair) : List (List Pair) :=
  if validate then
    let rec loop (acc : List Pair) : List Pair → List (List Pair)
      | [] => [acc]
      | p@((s0, i0), (s1, i1)) :: ps =>
          if s0 != s1 then loop (p :: acc) ps
          else if i0 < i1 then loop acc ps
          else []
    loop [] orderings
  else
    [orderings.filter fun ((s0, _), (s1, _)) => s0 != s1]

-- ── deleteStrandFacts / forward ────────────────────────────────────────────────

/-- Remove facts that reference strand `s`.
    Mirrors `deleteStrandFacts :: Sid -> [Fact] -> [Fact]`. -/
def deleteStrandFacts (s : Sid) (facts : List Fact) : List Fact :=
  facts.filter fun fact =>
    fact.terms.all fun ft =>
      match ft with
      | .FSid s' => s != s'
      | .ofTerm _ => true

/-- Redirect edges from strand `s` through its predecessors; drop incoming edges.
    Mirrors `forward :: Sid -> [Pair] -> [Pair]`. -/
def forward (s : Sid) (orderings : List Pair) : List Pair :=
  orderings.flatMap fun p@((s0, i0), (s1, i1)) =>
    if s0 == s then
      orderings.filterMap fun ((s2, i2), (s3, i3)) =>
        if s3 == s0 && i0 >= i3 then some ((s2, i2), (s1, i1)) else none
    else if s1 == s then []
    else [p]

-- ── compress / purge ─────────────────────────────────────────────────────────

/-- Eliminate strand `s` by merging it into `s'`.
    Mirrors `compress :: Bool -> PRS -> Sid -> Sid -> [PRS]`. -/
def compress (validate : Bool) (prs : PRS) (s s' : Sid) : List PRS :=
  let (k0, k, n, phi, hsubst) := prs
  let perm := updatePerm s s' k.strandids
  (normalizeOrderings validate (permuteOrderings perm k.orderings)).flatMap fun orderings' =>
    -- Use newPreskelBasic: result goes directly to wellFormedPreskel.
    let k' := newPreskelBasic k.gen k.shared (LeanCPSA.Lib.deleteNth s.toNat k.insts)
                orderings' k.knon k.kpnon k.kunique k.kuniqgen k.kabsent
                (k.kprecur.map (permuteNode perm)) k.kgenSt k.kconf k.kauth
                (k.kfacts.map (updateFact (updateStrand s s')))
                (updatePriority perm k.kpriority)
                k.operation k.krules k.pprob (updateProb perm k.prob) k.pov
    (wellFormedPreskel k').map fun k'' =>
      (k0, k'', permuteNode perm n, phi.map fun sid => perm.getD sid.toNat 0, hsubst)

/-- Purge strand `s`, forwarding its orderings to `s'`.  Used by thinning.
    Mirrors `purge :: PRS -> Sid -> Sid -> [PRS]`. -/
def purge (prs : PRS) (s s' : Sid) : List PRS :=
  let (k0, k, n, phi, hsubst) := prs
  let perm := updatePerm s s' k.strandids
  (normalizeOrderings false (permuteOrderings perm (forward s k.orderings))).flatMap
    fun orderings' =>
    -- Use newPreskelBasic: result goes to soothePreskel → wellFormedPreskel.
    let k' := newPreskelBasic k.gen k.shared (LeanCPSA.Lib.deleteNth s.toNat k.insts)
                orderings' k.knon k.kpnon k.kunique k.kuniqgen k.kabsent
                (k.kprecur.map (permuteNode perm)) k.kgenSt k.kconf k.kauth
                ((deleteStrandFacts s k.kfacts).map (updateFact (updateStrand s s')))
                (updatePriority perm k.kpriority)
                k.operation k.krules k.pprob (updateProb perm k.prob) k.pov
    (wellFormedPreskel (soothePreskel k')).map fun k'' =>
      (k0, k'', permuteNode perm n, phi.map fun sid => perm.getD sid.toNat 0, hsubst)

-- ── matchTraces ───────────────────────────────────────────────────────────────

/-- Match a trace pattern against a target trace (pattern may be shorter).
    Mirrors `matchTraces :: Trace -> Trace -> (Gen,Env) -> [(Gen,Env)]`. -/
partial def matchTraces : Trace → Trace → GenEnv → List GenEnv
  | [],           _,             ge => [ge]
  | .In  t :: c, .In  t' :: c', ge =>
      (cmMatch t t' ge).flatMap fun ge' => matchTraces c c' ge'
  | .Out t :: c, .Out t' :: c', ge =>
      (cmMatch t t' ge).flatMap fun ge' => matchTraces c c' ge'
  | _,           _,             _  => []

-- ── origGenChecks / origUgenDiffStrand ───────────────────────────────────────

/-- True when a term in orig or ugen originates/generates on multiple strands,
    or when a ugen term originates on a different strand than it generates.
    Mirrors `origGenChecks :: PRS -> Bool`. -/
def origGenChecks (prs : PRS) : Bool :=
  let k := skel prs
  k.korig.any (fun (_, l) => l.length > 1) ||
  k.kugen.any (fun (_, l) => l.length > 1) ||
  origUgenDiffStrand k.korig (ugensPlusInverses k) ||
  !ugenGoodOrig k
  where
    origUgenDiffStrand (orig : List (Term × List Node))
        : List (Term × List Node) → Bool
      | [] => false
      | (t, ns) :: ugen =>
          (match orig.lookup t with
          | none      => false
          | some ns'  => ns.any fun (s, _) => ns'.any fun (s', _) => s != s') ||
          (match invertKey t with
          | none    => false
          | some t' => match orig.lookup t' with
            | none     => false
            | some ns' => ns.any fun (s, _) => ns'.any fun (s', _) => s != s') ||
          origUgenDiffStrand orig ugen

-- ── origNode / genNode / addUniqOrigOrderings / addUniqGenOrderings ──────────

/-- Get the single origination node for a uniquely-originating term.
    Mirrors `origNode :: Preskel -> Term -> Maybe Node`. -/
def origNode (k : Preskel) (t : Term) : Option Node :=
  match k.korig.lookup t with
  | none    => assertError "Strand.origNode: term not in kunique"
  | some [] => none
  | some [n] => some n
  | some _   => assertError "Strand.origNode: not a hulled skeleton"

/-- Get the single generation node for a uniquely-generating term.
    Mirrors `genNode :: Preskel -> Term -> Maybe Node`. -/
def genNode (k : Preskel) (t : Term) : Option Node :=
  match k.kugen.lookup t with
  | none    => assertError "Strand.genNode: term not in kuniqgen"
  | some [] => none
  | some [n] => some n
  | some _   => assertError "Strand.genNode: not a hulled skeleton"

/-- Add ordering constraints so that the origination node of `t` precedes
    every strand that gains `t`.
    Mirrors `addUniqOrigOrderings :: Preskel -> [Pair] -> Term -> [Pair]`. -/
def addUniqOrigOrderings (k : Preskel) (orderings : List Pair) (t : Term) : List Pair :=
  match origNode k t with
  | none         => orderings
  | some n@(s, _) =>
      k.strandids.erase s |>.foldl fun ords s' =>
        match gainedPos t (strandInst k s').trace with
        | none     => ords
        | some pos => adjoin (n, (s', pos)) ords
      orderings

/-- Add ordering constraints so that the generation node of `t` precedes
    every strand that uses `t`.
    Mirrors `addUniqGenOrderings :: Preskel -> [Pair] -> Term -> [Pair]`. -/
def addUniqGenOrderings (k : Preskel) (orderings : List Pair) (t : Term) : List Pair :=
  match genNode k t with
  | none          => orderings
  | some n@(s, _) =>
      k.strandids.erase s |>.foldl fun ords s' =>
        match usedPos t (strandInst k s').trace with
        | none     => ords
        | some pos => adjoin (n, (s', pos)) ords
      orderings

-- ── origCheck / precedesCheck / dropInbnd / setSkel ──────────────────────────

/-- True when the substitution maps each unique/non term back into the same set.
    Mirrors `origCheck :: Preskel -> Env -> Bool`. -/
def origCheck (k : Preskel) (env : Env) : Bool :=
  let check (orig : List Term) :=
    orig.all fun item => orig.contains (instantiate env item)
  check k.kunique && check k.kuniqgen && check k.knon && check k.kpnon

/-- True when edge `e` satisfies the precedes condition for strand elimination.
    Mirrors `precedesCheck :: Preskel -> Sid -> Sid -> Edge -> Bool`. -/
def precedesCheck (k : Preskel) (s s' : Sid) (e : GraphEdge) : Bool :=
  let (gn0, gn1) := e
  let getNode (nd : Node) := k.strands.get? nd.1.toNat >>= fun st => st.nodes.get? nd.2.toNat
  if s == gn0.strandId then
    graphPrecedes getNode (vertex k (s', gn0.pos)) gn1
  else if s == gn1.strandId then
    graphPrecedes getNode gn0 (vertex k (s', gn1.pos))
  else true

/-- Drop all inbound edges to strand `s` (strong pruning helper).
    Mirrors `dropInbnd :: Preskel -> Sid -> Preskel`. -/
def dropInbnd (k : Preskel) (s : Sid) : Preskel :=
  newPreskel k.gen k.shared k.insts (forward s k.orderings)
    k.knon k.kpnon k.kunique k.kuniqgen k.kabsent k.kprecur
    k.kgenSt k.kconf k.kauth k.kfacts k.kpriority
    k.operation k.krules k.pprob k.prob k.pov

/-- Replace the candidate preskel in a PRS.
    Mirrors `setSkel :: PRS -> Preskel -> PRS`. -/
def setSkel (prs : PRS) (k : Preskel) : PRS :=
  let (k0, _, n, phi, hsubst) := prs; (k0, k, n, phi, hsubst)

-- ── Thinning helpers (non-recursive) ─────────────────────────────────────────

/-- True when a list has at least two elements. -/
private def atLeastTwo {α : Type} : List α → Bool
  | _ :: _ :: _ => true
  | _            => false

/-- Update a `(Sid, Sid)` pair under strand elimination.
    Mirrors `updatePairs :: Sid -> Sid -> (Sid,Sid) -> (Sid,Sid)`. -/
private def updatePairs (old new : Sid) (p : Sid × Sid) : Sid × Sid :=
  (updateStrand old new p.1, updateStrand old new p.2)

/-- Swap each pair in a list.
    Mirrors `swap :: [(a,a)] -> [(a,a)]`. -/
private def swapPairs (ps : List (Sid × Sid)) : List (Sid × Sid) :=
  ps.map fun (x, y) => (y, x)

/-- All length-≥2 subsets of matching pairs (for multistrand thinning).
    Mirrors `multiPairs :: [(Sid,Sid)] -> [[(Sid,Sid)]]`. -/
private partial def thinOne : List (Sid × Sid) → List (List (Sid × Sid))
  | []       => []
  | p :: ps  => thinTwo p ps ++ thinOne ps
  where
    thinTwo (p : Sid × Sid) (ps : List (Sid × Sid)) : List (List (Sid × Sid)) :=
      [p] :: ((thinOne (ps.filter fun q =>
                p.1 != q.1 && p.1 != q.2 && p.2 != q.1 && p.2 != q.2)).map (p :: ·))

private def multiPairs (ps : List (Sid × Sid)) : List (List (Sid × Sid)) :=
  if useSingleStrandThinning then []
  else (thinOne ps).filter atLeastTwo

/-- True when two strands have the same-height, mutually-matchable traces.
    Mirrors `thinStrandMatch :: Preskel -> Sid -> Sid -> Bool`. -/
def thinStrandMatch (k : Preskel) (s s' : Sid) : Bool :=
  let i  := strandInst k s
  let i' := strandInst k s'
  let ge : GenEnv := (k.gen, emptyEnv)
  i.height == i'.height &&
  !(matchTraces i.trace i'.trace ge).isEmpty &&
  !(matchTraces i'.trace i.trace ge).isEmpty

/-- Try to thin strand `s` using `s'`.  Returns `none` on no match,
    `some []` on match-with-no-result, or `some prss` on success.
    Mirrors `thinStrand :: PRS -> Sid -> Sid -> Maybe [PRS]`. -/
def thinStrand (prs : PRS) (s s' : Sid) : Option (List PRS) :=
  if !thinStrandMatch (skel prs) s s' then none
  else some
    ((purge prs s s').flatMap fun prs' =>
      (purge prs s' s).flatMap fun prs'' =>
        if probIsomorphic (skel prs') (skel prs'') then [prs'] else [])

-- ── reduce ────────────────────────────────────────────────────────────────────

/-- Transitively reduce the ordering relation.
    Mirrors `reduce :: PRS -> [PRS]`. -/
partial def reduce (prs : PRS) : List PRS :=
  let (k0, k, n, phi, hsubst) := prs
  let getNode (nd : Node) :=
    k.strands.get? nd.1.toNat >>= fun s => s.nodes.get? nd.2.toNat
  let o := (graphReduce getNode k.edges).map graphPair
  if o.length == k.orderings.length then [prs]
  else
    -- Use newPreskelBasic: result goes directly to wellFormedPreskel.
    let k' := newPreskelBasic k.gen k.shared k.insts o k.knon k.kpnon k.kunique k.kuniqgen
                k.kabsent k.kprecur k.kgenSt k.kconf k.kauth k.kfacts k.kpriority
                k.operation k.krules k.pprob k.prob k.pov
    (wellFormedPreskel k').map fun k'' => (k0, k'', n, phi, hsubst)

-- ── enforceAbsence ────────────────────────────────────────────────────────────

/-- Compute substitutions that satisfy the absence assumptions, apply them.
    Mirrors `enforceAbsence :: PRS -> [PRS]`. -/
partial def enforceAbsence (prs : PRS) : List PRS :=
  let k := skel prs
  if k.kabsent.isEmpty then [prs]
  else
    let envs := k.kabsent.foldl
      (fun es ts => es.flatMap fun e => absentEnv e ts)
      [(k.gen, emptyEnv)]
    envs.flatMap fun e => ksubst prs (e.1, substitution e.2)

-- ── unifyStrands / unifyTraces ────────────────────────────────────────────────

/-- Unify two traces allowing the first to be a prefix.
    Mirrors `unifyTraces :: Trace -> Trace -> (Gen,Subst) -> [(Gen,Subst)]`. -/
private def unifyTraces : Trace → Trace → (Gen × Subst) → List (Gen × Subst)
  | [],           _,             gs => [gs]
  | .In  t :: c, .In  t' :: c', gs =>
      (cmUnify t t' gs).flatMap fun gs' => unifyTraces c c' gs'
  | .Out t :: c, .Out t' :: c', gs =>
      (cmUnify t t' gs).flatMap fun gs' => unifyTraces c c' gs'
  | _,           _,             _  => []

/-- Try to unify two strand traces (shorter first).
    Mirrors `unifyStrands :: Preskel -> Sid -> Sid -> [(Sid,Sid,(Gen,Subst))]`. -/
private partial def unifyStrands (k : Preskel) (s s' : Sid)
    : List (Sid × Sid × (Gen × Subst)) :=
  let i  := strandInst k s
  let i' := strandInst k s'
  if i.height > i'.height then unifyStrands k s' s
  else
    (unifyTraces i.trace i'.trace (k.gen, emptySubst)).map fun gs =>
      (s, s', gs)

-- ── Mutually recursive PRS core ───────────────────────────────────────────────

mutual

/-- Hull: enforce unique origination.
    Mirrors `hull :: Bool -> PRS -> [PRS]`. -/
partial def hull (thin : Bool) (prs : PRS) : List PRS :=
  let k := skel prs
  hullLoop thin prs (k.korig ++ k.kugen)

private partial def hullLoop (thin : Bool) (prs : PRS)
    : List (Term × List Node) → List PRS
  | [] => enrich thin prs
  | (_, (s, _) :: (s', _) :: _) :: _ =>
      (unifyStrands (skel prs) s s').flatMap fun (s'', s''', subst) =>
      (ksubst prs subst).flatMap fun prs =>
      (compress false prs s'' s''').flatMap fun prs' =>
        hull thin prs'
  | _ :: rest => hullLoop thin prs rest

/-- Order enrichment: add orderings from unique orig/gen assumptions.
    Mirrors `enrich :: Bool -> PRS -> [PRS]`. -/
partial def enrich (thin : Bool) (prs : PRS) : List PRS :=
  if origGenChecks prs then []
  else
    let (k0, k, n, phi, hsubst) := prs
    let o  := k.kunique.foldl (addUniqOrigOrderings k) k.orderings
    let o' := k.kuniqgen.foldl (addUniqGenOrderings k) o
    if o'.length == k.orderings.length then
      maybeThin thin prs
    else
      -- Use newPreskelBasic: result goes directly to wellFormedPreskel.
      let k' := newPreskelBasic k.gen k.shared k.insts o' k.knon k.kpnon k.kunique k.kuniqgen
                  k.kabsent k.kprecur k.kgenSt k.kconf k.kauth k.kfacts k.kpriority
                  k.operation k.krules k.pprob k.prob k.pov
      (wellFormedPreskel k').flatMap fun k'' =>
        maybeThin thin (k0, k'', n, phi, hsubst)

/-- Dispatch to prune, thin, or reduce based on compile-time flags.
    Mirrors `maybeThin :: Bool -> PRS -> [PRS]`. -/
partial def maybeThin (thin' : Bool) (prs : PRS) : List PRS :=
  if usePruning then prune prs
  else if thin' then thin prs
  else reduce prs

/-- Thinning: try to eliminate redundant strands.
    Mirrors `thin :: PRS -> [PRS]`. -/
partial def thin (prs : PRS) : List PRS :=
  (reduce prs).flatMap fun prs =>
    let k := skel prs
    let ss := k.strandids.filter fun s => !k.prob.contains s
    thinStrands prs [] ss.reverse

/-- Drive thinning over all strands.
    Mirrors `thinStrands :: PRS -> [(Sid,Sid)] -> [Sid] -> [PRS]`. -/
partial def thinStrands (prs : PRS) (ps : List (Sid × Sid)) : List Sid → List PRS
  | [] =>
      match multiPairs ps with
      | []  => reduce prs
      | mps => thinMany prs mps
  | s :: ss => thinStrandPairs prs ps s ss ss

/-- Try all partner strands for a given strand.
    Mirrors `thinStrandPairs :: PRS -> [(Sid,Sid)] -> Sid -> [Sid] -> [Sid] -> [PRS]`. -/
partial def thinStrandPairs
    (prs : PRS) (ps : List (Sid × Sid)) (s : Sid) (ss : List Sid) : List Sid → List PRS
  | []        => thinStrands prs ps ss
  | s' :: ss' =>
      match thinStrand prs s s' with
      | none    => thinStrandPairs prs ps s ss ss'
      | some [] => thinStrandPairs prs ((s, s') :: ps) s ss ss'
      | some prss =>
          prss.flatMap fun prs => thin prs

/-- Try multiple multistrand pairings until one succeeds.
    Mirrors `thinMany :: PRS -> [[(Sid,Sid)]] -> [PRS]`. -/
partial def thinMany (prs : PRS) : List (List (Sid × Sid)) → List PRS
  | []        => reduce prs
  | ps :: mps =>
      match thinManyStrands prs ps with
      | []   => thinMany prs mps
      | prss => prss.flatMap fun prs => thin prs

/-- Check a multistrand pairing in both directions.
    Mirrors `thinManyStrands :: PRS -> [(Sid,Sid)] -> [PRS]`. -/
partial def thinManyStrands (prs : PRS) (ps : List (Sid × Sid)) : List PRS :=
  (compressMany prs ps).flatMap fun prs' =>
  (compressMany prs (swapPairs ps)).flatMap fun prs'' =>
    if probIsomorphic (skel prs') (skel prs'') then [prs'] else []

/-- Compress all pairs in a list sequentially.
    Mirrors `compressMany :: PRS -> [(Sid,Sid)] -> [PRS]`. -/
partial def compressMany (prs : PRS) : List (Sid × Sid) → List PRS
  | []              => [prs]
  | (s, s') :: ps   =>
      (purge prs s s').flatMap fun prs' =>
        compressMany prs' (ps.map (updatePairs s s'))

/-- Prune redundant strands.
    Mirrors `prune :: PRS -> [PRS]`. -/
partial def prune (prs : PRS) : List PRS :=
  let ss := (skel prs).strandids
  pruneStrands prs ss.reverse ss

/-- Drive pruning over all pairs of strands.
    Mirrors `pruneStrands :: PRS -> [Sid] -> [Sid] -> [PRS]`. -/
partial def pruneStrands (prs : PRS) : List Sid → List Sid → List PRS
  | [],       _          => reduce prs
  | _ :: ss', []         => pruneStrands prs ss' (skel prs).strandids
  | s :: ss', s' :: ss'' =>
      if s == s' then pruneStrands prs (s :: ss') ss''
      else
        match pruneStrand prs s s' with
        | []   => pruneStrands prs (s :: ss') ss''
        | prss => prss.flatMap fun prs => prune prs

/-- Try to prune strand `s` using `s'`.
    Mirrors `pruneStrand :: PRS -> Sid -> Sid -> [PRS]`. -/
partial def pruneStrand (prs : PRS) (s s' : Sid) : List PRS :=
  let k := skel prs
  if k.prob.contains s then []
  else
    (matchTraces (strandInst k s).trace (strandInst k s').trace (k.gen, emptyEnv)).flatMap
      fun (g, env) =>
      let ts    := (LeanCPSA.Lib.deleteNth s.toNat k.insts).flatMap (fun i => tterms i.trace)
      let subst := substitution env
      if !disjointDom subst ts then []
      else if !origCheck k env then []
      else
        let k'   := if useStrongPruning then dropInbnd k s else k
        let prs' := if useStrongPruning then setSkel prs k' else prs
        if !k'.edges.all (precedesCheck k' s s') then []
        else
          (ksubst prs' (g, subst)).flatMap fun prs' =>
            compress true prs' s s'

end  -- mutual

-- ── skeletonize ───────────────────────────────────────────────────────────────

/-- The main PRS entry point: enforce absence, check origination, enrich.
    Mirrors `skeletonize :: Bool -> PRS -> [PRS]`. -/
partial def skeletonize (thin : Bool) (prs : PRS) : List PRS :=
  (enforceAbsence prs).flatMap fun prs' =>
    if origGenChecks prs' then []
    else enrich thin prs'

-- ── Homomorphism filter ───────────────────────────────────────────────────────

/-- True when `phi`/`subst` witnesses a valid homomorphism.
    Mirrors `validateMappingSubst :: Preskel -> [Sid] -> Subst -> Preskel -> Bool`. -/
def validateMappingSubst (k : Preskel) (phi : List Sid) (subst : Subst)
    (k' : Preskel) : Bool :=
  useNoOrigPreservation ||
  (k.korig.all fun (u, ns) =>
    match k'.korig.lookup (substitute subst u) with
    | none     => false
    | some ns' => (ns.map (permuteNode phi)).all (ns'.contains)) &&
  (k.kugen.all fun (u, ns) =>
    match k'.kugen.lookup (substitute subst u) with
    | none     => false
    | some ns' => (ns.map (permuteNode phi)).all (ns'.contains))

/-- Filter a PRS to only those that define a valid homomorphism.
    This is the universal EXIT GATE of both the hull pipeline (`toSkeleton`) and
    the cohort primitives (`augment`/`contract`/`addListener`/`addAbsence`), and
    is never called on hull intermediates.  We attach the expensive TC fields
    (`addExpensiveFields`) here so every surviving output has TC for its
    downstream consumers (`povCheck`, `mgs`, `specialization`, rule predicates)
    while intermediates — which only pass through `wellFormedPreskel` — stay
    TC-free.  `addExpensiveFields` is idempotent, so this never double-computes.
    Mirrors `homomorphismFilter :: PRS -> [Ans]`. -/
def homomorphismFilter (prs : PRS) : List Ans :=
  let (k0, k, n, phi, subst) := prs
  if validateMappingSubst k0 phi subst k then [(addExpensiveFields k, n, phi, subst)] else []

-- ── toSkeleton ────────────────────────────────────────────────────────────────

/-- Convert a preskeleton to a list of skeletons.
    TC fields are attached by the exit gate `homomorphismFilter`, so each
    surviving skeleton already carries TC for downstream callers (e.g.
    `specialization`).  The hull intermediates deliberately stay TC-free.
    Mirrors `toSkeleton :: Bool -> Preskel -> [Preskel]`. -/
def toSkeleton (thin : Bool) (k : Preskel) : List Preskel :=
  (hull thin (k, k, (0, 0), k.strandids, emptySubst)).flatMap fun prs =>
    (homomorphismFilter prs).map fun (k', _, _, _) => k'

-- ── firstSkeleton ─────────────────────────────────────────────────────────────

/-- Convert the loader preskeleton to the first skeleton used in search.
    Mirrors `firstSkeleton :: Preskel -> [Preskel]`. -/
def firstSkeleton (k : Preskel) : List Preskel :=
  (wellFormedPreskel k).flatMap fun k =>
    (toSkeleton false k).map fun k' =>
      { k' with pprob := k'.prob, pov := some k }

-- ── Inheritance ───────────────────────────────────────────────────────────────

private def inherit (i : Instance) (rorigs : List (Term × Int)) : List Term :=
  rorigs.filterMap fun (t, pos) =>
    if pos < i.height then some (instantiate i.env t) else none

/-- Inherit non-originating atoms from an instance.
    Mirrors `inheritRnon :: Instance -> [Term]`. -/
def inheritRnon (i : Instance) : List Term := inherit i i.role.rnorig

/-- Inherit penetrator-non-originating atoms from an instance.
    Mirrors `inheritRpnon :: Instance -> [Term]`. -/
def inheritRpnon (i : Instance) : List Term := inherit i i.role.rpnorig

/-- Inherit uniquely-originating atoms from an instance.
    Mirrors `inheritRunique :: Instance -> [Term]`. -/
def inheritRunique (i : Instance) : List Term := inherit i i.role.ruorig

/-- Inherit uniquely-generating atoms from an instance.
    Mirrors `inheritRuniqgen :: Instance -> [Term]`. -/
def inheritRuniqgen (i : Instance) : List Term := inherit i i.role.rugen

/-- Inherit confidential channels from an instance.
    Mirrors `inheritRconf :: Instance -> [Term]`. -/
def inheritRconf (i : Instance) : List Term := inherit i i.role.rpconf

/-- Inherit authenticated channels from an instance.
    Mirrors `inheritRauth :: Instance -> [Term]`. -/
def inheritRauth (i : Instance) : List Term := inherit i i.role.rpauth

/-- Inherit absent constraints from an instance.
    Mirrors `inheritRabsent :: Instance -> [(Term,Term)]`. -/
def inheritRabsent (i : Instance) : List (Term × Term) :=
  i.role.rabs.filterMap fun (x, y, pos) =>
    if pos < i.height then some (instantiate i.env x, instantiate i.env y) else none

-- ── Augmentation ─────────────────────────────────────────────────────────────

/-- Add an instance and one ordering to the preskeleton.
    Mirrors `aug :: PRS -> Instance -> [PRS]`. -/
def aug (prs : PRS) (inst : Instance) : List PRS :=
  let (k0, k, n, phi, hsubst) := prs
  let insts'    := k.insts ++ [inst]
  let pair      : Pair := ((Int.ofNat k.insts.length, inst.height - 1), n)
  let orderings' := pair :: k.orderings
  -- Use newPreskelBasic: result goes directly to wellFormedPreskel.
  let k' := newPreskelBasic k.gen k.shared insts' orderings'
              (inheritRnon inst ++ k.knon)
              (inheritRpnon inst ++ k.kpnon)
              (inheritRunique inst ++ k.kunique)
              (inheritRuniqgen inst ++ k.kuniqgen)
              (inheritRabsent inst ++ k.kabsent)
              k.kprecur k.kgenSt
              (inheritRconf inst ++ k.kconf)
              (inheritRauth inst ++ k.kauth)
              k.kfacts k.kpriority k.operation k.krules k.pprob k.prob k.pov
  (wellFormedPreskel k').map fun k'' => (k0, k'', n, phi, hsubst)

/-- Apply a substitution and then augment.
    Mirrors `substAndAugment :: Preskel -> Node -> Cause -> Role -> (Gen,Subst) -> Instance -> [PRS]`. -/
partial def substAndAugment (k : Preskel) (n : Node) (cause : Cause) (role : Role)
    (subst : Gen × Subst) (inst : Instance) : List PRS :=
  let oper := .AddedStrand [] role.rname inst.height cause
  let prs  : PRS := (k, { k with operation := oper, krules := [] }, n, k.strandids, emptySubst)
  (ksubst prs subst).flatMap fun prs => aug prs inst

/-- Convert an AddedStrand operation to Displaced.
    Mirrors `addedToDisplaced :: Operation -> Int -> Int -> Operation`. -/
def addedToDisplaced : Operation → Int → Int → Operation
  | .AddedStrand [] role h cause, s, s' => .Displaced [] s s' role h cause
  | _,                            _,  _  => assertError "Strand.addedToDisplaced: Bad operation"

/-- Try to displace new strand `s` with existing strand `s'`.
    Mirrors `augDisplaceStrands :: PRS -> Sid -> Sid -> [PRS]`. -/
partial def augDisplaceStrands (prs : PRS) (s s' : Sid) : List PRS :=
  let (k0, k, n, phi, hsubst) := prs
  (unifyStrands k s s').flatMap fun (su, su', subst) =>
    let op := addedToDisplaced k.operation su su'
    (ksubst (k0, { k with operation := op, krules := [] }, n, phi, hsubst) subst).flatMap
      fun prs =>
      (compress true prs su su').flatMap fun prs =>
        skeletonize useThinningWhileSolving prs

/-- Try all displacements of the newly-added strand.
    Mirrors `augDisplace :: PRS -> [PRS]`. -/
partial def augDisplace (prs : PRS) : List PRS :=
  let s : Sid := Int.ofNat (skel prs).strandids.length - 1
  ((nats s.toNat).map Int.ofNat).flatMap fun s' =>
    augDisplaceStrands prs s s'

/-- Apply substitution, augment, and try all displacements.
    Mirrors `augmentAndDisplace :: Preskel -> Node -> Cause -> Role -> (Gen,Subst) -> Instance -> [PRS]`. -/
partial def augmentAndDisplace (k : Preskel) (n : Node) (cause : Cause) (role : Role)
    (subst : Gen × Subst) (inst : Instance) : List PRS :=
  (substAndAugment k n cause role subst inst).flatMap fun prs =>
    augDisplace prs ++ skeletonize useThinningWhileSolving prs

/-- Regular augmentation: add a strand and return answers.
    Mirrors `augment :: Preskel -> Node -> Cause -> Role -> (Gen,Subst) -> Instance -> [Ans]`. -/
partial def augment (k : Preskel) (n : Node) (cause : Cause) (role : Role)
    (subst : Gen × Subst) (inst : Instance) : List Ans :=
  (augmentAndDisplace k n cause role subst inst).flatMap homomorphismFilter

/-- Contraction: apply a substitution and skeletonize.
    Mirrors `contract :: Preskel -> Node -> Cause -> (Gen,Subst) -> [Ans]`. -/
partial def contract (k : Preskel) (n : Node) (cause : Cause)
    (subst : Gen × Subst) : List Ans :=
  let prs : PRS := (k, { k with operation := .Contracted [] emptySubst cause, krules := [] },
                    n, k.strandids, emptySubst)
  (ksubst prs subst).flatMap fun prs =>
    (skeletonize useThinningWhileSolving prs).flatMap homomorphismFilter

-- ── Listener augmentation ─────────────────────────────────────────────────────

/-- Add a listener strand for term `t`.
    Mirrors `addListener :: Preskel -> Node -> Cause -> Term -> [Ans]`. -/
partial def addListener (k : Preskel) (n : Node) (cause : Cause) (t : Term) : List Ans :=
  let (gen', inst)  := mkListener (protocol k) k.gen t
  let insts'        := k.insts ++ [inst]
  let pair          : Pair := ((Int.ofNat k.insts.length, 1), n)
  -- Use newPreskelBasic: result goes directly to wellFormedPreskel.
  let k'            := newPreskelBasic gen' k.shared insts' (pair :: k.orderings)
                         k.knon k.kpnon k.kunique k.kuniqgen k.kabsent k.kprecur
                         k.kgenSt k.kconf k.kauth k.kfacts k.kpriority
                         (.AddedListener [] t cause) [] k.pprob k.prob k.pov
  (wellFormedPreskel k').flatMap fun k' =>
    (skeletonize useThinningWhileSolving (k, k', n, k.strandids, emptySubst)).flatMap
      homomorphismFilter

/-- Base listener augmentation with precursor.
    Mirrors `formerAddBaseListener`. -/
partial def formerAddBaseListener (k : Preskel) (n : Node) (cause : Cause)
    (t : Term) : List Ans :=
  let (gen', t')    := basePrecursor k.gen t
  let (gen'', inst) := mkListener (protocol k) gen' t'
  let insts'        := k.insts ++ [inst]
  let pair          : Pair := ((Int.ofNat k.insts.length, 1), n)
  let precur'       := (Int.ofNat k.insts.length, 0) :: k.kprecur
  -- Use newPreskelBasic: result goes directly to wellFormedPreskel.
  let k'            := newPreskelBasic gen'' k.shared insts' (pair :: k.orderings)
                         k.knon k.kpnon k.kunique k.kuniqgen k.kabsent precur'
                         k.kgenSt k.kconf k.kauth k.kfacts k.kpriority
                         (.AddedListener [] t' cause) [] k.pprob k.prob k.pov
  (wellFormedPreskel k').flatMap fun k' =>
    (skeletonize useThinningWhileSolving (k, k', n, k.strandids, emptySubst)).flatMap
      homomorphismFilter

/-- Base listener augmentation: uses `baseRndx` if available.
    Mirrors `addBaseListener :: Preskel -> Node -> Cause -> Term -> [Ans]`. -/
partial def addBaseListener (k : Preskel) (n : Node) (cause : Cause)
    (t : Term) : List Ans :=
  match baseRndx t with
  | some ts => ts.flatMap fun x => addListener k n cause x
  | none    => formerAddBaseListener k n cause t

/-- Add an absence constraint and skeletonize.
    Mirrors `addAbsence :: Preskel -> Node -> Cause -> Term -> Term -> [Ans]`. -/
partial def addAbsence (k : Preskel) (n : Node) (cause : Cause)
    (x t : Term) : List Ans :=
  -- Use newPreskelBasic: result goes directly to wellFormedPreskel.
  let k' := newPreskelBasic k.gen k.shared k.insts k.orderings
               k.knon k.kpnon k.kunique k.kuniqgen ((x, t) :: k.kabsent) k.kprecur
               k.kgenSt k.kconf k.kauth k.kfacts k.kpriority
               (.AddedAbsence [] x t cause) k.krules k.pprob k.prob k.pov
  (wellFormedPreskel k').flatMap fun k' =>
    (skeletonize useThinningWhileSolving (k, k', n, k.strandids, emptySubst)).flatMap
      homomorphismFilter

-- ── Homomorphism ──────────────────────────────────────────────────────────────

/-- Match a strand `s` from `k` into `k'` using `mapping`.
    Mirrors `matchStrand :: Preskel -> Preskel -> [Sid] -> (Gen,Env) -> Sid -> [(Gen,Env)]`. -/
private def matchStrand (k k' : Preskel) (mapping : List Sid)
    (ge : GenEnv) (s : Sid) : List GenEnv :=
  let s' := mapping.getD s.toNat 0
  matchTraces (strandInst k s).trace (strandInst k' s').trace ge

/-- Simple left-fold over List monad (Haskell's `foldM`). -/
private def listFoldM {α β : Type} (f : β → α → List β) (acc : β) : List α → List β
  | []      => [acc]
  | x :: xs => (listFoldM f acc xs).flatMap fun acc' => f acc' x

/-- Find environments witnessing a strand-map homomorphism from `k` to `k'`.
    Mirrors `findReplacement :: Preskel -> Preskel -> [Sid] -> [(Gen,Env)]`. -/
def findReplacement (k k' : Preskel) (mapping : List Sid) : List GenEnv :=
  if mapping.length != k.insts.length then []
  else
    let gg := gmerge k.gen k'.gen
    listFoldM (matchStrand k k' mapping) (gg, emptyEnv) k.strandids

private def instantiatePair (env : Env) (p : Term × Term) : Term × Term :=
  (instantiate env p.1, instantiate env p.2)

/-- True when `env` preserves orig/gen nodes under `mapping`.
    Mirrors `validateEnvOrig :: Preskel -> Preskel -> [Sid] -> Env -> Bool`. -/
private def validateEnvOrig (k k' : Preskel) (mapping : List Sid) (env : Env) : Bool :=
  useNoOrigPreservation ||
  (k.korig.all fun (u, ns) =>
    match k'.korig.lookup (instantiate env u) with
    | none     => assertError "Strand.validateEnvOrig: term not in kunique"
    | some ns' => (ns.map (permuteNode mapping)).all ns'.contains) &&
  (k.kugen.all fun (u, ns) =>
    match k'.kugen.lookup (instantiate env u) with
    | none     => assertError "Strand.validateEnvOrig: term not in kuniqgen"
    | some ns' => (ns.map (permuteNode mapping)).all ns'.contains)

/-- Match two facts term-by-term.
    Mirrors `matchFact :: Fact -> Fact -> (Gen,Env) -> [(Gen,Env)]`. -/
private partial def matchFact (f f' : Fact) (ge : GenEnv) : List GenEnv :=
  if f.name != f'.name then []
  else matchFactArgs f.terms f'.terms ge
  where
    matchFactArgs : List FTerm → List FTerm → GenEnv → List GenEnv
      | [],              [],              ge => [ge]
      | .FSid i :: r1, .FSid j :: r2,   ge =>
          if i == j then matchFactArgs r1 r2 ge else []
      | .FSid _ :: _,   _,              _  => []
      | _,              .FSid _ :: _,   _  => []
      | .ofTerm t1 :: r1, .ofTerm t2 :: r2, ge =>
          (termMatch t1 t2 ge).flatMap fun ge' => matchFactArgs r1 r2 ge'
      | _,              _,              _  => []

/-- Extend `env` by matching uncovered facts against target facts.
    Mirrors `validateExtendEnv :: [Sid] -> (Gen,Env) -> [Fact] -> [Fact] -> [(Gen,Env)]`. -/
private partial def validateExtendEnv (mapping : List Sid)
    : GenEnv → List Fact → List Fact → List GenEnv
  | ge, [],              _            => [ge]
  | ge, fact :: uncRest, targetFacts  =>
      let updFact := updateFact (fun i => mapping.getD i.toNat 0) fact
      targetFacts.flatMap fun target =>
        (matchFact updFact target ge).flatMap fun ge' =>
          validateExtendEnv mapping ge' uncRest targetFacts

/-- Validate that an environment and strand map together form a homomorphism.
    Mirrors `validateEnv :: Preskel -> Preskel -> [Sid] -> (Gen,Env) -> [(Gen,Env)]`. -/
def validateEnv (k k' : Preskel) (mapping : List Sid) (ge : GenEnv) : List GenEnv :=
  let (_, env) := ge
  let f := fun (i : Sid) => mapping.getD i.toNat 0
  let ftermMatched : FTerm → Bool
    | .FSid _   => true
    | .ofTerm t => matched env t
  let factMatched (fact : Fact) := fact.terms.all ftermMatched
  let (covered, uncovered) := k.kfacts.partition factMatched
  let ordOk :=
    match normalizeOrderings true (permuteOrderings mapping k.orderings) with
    | [o] => o.all fun p => k'.tc.contains p
    | _   => false
  if k.knon.all   (fun t => k'.knon.contains   (instantiate env t)) &&
     k.kpnon.all  (fun t => k'.kpnon.contains  (instantiate env t)) &&
     k.kunique.all (fun t => k'.kunique.contains (instantiate env t)) &&
     k.kuniqgen.all (fun t => k'.kuniqgen.contains (instantiate env t)) &&
     k.kabsent.all (fun p => k'.kabsent.contains (instantiatePair env p)) &&
     k.kauth.all   (fun t => k'.kauth.contains   (instantiate env t)) &&
     k.kconf.all   (fun t => k'.kconf.contains   (instantiate env t)) &&
     k.kgenSt.all  (fun t => k'.kgenSt.contains  (instantiate env t)) &&
     validateEnvOrig k k' mapping env &&
     ordOk &&
     covered.all (fun fact => k'.kfacts.contains (instUpdateFact env f fact))
  then validateExtendEnv mapping ge uncovered k'.kfacts
  else []

/-- Find environments witnessing a homomorphism from `k` to `k'` via `mapping`.
    Mirrors `homomorphism :: Preskel -> Preskel -> [Sid] -> [(Gen,Env)]`. -/
def homomorphism (k k' : Preskel) (mapping : List Sid) : List GenEnv :=
  (findReplacement k k' mapping).flatMap fun ge =>
    validateEnv k k' mapping ge

-- ── Stage 6: Generalization ───────────────────────────────────────────────────

-- ── Dir / isStateChMsg / nodeIsStateNode / nodeIsStor ─────────────────────────

/-- Message direction.  Mirrors `data Dir = Send | Recv`. -/
inductive Dir where | Send | Recv

/-- True when `cm` is a channel message whose channel is a location.
    Mirrors `isStateChMsg :: ChMsg -> Bool`. -/
private def isStateChMsg : ChMsg → Bool
  | .Plain _         => false
  | .ChMsg ct _ _    => ct == .Locn

/-- The direction and channel message at a node, if any.
    Mirrors `dirChMsgOfNode :: Node -> Preskel -> Maybe (Dir, ChMsg)`. -/
def dirChMsgOfNode (n : Node) (k : Preskel) : Option (Dir × ChMsg) :=
  k.strands.get? n.1.toNat >>= fun s =>
  s.nodes.get? n.2.toNat >>= fun gn =>
  some (match gn.event with
        | .In  chm => (.Recv, chm)
        | .Out chm => (.Send, chm))

/-- True when the node carries a state channel message.
    Mirrors `nodeIsStateNode :: Preskel -> Node -> Bool`. -/
def nodeIsStateNode (k : Preskel) (n : Node) : Bool :=
  match dirChMsgOfNode n k with
  | none          => false
  | some (_, chm) => isStateChMsg chm

/-- True when the node stores (sends) a state channel message.
    Mirrors `nodeIsStor :: Preskel -> Node -> Bool`. -/
def nodeIsStor (k : Preskel) (n : Node) : Bool :=
  match dirChMsgOfNode n k with
  | some (.Send, chm) => isStateChMsg chm
  | _                 => false

-- ── Candidate ─────────────────────────────────────────────────────────────────

/-- A generalisation candidate: a preskel and a strand mapping.
    Mirrors `type Candidate = (Preskel, [Sid])`. -/
abbrev Candidate := Preskel × List Sid

/-- Wrap a preskel with the identity mapping.
    Mirrors `addIdentity :: Preskel -> Candidate`. -/
def addIdentity (k : Preskel) : Candidate := (k, k.strandids)

-- ── withCoreFacts ─────────────────────────────────────────────────────────────

/-- Restore facts from the POV skeleton via the homomorphism.
    Mirrors `withCoreFacts :: Preskel -> Preskel`. -/
def withCoreFacts (k : Preskel) : Preskel :=
  match k.pov with
  | none     => k
  | some k0  =>
      if k.prob.length != k0.insts.length then
        assertError "Strand.withCoreFacts: mapping from POV wrong length"
      else
        match homomorphism k0 k k.prob with
        | []          => k
        | (_, env) :: _ =>
            let f (s : Sid) := k.prob.getD s.toNat 0
            { k with kfacts := k0.kfacts.map (instUpdateFact env f) }

-- ── isListener / listeners ────────────────────────────────────────────────────

/-- True when `str` is a listener strand (in t, out t).
    Mirrors `isListener :: Strand -> Bool`. -/
def isListener (str : KStrand) : Bool :=
  match str.inst.trace with
  | [.In (.Plain t1), .Out (.Plain t2)] => t1 == t2
  | _                                   => false

/-- All listener strands in `k`.
    Mirrors `listeners :: Preskel -> [Strand]`. -/
def listeners (k : Preskel) : List KStrand :=
  k.strands.filter isListener

-- ── deleteOrderings / shortenOrderings ────────────────────────────────────────

/-- Drop all orderings that touch strand `s`, adjusting remaining strand ids.
    Mirrors `deleteOrderings :: Sid -> [Pair] -> [Pair]`. -/
def deleteOrderings (s : Sid) (ps : List Pair) : List Pair :=
  ps.flatMap fun ((s0, i0), (s1, i1)) =>
    if s == s0 || s == s1 then []
    else
      let adj (s' : Sid) (i' : Int) :=
        if s' > s then (s' - 1, i') else (s', i')
      [( adj s0 i0, adj s1 i1 )]

/-- Drop orderings that become invalid when strand `s` is shortened to `p` nodes.
    Mirrors `shortenOrderings :: Node -> [Pair] -> [Pair]`. -/
def shortenOrderings (n : Node) (ps : List Pair) : List Pair :=
  let (s, i) := n
  ps.flatMap fun p@((s0, i0), (s1, i1)) =>
    if s == s0 && i <= i0 then []
    else if s == s1 && i <= i1 then []
    else [p]

-- ── deleteNodeFacts ───────────────────────────────────────────────────────────

/-- Drop facts whose strand-index reference points to or past the deletion.
    Mirrors `deleteNodeFacts :: Sid -> Int -> [Fact] -> [Fact]`. -/
def deleteNodeFacts (s : Sid) (p : Int) (facts : List Fact) : List Fact :=
  let rec checkRest : List FTerm → Bool
    | []                               => true
    | .FSid s' :: .ofTerm t :: rest    =>
        if s == s' then
          match intOfIndex t with
          | some q => q < p && checkRest rest
          | none   => checkRest rest
        else checkRest rest
    | _ :: rest                        => checkRest rest
  facts.filter fun fact => checkRest fact.terms

-- ── deleteNodeRest ────────────────────────────────────────────────────────────

/-- Build the new preskel after a node deletion.
    Mirrors `deleteNodeRest :: Preskel -> Gen -> Node -> ...`. -/
def deleteNodeRest (k : Preskel) (gen : Gen) (n : Node) (insts' : List Instance)
    (orderings : List Pair) (prob : List Sid) (facts : List Fact)
    (mapping : List Sid) : Preskel :=
  let terms  := iterms insts'
  let vs     := instVars insts'
  let chans  := ichans insts'
  let mentionedIn (t : Term) := varSubset [t] terms
  let lostgen (si : Node) (t : Term) :=
    match generationPos t (k.insts.getD si.1.toNat default).trace with
    | none     => false
    | some pos => si.2 <= pos
  let nonOrig (t : Term) := varSubset [t] terms
  newPreskel gen k.shared insts' orderings
    (k.knon.filter mentionedIn)
    (k.kpnon.filter mentionedIn)
    (k.kunique.filter fun t => terms.any (carriedBy t))
    (k.kuniqgen.filter fun t => !lostgen n t)
    (k.kabsent.filter fun (x, y) => !lostgen n x && nonOrig x && nonOrig y)
    (k.kprecur.map (updateNode n.1 n.1) |>.erase n)
    (k.kgenSt.filter fun t =>
      foldVars (fun b v => b && vs.contains v) true t)
    (k.kconf.filter (chans.contains))
    (k.kauth.filter (chans.contains))
    facts
    (k.kpriority.filter fun ((s, i), _) =>
      s < n.1 || (s == n.1 && i < n.2))
    (.Generalized mapping (.Deleted n)) [] k.pprob prob k.pov

-- ── deleteNode ────────────────────────────────────────────────────────────────

/-- Delete node `n` from `k`, returning a list of (preskel, mapping) pairs.
    Mirrors `deleteNode :: Preskel -> Vertex -> [(Preskel, [Sid])]`. -/
def deleteNode (k : Preskel) (n : Vertex) : List (Preskel × List Sid) :=
  let p := n.pos
  let s := n.strandId
  if p == 0 then
    if k.prob.contains s then []
    else
      let mapping := LeanCPSA.Lib.deleteNth s.toNat k.strandids
      let k' := deleteNodeRest k k.gen (s, p)
                  (LeanCPSA.Lib.deleteNth s.toNat k.insts)
                  (deleteOrderings s k.tc)
                  (updatePerm s s k.prob)
                  ((deleteStrandFacts s k.kfacts).map (updateFact (updateStrand s s)))
                  mapping
      [(k', mapping)]
  else
    let mapping := k.strandids
    let i := strandInst k s
    (bldInstance i.role (i.trace.take p.toNat) k.gen).flatMap fun (gen', i') =>
      let k' := deleteNodeRest k gen' (s, p)
                  (LeanCPSA.Lib.replaceNth i' s.toNat k.insts)
                  (shortenOrderings (s, p) k.tc)
                  k.prob
                  (deleteNodeFacts s p k.kfacts)
                  mapping
      [(k', mapping)]

-- ── deleteNodes ───────────────────────────────────────────────────────────────

/-- Enumerate all node-deletion candidates.
    Mirrors `deleteNodes :: Preskel -> [Candidate]`. -/
def deleteNodes (k : Preskel) : List Candidate :=
  let strs := if generalizeDeleteOnlyListeners then listeners k else k.strands
  strs.flatMap fun str =>
    str.nodes.flatMap fun n =>
      (deleteNode k n).map fun (k', mapping) => (k', mapping)

-- ── sameContractedEvent / weaken / weakenOrdering / weakenOrderings ───────────

/-- True when `(s,i)` and `(s',i')` refer to the same contracted event.
    Mirrors `sameContractedEvent :: Preskel -> Node -> Node -> Bool`. -/
private partial def sameContractedEvent (k : Preskel) (n n' : Node) : Bool :=
  let (s, i)   := n
  let (s', i') := n'
  s == s' &&
  (i == i' ||
    (nodeIsStateNode k n && nodeIsStateNode k n' &&
      let validSubSeg : Bool → Int → Int → Bool := fun isStor j j' =>
        let rec loop (isStor : Bool) (j : Int) : Bool :=
          if j == j' then (if isStor then nodeIsStor k (s, j) else true)
          else if !nodeIsStateNode k (s, j + 1) then false
          else loop (isStor || nodeIsStor k (s, j + 1)) (j + 1)
        loop isStor j
      match compare i i' with
      | .lt => validSubSeg (nodeIsStor k n) i i'
      | .eq => true
      | .gt => validSubSeg (nodeIsStor k n') i' i))

/-- Build a weaker preskel by removing pair `p` from `orderings`.
    Uses `newPreskelBasic`: TC is deferred to `addExpensiveFields` in
    `Cohort.maximize` (before `simplify`) so rejected candidates don't pay it.
    Mirrors `weaken :: Preskel -> Pair -> [Pair] -> Candidate`. -/
private def weaken (k : Preskel) (p : Pair) (orderings : List Pair) : Candidate :=
  let k' := newPreskelBasic k.gen k.shared k.insts orderings
              k.knon k.kpnon k.kunique k.kuniqgen k.kabsent k.kprecur
              k.kgenSt k.kconf k.kauth k.kfacts k.kpriority
              (.Generalized k.strandids (.Weakened p)) [] k.pprob k.prob k.pov
  addIdentity k'

/-- Weaken `k` by removing one edge from the transitive closure.
    Mirrors `weakenOrdering :: Preskel -> Pair -> Candidate`. -/
private def weakenOrdering (k : Preskel) (p : Pair) : Candidate :=
  weaken k p
    (k.tc.filter fun (m, m') =>
      !(sameContractedEvent k p.1 m && sameContractedEvent k p.2 m'))

/-- All single-edge weakening candidates.
    Mirrors `weakenOrderings :: Preskel -> [Candidate]`. -/
def weakenOrderings (k : Preskel) : List Candidate :=
  k.orderings.map (weakenOrdering k)

-- ── forgetAssumption ──────────────────────────────────────────────────────────

/-- Terms in `knon` not inherited from any role.
    Mirrors `skelNons :: Preskel -> [Term]`. -/
private def skelNons (k : Preskel) : List Term :=
  let ru := k.insts.flatMap inheritRnon
  k.knon.filter fun t => !ru.contains t

/-- Terms in `kpnon` not inherited from any role. -/
private def skelPnons (k : Preskel) : List Term :=
  let ru := k.insts.flatMap inheritRpnon
  k.kpnon.filter fun t => !ru.contains t

/-- Terms in `kunique` not inherited from any role. -/
private def skelUniques (k : Preskel) : List Term :=
  let ru := k.insts.flatMap inheritRunique
  k.kunique.filter fun t => !ru.contains t

/-- Terms in `kuniqgen` not inherited from any role. -/
private def skelUniqgens (k : Preskel) : List Term :=
  let ru := k.insts.flatMap inheritRuniqgen
  k.kuniqgen.filter fun t => !ru.contains t

/-- Drop each non-inherited non-orig assumption in turn.
    Uses `renewPreskelBasic`: TC deferred to `Cohort.maximize`.
    Mirrors `forgetNonTerm :: Preskel -> [Candidate]`. -/
private def forgetNonTerm (k : Preskel) : List Candidate :=
  (skelNons k).map fun t =>
    addIdentity (renewPreskelBasic { k with
      knon      := k.knon.erase t,
      operation := .Generalized [] (.Forgot t),
      krules    := [] })

/-- Drop each non-inherited pnon assumption in turn. -/
private def forgetPnonTerm (k : Preskel) : List Candidate :=
  (skelPnons k).map fun t =>
    addIdentity (renewPreskelBasic { k with
      kpnon     := k.kpnon.erase t,
      operation := .Generalized [] (.Forgot t),
      krules    := [] })

/-- Drop each non-inherited unique assumption in turn. -/
private def forgetUniqueTerm (k : Preskel) : List Candidate :=
  (skelUniques k).map fun t =>
    addIdentity (renewPreskelBasic { k with
      kunique   := k.kunique.erase t,
      operation := .Generalized [] (.Forgot t),
      krules    := [] })

/-- Drop each non-inherited uniqgen assumption in turn. -/
private def forgetUniqgenTerm (k : Preskel) : List Candidate :=
  (skelUniqgens k).map fun t =>
    addIdentity { k with
      kuniqgen  := k.kuniqgen.erase t,
      operation := .Generalized [] (.Forgot t),
      krules    := [] }

/-- All origination-assumption forgetting candidates.
    Mirrors `forgetAssumption :: Preskel -> [Candidate]`. -/
def forgetAssumption (k : Preskel) : List Candidate :=
  forgetUniqueTerm k ++ forgetNonTerm k ++ forgetPnonTerm k ++ forgetUniqgenTerm k

-- ── separateVariables ─────────────────────────────────────────────────────────

/-- A location: strand id, role variable, place within the mapped term.
    Mirrors `type Location = (Sid, Term, Place)`. -/
abbrev Location := Sid × Term × Place

/-- The (role-variable, substituted-term) pairs for an instance.
    Mirrors `instAssocs :: Instance -> [(Term, Term)]`. -/
private def instAssocs (i : Instance) : List (Term × Term) :=
  reify i.role.rvars i.env

/-- All (variable, location) pairs across every strand.
    Mirrors `extractPlaces :: Preskel -> [(Term, Location)]`. -/
private def extractPlaces (k : Preskel) : List (Term × Location) :=
  k.strands.flatMap fun s =>
    (instAssocs s.inst).flatMap fun (v, t) =>
      (foldVars (fun acc x => adjoin x acc) ([] : List Term) t).flatMap fun var =>
        if isExpr var then []
        else (places var t).map fun p => (var, (s.sid, v, p))

/-- The locations associated with variable `t`.
    Mirrors `locsFor :: [(Term, Location)] -> Term -> [Location]`. -/
private def locsFor (ps : List (Term × Location)) (t : Term) : List Location :=
  (ps.filter fun (t', _) => t == t').map (·.2) |>.reverse

/-- Match `t` against `t'`, failing hard if no match exists.
    Mirrors `matchAlways :: Term -> Term -> (Gen,Env) -> (Gen,Env)`. -/
private def matchAlways (t t' : Term) (ge : GenEnv) : GenEnv :=
  match termMatch t t' ge with
  | e :: _ => e
  | []     => assertError "Strand.matchAlways: bad match"

/-- Apply a location change to a single maplet.
    Mirrors `changeMaplet :: [Location] -> Term -> Sid -> (Term, Term) -> (Term, Term)`. -/
private def changeMaplet (locs : List Location) (copy : Term) (s : Sid)
    (maplet : Term × Term) : Term × Term :=
  locs.foldl (fun (v, t) (s', v', p) =>
    (v, if s' == s && v' == v then replace copy p t else t)) maplet

/-- Rebuild one strand instance, relocating `copy` at each affected location.
    Mirrors `changeStrand :: [Location] -> Term -> Gen -> Strand -> [(Gen,Instance)]`. -/
private def changeStrand (locs : List Location) (copy : Term)
    (gen : Gen) (str : KStrand) : List (Gen × Instance) :=
  let i   := str.inst
  let assocs := (instAssocs i).map (changeMaplet locs copy str.sid)
  let (gen', env') := assocs.foldl
    (fun acc (v, t) => matchAlways v t acc) (gen, emptyEnv)
  let tr := (i.role.rtrace.take i.height.toNat).map (evtMap (instantiate env'))
  bldInstance i.role tr gen'

/-- Tail-recursive worker for `changeStrands`.
    Processes strands left-to-right, accumulating instances in reverse, then
    reverses at the end.  The original `foldMapM`-based version processed
    right-to-left (recurse on tail first, then head), which is equivalent but
    creates O(n) stack frames.  Since `changeStrand` returns exactly 0 or 1
    results (the match is always fully concrete after `matchAlways`), the list
    monad in `foldMapM` adds no additional branching — we can safely use a
    flat iterative fold.  Gen-counter ordering changes (only fresh-variable
    names are affected, not the search structure), which is invisible to
    `cpsa4diff`. -/
private def changeStrandsGo (locs : List Location) (copy : Term)
    : Gen → List KStrand → List Instance → Gen × List Instance
  | gen, [],           acc => (gen, acc.reverse)
  | gen, str :: rest,  acc =>
    match changeStrand locs copy gen str with
    | []                => assertError "Strand.changeStrands: bad strand build"
    | (gen', inst) :: _ => changeStrandsGo locs copy gen' rest (inst :: acc)

/-- Rebuild all strand instances, relocating `copy` at each affected location.
    Mirrors `changeStrands :: [Location] -> Term -> Gen -> [Strand] -> (Gen,[Instance])`. -/
private def changeStrands (locs : List Location) (copy : Term)
    (gen : Gen) (strs : List KStrand) : Gen × List Instance :=
  changeStrandsGo locs copy gen strs []

/-- Generate all non-empty subsets of `{0..n-1}` (as index lists).
    Mirrors `subsets :: Int -> [[Int]]`. -/
private partial def subsets (n : Int) : List (List Int) :=
  if n <= 0 then []
  else
    let sub := subsets (n - 1)
    [n - 1] :: (sub ++ sub.map ((n - 1) :: ·))

/-- Build the two candidate preskels from a set of changed locations.
    Mirrors `changeLocations :: Preskel -> Env -> Gen -> Term -> [Location] -> [Candidate]`. -/
private def changeLocations (k : Preskel) (env : Env) (gen : Gen)
    (t : Term) (locs : List Location) : List Candidate :=
  let (gen', insts') := changeStrands locs t gen k.strands
  let non    := k.knon ++ k.knon.map (instantiate env)
  let pnon   := k.kpnon ++ k.kpnon.map (instantiate env)
  let unique' := insts'.flatMap inheritRunique
  let uniqgen' := insts'.flatMap inheritRuniqgen
  let unique0  := k.kunique ++ unique'
  let unique1  := k.kunique.map (instantiate env) ++ unique'
  let uniqgen0 := k.kuniqgen ++ uniqgen'
  let uniqgen1 := k.kuniqgen.map (instantiate env) ++ uniqgen'
  let facts    := k.kfacts.map (instFact env)
  -- Use newPreskelBasic: TC is deferred to addExpensiveFields in Cohort.maximize
  -- (before simplify) so candidates never pay TC for preskels rejected by
  -- preskelWellFormed or simplify.
  let mk unique uniqgen kfacts :=
    newPreskelBasic gen' k.shared insts' k.orderings non pnon
      unique uniqgen k.kabsent k.kprecur k.kgenSt k.kconf k.kauth kfacts
      k.kpriority (.Generalized k.strandids (.Separated t))
      [] k.pprob k.prob k.pov
  [addIdentity (mk unique0 uniqgen0 k.kfacts),
   addIdentity (mk unique1 uniqgen1 facts)]

/-- Generate separation candidates for variable `t` using place information `ps`.
    Mirrors `separateVariable :: Preskel -> [(Term, Location)] -> Term -> [Candidate]`. -/
private def separateVariable (k : Preskel) (ps : List (Term × Location))
    (t : Term) : List Candidate :=
  if isChanSort t || isLocnSort t || isExpr t then []
  else
    let locs := locsFor ps t
    if locs.length <= 1 then []
    else
      let (gen', t') := clone k.gen t
      let ge := matchAlways t t' (gen', emptyEnv)
      -- In Haskell, the outer `take separateVariablesLimit` on `separateVariables`
      -- is lazy and stops evaluation after 1024 candidates total.  In Lean, `flatMap`
      -- is strict, so without an early truncation we would evaluate all 2^n subsets
      -- before `take` ever runs.  Cap at `separateVariablesLimit` subsets here so
      -- each variable contributes at most 2×separateVariablesLimit candidates; the
      -- outer take in `generalize` then limits the grand total to separateVariablesLimit.
      let parts := ((subsets (Int.ofNat locs.length)).take separateVariablesLimit).map
        (fun idxs => idxs.filterMap (fun i => locs.get? i.toNat))
      parts.flatMap fun locs' => changeLocations k ge.2 ge.1 t' locs'

/-- All variable-separation candidates.
    Mirrors `separateVariables :: Preskel -> [Candidate]`. -/
def separateVariables (k : Preskel) : List Candidate :=
  let ps := extractPlaces k
  (kvars k).flatMap (separateVariable k ps)

-- ── generalize ────────────────────────────────────────────────────────────────

/-- Enumerate all generalisation candidates for `k`.
    Mirrors `generalize :: Preskel -> [Candidate]`. -/
def generalize (k : Preskel) : List Candidate :=
  let k' := withCoreFacts k
  deleteNodes k' ++
  if generalizeOnlyByDeletion then []
  else
    forgetAssumption k' ++ weakenOrderings k' ++
    if useVariableSeparation then
      (separateVariables k').take separateVariablesLimit
    else []

/-- Generalization candidates as lazily-forced groups, in the same order as
    `generalize`, so that `Cohort.maximize` can stop before later groups are
    built.  This mirrors Haskell, where `generalize` is a lazy list consumed by
    a short-circuiting `iter` that stops at the first candidate that specializes.

    Returns `(base, sep)`:
    * `base` — the delete/forget/weaken groups (no global cap).
    * `sep`  — one separation group per skeleton variable, in `kvars` order.
      The consumer applies the global `separateVariablesLimit` budget across
      these (matching `take separateVariablesLimit (separateVariables k')`).

    Construction of each group's candidates (`changeLocations`/`newPreskelBasic`)
    is deferred to when the thunk is forced, so a protocol whose generalization
    is dominated by variable separation (e.g. wonthull2) no longer pays to build
    the whole separation space when an earlier candidate already succeeds. -/
def generalizeGroups (k : Preskel)
    : List (Unit → List Candidate) × List (Unit → List Candidate) :=
  let k' := withCoreFacts k
  if generalizeOnlyByDeletion then
    ([fun _ => deleteNodes k'], [])
  else
    let base : List (Unit → List Candidate) :=
      [ fun _ => deleteNodes k',
        fun _ => forgetAssumption k',
        fun _ => weakenOrderings k' ]
    if useVariableSeparation then
      let ps := extractPlaces k'
      let sep := (kvars k').map (fun v => (fun (_ : Unit) => separateVariable k' ps v))
      (base, sep)
    else
      (base, [])

-- ── collapse ──────────────────────────────────────────────────────────────────

/-- Try to collapse strands `s` and `s'` into one.
    Like `homomorphismFilter`, this is a pipeline EXIT GATE: it consumes the
    `skeletonize` output directly (rather than via `homomorphismFilter`), so it
    must attach the expensive TC fields here.  Otherwise collapsed skeletons —
    which flow into the search state and are displayed by `maps` (needs `tc`) —
    would be left TC-free now that `wellFormedPreskel` defers TC.
    Mirrors `collapseStrands :: Preskel -> Sid -> Sid -> [Preskel]`. -/
def collapseStrands (k : Preskel) (s s' : Sid) : List Preskel :=
  (unifyStrands k s s').flatMap fun (su, su', subst) =>
    let prs : PRS := (k, { k with operation := .Collapsed [] su su', krules := [] },
                      (0, 0), k.strandids, emptySubst)
    (ksubst prs subst).flatMap fun prs =>
    (compress true prs su su').flatMap fun prs =>
    (skeletonize useThinningDuringCollapsing prs).map fun prs =>
      updateStrandMap (let (_, _, _, sm, _) := prs; sm) (addExpensiveFields (skel prs))

/-- All strand-collapse candidates.
    Mirrors `collapse :: Preskel -> [Preskel]`. -/
def collapse (k : Preskel) : List Preskel :=
  k.strandids.flatMap fun s =>
    (nats s.toNat).flatMap fun sn =>
      collapseStrands k s (Int.ofNat sn)

-- ── Stage 7: Security goals, rules, and rewriting ────────────────────────────

-- ── Sem ───────────────────────────────────────────────────────────────────────

/-- The semantic type for goal satisfaction.
    Mirrors `type Sem = Preskel -> (Gen, Env) -> [(Gen, Env)]`. -/
abbrev Sem := Preskel → GenEnv → List GenEnv

-- ── Node helpers for goal satisfaction ───────────────────────────────────────

/-- Look up the concrete node for a node variable term.
    Mirrors `nodeLookup :: Env -> NodeTerm -> Maybe Node`. -/
private def nodeLookup (e : Env) (n : NodeTerm) : Option Node :=
  (strdLookup e n.1).bind fun s =>
  (indxLookup e n.2).map  fun i => (s, i)

/-- Match a node-variable term against a concrete node.
    Mirrors `nodeMatch :: NodeTerm -> Node -> (Gen, Env) -> [(Gen, Env)]`. -/
private def nodeMatch (n : NodeTerm) (p : Node) (ge : GenEnv) : List GenEnv :=
  let (z, t) := n
  let (s, j) := p
  (termMatch t (indxOfInt j) ge).flatMap fun ge =>
    match indxLookup ge.2 t with
    | some i => if i == j then strdMatch z s ge else []
    | none   => []

/-- True when `p` is a valid node in `k`.
    Mirrors `inSkel :: Preskel -> (Int, Int) -> Bool`. -/
private def inSkel (k : Preskel) (p : Node) : Bool :=
  let (s, i) := p
  s >= 0 && s < nstrands k && i >= 0 && i < (strandInst k s).height

/-- True when `(s, i) ≺ (s', i')` on the same strand.
    Mirrors `strandPrec :: Node -> Node -> Bool`. -/
private def strandPrec (p p' : Node) : Bool :=
  p.1 == p'.1 && p.2 < p'.2

-- ── Satisfaction helpers ──────────────────────────────────────────────────────

private def nullSem : Sem := fun _ _ => []

private def localSignal : Preskel → GenEnv → GenEnv := fun _ ge => ge

private def checkEnv (k : Preskel) (e : Env) : Bool :=
  strandBoundEnv e <= nstrands k

private def checkKFacts (k : Preskel) : Bool :=
  k.kfacts.all fun fact =>
    fact.terms.all fun ft =>
      match ft with
      | .FSid s => s < nstrands k
      | _       => true

private def checkBoth (k : Preskel) (ge : GenEnv) : Bool :=
  checkEnv k ge.2 && checkKFacts k

private def checkQuietly (k : Preskel) (ge : GenEnv) : GenEnv :=
  if checkBoth k ge then ge else localSignal k ge

private def checkSem (f : Sem) : Sem := fun k ge =>
  if checkBoth k ge then (f k ge).map (checkQuietly k)
  else [localSignal k ge]

/-- Extend the environment for a `length` predicate match.
    Mirrors `glengthExtendEnv :: Role -> Term -> Sid -> Int -> Instance -> (Gen,Env) -> [(Gen,Env)]`. -/
private def glengthExtendEnv (r : Role) (z : Term) (s : Sid) (h : Int)
    (inst : Instance) (ge : GenEnv) : List GenEnv :=
  if h > inst.height then []
  else if inst.role.rname == r.rname then strdMatch z s ge
  else
    match bldInstance r (inst.trace.take h.toNat) ge.1 with
    | []  => []
    | _   => strdMatch z s ge

-- ── Atomic formula satisfaction (g* functions) ────────────────────────────────

/-- Role-length predicate.
    Mirrors `glength :: Role -> Term -> Term -> Sem`. -/
private def glength (r : Role) (z ht : Term) : Sem := fun k ge =>
  match indxLookup ge.2 ht with
  | none   => []
  | some h =>
      match strdLookup ge.2 z with
      | none   =>
          (LeanCPSA.Lib.enum k.insts).flatMap fun (sn, inst) =>
            glengthExtendEnv r z (Int.ofNat sn) h inst ge
      | some s =>
          if s < nstrands k then glengthExtendEnv r z s h (strandInst k s) ge
          else []

/-- Match a role-parameter maplet.
    Mirrors `paramMatch :: Role -> Term -> Int -> Term -> Int -> Term -> Instance -> (Gen,Env) -> [(Gen,Env)]`. -/
private def paramMatch (r : Role) (pname : Term) (h : Int) (z : Term)
    (s : Sid) (t' : Term) (inst : Instance) (ge : GenEnv) : List GenEnv :=
  if h > inst.height then []
  else if inst.role.rname == r.rname then
    (strdMatch z s ge).flatMap fun ge => termMatch t' (instantiate inst.env pname) ge
  else
    (bldInstance r (inst.trace.take h.toNat) ge.1).flatMap fun (g', inst') =>
    (strdMatch z s (g', ge.2)).flatMap fun ge =>
    termMatch t' (instantiate inst'.env pname) ge

/-- Role-parameter predicate.
    Mirrors `gparam :: Role -> Term -> Int -> Term -> Term -> Sem`. -/
private def gparam (r : Role) (pname : Term) (h : Int) (z t' : Term) : Sem := fun k ge =>
  match strdLookup ge.2 z with
  | none   =>
      (LeanCPSA.Lib.enum k.insts).flatMap fun (sn, inst) =>
        paramMatch r pname h z (Int.ofNat sn) t' inst ge
  | some s =>
      if s < nstrands k then paramMatch r pname h z s t' (strandInst k s) ge
      else []

/-- Node-ordering predicate (uses transitive closure).
    Mirrors `gprec :: NodeTerm -> NodeTerm -> Sem`. -/
private def gprec (n n' : NodeTerm) : Sem := fun k ge =>
  let tc := k.kgpOrdsAll
  match nodeLookup ge.2 n, nodeLookup ge.2 n' with
  | some p, some p' =>
      if inSkel k p && inSkel k p' && (strandPrec p p' || tc.contains (p, p')) then [ge]
      else tc.flatMap fun (p, p') => (nodeMatch n p ge).flatMap fun ge => nodeMatch n' p' ge
  | _, _ =>
      tc.flatMap fun (p, p') => (nodeMatch n p ge).flatMap fun ge => nodeMatch n' p' ge

private def ggnon (t : Term) : Sem := fun k ge =>
  k.knon.flatMap fun t' => termMatch t t' ge

private def ggpnon (t : Term) : Sem := fun k ge =>
  k.kpnon.flatMap fun t' => termMatch t t' ge

private def gguniq (t : Term) : Sem := fun k ge =>
  k.kunique.flatMap fun t' => termMatch t t' ge

private def guniqAt (t : Term) (n : NodeTerm) : Sem := fun k ge =>
  k.korig.flatMap fun (t', ls) =>
    (termMatch t t' ge).flatMap fun ge =>
      match ls with
      | [(s, j)] =>
          (strdMatch n.1 s ge).flatMap fun ge => indxMatch n.2 j ge
      | _        => []

private def gggen (t : Term) : Sem := fun k ge =>
  k.kuniqgen.flatMap fun t' => termMatch t t' ge

private def gugenAt (t : Term) (n : NodeTerm) : Sem := fun k ge =>
  k.kugen.flatMap fun (t', ls) =>
    (termMatch t t' ge).flatMap fun ge =>
      match ls with
      | [(s, j)] =>
          (strdMatch n.1 s ge).flatMap fun ge => indxMatch n.2 j ge
      | _        => []

private def ggenstv (t : Term) : Sem := fun k ge =>
  k.kgenSt.flatMap fun t' => termMatch t t' ge

private def ggconf (t : Term) : Sem := fun k ge =>
  k.kconf.flatMap fun t' => termMatch t t' ge

private def ggauth (t : Term) : Sem := fun k ge =>
  k.kauth.flatMap fun t' => termMatch t t' ge

/-- Fact predicate.
    Mirrors `gafact :: String -> [Term] -> Sem`. -/
private def fmatch (t : Term) (ft : FTerm) (ge : GenEnv) : List GenEnv :=
  match ft with
  | .FSid s   => strdMatch t s ge
  | .ofTerm t' => termMatch t t' ge

private def fmatchList : List Term → List FTerm → GenEnv → List GenEnv
  | [],      [],      ge => [ge]
  | f :: fs, t :: ts, ge => (fmatch f t ge).flatMap fun ge => fmatchList fs ts ge
  | _,       _,       _  => []

private def gafact (name : String) (fs : List Term) : Sem := fun k ge =>
  k.kfacts.flatMap fun fact =>
    if fact.name == name then fmatchList fs fact.terms ge else []

/-- Equality/unification predicate.
    Mirrors `geq :: [Term] -> Term -> Term -> Sem`. -/
private def geq (ebvs : List Term) (t t' : Term) : Sem := fun _ ge =>
  let (_, e) := ge
  if !unmatchedVarsWithin e t ebvs then
    assertError s!"Strand.geq: unmatched variables in {reprStr t}"
  else if !unmatchedVarsWithin e t' ebvs then
    assertError s!"Strand.geq: unmatched variables in {reprStr t'}"
  else
    let ti  := instantiate e t
    let ti' := instantiate e t'
    match matched e t, matched e t' with
    | true,  true  => if ti == ti' then [ge] else []
    | false, true  => termMatch t ti' ge
    | true,  false => termMatch t' ti ge
    | false, false => assertError "Strand.geq: both terms have unbound variables"

/-- Component predicate.
    Mirrors `gcomponent :: Term -> Term -> Sem`. -/
private def gcomponent (t t' : Term) : Sem := fun k ge =>
  (components t').flatMap fun cmpt => geq [] t cmpt k ge

/-- State-node predicate.
    Mirrors `gstateNode :: NodeTerm -> Sem`. -/
private def gstateNode (n : NodeTerm) : Sem := fun k ge =>
  match nodeLookup ge.2 n with
  | some p => if nodeIsStateNode k p then [ge] else []
  | none   =>
      (genNodes k).flatMap fun p =>
        if nodeIsStateNode k p then nodeMatch n p ge else []

/-- Match channel messages at `p` (send) and `p'` (recv).
    Mirrors `chMsgMatch` and `dirMsgMatch` combined. -/
private def dirMsgMatch (p p' : Node) : Sem := fun k ge =>
  match dirChMsgOfNode p k with
  | none | some (.Recv, _) => []
  | some (.Send, cm) =>
      match dirChMsgOfNode p' k with
      | none | some (.Send, _) => []
      | some (.Recv, cm') =>
          match cm, cm' with
          | .Plain _, .ChMsg _ _ _ | .ChMsg _ _ _, .Plain _ => []
          | .Plain m,        .Plain m'          => if m == m' then [ge] else []
          | .ChMsg ct c m,   .ChMsg ct' c' m'   =>
              if ct != ct' || c != c' || m != m' then [] else [ge]

/-- Communication-pair predicate.
    Mirrors `gcommpair :: NodeTerm -> NodeTerm -> Sem`. -/
private def gcommpair (n n' : NodeTerm) : Sem := fun k ge =>
  match nodeLookup ge.2 n, nodeLookup ge.2 n' with
  | some p, some p' => dirMsgMatch p p' k ge
  | some p, none    =>
      (genNodes k).flatMap fun p' =>
        (nodeMatch n' p' ge).flatMap fun ge => dirMsgMatch p p' k ge
  | none, some p'   =>
      (genNodes k).flatMap fun p =>
        (nodeMatch n p ge).flatMap fun ge => dirMsgMatch p p' k ge
  | none, none      =>
      (genNodes k).flatMap fun p =>
      (nodeMatch n p ge).flatMap fun ge =>
      (genNodes k).flatMap fun p' =>
      (nodeMatch n' p' ge).flatMap fun ge =>
        dirMsgMatch p p' k ge

/-- The location (channel variable) of a node, if it is a state node.
    Mirrors `nodeLocn :: Node -> Preskel -> [Term]`. -/
private def nodeLocn (p : Node) (k : Preskel) : List Term :=
  match dirChMsgOfNode p k with
  | none | some (_, .Plain _)          => []
  | some (_, .ChMsg .Chan _ _)         => []
  | some (_, .ChMsg .Locn c _)         => [c]

private def glocnSem (n : NodeTerm) (k : Preskel) (ge : GenEnv) : List (Term × GenEnv) :=
  match nodeLookup ge.2 n with
  | some p => (nodeLocn p k).map fun loc => (loc, ge)
  | none   =>
      (genNodes k).flatMap fun p =>
        (nodeLocn p k).flatMap fun loc =>
          (nodeMatch n p ge).map fun ge => (loc, ge)

/-- Same-location predicate.
    Mirrors `gsamelocn :: NodeTerm -> NodeTerm -> Sem`.
    Uses nested `foldl` with prepend to match Haskell's accumulation order:
    outer processes left-to-right prepending each inner result, and the
    inner also processes left-to-right prepending matches. This produces the
    same environment ordering as Haskell, which matters for fact generation. -/
private def gsamelocn (n n' : NodeTerm) : Sem := fun k ge =>
  (glocnSem n k ge).foldl (fun soFar (l, ge) =>
    (glocnSem n' k ge).foldl (fun soFar' (l', ge') =>
      if l' == l then ge' :: soFar' else soFar') []
    ++ soFar) []

-- ── satisfy / conjoin / conjoinEbvs ──────────────────────────────────────────

/-- Extend `ge` to satisfy atomic formula `a` (existential variables in `ebvs`).
    Mirrors `satisfy :: AForm -> [Term] -> Sem`. -/
partial def satisfy (a : AForm) (ebvs : List Term) : Sem := fun k ge =>
  match a with
  | .Length r z h       => glength r z h k ge
  | .Param r v i z t   => gparam r v i z t k ge
  | .Prec n n'          => gprec n n' k ge
  | .Non t              => ggnon t k ge
  | .Pnon t             => ggpnon t k ge
  | .Uniq t             => gguniq t k ge
  | .UniqAt t n         => guniqAt t n k ge
  | .Ugen t             => gggen t k ge
  | .UgenAt t n         => gugenAt t n k ge
  | .GenStV t           => ggenstv t k ge
  | .Conf t             => ggconf t k ge
  | .Auth t             => ggauth t k ge
  | .AFact name fs      => gafact name fs k ge
  | .Equals t t'        => geq ebvs t t' k ge
  | .Component t t'     => gcomponent t t' k ge
  | .Commpair n n'      => gcommpair n n' k ge
  | .SameLocn n n'      => gsamelocn n n' k ge
  | .StateNode n        => gstateNode n k ge
  | .Trans (t, t')      => gafact "trans" [t, t'] k ge
  | .LeadsTo n n'       =>
      (satisfy (.Commpair n n') [] k ge).flatMap fun ge =>
      (satisfy (.Prec n n') [] k ge).flatMap fun ge =>
        satisfy (.StateNode n) [] k ge

/-- Satisfy a conjunction of atomic formulas.
    Mirrors `conjoin :: [AForm] -> Sem`. -/
def conjoin (as : List AForm) (k : Preskel) (ge : GenEnv) : List GenEnv :=
  as.foldl (fun ges a => ges.flatMap (satisfy a [] k)) [ge]

/-- Satisfy a conjunction in the presence of existentially bound variables.
    Mirrors `conjoinEbvs :: [AForm] -> [Term] -> Sem`. -/
def conjoinEbvs (as : List AForm) (ebvs : List Term) (k : Preskel) (ge : GenEnv)
    : List GenEnv :=
  as.foldl (fun ges a => ges.flatMap (satisfy a ebvs k)) [ge]

-- ── counterExamples / goalCounterExamples ────────────────────────────────────

/-- Return environments that satisfy the antecedent but not any conclusion.
    Mirrors `counterExamples :: Preskel -> Goal -> (Goal, [(Gen, Env)])`. -/
def counterExamples (k : Preskel) (g : Goal) : Goal × List GenEnv :=
  let conclusionSucceeds (ge : GenEnv) :=
    g.consq.any fun (ebvs, a) => !(conjoinEbvs a ebvs k ge).isEmpty
  (g, (conjoin g.antec k (k.gen, emptyEnv)).filter fun ge =>
    envStrandsWithin ge.2 k.prob && !conclusionSucceeds ge)

/-- All goals with counterexamples.
    Mirrors `goalCounterExamples :: Preskel -> [(Goal, [(Gen, Env)])]`. -/
def goalCounterExamples (k : Preskel) : List (Goal × List GenEnv) :=
  (kgoals k).foldr (fun goal acc =>
    match counterExamples k goal with
    | (_, []) => acc
    | pair    => pair :: acc) []

/-- Unsatisfied atomic formulas in the conclusion for a given assignment.
    Mirrors `unSatReport :: Preskel -> Goal -> (Gen, Env) -> [AForm]`. -/
def unSatReport (k : Preskel) (g : Goal) (ge : GenEnv) : List AForm :=
  match g.consq with
  | []   => [.AFact "false" []]
  | eas  =>
      let rec iter (ebvs : List Term) : List AForm → GenEnv → List AForm
        | [],      _   => []
        | a :: as', ge =>
            match satisfy a ebvs k ge with
            | []      => a :: iter ebvs as' ge
            | ge' :: _ => iter ebvs as' ge'
      eas.flatMap fun (ebvs, as') => iter ebvs as' ge

-- ── Isomorphism factoring ─────────────────────────────────────────────────────

/-- Merge two lists removing from `as` those isomorphic to any element of `bs`.
    Mirrors `mergeEqRel :: (a -> a -> Bool) -> [a] -> [a] -> [a]`. -/
private def mergeEqRel {α : Type} (eqRel : α → α → Bool) (as bs : List α) : List α :=
  let rec loop : List α → List α → List α
    | [],       keep => keep ++ bs
    | a :: rest, keep =>
        if bs.any (eqRel a) then loop rest keep
        else loop rest (a :: keep)
  loop as []

/-- Reduce a list to a maximal subset with no two elements related by `eqRel`.
    Mirrors `parFactor :: (a -> a -> Bool) -> [a] -> [a]`. -/
private partial def parFactor {α : Type} (eqRel : α → α → Bool) : List α → List α
  | []       => []
  | [a]      => [a]
  | [a, b]   => if eqRel a b then [b] else [a, b]
  | as       =>
      let (left, right) := as.splitAt (as.length / 2)
      mergeEqRel eqRel (parFactor eqRel left) (parFactor eqRel right)

/-- Remove isomorphic duplicate preskels.
    Mirrors `factorIsomorphic :: [Preskel] -> [Preskel]`. -/
def factorIsomorphic (ks : List Preskel) : List Preskel :=
  parFactor (fun k1 k2 => isomorphic (gist k1) (gist k2)) ks

/-- Merge two preskel lists removing isomorphic duplicates.
    Mirrors `mergeIsomorphic :: [Preskel] -> [Preskel] -> [Preskel]`. -/
def mergeIsomorphic (ks ks' : List Preskel) : List Preskel :=
  mergeEqRel (fun k1 k2 => isomorphic (gist k1) (gist k2)) ks ks'

def factorIsomorphicPreskels : List Preskel → List Preskel := factorIsomorphic

-- ── URewriteVal / URewrite ───────────────────────────────────────────────────

/-- Result of a unary rewrite step.
    Mirrors `data URewriteVal = None | Some (Preskel, (Gen, Env)) | Failing String`. -/
inductive URewriteVal where
  | none    : URewriteVal
  | some    : Preskel × GenEnv → URewriteVal
  | failing : String → URewriteVal

instance : Inhabited URewriteVal := ⟨.none⟩

/-- The type of a unary rewrite function.
    Mirrors `type URewrite = Preskel -> (Gen, Env) -> URewriteVal`. -/
abbrev URewrite := Preskel → GenEnv → URewriteVal

/-- Check-wrap a `URewrite`.
    Mirrors `checkURewrite :: URewrite -> URewrite`. -/
private def checkURewrite (f : URewrite) : URewrite := fun k ge =>
  if checkBoth k ge then
    match f k ge with
    | .none           => .none
    | .failing st     => .failing st
    | .some (k', ge') =>
        .some (k', if checkBoth k' ge' then ge' else localSignal k' ge')
  else .some (k, localSignal k ge)

-- ── addStrand / rSubst / rCompress / rDisplace ────────────────────────────────

/-- Add a fresh strand of role `r` and height `h` to `k`.
    Mirrors `addStrand :: Gen -> Preskel -> Role -> Int -> Preskel`. -/
def addStrand (g : Gen) (k : Preskel) (r : Role) (h : Nat) : Preskel :=
  let (g', inst) := mkInstance g r emptyEnv (Int.ofNat h)
  let insts'  := k.insts ++ [inst]
  newPreskel g' k.shared insts' k.orderings
    (inheritRnon inst ++ k.knon) (inheritRpnon inst ++ k.kpnon)
    (inheritRunique inst ++ k.kunique) (inheritRuniqgen inst ++ k.kuniqgen)
    (inheritRabsent inst ++ k.kabsent) k.kprecur k.kgenSt
    (inheritRconf inst ++ k.kconf) (inheritRauth inst ++ k.kauth)
    k.kfacts k.kpriority k.operation k.krules k.pprob k.prob k.pov

/-- Apply a substitution to all instances, rebuilding the preskel.
    Mirrors `rSubst :: Preskel -> (Gen, Subst) -> [Preskel]`. -/
private def rSubst (k : Preskel) (gs : Gen × Subst) : List Preskel :=
  let (gen, subst) := gs
  (foldMapM (substInst subst) gen k.insts).flatMap fun (gen', insts') =>
    [newPreskel gen' k.shared insts' k.orderings
      (k.knon.map (substitute subst)) (k.kpnon.map (substitute subst))
      (k.kunique.map (substitute subst)) (k.kuniqgen.map (substitute subst))
      (k.kabsent.map fun (x, y) => (substitute subst x, substitute subst y))
      k.kprecur (k.kgenSt.map (substitute subst))
      (k.kconf.map (substitute subst)) (k.kauth.map (substitute subst))
      (k.kfacts.map (substFact subst)) k.kpriority
      (substOper subst k.operation) k.krules k.pprob k.prob k.pov]

/-- Update a strand map when compressing strand `i` onto `j`.
    Mirrors `compressUpdate :: Int -> Int -> [Sid] -> [Sid]`. -/
private def compressUpdate (i j : Sid) (xs : List Sid) : List Sid :=
  if i.toNat < xs.length && j.toNat < xs.length then
    xs.map (updateStrand i j)
  else if i.toNat < xs.length then
    let x := xs.getD i.toNat 0
    (xs.erase x) ++ [x]
  else xs

/-- Compress strand `s` into `s'` for rule application.
    Mirrors `rCompress :: Preskel -> Sid -> Sid -> [Preskel]`. -/
private def rCompress (k : Preskel) (s s' : Sid) : List Preskel :=
  let perm := updatePerm s s' k.strandids
  (normalizeOrderings true (permuteOrderings perm k.orderings)).map fun orderings' =>
    newPreskel k.gen k.shared (LeanCPSA.Lib.deleteNth s.toNat k.insts) orderings'
      k.knon k.kpnon k.kunique k.kuniqgen k.kabsent
      (k.kprecur.map (permuteNode perm))
      k.kgenSt k.kconf k.kauth
      (k.kfacts.map (updateFact (updateStrand s s')))
      (updatePriority perm k.kpriority)
      (let op := k.operation
       LeanCPSA.Operation.addStrandMap (compressUpdate s s' (LeanCPSA.Operation.getStrandMap op)) op)
      k.krules k.pprob (updateProb perm k.prob) k.pov

/-- Try to displace strand `s` onto `s'`, updating the environment.
    Mirrors `rDisplace :: Env -> Preskel -> Sid -> Sid -> [(Preskel, (Gen, Env))]`. -/
private partial def rDisplace (e : Env) (k : Preskel) (ns s : Sid)
    : List (Preskel × GenEnv) :=
  if ns == s then [(k, (k.gen, e))]
  else
    (unifyStrands k ns s).flatMap fun (ns', s', subst) =>
    (rSubst k subst).flatMap fun k =>
    (rCompress k ns' s').map fun k =>
      let e' := strdUpdate (substUpdate e subst.2) (updateStrand ns' s')
      (k, (k.gen, e'))

/-- Unify `t` and `t'` and apply the resulting substitution.
    Mirrors `rUnify :: Preskel -> (Gen, Env) -> Term -> Term -> [(Preskel, (Gen, Env))]`. -/
private def rUnify (k : Preskel) (ge : GenEnv) (t t' : Term) : List (Preskel × GenEnv) :=
  (unify t t' (ge.1, emptySubst)).flatMap fun subst =>
    (rSubst k subst).map fun k => (k, (k.gen, substUpdate ge.2 subst.2))

/-- Retrieve the parameter binding from a matched strand instance.
    Mirrors `rParam :: String -> Preskel -> (Gen, Env) -> Term -> Term -> [(Preskel, (Gen, Env))]`. -/
private def rParam (rule : String) (k : Preskel) (ge : GenEnv) (t t' : Term)
    : List (Preskel × GenEnv) :=
  if !matched ge.2 t then
    assertError s!"In rule {rule}, parameter predicate did not get a value"
  else rUnify k ge (instantiate ge.2 t) t'

private def badIndex (k : Preskel) (s : Sid) (i : Int) : Bool :=
  i >= (strandInst k s).height

private def checkOrigination (t : Term) (c : Trace) (i : Nat) : Bool :=
  originationPos t c == some (Int.ofNat i)

private def checkGeneration (t : Term) (c : Trace) (i : Nat) : Bool :=
  generationPos t c == some (Int.ofNat i)

-- ── ur* atomic rewrite helpers ────────────────────────────────────────────────

private def urlength (rule : String) (r : Role) (z ht : Term) : URewrite := fun k ge =>
  let (g, e) := ge
  match indxLookup e ht with
  | none   => .failing s!"In rule {rule}, role length did not get a height"
  | some h =>
      if r.rtrace.length < h.toNat then .none
      else
        match strdLookup e z with
        | some s =>
            let k' := addStrand g k r h.toNat
            match rDisplace e k' (nstrands k) s with
            | []        => .none
            | [kge]     => .some kge
            | _         => assertError "urlength: rDisplace multiple results"
        | none   =>
            .failing s!"urlength: strand variable unbound {reprStr z}"

private def urparam (rule : String) (r : Role) (v : Term) (h : Int)
    (z t : Term) : URewrite := fun k ge =>
  let (g, e) := ge
  match strdLookup e z with
  | none   => .failing s!"In rule {rule}, parameter predicate did not get a strand"
  | some s =>
      let inst := strandInst k s
      let t'   := instantiate inst.env v
      let k'   := addStrand g k r h.toNat
      let ns   := nstrands k
      match rDisplace e k' ns s with
      | []         => .none
      | [(k, ge)]  =>
          match rParam rule k ge t t' with
          | []    => .none
          | [kge] => .some kge
          | _     => assertError "urparam: rParam multiple results"
      | _          => assertError "urparam: rDisplace multiple results"

private partial def prevIn (inst : Instance) (i : Int) : Option Int :=
  if i < 0 || i.toNat >= inst.trace.length then none
  else match inbnd (inst.trace.get! i.toNat) with
  | some _ => some i
  | none   => if 0 < i then prevIn inst (i - 1) else none

private partial def succOut (inst : Instance) (i : Int) : Option Int :=
  if i < 0 || i.toNat >= inst.trace.length then none
  else match outbnd (inst.trace.get! i.toNat) with
  | some _ => some i
  | none   => if i + 1 < inst.height then succOut inst (i + 1) else none

private def urprec (rule : String) (n n' : NodeTerm) : URewrite := fun k ge =>
  let (z, t)   := n
  let (z', t') := n'
  let (g, e)   := ge
  match strdLookup e z, strdLookup e z', indxLookup e t, indxLookup e t' with
  | some s, some s', some i, some i' =>
      if badIndex k s i || badIndex k s' i' then .none
      else if k.tc.contains ((s, i), (s', i')) then .some (k, ge)
      else
        match succOut (strandInst k s) i, prevIn (strandInst k s') i' with
        | some i'', some i''' =>
            match normalizeOrderings true (((s, i''), (s', i''')) :: k.orderings) with
            | []             => .none
            | [orderings']   =>
                let k' := newPreskel g k.shared k.insts orderings'
                            k.knon k.kpnon k.kunique k.kuniqgen k.kabsent k.kprecur
                            k.kgenSt k.kconf k.kauth k.kfacts k.kpriority
                            k.operation k.krules k.pprob k.prob k.pov
                .some (k', (k.gen, e))
            | _              => assertError "urprec: normalizeOrderings multiple results"
        | _, _ => .none
  | _, _, _, _ => .failing s!"In rule {rule}, precedence did not get a strand or height"

private def mkPreskelAddNon (k : Preskel) (t' : Term) : Preskel :=
  newPreskel k.gen k.shared k.insts k.orderings
    (t' :: k.knon) k.kpnon k.kunique k.kuniqgen k.kabsent k.kprecur
    k.kgenSt k.kconf k.kauth k.kfacts k.kpriority k.operation k.krules k.pprob k.prob k.pov

private def mkPreskelAddPnon (k : Preskel) (t' : Term) : Preskel :=
  newPreskel k.gen k.shared k.insts k.orderings
    k.knon (t' :: k.kpnon) k.kunique k.kuniqgen k.kabsent k.kprecur
    k.kgenSt k.kconf k.kauth k.kfacts k.kpriority k.operation k.krules k.pprob k.prob k.pov

private def mkPreskelAddUniq (k : Preskel) (t' : Term) : Preskel :=
  newPreskel k.gen k.shared k.insts k.orderings
    k.knon k.kpnon (t' :: k.kunique) k.kuniqgen k.kabsent k.kprecur
    k.kgenSt k.kconf k.kauth k.kfacts k.kpriority k.operation k.krules k.pprob k.prob k.pov

private def mkPreskelAddUgen (k : Preskel) (t' : Term) : Preskel :=
  newPreskel k.gen k.shared k.insts k.orderings
    k.knon k.kpnon k.kunique (t' :: k.kuniqgen) k.kabsent k.kprecur
    k.kgenSt k.kconf k.kauth k.kfacts k.kpriority k.operation k.krules k.pprob k.prob k.pov

private def mkPreskelAddGenSt (k : Preskel) (t' : Term) : Preskel :=
  newPreskel k.gen k.shared k.insts k.orderings
    k.knon k.kpnon k.kunique k.kuniqgen k.kabsent k.kprecur
    (adjoin t' k.kgenSt) k.kconf k.kauth k.kfacts k.kpriority
    k.operation k.krules k.pprob k.prob k.pov

private def mkPreskelAddConf (k : Preskel) (t' : Term) : Preskel :=
  newPreskel k.gen k.shared k.insts k.orderings
    k.knon k.kpnon k.kunique k.kuniqgen k.kabsent k.kprecur
    k.kgenSt (t' :: k.kconf) k.kauth k.kfacts k.kpriority
    k.operation k.krules k.pprob k.prob k.pov

private def mkPreskelAddAuth (k : Preskel) (t' : Term) : Preskel :=
  newPreskel k.gen k.shared k.insts k.orderings
    k.knon k.kpnon k.kunique k.kuniqgen k.kabsent k.kprecur
    k.kgenSt k.kconf (t' :: k.kauth) k.kfacts k.kpriority
    k.operation k.krules k.pprob k.prob k.pov

private def mkPreskelAddFact (k : Preskel) (fact : Fact) : Preskel :=
  newPreskel k.gen k.shared k.insts k.orderings
    k.knon k.kpnon k.kunique k.kuniqgen k.kabsent k.kprecur
    k.kgenSt k.kconf k.kauth (k.kfacts.eraseDups.cons fact |>.eraseDups) k.kpriority
    k.operation k.krules k.pprob k.prob k.pov

private def urnon (rule : String) (t : Term) : URewrite := fun k ge =>
  let (_, e) := ge
  if !matched e t then .failing s!"In rule {rule}, non did not get a term"
  else
    let t' := instantiate e t
    if k.knon.contains t' then .some (k, ge)
    else if !isAtom t' then .none
    else .some (mkPreskelAddNon k t', ge)

private def urpnon (rule : String) (t : Term) : URewrite := fun k ge =>
  let (_, e) := ge
  if !matched e t then .failing s!"In rule {rule}, pnon did not get a term"
  else
    let t' := instantiate e t
    if k.kpnon.contains t' then .some (k, ge)
    else if !isAtom t' then .none
    else .some (mkPreskelAddPnon k t', ge)

private def uruniq (rule : String) (t : Term) : URewrite := fun k ge =>
  let (_, e) := ge
  if !matched e t then .failing s!"In rule {rule}, uniq did not get a term"
  else
    let t' := instantiate e t
    if k.kunique.contains t' then .some (k, ge)
    else if !isAtom t' then .none
    else .some (mkPreskelAddUniq k t', ge)

private def uruniqAt (rule : String) (t : Term) (n : NodeTerm) : URewrite := fun k ge =>
  let (_, e) := ge
  let (z, ht) := n
  match matched e t, strdLookup e z, indxLookup e ht with
  | false, _, _ => .failing s!"In rule {rule}, uniq-at did not get a term"
  | _, none, _ => .failing s!"In rule {rule}, uniq-at did not get a strand"
  | _, _, none => .failing s!"In rule {rule}, uniq-at did not get an index"
  | true, some s, some i =>
      let t' := instantiate e t
      if k.korig.any fun (u, ns) => u == t' && ns == [(s, i)] then .some (k, ge)
      else if !isAtom t' then .none
      else if i >= (strandInst k s).height then .none
      else if checkOrigination t' (strandInst k s).trace i.toNat then
        .some (mkPreskelAddUniq k t', ge)
      else .failing s!"In rule {rule}, uniq-at not at an origination"

private def urugen (rule : String) (t : Term) : URewrite := fun k ge =>
  let (_, e) := ge
  if !matched e t then .failing s!"In rule {rule}, ugen did not get a term"
  else
    let t' := instantiate e t
    if k.kuniqgen.contains t' then .some (k, ge)
    else if !isAtom t' then .none
    else .some (mkPreskelAddUgen k t', ge)

private def urugenAt (rule : String) (t : Term) (n : NodeTerm) : URewrite := fun k ge =>
  let (_, e) := ge
  let (z, ht) := n
  match matched e t, strdLookup e z, indxLookup e ht with
  | false, _, _ => .failing s!"In rule {rule}, ugen-at did not get a term"
  | _, none, _ => .failing s!"In rule {rule}, ugen-at did not get a strand"
  | _, _, none => .failing s!"In rule {rule}, ugen-at did not get an index"
  | true, some s, some i =>
      let t' := instantiate e t
      if k.kugen.any fun (u, ns) => u == t' && ns == [(s, i)] then .some (k, ge)
      else if !isAtom t' then .none
      else if i >= (strandInst k s).height then .none
      else if checkGeneration t' (strandInst k s).trace i.toNat then
        .some (mkPreskelAddUgen k t', ge)
      else .failing s!"In rule {rule}, ugen-at not at a generation"

private def urgenst (rule : String) (t : Term) : URewrite := fun k ge =>
  let (_, e) := ge
  if !matched e t then .failing s!"In rule {rule}, genSt did not get a term"
  else
    let t' := instantiate e t
    if k.kgenSt.contains t' then .some (k, ge)
    else .some (mkPreskelAddGenSt k t', ge)

private def urconf (rule : String) (t : Term) : URewrite := fun k ge =>
  let (_, e) := ge
  if !matched e t then .failing s!"In rule {rule}, conf did not get a term"
  else
    let t' := instantiate e t
    if k.kconf.contains t' then .some (k, ge)
    else if !isAtom t' then .none
    else .some (mkPreskelAddConf k t', ge)

private def urauth (rule : String) (t : Term) : URewrite := fun k ge =>
  let (_, e) := ge
  if !matched e t then .failing s!"In rule {rule}, auth did not get a term"
  else
    let t' := instantiate e t
    if k.kauth.contains t' then .some (k, ge)
    else if !isAtom t' then .none
    else .some (mkPreskelAddAuth k t', ge)

private def rFactLookup (rule : String) (e : Env) (t : Term) : FTerm :=
  if isStrdVar t then
    match strdLookup e t with
    | some s => .FSid s
    | none   => assertError s!"In rule {rule}: fact did not get a strand"
  else if matched e t then .ofTerm (instantiate e t)
  else assertError s!"In rule {rule}: fact did not get a term"

private def urafact (rule : String) (predname : String) (fts : List Term)
    : URewrite := fun k ge =>
  let (_, e) := ge
  let fts' := fts.map (rFactLookup rule e)
  let fact := { name := predname, terms := fts' }
  if k.kfacts.contains fact then .some (k, ge)
  else .some (mkPreskelAddFact k fact, (k.gen, e))

private def ureq (rule : String) (x y : Term) : URewrite := fun k ge =>
  let (g, e) := ge
  if isStrdVar x && isStrdVar y then
    match strdLookup e x, strdLookup e y with
    | some s, some t =>
        if s == t then .some (k, ge)
        else if s < nstrands k && t < nstrands k then
          match rDisplace e { k with gen := gmerge g k.gen } s t with
          | []        => .none
          | [(k', ge')] => .some (k', ge')
          | _         => assertError "ureq: rDisplace multiple results"
        else assertError s!"ureq: indices too large ({s}, {t})"
    | _, _ => .failing s!"In rule {rule}, = did not get a strand"
  else if isStrdVar x || isStrdVar y then .none
  else
    let u := if matched e x then instantiate e x else x
    let v := if matched e y then instantiate e y else y
    if u == v then .some (k, ge)
    else
      match rUnify k ge u v with
      | []          => .none
      | [(k', ge')] => .some (k', ge')
      | _           => assertError "ureq: rUnify multiple results"

private def urcommpair (rule : String) (n n' : NodeTerm) : URewrite := fun k ge =>
  match nodeLookup ge.2 n with
  | none   => .failing s!"In rule {rule}, comm-pair did not get two node terms"
  | some p =>
      match dirChMsgOfNode p k with
      | none | some (.Recv, _) => .none
      | some (.Send, cm) =>
          match nodeLookup ge.2 n' with
          | none    => .failing s!"In rule {rule}, comm-pair did not get two node terms"
          | some p' =>
              match dirChMsgOfNode p' k with
              | none | some (.Send, _) => .none
              | some (.Recv, cm') =>
                  match cm, cm' with
                  | .Plain _, .ChMsg _ _ _ | .ChMsg _ _ _, .Plain _ => .none
                  | .Plain m,        .Plain m'          => ureq rule m m' k ge
                  | .ChMsg ct c m,   .ChMsg ct' c' m'   =>
                      if ct != ct' then .none else
                      match ureq rule c c' k ge with
                      | .none | .failing _ => .none
                      | .some (k', ge')    => ureq rule m m' k' ge'

private def ursamelocn (rule : String) (n n' : NodeTerm) : URewrite := fun k ge =>
  match nodeLookup ge.2 n, nodeLookup ge.2 n' with
  | some p, some p' =>
      match nodeLocn p k, nodeLocn p' k with
      | [c], [c'] => ureq rule c c' k ge
      | _,   _    => .none
  | _, _ => .failing s!"In rule {rule}, same-locn did not get two node terms"

private def urstateNode (rule : String) (n : NodeTerm) : URewrite := fun k ge =>
  match nodeLookup ge.2 n with
  | some p => if nodeIsStateNode k p then .some (k, ge) else .none
  | none   => .failing s!"In rule {rule}, state-node did not get a node term"

-- ── uconjoin / urwt (mutually recursive via LeadsTo) ─────────────────────────

mutual

/-- Satisfy a conjunction for unary rewriting.
    Mirrors `uconjoin :: String -> [AForm] -> URewrite`. -/
private partial def uconjoin (rule : String) : List AForm → URewrite
  | [],        k, ge => .some (k, ge)
  | af :: rest, k, ge =>
      match checkURewrite (urwt rule af) k ge with
      | .some (k', ge') => uconjoin rule rest k' ge'
      | result          => result

/-- Dispatch unary rewrite for each `AForm`.
    Mirrors `urwt :: String -> AForm -> URewrite`. -/
private partial def urwt (rule : String) : AForm → URewrite
  | .Length r z ht     => urlength rule r z ht
  | .Param r v i z t   => urparam rule r v i z t
  | .Prec n n'         => urprec rule n n'
  | .Non t             => urnon rule t
  | .Pnon t            => urpnon rule t
  | .Uniq t            => uruniq rule t
  | .UniqAt t n        => uruniqAt rule t n
  | .Ugen t            => urugen rule t
  | .UgenAt t n        => urugenAt rule t n
  | .GenStV t          => urgenst rule t
  | .Conf t            => urconf rule t
  | .Auth t            => urauth rule t
  | .AFact name fs     => urafact rule name fs
  | .Equals t t'       => ureq rule t t'
  | .Component _ _    => fun _ _ =>
        .failing s!"In rule {rule}, component in conclusion"
  | .Commpair n n'     => urcommpair rule n n'
  | .SameLocn n n'     => ursamelocn rule n n'
  | .StateNode n       => urstateNode rule n
  | .Trans (t, t')     => urafact rule "trans" [t, t']
  | .LeadsTo n n'      =>
        uconjoin rule [.Commpair n n', .Prec n n', .StateNode n]

end  -- mutual uconjoin / urwt

-- ── rewriteUnary cluster ──────────────────────────────────────────────────────

/-- Result of a unary rewrite pass.
    Mirrors `data Ternary k = Unsat | Unch | Found k`. -/
inductive Ternary (α : Type) where
  | unsat : Ternary α
  | unch  : Ternary α
  | found : α → Ternary α

instance {α : Type} : Inhabited (Ternary α) := ⟨.unsat⟩

/-- True when the nullary rules' antecedents are all unsatisfied.
    Mirrors `checkNullary :: Preskel -> Bool`. -/
def checkNullary (k : Preskel) : Bool :=
  (protocol k).nullaryrules.all fun nr =>
    (conjoin nr.rlgoal.antec k (k.gen, emptyEnv)).isEmpty

/-- Apply a single conjunct of a unary rule to all satisfied environments.
    Mirrors `rewriteUnaryOneOnce`. -/
partial def rewriteUnaryOneOnce (rn : String) (conjuncts : List AForm)
    (k : Preskel) (ge : GenEnv) : Option Preskel :=
  match conjuncts with
  | []       => some k
  | a :: as' =>
      match checkURewrite (urwt rn a) k ge with
      | .none | .failing _ => none
      | .some (k', ge')    =>
          if !preskelWellFormed k' then none
          else
            match toSkeleton false { k' with krules := k'.krules.eraseDups.cons rn |>.eraseDups } with
            | []    => none
            | k'' :: _ => rewriteUnaryOneOnce rn as' k'' ge'

/-- Apply a unary rule at all satisfying environments (foldM over Maybe).
    Mirrors `rewriteUnaryOne :: Preskel -> Rule -> [(Gen, Env)] -> Maybe Preskel`. -/
def rewriteUnaryOne (k : Preskel) (ur : Rule) (vas : List GenEnv) : Option Preskel :=
  match ur.rlgoal.consq with
  | [([], conjuncts)] =>
      vas.foldlM (fun k ge => rewriteUnaryOneOnce ur.rlname conjuncts k ge) k
  | _ => none

/-- All antecedent-satisfying environments for which the conclusion fails.
    Mirrors `tryRule :: Preskel -> Rule -> [(Gen, Env)]`. -/
def tryRule (k : Preskel) (r : Rule) : List GenEnv :=
  (conjoin r.rlgoal.antec k (k.gen, emptyEnv)).filter fun ge =>
    r.rlgoal.consq.all fun (ebvs, a) => (conjoinEbvs a ebvs k ge).isEmpty

private partial def rewriteUnaryLoop (urs : List Rule)
    (k : Preskel) (urs' : List Rule) (changed : Bool) (changed2 : Bool) : Ternary Preskel :=
  match urs' with
  | [] =>
      if !changed && !changed2 then .unch
      else if changed then rewriteUnaryLoop urs k urs false changed2
      else if preskelWellFormed k then .found k else .unsat
  | ur :: rest =>
      match tryRule k ur with
      | []  => rewriteUnaryLoop urs k rest changed changed2
      | vas =>
          match rewriteUnaryOne k ur vas with
          | none    => .unsat
          | some k' => rewriteUnaryLoop urs k' rest true true

partial def rewriteUnary (k : Preskel) : Ternary Preskel :=
  let urs := (protocol k).unaryrules
  rewriteUnaryLoop urs k urs false false

-- ── Rewrite / doConj / rwt ────────────────────────────────────────────────────

/-- The type of a general rewrite step.
    Mirrors `type Rewrite = Preskel -> (Gen, Env) -> [(Preskel, (Gen, Env))]`. -/
abbrev Rewrite := Preskel → GenEnv → List (Preskel × GenEnv)

-- ── r* atomic rewrite helpers ─────────────────────────────────────────────────

private def rlength (rule : String) (r : Role) (z ht : Term) : Rewrite := fun k ge =>
  let (g, e) := ge
  match indxLookup e ht with
  | none   => assertError s!"In rule {rule}, role length did not get a height"
  | some h =>
      if r.rtrace.length < h.toNat then []
      else
        match strdLookup e z with
        | some s =>
            rDisplace e (addStrand g k r h.toNat) (nstrands k) s
        | none   =>
            let ns := nstrands k
            (strdMatch z ns ge).flatMap fun ge' =>
              let k' := addStrand ge'.1 k r h.toNat
              (k', (k'.gen, ge'.2)) ::
                ((nats ns.toNat).flatMap fun sn =>
                  rDisplace ge'.2 k' ns (Int.ofNat sn))

private def rparam (rule : String) (r : Role) (v : Term) (h : Int) (z t : Term)
    : Rewrite := fun k ge =>
  let (g, e) := ge
  match strdLookup e z with
  | none   =>
      assertError s!"In rule {rule}, parameter predicate {reprStr v} did not get a strand"
  | some s =>
      let inst := strandInst k s
      let t'   := instantiate inst.env v
      if inst.height < h then []
      else if inst.role.rname == r.rname then
        rParam rule k ge t t'
      else
        (rDisplace e (addStrand g k r h.toNat) (nstrands k) s).flatMap fun (k, ge) =>
          rParam rule k ge t t'

private def rprec (rule : String) (n n' : NodeTerm) : Rewrite := fun k ge =>
  let (z, t)   := n
  let (z', t') := n'
  let (g, e)   := ge
  match strdLookup e z, strdLookup e z', indxLookup e t, indxLookup e t' with
  | some s, some s', some i, some i' =>
      if k.kgpOrds.contains ((s, i), (s', i')) then [(k, ge)]
      else if badIndex k s i || badIndex k s' i' then []
      else
        match succOut (strandInst k s) i, prevIn (strandInst k s') i' with
        | some i'', some i''' =>
            (normalizeOrderings true (((s, i''), (s', i''')) :: k.orderings)).map fun orderings' =>
              let k' := newPreskel g k.shared k.insts orderings'
                          k.knon k.kpnon k.kunique k.kuniqgen k.kabsent k.kprecur
                          k.kgenSt k.kconf k.kauth k.kfacts k.kpriority
                          k.operation k.krules k.pprob k.prob k.pov
              (k', (k.gen, e))
        | _, _ => []
  | _, _, _, _ =>
      assertError s!"In rule {rule}, precedence did not get a strand or height"

private def rlnon (rule : String) (t : Term) : Rewrite := fun k ge =>
  let (_, e) := ge
  if !matched e t then assertError s!"In rule {rule}, non did not get a term"
  else
    let t' := instantiate e t
    if k.knon.contains t' then [(k, ge)]
    else if !isAtom t' then []
    else [(mkPreskelAddNon k t', ge)]

private def rlpnon (rule : String) (t : Term) : Rewrite := fun k ge =>
  let (_, e) := ge
  if !matched e t then assertError s!"In rule {rule}, pnon did not get a term"
  else
    let t' := instantiate e t
    if k.kpnon.contains t' then [(k, ge)]
    else if !isAtom t' then []
    else [(mkPreskelAddPnon k t', ge)]

private def rluniq (rule : String) (t : Term) : Rewrite := fun k ge =>
  let (_, e) := ge
  if !matched e t then assertError s!"In rule {rule}, uniq did not get a term"
  else
    let t' := instantiate e t
    if k.kunique.contains t' then [(k, ge)]
    else if !isAtom t' then []
    else [(mkPreskelAddUniq k t', ge)]

private def rlugen (rule : String) (t : Term) : Rewrite := fun k ge =>
  let (_, e) := ge
  if !matched e t then assertError s!"In rule {rule}, ugen did not get a term"
  else
    let t' := instantiate e t
    if k.kuniqgen.contains t' then [(k, ge)]
    else if !isAtom t' then []
    else [(mkPreskelAddUgen k t', ge)]

private def rlgenst (rule : String) (t : Term) : Rewrite := fun k ge =>
  let (_, e) := ge
  if !matched e t then assertError s!"In rule {rule}, genSt did not get a term"
  else
    let t' := instantiate e t
    if k.kgenSt.contains t' then [(k, ge)]
    else [(mkPreskelAddGenSt k t', ge)]

private def rlconf (rule : String) (t : Term) : Rewrite := fun k ge =>
  let (_, e) := ge
  if !matched e t then assertError s!"In rule {rule}, conf did not get a term"
  else
    let t' := instantiate e t
    if k.kconf.contains t' then [(k, ge)]
    else if !isAtom t' then []
    else [(mkPreskelAddConf k t', ge)]

private def rlauth (rule : String) (t : Term) : Rewrite := fun k ge =>
  let (_, e) := ge
  if !matched e t then assertError s!"In rule {rule}, auth did not get a term"
  else
    let t' := instantiate e t
    if k.kauth.contains t' then [(k, ge)]
    else if !isAtom t' then []
    else [(mkPreskelAddAuth k t', ge)]

private def rafact (rule : String) (name : String) (fts : List Term) : Rewrite := fun k ge =>
  let (g, e) := ge
  let fts' := fts.map (rFactLookup rule e)
  let fact  := { name := name, terms := fts' }
  if k.kfacts.contains fact then [(k, ge)]
  else
    let k' := newPreskel g k.shared k.insts k.orderings
                k.knon k.kpnon k.kunique k.kuniqgen k.kabsent k.kprecur
                k.kgenSt k.kconf k.kauth (k.kfacts.eraseDups.cons fact |>.eraseDups) k.kpriority
                k.operation k.krules k.pprob k.prob k.pov
    [(k', (k'.gen, e))]

private def req (rule : String) (x y : Term) : Rewrite := fun k ge =>
  let (g, e) := ge
  if isStrdVar x then
    match strdLookup e x, strdLookup e y with
    | some s, some t =>
        if s == t then [(k, ge)]
        else if s.toNat < k.insts.length && t.toNat < k.insts.length then
          rDisplace e { k with gen := gmerge g k.gen } s t
        else assertError s!"req: indices too large ({s}, {t})"
    | _, _ => assertError s!"In rule {rule}, = did not get a strand"
  else
    let u := if matched e x then instantiate e x else x
    let v := if matched e y then instantiate e y else y
    if u == v then [(k, ge)]
    else rUnify k ge u v

private def rcommpair (rule : String) (n n' : NodeTerm) : Rewrite := fun k ge =>
  match nodeLookup ge.2 n with
  | none   => assertError s!"In rule {rule}, comm-pair did not get two node terms"
  | some p =>
      match dirChMsgOfNode p k with
      | none | some (.Recv, _) => []
      | some (.Send, cm) =>
          match nodeLookup ge.2 n' with
          | none    => assertError s!"In rule {rule}, comm-pair did not get two node terms"
          | some p' =>
              match dirChMsgOfNode p' k with
              | none | some (.Send, _) => []
              | some (.Recv, cm') =>
                  match cm, cm' with
                  | .Plain _, .ChMsg _ _ _ | .ChMsg _ _ _, .Plain _ => []
                  | .Plain m,        .Plain m'          => req rule m m' k ge
                  | .ChMsg ct c m,   .ChMsg ct' c' m'   =>
                      if ct != ct' then [] else
                      (req rule c c' k ge).flatMap fun (k, ge) =>
                        req rule m m' k ge

private def rsamelocn (rule : String) (n n' : NodeTerm) : Rewrite := fun k ge =>
  match nodeLookup ge.2 n, nodeLookup ge.2 n' with
  | some p, some p' =>
      match nodeLocn p k, nodeLocn p' k with
      | [c], [c'] => req rule c c' k ge
      | _,   _    => []
  | _, _ => assertError s!"In rule {rule}, same-locn did not get two node terms"

private def rstateNode (rule : String) (n : NodeTerm) : Rewrite := fun k ge =>
  match nodeLookup ge.2 n with
  | some p => if nodeIsStateNode k p then [(k, ge)] else []
  | none   => assertError s!"In rule {rule}, state-node did not get a node term"

private def runiqAt (rule : String) (t : Term) (n : NodeTerm) : Rewrite := fun k ge =>
  let (_, e) := ge
  let (z, ht) := n
  match matched e t, strdLookup e z, indxLookup e ht with
  | true, some s, some i =>
      let t' := instantiate e t
      if k.korig.any fun (u, ns) => u == t' && ns == [(s, i)] then [(k, ge)]
      else if !isAtom t' then []
      else if i >= (strandInst k s).height then []
      else if checkOrigination t' (strandInst k s).trace i.toNat then
        [(mkPreskelAddUniq k t', ge)]
      else assertError s!"In rule {rule}, uniq-at not at an origination"
  | false, _, _ => assertError s!"In rule {rule}, uniq-at did not get a term"
  | _, none, _  => assertError s!"In rule {rule}, uniq-at did not get a strand"
  | _, _, none  => assertError s!"In rule {rule}, uniq-at did not get an index"

private def rugenAt (rule : String) (t : Term) (n : NodeTerm) : Rewrite := fun k ge =>
  let (_, e) := ge
  let (z, ht) := n
  match matched e t, strdLookup e z, indxLookup e ht with
  | true, some s, some i =>
      let t' := instantiate e t
      if k.kugen.any fun (u, ns) => u == t' && ns == [(s, i)] then [(k, ge)]
      else if !isAtom t' then []
      else if i >= (strandInst k s).height then []
      else if checkGeneration t' (strandInst k s).trace i.toNat then
        [(mkPreskelAddUgen k t', ge)]
      else assertError s!"In rule {rule}, ugen-at not at an origination"
  | false, _, _ => assertError s!"In rule {rule}, ugen-at did not get a term"
  | _, none, _  => assertError s!"In rule {rule}, ugen-at did not get a strand"
  | _, _, none  => assertError s!"In rule {rule}, ugen-at did not get an index"

-- ── Rewrite / rwt / doConj ────────────────────────────────────────────────────

/-- Wrap a `Rewrite` with invariant checking.
    Mirrors `checkRewrite :: Rewrite -> Rewrite`. -/
private def checkRewrite (f : Rewrite) : Rewrite := fun k ge =>
  if checkBoth k ge then
    (f k ge).map fun (k', ge') => (k', checkQuietly k' ge')
  else [(k, localSignal k ge)]

/-- Dispatch general rewrite for each `AForm`.
    Mirrors `rwt :: String -> AForm -> Rewrite`. -/
private partial def rwt (rule : String) : AForm → Rewrite
  | .Length r z ht       => rlength rule r z ht
  | .Param r v i z t     => rparam rule r v i z t
  | .Prec n n'            => rprec rule n n'
  | .Non t                => rlnon rule t
  | .Pnon t               => rlpnon rule t
  | .Uniq t               => rluniq rule t
  | .UniqAt t n           => runiqAt rule t n
  | .Ugen t               => rlugen rule t
  | .UgenAt t n           => rugenAt rule t n
  | .GenStV t             => rlgenst rule t
  | .Conf t               => rlconf rule t
  | .Auth t               => rlauth rule t
  | .AFact name fs        => rafact rule name fs
  | .Equals t t'          => req rule t t'
  | .Component t t'       => fun _ _ =>
        assertError s!"In rule {rule}, component in conclusion with {reprStr t}, {reprStr t'}"
  | .Commpair n n'        => rcommpair rule n n'
  | .SameLocn n n'        => rsamelocn rule n n'
  | .StateNode n          => rstateNode rule n
  | .Trans (t, t')        => rafact rule "trans" [t, t']
  | .LeadsTo n n'         => fun k ge =>
        (rwt rule (.Commpair n n') k ge).flatMap fun (k, ge) =>
        (rwt rule (.Prec n n') k ge).flatMap fun (k, ge) =>
          rwt rule (.StateNode n) k ge

/-- Apply a conjunction of `AForm`s as a `Rewrite`.
    Mirrors `doConj :: String -> [AForm] -> Rewrite`. -/
private partial def doConj (rule : String) : List AForm → Rewrite
  | [],        k, ge => [(k, ge)]
  | f :: fs,   k, ge =>
      (checkRewrite (rwt rule f) k ge).flatMap fun (k, ge) =>
        doConj rule fs k ge

-- ── tryRule / doRewrite / doRewriteOne ────────────────────────────────────────

/-- Apply a rewrite rule at a single environment.
    Mirrors `doRewriteOne :: Preskel -> Rule -> (Gen, Env) -> [Preskel]`. -/
private def fresh (ge : GenEnv) (t : Term) : GenEnv :=
  if isStrdVar t then ge
  else
    let (g', t') := clone ge.1 t
    match termMatch t t' (g', ge.2) with
    | e :: _ => e
    | []     => assertError "Strand.fresh: Cannot match logical variable to clone"

private def doRewriteOne (k : Preskel) (r : Rule) (ge : GenEnv) : List Preskel :=
  r.rlgoal.consq.flatMap fun (evars, cl) =>
    let ge' := evars.foldl fresh ge
    (doConj r.rlname cl k ge').flatMap fun (k, _) =>
      (wellFormedPreskel k).flatMap fun k =>
        (toSkeleton true k).map fun k =>
          { k with krules := (r.rlname :: k.krules).eraseDups }

/-- Apply a rule at all satisfying environments.
    Mirrors `doRewrite :: Preskel -> Rule -> [(Gen, Env)] -> [Preskel]`. -/
def doRewrite (k : Preskel) (r : Rule) (vas : List GenEnv) : List Preskel :=
  vas.flatMap (doRewriteOne k r)

-- ── rewrite / simplify ────────────────────────────────────────────────────────

/-- Maximum rule-application depth.
    Mirrors `rewriteDepthCount :: Int`. -/
def rewriteDepthCount : Int := 2000

/-- Apply all general rules, iterating to fixpoint.
    Mirrors `rewrite :: Preskel -> Maybe [Preskel]`. -/
partial def rewrite (k : Preskel) : Option (List Preskel) :=
  let grules := (protocol k).generalrules
  let nullUnary (k : Preskel) : Option (List Preskel) :=
    if checkNullary k then
      match rewriteUnary k with
      | .unsat   => some []
      | .unch    => none
      | .found k' =>
          if checkNullary k' then some [k'] else some []
    else some []
  let nullUnaryThrough (ks : List Preskel) : List Preskel :=
    ks.flatMap fun k => (nullUnary k).getD [k]
  let rec subiter (k : Preskel) : List Rule → Option (List Preskel)
    | []        => none
    | r :: rs   =>
        match tryRule k r with
        | [] => subiter k rs
        | vas =>
            some (factorIsomorphic
              ((nullUnaryThrough (doRewrite k r vas)).flatMap fun k' =>
                (subiter k' rs).getD [k']))
  let rec iterate (dc : Int) (todos done : List Preskel) (changed : Bool)
      : Option (List Preskel) :=
    match todos with
    | [] =>
        if !changed then none
        else some done
    | k :: rest =>
        if dc <= 0 then some (todos ++ done)
        else
          match subiter k grules with
          | none      => iterate (dc - 1) rest (k :: done) changed
          | some new  =>
              let new' := factorIsomorphic (nullUnaryThrough new)
              iterate dc (mergeIsomorphic new' rest) done true
  match nullUnary k with
  | some []   => some []
  | some [k'] => iterate rewriteDepthCount [k'] [] true
  | none      => iterate rewriteDepthCount [k] [] false
  | some _    => assertError "rewrite: nullUnary returned too many results"

/-- Simplify `k` by applying rewrite rules.
    Mirrors `simplify :: Preskel -> [Preskel]`. -/
def simplify (k : Preskel) : List Preskel :=
  if checkNullary k then
    match rewrite k with
    | none    => [k]
    | some ks => ks
  else []

-- ── applyLeadsTo ─────────────────────────────────────────────────────────────

/-- Apply the leads-to rewrite to `k` for given ordering pairs.
    Mirrors `applyLeadsTo :: Preskel -> [Pair] -> Preskel`. -/
def applyLeadsTo (k : Preskel) (pairs : List Pair) : Preskel :=
  let rn := "(reading leads-to field)"
  let ge := (k.gen, emptyEnv)
  let aforms := pairs.map fun ((s1, i1), (s2, i2)) =>
    AForm.Commpair (strdOfInt s1, indxOfInt i1) (strdOfInt s2, indxOfInt i2)
  match rewriteUnaryOneOnce rn aforms k ge with
  | none    => k
  | some k' => k'

-- ── Display helpers ───────────────────────────────────────────────────────────

def showPreskelSelectively (rolenames : List String) (k : Preskel) : String :=
  let parts := k.insts.filterMap (maybeShowInstance rolenames)
  "(k:" ++ parts.foldr (fun s acc => "\n" ++ s ++ acc) "" ++ ")"

def showPreskelUnselectively (k : Preskel) : String :=
  showPreskelSelectively (k.insts.map (fun i => i.role.rname)) k

-- ── Channel checks ────────────────────────────────────────────────────────────

/-- True when `e` is sent on a confidential channel.
    Mirrors `confCm :: Preskel -> ChMsg -> Bool`. -/
def confCm (k : Preskel) (e : ChMsg) : Bool :=
  match e with
  | .ChMsg ct ch _ => k.kconf.contains ch || ct == .Locn
  | .Plain _       => false

/-- True when `e` is sent on an authenticated channel.
    Mirrors `authCm :: Preskel -> ChMsg -> Bool`. -/
def authCm (k : Preskel) (e : ChMsg) : Bool :=
  match e with
  | .ChMsg ct ch t =>
    k.kauth.contains ch ||
    (ct == .Locn &&
      (k.kgenSt.contains t ||
        (isLocnMsg t && k.kgenSt.contains (locnMsgPayload t))))
  | .Plain _ => false

-- ── verbosePreskelWellFormed ──────────────────────────────────────────────────

/-- Helper: fail with `msg` if `b` is false.
    Mirrors `failwith :: MonadFail m => String -> Bool -> m ()`. -/
private def failwith (msg : String) (b : Bool) : Except String Unit :=
  if b then pure () else throw msg

/-- Well-formedness check that returns a descriptive error on failure.
    Mirrors `verbosePreskelWellFormed :: MonadFail m => Preskel -> m ()`. -/
def verbosePreskelWellFormed (k : Preskel) : Except String Unit := do
  let terms := kterms k
  let vs    := kvars k
  failwith "a variable in non-orig is not in some trace"         (varSubset k.knon terms)
  failwith "a variable in pen-non-orig is not in some trace"     (varSubset k.kpnon terms)
  k.knon.forM    fun t => failwith "non-orig carried"            (terms.all fun t' => !carriedBy t t')
  k.kunique.forM fun t => failwith "uniq-orig not carried"       (terms.any (carriedBy t))
  k.kuniqgen.forM fun t => failwith "uniq-gen does not occur"    (terms.any (constituentModInv t))
  k.kabsent.forM fun (x, y) => do
    failwith "absent: first term not in strand"  (vs.contains x)
    failwith "absent: second term not in strand" (varSubset [y] vs)
  k.kgenSt.forM  fun t => failwith "gen-st not carried"          (terms.any (carriedBy t))
  k.kconf.forM   fun c => failwith "some variable in confidential channel not in some strand"
                            (foldVars (fun b v => b && vs.contains v) true c)
  k.kauth.forM   fun c => failwith "some variable in authenticated channel not in some strand"
                            (foldVars (fun b v => b && vs.contains v) true c)
  failwith "ordered pairs not well formed"                       (wellOrdered k)
  failwith "cycle found in ordered pairs"                        (acyclicOrder k)
  failwith "an inherited unique doesn't originate in its strand" (roleOrigCheck k)
  failwith "an inherited unique gen doesn't generate in its strand" (roleGenCheck k)

-- ── nodePairsOfSkel ──────────────────────────────────────────────────────────

/-- Collect all `(node, node)` pairs witnessing `LeadsTo` facts in `k`.
    Mirrors `nodePairsOfSkel :: Preskel -> [Pair]`. -/
def nodePairsOfSkel (k : Preskel) : List Pair :=
  let (g1, z1) := newVarDefault k.gen "z1" "strd"
  let (g2, z2) := newVarDefault g1   "z2" "strd"
  let (g3, i1) := newVarDefault g2   "i1" "indx"
  let (g4, i2) := newVarDefault g3   "i2" "indx"
  let results  := satisfy (.LeadsTo (z1, i1) (z2, i2)) [] k (g4, emptyEnv)
  (results.mapM fun (ge : GenEnv) =>
    let e := ge.2
    (strdLookup e z1).bind fun s1 =>
    (indxLookup e i1).bind fun idx1 =>
    (strdLookup e z2).bind fun s2 =>
    (indxLookup e i2).map  fun idx2 =>
      ((s1, idx1), (s2, idx2))).getD []

end LeanCPSA.Strand
