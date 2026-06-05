/-
LeanCPSA.Operation

Port of CPSA.Operation (MITRE cpsa).

Copyright (c) 2026 Paul D. Rowe

The operation datastructure

Copyright (c) 2009 The MITRE Corporation

This program is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.
-/

/-
Defines the data structures that track how preskeletons are created
during bundle analysis.

`Set CMT` from `Data.Set` is replaced by `RBSet CMT`.
`deriving Show` is dropped: `Term`, `Subst`, and `CMT` have no `Repr`
instance, so the containing types cannot derive `Repr` either.
`Direction` is the sole exception.
-/

import LeanCPSA.Algebra
import LeanCPSA.Channel
import LeanCPSA.Lib.RBMap

namespace LeanCPSA.Operation

open LeanCPSA.Algebra (Term Subst)
open LeanCPSA.Channel (CMT)
open LeanCPSA.Lib (RBSet)

-- ── Basic type aliases ────────────────────────────────────────────────────────

/-- Strand identifier.  Mirrors `type Sid = Int`. -/
abbrev Sid := Int

/-- A node is a (strand-id, position) pair.  Mirrors `type Node = (Sid, Int)`. -/
abbrev Node := Sid × Int

/-- An ordering constraint between two nodes.  Mirrors `type Pair = (Node, Node)`. -/
abbrev Pair := Node × Node

/-- Lexicographic ordering on `Node = Sid × Int`. -/
instance : Ord Node where
  compare n m :=
    match compare n.1 m.1 with
    | .eq => compare n.2 m.2
    | o   => o

/-- Lexicographic ordering on `Pair = Node × Node`. -/
instance : Ord Pair where
  compare p q :=
    match compare p.1 q.1 with
    | .eq => compare p.2 q.2
    | o   => o

-- ── Direction ─────────────────────────────────────────────────────────────────

/-- The kind of term that triggered the creation of a preskeleton.
    Mirrors `data Direction = Encryption | Nonce | Channel`. -/
inductive Direction where
  | Encryption : Direction
  | Nonce      : Direction
  | Channel    : Direction
  deriving Repr

-- ── Cause ─────────────────────────────────────────────────────────────────────

/-- Tracks why a preskeleton was created.
    Mirrors `data Cause = Cause Direction Node CMT (Set CMT)`. -/
structure Cause where
  direction : Direction
  node      : Node
  cmt       : CMT
  cmts      : RBSet CMT
  deriving Repr

-- ── Method ────────────────────────────────────────────────────────────────────

/-- The method used to minimise a preskeleton.
    Mirrors `data Method = Deleted Node | Weakened Pair | ...`. -/
inductive Method where
  | Deleted   : Node → Method
  | Weakened  : Pair → Method
  | Separated : Term → Method
  | Forgot    : Term → Method
  deriving Repr

-- ── Operation ────────────────────────────────────────────────────────────────

/-- The operation that generated a preskeleton.
    Mirrors `data Operation = New | Contracted ... | ...`. -/
inductive Operation where
  | New           : Operation
  | Contracted    : List Sid → Subst  → Cause → Operation
  | Displaced     : List Sid → Int → Int → String → Int → Cause → Operation
  | AddedStrand   : List Sid → String → Int → Cause → Operation
  | AddedListener : List Sid → Term   → Cause → Operation
  | AddedAbsence  : List Sid → Term   → Term  → Cause → Operation
  | Generalized   : List Sid → Method → Operation
  | Collapsed     : List Sid → Int → Int → Operation
  | AppliedRules  : List Sid → Operation
  deriving Repr

-- ── Operations on strand maps ─────────────────────────────────────────────────

/-- Extract the strand map embedded in an operation.
    Mirrors `getStrandMap :: Operation -> [Sid]`. -/
def getStrandMap : Operation → List Sid
  | .New                        => []
  | .Contracted    sm _ _       => sm
  | .Displaced     sm _ _ _ _ _ => sm
  | .AddedStrand   sm _ _ _     => sm
  | .AddedListener sm _ _       => sm
  | .AddedAbsence  sm _ _ _     => sm
  | .Generalized   sm _         => sm
  | .Collapsed     sm _ _       => sm
  | .AppliedRules  sm           => sm

/-- Replace the strand map in an operation.
    Mirrors `addStrandMap :: [Sid] -> Operation -> Operation`. -/
def addStrandMap (sm : List Sid) : Operation → Operation
  | .New                           => .New
  | .Contracted    _ s c           => .Contracted    sm s c
  | .Displaced     _ n1 n2 str n3 c => .Displaced   sm n1 n2 str n3 c
  | .AddedStrand   _ str n c       => .AddedStrand   sm str n c
  | .AddedListener _ t c           => .AddedListener sm t c
  | .AddedAbsence  _ t1 t2 c       => .AddedAbsence  sm t1 t2 c
  | .Generalized   _ m             => .Generalized   sm m
  | .Collapsed     _ n1 n2         => .Collapsed     sm n1 n2
  | .AppliedRules  _               => .AppliedRules  sm

end LeanCPSA.Operation
