/-
LeanCPSA.Lib.Utilities

Port of CPSA.Lib.Utilities (MITRE cpsa v4.4.8).

Copyright (c) 2026 Paul D. Rowe 

Contains generic list functions and a function that determines if a
graph has a cycle.

Copyright (c) 2009 The MITRE Corporation

This program is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.
-/

/-

`seqList` is omitted — Lean is strict, so it would be the identity.
`assert` maps `MonadFail` to `Except String`.
`isAcyclic` and `dfs` use `Lean.RBTree` in place of `Data.Set`.
-/

import Lean.Data.RBMap

namespace LeanCPSA.Lib

-- ── List set operations ───────────────────────────────────────────────────────

/-- Prepend `x` to `xs` only if it is not already a member. -/
def adjoin {α : Type} [BEq α] (x : α) (xs : List α) : List α :=
  if xs.contains x then xs else x :: xs

/-- True when every element of `as` appears in `bs`. -/
def subset {α : Type} [BEq α] (as bs : List α) : Bool :=
  as.all (bs.contains ·)

/-- List union: elements of `as` not already in `bs`, prepended to `bs`. -/
def union {α : Type} [BEq α] : List α → List α → List α
  | [],      bs => bs
  | a :: as, bs => if bs.contains a then union as bs else a :: union as bs

/-- List set-minus: elements of `as` that do not appear in `bs`. -/
def setMinus {α : Type} [BEq α] : List α → List α → List α
  | [],      _ => []
  | a :: as, bs => if bs.contains a then setMinus as bs else a :: setMinus as bs

-- ── Index operations ──────────────────────────────────────────────────────────

/-- Delete the element at index `n` (0-based).
    Returns the list unchanged if the index is out of range. -/
def deleteNth {α : Type} (n : Nat) : List α → List α
  | []      => []
  | x :: xs => if n == 0 then xs else x :: deleteNth (n - 1) xs

/-- Replace the element at index `n` (0-based) with `z`.
    Returns the list unchanged if the index is out of range. -/
def replaceNth {α : Type} (z : α) (n : Nat) : List α → List α
  | []      => []
  | x :: xs => if n == 0 then z :: xs else x :: replaceNth z (n - 1) xs

/-- Safe index lookup (0-based).  Mirrors `maybeNth` in `Utilities.hs`. -/
def maybeNth {α : Type} (xs : List α) (i : Nat) : Option α :=
  match i, xs with
  | 0, x :: _ => some x
  | n + 1, _ :: rest => maybeNth rest n
  | _, _ => none

/- Enumerate a list as `[(0,x0),(1,x1),...]` -/
def enum {α : Type} (xs : List α) : List (Nat × α) :=
  let rec loop (i : Nat) (acc : List (Nat × α)) (ys : List α) :=
    match ys with
    | [] => acc
    | y :: ys' => loop (i+1) ((i, y) :: acc) ys'
  loop 0 [] xs |> List.reverse

/- Provide List-style indexed accessors used in the original CPSA code -/

/-- Maximum of a non-empty list, or `none` for the empty list. -/
def listMax {α : Type} [Max α] : List α → Option α
  | []      => none
  | [a]     => some a
  | a :: rest =>
    match listMax rest with
    | none   => some a
    | some m => some (max a m)

/-- Delete the first occurrence of `a` in `l`.
    Returns `none` if `a` is not present. -/
def deleteWhenPresent {α : Type} [BEq α] (a : α) (l : List α) : Option (List α) :=
  let rec collect (rest passed : List α) : Option (List α) :=
    match rest with
    | []      => none
    | b :: bs =>
      if a == b then some (passed.reverse ++ bs)
      else collect bs (b :: passed)
  collect l []

/-- Apply a binary function to corresponding pairs of two lists,
    discarding excess elements from the longer list.
    Equivalent to Haskell's `zipWith`. -/
def mapTwo {α β γ : Type} (f : α → β → γ) (as : List α) (bs : List β) : List γ :=
  (as.zip bs).map (fun (a, b) => f a b)

/-- Right-fold a binary function over corresponding pairs of two lists. -/
def foldrTwo {α β γ : Type} (f : α → β → γ → γ) (seed : γ) (as : List α) (bs : List β) : γ :=
  (as.zip bs).foldr (fun (a, b) c => f a b c) seed

/-- Return the first `some` value in a list of options, or `none`. -/
def someOfList {α : Type} : List (Option α) → Option α
  | []           => none
  | none :: rest => someOfList rest
  | some v :: _  => some v

/-- The list `[0, 1, ..., n-1]`. -/
def nats (n : Nat) : List Nat :=
  List.range n

-- ── Assertion utilities ───────────────────────────────────────────────────────

/-- Assert a predicate, returning `Except.error` on failure.
    Mirrors `assert :: MonadFail m => (a -> Bool) -> a -> m a`. -/
def assert {α : Type} (pred : α → Bool) (x : α) : Except String α :=
  if pred x then .ok x else .error "assertion failed"

/-- Raise a panic with an `[ASSERT FAILED]` prefix.
    Use instead of `assert` when the failure indicates a program bug.
    Requires `[Inhabited α]` because Lean's `panic!` needs a default value
    (unlike Haskell's `error`, which is unconstrained). -/
def assertError {α : Type} [Inhabited α] (s : String) : α :=
  panic! s!"[ASSERT FAILED] {s}"

-- ── Cycle detection ───────────────────────────────────────────────────────────

-- `dfs` computes a DFS postorder numbering of a directed graph.
-- The `seen` set is represented as `RBMap α Unit cmp` (an ordered set using
-- the `Unit`-valued map idiom, since `Lean.RBTree` = `RBMap α Unit cmp` but
-- requires a separate import).
private partial def dfsStep {α : Type} (cmp : α → α → Ordering)
    (adj : α → List α)
    (state : Nat × List (α × Nat) × Lean.RBMap α Unit cmp)
    (node : α)
    : Nat × List (α × Nat) × Lean.RBMap α Unit cmp :=
  let (num, alist, seen) := state
  if seen.contains node then state
  else
    let seen' := seen.insert node ()
    let (num', alist', seen'') := (adj node).foldl (dfsStep cmp adj) (num, alist, seen')
    (num' + 1, (node, num') :: alist', seen'')

/-- Compute a DFS postorder numbering of `nodes` under adjacency `adj`.
    Only nodes reachable from `nodes` appear in the result.

    Mirrors `dfs :: Ord a => (a -> [a]) -> [a] -> [(a, Int)]`. -/
def dfs {α : Type} (cmp : α → α → Ordering) (adj : α → List α) (nodes : List α)
    : List (α × Nat) :=
  let (_, alist, _) := nodes.foldl (dfsStep cmp adj) (0, [], Lean.RBMap.empty)
  alist

/-- True when `edge` is a back edge in the DFS numbering `alist`.
    An edge `(node, node')` is a back edge when `node`'s postorder number is ≥
    `node'`'s, or when either node was not visited.

    Mirrors `backEdge :: Eq a => [(a, Int)] -> (a, a) -> Bool`. -/
def backEdge {α : Type} [BEq α] (alist : List (α × Nat)) (edge : α × α) : Bool :=
  let (node, node') := edge
  match List.lookup node alist, List.lookup node' alist with
  | some n, some n' => n >= n'
  | _,      _       => true

/-- True when the directed graph defined by `adj` has no cycle reachable from
    `nodes`.

    Mirrors `isAcyclic :: Ord a => (a -> [a]) -> [a] -> Bool`. -/
def isAcyclic {α : Type} [BEq α] (cmp : α → α → Ordering)
    (adj : α → List α)
    (nodes : List α)
    : Bool :=
  -- edges = [(dst, src) | src <- nodes, dst <- adj src]
  let edges := nodes.flatMap fun src => (adj src).map fun dst => (dst, src)
  -- start = nodes with in-degree zero (not the destination of any edge)
  let destinations := edges.map Prod.fst
  let start := destinations.foldl (fun ns dst => ns.erase dst) nodes
  let numbering := dfs cmp adj start
  edges.all fun e => !backEdge numbering e

end LeanCPSA.Lib

/- Global List accessors that mirror the original CPSA code's use of
  dot-projections like `xs.get?` and `xs.get!`. These delegate to the
  safe `maybeNth` helper in `LeanCPSA.Lib`. -/
namespace List

def get? {α : Type} (xs : List α) (i : Nat) : Option α :=
  LeanCPSA.Lib.maybeNth xs i

def get! {α : Type} [Inhabited α] (xs : List α) (i : Nat) : α :=
  match get? xs i with
  | some a => a
  | none   => panic! "List.get!: index out of bounds"

end List
