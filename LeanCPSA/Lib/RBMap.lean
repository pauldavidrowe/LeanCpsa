/-
LeanCPSA.Lib.RBMap

A thin shim over `Lean.RBMap` that exposes a `Data.Map`-like API for
the port of CPSA.Algebra and related files.  There is no corresponding
Haskell source file; this module is new infrastructure.

Copyright (c) 2026 Paul D. Rowe

Also defines `RBSet` (= `Lean.RBMap α Unit compare`) to cover the
`Data.Set` surface used in the same files, including `M.keysSet`.

Note: functions in each namespace use `Lean.RBMap.*` calls explicitly
to avoid dot-notation resolving to our own shim definitions.
-/

import Lean.Data.RBMap

namespace LeanCPSA.Lib

-- ── RBSet ────────────────────────────────────────────────────────────────────

/-- Ordered finite set backed by `Lean.RBMap α Unit compare`.
    Mirrors the `Data.Set` interface used in CPSA (qualified as `S`). -/
abbrev RBSet (α : Type) [Ord α] : Type :=
  Lean.RBMap α Unit compare

namespace RBSet

variable {α β : Type} [Ord α]

def empty : RBSet α := Lean.RBMap.empty

def singleton (x : α) : RBSet α :=
  Lean.RBMap.insert Lean.RBMap.empty x ()

def insert (x : α) (s : RBSet α) : RBSet α :=
  Lean.RBMap.insert s x ()

def delete (x : α) (s : RBSet α) : RBSet α :=
  Lean.RBMap.erase s x

def member (x : α) (s : RBSet α) : Bool :=
  Lean.RBMap.contains s x

def notMember (x : α) (s : RBSet α) : Bool :=
  !Lean.RBMap.contains s x

/-- Elements as a list in ascending order.  Mirrors `S.toList` and `S.elems`. -/
def toList (s : RBSet α) : List α :=
  (Lean.RBMap.toList s).map Prod.fst

def fromList (xs : List α) : RBSet α :=
  xs.foldl (fun acc x => Lean.RBMap.insert acc x ()) Lean.RBMap.empty

/-- Right fold over elements in ascending order.
    Mirrors `S.fold :: (a -> b -> b) -> b -> Set a -> b`. -/
def fold (f : α → β → β) (z : β) (s : RBSet α) : β :=
  ((Lean.RBMap.toList s).map Prod.fst).foldr f z

def unions (ss : List (RBSet α)) : RBSet α :=
  ss.foldl
    (fun acc s => Lean.RBMap.fold (fun a x _ => Lean.RBMap.insert a x ()) acc s)
    Lean.RBMap.empty

def map [Ord β] (f : α → β) (s : RBSet α) : RBSet β :=
  Lean.RBMap.fold
    (fun acc x _ => Lean.RBMap.insert acc (f x) ())
    Lean.RBMap.empty s

def filter (f : α → Bool) (s : RBSet α) : RBSet α :=
  Lean.RBMap.fold
    (fun acc x _ => if f x then Lean.RBMap.insert acc x () else acc)
    Lean.RBMap.empty s

/-- Elements as a list in ascending order.  Same as `toList`.
    Mirrors `S.elems`. -/
def elems (s : RBSet α) : List α :=
  (Lean.RBMap.toList s).map Prod.fst

end RBSet

-- ── RBMap ────────────────────────────────────────────────────────────────────

/-- Ordered finite map from `α` to `β`, backed by `Lean.RBMap α β compare`.
    Mirrors the `Data.Map` interface used in CPSA (qualified as `M`). -/
abbrev RBMap (α β : Type) [Ord α] : Type :=
  Lean.RBMap α β compare

namespace RBMap

variable {α β γ : Type} [Ord α]

def empty : RBMap α β := Lean.RBMap.empty

def singleton (k : α) (v : β) : RBMap α β :=
  Lean.RBMap.insert Lean.RBMap.empty k v

/-- True when the map has no entries.  Mirrors `M.null`. -/
def null (m : RBMap α β) : Bool :=
  Lean.RBMap.isEmpty m

def size (m : RBMap α β) : Nat :=
  Lean.RBMap.size m

def member (k : α) (m : RBMap α β) : Bool :=
  Lean.RBMap.contains m k

def notMember (k : α) (m : RBMap α β) : Bool :=
  !Lean.RBMap.contains m k

/-- Look up a key.  Mirrors `M.lookup`. -/
def lookup (k : α) (m : RBMap α β) : Option β :=
  Lean.RBMap.find? m k

/-- Look up with a default.  Mirrors `M.findWithDefault`. -/
def findWithDefault (dflt : β) (k : α) (m : RBMap α β) : β :=
  Lean.RBMap.findD m k dflt

/-- Unsafe lookup; panics if the key is absent.  Mirrors `m M.! k`. -/
def index [Inhabited β] (m : RBMap α β) (k : α) : β :=
  match Lean.RBMap.find? m k with
  | some v => v
  | none   => panic! "RBMap.index: key not found"

def insert (k : α) (v : β) (m : RBMap α β) : RBMap α β :=
  Lean.RBMap.insert m k v

def delete (k : α) (m : RBMap α β) : RBMap α β :=
  Lean.RBMap.erase m k

/-- Apply `f` to the value at `k` (or `none` if absent); insert or erase
    based on the result.  Mirrors `M.alter`. -/
def alter (f : Option β → Option β) (k : α) (m : RBMap α β) : RBMap α β :=
  match f (Lean.RBMap.find? m k) with
  | none   => Lean.RBMap.erase m k
  | some v => Lean.RBMap.insert m k v

/-- Left-biased union: when a key appears in both maps, the value from
    the left map is kept.  Mirrors `M.union`. -/
def union (m1 m2 : RBMap α β) : RBMap α β :=
  Lean.RBMap.fold
    (fun acc k v => if Lean.RBMap.contains acc k then acc else Lean.RBMap.insert acc k v)
    m1 m2

/-- Intersection keeping values from the left map.
    Mirrors `M.intersection`. -/
def intersection (m1 : RBMap α β) (m2 : RBMap α γ) : RBMap α β :=
  Lean.RBMap.fold
    (fun acc k v => if Lean.RBMap.contains m2 k then Lean.RBMap.insert acc k v else acc)
    Lean.RBMap.empty m1

/-- Map a function over all values.  Mirrors `M.map`. -/
def map (f : β → γ) (m : RBMap α β) : RBMap α γ :=
  Lean.RBMap.fold
    (fun acc k v => Lean.RBMap.insert acc k (f v))
    Lean.RBMap.empty m

/-- Map a function over key-value pairs.  Mirrors `M.mapWithKey`. -/
def mapWithKey (f : α → β → γ) (m : RBMap α β) : RBMap α γ :=
  Lean.RBMap.fold
    (fun acc k v => Lean.RBMap.insert acc k (f k v))
    Lean.RBMap.empty m

/-- Keep entries whose value satisfies `f`.  Mirrors `M.filter`. -/
def filter (f : β → Bool) (m : RBMap α β) : RBMap α β :=
  Lean.RBMap.fold
    (fun acc k v => if f v then Lean.RBMap.insert acc k v else acc)
    Lean.RBMap.empty m

/-- Keep entries whose key and value satisfy `f`.  Mirrors `M.filterWithKey`. -/
def filterWithKey (f : α → β → Bool) (m : RBMap α β) : RBMap α β :=
  Lean.RBMap.fold
    (fun acc k v => if f k v then Lean.RBMap.insert acc k v else acc)
    Lean.RBMap.empty m

/-- Right fold over values in ascending key order.  Mirrors `M.foldr`. -/
def foldr (f : β → γ → γ) (z : γ) (m : RBMap α β) : γ :=
  (Lean.RBMap.toList m).foldr (fun (_, v) acc => f v acc) z

/-- Left fold over values in ascending key order.  Mirrors `M.foldl`. -/
def foldl (f : γ → β → γ) (z : γ) (m : RBMap α β) : γ :=
  Lean.RBMap.fold (fun acc _ v => f acc v) z m

/-- Right fold over key-value pairs in ascending key order.
    Mirrors `M.foldrWithKey`. -/
def foldrWithKey (f : α → β → γ → γ) (z : γ) (m : RBMap α β) : γ :=
  (Lean.RBMap.toList m).foldr (fun (k, v) acc => f k v acc) z

/-- Left fold over key-value pairs in ascending key order.
    Mirrors `M.foldlWithKey`. -/
def foldlWithKey (f : γ → α → β → γ) (z : γ) (m : RBMap α β) : γ :=
  Lean.RBMap.fold (fun acc k v => f acc k v) z m

/-- Convert to an association list in ascending key order.
    Mirrors both `M.toList` and `M.assocs`. -/
def toList (m : RBMap α β) : List (α × β) :=
  Lean.RBMap.toList m

/-- Build a map from an association list (last writer wins for duplicate keys).
    Mirrors `M.fromList`. -/
def fromList (pairs : List (α × β)) : RBMap α β :=
  pairs.foldl (fun acc (k, v) => Lean.RBMap.insert acc k v) Lean.RBMap.empty

/-- The keys in ascending order.  Mirrors `M.keys`. -/
def keys (m : RBMap α β) : List α :=
  (Lean.RBMap.toList m).map Prod.fst

/-- The values in ascending key order.  Mirrors `M.elems`. -/
def elems (m : RBMap α β) : List β :=
  (Lean.RBMap.toList m).map Prod.snd

/-- Association list in ascending key order.  Mirrors `M.assocs`. -/
def assocs (m : RBMap α β) : List (α × β) :=
  Lean.RBMap.toList m

/-- Partition entries by a predicate on values.  Mirrors `M.partition`. -/
def partition (f : β → Bool) (m : RBMap α β) : RBMap α β × RBMap α β :=
  Lean.RBMap.fold
    (fun (yes, no) k v =>
      if f v then (Lean.RBMap.insert yes k v, no)
             else (yes, Lean.RBMap.insert no k v))
    (Lean.RBMap.empty, Lean.RBMap.empty) m

/-- Partition entries by a predicate on key-value pairs.
    Mirrors `M.partitionWithKey`. -/
def partitionWithKey (f : α → β → Bool) (m : RBMap α β) : RBMap α β × RBMap α β :=
  Lean.RBMap.fold
    (fun (yes, no) k v =>
      if f k v then (Lean.RBMap.insert yes k v, no)
               else (yes, Lean.RBMap.insert no k v))
    (Lean.RBMap.empty, Lean.RBMap.empty) m

/-- The set of keys.  Mirrors `M.keysSet`. -/
def keysSet (m : RBMap α β) : RBSet α :=
  Lean.RBMap.fold (fun acc k _ => Lean.RBMap.insert acc k ()) Lean.RBMap.empty m

def reprMap [Repr α] [Repr β] (m : RBMap α β) : String :=
  let pairs := Lean.RBMap.toList m
  let pairStrs := pairs.map (fun (k, v) => s!"{repr k} ↦ {repr v}")
  "{" ++ String.intercalate ", " pairStrs ++ "}"

instance [Repr α] [Repr β] : Repr (RBMap α β) where
  reprPrec m _ := reprMap m

end RBMap

end LeanCPSA.Lib
