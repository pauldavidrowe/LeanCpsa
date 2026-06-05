/-
LeanCPSA.Signature

Port of CPSA.Signature.hs (MITRE cpsa v4.4.8).

Copyright (c) 2026 Paul D. Rowe 

Signatures for algebras

Copyright (c) 2009 The MITRE Corporation

This program is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.
-/

/-
Defines `Sig`, `Operator`, `defaultSig`, `findOper`, and `loadSig`.
-/

import LeanCPSA.Lib.SExpr

namespace LeanCPSA.Signature

open LeanCPSA.Lib (SExpr Pos)

/-- Operators that may appear in an algebra's signature.  Each carries the
    user-facing symbol used in the surface syntax (e.g. `"enc"`, `"hash"`,
    or a custom name).

    Mirrors `data Operator` in `CPSA.Signature`. -/
inductive Operator where
  /-- An "enc"-like operator. -/
  | enc  (sym : String) : Operator
  /-- An "enc"-like operator for use with symmetric keys. -/
  | senc (sym : String) : Operator
  /-- An "enc"-like operator for use with asymmetric keys. -/
  | aenc (sym : String) : Operator
  /-- A digital-signature-like operator. -/
  | sign (sym : String) : Operator
  /-- A "hash"-like operator. -/
  | hash (sym : String) : Operator
  /-- A "cat"-like (tuple) operator.  `arity` is expected to be at least 1;
      `loadSig` enforces this invariant. -/
  | tupl (sym : String) (arity : Nat) : Operator
  deriving Repr, BEq, DecidableEq

/-- The surface symbol associated with an operator. -/
def Operator.sym : Operator → String
  | .enc s | .senc s | .aenc s | .sign s | .hash s | .tupl s _ => s

/-- A signature for an algebra: lists of atom sorts, akey sorts, and
    operators.

    Mirrors `data Sig` in `CPSA.Signature`.  Field names match the Haskell
    source so qualified references like `Sig.atoms s` carry over unchanged. -/
structure Sig where
  /-- Sorts that are not `chan` or `locn`. -/
  atoms : List String
  /-- Asymmetric-key sorts; expected to be a subset of `atoms`. -/
  akeys : List String
  /-- Operators declared in this signature. -/
  opers : List Operator
  deriving Repr, BEq, DecidableEq

/-- The default signature used when no `(lang ...)` form is supplied in a
    CPSA input: five atom sorts (`text`, `data`, `skey`, `akey`, `dev`), one akey
    sort (`akey`), and two operators (`enc`, `hash`). -/
def defaultSig : Sig :=
  { atoms := ["text", "data", "skey", "akey", "dev"],
    akeys := ["akey"],
    opers := [.enc "enc", .hash "hash"] }

/-- Look up an operator by its surface symbol.  Returns the first operator
    in the list whose `sym` matches, or `none`.

    The Haskell source contains two duplicate `Enc` clauses in the middle
    of this function (lines 44–45 of `Signature.hs`); those are dead code
    and are deliberately omitted here. -/
def findOper (sym : String) : List Operator → Option Operator
  | []          => none
  | op :: rest  => if op.sym == sym then some op else findOper sym rest

/-- True when every entry in `akeys` is also in `atoms`.  This is the
    invariant enforced by `loadSig`; `Sig` values constructed by other
    means are not required to satisfy it. -/
def Sig.isValidAkeys (s : Sig) : Bool :=
  s.akeys.all (s.atoms.contains ·)

-- ── loadSig helpers ───────────────────────────────────────────────────────────

-- Remove duplicates, keeping the first occurrence of each element.
private def nubList {α : Type} [BEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

private def badAtomSyms : List String :=
  ["mesg", "name", "chan", "locn", "indx", "pval", "strd"]

private def badOperSyms : List String :=
  ["pubk", "privk", "invk", "ltk", "cat"]

-- Internal tag used while parsing a declaration's type field.
-- Mirrors `data Type` in `Signature.hs`.
private inductive DeclType where
  | atom | akey | enc | senc | aenc | sign | hash
  | tupl (n : Int)

-- Parse the type keyword or `(tuple N)` / `(tupl N)` form.
private def loadType (s : SExpr Pos) : Except String DeclType :=
  match s with
  | .sym pos sym =>
    match sym with
    | "atom" => .ok .atom
    | "akey" => .ok .akey
    | "enc"  => .ok .enc
    | "senc" => .ok .senc
    | "aenc" => .ok .aenc
    | "sign" => .ok .sign
    | "hash" => .ok .hash
    | _      => .error s!"{pos}Bad type in language"
  | .lst _ [.sym _ "tuple", .num _ n] => .ok (.tupl n)
  | .lst _ [.sym _ "tupl",  .num _ n] => .ok (.tupl n)   -- legacy spelling
  | x => .error s!"{x.annotation}Bad type in language"

-- Require an S-expression to be a symbol and return its string.
private def loadSym (s : SExpr Pos) : Except String String :=
  match s with
  | .sym _ sym => .ok sym
  | x          => .error s!"{x.annotation}Bad symbol in language"

-- Fold one declaration `(sym+ type)` into the accumulator triple.
-- Mirrors `loadDecl` in `Signature.hs`.
private def loadDecl
    (acc : List String × List String × List Operator)
    (s   : SExpr Pos)
    : Except String (List String × List String × List Operator) :=
  match s with
  | .lst pos xs =>
    -- Split `xs` into all-but-last (the symbols) and last (the type).
    match xs.reverse with
    | []  | [_] => .error s!"{pos}Malformed declaration in language"
    | typeX :: symXsRev => do
      let typ  ← loadType typeX
      let syms ← symXsRev.reverse.mapM loadSym
      let (ats, aks, ops) := acc
      match typ with
      | .atom   => return (syms ++ ats, aks, ops)
      | .akey   => return (ats, syms ++ aks, ops)
      | .enc    => return (ats, aks, syms.map (.enc  ·) ++ ops)
      | .senc   => return (ats, aks, syms.map (.senc ·) ++ ops)
      | .aenc   => return (ats, aks, syms.map (.aenc ·) ++ ops)
      | .sign   => return (ats, aks, syms.map (.sign ·) ++ ops)
      | .hash   => return (ats, aks, syms.map (.hash ·) ++ ops)
      | .tupl n => return (ats, aks, syms.map (.tupl · n.toNat) ++ ops)
  | x => .error s!"{x.annotation}Malformed declaration in language"

-- Reject atoms whose names are reserved by the CPSA framework.
private def checkAtom (pos : Pos) (atom : String) : Except String Unit :=
  if badAtomSyms.contains atom then
    .error s!"{pos}Bad atom {atom} in language"
  else .ok ()

-- Reject operators whose symbols are reserved, and tuples with arity < 1.
-- Mirrors `badOper` in `Signature.hs`.
private def checkOper (pos : Pos) (op : Operator) : Except String Unit := do
  if badOperSyms.contains op.sym then
    let kind : String := match op with
      | .enc _    => "enc"
      | .senc _   => "senc"
      | .aenc _   => "aenc"
      | .sign _   => "sign"
      | .hash _   => "hash"
      | .tupl _ _ => "tuple"
    throw s!"{pos}Bad {kind} operator {op.sym} in language"
  match op with
  | .tupl _ n => if n < 1 then throw s!"{pos}Bad tuple length {n} in language"
  | _ => pure ()

-- ── loadSig ───────────────────────────────────────────────────────────────────

/-- Parse a list of S-expression declarations (the body of a `(lang ...)` form)
    into a `Sig`.  Starts from `defaultSig` and folds each declaration over it.

    Mirrors `loadSig :: MonadFail m => Pos -> [SExpr Pos] -> m Sig` in
    `Signature.hs`, rendered as `Except String` rather than a typeclass. -/
def loadSig (pos : Pos) (decls : List (SExpr Pos)) : Except String Sig := do
  let initAcc := (defaultSig.atoms, defaultSig.akeys, defaultSig.opers)
  let (ats, aks, ops) ← decls.foldlM loadDecl initAcc
  let sig : Sig := {
    atoms := nubList (aks ++ ats),
    akeys := nubList aks,
    opers := ops
  }
  for atom in sig.atoms do
    checkAtom pos atom
  for op in sig.opers do
    checkOper pos op
  if !sig.isValidAkeys then
    throw s!"{pos}Invalid language because an akey is not in atoms"
  let syms := sig.opers.map (·.sym)
  if syms.length != (nubList syms).length then
    throw s!"{pos}Duplicate operator symbol in language"
  return sig

end LeanCPSA.Signature
