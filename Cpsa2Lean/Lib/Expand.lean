/-
Cpsa2Lean.Lib.Expand

Port of CPSA.Lib.Expand (MITRE cpsa v4.4.8).

Copyright (c) 2026 Paul D. Rowe

Expand macros using definitions in the input.

Copyright (c) 2009 The MITRE Corporation

This program is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.
-/

/-
Reads all S-expressions from a handle and expands defmacro/include forms.
-/

import Cpsa2Lean.Lib.SExpr

namespace Cpsa2Lean.Lib

open Cpsa2Lean.Lib  -- brings SExpr, Pos, PosHandle, load into scope

-- ── Constants ─────────────────────────────────────────────────────────────────

/-- Include nesting depth bound.  Mirrors `bound = 16`. -/
def bound : Int := 16

/-- Macro expansion loop limit.  Mirrors `limit = 1000`. -/
private def expansionLimit : Int := 1000

-- ── Macro structure ───────────────────────────────────────────────────────────

/-- A macro definition: name, formal args, and body.
    Mirrors `data Macro = Macro { name, args, body }`. -/
structure Macro where
  name : String
  args : List String
  body : SExpr Pos

def getMacroName (m : Macro) : String      := m.name
def getMacroArgs (m : Macro) : List String := m.args
def getMacroBody (m : Macro) : SExpr Pos   := m.body

-- ── readSExprs ────────────────────────────────────────────────────────────────

/-- Read all S-expressions from a handle until EOF.
    Mirrors `readSExprs :: PosHandle -> IO [SExpr Pos]`. -/
private partial def readSExprsAux (ph : PosHandle) (acc : List (SExpr Pos))
    : IO (List (SExpr Pos)) := do
  match ← load ph with
  | none   => return acc.reverse
  | some x => readSExprsAux ph (x :: acc)

def readSExprs (ph : PosHandle) : IO (List (SExpr Pos)) :=
  readSExprsAux ph []

-- ── Pure helpers ──────────────────────────────────────────────────────────────

/-- Extract a symbol string from an S-expression.
    Mirrors `symbol :: MonadFail m => SExpr Pos -> m String`. -/
private def symbol (x : SExpr Pos) : Except String String :=
  match x with
  | .sym _ s => .ok s
  | _        => .error s!"{x.annotation}Expecting a symbol"

/-- Parse a defmacro form.
    Mirrors `defmacro :: MonadFail m => Pos -> [SExpr Pos] -> m Macro`. -/
private def defmacro (pos : Pos) (xs : List (SExpr Pos)) : Except String Macro :=
  match xs with
  | [.lst _ (nameExpr :: argExprs), body] => do
      let n    ← symbol nameExpr
      let args ← argExprs.mapM symbol
      .ok { name := n, args, body }
  | _ => .error s!"{pos}Malformed macro"

/-- Substitute macro arguments into a body.
    Mirrors `subst :: [(String, SExpr Pos)] -> SExpr Pos -> SExpr Pos`. -/
private partial def subst (env : List (String × SExpr Pos)) : SExpr Pos → SExpr Pos
  | (.sym ann sym) =>
      match env.lookup sym with
      | some replacement => replacement
      | none             => .sym ann sym
  | (.lst ann xs) => .lst ann (xs.map (subst env))
  | x             => x

/-- Apply a macro to a list of arguments.
    Mirrors `apply :: Macro -> [SExpr Pos] -> SExpr Pos`. -/
private def applyMacro (mac : Macro) (xs : List (SExpr Pos)) : SExpr Pos :=
  subst (mac.args.zip xs) mac.body

/-- Splice ^ forms in a list.
    Mirrors `splice :: [SExpr Pos] -> [SExpr Pos]`.
    (^xs) splices xs into the surrounding list. -/
private def splice : List (SExpr Pos) → List (SExpr Pos)
  | []                                => []
  | .lst _ (.sym _ "^" :: xs) :: rest => xs ++ splice rest
  | x                         :: rest => x  :: splice rest

/-- Try to expand one macro call.  Returns none if no matching macro.
    Mirrors `macroExpand1`. -/
private def macroExpand1 (macs : List Macro) (pos : Pos) (sym : String)
    (xs : List (SExpr Pos)) : Except String (Option (SExpr Pos)) :=
  match macs.find? (fun m => m.name == sym) with
  | none     => .ok none
  | some mac =>
      if mac.args.length == xs.length then
        .ok (some (applyMacro mac xs))
      else
        .error s!"{pos}Expected argument count for macro {sym} is {mac.args.length}"

/-- Expand one S-expression, up to `lim` macro applications.
    Mirrors `macroExpand`.  Must be `partial` (termination not provable). -/
private partial def macroExpand (macs : List Macro) (pos : Pos) (lim : Int)
    (sexpr : SExpr Pos) : Except String (SExpr Pos) :=
  if lim <= 0 then
    .error s!"{pos}Expansion limit exceeded"
  else
  match sexpr with
  | .lst _ (.sym _ sym :: xs) => do
      match ← macroExpand1 macs pos sym xs with
      | none        => .ok sexpr
      | some sexpr' => macroExpand macs pos (lim - 1) sexpr'
  | _ => .ok sexpr

/-- Expand all macros in an S-expression tree.
    Mirrors `expandAll`.  Must be `partial` (recursive through macroExpand). -/
private partial def expandAll (macs : List Macro) (sexpr : SExpr Pos)
    : Except String (SExpr Pos) := do
  let sexpr ← macroExpand macs sexpr.annotation expansionLimit sexpr
  match sexpr with
  | .lst ann xs =>
      let xs' ← xs.mapM (expandAll macs)
      .ok (.lst ann (splice xs'))
  | _ => .ok sexpr

/-- Lift an `Except String` result into IO, throwing on error. -/
private def exceptToIO {α : Type} (e : Except String α) : IO α :=
  match e with
  | .ok x    => pure x
  | .error s => throw (IO.userError s)

-- ── IO functions: expandSExpr, expandInclude, expand ─────────────────────────

mutual

/-- Process one S-expression: defmacro, include, or expand.
    Mirrors `expandSExpr`.  Must be `partial`. -/
partial def expandSExpr (bnd : Int) (state : List Macro × List (SExpr Pos))
    (sexpr : SExpr Pos) : IO (List Macro × List (SExpr Pos)) := do
  let (macs, sexprs) := state
  match sexpr with
  | .lst _ (.sym _ "defmacro" :: xs) =>
      let mac ← exceptToIO (defmacro sexpr.annotation xs)
      return (mac :: macs, sexprs)
  | .lst _ [.sym _ "include", .str _ file] =>
      expandInclude bnd state sexpr.annotation file
  | _ =>
      let sexpr' ← exceptToIO (expandAll macs sexpr)
      return (macs, sexpr' :: sexprs)

/-- Handle an include form by reading and expanding the named file.
    Mirrors `include`.  Must be `partial`. -/
partial def expandInclude (bnd : Int) (state : List Macro × List (SExpr Pos))
    (pos : Pos) (file : String) : IO (List Macro × List (SExpr Pos)) := do
  if bnd <= 0 then
    throw (IO.userError s!"{pos}Include depth exceeded with file {file}")
  let h ← try
    IO.FS.Handle.mk file .read
  catch _ =>
    throw (IO.userError s!"{pos}File {file}: could not open")
  let ph  ← posHandle file (IO.FS.Stream.ofHandle h)
  let xs  ← readSExprs ph
  xs.foldlM (expandSExpr (bnd - 1)) state

end

/-- Expand macros and includes in a list of S-expressions.
    Mirrors `expand :: [SExpr Pos] -> IO [SExpr Pos]`. -/
def expand (sexprs : List (SExpr Pos)) : IO (List (SExpr Pos)) := do
  let (_, result) ← sexprs.foldlM (expandSExpr bound) ([], [])
  return result.reverse

end Cpsa2Lean.Lib
