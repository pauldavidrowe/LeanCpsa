/-
Cpsa2Lean.Lib.SExpr

Port of CPSA.Lib.SExpr (MITRE cpsa v4.4.8).

Copyright (c) 2026 Paul D. Rowe 

This module provides a data structure for S-expressions, and a reader.
The reader records the position in the file at which items that make
up the list are located.

The S-expressions used are restricted so that most dialects of Lisp
can read them, and characters within symbols and strings never need
quoting. Every list is proper. An atom is either a symbol, an integer,
or a string. The characters that make up a symbol are the letters, the
digits, and these special characters.

Copyright (c) 2009 The MITRE Corporation

This program is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.
-/

/-
S-expressions are restricted so that most Lisp dialects can read them.
Every list is proper.  An atom is a symbol, an integer, or a quoted string.
Symbol characters are letters, digits, and: + - * / < = > ! ? : $ % _ & ~ ^
A symbol may not begin with a digit or a sign followed by a digit.
Comments begin with `;` and run to end of line.
-/

namespace Cpsa2Lean.Lib

-- ── SExpr data type ───────────────────────────────────────────────────────────

/-- An S-expression annotated by values of type `α`. -/
inductive SExpr (α : Type) where
  | sym (ann : α) (s  : String)          : SExpr α  -- symbol
  | str (ann : α) (s  : String)          : SExpr α  -- quoted string
  | num (ann : α) (n  : Int)             : SExpr α  -- integer
  | lst (ann : α) (xs : List (SExpr α))  : SExpr α  -- proper list
  deriving Repr

namespace SExpr

variable {α : Type}

/-- Extract the annotation from any constructor. -/
def getPos : SExpr α → α
  | .sym a _ | .str a _ | .num a _ | .lst a _ => a

/-- Alias for `getPos`. -/
def annotation : SExpr α → α := getPos

-- ── Equality (ignores annotations) ────────────────────────────────────────────

-- `BEq (List (SExpr α))` depends on `BEq (SExpr α)`, so we bootstrap with
-- a mutual pair of functions and then register the instance.
mutual
  private partial def beqSExpr (x y : SExpr α) : Bool :=
    match x, y with
    | .sym _ s,  .sym _ s'  => s == s'
    | .str _ s,  .str _ s'  => s == s'
    | .num _ n,  .num _ n'  => n == n'
    | .lst _ xs, .lst _ xs' => beqList xs xs'
    | _,         _          => false

  private partial def beqList (xs ys : List (SExpr α)) : Bool :=
    match xs, ys with
    | [],      []      => true
    | x :: xs, y :: ys => beqSExpr x y && beqList xs ys
    | _,       _       => false
end

instance : BEq (SExpr α) := ⟨beqSExpr⟩

-- ── Ordering (ignores annotations): sym < str < num < lst ─────────────────────

mutual
  private partial def cmpSExpr (x y : SExpr α) : Ordering :=
    match x, y with
    | .sym _ s,  .sym _ s'  => compare s s'
    | .sym _ _,  .str _ _   => .lt
    | .sym _ _,  .num _ _   => .lt
    | .sym _ _,  .lst _ _   => .lt
    | .str _ _,  .sym _ _   => .gt
    | .str _ s,  .str _ s'  => compare s s'
    | .str _ _,  .num _ _   => .lt
    | .str _ _,  .lst _ _   => .lt
    | .num _ _,  .sym _ _   => .gt
    | .num _ _,  .str _ _   => .gt
    | .num _ n,  .num _ n'  => compare n n'
    | .num _ _,  .lst _ _   => .lt
    | .lst _ _,  .sym _ _   => .gt
    | .lst _ _,  .str _ _   => .gt
    | .lst _ _,  .num _ _   => .gt
    | .lst _ xs, .lst _ xs' => cmpList xs xs'

  private partial def cmpList (xs ys : List (SExpr α)) : Ordering :=
    match xs, ys with
    | [],      []      => .eq
    | [],      _       => .lt
    | _,       []      => .gt
    | x :: xs, y :: ys =>
      match cmpSExpr x y with
      | .eq => cmpList xs ys
      | o   => o
end

instance : Ord (SExpr α) := ⟨cmpSExpr⟩

-- ── String representation (no line breaks) ────────────────────────────────────

private def showEscaped (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ match c with
      | '\\' => "\\\\"
      | '"'  => "\\\""
      | _    => c.toString) ""

/-- Wrap `s` in double quotes, escaping `\` and `"`. -/
def showQuoted (s : String) : String :=
  "\"" ++ showEscaped s ++ "\""

mutual
  private partial def reprSExpr (x : SExpr α) : String :=
    match x with
    | .sym _ s         => s
    | .str _ s         => showQuoted s
    | .num _ n         => toString n
    | .lst _ []        => "()"
    | .lst _ (x :: xs) => "(" ++ reprSExpr x ++ reprTail xs ++ ")"

  private partial def reprTail (xs : List (SExpr α)) : String :=
    match xs with
    | []      => ""
    | x :: xs => " " ++ reprSExpr x ++ reprTail xs
end

instance : ToString (SExpr α) := ⟨reprSExpr⟩

instance [Inhabited α] : Inhabited (SExpr α) := ⟨.sym default ""⟩

-- ── Utilities ─────────────────────────────────────────────────────────────────

/-- Wrap a printable ASCII string as a quoted S-expression atom.
    Panics on any non-printable character. -/
def stringSExpr (s : String) : SExpr Unit :=
  if s.all (fun c => let n := c.toNat; n >= 32 && n < 127) then
    .str () s
  else
    panic! "SExpr.stringSExpr: Bad string"

private def observeSymbol (tgt : String) : SExpr α → Bool
  | .sym _ s => tgt == s
  | _        => false

private def observeHead (tgt : String) : SExpr α → Bool
  | .lst _ (x :: _) => observeSymbol tgt x
  | _                => false

private def confrontNothing {β : Type} : List (Option β) → Option (List β)
  | []             => some []
  | none :: _      => none
  | some a :: rest =>
    match confrontNothing rest with
    | none       => none
    | some rest' => some (a :: rest')

-- Drop list elements that fail `pred`, returning `none` if the result is empty.
-- Non-list S-expressions pass through unchanged.
private partial def filterListExprs (pred : SExpr α → Bool) (s : SExpr α) : Option (SExpr α) :=
  match s with
  | .lst _ []        => none
  | .lst p (x :: xs) =>
    if pred x then some (.lst p (x :: xs.filter pred))
    else
      match xs with
      | []      => none
      | y :: ys => filterListExprs pred (.lst (getPos y) (y :: ys))
  | _ => some s

-- Descend `n` layers and apply `filterListExprs` at that depth.
private partial def filterSubExprs
    (n : Nat) (pred : SExpr α → Bool) (s : SExpr α) : Option (SExpr α) :=
  match n with
  | 0     => filterListExprs pred s
  | n + 1 =>
    match s with
    | .lst p xs =>
      match confrontNothing (xs.map (filterSubExprs n pred)) with
      | none    => none
      | some ys => some (.lst p ys)
    | _ => some s

/-- Remove any immediate sub-list whose head symbol equals `avoidStr`. -/
def filterListsByHead (avoidStr : String) (sexpr : SExpr α) : Option (SExpr α) :=
  filterSubExprs 0 (fun s => !observeHead avoidStr s) sexpr

end SExpr

-- ── Source position ───────────────────────────────────────────────────────────

/-- A position in a source file; used to annotate `SExpr Pos`. -/
structure Pos where
  file   : String
  line   : Nat
  column : Nat

/-- Emacs-compatible `file:line:col:` format. -/
instance : ToString Pos where
  toString p := s!"{p.file}:{p.line}:{p.column}: "

-- ── PosHandle ─────────────────────────────────────────────────────────────────

/-- A stream handle that tracks the current source position and buffers one
    look-ahead character (needed to implement `peek` on top of `read`).
    Uses `IO.FS.Stream` so that both file handles and stdin/stdout work. -/
structure PosHandle where
  handle  : IO.FS.Stream
  pFile   : String
  posRef  : IO.Ref (Nat × Nat)   -- (line, column)
  peekRef : IO.Ref (Option Char) -- one-character lookahead buffer

/-- Wrap an open stream in a `PosHandle`, starting at line 1, column 1. -/
def posHandle (file : String) (handle : IO.FS.Stream) : IO PosHandle := do
  let posRef  ← IO.mkRef (1, 1)
  let peekRef ← IO.mkRef (none : Option Char)
  return { handle, pFile := file, posRef, peekRef }

-- ── Private I/O helpers ───────────────────────────────────────────────────────

private def isPrint (c : Char) : Bool :=
  let n := c.toNat; n >= 32 && n < 127

private def isSym (c : Char) : Bool :=
  "+-*/<=>!?:$%_&~^".contains c || c.isAlpha || c.isDigit

private def mkPos (ph : PosHandle) (l c : Nat) : Pos :=
  { file := ph.pFile, line := l, column := c }

-- Consume and return the next character; returns `none` at EOF.
private def hGetChar (ph : PosHandle) : IO (Option Char) := do
  match ← ph.peekRef.get with
  | some c =>
    ph.peekRef.set none
    return some c
  | none =>
    let b ← ph.handle.read 1
    if b.size == 0 then return none
    return some (Char.ofNat b[0]!.toNat)

-- Peek at the next character without consuming it; returns `none` at EOF.
private def hPeekChar (ph : PosHandle) : IO (Option Char) := do
  match ← ph.peekRef.get with
  | some c => return some c
  | none =>
    let b ← ph.handle.read 1
    if b.size == 0 then return none
    let c := Char.ofNat b[0]!.toNat
    ph.peekRef.set (some c)
    return some c

-- Raise an IO error (handle is left open to be closed by the caller or GC).
private def hAbort {α : Type} (_ : PosHandle) (msg : String) : IO α :=
  throw (IO.userError msg)

-- ── Token ─────────────────────────────────────────────────────────────────────

private inductive Token where
  | atom   (x   : SExpr Pos) : Token
  | lparen (pos : Pos)       : Token
  | rparen (pos : Pos)       : Token
  | eof                      : Token

-- ── Scanner (mutually recursive) ──────────────────────────────────────────────

mutual

  private partial def scan (ph : PosHandle) (l c : Nat) : IO (Nat × Nat × Token) := do
    match ← hGetChar ph with
    | none    => return (l, c, .eof)
    | some ch => skip ph l c ch

  -- Skip whitespace; dispatch on the first non-whitespace character.
  private partial def skip (ph : PosHandle) (l c : Nat) (ch : Char)
      : IO (Nat × Nat × Token) :=
    if ch == '\n'        then scan ph (l + 1) 1
    else if ch.isWhitespace then scan ph l (c + 1)
    else if ch == ';'    then scanComment ph l (c + 1)
    else if ch == '('    then return (l, c + 1, .lparen (mkPos ph l c))
    else if ch == ')'    then return (l, c + 1, .rparen (mkPos ph l c))
    else                      atomTok ph l (c + 1) (mkPos ph l c) ch

  private partial def scanComment (ph : PosHandle) (l c : Nat)
      : IO (Nat × Nat × Token) := do
    match ← hGetChar ph with
    | none      => return (l, c, .eof)
    | some '\n' => scan ph (l + 1) 1
    | some _    => scanComment ph l (c + 1)

  -- Dispatch on the first character of a token body.
  private partial def atomTok (ph : PosHandle) (l c : Nat) (pos : Pos) (ch : Char)
      : IO (Nat × Nat × Token) :=
    if ch == '"'               then scanStr    ph l c pos []
    else if ch.isDigit         then scanNumber ph l c pos [ch]
    else if ch == '+' || ch == '-' then numOrSym  ph l c pos [ch]
    else if isSym ch           then scanSymbol ph l c pos [ch]
    else hAbort ph s!"{pos}Bad char in atom"

  -- Scan a quoted string; `s` accumulates characters in reverse.
  private partial def scanStr (ph : PosHandle) (l c : Nat) (pos : Pos) (s : List Char)
      : IO (Nat × Nat × Token) := do
    match ← hGetChar ph with
    | none      => hAbort ph s!"{pos}End of input in string"
    | some '"'  => return (l, c + 1, .atom (.str pos (String.ofList s.reverse)))
    | some '\\' => scanEscaped ph l (c + 1) pos s
    | some ch   =>
      if isPrint ch then scanStr ph l (c + 1) pos (ch :: s)
      else hAbort ph s!"{pos}Bad char in string"

  -- Handle a backslash escape inside a quoted string.
  private partial def scanEscaped (ph : PosHandle) (l c : Nat) (pos : Pos) (s : List Char)
      : IO (Nat × Nat × Token) := do
    match ← hGetChar ph with
    | none      => hAbort ph s!"{pos}End of input in escaped char in string"
    | some '"'  => scanStr ph l (c + 1) pos ('"'  :: s)
    | some '\\' => scanStr ph l (c + 1) pos ('\\' :: s)
    | some _    => hAbort ph s!"{pos}Bad escaped char in string"

  -- Scan a decimal integer; `s` accumulates digit characters in reverse.
  private partial def scanNumber (ph : PosHandle) (l c : Nat) (pos : Pos) (s : List Char)
      : IO (Nat × Nat × Token) := do
    match ← hPeekChar ph with
    | none =>
      mkNumTok ph l c pos s
    | some ch =>
      if ch.isDigit then do
        _ ← hGetChar ph
        scanNumber ph l (c + 1) pos (ch :: s)
      else if isSym ch then
        hAbort ph s!"{pos}Bad char after number"
      else
        mkNumTok ph l c pos s

  -- A token starting with `+` or `-`: look ahead to decide number vs symbol.
  private partial def numOrSym (ph : PosHandle) (l c : Nat) (pos : Pos) (s : List Char)
      : IO (Nat × Nat × Token) := do
    match ← hPeekChar ph with
    | none    => scanSymbol ph l c pos s
    | some ch =>
      if ch.isDigit then
        -- `+` is simply dropped (Haskell convention); `-` is kept as sign.
        if s == ['+'] then scanNumber ph l c pos []
        else               scanNumber ph l c pos s
      else
        scanSymbol ph l c pos s

  -- Scan a symbol; `s` accumulates characters in reverse.
  private partial def scanSymbol (ph : PosHandle) (l c : Nat) (pos : Pos) (s : List Char)
      : IO (Nat × Nat × Token) := do
    match ← hPeekChar ph with
    | none    => return (l, c, .atom (.sym pos (String.ofList s.reverse)))
    | some ch =>
      if isSym ch then do
        _ ← hGetChar ph
        scanSymbol ph l (c + 1) pos (ch :: s)
      else
        return (l, c, .atom (.sym pos (String.ofList s.reverse)))

  -- Build a `.num` token from the digit accumulator `s`.
  private partial def mkNumTok (ph : PosHandle) (l c : Nat) (pos : Pos) (s : List Char)
      : IO (Nat × Nat × Token) := do
    let numStr := String.ofList s.reverse
    match numStr.toInt? with
    | some n => return (l, c, .atom (.num pos n))
    | none   => hAbort ph s!"{pos}Invalid number: {numStr}"

  -- Recursive-descent list parser.
  private partial def parseList (ph : PosHandle) (pos : Pos) (l c : Nat)
      (xs : List (SExpr Pos)) : IO (Nat × Nat × SExpr Pos) := do
    let (l', c', tok) ← scan ph l c
    match tok with
    | .rparen _  => return (l', c', .lst pos xs.reverse)
    | .atom x    => parseList ph pos l' c' (x :: xs)
    | .lparen p  =>
      let (l'', c'', x) ← parseList ph p l' c' []
      parseList ph pos l'' c'' (x :: xs)
    | .eof       => hAbort ph s!"{pos}Unexpected end of input in list"

end

-- ── Public reader ─────────────────────────────────────────────────────────────

/-- Read one S-expression from `ph`, returning `none` at end of file.
    Closes the handle on EOF. -/
def load (ph : PosHandle) : IO (Option (SExpr Pos)) := do
  let (l, c) ← ph.posRef.get
  let (l', c', tok) ← scan ph l c
  match tok with
  | .atom x    =>
    ph.posRef.set (l', c')
    return some x
  | .lparen pos =>
    let (l'', c'', x) ← parseList ph pos l' c' []
    ph.posRef.set (l'', c'')
    return some x
  | .rparen pos =>
    hAbort ph s!"{pos}Close of unopened list"
  | .eof       =>
    return none

end Cpsa2Lean.Lib
