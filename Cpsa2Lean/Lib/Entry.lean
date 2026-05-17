/-
Cpsa2Lean.Lib.Entry

Port of the portable subset of CPSA.Lib.Entry (MITRE cpsa v4.4.8).

The IO-bound functions (`start`, `opts`, `openInput`, `usage`, `abort`,
`success`, `readSExpr`, `gentlyReadSExpr`, `tryIO`, `outputHandle`,
`filterOptions`, `filterInterp`) are omitted — they depend on
`System.IO`, `System.Exit`, `System.Console.GetOpt`, and Haskell's
exception model, none of which have direct Lean analogues.

What IS ported:
  - `defaultMargin`, `defaultIndent` — formatting constants
  - `cpsaVersion`                    — version string (hardcoded for v4.4.8)
  - `comment`                        — build a comment S-expression
  - `writeSExpr`, `writeLnSExpr`     — pure String renderers (no Handle)
  - `writeComment`                   — convenience wrapper
-/

import Cpsa2Lean.Lib.SExpr
import Cpsa2Lean.Lib.Printer

namespace Cpsa2Lean.Lib

-- ── Formatting constants ──────────────────────────────────────────────────────

/-- Default output line length.  Mirrors `defaultMargin`. -/
def defaultMargin : Int := 72

/-- Default pretty-printing indent.  Mirrors `defaultIndent`. -/
def defaultIndent : Int := 2

-- ── Version ───────────────────────────────────────────────────────────────────

/-- CPSA version string.  Mirrors `cpsaVersion` (hardcoded for v4.4.8). -/
def cpsaVersion : String := "CPSA 4.4.8"

-- ── S-expression helpers ──────────────────────────────────────────────────────

/-- Build a `(comment "msg")` S-expression.
    Mirrors `comment :: String -> SExpr ()`. -/
def comment (msg : String) : SExpr Unit :=
  .lst () [.sym () "comment", SExpr.stringSExpr msg]

-- ── Pure rendering (IO-free analogues of the Handle-based writers) ────────────

/-- Render an S-expression to a string using the given margin.
    Mirrors `writeSExpr` (Handle → IO () → pure String). -/
def writeSExpr {α : Type} (margin : Int) (sexpr : SExpr α) : String :=
  pp margin defaultIndent sexpr

/-- Render an S-expression preceded by a blank line.
    Mirrors `writeLnSExpr`. -/
def writeLnSExpr {α : Type} (margin : Int) (sexpr : SExpr α) : String :=
  "\n" ++ writeSExpr margin sexpr

/-- Render a comment S-expression.
    Mirrors `writeComment`. -/
def writeComment (margin : Int) (msg : String) : String :=
  writeSExpr margin (comment msg)

-- ── IO helpers ────────────────────────────────────────────────────────────────

/-- Print `msg` to stderr and exit with failure code 1.
    Mirrors `abort :: String -> IO a`. -/
def abort {α : Type} (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

/-- Print `msg` to stderr and exit with success code 0.
    Mirrors `success :: String -> IO a`. -/
def success {α : Type} (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 0

/-- Open a file for writing, or return stdout if no file is specified.
    Mirrors `outputHandle :: Maybe FilePath -> IO Handle`.
    Returns `IO.FS.Stream` (Lean's unified IO stream type) so that stdout
    (`IO.getStdout`) and file handles (`Handle.toStream`) share a common type. -/
def outputHandle (file : Option String) : IO IO.FS.Stream :=
  match file with
  | none      => IO.getStdout
  | some path => do
      let h ← IO.FS.Handle.mk path .write
      return IO.FS.Stream.ofHandle h

/-- Write an S-expression to a stream followed by a newline.
    Mirrors `writeSExpr h m sexpr` (Haskell's `hPutStrLn h (pp m i sexpr)`). -/
def writeSExprH {α : Type} (h : IO.FS.Stream) (margin : Int)
    (sexpr : SExpr α) : IO Unit :=
  h.putStrLn (pp margin defaultIndent sexpr)

/-- Write a blank line then an S-expression to a stream.
    Mirrors `writeLnSExpr h m sexpr`. -/
def writeLnSExprH {α : Type} (h : IO.FS.Stream) (margin : Int)
    (sexpr : SExpr α) : IO Unit := do
  h.putStrLn ""
  h.putStrLn (pp margin defaultIndent sexpr)

/-- Write a comment S-expression to a stream.
    Mirrors `writeComment h m msg`. -/
def writeCommentH (h : IO.FS.Stream) (margin : Int) (msg : String) : IO Unit :=
  writeSExprH h margin (comment msg)

end Cpsa2Lean.Lib
