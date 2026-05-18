/-
Main

Entry point for the CPSA solver executable.
Port of CPSA.Main (MITRE cpsa v4.4.8).

Reads command-line arguments, opens input, expands macros, and dispatches
to the reduction engine or the macro-expand-only pretty-printer.
-/

import Cpsa2Lean

open Cpsa2Lean.Lib (SExpr Pos PosHandle comment posHandle load
                    readSExprs expand writeSExprH writeLnSExprH writeCommentH
                    abort success outputHandle cpsaVersion defaultMargin)
open Cpsa2Lean.Options (Options Flag defaultOptions)
open Cpsa2Lean.Algebra (name algAlias origin)
open Cpsa2Lean.Signature (Sig defaultSig loadSig)
open Cpsa2Lean.Loader (loadSExprs)
open Cpsa2Lean.Reduction (runSolver)

-- ── Algebra constants ─────────────────────────────────────────────────────────

/-- List of recognized algebra names (name and its alias). -/
private def algs : List String := [name, algAlias]

/-- Default step limit (from defaultOptions). -/
private def defaultStepLimit : Int := defaultOptions.optLimit

/-- Default strand bound (from defaultOptions). -/
private def defaultStrandBound : Int := defaultOptions.optBound

/-- Default depth bound (from defaultOptions). -/
private def defaultDepthBound : Int := defaultOptions.optDepth

/-- Default algebra name (from defaultOptions). -/
private def defaultAlgebra : String := defaultOptions.optAlg

-- ── Command-line argument parser ──────────────────────────────────────────────

/-- Usage string.  (`getProgName` is unavailable in Lean; name is hardcoded.) -/
private def usageStr : String :=
  "Usage: cpsa [OPTIONS] [FILE]\n" ++
  "  -o FILE  --output=FILE       output FILE\n" ++
  "  -l INT   --limit=INT         step count limit (default " ++
    s!"{defaultStepLimit})\n" ++
  "  -b INT   --bound=INT         strand count bound (default " ++
    s!"{defaultStrandBound})\n" ++
  "  -d INT   --depth=INT         tree depth bound (default unbounded)\n" ++
  "  -m INT   --margin=INT        set output margin (default " ++
    s!"{defaultMargin})\n" ++
  "  -e       --expand            expand macros only; don't analyze\n" ++
  "  -n       --noisochk          disable isomorphism checks\n" ++
  "  -c       --check-nonces      check nonces first\n" ++
  "  -t       --try-old-strands   try old strands first\n" ++
  "  -r       --reverse-nodes     try younger nodes first\n" ++
  "  -g       --goals-sat         stop when goals are satisfied\n" ++
  "  -a STR   --algebra=STR       algebra (default " ++ defaultAlgebra ++ ")\n" ++
  "  -s       --show-algebras     show algebras\n" ++
  "  -h       --help              show help message\n" ++
  "  -v       --version           show version number\n"

/-- Try to parse one argument (or argument+value pair).
    Returns `some (flag, remaining_args)` on success, `none` if unrecognized.
    Mirrors the `options` descriptor list in Haskell's Main.hs. -/
private def parseOne (arg : String) (rest : List String)
    : Option (Flag × List String) :=
  -- Short option consuming next token as value
  let shortArg (flag : String → Flag) : Option (Flag × List String) :=
    match rest with
    | []         => none  -- missing required argument
    | v :: rest' => some (flag v, rest')
  -- Long option: `--key` (next token) or `--key=val` (inline)
  let longArg (key : String) (flag : String → Flag) : Option (Flag × List String) :=
    let longEq    := arg == "--" ++ key
    let longEqArg := arg.startsWith ("--" ++ key ++ "=")
    if longEq then shortArg flag
    else if longEqArg then
      some (flag ((arg.drop (("--" ++ key ++ "=").length)).toString), rest)
    else none
  match arg with
  | "-o" => shortArg .Output
  | "-l" => shortArg .Limit
  | "-b" => shortArg .Bound
  | "-d" => shortArg .Depth
  | "-m" => shortArg .Margin
  | "-a" => shortArg .Algebra
  | "-e" | "--expand"           => some (.Expand,             rest)
  | "-n" | "--noisochk"         => some (.NoIsoChk,           rest)
  | "-c" | "--check-nonces"     => some (.CheckNoncesFirst,   rest)
  | "-t" | "--try-old-strands"  => some (.TryOldStrandsFirst, rest)
  | "-r" | "--reverse-nodes"    => some (.TryYoungNodesFirst, rest)
  | "-g" | "--goals-sat"        => some (.GoalsSat,           rest)
  | "-s" | "--show-algebras"    => some (.Algebras,           rest)
  | "-h" | "--help"             => some (.Help,               rest)
  | "-v" | "--version"          => some (.Info,               rest)
  | _ =>
      -- Try long-option forms with a value argument
      longArg "output"  .Output  <|>
      longArg "limit"   .Limit   <|>
      longArg "bound"   .Bound   <|>
      longArg "depth"   .Depth   <|>
      longArg "margin"  .Margin  <|>
      longArg "algebra" .Algebra

/-- Parse all command-line arguments.
    Returns `(flags, files)`.  Stops at the first non-option argument
    (RequireOrder semantics).  Aborts with a message for unrecognized options.
    Mirrors the `getOpt RequireOrder options argv` call in Haskell's Main.hs. -/
private partial def parseArgs (argv : List String) : IO (List Flag × List String) :=
  let rec loop (flags : List Flag) : List String → IO (List Flag × List String)
    | []              => return (flags.reverse, [])
    | "--" :: rest    => return (flags.reverse, rest)
    | arg :: rest     =>
        if arg.startsWith "-" then
          match parseOne arg rest with
          | none             => abort s!"Unrecognized option: {arg}\n{usageStr}"
          | some (fl, rest') => loop (fl :: flags) rest'
        else
          return (flags.reverse, arg :: rest)
  loop [] argv

-- ── Flag interpreter ──────────────────────────────────────────────────────────

/-- Interpret a list of flags into an `Options` record.
    Early-exit flags (`Help`, `Info`, `Algebras`) call `success` and exit.
    Mirrors `interp :: [String] -> Options -> [Flag] -> IO Options`. -/
private partial def interp (algs_ : List String) (opts : Options)
    : List Flag → IO Options
  | []                            => return opts
  | .Output n      :: rest        =>
      -- First output flag wins; subsequent ones are ignored.
      if opts.optFile.isNone then
        interp algs_ { opts with optFile := some n } rest
      else
        interp algs_ opts rest
  | .Limit  v      :: rest        =>
      match v.toNat? with
      | some n => interp algs_ { opts with optLimit := Int.ofNat n } rest
      | none   => abort "Bad value for step limit (expected non-negative integer)"
  | .Bound  v      :: rest        =>
      match v.toNat? with
      | some n => interp algs_ { opts with optBound := Int.ofNat n } rest
      | none   => abort "Bad value for strand bound (expected non-negative integer)"
  | .Depth  v      :: rest        =>
      match v.toNat? with
      | some n => interp algs_ { opts with optDepth := Int.ofNat n } rest
      | none   => abort "Bad value for depth bound (expected non-negative integer)"
  | .Margin v      :: rest        =>
      match v.toNat? with
      | some n => interp algs_ { opts with optMargin := Int.ofNat n } rest
      | none   => abort "Bad value for margin (expected non-negative integer)"
  | .Expand           :: rest     => interp algs_ { opts with optAnalyze := false } rest
  | .NoIsoChk         :: rest     => interp algs_ { opts with optNoIsoChk := true } rest
  | .CheckNoncesFirst :: rest     => interp algs_ { opts with optCheckNoncesFirst := true } rest
  | .TryOldStrandsFirst :: rest   => interp algs_ { opts with optTryOldStrandsFirst := true } rest
  | .TryYoungNodesFirst :: rest   => interp algs_ { opts with optTryYoungNodesFirst := true } rest
  | .GoalsSat         :: rest     => interp algs_ { opts with optGoalsSat := true } rest
  | .Algebra n        :: rest     =>
      if algs_.contains n then
        interp algs_ { opts with optAlg := n } rest
      else
        abort s!"Algebra {n} not one of\n{String.intercalate "\n" algs_}"
  | .Algebras         :: _        => success (String.intercalate "\n" algs_)
  | .Help             :: _        => success usageStr
  | .Info             :: _        => success cpsaVersion

-- ── Input file opener ─────────────────────────────────────────────────────────

/-- Open input from a named file, or stdin if no files are given.
    Mirrors `openInput :: [String] -> IO PosHandle`. -/
private def openInput (files : List String) : IO PosHandle := do
  match files with
  | []       =>
      -- IO.getStdin returns BaseIO IO.FS.Stream; posHandle accepts IO.FS.Stream
      let h ← IO.getStdin
      posHandle "" h
  | [file]   =>
      -- Convert IO.FS.Handle to IO.FS.Stream with ofHandle
      let fh ← try IO.FS.Handle.mk file .read
                catch _ => abort s!"Cannot open input file: {file}"
      posHandle file (IO.FS.Stream.ofHandle fh)
  | _        => abort s!"Too many input files\n{usageStr}"

-- ── Herald helpers ────────────────────────────────────────────────────────────

/-- Find the first herald form (skipping leading comment forms).
    Mirrors `getHerald :: [SExpr Pos] -> Maybe (SExpr Pos)`. -/
private def getHerald : List (SExpr Pos) → Option (SExpr Pos)
  | []        => none
  | x :: rest =>
      match x with
      | .lst _ (.sym _ "herald"  :: _) => some x
      | .lst _ (.sym _ "comment" :: _) => getHerald rest
      | _                              => none

/-- Extract the association list from a herald form.
    Mirrors `getAlist :: SExpr Pos -> IO [SExpr Pos]`. -/
private def getAlist (x : SExpr Pos) : IO (List (SExpr Pos)) :=
  match x with
  | .lst _ (.sym _ "herald" :: .sym _ _ :: alist) => return alist
  | .lst _ (.sym _ "herald" :: .str _ _ :: alist) => return alist
  | _ => abort "Bad herald form"

/-- Look up all values for `key` in an association list.
    Mirrors `assoc :: String -> [SExpr a] -> [SExpr a]`. -/
private def assoc (key : String) (alist : List (SExpr Pos)) : List (SExpr Pos) :=
  alist.flatMap fun x => match x with
    | .lst _ (.sym _ head :: rest) => if head == key then rest else []
    | _                            => []

/-- Map a herald key-value pair to a Flag (returns `none` for unknown keys).
    Mirrors the combined logic of `flagOf`, `findOpt`, and `interpAssoc`. -/
private def flagOfAssoc (key : String) (vals : List (SExpr Pos)) : Option Flag :=
  match key, vals with
  | "output",          [.sym _ v] => some (.Output v)
  | "output",          [.str _ v] => some (.Output v)
  | "limit",           [.sym _ v] => some (.Limit v)
  | "limit",           [.num _ n] => some (.Limit s!"{n}")
  | "bound",           [.sym _ v] => some (.Bound v)
  | "bound",           [.num _ n] => some (.Bound s!"{n}")
  | "depth",           [.sym _ v] => some (.Depth v)
  | "depth",           [.num _ n] => some (.Depth s!"{n}")
  | "margin",          [.sym _ v] => some (.Margin v)
  | "margin",          [.num _ n] => some (.Margin s!"{n}")
  | "expand",          []         => some .Expand
  | "noisochk",        []         => some .NoIsoChk
  | "check-nonces",    []         => some .CheckNoncesFirst
  | "try-old-strands", []         => some .TryOldStrandsFirst
  | "reverse-nodes",   []         => some .TryYoungNodesFirst
  | "goals-sat",       []         => some .GoalsSat
  | "algebra",         [.sym _ v] => some (.Algebra v)
  | "algebra",         [.str _ v] => some (.Algebra v)
  | _,                 _          => none  -- unknown or malformed; skip

/-- Extract flags from the herald's association list.
    Mirrors `getAlistOpts :: [SExpr Pos] -> IO [Flag]`. -/
private partial def getAlistOpts (alist : List (SExpr Pos)) : IO (List Flag) :=
  let rec loop (acc : List Flag) : List (SExpr Pos) → IO (List Flag)
    | [] => return acc.reverse
    | .lst _ (.sym _ key :: vals) :: rest =>
        match flagOfAssoc key vals with
        | none       => loop acc rest
        | some flag  => loop (flag :: acc) rest
    | _ => abort "Bad herald form"
  loop [] alist

/-- Verify that a flag is legal inside a herald (no output/help/info/algebras).
    Mirrors `checkHeraldFlag :: Flag -> IO ()`. -/
private def checkHeraldFlag (flag : Flag) : IO Unit :=
  match flag with
  | .Output _  => abort "output option not allowed in herald"
  | .Help      => abort "help option not allowed in herald"
  | .Info      => abort "version option not allowed in herald"
  | .Algebras  => abort "show algebras option not allowed in herald"
  | _          => return ()

-- ── Signature loader ──────────────────────────────────────────────────────────

/-- Get the signature from a herald form, or return the default.
    Mirrors `getSig :: Maybe (SExpr Pos) -> IO Sig`. -/
private def getSig (herald : Option (SExpr Pos)) : IO Sig :=
  match herald with
  | none    => return defaultSig
  | some x  => do
      let xs    ← getAlist x
      let decls := assoc "lang" xs
      match loadSig x.annotation decls with
      | .ok sig    => return sig
      | .error msg => abort msg

-- ── Pretty-printer (--expand mode) ───────────────────────────────────────────

/-- When `--expand` is given: just pretty-print the expanded S-expressions.
    Mirrors `prettyPrint :: Options -> [SExpr a] -> IO ()`. -/
private def prettyPrint (opts : Options) (sexprs : List (SExpr Pos)) : IO Unit := do
  let h ← outputHandle opts.optFile
  let m := opts.optMargin
  writeCommentH h m cpsaVersion
  writeCommentH h m "Expanded macros"
  for sexpr in sexprs do
    writeLnSExprH h m sexpr
  h.flush

-- ── go / select (load, configure, solve) ─────────────────────────────────────

/-- Open output, write header comments, load preskeletons, run the solver.
    Mirrors `go :: String -> Gen -> [String] -> Maybe (SExpr Pos) ->
                 Options -> [SExpr Pos] -> IO ()`. -/
private def go (nom : String) (gen : Cpsa2Lean.Algebra.Gen) (files : List String)
    (herald : Option (SExpr Pos)) (opts : Options)
    (sexprs : List (SExpr Pos)) : IO Unit := do
  let sig   ← getSig herald
  let preskels ←
    match loadSExprs sig nom gen sexprs with
    | .ok ks     => pure ks
    | .error msg => abort msg
  let h ← outputHandle opts.optFile
  let m := opts.optMargin
  -- Print herald if present
  match herald with
  | none       => pure ()
  | some sexpr => do
      writeSExprH h m sexpr
      h.putStrLn ""
  -- Print run-time information comments
  writeCommentH h m cpsaVersion
  match files with
  | [file] => writeCommentH h m s!"All input read from {file}"
  | _      => writeCommentH h m "All input read"
  if opts.optNoIsoChk then
    writeCommentH h m "Isomorphism checking disabled"
  if opts.optLimit != defaultStepLimit then
    writeCommentH h m s!"Step count limited to {opts.optLimit}"
  if opts.optBound != defaultStrandBound then
    writeCommentH h m s!"Strand count bounded at {opts.optBound}"
  if opts.optDepth != defaultDepthBound then
    writeCommentH h m s!"Tree depth bounded at {opts.optDepth}"
  if opts.optCheckNoncesFirst then
    writeCommentH h m "Nonces checked first"
  if opts.optTryOldStrandsFirst then
    writeCommentH h m "Old strands tried first"
  if opts.optTryYoungNodesFirst then
    writeCommentH h m "Younger nodes tried first"
  -- Run the solver
  runSolver opts h preskels
  h.flush

/-- Select the algebra and dispatch.
    Mirrors `select :: [String] -> Maybe (SExpr Pos) -> Options ->
                     [SExpr Pos] -> IO ()`. -/
private def select (files : List String) (herald : Option (SExpr Pos))
    (opts : Options) (sexprs : List (SExpr Pos)) : IO Unit :=
  if opts.optAlg == name || opts.optAlg == algAlias then
    go name origin files herald opts sexprs
  else
    abort s!"Bad algebra: {opts.optAlg}"

-- ── main ──────────────────────────────────────────────────────────────────────

/-- Entry point.  Mirrors `main :: IO ()` in CPSA/Main.hs.
    In Lean 4, command-line arguments are passed as the `args` parameter. -/
def main (args : List String) : IO Unit := do
  let (flags, files) ← parseArgs args
  -- Handle early-exit flags first (--help/--version/--show-algebras exit before
  -- reading any input file, matching the Haskell behavior).
  let _              ← interp algs defaultOptions flags
  -- Open input
  let ph             ← openInput files
  let sexprs         ← readSExprs ph
  -- Herald handling
  let herald := getHerald sexprs
  let heraldFlags ←
    match herald with
    | none       => pure ([] : List Flag)
    | some sexpr => do
        let alist  ← getAlist sexpr
        let hflags ← getAlistOpts alist
        hflags.forM checkHeraldFlag
        pure hflags
  -- Build final options: herald flags first, then command-line flags override.
  let opts           ← interp algs defaultOptions heraldFlags
  let opts           ← interp algs opts flags
  -- Expand macros (throws IO.userError on include/macro errors)
  let sexprs         ← try expand sexprs
                        catch e => abort e.toString
  -- Analyze or pretty-print
  if opts.optAnalyze then
    select files herald opts sexprs
  else
    prettyPrint opts sexprs
