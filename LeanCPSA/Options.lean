/-
LeanCPSA.Options

Command line options
Port of CPSA.Options (MITRE cpsa).

Copyright (c) 2026 Paul D. Rowe
Copyright (c) 2009 The MITRE Corporation

This program is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.
-/

/-
Defines the `Options` record and its defaults, plus the `Flag` ADT used
by the command-line option parser.

The `Flag` ADT is used by the Lean command-line parser in Main.lean.
The Haskell `algOptions`/`algInterp` (which used `System.Console.GetOpt`)
are replaced by `parseArgs`/`interp` in Main.lean.
-/

import LeanCPSA.Algebra

namespace LeanCPSA.Options

open LeanCPSA.Algebra (name)

-- ── Options ───────────────────────────────────────────────────────────────────

/-- CPSA analysis options.
    Mirrors `data Options = Options { ... }`. -/
structure Options where
  optFile               : Option String -- Nothing specifies standard output
  optAlg                : String        -- Name of the algebra
  optAnalyze            : Bool          -- False when only expanding macros
  optNoIsoChk           : Bool          -- True when not performing isomorphism checks
  optCheckNoncesFirst   : Bool          -- True when checking nonces first
  optTryOldStrandsFirst : Bool          -- True when visiting old strands first
  optTryYoungNodesFirst : Bool          -- True when visiting young nodes first
  optGoalsSat           : Bool          -- True when goals satisfied stops tree expansion
  optLimit              : Int           -- Step count limit
  optBound              : Int           -- Strand count bound
  optDepth              : Int           -- Tree depth bound (0 = infinite)
  optMargin             : Int           -- Output line length
  optIndent             : Int           -- Pretty printing indent
  deriving Repr

/-- Default CPSA options.
    Mirrors `defaultOptions`. -/
def defaultOptions : Options where
  optFile               := none
  optAlg                := name
  optAnalyze            := true
  optNoIsoChk           := false
  optCheckNoncesFirst   := false
  optTryOldStrandsFirst := false
  optTryYoungNodesFirst := false
  optGoalsSat           := false
  optLimit              := 2000
  optBound              := 12
  optDepth              := 0
  optMargin             := 72
  optIndent             := 2

-- ── Flag ──────────────────────────────────────────────────────────────────────

/-- Command-line option flags.
    Mirrors `data Flag = Help | Info | Algebra String | ...`.
    Used by the command-line option parser in Main.lean. -/
inductive Flag where
  | Output             : String → Flag -- -o / --output FILE
  | Limit              : String → Flag -- -l / --limit INT
  | Bound              : String → Flag -- -b / --bound INT
  | Depth              : String → Flag -- -d / --depth INT
  | Margin             : String → Flag -- -m / --margin INT
  | Expand             : Flag          -- -e / --expand  (no arg)
  | NoIsoChk           : Flag          -- -n / --noisochk
  | CheckNoncesFirst   : Flag          -- -c / --check-nonces
  | TryOldStrandsFirst : Flag          -- -t / --try-old-strands
  | TryYoungNodesFirst : Flag          -- -r / --reverse-nodes
  | GoalsSat           : Flag          -- -g / --goals-sat
  | Algebra            : String → Flag -- -a / --algebra STRING
  | Algebras           : Flag          -- -s / --show-algebras
  | Help               : Flag          -- -h / --help
  | Info               : Flag          -- -v / --version
  deriving Repr

end LeanCPSA.Options
