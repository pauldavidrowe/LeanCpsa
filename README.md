# LeanCPSA

A Lean 4 port of the CPSA (Cryptographic Protocol Shapes Analyzer) Haskell
codebase. This port made heavy use of Claude Code. It is known to pass the 
CPSA 4.4.8 test suite cleanly.

## Layout

```
LeanCPSA/
├── lakefile.toml          # Lake package manifest
├── lean-toolchain         # Pinned Lean toolchain version
├── LeanCPSA.lean         # Library root — re-exports submodules
└── LeanCPSA/             # Library modules
    └── Lib/
        └── Entry.lean     # Common entry point for possible other programs
        └── Expand.lean    # Expands macros
        └── Pretty.lean    # Formats for pretty printing
        └── Printer.lean   # Functionality for writing output
        └── RBMap.lean     # Lean-specific implementations of some Haskell functions
        └── SExpr.lean     # Common library for S-Expressions
        └── Utilities.lean # Other miscellaneous utitlities
    └── Algebra.lean       # Core algebra implementation
    └── Channel.lean       # Channel implementation
    └── Characteristic.lean # Make a skeleton from a defgoal
    └── Cohort.lean        # Defines main cohort steps
    └── Displayer.lean     # Formats internally for display
    └── GenRules.lean      # Generates default rules
    └── Loader.lean        # Core loading functionality
    └── LoadFormula.lean   # Loads goals and rules
    └── Operation.lean     # Helper to track the operation field
    └── Protocol.lean      # Core protocol definitions
    └── Reduction.lean     # Orchestrates the search
    └── Signature.lean     # Defines extensible algebra interface
    └── Strand.lean        # Core functionality
├── lake-manifest.json     # Package maintenance
├── Main.lean              # Main entry point
└── README.md              # This README file
```

## Build

```sh
lake build
```

(Requires [`elan`](https://github.com/leanprover/elan); the toolchain pinned in
`lean-toolchain` will be installed automatically on first build.)

## Adding modules

Each new module lives under `LeanCPSA/` and must be re-exported from

`LeanCPSA.lean` with an `import` line.

## TODO

- Consider porting secondary executables as well
- Replicate test suite and testing infrastructure
- Reduce the number of partial functions by proving termination
- Identify other properties of code to prove
