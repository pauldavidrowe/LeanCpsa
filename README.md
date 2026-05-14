# cpsa2lean

A Lean 4 port of the CPSA (Cryptographic Protocol Shapes Analyzer) Haskell
codebase.

## Layout

```
cpsa2lean/
├── lakefile.toml          # Lake package manifest
├── lean-toolchain         # Pinned Lean toolchain version
├── Cpsa2Lean.lean         # Library root — re-exports submodules
└── Cpsa2Lean/             # Library modules
    └── Basic.lean         # Starter module (placeholder)
```

## Build

```sh
lake build
```

(Requires [`elan`](https://github.com/leanprover/elan); the toolchain pinned in
`lean-toolchain` will be installed automatically on first build.)

## Adding modules

Each new module lives under `Cpsa2Lean/` and must be re-exported from
`Cpsa2Lean.lean` with an `import` line.
