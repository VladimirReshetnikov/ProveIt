# Original-code model bridge

This directory supplies three new Lean source files and the exact narrow
ProveIt source closure needed to check them. The source snapshot is
`426592ce97e52d309bfb8f0132411556650b7ac1`.

The main result is same-structure equivalence of the original all-code
decoded-bundle theory, the original encodable-bundle theory, and native-equality
CP/GIC, under irreflexivity. The abstract six-register enumerator consequently
halts exactly when that model theory has no nonempty irreflexive model.

The new theorem is not a binary-machine simulation, an internal-ZFC theorem,
or a new state-count record. See `theory-findings.md` for the mathematical
proof, exact scope, prior-source audit and remaining work.

## Reproduce

Install Lean 4.32.0 and run from this directory:

```sh
ZFC_LEAN=/absolute/path/to/lean python build.py
```

If `lean` already resolves to Lean 4.32.0 on PATH, `python build.py` is enough.
The script uses only Python's standard library. It checks all 23 original
Git blob identities and serially rebuilds all 26 modules from source.
It writes `dependency-build.json` and `verification.json`. Generated
`.olean` files are kept under `cache/` and are not needed in a source archive.

The recorded complete build passed in 15.84 seconds. All printed dependencies
of the new theorems are among `propext`, `Classical.choice`, and `Quot.sound`.
The checks include truth code zero together with coincident nongated labels,
native equality code 35, and the empty-domain scope of model equivalence.

## Integrate

Apply `model-bridge.patch` at the repository root, or copy these files:

- `src/BusyBeaver/ZFC/ModelBridge254.lean`
- `src/BusyBeaver/ZFC/EnumModelBridge254.lean`
- `src/BusyBeaver/ZFC/ModelBridge254Checks.lean`

The destination is `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`.
The patch only adds these three files. The repository umbrella and source
runner can then import the new modules as appropriate for the current tree.
The remaining `src/` files are unchanged pinned dependencies supplied for
reproducibility and should not overwrite newer repository files.

All pre-existing source attributions are preserved. The original numerical
calculus and enumerator are attributed in their existing headers to the
Mira-Cult / Jeff machine-verification development; the model comparison
modules supplied here are new additions.
