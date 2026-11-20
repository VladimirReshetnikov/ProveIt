# Final formalization consistency audit

Scope: `paper/sections/07_formalization.tex`, `lean/README.md`,
`lean/verification.log`, and the package `README.md`, checked against the actual
standalone Lean sources and replay configuration. No broad test suite or
mathematical source was changed or rerun for this audit.

## Counts confirmed

| Lean file | Named proved theorems | Anonymous checked examples |
|---|---:|---:|
| `Truncation.lean` | 23 | 0 |
| `Energy.lean` | 11 | 0 |
| `Examples.lean` | 1 | 8 |
| `Audit.lean` | 0 | 0 |
| **Total** | **35** | **8** |

The counterexample `independent_tail_shortcut_false` is the one named theorem
in `Examples.lean`; it is included among the 35, and is additional to the eight
anonymous examples. I corrected one misleading table sentence in Section 7
which had said “eight checks, including the counterexample.” It now says
“a named counterexample ... plus eight concrete exact examples.”
No other documentation correction was required.

## Build and axiom status confirmed

- `lean-toolchain` pins `leanprover/lean4:v4.32.0`.
- The Lake manifest has no package dependencies; there is no Mathlib dependency.
- The four source files have no `sorry`, `admit`, or new `axiom` declaration.
- The retained verification log ends with “Build completed successfully (9 jobs).”
- Its principal-result axiom receipts report `propext`, `Classical.choice`, and
  `Quot.sound`, exactly as disclosed in the documentation.
- The documents consistently identify the new compiled results as host Lean
  proofs, not new `Prf PRAAx` derivations or a completed formalization of the
  infinite analytic endpoints.
- `ObjectAdapter.lean.txt` is clearly identified as an uncompiled integration
  candidate and is absent from the four Lake targets.
- Existing repository object proofs are described as inspected, not rebuilt.

## Replay instructions confirmed

`bash replay.sh` changes to its own directory and invokes `lake build`.
`LEAN_LAKE_BIN` can select a standalone distribution's absolute `bin/lake` path.
The package `reproduce.py --lean` uses the same environment variable and builds
from the `lean/` directory. Thus Elan can read the pinned toolchain, and the
standalone instructions also match the implemented command path.

The successful receipt is retained from the actual earlier build. This narrow
audit does not claim a fresh rebuild or expand the verification scope.

## Final source fingerprints

- `Audit.lean`: `6e4f7f7e1881490bdcb8d35ddd21117e40d64e9a4f5f4d0bff26c63264eaebb0`
- `Energy.lean`: `da962fa5167aca6bd333cf7bd0722c6415465bea2109af28a90d762f0ca214b2`
- `Examples.lean`: `efb4183c5f77e620f6dc3db41e186877a2b583cfd72d909f59d75d8374de0455`
- `Truncation.lean`: `6d64242725e2eab959cae5b8f3f305813501dd6eedcf709f994652b67d8e7d4b`

**Packaging action:** include this receipt, then recompile the PDF after the
single Section 7 wording correction and regenerate package checksums.
