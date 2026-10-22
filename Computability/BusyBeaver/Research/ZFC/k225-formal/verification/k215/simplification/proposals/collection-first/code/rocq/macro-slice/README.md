# Checked program-slice transport for the Rocq K215 macro library

This focused prototype is reviewed against ProveIt commit
`6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95`.

## Result

The 53 literal macro roots in `coq/215/ProgLibPerm.v` have a closed support of
89 DAG nodes. Every row in that support is identical in the literal programs
`dagPerm` (215), `dagDom` (217), and `dag219` (the 218 lane).

`RMSlice.v` proves that agreement on a closed node support preserves the exact
structured `RM.run` relation, with the same input registers, output registers,
and exit. `K215MacroSlice.v` checks the 89-row certificate and proves this
equivalence at all 53 macro roots. The result is uniform over arbitrary
natural-valued register files; it includes normal, break, continue, and halt
exits. It is not an assertion that the complete programs are equivalent.

All three macro-library bodies, starting at the first `From Coq Require Import`,
are byte-identical after renaming only the namespace and DAG identifiers. Each
normalized body is 759 lines / 36,402 bytes, SHA-256
`3bf4c8513969c944aba82ea909154e4d929a40ebba152a497d0377877ffc6106`.
The full files are 780, 781, and 779 lines including ancestry comments.

## Evidence and exact scope

The six modules (`RM`, three DAGs, `RMSlice`, `K215MacroSlice`) compiled with
Coq 8.18.0; `checked_run_iff`, `macro_run_215_217`, and `macro_run_215_218`
printed `Closed under the global context`. Recursive `coqchk -silent` on
`K215MacroSlice` exited successfully. This is a prototype check on the stated
toolchain, not a rebuild of the repository's Rocq 9.1 machine-to-ZFC endpoint.

`slice_audit.json` pins the inspected inputs and reports the exact support.
`audit_slice.py REPOSITORY` recomputes the support and emits the Rocq literal;
the kernel checks the literal independently, so the Python parser/generator is
outside the trust boundary. The small dependency files under `deps/` are
byte-exact copies from the reviewed repository; see `SOURCE_MANIFEST.json`.

## Reproduction

With `coqc` and `coqchk` on PATH, run `python3 build.py`. The script compiles the
six modules in dependency order and recursively checks the final module. Set
`COQC` and `COQCHK` to executable paths if needed. The proof imports use only
the standard library and the included unchanged `RM.v`.

## Recommended integration

1. Move the program-independent nine-register record and its `get`, `set`,
   `approx` lemmas to one shared module. Factor the structural `sem` and
   `seqx` rules, `expand`, and tactics over an arbitrary program.
2. Keep one source of the 759-line macro library. Its named contracts use the
   shared register record and one reference DAG.
3. Instantiate those macro contracts at `dagPerm` and `dagDom` through the
   checked slice theorem. Keep same-name public wrappers where required.
4. Retain the K215-specific dispatcher, AX word, root theorem, and program
   expansion against the actual K215 DAG. Node 141 is a dispatch atom but is
   outside the shared macro slice; replacing the whole DAG would be wrong.
5. Update the producers (`regenerate215.py`, `regenerate217.py`) as part of the
   same change; currently they copy and rename the full earlier library.
6. Compile every affected client, print the unchanged endpoint assumptions,
   and run the repository's Rocq 9.1 recursive endpoint check before adoption.

This reduces the number of maintained macro proofs across the family. It does
not by itself establish a smaller single-endpoint import closure, smaller
proof terms, faster compilation, or a smaller Turing machine. A single K215
endpoint still needs one copy of the macro mathematics; wrappers and extra
reference data must be counted in any net-size measurement.

No production repository file was changed by this packet.
