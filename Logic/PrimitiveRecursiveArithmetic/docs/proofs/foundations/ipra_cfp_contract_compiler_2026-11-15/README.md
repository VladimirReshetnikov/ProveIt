# Certified Finitary Presentations and a Contract-DAG Compiler

Research package prepared from the current ProveIt iPRA tree, 15 November
2026 (America/Los_Angeles).

## Start here

- `paper/cfp_contract_compiler.pdf` — complete human-readable report.
- `paper/cfp_contract_compiler.tex` and `paper/sections/` — editable LaTeX.
- `THEOREM_LEDGER.md` — claim-by-claim proof status.
- `lean/LEAN_PLAN.md` — dependency-ordered path to full `Prf PRAAx` proofs.
- `code/certificate_kernel.py` — exact reference algorithms.
- `examples/framework_certificate.json` — reproducible finite certificate.

## Main contribution

The repository already contains several certificate/modulus/finite-observation
frameworks and a newly placed 40-page Certified Finitary Presentation packet.
This package treats those as the baseline and adds an explicit **contract-DAG
compiler architecture**:

1. local proof-producing primitive-recursive transducers;
2. a reverse pass computing all precision and observation demands;
3. a forward bounded trace;
4. one quantifier-free global invariant;
5. finite-horizon relational refinement without hidden choice;
6. deterministic branch collapse only under an explicit isolation gap;
7. a packet-conversion workflow that separates producers, verifiers,
   barriers, semantic Lean lemmas, and object-language proofs.

The developed human proofs include finite-trace reflection, contract-DAG
composition, backward precision budgeting, finite coherent selection,
gap-based exact branching, bounded enumeration, height/list conversion,
the cardinality-versus-cutoff obstruction, and an exact cubic bisection
benchmark for `y^3 + y = x`.

## Repository baseline

- Repository: `VladimirReshetnikov/ProveIt`
- Inspected `main`: `b88e843c31b50dfe461bfbd0380166ca422cd3ab`
- The inspected tree reports 58 research packets and explicitly distinguishes
  them from the kernel-checked `ConciseIPRA` library.
- No upstream files were modified.

## Exact status

- Human mathematical arguments: complete for the framework theorems listed in
  `THEOREM_LEDGER.md`.
- Python: 11 exact-arithmetic unit tests pass; the JSON certificate validates.
- PDF: built from the included LaTeX and separately rendered/inspected.
- Lean: detailed semantic and object-language blueprints are included, but
  Lean 4.32.0 was unavailable in the build runtime.  The semantic file retains
  explicit `sorry` placeholders; the object file retains schematic targets.
- Generic `Prf PRAAx` trace and DAG theorems: not yet implemented.
- General effective Faltings, Siegel, and ineffective prime-distribution
  producers: not claimed.
- Uniform exact Puiseux branches from arbitrary Cauchy coefficients and
  unrestricted exact rotation-axis selection: deliberately not claimed.

## Reproduce

From the package root:

```sh
bash build.sh
```

The script uses Python's standard library and a standard TeX Live
installation with `latexmk`.  The supplied Python implementation is semantic
evidence and regression testing, not an iPRA proof checker.

For Lean, place this directory inside the pinned ProveIt checkout and follow
`lean/LEAN_PLAN.md`.

## Contents

- `paper/` — report, sections, and compiled PDF.
- `lean/` — semantic prototype, object compiler blueprint, status, and plan.
- `code/` — exact reference implementation and tests.
- `examples/` — example contract certificate.
- `metadata/` — claims, difficulty matrix, framework schema, and source audit.
- `verification/` — actual build/test/PDF inspection records.
- `THEOREM_LEDGER.md` — concise theorem status.
- `MANIFEST.sha256` — hashes of delivered files, excluding itself.
