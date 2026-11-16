# Staged Contract Kernels for iPRA

Research package prepared for Vladimir Reshetnikov, 15 November 2026
(America/Los_Angeles).

## Start here

Read `paper/ipra_staged_contract_kernel.pdf`. Its complete editable LaTeX
source is `paper/ipra_staged_contract_kernel.tex` with section files under
`paper/sections/`.

The repository audit is pinned to ProveIt commit
`38e83bc0d09647a98ce9fe5edf45d6b34f820dff`.

## Main contribution

The package consolidates the repository's finite-observation, demand,
relational-certificate, and proof-graph approaches around one missing
proof-engineering device: **arity-normalized staged specialization**.

A local object-iPRA theorem may live in any finite variable frame. The generic
kernel:

1. specializes it with the checked `Prf.subst` theorem;
2. aligns its assumptions with `Prf.weaken`;
3. composes it with prior nodes using `Prf.trans`;
4. uses `PRA.qfInd` only for explicitly packaged loop nodes.

The final endpoint is a literal `Prf PRAAx` judgment. Native export is performed
only afterward with `pra_iff_native.mp`. The graph is traversed by Lean at the
host stage; the object theory receives concrete `PR` symbols and proof terms,
not a universal evaluator.

## Contents

- `paper/`:  complete human-readable report and compiled PDF.
- `lean/`:   integration-oriented Lean kernel, obligation interfaces, and a
  dependency-ordered formalization plan.
- `code/`:   standard-library exact reference algorithms and tests.
- `examples/demo_evidence.json`: replayable demand, schedule, viability, and
  cubic-bisection evidence.
- `schema/contract.schema.json`: machine-readable shape for application
  contracts.
- `metadata/`: theorem ledger, difficulty matrix, claims, and source audit.
- `provenance/`: pinned-source manifest.
- `validation/`: test, build, PDF, and preflight logs.
- `verify.py`: standard-library verification runner.
- `build.sh`: rebuild tests, demo, PDF, manifest, and archive-local checks.

## Exact status

- Human mathematical arguments: complete for the generic framework theorems
  listed in `metadata/THEOREM_LEDGER.md`.
- Python: eight exact test groups pass.
- PDF: built and visually inspected in this artifact environment.
- Lean: no `axiom`, `sorry`, or `admit`; **not compiled**, because Lean/Lake was
  absent from the preparation runtime. The files target the current
  `ConciseIPRA` APIs and include a precise completion path.

This package does not claim general effective Siegel or Faltings, uniform
Mordell-Weil representatives, ineffective analytic constants, exact branch
selection through collisions, or verification of all repository packets.

## Reproduce

```sh
./build.sh
```

The Python checks require Python 3.10 or newer. PDF rebuilding requires
`pdflatex`. Lean testing must be done from the pinned ProveIt root workspace;
see `lean/FORMALIZATION_PLAN.md`.
