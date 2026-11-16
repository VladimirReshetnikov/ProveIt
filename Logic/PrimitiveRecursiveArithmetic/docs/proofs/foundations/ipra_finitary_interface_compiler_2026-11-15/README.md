# Finitary interfaces and proof-producing compilation for iPRA

Research package prepared against
`VladimirReshetnikov/ProveIt` commit
`9df5cbdf39e6220be823f611987bd584d37711fd`.
A close-out check found repository head `976e82c3b27401ac97038100d257680973e72dc6`; the intervening latest commit inspected changed only Busy Beaver/PA material, while the audited iPRA README and the two core API files checked for drift retained the same blob hashes. The package remains pinned to the earlier commit for reproducibility.

## Start here

- `paper/ipra_finitary_interface_compiler.pdf` - the complete report.
- `paper/ipra_finitary_interface_compiler.tex` and `paper/sections/` - LaTeX source.
- `lean/ObjectTraceCompiler.lean` - exact object-language trace-compiler outline.
- `lean/LEAN_PLAN.md` - dependency-ordered path to a complete Lean proof.
- `code/finitary_kernel.py` - exact finite reference algorithms.
- `code/test_finitary_kernel.py` - regression suite.
- `metadata/theorem_ledger.md` - claim-by-claim status.
- `metadata/difficulty_matrix.csv` - repository difficulty audit.

## Main contribution

The package unifies the repository's finite-observation, certificate, modulus,
and relational-witness approaches around a proof-producing bridge to the
checked `ConciseIPRA` backend:

1. fixed bounded formulas compile to primitive-recursive Boolean equations;
2. precision parameters are fixed before quantifier-free induction;
3. a bounded trace is reflected from local `Prf PRAAx` base/step/final proofs;
4. contract DAGs use a reverse precision-demand pass and one forward trace;
5. nonunique finite witnesses use backward viability and stable quotient
   erasure;
6. regular names arise from explicit diameter and tail bounds;
7. partial and discontinuous constructions are guarded or relational;
8. finite nets, height/list conversion, simplicial carriers, and affine gluing
   are developed as reusable templates.

## Exact status

- Human-readable mathematical arguments: complete at the level stated in the
  theorem ledger.
- Python: executed with exact `Fraction` arithmetic; all 11 tests pass.
- PDF: compiled and rendered for visual inspection.
- Lean: **uncompiled outline**. Visible `sorry` obligations remain, and no new
  kernel-checked theorem is claimed.
- Checked transport: the existing upstream theorem `pra_iff_native` may be used
  after the ordinary `Prf PRAAx` derivation is completed.
- General Faltings/Siegel height bounds, rational covering representatives,
  ineffective analytic constants, and unrestricted exact branch selectors are
  not claimed.

## Reproduce

From the package root:

```sh
bash build.sh
```

The script runs the Python tests, regenerates the example certificate, and
compiles the PDF with `latexmk` or `pdflatex` when available. Lean is not built
by this script; follow `lean/LEAN_PLAN.md` inside the pinned ProveIt checkout.
