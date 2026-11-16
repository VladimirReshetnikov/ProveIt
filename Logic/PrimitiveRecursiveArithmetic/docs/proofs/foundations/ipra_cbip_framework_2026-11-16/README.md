# Certified Bounded Interaction Programs for iPRA

This package develops a general proof-producing framework for translating finite, quantitative mathematical arguments into intuitionistic primitive recursive arithmetic (iPRA).

Repository close-out head: `210616e660a7ab5f0d706761c12bba673174cec9`.

## Start here

- `paper/cbip_framework.pdf` - complete report.
- `paper/cbip_framework.tex` and `paper/sections/` - editable LaTeX.
- `lean/NormalizedTraceReflection.lean` - a no-placeholder candidate for the small normalized trace-reflection kernel.
- `lean/CBIPBlueprint.lean` - source-oriented definitions and theorem signatures for bounded games, relational viability, and the compiler.
- `lean/FORMALIZATION_PLAN.md` - dependency-ordered route to checked `Prf PRAAx` theorems.
- `code/cbip_kernel.py` - exact reference algorithms.
- `code/test_cbip_kernel.py` - regression tests.
- `metadata/theorem_ledger.csv` and `metadata/difficulty_matrix.csv` - claim and obstacle status.
- `metadata/source_audit.md` - audited repository snapshot and prior-art boundary.

## Main contribution

Earlier ProveIt packets already describe finite observations, relational witnesses, precision DAGs, and contract compilers. This package isolates and develops the missing common denominator:

1. a typed fixed-program intermediate language of bounded mathematical interactions;
2. a two-stage compiler separating local normalization from a tiny object-level reflection kernel;
3. dual finite strategy certificates for arbitrary fixed bounded quantifier alternation;
4. finite-use relational composition and stable/quotient witness erasure;
5. direct reuse of the checked `IPRADerivations` arithmetic, pairing, search, and induction infrastructure;
6. explicit barriers preventing accidental claims of exact choice, convergence rates, or Diophantine cutoffs.

## Exact status

- Human mathematical proofs: complete for the generic theorem schemas stated in the report.
- Python: exact tests executed successfully; see `verification/test_output.txt`.
- PDF: compiled, rendered, and inspected; see `verification/`.
- Lean: not compiled in this runtime. `NormalizedTraceReflection.lean` intentionally contains no `sorry`; the larger blueprint marks unfinished proof-producing compiler steps explicitly.
- No general Faltings, Siegel, Mordell-Weil, Chebotarev, exact Puiseux selector, or unrestricted sign/branch selector is claimed.

## Reproduce

From the package root:

```sh
bash build.sh
```

The script runs Python tests and compiles the PDF with `latexmk`. Lean verification requires placing `lean/` inside a checkout of the pinned ProveIt repository and following `lean/FORMALIZATION_PLAN.md`.
