# Certified Zariski Descent in iPRA

Research package prepared for Vladimir Reshetnikov, 15 November 2026.

## Start here

- `paper/ipra_algebraic_geometry_framework.pdf` — complete human-readable report.
- `paper/ipra_algebraic_geometry_framework.tex` and `paper/sections/` — editable LaTeX source.
- `lean/FORMALIZATION_PLAN.md` — dependency-ordered route to actual `Prf PRAAx` derivations.
- `metadata/THEOREM_LEDGER.md` — claim-by-claim status and boundaries.
- `code/zariski_descent.py` — exact finite reference algorithms.

## Main contribution

The existing ProveIt packets already provide finite contracts, demand-driven observations, relational finite-use composition, stable observables, and substantial Diophantine arithmetic. This package adds a proof-relevant algebraic-geometric layer:

1. certified setoids and quotient equality by explicit ideal-combination witnesses;
2. localization equality by explicit killing exponents, valid with zero divisors;
3. an explicit primitive-recursive power-cover constructor;
4. a finite principal-open module-gluing algorithm and uniqueness theorem;
5. finite affine atlases, quasi-coherent descent data, and finite Čech complexes;
6. a complete finite Čech computation of `O(d)` on `P^1` and the standard `P^n` cover.

The central gluing formula starts with a certificate `sum c_i f_i = 1`, compatible local fractions, and overlap annihilation witnesses. It clears all denominators and overlap torsion to one exponent, constructs `sum d_i f_i^q = 1`, and returns the global section `m = sum d_i b_i`. No integral-domain cancellation or prime-ideal search is used.

For `P^n`, the standard Čech complex splits by Laurent exponent vector. All-nonnegative vectors give `H^0`, all-negative vectors give top cohomology, and every mixed-sign summand has an explicit insertion contracting homotopy. The rank formulas are therefore finite weak-composition counts.

## Formal status

The mathematical arguments are fully written in the report, and the central algorithms have exact Python implementations and tests. The Lean files are source-level blueprints. They contain no `axiom`, `sorry`, or `admit`, but they are **not claimed compiler-checked**. No principal theorem in this archive is claimed as an already constructed `Prf PRAAx` value.

The intended final endpoints are actual derivations such as:

```lean
Prf PRAAx [] powerCoverFormula
Prf PRAAx [] principalCoverGlueFormula
Prf PRAAx [] p1OdCechFormula
Prf PRAAx [] pnOdCechFormula
```

Only after such objects exist should the repository theorem `pra_iff_native` transport them to the native calculus.

## What is not claimed

This package does not prove general effective Siegel or Faltings, produce uniform Mordell–Weil generators or rational representatives of arbitrary Selmer classes, decide equality of arbitrary represented reals, construct exact Puiseux branches from arbitrary Cauchy coefficients, or provide a primitive-recursive universal evaluator.

It computes the finite standard-cover Čech complex of `O(d)` explicitly. Agreement with conventional derived-functor sheaf cohomology uses the standard affine-cover comparison theorem; a full internal theory of derived categories is not claimed.

## Reproduce

From the package root:

```bash
python3 -m unittest discover -s code -v
python3 code/zariski_descent.py
bash build.sh
```

`build.sh` runs the Python tests, refreshes the validation output, compiles the PDF with `latexmk`, checks the PDF metadata and text extraction when the corresponding utilities are installed, and writes `MANIFEST.sha256`.

Python 3.10 or later and the standard library are sufficient for the executable companion. The PDF uses ordinary TeX Live packages listed in the master source.

## Repository baseline

- Repository: `VladimirReshetnikov/ProveIt`
- Audited directory: `Logic/PrimitiveRecursiveArithmetic`
- Pinned audit commit: `bce5113f44d613f5625c274128ee761f35486fc5`
- Repository head at the final check: `a2f72b0cdf57f8a3fefd34b272c3d471385e819c`
- Stability check: the `ConciseIPRA`, `README.md`, and `docs` entries under `Logic/PrimitiveRecursiveArithmetic` had the same Git object identifiers at both commits.
- Access: read-only; no upstream files were modified or rebuilt.

The repository README says the proof packets are filed as delivered and have not been independently verified. This package therefore treats their frameworks as prior work but does not inherit their unverified claims as axioms. The later repository commits observed during preparation did not change the audited iPRA subtree. Exact paths, object identifiers, and reuse limits are recorded in `metadata/SOURCE_AUDIT.md`.

## Contents

| Path | Purpose |
|---|---|
| `paper/` | Complete LaTeX source and rendered report |
| `code/` | Exact power-cover, gluing, ideal-certificate, and Čech algorithms |
| `lean/` | Host interfaces, target propositions, and object-iPRA completion plan |
| `metadata/` | Source audit, theorem ledger, limitations, claims, and validation JSON |
| `verification/` | Unit-test, demo, PDF-build, and visual-QA records |
| `build.sh` | Reproducible test/PDF/manifest build |
| `MANIFEST.sha256` | Integrity hashes for delivered files other than itself |
