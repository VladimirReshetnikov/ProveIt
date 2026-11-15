# Faltings' theorem and intuitionistic PRA

**This package does not prove general Faltings in iPRA.** It provides a
precise analysis of the missing positive height-bound theorem, complete
constructive special cases, and a compiled Lean foundation. It makes no
independence or unprovability claim.

## Main results

- A positive uniform iPRA proof of height-boundedness for squarefree monic
  quintics would yield a primitive recursive effective Mordell algorithm,
  by arbitrary-matrix intuitionistic witnessing.
- Complete finite lists and height bounds are constructively equivalent
  for the explicitly coded rational-point predicate.
- An explicit bound on the **number** of points does not by itself give
  a height bound or a stopping criterion for finding the points.
- The Fermat quartic `X^4 + Y^4 = Z^4` has exactly the four rational
  projective points `[1:0:1]`, `[-1:0:1]`, `[0:1:1]`, `[0:-1:1]`.
  The report gives the full primitive recursive finite-descent argument.
- The smooth completions of `y^2 = -(x^(2g+2)+1)`, `g >= 2`, have no
  rational points; the arithmetic contradiction is checked in Lean.

## Contents

| Path | Purpose |
| --- | --- |
| `faltings_ipra.tex`, `faltings_ipra.pdf` | Main report and compiled version |
| `sections/fermat_instance.tex` | Complete quartic descent proof |
| `lean/FiniteSearch.lean` | Checked generic finite-list and bound equivalence |
| `lean/Logic.lean` | Checked double-negation and finite-prefix distinctions |
| `lean/Curves.lean` | Concrete quintic definitions, bounded search, exact correctness, and the unproved general target |
| `python/bounded_points.py` | Exact search **only below a supplied height bound** |
| `python/verify.py` | Independent finite arithmetic cross-checks |
| `tools/verify_lean.py` | Reproduce compiler and kernel-dependency audits |
| `tools/build_pdf.py` | Rebuild PDF with an ordinary or private TeX format |
| `verification/` | Build and validation evidence |
| `provenance/` | Sources and pinned repository audit |
| `SHA256SUMS` | Delivered-file checksums |

## Verification

The three Lean modules compiled with Lean 4.32.0 and only `Std`.
No `sorry`, custom axiom, or `Classical.choice` occurs in the audited
results. Generic search uses `propext`; concrete box lemmas also use
`Quot.sound` through standard-library lemmas. Logical distinctions and
the sign contradiction have no axiom dependencies.

These are **native Lean theorems**, not constructed `Prf PRAAx` objects.
The report gives explicit induction invariants and a plan to build the
embedded proofs. The general `QuinticHeightGoal` is only a definition;
the supplied code does not prove it or assume it as an axiom.

The Python checks compare two independent finite-search algorithms on
four polynomials at five bounds. They do not certify the absence of
points above a search cutoff.

## Reproduce

From the `lean` directory, with Lean 4.32.0 available:

```sh
lake build
```

From the package root:

```sh
python3 tools/verify_lean.py
python3 python/verify.py
python3 python/bounded_points.py --bound 12
python3 tools/build_pdf.py
```

An alternative ordinary TeX build is `latexmk -pdf faltings_ipra.tex`.
The LaTeX source requires the included `sections` directory.

## Repository and research scope

Inspected ProveIt revision:
`d72c8b24637e342816dc92d11bef337748683e51`.
Relevant repository modules and draft archives were read and their
provenance recorded. The repository foundation was not rebuilt as part
of this package, and the audit was not an exhaustive read of ProveIt.
No upstream repository files were modified.

Sources checked on November 15, 2026 include Stoll's ICM 2026 account,
the arbitrary-matrix witnessing theorem presented by Ferreira--Marques,
the 2026 Yu--Yuan--Zhou cardinality estimates, and the effective results
and conditional algorithms cited in the report.
