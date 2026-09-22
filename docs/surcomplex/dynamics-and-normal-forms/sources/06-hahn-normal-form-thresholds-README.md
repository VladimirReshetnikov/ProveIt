# Exact Hahn Normal Forms in Surcomplex Analysis

**Subtitle:** Integrability, sharp small-divisor thresholds, and support-controlled domains  
**Date:** 21 September 2026  
**Length:** 24 pages  
**Status:** Research manuscript with mathematical proofs and finite exact symbolic checks;
not peer-reviewed and not proof-assistant verified.

## Contents

- `article.pdf`: compiled article with a linked table of contents and bibliography.
- `article.tex`: standalone LaTeX source with an internal bibliography.
- `code/verify.py`: reproducible exact SymPy verification program.
- `data/verification.json`: output of the successful 119-check run.
- `data/build_report.json`: build and verification metadata.
- `requirements.txt`: the SymPy version used for the recorded run.
- `Makefile`: build, test, and auxiliary-file cleanup targets.

## Principal results

**Theorem 5.1 — Exact positive-Hahn Hamiltonian normal form.** A positive
Hahn perturbation of a nonresonant quadratic Hamiltonian, with polynomial
coefficients of phase order at least three, has a uniquely gauge-normalized
Hamiltonian generator. The resulting symplectic map and its inverse are
actually defined on the entire finite surcomplex phase space. Arbitrary
set-sized ordered value groups and well-ordered positive supports are
allowed; no arithmetic estimate on the nonzero divisors is required.

**Theorems 4.2 and 7.1 — Sharp entire-coefficient threshold.** Replacing
polynomial layers by arbitrary entire layers is universally valid exactly
when reciprocal homological divisors have at most exponential growth in
phase degree. An explicit super-Liouville entire perturbation obstructs
ordinary analytic first-order coefficient germs when this condition fails.
The obstruction does not rule out formal or infinitesimal-monad
normalizations in a different coefficient category.

**Theorems 6.1 and 6.2 — Integrability and the Poisson centralizer.** The
constructed actions commute, and every first integral in the entire-
coefficient Hahn algebra is a unique entire-coefficient Hahn function of
those actions. A coefficientwise holomorphic flow for every ordinary
complex time is also constructed.

**Theorem 8.2 — Support-certified infinite-scale domains.** A shifted
monomial-weight certificate gives compatible extensions to valuation
polydisks, including domains with infinite phase magnitudes. Strict
positivity, well-ordering, and finite fibers are distinct requirements.
The article gives failure examples for the omitted hypotheses and a sharp
cubic boundary with an additional critical-point obstruction.

## Build

Use a standard TeX Live installation with the common packages listed in the
preamble:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Repeated `pdflatex` runs are also sufficient. There are no external figures
or `.bib` files. `make pdf` invokes the same build.

## Reproduce the finite checks

Python 3.10 or later is required. The recorded run used SymPy 1.14.0:

```sh
python -m pip install -r requirements.txt
python code/verify.py
```

Expected output begins:

```text
PASS: 119 exact checks through total label degree 4.
```

`make test` invokes the verifier. It uses exact arithmetic in Q(sqrt(2))
and auxiliary rational-function identities, not floating-point tolerances.
The output JSON includes all check names and the computed generator and
normal-form coefficients.

The truncation is by **total degree in independent input labels**, not by
Hahn valuation. It is not a proof of arbitrary-support summability or of
the analytic threshold, centralizer, or rescaling theorems.

## Provenance and novelty

The motivating repository was inspected at commit
`39f2be6667ade51bca2b45daa47e289d69c09764`:
`VladimirReshetnikov/Surreal`. The comparison uses its documentation
catalogue and the foundational analysis README; it is not an exhaustive
full-text audit of every repository manuscript.

Classical formal Birkhoff normalization, non-Archimedean linearization,
and general formal-sum Lie exponentiation are explicitly credited rather
than claimed as new. The proposed contributions are the precise
support-controlled realization, universal coefficient-domain threshold,
centralizer, and rescaling statements. These formulations were not located
in the consulted primary sources, but bibliographic priority has not been
established exhaustively. No named published open conjecture is claimed
solved. See the article for the exact hypotheses and proofs.

All phase derivatives fix the Hahn coefficient field. The article does not
identify them with an intrinsic surreal derivation, infer ordinary analytic
convergence in a complex perturbation parameter, or assert fine-topological
continuity of nonconstant ordinary-time paths in the whole proper-class
surcomplex field.
