# Finite Separators and Discriminant Factorizations for Sextic Block Resolvents

Research article prepared for Vladimir Reshetnikov, September 28, 2026.

## Main mathematical results

The article develops an explicit bounded replacement for the separating-invariant
search in the ProveIt sextic radical-solvability development. It proves:

* A single parameter among **1 through 196** simultaneously separates the fifteen
  pair partitions and ten triple partitions of every sextic with distinct roots
  in characteristic zero. It matches the existing descriptor interface through
  `x(0) = 2*t^2`, `x(1) = t`.
* The compressed invariants are quadratics `h_P(t)` and linears `k_T(t)`.
  Their bad parameters are exactly the roots of `E_f = Q_f U_f L_f`, with
  degrees at most 30, 120, and 45.
* Exact identities hold:
  `disc_Z(R_2) = disc(f)^6 Q_f^6 U_f^2` and
  `disc_Z(R_3) = disc(f)^3 L_f^2`.
* In the generic sextic coefficient field, the three factors are irreducible,
  have those exact parameter degrees, and have a squarefree product. Thus the
  196-point guarantee is **sharp for arbitrary nonzero complex test sets**.
  This does NOT establish that the initial integer interval cannot be shortened.
  For that distinct problem the article proves only `8 <= N_int <= 196`.
* The bounded separator leads to a coefficient-only primitive-recursive decision
  architecture. A second construction gives a height-dependent separator with
  no search. The article includes a source-level integration plan and twelve
  further research questions.

## Status and scope

This is an unrefereed article with complete written proofs, exact symbolic checks,
and an explicit modular certificate. The new results were not run in Lean or
Rocq, and no repository rebuild or source modification was performed.

General decidability, even polynomial-time decidability, of solvability by
radicals is classical (Landau and Miller, 1985). It is not claimed as new.
The specific separator, collision factorization, and generic irreducibility
results are proposed contributions relative to the inspected repository.
An exhaustive historical priority search has not been completed.

The Python files are an exact verifier and a root-level prototype, NOT a complete
coefficient-only solver and NOT an extraction of a formal proof. Expanded
universal resolvent coefficient tables are not included. Their finite symbolic
construction is specified in the article.

## Files

- `article.pdf`: compiled 24-page article.
- `article.tex`: self-contained LaTeX source, including bibliography.
- `build.sh`: PDF build script.
- `code/verify.py`: combinatorial enumeration, four universal symbolic identities,
  exact discriminant and descriptor checks, and exhaustive finite examples.
- `code/sharpness_certificate.py`: a standard-library modular certificate generator
  and checker for a sextic with exactly 195 distinct nonzero bad complex parameters.
- `checks/verification.json`: complete output from `verify.py`.
- `checks/sharpness_certificate.json`: all coefficients in the modular Bezout
  identity `A*E + B*E' = 1 (mod 1000003)` for roots `(1,4,10,23,51,109)`.
- `checks/environment.json`: software versions and execution status.
- `requirements.txt`: the SymPy version used for the local symbolic checks.
- `SHA256SUMS`: checksums for the packaged files other than this checksum file.

## Build the PDF

A TeX distribution with `pdflatex`, `newtx`, `microtype`, `tcolorbox`, and the
other packages named in the preamble is required. From this directory:

```sh
./build.sh
```

On Windows, run the commands in `build.sh` using a suitable shell or run
`pdflatex` on `article.tex` three times manually. No BibTeX or Biber step is
needed. The build script uses `.build/` for intermediate files and copies the
finished PDF to `article.pdf`.

## Reproduce the exact checks

Python 3.10 or later is suitable for the scripts. The recorded run used
Python 3.13.5 and SymPy 1.14.0.

```sh
python -m pip install -r requirements.txt
python code/verify.py
python code/sharpness_certificate.py
```

Run without Python's `-O` optimization flag, because the test suite uses assertions.
The second script itself needs no SymPy. Importing `verify.py` does not load
SymPy or execute the first script's test suite.

The executed checks include 68 exact parameter cases, each checking both
resolvent discriminant identities, 60 exact root-transposition symmetry cases,
all 462 six-element subsets of the integer interval [-3,7], and 20 fixed-parameter
counterexamples. The modular certificate separately verifies degree 195,
nonzero constant coefficient, and coprimality with the derivative over a
trial-division-checked prime field. These are exact finite checks, not
floating-point tests.

## Repository snapshot and references

The inspected snapshot is:

`e2b1f016a94102663f12b970e6dd434229f90d01`

Repository: https://github.com/VladimirReshetnikov/ProveIt

Relevant files are under
`Algebra/PolynomialFormulas/Lean/PolynomialFormulas/`:
`SexticSeparatingInvariants.lean`, `SexticIrreducibleDecision.lean`,
`SexticReducibleDecision.lean`, `SexticRadicalComputability.lean`,
`SexticRadicalSemantics.lean`, and `SexticRadicalDecision.lean`.

The bibliography contains pinned links and primary literature references.
Later repository states may differ from the inspected snapshot.
