# Finite Resonance Certificates and Sharp Analytic Normalization for Hahn–Fuchsian Systems

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Read

- `hahn_fuchsian.pdf`: the compiled 24-page A4 article.
- `hahn_fuchsian.tex`: standalone editable LaTeX source, with embedded bibliography.
- `verification/verify.py`: exact finite matrix computations and numerical crossover checks.
- `verification/results.json`: the recorded successful verification run.
- `notes/proof_audit.md`: mathematical hypotheses and verification boundaries.
- `notes/repository_provenance.json`: pinned repository sources and inspection scope.
- `notes/build_report.json`: compilation and rendering checks.

## Main results

The system is `x Y' = (A0 + A+(x)) Y`, with real-spectrum constant matrix A0
and positive, well-ordered real Hahn exponents. Supports need not be locally finite.

The central result (Theorem 6.2) is an equivalence: every absolutely convergent
coefficient series supported in a fixed exponent semigroup has an absolutely
convergent normalized gauge if and only if the nonresonant exponents stay
uniformly separated from the eigenvalue differences. Failure occurs precisely
when a positive spectral difference is a left accumulation point. Counterexamples
can be arbitrarily small and proportional to one square-zero rank-one matrix.

The formal normal form yields a finite nilpotent matrix B. The dimension of the
solution space of logarithmic degree at most d is dim ker(B^(d+1)). Its entries
depend polynomially on finitely many original coefficients, even when infinitely
many exponents lie below the largest resonance.

An explicit family with exponents 2-1/n and coefficients n^(-p) has a convergent
formal normalizer exactly for p>2, although a renormalized analytic solution exists
and realizes every finite asymptotic prefix for all p>1. A uniform crossover at
N proportional to log(1/x) has an explicit Euler–Maclaurin error certificate.

Ten further research directions are developed in Section 11.

## Scope and novelty

The article supplies conventional mathematical proofs, not a Lean formalization.
The classical Fuchsian normal-form architecture and the repository's earlier
finite-residue-obstruction work are acknowledged. The proposed additions are the
sharp analytic criterion, finite-ancestry formulation, explicit threshold example,
and certified crossover. The literature check was targeted, not exhaustive; no
independent peer review or general breakthrough claim is asserted.

The universal convergence theorem quantifies over all inputs supported in the
whole semigroup, not merely an arbitrarily specified proper generating subset.
Divergence refers to the normalized Hahn expansion, not nonexistence of analytic
solutions of the differential equation.

## Build the PDF

Run from this directory:

```sh
sh build.sh
```

A standard TeX Live installation with `pdflatex` and the packages named in the
preamble is sufficient. The build uses three passes. No bibliography processor,
repository checkout, private fonts, or network access is required.

## Reproduce the checks

```sh
python -m pip install -r verification/requirements.txt
python verification/verify.py
```

The recorded run used Python 3.13.5, SymPy 1.14.0, and mpmath 1.3.0, with seed
20260929. It reports 33 exact finite gauge systems, 292 exact coefficient checks
including scalar counterexample checks, and 36 crossover parameter cases, all
passing. Numerical checks use 85-digit working precision, not interval arithmetic.
The theorem-level error bounds are proved in the article.

The code is a finite rational-exponent implementation. It does not decide resonance
for arbitrary real or infinite support presentations and does not verify the
infinite-support theorems in a proof assistant.

## Provenance

Repository: VladimirReshetnikov/ProveIt.
Pinned snapshot: `04473354a0f3edff2d6c365caf26170ca6b88735`.

Selected repository documentation and Lean modules were read through the connected
GitHub tools. The canonical large TeX volume exceeded the connector's content limit;
this package does not claim a complete line-by-line audit of that volume or repository.
No repository files were changed.
