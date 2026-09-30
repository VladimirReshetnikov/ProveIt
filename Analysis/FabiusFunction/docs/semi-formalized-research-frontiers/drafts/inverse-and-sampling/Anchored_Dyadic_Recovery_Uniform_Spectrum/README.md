# Anchored Recovery of the Dyadic Uniform Spectrum

A research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Main results

For sums of independent centered uniforms with decreasing summable half-lengths,
the inverse modulus anchored at the exact dyadic spectrum a_j = 2^(-j) is

    exp[-Theta(sqrt(log(1/epsilon)))].

This holds for total variation and Kolmogorov distance. The lower construction
preserves the predecessor's exact variance and all its derivative bounds, and
remains geometrically separated for any fixed ratio rho > 1/2. Every fixed
leading prefix, in contrast, is locally Lipschitz-stable under only a common
support bound on the unknown entire spectrum. The article also proves a
matching-order testing sample-complexity theorem and honest confidence-set
contraction at the reference.

The exponent 1/2 is sharp. The leading stretched-exponential constant is not
determined. The pairwise modulus, the exact-support-endpoint restriction, and
the separation boundary rho = 1/2 are left open.

## Contents

- article.tex and article.pdf: self-contained article, complete proofs, references,
  explicit error formulas, numerical tables, proof audit, and nine further questions.
- code/verify.py: exact rational regression checks and separately labeled
  high-precision diagnostics.
- data/: recorded verification output and CSV evaluations of the analytic bounds.
- notes/proof_audit.md: sensitive proof steps and limitations.
- notes/sources.md and notes/provenance.json: repository snapshot, source identity,
  source-question mapping, and primary literature.
- notes/validation.json: build and PDF validation record.
- requirements.txt, Makefile, SHA256SUMS: reproduction helpers and file integrity.

## Build

From this directory, run:

    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

Alternatively run `latexmk -pdf article.tex` or `make pdf`. No shell escape,
Python execution, network access, or separate bibliography processor is needed.
The standard TeX packages listed in the preamble must be installed.

For the computations:

    python -m pip install -r requirements.txt
    python code/verify.py

The script resolves output paths relative to itself. It can also be invoked by
absolute path from another directory. It regenerates the four data files.

## Verification status

The recorded run passed 949 finite exact-arithmetic checks. The high-precision
root computations and decimal evaluations are diagnostics, not interval
certificates. A displayed TV upper bound is not an actual TV distance obtained
by numerical quadrature. The mathematical assertions for all n rely on the
written proofs, not extrapolation from finite tests.

The manuscript is an unrefereed, AI-assisted conventional mathematical proof.
It is not Lean- or Rocq-checked; no formal build was performed. Exhaustive
literature priority has not been established. No repository file was modified.

## Relation to ProveIt

The specific predecessor is Recovering_Uniform_Factors_Fabius_Rvachev/article.tex
in the inverse-and-sampling research collection. The pinned repository commit is
39472967ce67566d7c530fd5b8d6a3a95e68fe22. See notes/sources.md for the full path
and the exact questions addressed. This article does not claim to originate
qualitative identifiability of uniform-convolution spectra.
