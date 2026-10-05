# Asymptotics and inverses for A126348

## Results

The article proves a relative all-orders coefficient expansion for
F(q)=product_{k>=1}(1+q^k/(1-q)), using the resummed coordinate
n=e^(2L)(L^2/2+L+pi^2/6). It supplies two explicit relative corrections and a finite exact formula for every further correction, with a remainder O_J(e^(-(J+1)L)(1+L)^(J+1)).

A Jacobi/eta factorization gives a separate exact convergent modular sector expansion for the generating function. Its coefficient amplitudes are finite trigonometric polynomials involving ordinary partition numbers.

An explicit inverse recovers the integer index on the sequence range with o(1) error. A threshold inverse is confined to an eventual two-candidate bracket; a single ceiling requires a separation check. The note does not specify an exact interpolation, coefficient-level exponentially small sectors, or an effective onset.

## Contents

- article.tex and article.pdf: self-contained article
- checks/: producer symbolic derivations, a separately written symbolic reconstruction, exact integer coefficient calculations, high-precision diagnostics, and replay records
- inputs/derivation.md: expanded mathematical derivation
- inputs/source_audit.md: bounded primary-literature and duplicate checks, including the other screened candidates
- inputs/AUDIT.md: independent analytic sign-off
- PROVENANCE.json and SHA256SUMS: source/replay metadata and hashes

The current OEIS entry has no asymptotic formula. Pan and Yu, Algebraic Combinatorics7(1)(2024), Proposition6.10 identifies the generating function as a stable Hilbert series. The primary references and search qualifications are in the article and source audit.

## Reproduction

Python3 with SymPy and mpmath is sufficient for the checks:

    ./run_checks.sh

The scripts are run under python -O and do not rely on assert statements for acceptance. Symbolic identities are checked exactly. Numeric replays are high-precision diagnostics and are not interval-certified numerical onset bounds. Exact coefficient generation through10000 is included.

Build with a normal LaTeX distribution:

    pdflatex article.tex
    pdflatex article.tex

The optional build_local.sh configures writable TeX cache directories for the execution environment used here. Its shell commands only build this local article.

## Review

Root and an independent asymptotic reviewer checked the all-orders argument, modular normalization, Gaussian displacement terms and inverse. The independent reviewer imported none of the producer code. The final article was also checked for transcription and rendered for visual review. No external publication or repository modification was performed.
