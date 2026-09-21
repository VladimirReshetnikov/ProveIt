# Finite Infinitesimal Fibres in Surcomplex Analysis

**Uniform-Support Division, Conservation of Multiplicity, and Multiscale Zero Clusters**  
Research manuscript, September 21, 2026.

## Contents

- `surcomplex_finite_fibres.tex`: self-contained LaTeX source, including references.
- `surcomplex_finite_fibres.pdf`: compiled, 31-page article.
- `verify_examples.py`: exact symbolic verification of the worked example and finite tests of the explicit Koszul contraction.
- `verification_report.txt`: output of the verification script; 29 named checks passed, including a group of contraction tests on 49 monomials in all chain degrees.
- `build.sh`: build the article and rerun its example checks.

## Principal results

Theorem 4.1 constructs support-controlled division and a finite free quotient for an arbitrary positive-support Hahn perturbation of an isolated formal complete intersection. Its polynomial basis is the same as that of the leading quotient. The integral quotient is free as well.

Theorem 6.4 identifies the quotient with all actual infinitesimal zeros, counted with their local fine-analytic intersection multiplicities. The sum of those multiplicities is exactly the leading colength. No additional roots appear outside the algebraically closed Hahn workspace containing the data.

Theorem 7.1 gives finite fibres of constant total multiplicity over every infinitesimal target; Corollary 7.2 gives a fine-analytic inverse on the whole monad when the leading Jacobian is invertible.

Theorem 9.2 proves a stronger common-polydisk division statement for monomial leading systems, preserving ordinary holomorphic parameters and the original domain of every coefficient.

Theorem 10.2 gives a perfect coefficientwise torus-residue pairing. Section 11 computes a coupled four-point example in which a triple collision is split by a scale smaller than every power of the first infinitesimal, and proves a complete moving-residue formula for that example. A nonpolynomial six-point application follows.

## Scope and novelty

This is a research continuation of the user-supplied exposition `surcomplex_analysis(3).tex`. It addresses that exposition's multivariable division and finite-mapping research target; it does not claim to resolve a named published conjecture.

The exact combined uniform-support statements are candidate new results. Their proofs use acknowledged classical inputs: Hahn–Neumann summability, algebraic closedness of divisible Hahn fields, regular sequences and Koszul resolutions, and a specialization of the homological perturbation lemma. No exhaustive priority review, independent peer review, or proof-assistant verification is claimed.

The general theorem is formulated in the uniform-support monad algebra C[[z]]((t^Gamma)), not in K[[z]]. The distinction is essential: z^2-t is a unit in K[[z]], but its inverse has inadmissible decreasing Hahn support in the monad algebra. The fixed-polydisk theorem has the additional, explicit monomial-leading hypothesis. The article does not silently extend that common-domain conclusion to every formal leading system.

All infinite sums are justified by strong Hahn summability. No sequence of ordinary partial sums is asserted to converge in the full surcomplex fine topology.

## Reproduction

A standard TeX Live installation with the packages named in the source is sufficient. The bibliography is embedded; no external `.bib` file is needed.

Preferred PDF build:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error surcomplex_finite_fibres.tex
```

Alternatively, run `pdflatex` three times. The included `build.sh` selects either method.

The verification script requires Python 3 and SymPy. Run:

```sh
python3 verify_examples.py
```

The recorded checks used SymPy 1.14.0 and exact symbolic arithmetic. The variables `t` and `s` remain algebraic indeterminates; the script does not approximate surreal numbers numerically. The interpretation of s as the Conway monomial omega^(-Omega) and all infinite-support assertions are justified by the proofs, not by the script.
