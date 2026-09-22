# Nonabelian Support Obstructions in Surcomplex Analysis

## Article

**Nonabelian Support Obstructions in Surcomplex Analysis: A Sharp Matrix Cousin
Criterion and Arbitrarily Deep Unipotent Examples**

Research continuation dated September 21, 2026.

The article gives full proofs of an exact global support criterion for positive
Hahn-valued matrix gluing on puncture-and-disk covers of open Riemann surfaces.
It constructs a rank-three obstruction invisible in the raw singular support and
in the abelianized cocycle, and examples at arbitrarily deep nilpotent levels.
It also develops support-controlled matrix and deformation rigidity on Stein
manifolds.

## Precise scope

The coefficient sheaf is the common-domain integral Hahn sheaf
`I_Gamma(V) = O(V)((t^Gamma))_{>=0}`. Transition matrices have ordinary reduction
identity, or a specified ordinary vector-bundle reduction in the deformation
theorem. The set-sized ordered value group may be non-Archimedean.

For a subgroup of the surreal numbers, `t^gamma = omega^(-gamma)` gives the
surcomplex interpretation. All infinite algebra uses well-ordered supports and
finite coefficient multiplicity, not convergence in the fine surreal topology.

Nontriviality is proved for the integral coefficient sheaf, even after forgetting
the flag and reduced framing. The article does **not** claim that these examples
remain nontrivial after all monomials are inverted and arbitrary negative-valuation
matrix changes of frame are allowed.

## Novelty and verification status

The exact global matrix criterion and the explicit nonabelian hierarchy are
proposed new results in this precise framework. The local Birkhoff/Atkinson-type
factorization mechanism, Neumann support calculus, and ordinary analytic
cohomology inputs are established mathematics and are credited separately.
The literature check was targeted and does not certify priority. No named
published conjecture is claimed solved.

The arguments are not refereed or proof-assistant verified. The companion code
checks exact finite algebra only; it does not establish an infinite support
obstruction, an analytic existence theorem, or novelty.

## Contents

- `article.tex`: standalone LaTeX source with internal bibliography.
- `article.pdf`: compiled article.
- `code/verify.py`: exact symbolic verification program.
- `data/verification.txt`: recorded output, 2,899 exact checks passed.
- `requirements.txt`: version used for the symbolic checks.
- `Makefile`: build, test, and cleanup commands.

## Build

A standard TeX Live installation with latexmk and pdfLaTeX is sufficient.
The source uses standard packages, has no external graphics or bibliography
file, and requires no separately distributed fonts.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

## Run the finite checks

The recorded run used Python 3.13.5 and SymPy 1.14.0. The code requires Python
3.10 or later.

```sh
python -m pip install -r requirements.txt
python code/verify.py
```

To update the output file:

```sh
python code/verify.py > data/verification.txt
```

The checks cover rank-three factorization and repair, the logarithm diagnostic,
chain identities through rank 10, rational-exponent matrix recursion through
cutoff 3, holomorphic right-gauge invariance, two-sided inversion, finite
exponent formulas, and an exact four-puncture splitting. There are no
floating-point comparisons in the checked identities.

## Repository provenance

Repository: https://github.com/VladimirReshetnikov/Surreal

Inspected commit: `39f2be6667ade51bca2b45daa47e289d69c09764`.

The motivating question is in `docs/surcomplex/global-divisors/article.tex`,
subsection **Further precise directions**, which explicitly identifies the
finite-rank vector-bundle problem and the need for noncommutative support
recursion. `docs/README.md` supplies the report map and ring distinctions.
The article is a standalone continuation; no repository files were changed.
