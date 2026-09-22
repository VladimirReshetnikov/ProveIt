# A Spectral–Integral Classification of Surcomplex Unitary Differential Systems

Research manuscript prepared for Vladimir Reshetnikov, September 21, 2026.

## Main result

Fix the Berarducci–Mantova derivation ∂ on No, normalized by ∂ω = 1,
and put K = No[i]. Let I = ∂O be the real coefficients with finite
primitives. For a real surreal b, define Ψ(b) to be the purely infinite
part of any primitive of b; this does not depend on the integration constant.

For every ordinary finite Hermitian matrix H over K, the manuscript proves
that the complete differential phase spectrum of ∂y = iHy is the multiset
{Ψ(λ₁(H)), …, Ψ(λₙ(H))}. A unitary gauge reduces the system exactly to
∂z = i diag(∂p₁, …, ∂pₙ) z, with these phases pⱼ. Neither commutation nor
a spectral gap is assumed. See Theorem 7.1.

Consequences include a sharp finite-primitive perturbation theorem,
normalized non-Abelian integration, a classification of positive invariant
metrics, a real Ermakov–Pinney existence/uniqueness dichotomy, exact Airy
Hahn expansions, and finite phase-lattice Galois tori. The full article
contains proofs and carefully distinguishes established results from the
candidate contribution.

## Research status

The proposed new contribution is the precise arbitrary-dimensional
Hermitian spectral–integral formula and its matrix consequences. A targeted
literature search did not locate an exact prior statement; this is not an
exhaustive priority determination. No named published open problem is
claimed solved. The proofs are not independently refereed or proof-assistant
verified.

The Berarducci–Mantova derivation and the Aschenbrenner–van den Dries–van der
Hoeven existence and transfer theorems are explicitly imported. Rank-one
phase obstructions and universal exponential extensions are prior coverage,
not claimed as new. Recent amplitude–phase literature and the classical
Pinney formula are cited as antecedents of the second-order consequences.

The repository comparison is pinned to:
aa846271b4dcae2c055b216126a87210292ec19b

## Contents

- `article.pdf`: the compiled 27-page article.
- `article.tex`: standalone LaTeX source with an internal bibliography.
- `code/verify_examples.py`: exact symbolic verification of finite examples.
- `data/verification.json`: recorded execution report, 62 checks passed.
- `requirements.txt`: pinned dependency used for the verification script.

## Rebuild the article

With a standard TeX Live installation and latexmk, from this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

No external bibliography, images, or custom font files are needed.

## Re-run the exact example checks

With Python and SymPy installed:

```sh
python -m pip install -r requirements.txt
python code/verify_examples.py
```

The script regenerates `data/verification.json`. Its checks include exact
matrix gauges and metric identities, a deliberate counterexample to a
nonnormal spectral formula, a noncommuting exponential defect, polynomial
first integrals, the Airy coefficient recurrence and truncation residual,
and the Pinney metric/symplectic identities. They do not certify the
arbitrary-support arguments or the general theorems.
