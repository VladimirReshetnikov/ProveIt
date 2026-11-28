# How theta lifts locate the zeros of Dirichlet L-functions

A 79-page mathematical guide to the proof of the Riemann hypothesis and the generalized Riemann hypothesis for Dirichlet characters by Levent Alpöge with Claude. This edition expands the supplied 60-page revised guide. The remaining higher-rank groups and their special values occur inside the proof. The downloadable PDF has a linked contents page, subsection bookmarks, internal cross-references, and links into the readable Lean source.

## Reading routes

| Interest | Where to start |
| --- | --- |
| The argument in outline | Page 3 starts with the divisors of 924. Pages 56–61 carry out the volume comparison. Pages 62–67 explain why it excludes an off-line zero. |
| The inspiration for the construction | Pages 9–16 connect Stepanov multiplicity, a finite Fourier calculation on a path, the Nyman–Beurling criterion, and the de Bruijn–Newman deformation. |
| What a prime does to a derivative | Pages 21–23 compute a differential operator on one elliptic curve, then use the formal parameter to explain the odd Frobenius exponents in the proof. |
| Which forms survive projection | Pages 32–36 describe the finite-field labels and work through 72 pairs over the field of five elements. |
| The hardest coefficient to match | Pages 42–45 show how the squared special-value product recovers the ordinary-direction cost. Pages 57–58 derive the centering constant twice and show where the compensating power of the level enters. |
| Why congruences can be tolerated | Pages 48–52 identify the coefficient that controls the determinant, demonstrate what a weak lift detects, and show how a single operator can clear every eigenline. |
| Why one-sided control is enough | Pages 62–75 follow a possible zero into the smoothed prime remainder, explain how a quadratic twist keeps its pole visible, and derive a conditional deficit for an ordinary prime count. |
| Formal scope and independent checks | Section 20 begins on page 75. The notation guide is on page 79. |

## Contents

- **theta_lifts_and_dirichlet_zeros.pdf** is the typeset guide.
- **theta_lifts_and_dirichlet_zeros.tex** is its self-contained LaTeX source. The diagrams are built from this file.
- **source-index.html** links 253 section references to 243 distinct declarations in 83 Lean files. Open it locally in a browser.
- **source-map.tsv** contains the same index, including full paths, line numbers, Git blob identifiers, and immutable links.
- **check_sources.py** verifies every entry against the readable package.
- **check_examples.py**, **check_lifts.py**, **check_torsion.py**, and **check_analytic.py** check the inherited examples of prime weights, rank and dimension, finite-field point counting, cyclotomic valuations, and residues.
- **check_local_models.py** checks the derivatives at 3 and 5, the odd prime-power differences, and the finite Fourier path counts.
- **check_good_types.py** enumerates the allowed polynomials and their representation weights.
- **check_denominators.py** checks the weak-lift, relation-lattice, and residue-field examples.
- **check_twists.py** checks the pair correlations and the exceptional-prime exponent exactly, and tests the Gaussian inversion numerically in conductor 7.

The finite Fourier calculation, the elliptic curve over the rationals with complex multiplication by i, the auxiliary examples over small finite fields, and the conditional quantitative excursion are explanatory calculations in the guide. They illustrate specific transitions. The PDF identifies the theorems used in the formal proof and gives Alpöge’s source for the discovery chronology.

## Rebuild and reproduce

Run this command from the extracted archive with a standard TeX Live installation.

```sh
latexmk -pdf -halt-on-error theta_lifts_and_dirichlet_zeros.tex
```

The eight example scripts need Python 3 and its standard library. Run each with Python, for example `python3 check_local_models.py`. Each exits with a failure on a mismatch.

The source links are pinned to [ProveIt revision d8415e76](https://github.com/VladimirReshetnikov/ProveIt/tree/d8415e76ad850651f8c0083afe689dd9f4a45a10/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh). The readable package has the same Git tree as the [independently checked upstream revision](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh) and as the ProveIt revision used by the supplied draft.

```sh
git clone https://github.com/lsernau/grh-lean.git upstream-grh
git -C upstream-grh checkout --detach 72fead102f663d5c7a407964a13dc0cf9d977207
git -C upstream-grh rev-parse HEAD:grh
python3 check_sources.py upstream-grh/grh
```

The expected tree is `2e133df63d7f4da6b3059c4195324f8e9187ba73`. The index checker should report 253 declaration anchors and 83 Git blobs.

The source comparison, example calculations, PDF compilation, and document checks were performed for this edition. The formal build and independent kernel checks cited in the guide come from [Andrew Sutherland’s verification of the shorter editions](https://math.mit.edu/~drew/shortgrh/). They used Lean v4.35.0 and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. To build the readable Lean package with its dependencies and inspect the axioms of the five public theorems, run the following from its `grh/` directory.

```sh
lake exe cache get
lake build
lake env lean scripts/PrintAxioms.lean
```

The verification records also link the challenge statement, comparator logs, and outputs of independent checkers. Alpöge’s [announcement and discovery notes](https://alpo.ge/remark.pdf) describe the original proof.
