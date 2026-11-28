# The radical-square invariant for geometric-progression-free polynomial sets

Research note, 27 November 2026. Intended as a standalone packet for the ProveIt GeneralizedRiemannHypothesis article (Part IV, finite coefficient rings).

## Contents

- `paper.tex` — complete LaTeX source.
- `paper.pdf` — compiled 8-page mathematical paper, with full proofs and bibliography.
- `check.py` — dependency-free Python 3 exhaustive checks for the exact square-start obstruction and disjoint progression packing in six finite rings (degree cutoff 3). Also verifies the opposite-limit example's exact parameter sums.
- `checks.txt` — actual output of `python3 check.py`.
- `SOURCE_AUDIT.md` — inspected repository files, blob identities, relation to existing results, and scope limitations.
- `SHA256SUMS` — integrity hashes for the six preceding files.

## Main results

For a finite commutative local ring A with maximal ideal m, residue field size q even, and |A|=Q, assume 2m=0 and m annihilates every square of an element of m. Let S={a²:a∈m}. In particular the hypotheses hold for every characteristic-two local ring with m³=0.

1. An exact criterion and count for starts of square-ratio pairs in a finite degree ball with nonzero residue. For m³=0, every such start belongs to an actual three-term progression in the ball with ratio reducing to x.
2. For every fixed L≥2 (two positive exponent gaps with sum at most L), write Δ_L for the extremal upper density. With w=|S|/Q², the density loss is between (1−1/q)² w and w.
3. For a growing product of eligible local rings, the limit of the extremal upper densities is positive if and only if ∑ w_i is finite. Explicit product bounds and uniform endpoint criteria are given.
4. There exist sequences of characteristic-two cube-zero local rings with identical size and radical-layer dimensions factor by factor, but with opposite limiting densities. The Frobenius-semilinear square-map rank distinguishes them.

## Reproduction

```
python3 check.py
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
sha256sum -c SHA256SUMS  # run before rebuilding if checking distributed bytes
```

The mathematical proof does not depend on the finite tests. The product criterion uses the classical density Hales–Jewett theorem. The result answers the characteristic-two cube-zero case of the repository's open question `gpp:q:cube`; it is not a full solution of Asada et al.'s Question 6.5 for arbitrary finite rings. No upstream Lean build or Lean formalization of this new result was run. No repository contents were modified. Global publication priority is not certified.
