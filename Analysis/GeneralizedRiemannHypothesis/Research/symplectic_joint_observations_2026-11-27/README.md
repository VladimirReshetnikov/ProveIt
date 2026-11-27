# Hidden higher-order dependence in symplectic observations

**Complete research packet — 27 November 2026**

Start with `paper.pdf`. Its complete source is `paper.tex`.

## Main result

For independent uniformly sampled frames with arbitrary prescribed alternating forms in a symplectic space of dimension `2n` over `F_q`, the paper proves:

1. An exact joint law for all pairwise cross-Gram matrices, including the dimension of the combined relation space.
2. An exact constructive feasibility criterion: if the full Gram matrix has rank `2s` and its radical intersects block `i` in dimension `t_i`, the minimum ambient symplectic dimension is `2(s + max t_i)`.
3. Explicit total-variation bounds showing a sharp threshold at total frame dimension `D = 2n`, with exponentially small tails in the balanced regime.
4. Exact independence for observations indexed by any forest.
5. For every fixed `k >= 3`, a family in which every proper frame marginal is exponentially close to independent uniform matrices, but the full joint observation is almost perfectly distinguishable from independence.

A concrete binary example gives three pairwise independent 40 by 40 matrices, each within 0.00000159 of a uniform matrix, whose joint distance from three independent uniform matrices is greater than 0.99999809. Their distance from the product of their own marginal laws is greater than 0.99999332.

These theorems are unconditional finite linear algebra. They extend the frame-statistics branch of the ProveIt GRH project; the proofs do not need an analytic GRH assumption. The complete written proofs are in the paper. The new results have not been formalized in Lean.

## Repository and novelty scope

Pinned ProveIt commit: `6d284fcf75bc3a91bb2e79ba7636f94724bff62c`.

The specific starting points are `spn:thm:complete-law` and the correlated-observation question under `spn:q:symplectic`. The inspected existing material treats two-frame laws extensively. The paper distinguishes that material and relevant external random-matrix literature from the proposed several-frame extension. Worldwide priority has not been established. One incoming archive could not be retrieved; see `SOURCE_AUDIT.md` for its exact name and the coverage limit.

## Contents

- `paper.tex`, `paper.pdf`: complete paper, proofs, references, and computational table.
- `code/exact_law.py`: reusable exact likelihood and bound evaluator. Uses the polynomial kernel count.
- `code/exhaustive_check.py`: independent actual-frame enumeration and direct Möbius-sum comparison.
- `code/cross_check_implementations.py`: checks the reusable implementation against all saved exact observations.
- `code/independent_moment_check.py`: independent enumeration of the first kernel moment, including degenerate and nondegenerate individual forms.
- `code/make_figure.py`: reproduces the scientific figure of certified bounds.
- `results/`: full pointwise integer counts, exact fractions, summary, and plotting data.
- `figures/`: PDF and PNG figure. It displays bounds, not empirical estimates of exact distances.
- `SOURCE_AUDIT.md`, `sources/manifest.json`: source scope, prior-art comparison, pinned URLs, and retrieved-source hashes.
- `FORMALIZATION_PLAN.md`: a proposed Lean development plan, without unchecked placeholder proofs.
- `review/`: mathematical review notes from separate derivations within this session; these are not external peer review.
- `BUILD_VERIFICATION.txt`: document build and validation record.
- `SHA256SUMS`: checksums of the delivered packet members other than itself.

## Reproduce

Python 3.10 or newer is sufficient for core computations. Only the figure generator additionally needs Matplotlib.

```bash
python3 code/exhaustive_check.py
python3 code/cross_check_implementations.py
python3 code/independent_moment_check.py > results/independent_moment_results.json
python3 code/exact_law.py --q 2 --n 50 --dimensions 40 40 40
python3 code/make_figure.py
```

Compile with a complete TeX Live installation:

```bash
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

Alternatively, `tectonic paper.tex` performs the necessary reruns automatically when its TeX bundle is available. The delivered PDF was compiled with pdfLaTeX.

To evaluate one observed full Gram matrix, supply its entries as a JSON array:

```bash
python3 code/exact_law.py --q 2 --n 1 --dimensions 1 1 1 \
  --matrix-json examples/triangle.json
```

Counting formulas apply to all prime-power `q`. Matrix elimination and exhaustive enumeration in these scripts intentionally support **prime fields only**. Modulo `p^a` arithmetic is not used as a substitute for extension-field arithmetic.

## Verification status

The independent frame enumerator covered 733,531 actual tuples, 753 complete candidate observations, and 83 nontrivial forest marginals. Every formula, support criterion, and bound passed. The second likelihood implementation matched every candidate observation. The additional moment checker covered 60,685 matrices in 23 form configurations. These are finite implementation checks; the paper supplies the proofs in arbitrary dimension and characteristic.

The paper determines the transition and its tails. It does not give a universal exact limiting profile within the bounded critical window, and it does not claim the rank test is optimal at every finite size for every degenerate frame type.
