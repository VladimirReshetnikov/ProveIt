# Centered moments and adaptive completion in the theta-lift proof

Research note, 27 November 2026.

## Main contribution

From the exact existing moment bounds in the readable Alpöge–Claude proof, derive a centered rank increment, applied directly to the ramified source. Weaken the original rank threshold by using the actual basis-completion cost in the product-formula inequality. The combined argument reduces the sufficient translate budget to `3 * targetDim * log b` (with a sharper asymptotic bound) and yields `m * totalRemainder ≤ 17 * f * a * log(b)^4`. It preserves the existing Dirichlet GRH analytic endpoint. An optional nonadaptive random-product proof is included. The main result is a rigorous local proof simplification, not an independent elementary proof or a new verified Lean development.

## Files

- `centered_theta_lifts.tex` — complete LaTeX source.
- `centered_theta_lifts.pdf` — compiled mathematical report, including proofs, source links, and research directions.
- `FORMALIZATION.md` — detailed source-level integration blueprint, not an elaborated Lean patch.
- `check_bounds.py` — exact rational sanity checks of constants, finite cyclic models and obstructions.
- `checks.txt` — actual output of `check_bounds.py`.
- `source_anchors.tsv` — selected immutable upstream declaration coordinates and Git blob SHA-1s, retrieved with the GitHub connector; overlapping hashes were also compared against the supplied guide's source map.
- `verify_sources.py` — verifies these anchors in a local checkout (not run against a local Lean checkout here).

## Reproduction

```sh
latexmk -pdf -halt-on-error centered_theta_lifts.tex
python3 check_bounds.py
git clone https://github.com/lsernau/grh-lean.git upstream-grh
git -C upstream-grh checkout --detach 72fead102f663d5c7a407964a13dc0cf9d977207
python3 verify_sources.py upstream-grh/grh
```

No Lean executable or project cache was available in the working environment. The original readable and compact editions were independently verified by Andrew Sutherland (https://math.mit.edu/~drew/shortgrh/); those checks do not verify the proposed replacement. No repository files have been changed. The report explicitly distinguishes old verified inputs, new mathematical derivations, and open research questions.
