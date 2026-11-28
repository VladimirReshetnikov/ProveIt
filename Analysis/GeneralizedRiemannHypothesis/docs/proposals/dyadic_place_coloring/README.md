# Dyadic-shift coloring for the theta-lift proof

A paper-level simplification of the sparse-infinite-place construction in the Alpöge–Claude proof of the Riemann hypothesis and Dirichlet GRH. The result is independent of the five proposals in the inspected `docs/proposals` directory. The original weighted-free digit-set construction is replaced by a finite modular coloring, preserving the full source sparsity condition, including repeated places and independent signs.

## Files

- `dyadic_place_coloring.pdf`: 10-page research paper, full mathematical arguments, comparison with prior proposals, and integration into the one-sided bound.
- `dyadic_place_coloring.tex`: complete standalone LaTeX source.
- `LEAN_PLAN.md`: source-level implementation plan and validation checklist. Not compiled Lean code.
- `check_coloring.py`: dependency-free exact finite regressions and integer loss estimates.
- `checks.txt`: recorded run output.
- `source_audit.tsv`: inspected paths, blob IDs, selected anchors, and immutable source links. The proposal TeX inspection concentrated on headings and terms relevant to sparse places, not exhaustive line-by-line review of all unrelated proofs.
- `verify_sources.py`: checks audited Git blob hashes against a local checkout of ProveIt.

## Reproduction

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error dyadic_place_coloring.tex
python3 check_coloring.py
python3 verify_sources.py /path/to/ProveIt
```

The source baseline is commit `89d12dd40424f1217fd818d84877b3da52396a3b`. The readable Lean subtree matches the independently checked readable tree `2e133df63d7f4da6b3059c4195324f8e9187ba73`. The original independent checking record is https://math.mit.edu/~drew/shortgrh/ . That verification does not cover this proposal. The verifier for local source blobs is supplied but has not been run against a local checkout; the blob hashes were retrieved through GitHub.

The new finite bounds and reductions are proved mathematically in the paper. Python regressions are not substitutes for those proofs. No Lean executable/project cache was available, so the new replacement is uncompiled. No repository files were modified. The subpower loss is not claimed to be a new additive-combinatorial phenomenon (it can also be obtained by optimizing the original Behrend construction). The contribution is the distinct coloring interface, the drop-in W^4 estimate with fewer assumptions, and the separation of the dimension of the exponent construction from the prime-window parameter.
