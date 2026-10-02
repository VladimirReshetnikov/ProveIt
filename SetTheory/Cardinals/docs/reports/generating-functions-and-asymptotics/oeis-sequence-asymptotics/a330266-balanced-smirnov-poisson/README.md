# Fixed-multiplicity shuffles and balanced Smirnov words

This archive accompanies the article on OEIS A007060, A193624, A330266, and
related multiset sequences.

## Main result

For fixed `k >= 2`, if `B(n,k)` counts shuffles of `k*n` distinct cards,
partitioned into `n` ranks of size `k`, with no equal adjacent ranks, then

```
B(n,k)/(k*n)! -> exp(-(k-1)).
```

The article proves the stronger convergence of the full equal-adjacency count
to `Poisson(k-1)`, gives exact factorial cumulants, and derives correction
terms through `n^-3` plus an all-orders construction.

## Files

- `article.tex` -- LaTeX source.
- `article.pdf` -- compiled article.
- `code/verify.py` -- standard-library exact enumeration and numerical checks.
- `code/derive_symbolic.py` -- optional SymPy verification of cumulants.
- `data/verification.csv` -- generated convergence data.
- `data/standard_deck.txt` -- exact 52-card calculation and approximations.
- `oeis_proposed_updates.txt` -- proposed, unsubmitted OEIS comments.

## Reproduce

From this directory:

```bash
python code/verify.py
python code/derive_symbolic.py   # requires SymPy
latexmk -pdf article.tex
```

The manuscript explicitly makes no claim of a complete literature search or
historical priority.  Independent review is recommended before submission.
