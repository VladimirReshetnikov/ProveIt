# Identifying abelian number fields from a short interval of zeta zeros

The complete argument and bibliography are in `zero_windows.pdf`. The editable source is `zero_windows.tex`.

## Main result

For a fixed number of distinct primitive Dirichlet characters of conductor at most Q, every nonzero complex linear combination of their zero multiplicities is detected in a positive window starting at zero of length O(log² Q / log log Q). Theorem 1.1 gives a quantitative lower bound and treats translated windows. Corollary 1.2 applies this to products and to abelian number fields of bounded degree. Corollary 4.1 allows missing and displaced observations. The proofs use Dirichlet GRH as provided by the referenced Lean development. The new mathematical argument is presented in ordinary mathematical prose.

## Reproduce the files

On a standard TeX Live installation with the listed packages, run these commands in the directory containing this file.

```sh
pdflatex -interaction=nonstopmode -halt-on-error zero_windows.tex
pdflatex -interaction=nonstopmode -halt-on-error zero_windows.tex
```

The two checks can be run independently.

```sh
python3 checks/sieve_window.py
python3 checks/signed_zero_example.py
```

The first uses the Python standard library. The second uses mpmath 1.3.0. Expected output is in the corresponding `.txt` files. The finite arithmetic calculation illustrates the local prime and prime-power contribution. The signed-zero scan illustrates Fourier orientation for a quartic character and its conjugate. A sign-change scan can miss roots, including roots of even order. Neither experiment is needed by the proof of Theorem 1.1.

## Pinned sources

- [Lean theorem statements](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Statements.lean), [exported theorems](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Main.lean) and [independent verification](https://math.mit.edu/~drew/shortgrh/).
- [ProveIt reconstruction section and open questions](https://github.com/VladimirReshetnikov/ProveIt/blob/dec3e4f216305071186a1cc4c42fe1cdb38df9be/Analysis/GeneralizedRiemannHypothesis/Article/sections/rec.tex) and [zero distribution section](https://github.com/VladimirReshetnikov/ProveIt/blob/dec3e4f216305071186a1cc4c42fe1cdb38df9be/Analysis/GeneralizedRiemannHypothesis/Article/sections/zer.tex).
