# Sharp-window transport of Dirichlet zeros

Read **sharp_transport.pdf** for the complete statements and proofs. Theorem 1 gives the scalar Cauchy law, Theorem 2 the dimension-free matrix estimate, and Theorem 5 the convergent displacement remainder. Section 5.1 gives all coefficients of the sharp-window expansion.

## Contents

| File | Purpose |
|---|---|
| sharp_transport.tex | Editable LaTeX source |
| sharp_transport.pdf | Compiled paper |
| zeta_transport.pdf | Vector figure used by the source |
| checks/check_identities.py | Exact kernel identity and two noncommuting matrix coefficient checks |
| checks/check_identities.txt | Expected exact output |
| checks/example.py | Floating-point calculation of 23 consecutive zeta-gap displacements |
| checks/example.json | All numerical crossings, interval endpoints and totals |
| checks/plot_example.py | Regenerates the vector figure from the JSON data |

## Rebuild

Run the following from the extracted directory. The vector figure is included, so building the paper requires only a standard TeX Live installation with pdfLaTeX and the packages listed in the source.

```sh
pdflatex -halt-on-error sharp_transport.tex
pdflatex -halt-on-error sharp_transport.tex
```

Run the checks with Python 3.12. The exact rational check uses its standard library. The numerical calculation was run with mpmath 1.3.0. Rendering the optional figure uses NumPy 2.3.5 and Matplotlib 3.10.8.

```sh
python checks/check_identities.py
python checks/example.py > replay.json
python checks/plot_example.py
```

The source comparison is pinned to ProveIt commit f6b5955e13bcefb2760480e7b823eba55ed2383e, including Article/sections/zer.tex. The Dirichlet GRH input is the result recorded at lsernau/grh-lean commit 72fead102f663d5c7a407964a13dc0cf9d977207. The present results have mathematical proofs in the paper. The included computations check algebra and illustrate the scalar example.
