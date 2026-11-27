# Detecting nonreal zeros from sparse logarithmic derivatives

Open **paper.pdf** for the nine-page research paper. Its complete editable source is **paper.tex**, together with the vector diagram in **figures/**.

## Mathematical results

For completed Dirichlet functions, the heights 0, 1 and 5 suffice to test critical-line reality by positive semidefiniteness of Hankel matrices built from sparse logarithmic derivatives. Each height may use a different positive integer stride. Dyadic blocks require only O((log N)^2) specified derivative orders through N per height. For the even Riemann xi-function, the heights 1 and 4 suffice.

The general results apply to any nonzero real entire function of order at most one, also allowing multiplication by a constant phase. The paper establishes the limiting negative index for moving blocks, the five-point classification of exceptional rational center sets, the optimal total loss 5D + D(D−1)/2 for D distinct nonreal conjugate pairs, and integer sampling designs for which every three retained heights suffice.

The paper gives written proofs for all of its new results. The programs check finite instances by exact arithmetic. Source revisions, comparisons with the supplied research collection, classical precedents and further research questions appear in the paper and in source_screen.md.

## Reproduce the exact checks

From the extracted directory, with Python 3.9 or later, run

```sh
python3 checks/verify.py
python3 checks/verify_designs.py
```

Both programs use the Python standard library. Their expected output is in **checks/verification.txt** and **checks/designs_verification.txt**, respectively. Leave Python assertions enabled.

- **verify.py** enumerates normalized rational center configurations, checks the quadratic counterexample in two ways, and computes exact inertia at 12 centers and three even starting orders for a polynomial with two nonreal pairs. Its output uses H_0 and H_2 for the two-by-two matrices with starting exponents 0 and 2 in its finite quadratic example. The paper uses K = 2 there.
- **verify_designs.py** computes all rational triple ratios for strides through 40 in exact cyclotomic quotient rings, checks the 2,024 triples of a 24-center integer design, and verifies the sharp construction through 50 nonreal pairs.

## Rebuild the PDF

From the same directory, on a standard TeX Live installation with pdfLaTeX, run

```sh
pdflatex -halt-on-error paper.tex
pdflatex -halt-on-error paper.tex
```

The vector figure is included. Its Python source in **figures/rational_centers.py** is provided for editing and requires Matplotlib. SHA256SUMS records the delivered files. On systems with Coreutils, run `sha256sum -c SHA256SUMS` to check them.

