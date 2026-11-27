# Sharp parity bias for a missing Hamming ball

Open **paper.pdf** for the full mathematical argument and the quadratic-prime application. The main theorem is on page 1. Page 5 proves rigidity of near minimizers, pages 6–8 handle transition points and the exact finite equatorial formula, and page 9 proves the prime bound. Pages 10–11 give finite examples, research questions, and sources.

## Reproduce

From this directory, with a standard TeX Live installation, run the first command twice. The figure is already included.

    pdflatex -interaction=nonstopmode -halt-on-error paper.tex

Both verification programs use Python 3.10 or later and its standard library. Run them with assertions enabled.

    python3 verify.py
    python3 radau_construction.py

Compare the printed results with **verification.txt** and **radau_output.txt**. The first program checks rational primal–dual certificates for six positive-threshold balls, verifies 1,088 equatorial or larger balls, and enumerates all 4,096 targets for twelve Legendre symbols. The second constructs measures on eight Hamming layers and verifies rational upper and lower bounds in five dimensions. It proves the all-level upper bound using exact computations for the extreme levels and a uniform bound for the middle levels. Decimal displays are rounded. The **paper.tex** and **endpoint.tex** files contain the proofs of the general theorems.

**thresholds.pdf** is the vector figure on page 1. To regenerate it, run **plot_thresholds.py** with Matplotlib 3.6 or later. **source-notes.txt** records the repository revisions and comparison sources.
