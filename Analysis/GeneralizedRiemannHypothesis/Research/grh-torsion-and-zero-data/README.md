# How far must a torsion selector search?

Open **report.pdf** for the complete proofs. The main result gives the exact minimum witness budget for defeating simultaneous one-variable torsion selection through a prescribed shell, together with its sharp tolerance asymptotics. The analytic sections address finite inverse recovery from signed zero data and a fourth-power criterion for symmetric powers of elliptic curves.

## Rebuilding the paper

With a standard TeX Live installation, run the following from this directory. The figure is supplied as a PDF and does not need regenerating to compile the paper.

```sh
pdflatex -halt-on-error report.tex
pdflatex -halt-on-error report.tex
```

The five section files are torsion.tex, minimax.tex, phase.tex, recovery.tex and sympower.tex. Source locations and Git blob identifiers are in source-audit.json. The report uses upstream verification records. The downstream results have human-readable proofs.

## Reproducing the checks

Use Python 3.10 or later. Only selection_figure.py requires Matplotlib. Run from this directory.

```sh
python3 check_torsion.py
python3 check_minimax.py
python3 check_threshold.py
python3 check_recovery.py
python3 elliptic_samples.py
python3 selection_figure.py
```

* **check_torsion.py** checks valuations for the explicit dyadic example and its finite cost bound.
* **check_minimax.py** exhausts all multiset layouts in eight small shells, including repeated roots. It independently evaluates the worst point for each layout and compares the optimum to the floor sum. It then tabulates exact costs through shell 16 for three primes.
* **check_threshold.py** verifies the boundary cases at the critical budget and zero tolerance.
* **check_recovery.py** checks the integer candidates, a distinguishing prime, and conservative truncation bounds for the two probes. It uses exact rational inequalities. It works with known arithmetic parameters. An actual zero list and the cost of obtaining one are outside this computation.
* **elliptic_samples.py** counts points over finite fields, checks the Hasse bounds and prints an illustrative floating-point table. The table gives the sum before subtracting the centering constant.
* **selection_figure.py** checks the exact 371/372 boundary and draws selection_budget.pdf. Its independent implementation inverts the shell formula using base-p digits.

Recorded outputs are under verification/. The elliptic-curve sample is elliptic_samples.csv. The archive's SHA256SUMS covers every other file.
