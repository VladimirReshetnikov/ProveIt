# Geometric-progression density over finite fields

Start with **counterexample.pdf**. It disproves Conjecture 6.3 of Asada, Fourakis, Manski, McNew, Miller and Moreland for every prime power, provides an explicit positive density margin, and gives two-sided approximations to the true supremum. The construction uses the carry-free sphere argument present in the Dirichlet GRH source. It is independent of RH and GRH.

**analytic_transfers.pdf** develops two further uses of the source. It compares signed multiplicities in short height intervals and in boxes of prime phases. It also proves an exact extremal-weight formula for Gaussian Hecke characters. The one-sided prime estimate for those characters remains an open input.

## Rebuild the papers

Run the commands in the extracted directory with a standard TeX Live installation.

```sh
latexmk -pdf counterexample.tex
latexmk -pdf analytic_transfers.tex
```

## Reproduce the checks

The Python programs use only the standard library. Run them with Python 3.10 or later with assertions enabled.

```sh
python3 check_sphere.py
python3 check_small_pattern.py
python3 check_tilted.py
python3 check_polynomial_fibers.py
python3 check_gaussian.py
python3 check_frequencies.py
```

The sphere and two smaller patterns certify the finite additive inputs. The binary-polynomial example exhausts triples in a finite ball and verifies that all triples touching a new point have the same rough part. Its small sample change has negative net size. The strict gain in the theorem comes from the separately proved generating-function inequality. The angular checker uses exact rational primal and dual certificates. The frequency checker verifies the prime-power terms in a finite expansion. These programs do not certify the full asymptotic or complex-analytic arguments.

**verification.txt** records the outputs. **source-map.md** identifies the Lean declarations and the prior reports, and **prior_archives.tsv** lists the earlier archives at the inspected revision.
