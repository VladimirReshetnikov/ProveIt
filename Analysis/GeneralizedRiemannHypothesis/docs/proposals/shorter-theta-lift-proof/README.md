# Shortening the theta-lift proof of Dirichlet GRH

The 11-page paper gives two mathematical replacements inside the readable theta-lift proof. For the shortest proof of quadratic-twist selection, start on page 6. Pages 3–5 derive a version using elementary character estimates and Poisson summation. Pages 8–9 prove the revised spanning lemma. Page 10 explains the cutoff and interpolation arguments.

## Files

- `shorter_theta_proof.pdf` and `shorter_theta_proof.tex` are the paper and its self-contained source.
- `check_twist_identities.py` checks the square-pair parametrization, Jacobi Gram identity, Möbius cancellation and a finite Gauss transform for a complex primitive character.
- `check_spanning.py` checks trace identities and rank-gain inequalities in a finite rational representation. It includes the numerical endpoint of the centered trace estimate.
- `source-map.tsv` and `check_sources.py` reproduce the correspondence between the paper and the readable Lean declarations. The checker is taken from the supplied guide.
- `verification.txt` records the results of the checks.

## Reproduce

Run the following from this directory with Python 3 and a standard TeX Live installation.

```sh
latexmk -pdf -halt-on-error shorter_theta_proof.tex
python3 check_twist_identities.py
python3 check_spanning.py
```

For the source-anchor check use the readable package in upstream revision 72fead102f663d5c7a407964a13dc0cf9d977207 of lsernau/grh-lean.

```sh
python3 check_sources.py /path/to/grh-lean/grh
```

The replacements are paper proofs. The public verification record for the base proof is cited in the paper. These scripts are finite checks, and no Lean implementation of the new derivations is claimed.
