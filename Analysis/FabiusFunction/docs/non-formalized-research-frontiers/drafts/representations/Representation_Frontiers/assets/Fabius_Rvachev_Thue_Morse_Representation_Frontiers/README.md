# Fabius–Rvachev–Thue–Morse Representation Frontiers

This archive contains the complete LaTeX source, the compiled 43-page PDF, two fully
commented experiment programs, exact rational data, high-precision numerical
checks, figures, checksums, and the recursive repository-audit ledger for the
report:

**Sampling, Padé, Mellin, Resolvent, and Product–Integral Representations of the
Fabius–Rvachev–Thue–Morse System**.

## Main files

- `fabius_rvachev_thue_morse_representation_frontiers.tex` — complete report source.
- `fabius_rvachev_thue_morse_representation_frontiers.pdf` — compiled report.
- `rvachev_frontier_experiments.py` — first-wave exact moment, positive-Jacobi,
  resolvent, and logarithmic-derivative experiments.
- `frontier_sampling_pade_experiments.py` — second-wave sparse sampling,
  Bose–Malmsten, Mellin, formal-Jacobi, Padé, and complex-quadrature experiments.
- `corpus_inventory.tex` — pinned 67-path recursive audit ledger plus live additions.
- `AUDIT_SCOPE.md` — snapshot and novelty conventions.
- `SHA256SUMS` — checksums for every packaged file except the checksum file itself.

## Reproducibility data

- `first_wave_generated/` contains exact up-law moments, exact positive Jacobi
  coefficients, numerical transform checks, and two first-wave figures.
- `generated/data/` contains half-lattice coefficients, weighted cancellation
  sums, formal-Jacobi coefficients and exact checks, Padé/quadrature checks,
  Mellin checks, Malmsten checks, sampling checks, and exact up-law moments.
- `generated/figures/` contains PDF and PNG versions of the four second-wave figures.
- `figures/` and the two root-level Jacobi PDFs are compile-ready copies used by
  the LaTeX source.
- `source_audit/` preserves the principal living/formula-atlas sources used for
  theorem-level comparison. The complete path inventory is in the ledger.

## Principal corpus-relative results

The report organizes the repository's established probability, convolution,
Fourier-product, q-binomial, exact-dyadic, inverse-function, Lambert-W,
Bell/Bernoulli, Cauchy-transform, Fredholm-determinant, and Jacobi-fraction
representations. It then proves a second wave of results, including:

1. sparse half-lattice Shannon reconstruction and a paired Mittag–Leffler
   expansion for the Rvachev Fourier image;
2. exact recovery of signed and unsigned Thue–Morse values from the residues;
3. odd-harmonic cosine series for `up` and the Fabius function, with infinite
   weighted Prouhet cancellation identities;
4. a Bose–Malmsten product–integral representation and logarithmic-derivative hierarchy;
5. Mellin/quantile identities linking `up`, `F`, and the inverse Fabius function;
6. formal orthogonal polynomials for the signed Thue–Morse moment functional,
   including dyadic polynomial and Jacobi-coefficient recursions;
7. the closed dyadic Padé denominator `1+z^(2^m)` and an exact roots-of-minus-one
   complex quadrature reproducing `2^(m+1)` consecutive signs;
8. Krawtchouk, hypergeometric, contour, residue, and antiperiodic Fourier avatars
   of the signed and unsigned words.

Results called “new” are new relative to the audited repository snapshot; no
absolute literature-priority claim is made.

## Run the experiments

Requirements: Python 3.10 or newer plus the packages in `requirements.txt`.

```bash
python3 -m pip install -r requirements.txt

python3 rvachev_frontier_experiments.py \
  --order 40 --digits 45 --output-dir first_wave_generated

python3 frontier_sampling_pade_experiments.py \
  --output-dir generated
```

The first computation uses exact rational Gram–Schmidt arithmetic and can be
substantially more expensive than the second-wave suite.

## Compile the report

A current TeX Live installation with `latexmk` is sufficient:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  fabius_rvachev_thue_morse_representation_frontiers.tex
```

The archive already contains every input needed for a clean compilation.
