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
- The former `SHA256SUMS` package ledger was retired repository-wide on
  2026-09-01; its final snapshot remains recoverable from Git history.

## Reproducibility data

- `first_wave_generated/` contains exact up-law moments, exact positive Jacobi
  coefficients, numerical transform checks, and two first-wave figures.
- `generated/data/` contains half-lattice coefficients, weighted cancellation
  sums, formal-Jacobi coefficients and exact checks, Padé/quadrature checks,
  Mellin checks, Malmsten checks, sampling checks, and exact up-law moments.
- `generated/figures/` contains PDF and PNG versions of the four second-wave figures.
- `figures/` and the two root-level Jacobi PDFs are compile-ready copies used by
  the LaTeX source.
- The historical ledger below preserves the hashes of the deleted
  `source_audit/` copies used for theorem-level comparison. The complete path
  inventory is in `corpus_inventory.tex`.

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

## Historical deleted source-audit ledger

The six source-audit copies below were removed during consolidation and are no
longer active package files.  Their last archived SHA-256 values are preserved
here; git history remains the byte-for-byte archive.

```text
be9b986264c626fffb889ffdac53c49f28ff78cbeabb87e376b5927667bc7b7b  source_audit/Consolidated_Formula_Atlas_for_the_Thue_Morse_Sequence.tex
4c90d3a51eff3812c4248e4ffe37ba4e9ea8e06a00bee89db390dfc0b69309f3  source_audit/Fabius_Function_and_Rvachev_Up.tex
027ba4ded88535b8e3f8a18a6ce0f15ea10e0b9f29ec0a8e80f54c430053fc42  source_audit/Fabius_Rvachev_Thue_Morse_Frontier_Results.tex
b88b32f94dc3bcfe875705000d9e47386cab0b71ba43425dc68cd363bf35b439  source_audit/Thue_Morse_Formula_Atlas.tex
a00f1cae980ac4e2a15600b68f55d5688b71c30a41bf8ed9898930177f7ab1e8  source_audit/fabius-q-special-functions.tex
8fdba498ec33cde2db9e7dc82c0c928946f632beb8a0ffd216afe310eaea0ea2  source_audit/prior_representation_report.tex
```

> **Editorial note (2026-08-28):** the report source (.tex) and compiled PDF listed above were removed from this directory after their content was merged into the volume `Representation_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance section, and git history archives the files. This directory keeps only figures, data, and scripts.
