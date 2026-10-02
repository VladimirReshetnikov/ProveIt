# Rooted identity trees with fixed maximum outdegree

This bundle accompanies the research article dated 2 October 2026.

## Read the result

- `report.pdf`: the 12-page article
- `report.tex`: editable, self-contained LaTeX source
- `code/`: portable exact enumeration, Puiseux/Gamma, and inverse generators
- `data/`: exact counts and high-precision numerical reference results
- `SHA256SUMS`: SHA-256 release manifest for every bundled file except itself

The theorem concerns rooted unlabeled identity trees with **at most** d children
per vertex, for each fixed d >= 2. The worked cases d=3 and d=4 are OEIS A116379
and A116380. All asymptotic orders are fixed. A degree-independent derivative
bound does not imply a growing-degree uniform asymptotic theorem.

The proof supplies a finite endpoint, analytic nested inputs, characteristicity,
positive transversality, and unique complex dominance. Standard Puiseux and
singularity-transfer methods then give all fixed coefficient orders. Exact
thresholds receive qualified ceiling bounds. The inverses are for explicitly
specified finite models, with D_j=0 beyond the model truncation.

Priority is not asserted. The derivative cancellation is credited to
Bell–Burris–Yeats, and two relevant older full texts were not accessible for
inspection. See the article's prior-work section and direct reference links.
No third-party full papers are included.

## Reproduce everything

Requirements:

- Python 3.10 or later, with `mpmath==1.3.0`
- Bash
- pdfLaTeX/TeX Live, with the standard AMS, Latin Modern, microtype, geometry,
  booktabs, enumitem, hyperref and fancyhdr packages
- Poppler's `pdftotext` and `pdftoppm` are optional for independent visual review

The release was checked with Python 3.12.14, mpmath 1.3.0, and
pdfTeX 3.141592653-2.6-1.40.26 (TeX Live 2025/dev/Debian).

Install the numerical dependency if needed:

```sh
python3 -m pip install -r code/requirements.txt
```

From the extracted bundle directory run:

```sh
bash replay.sh
```

This verifies the manifest; recomputes counts through n=400 for d=2,3,4 by the
positive-product and independent Newton recurrences; repeats the three
truncation/precision runs for d=3,4; checks both nested-jet routes; tests the
Lambert and pure-log inverse generators; and rebuilds the PDF. Fresh generated
numerical outputs go to `replay-output/`, and TeX intermediates to `.build/`.
To run numerical checks alone, use `bash code/reproduce.sh`. Individual generator
commands and all data conventions appear in `code/README.md` and `data/README.md`.

The PDF build fixes SOURCE_DATE_EPOCH. A fresh extraction and replay with the
release toolchain produced a byte-identical PDF. Different TeX/font versions may
change PDF bytes. If that happens, the script reports the difference; compare
extracted text and all rendered pages before attributing it to a content change.
The release manifest intentionally identifies the original PDF bytes.

## Safe ZIP extraction

Use Python's zipfile library after validating the member names, rather than
blindly extracting an unknown archive. `code/safe_extract.py` rejects absolute
paths, parent traversal, backslashes, symlinks, duplicate names, oversized
archives, and a pre-existing destination. For this archive:

```sh
python3 code/safe_extract.py rooted-identity-trees-source.zip fresh-copy
cd fresh-copy/rooted-identity-trees
bash replay.sh
```

The extraction helper can be run from a trusted existing copy of this source
bundle. No network access is used by extraction, replay, or the PDF build.
The shell scripts are deliberately invoked with `bash`; executable permission
bits are not needed after ZIP extraction.

## What the numerical checks mean

- Count residual = exact count / truncated asymptotic model - 1
- Model inverse residual = model inverse - exact index n, at y=a_n
- Inverse-series residual = truncated inverse - model inverse
- Total inverse residual = truncated inverse - exact index n
- The nested routes share exact counts and later jet algebra; their independence
  concerns construction of the nested Taylor coefficients
- Agreement beyond 60 decimals is a stability observation, not a certified tail
  bound, interval enclosure, or proof that all displayed digits are correct
- No finite asymptotic expansion can guarantee exact integer rounding arbitrarily
  close to every jump; the article states the necessary separation condition

## References

The article provides primary-source citations with links. The leading-law
framework and all-order analytic machinery are established prior work. The
present emphasis is the explicit fixed-cap boundary/transversality closure and
its reproducible correction/inverse calculus.
