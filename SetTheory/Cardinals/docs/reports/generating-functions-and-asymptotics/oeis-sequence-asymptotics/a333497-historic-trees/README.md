# Historic tree asymptotics and a high order obstruction

This reproducibility package accompanies `historic-trees.pdf`.
For the all-one equations H_r^(r) = H_r^2 and m = r−1, the article proves:

- m=2, reduced 5-historic trees (A333497): h_n ~ 30 (n+2)! rho_3^(-n-3)
- m=3, reduced 7-historic trees (A336009): h_n ~ 140 (n+3)! rho_4^(-n-4)
- Every m>=29: the equivalent in Burghart and Wagner's 2026 Conjecture 1 is false
  for the specified all-one counting sequence

Both low-order cases have convergent local complex-power expansions, nonzero
logarithmically oscillating first corrections, all fixed coefficient grades
with exact Gamma ratios, and qualified eventual inverse-threshold brackets.
The high-order result combines exact phase inequalities with an orbit-specific
sign-variation obstruction and a generalized stable-manifold argument.

The article credits Astashova's real-axis theorems, the B-urn spectral family,
Kozlov's large-order instability result, and the sign-regularity and invariant
manifold theorems it uses. It does not identify a replacement high-order
asymptotic, prove a periodic limiting profile, prove m=29 is the first failure,
or settle the separate Conjecture 2. Numerical constants are not interval
certified, and no infinite transferred coefficient sum at fixed n is asserted.

## Files

- `historic-trees.pdf`: complete mathematical article
- `historic-trees.tex`, `extensions.tex`, `references.bib`: editable LaTeX and source bibliography
- `figures/oscillation.pdf`, `figures/oscillation.csv`, `make_figure.py`: original
  exploratory illustration, underlying data, and regeneration code
- `code/`: original research calculations with documented portable path changes,
  plus isolated replay orchestration
- `data/producer/`, `data/independent/`, `data/extensions/`: preserved exact and
  exploratory outputs, with exact high-order certificates
- `data/provenance.json`: original and bundled computational-source hashes
- `data/verified_final_replay.json`: complete final replay evidence
- Earlier `data/verified_replay.json` and `data/verified_extension_replay.json`:
  preserved earlier replay snapshots, superseded in scope by the final snapshot
- `REPRODUCIBILITY.md`: detailed replay methods and numerical limits
- `build.sh`, `replay.sh`, `requirements.txt`, `requirements-figure.txt`:
  rebuild and replay instructions
- `MANIFEST.sha256`: hashes of the released files

The package contains no third-party papers, raw working notes, or private review
reports. The bibliography links to primary sources.

## Verify and replay

From this directory:

    sha256sum -c MANIFEST.sha256
    bash replay.sh

Use Python 3 with the packages in `requirements.txt`. The verified run used
Python 3.12.14. Replay creates a separate temporary output tree and preserves all
shipped data; its path and machine-readable summary are printed. See
`REPRODUCIBILITY.md` for details. A full replay passed and matched all archived
exact outputs; floating outputs also matched byte-for-byte in the checked
environment. Floating agreement is not an interval certificate.

## Build the article

    bash build.sh

The script uses pdfLaTeX and BibTeX with standard TeX Live packages. Where the
package tree exists but formats or font maps are absent, it builds those
locally under `.build`. It makes no system installation changes. The supplied
figure is already included, so matplotlib is not needed merely to rebuild the
article. To regenerate the original plot, also install the optional packages
in `requirements-figure.txt`, then run:

    python3 make_figure.py
    bash build.sh

The plot includes every integer index from 80 to 600. Exact counts are normalized
using fitted, non-certified constants. No numerical data are used to prove the
analytic assertions.
