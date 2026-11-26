# Beyond Dirichlet GRH: structural transfer analysis

Prepared for Vladimir Reshetnikov, 25 November 2026 (Pacific date).

Start with `report.pdf`. The complete LaTeX is `report.tex` plus `sections/`.

## Findings

The report analyzes the internal theta-lift, determinant, and Selmer method of
`lsernau/grh-lean`, rather than repeating standard consequences of RH/Dirichlet
GRH. It compares all 26 archives in the pinned ProveIt incoming directory.

The main proved results are:

1. An exact Smith formula for finite-level conjugate-dual Hom lengths, and the
   criterion that the source's global congruence term is finite exactly when
   its rational conjugate-dual Hom space vanishes.
2. Anticyclotomic invariance of that obstruction and its consequences for the
   central Tate modules of polarized abelian varieties.
3. A sharper symmetric-image bound extracted from the source's mirror proof,
   with an exact sign dichotomy under its integral matrix-span condition.
4. A symmetric-power extension of the scalar-inertia obstruction, including
   the fact that the source's ell-power-order twists cannot repair it.
5. An exact weight-24 Hecke-projector denominator, with a whole-orbit alternative
   that avoids internal eigenline splitting.
6. A finite-image Artin criterion and explicit loss accounting for future
   arithmetic transfers.

The full generalized Selmer twisting theorem is a proposed refactor, not an
already compiled extension. No new nonabelian RH, modular RH, BSD case, or
arithmetic vanishing theorem is claimed. No worldwide novelty claim is made
for elementary algebra; the incremental contribution is its application to
the actual source interfaces and the strengthened mirror endpoint.

## Reproduce exact calculations

Requires Python 3, standard library only:

```sh
python3 computation/verify_exact.py
```

The script writes `computation/exact_results.json`. It uses only integers and
rational numbers. It checks eight Smith diagonals by minors, 26 finite
commutant counts, 27 symmetric-pairing counts, and eleven prime Hecke matrices,
as well as eigenprojector identities and the exact denominator. The finite
enumerations can take a few minutes on a slower computer. General theorems
are proved in the report; finite checks do not substitute for those proofs.

## Compile the report

With a normal TeX Live installation providing Latin Modern, AMS, microtype,
geometry, booktabs, longtable, array, enumitem, xcolor, xurl, hyperref and
fancyhdr:

```sh
sh build_report.sh
```

The script runs `pdflatex` three times so that the table of contents and
cross-references stabilize. The bibliography is embedded in the source;
BibTeX/Biber and shell escape are not needed. On Debian or Ubuntu the standard
packages `texlive-latex-base`, `texlive-latex-recommended`,
`texlive-latex-extra`, `texlive-fonts-recommended` and `lmodern` provide these
dependencies. The actual compilation environment and verified package hashes
are recorded in `evidence/tex_build_environment.json`.

To use Tectonic with its available compatible resource bundle:

```sh
REPORT_TEX_ENGINE=tectonic sh build_report.sh
```

## Pinned sources

- Upstream: `lsernau/grh-lean`, commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`.
- Comparison corpus: `VladimirReshetnikov/ProveIt`, commit
  `6fe2c1bd450aa7f19eab17fb9a6e76170b4fce00`, `docs/incoming`.

`upstream/` contains 19 unmodified files sufficient to inspect the key
interfaces, including the original Apache 2.0 license, notice, and attribution.
It is not the entire Lean project. All included source hashes and pinned
URLs appear in `evidence/source_manifest.json`.

The independent published hash manifest was compared against our full clone:
all 1,625 files matched. Its original manifest and the comparison result are
in `evidence/`. This does not mean that we independently reran the Lean build.
The report distinguishes the published independent checks from our source
inspection and exact computations.

To repeat the full lexical audit, first clone the upstream repository at the
pinned commit, then run:

```sh
python3 computation/static_audit.py /absolute/path/to/grh-lean
```

The scan covers `src/` in both editions. Challenge placeholders outside `src/`
are intentional and not counted. A lexical scan is not a kernel check.

## Prior reports

`evidence/prior_inventory.json` and `.csv` record all 26 ZIPs, exact Git blob
identities, principal reports, claimed achievements, and unresolved obligations.
The source paths in that inventory are the paths used while reading those
archives; the prior archives themselves are not duplicated here. Several later
reports claim completed arithmetic classifications or finiteness results.
We preserve those claims and do not assert that they have all been independently
recertified in this session.

## Integrity and licensing

`SHA256SUMS` covers all deliverable files except itself. Validate from this
directory with `sha256sum -c SHA256SUMS`.

Upstream code remains under its supplied Apache 2.0 license. The newly written
mathematical report and exact verifier are supplied as research artifacts;
they do not change the provenance or license of the upstream source.
