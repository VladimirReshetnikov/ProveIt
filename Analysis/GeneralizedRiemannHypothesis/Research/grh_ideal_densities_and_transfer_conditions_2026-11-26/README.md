# Beyond Dirichlet GRH: Ideal Densities and Arithmetic Transfer Conditions

Research report prepared for Vladimir Reshetnikov, 26 November 2026.

Read `report.pdf` for the complete argument. The editable source is `report.tex`
with its included files in `sections/`.

## Results

1. For every number field, an explicit finite change in the prime-ideal
   valuation rules gives a set of integral ideals of natural density strictly
   greater than the greedy set, while avoiding three-term geometric
   progressions with proper integral-ideal ratios. This answers the existence
   part of Best et al.'s published Question 5.1 and extends the assertion to
   every number field. Worldwide historical priority is not established.
   In Q(sqrt(-23)) the proved gain is greater than 0.0011957.
2. In every number field the supremum of upper densities is strictly greater
   than the supremum of natural densities, for either integral-ideal ratios
   or arbitrary nontrivial fractional-ideal ratios. Both numbers are
   computable. In Q(sqrt(-23)) the gap is greater than 1/20,000,000 under
   either convention. This does not prove natural density above greedy for
   fractional ratios.
3. Over Q(sqrt(-23)), at coefficient prime 3, an explicit class-field
   construction supplies tame anticyclotomic characters with arbitrarily
   small normalized ramification cost and the stronger one-sided precursor
   condition used by the source. Five conductor minima are proved by a
   class-field reduction and exhaustive integer certificates, including
   exclusion of all smaller multipair supports. The benchmark does not
   satisfy every hypothesis of the upstream global Data construction.
4. The readable source already bounds a full divisible Selmer module. A
   prior blanket objection based on fixed precision is corrected. The report
   proves coefficient descent and a single-precision equivalent of the
   source's fixed-field strict odd-cocycle bound. The missing uniform
   arithmetic bounds for nonabelian transfer remain explicit.

The density theorems do not use RH or GRH. The report does not claim a new
nonabelian Riemann hypothesis, a new K-group vanishing, or a solution of
Vandiver, BSD, twin primes, or Goldbach. The mathematical arguments are
human-readable proofs, not new Lean-checked theorems.

## Source snapshots

- `lsernau/grh-lean`:
  `72fead102f663d5c7a407964a13dc0cf9d977207`.
- `VladimirReshetnikov/ProveIt`:
  `5cc267af75a635199ac5d93a7d49cbce521daefc`.
- Prior comparison snapshot:
  `48efe71a726dddc5a505534edaa4c0fd190416b9`.

All 46 relevant incoming archives were downloaded and checked against byte
sizes and Git blob SHA-1 identifiers, and their SHA-256 checksums were
recorded. The corpus review was targeted, not a complete proof audit of
every archive. The archive inventory records the earlier download workspace
paths for provenance; the 46 original ZIP files are not duplicated here.
Selected exact upstream source blobs are included under `sources/upstream/`.

The upstream README reports formal verification of its RH/Dirichlet-GRH
endpoint. This analysis did not rebuild that project: Lean and Lake were
not installed in the analysis environment. The source statements and
selected proof passages were inspected statically.

## Contents

| Location | Purpose |
| --- | --- |
| `report.pdf` | Complete compiled mathematical report |
| `report.tex`, `sections/*.tex` | Complete editable LaTeX source |
| `code/check_ideal_density.py` | Valuation-exchange models, prefix obstruction, directed exact Euler-product certificate |
| `code/verify_ideal_natural_gain.py` | Independent rational certificate for the natural-density gain |
| `code/check_source_twists.py` | Exact conductor search and all smaller multipair exclusions |
| `code/check_module_bridge.py` | Finite module and cocycle sanity checks |
| `code/verify_ktheory_prefilter.py` | Replayed checker from an earlier incoming report; preliminary identities only |
| `data/*.json`, `data/*.csv` | Machine-readable certificates and corpus inventory |
| `verification/*.log` | Recorded successful checker and compilation outputs |
| `sources/` | Pinned source excerpts, audit notes, manifests and attribution |
| `FORMALIZATION_PLAN.txt` | Proposed next formalization steps, explicitly not completed Lean code |
| `SHA256SUMS` | Integrity manifest for delivered files |

## Reproduce the finite certificates

Only the Python standard library is required, with Python 3.10 or later.
From this directory run:

```sh
make check
```

The individual commands are:

```sh
python3 code/check_ideal_density.py --output data/ideal_density_certificate.json
python3 code/verify_ideal_natural_gain.py --output data/ideal_natural_gain_certificate.json
python3 code/check_source_twists.py
python3 code/check_module_bridge.py --output data/module_bridge_checks.json
python3 code/verify_ktheory_prefilter.py --ranks --output data/ktheory_prefilter_rerun.json
```

All five staged checkers were run successfully. The numeric searches use
exact integers or rational numbers. No probabilistic primality assertions
or floating-point decisions support the conductor minima or density bounds.
The exact Euler-product calculation rounds down after every multiplication
on a fixed rational grid. This gives a proved lower bound, not a numerical
estimate presented as an inequality.

These computations check finite arithmetic. They do not check ideal-counting
limits, class field theory, infinite constructions, or arithmetic Galois
cohomology; those arguments and their external inputs are in the report.

## Rebuild the PDF

A standard TeX installation with pdfLaTeX and the packages listed in
`report.tex` is sufficient. Run:

```sh
make pdf
```

This runs pdfLaTeX twice to resolve the table of contents and references.
The delivered PDF was rendered and visually inspected. No network access
is required to compile it or to run the finite checkers.

To verify the delivered bytes before rebuilding or rewriting certificates:

```sh
sha256sum -c SHA256SUMS
```

Rebuilding intentionally changes some generated files and therefore can
invalidate their delivered-byte checksums.

## Attribution and scope

See `sources/THIRD_PARTY_NOTICES.txt` for copied material. The density method
builds on the earlier supplied reports and classical exponent constructions;
the report separates those antecedents from the all-number-field extensions
proved here. The character construction specializes class field theory and
the source's existing strategy. All proposed global transfers retain their
unproved hypotheses explicitly.
