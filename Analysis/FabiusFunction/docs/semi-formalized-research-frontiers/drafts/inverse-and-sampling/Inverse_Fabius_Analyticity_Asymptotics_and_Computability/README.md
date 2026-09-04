# Inverse Fabius Theory: analyticity, asymptotics, computability, and dyadic sampling

This directory is the canonical source and publication package for
[`inverse_fabius_theory.tex`](inverse_fabius_theory.tex)
([PDF](inverse_fabius_theory.pdf)). It replaces five overlapping reports on
inverse Fabius theory and the Rvachev law: dense-open analyticity and
non-elementarity, positive inverse iterates, inverse-dyadic germs,
Barnes--Rvachev deconvolution, all-orders Lambert--W endpoint inversion,
dyadic self-sampling and Richardson filters, exact inverse moduli, and
certified computation.

Every nonconjectural retained assertion has a complete human-readable proof.
`Lean-proved` is reserved for an exact current declaration with matching
hypotheses and conclusion; other complete proofs are labelled
`human-proved frontier result`. Genuine unresolved obligations remain visibly
labelled as conjectures or open problems, and numerical experiments are used
only as reproducible checks.

The package audit surfaces are:

- [`theorem_concordance.csv`](theorem_concordance.csv): all 194 immutable
  source-result rows, fully dispositioned as 50 Lean-proved, 95 human-proved
  frontier results, 10 conjectures, 15 open problems, and 24 non-applicable
  source environments;
- [`LEAN_CROSSWALK.md`](LEAN_CROSSWALK.md): exact module and declaration
  matches, formalization boundaries, and five separately classified
  post-snapshot additions;
- [`ASSET_DISPOSITION.csv`](ASSET_DISPOSITION.csv): the disposition of all 88
  files in the two superseded source subgroups;
- [`SOURCE_CLOSURE.sha256`](SOURCE_CLOSURE.sha256): the reproducible ledger
  of the 23 files consumed by the TeX build;
- [`PROVENANCE.md`](PROVENANCE.md): source hashes, arrival lineage, nested
  predecessors, and immutable recovery points.

The source-closure ledger and migrated-asset audit are checked independently:

```bash
python -B audit/build_source_closure.py --check
python -B audit/build_asset_manifest.py --check
```

`theorem_concordance.csv` records the disposition of all 194 source-result
environments while preserving the ten immutable source fields reproduced from
`audit/SOURCE_REVISION`.  Its current totals are 50 Lean-proved, 95
human-proved frontier results, 10 conjectures, 15 open problems, and 24
nonassertoric rows.  Nine inverse-computability rows now have exact compiled
counterparts: the main theorem, the three tolerant-difference branch
certificates, tolerant-bisection correctness, unit-interval sequential
inversion, computable clamping, and sequential computability of the totalized
inverse.  `FabiusFunction.EffectiveGapInverse` closes the ninth, abstract row:
it derives a computable reciprocal inverse modulus from computable positive
rational gap data and concludes both subset sequential computability and
effective uniform continuity; its companion theorem packages the clamped
inverse as a total computable real function.  The centered Appell
deconvolution, positive-degree Appell
mean-zero, and arbitrarily phased polynomial-deconvolution rows also have exact
named Lean counterparts.  The Appell lattice theorem is now Lean-proved:
Lean covers both its arbitrary-phase `0 <= n <= N` formula and its
degree-`N+1` clause at the parity-selected superconvergent phases.  The same
compiled synthesis module gives the exact physical quadrature form of forced
superconvergence, with the phase dictionary and existing positivity,
rational-dyadic-value, and finite-support kernels.  This does not claim a
classification of every superconvergent phase or sharpness beyond the stated
degree.  The static canonical validator passes.  `PROVENANCE.md` records source
and asset lineage.

The package checksum inventory is defined by the Git index. Resolve unmerged
paths and stage every intended permanent package file before generating or
checking it; the source-closure check is independent of that index state.

The result and asset extractors are pinned by
[`audit/SOURCE_REVISION`](audit/SOURCE_REVISION) to
`0a0cdabeb72a6f7d67cfdfb76d02a8f7381c7bf7`.
The five later notation-normalized source layouts remain recoverable together
at `93db15ad3c0645bd3cfd0a3e6e694e3c86a3aa2b`, a complete pre-retirement
repository snapshot. The old paths are retained as provenance locators, not
as live links.

The six newest exact source-row matches are abstract effective inversion,
centered Appell deconvolution, positive-degree Appell mean-zero,
arbitrary-phase polynomial deconvolution, forced superconvergence, and finite
Appell lattice reproduction.  The last two use
`FabiusFunction.RvachevSuperconvergentSynthesis`: its phase dictionary
specializes the selected phases at `M = 2^N`, its physical quadrature wrapper
proves polynomial exactness through degree `N+1`, and its Appell wrapper proves
the corresponding finite lattice identity.  These declarations do not assert
an all-phase classification or a sharpness theorem.

## Inverse-asymptotics subgroup closure

The former `inverse-asymptotics-and-computability/` subgroup is fully
dispositioned and consolidated here, rather than merely summarized. Its three
masters contribute 152 of the 194 concordance rows:

- `Inverse_and_Sampling_Frontiers`: 83 rows;
- `Inverse_Endpoint_All_Orders`: 29 rows; and
- `Inverse_Fabius_Computability_Report`: 40 rows.

Their canonical classifications are 34 exact Lean matches, 77 complete
human-proved frontier results, 18 non-live source environments (seven
definitions, three algorithms, two examples, four editorial obligations, and
two superseded source conjectures), nine explicitly retained conjectures, and
14 explicitly labelled open problems. The three package directories contribute
67 audited files, and the subgroup README is a 68th disposition row.
`ASSET_DISPOSITION.csv` accounts for all of them: unique scripts, exact tables,
figures, generated fragments, and captured checks were retained in the
deduplicated asset tree; superseded masters and renderings remain recoverable
from the immutable pre-retirement revision. Thus the historical subgroup
contains no live theorem, proof, or reproducibility payload that is absent or
unaccounted for here.

## Current source and retained publication artifact

The canonical source surface is current and exhaustively inventoried:

- `inverse_fabius_theory.tex`: 293 lines, 11,514 bytes, SHA-256
  `92fab1fae38bbcf86a45b51bfe7ff34e2801361df9d2f3d6aa3de4dc966eaa3c`;
- its exhaustive 23-input source closure: SHA-256
  `aedf007c2cd150b1f83de6d8996b4bf31e267b3dbcec2d5cd4720f5d92122bdb`;
- the retained `inverse_fabius_theory.pdf`: 134 A4 pages, 2,027,726 bytes,
  SHA-256
  `22bc68d855ad04dde9654e9fbd20b3ba7f05a33e3c5df0e5b80bb8991c94b41d`.

The PDF is the last fully reviewed publication checkpoint.  Its historical
three-pass sequence was 127, 134, and 134 pages, and its log, page, text, box,
font, and visual checks remain valid for those exact PDF bytes.  The master and
shared notation have changed since that render, so this document does **not**
claim that the retained PDF renders the current source.  A fresh three-pass
render is required before source/PDF synchronization is claimed again.
`VALIDATION.md` separates current source-integrity evidence from the retained
artifact receipt. Package checksum manifests are retired repository-wide;
`SOURCE_CLOSURE.sha256` and `ASSET_DISPOSITION.csv` retain the scoped source
and migration evidence without acting as whole-package checksum gates.

The mathematical consolidation and provenance gate are complete.  The five
source packages and their retained renderings are historical inputs represented
by the immutable revision, concordance, migrated evidence, and repository
history; they are not parallel renderings of this canonical master.
