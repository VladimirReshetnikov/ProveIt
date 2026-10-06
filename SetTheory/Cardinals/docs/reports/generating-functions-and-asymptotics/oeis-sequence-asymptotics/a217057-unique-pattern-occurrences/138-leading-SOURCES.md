# Report138 source inventory and provenance

All numerical inputs needed for replay are bundled. No command downloads data.
`sources/inventory.json` records the exact bytes, SHA256, URL, capture date, and
transformation for each source file. The top-level manifest covers that inventory
and every file it names. The source inventory is closed rather than a free list
of paths. No downloaded source or fixture is imported or executed.

## Official numerical sources

- `sources/A224248.seq`: OEIS A224248, official oeisdata-repository snapshot, terms n=0..23.
  https://github.com/oeis/oeisdata/blob/main/seq/A224/A224248.seq
- `sources/A047889.seq`: OEIS A047889, official oeisdata-repository snapshot, terms n=0..21,
  including the Mihailovs recurrence used as an independent avoidance check.
  https://github.com/oeis/oeisdata/blob/main/seq/A047/A047889.seq
- `sources/oF12345a`: Nakamura and Zeilberger's Rutgers output, 40 terms indexed
  n=1..40. The parser prepends U_0=0 and verifies the entire OEIS overlap.
  https://sites.math.rutgers.edu/~zeilberg/tokhniot/oF12345a
  Context: https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/Gwilf.html
- `sources/b047889_0_24.txt`: exact first 25 lines of Gheorghe Coserea's OEIS
  A047889 b-file, n=0..24, verified from the official b-file on October 2, 2026.
  https://oeis.org/A047889/b047889.txt

The two .seq files and Rutgers output are unmodified local snapshots supplied
with the research investigation on October 2, 2026. The .seq files came from
OEIS's official oeisdata repository. A047889's official internal page
(https://oeis.org/A047889/internal) was independently rechecked during packaging.
Fresh retrieval of A224248 and the Rutgers output was unavailable at packaging
time; no claim is made that these snapshots are new independent downloads. The overlap checks and newly recomputed
exact terms provide independent checks of the consumed numeric content.

## Independent evidence and implementation provenance

`sources/independent_audit.json` is the unmodified `independent_checks.json`
provided by the separate baseline audit on October 2, 2026. Its elapsed runtime
is historical provenance only. Replay freshly recomputes and compares all 5,096
skew-dimension checks, the boundary row counters, and the saturation row counters.
Its assertions and historical PASS fields are never executed or accepted as
substitutes for those new computations.

`code/exact.py` is newly implemented for this companion from the mathematical
formulas and combinatorial definitions; it imports no prior report code or audit
code. `code/object_check.cpp` is copied without modification from the earlier
investigation's independent object-level validator. The optional `deep` command
compiles that source freshly and checks its complete output through n=10. This
is additional object-level evidence, not a third new independent implementation.

`checks/fixtures.json` records this companion's exact replay results. It is
validated against an executable strict field/type contract, recomputed from
scratch, compared with official-source terms, and cross-checked against the
separately supplied audit counters. No decimal estimate of R_5 is included.

## Mathematical references (not bundled and not needed by replay)

These are proof references, not runtime input files. Consult the article for
full citations and the exact statements applied.

- A. Bostan, P. Lairez, B. Salvy, *Multiple binomial sums*, arXiv:1510.07487;
  J. Symbolic Computation 80 (2017), 351–386.
  https://arxiv.org/abs/1510.07487
  https://doi.org/10.1016/j.jsc.2016.04.002
- A. Regev, *Asymptotic values for degrees associated with strips of Young
  diagrams*, Advances in Mathematics 41 (1981), 115–136.
  https://doi.org/10.1016/0001-8708(81)90012-8
- A. Regev, *Asymptotics of Young tableaux in the strip, the d-sums*, §3.1.4,
  the accessible normalization source for the four-row ordinary strip sum.
  https://arxiv.org/abs/1004.4476
- B. Nakamura and D. Zeilberger, functional-equation enumeration paper and
  programs, linked from the Rutgers page above.
- The Bóna–Burstein and Waite order-comparison results are discussed and cited
  in the article. A two-sided order estimate is not treated as a ratio limit.

The original proof audit and large third-party PDFs are not redistributed here.
This avoids an inherited companion dependency and keeps the computational
package small, offline, and independently inspectable.
