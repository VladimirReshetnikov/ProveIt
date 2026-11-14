PA CONSISTENCY MACHINES: COMPARISON, CONSTRUCTION, AND VERIFICATION
================================================================
Research release, 14 November 2026

Read report/pa194h5_research.pdf for the complete report. Its editable LaTeX
source and all included fragments are beside it. This ZIP is self-contained
for the principal executable checks; no network or repository checkout is
needed to reproduce the delivered machines and certificates.

RESULT AND LIMITATION
--------------------

No machine with fewer than 194 working states was obtained.

PA194H5 is a new verified 194-state coefficient-five specialization of the
existing H architecture. It is a binary, deterministic, one-tape machine,
started on an entirely zero two-way infinite tape. The ordinary mathematical
proof establishes

    PA |- Halt(PA194H5, blank) <-> exists p Prf_PA(p, code(0=1)),

and hence PA proves that its nonhalting is equivalent to Con(PA). A separate
halt label is excluded from the working-state count, as in the source corpus.

The novelty claim is deliberately narrow. H5 is absent from the 76 concrete
194-state graphs in the pinned comparison corpus, including under the broad
structural symmetries checked. Its closest predecessor is H6: one native
decoder edge changes all 61 formula multipliers from six to five. H6 already
has the same command protocol, proof-search algorithm, and physical
architecture. Relative to M5, six controller rows also change. This is a
new verified combination/radix specialization of existing mechanisms, not
a new proof-search architecture. Graph novelty alone does not demonstrate
the stronger requested standard of a materially different design.

PA195EvenHX is the more substantial algorithmic construction in this release.
It visits only candidates 4,6,8,... while retaining every finite command word
as a possible prefix. The report proves this parity-prefix property and the
PA consistency calibration. The literal machine, complete blank startup,
and all source outcomes are independently verified. It has 195 working
states, so it misses the requested 194-state limit by one.

No new end-to-end Lean, Rocq, or iPRA theorem has been compiled. The proofs
of the PA biconditionals are ordinary mathematical proofs with explicit
inherited dependencies and separately replayed executable certificates.

START HERE
----------

  report/pa194h5_research.pdf    Full report and printed comparison/table.
  report/pa194h5_research.tex    Main editable LaTeX source.
  machine/machine.tm            Complete 194-state H5 dense table.
  machine/machine.native.tm     Equivalent native labels.
  proof/                       Mathematical proof and source/command checks.
  calibration/                 Inherited logical calibration dependencies.
  construction/                Portable builder and exact pinned inputs.
  verification/                Independent literal-table checker/receipts.
  comparison/                  All-packet ledger and all-table inventory.
  research/sparse/              195-state parity scheduler and its proof data.
  research/reduction/           Scoped negative searches, inputs, and replay.
  SHA256SUMS                   SHA-256 of every delivered content file.
  README_H5.txt                 Detailed original H5 construction notes.

EXACT MAIN MACHINE
------------------

  Working states: 0..193. Start: 0. Halt label: 194, with no outgoing rows.
  Blank symbol: 0. Initial head coordinate: 0. Tape coordinates: all integers.
  Each of the 388 rows is: state read write direction successor.
  Directions are L and R; every nonhalting transition moves one cell.

  Dense SHA-256:
  417e3940a77a6222ccd06885209cc853e572ac48b64acbabf581942f142304c9

  Native SHA-256:
  4448d94a91c04443a34b1d99015c13ee514fd1a9d2cff091616eb60aeece726e

  Allocation: 135 fixed controls + 67 AX readers - 8 simultaneous folds.
  All 32 local history/read-bit cases of the simultaneous folds pass.
  Source: 3,714 sites, giving 4,815 branch-sensitive physical outcomes.
  All 61 constructor blocks multiply by five; 3,409 outside source sites
  and their successors are exactly preserved under relocation.
  Independent literal audit: four list lemmas derived from the rows;
  1,121,654 symbolic operations; maximum case length 403; positive durations.
  Blank startup: exactly 58,088 literal steps to clean source entry 25,
  logical registers (2,0,0,0,0,0,0,0,0), and 26 one-valued spare registers.
  Complete tape, head, control, zero exterior, and dense/native conjugacy
  are checked. This is not a sampled-register test or a long-run heuristic.

The proof addresses hereditary recoding of variable labels, unused residue
four, nonmonotonic recoding and the restricted propositional head, the
equal-variable gate case, zero stack/implication aliases, the no-push MP
compiler's reserved dummy zero, final contradiction detection by Pop, and
the all-incoming-stores property required by the store-carrying scheduler.

ADDITIONAL 195-STATE MACHINE
---------------------------

  Table: research/sparse/even195HX/even195HX.tm
  Working states: 0..194. Start: 0. Halt label: 195. Rows: 390.
  Dense SHA-256:
  c1934e3132f577559e41df0fdb59f63ab9ef63963e705cfe26fdd6f2091c95f8

  Source: 3,674 sites and 4,781 outcomes, all independently checked.
  Four literal list lemmas; 1,068,285 symbolic operations; maximum case 392.
  Complete blank startup: 44,094 literal steps to source site 40.
  Independent 48-source-step bridge: clean entry 25 with counter 4.
  Exact source delta: one increment added at site 31, entered only from
  the fresh-candidate branch and skipped by the restoring loop.

Its physical H/X register swap is necessary for this startup certificate.
The first unswapped sparse trial halts and is not a consistency machine.
The source parity-prefix induction, not finite numerical testing alone,
is what establishes that every needed proof word is eventually tried.

COMPARISON SCOPE
----------------

Pinned ProveIt commit:
  2337ce611a26e308697ccbddb2a1636f989f01c3
  https://github.com/VladimirReshetnikov/ProveIt/tree/2337ce611a26e308697ccbddb2a1636f989f01c3

The audit covers the requested PA tree and docs/incoming, including nested
archives, five-column transition tables, and supported JSON encodings.
It contains 66 delivery records (61 filed packets and five incoming ZIPs),
1,594 recognized table occurrences, 670 distinct byte forms, and 567 complete
spanning action graphs. All 535 retained catalogue entries were independently
reproduced. The complete 194-state frontier contains 76 distinct graphs:
34 principal/supported, seven supplementary, 30 research auxiliaries/seeds,
and five rejected. These categories attribute the supplied evidence; they
do not claim fresh reconstruction of every historical PA proof.

All 66 deliveries and all 76 frontier graphs are compared in the PDF.
comparison/table_classes.json and occurrences.* cover all recognized sizes,
including larger machines and tiny fixtures that are not consistency claims.
comparison/git_manifest.json binds the scan to exact source blobs.

The two recognized 193-state graphs do not solve the blank-start problem:
one uses an inconsistent coefficient-three numerical calculus; the other
is correct on valid source frames but fails its blank initialization.
The new negative searches are limited to the specified finite or heuristic
families. They give no general lower bound for PA consistency machines.

REPRODUCE THE DELIVERED CERTIFICATES
----------------------------------

Python 3.10+ and the standard library suffice. Run without -O.

    python3 reproduce.py

This first checks every manifest hash, rebuilds H5 from the pinned local
inputs, compares literal/source bytes, checks all H5 command/source and
physical certificates, and repeats full canonical comparison with all 76
frontier graphs. It then rebuilds the 195-state scheduler, compares its
artifacts, replays its independent physical checker and exact source delta,
and runs the accompanying source/arithmetic checks. A new consolidated
replay_results.json is written; recorded certificates are not overwritten.
Temporary computations use the normal system temporary directory; set
TMPDIR to another writable directory if needed. Allow several minutes.

Options:

    python3 reproduce.py --checksums-only
    python3 reproduce.py --h5-only
    python3 reproduce.py --output /tmp/pa_replay.json
    python3 reproduce.py --bootstrap

The last option also compiles C++17 and replays the paired-row and physical-
permutation bootstrap experiments, asserting their exact recorded counts.
Other bounded discovery searches have retained receipts, not a claim that
the compact replay repeats every heuristic exploration.

The H5-specific driver remains available:

    python3 verify_all.py --frontier comparison/frontier_tables --output /tmp/h5_replay.json

To reconstruct the all-size inventory from a complete local Git repository:

    python3 comparison/audit_corpus.py --git-repo /path/to/ProveIt --out /tmp/pa_census

See that script's --help for optional source/census inputs. The bundled
inventory is already frozen; the ordinary replay does not access GitHub.

REBUILD THE REPORT
------------------

An ordinary TeX Live installation with LaTeX, AMS packages, Latin Modern,
microtype, booktabs, longtable, enumitem, xurl, hyperref and fancyhdr suffices.

    cd report
    python3 build_appendices.py
    latexmk -pdf -interaction=nonstopmode -halt-on-error pa194h5_research.tex

All included TeX fragments are present. The delivered PDF was compiled from
these sources and visually checked. Runtime-generated LaTeX auxiliary files
and temporary page images are intentionally excluded from the ZIP.

CREDITS AND PROOF BOUNDARIES
---------------------------

The logical foundations, compact source language, original PA machines,
H controller, radix family, and verification engines are credited to the
ProveIt repository and the imported research cited in the report. Original
copyright/license notices and file-level provenance are retained beside
copied code. ZFC scheduler/frame work supplies further inspiration; the
ConciseIPRA direction is assessed but no PA state saving is inferred from
its short rule inventory alone.

This release supplies two precise PA consistency calibrations and detailed
reproducible evidence. It does not claim a sub-194 result or a new 194-state
proof-search architecture, and it does not claim to settle the requested
stronger design goal.
