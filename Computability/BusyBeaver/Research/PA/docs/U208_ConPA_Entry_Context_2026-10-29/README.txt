U208: ELIMINATING A STATE USING ENTRY CONTEXT
Prepared for Vladimir Reshetnikov, 29 October 2026

RESULT
======
machine/u208.tm is a complete deterministic binary, one-tape machine with
208 working states (0 through 207), separate halt label 208, start state 0,
blank symbol 0, head coordinate 0, and a two-way infinite tape. It includes
blank initialization. All 416 transitions move L or R.

Dense table SHA-256:
a2fee9e41311c0d43aaac871ea411be24eada17e6b3633c55f40b437101144e1

Native table SHA-256:
b348a466a2c316511e0037ea3824de29d4c6ad37338404fbc98a3968fdb25135

Read report.pdf for the full comparison, exact patch, complete local proof,
logical calibration audit, evidence, and all 416 transitions. Its editable
source is report.tex plus paper/*.tex.

NEW CONTRIBUTION
================
The six supplied U209 packages represent only TWO transition-table classes
up to rooted state renaming. Five proposals, including the PDF-only package,
are one class; Compatibility is the other. All executable proposals implement
the same ordered source and ordinal control graph.

The principal U208 construction starts with the exact Joint U209 table.
Delete native state 172, redirect 116/read0 to 211, and change 211/read0 from
0 R157 to 0 L217. No source instruction or address changes.

The key old-machine invariants are:
* Every entry to 172 has the two preceding bits 10.
* Every entry to 211 READING ZERO has a one immediately to its left.

These follow from complete incoming inventories, using at most three
transitions of history, on every initial tape from state 0. Four exact
whole-tape blocks simulate the special old transitions in 7,1,3,1 steps;
414 other old rows commute in one step. The internal revisit to the new
211 row is executed explicitly, so there is no circular helper assumption.

The exact clock is T208 = T209 + 6*N(172,0) + 2*N(211,0), hence
T209 <= T208 <= 7*T209 for halting computations of the principal parent.

PROOF STATUS
============
The new local theorem establishes halting equivalence from state 0 on every
common initial tape. Its blank arithmetic instance is PA-formalizable.
Composing with the explicitly retained U209 numerical/source/U calibration
gives the conventional mathematical endpoint

  PA |- not Halt(U208,blank) <-> Con(U) <-> Con(PA).

This release contains ordinary mathematical proofs and executable symbolic
induction evidence. It contains NO new end-to-end Lean, Rocq, MM0, or exported
PA proof certificate. It does not assert PA consistency, unconditional
nonhalting, a globally minimal state count, or historical priority beyond
the supplied proposals. The separate K215/ZFC result is not a certificate
for this changed table.

VERIFIED
========
* Exact 208-state/416-row census, target closure, and graph reachability.
* Four arbitrary-exterior local blocks, complete predecessor inventories,
  ordinary transition correspondence, and eight rejected corruptions.
* Independent local checker passes normally and with python3 -O.
* All six input tables compared through explicit isomorphisms and conflicts;
  all 418 PDF-only transitions freshly extracted and matched to Plain.
* All 3,909 source primitives and 5,083 ordinal control arrows unchanged.
* All 3,908 internal source-prefix interfaces checked against both tables.
* Exact common 48,140-step startup, including whole tape and full trace.
* Fresh 5,084 arbitrary-natural runtime contracts, four list-induction
  schemas, 1,251,865 symbolic inferences, all 416 literal rows covered.
* Full fresh parent-release replay for one representative of each input class.

The alternative machine/u208_compatibility.tm uses the same new idea on
the distinct Compatibility parent, with helper 214 instead of 217. Its
complete direct local preservation theorem is checked separately. The
alternative source is comparison/compatibility/sites.json. The
full fresh U208 runtime/startup receipts are for the principal table.

REPRODUCE OFFLINE
================
Python 3.10+ and its standard library; assertions enabled:

  python3 -B reproduce.py --output /tmp/u208-verification.json

This verifies the release manifest and exact reconstruction in a temporary
directory, local proof (normal and -O), alternative, six-way comparison,
startup, and all universal primitive contracts. It leaves the release
unchanged. The runtime phase takes a few minutes.

  python3 -B reproduce.py --quick

The quick command EXPLICITLY SKIPS fresh universal runtime derivation.
It is not a replacement for the default full replay.

  python3 -B reproduce.py --parent-replay

Also replays the retained full Joint parent archive. Parent replay was
performed during preparation; its receipt is included.

The comparator freshly extracts the PDF-only table when pdftotext is present;
otherwise it reports that extraction was not rerun and checks the retained
extracted table. To require fresh extraction:

  python3 code/compare_snapshots.py --root . \
    --output /tmp/comparison.json --require-pdf-extraction

Optional discovery, independent of the fixed construction:

  python3 research/discover_folds.py baseline/u209.native.tm \
    --output /tmp/discovery.json

The default discovery bounds are history depth 3 and macro length 7.
Negative search results are restricted screens, not minimality proofs.

Rebuild the PDF IN A WORKING COPY to preserve the sealed manifest:

  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

ARCHIVE MAP
===========
report.tex, report.pdf, paper/  Full research report and transition table.
machine/                      Principal/alternative tables, source, state map.
code/                         Fixed builder and verification programs.
evidence/                     Receipts and complete symbolic case records.
comparison/                   Six table/report snapshots, five source maps.
baseline/                     Complete Joint parent, theory ZIP, exact inputs.
research/                     Discovery script/results and audit notes.
licenses/, NOTICE.txt         Preserved attribution and terms.
SHA256SUMS                    SHA-256 of every other sealed payload.

Some detailed audit notes retain original source-archive paths for provenance.
Those paths identify the inspected upstream packets; the portable executable
commands above use only the included release paths.

SOURCE SNAPSHOT
===============
VladimirReshetnikov/ProveIt commit
343da82d7384d10ec9fd1c17361fc923b2d1d117, docs/incoming.
Exact Git blob hashes, SHA-256 identities, sizes, and pinned URLs appear in
baseline/source_manifest.json.
