# FM215 and proof compression for the ZFC construction

This is a research packet for ProveIt, pinned to commit
`b6c7087477e51c017003bd729e712c8969733223` (21 October 2026).
Read **report.pdf** for the full argument and **report.tex** plus **sections/**
for its editable LaTeX source.

## Results

1. **New FM215:** a four-row variant of the certified primary K215, with
   215 working states, a binary tape, L/R moves, and a separate halt.
   `formal/FM215.lean` proves exact halting equivalence from state 0 for
   every integer head position and every complete Boolean tape. All three
   modules compiled in Lean 4.32.0; the generic and FM215 endpoints report
   only `propext` and `Quot.sound`. The exact `.tm` bindings are independently
   audited. This is a standalone native-table theorem. Its adapter to the
   existing ProveIt zipper/dense consistency endpoint is described but is
   not yet compiled in that project. The ordinary composition gives the
   requested ZFC-formalizable nonhalting/Con(ZFC) equivalence.
2. **A smaller decoder certificate:** 234 context roles, 371 internal rules
   and 97 primitive-entry bindings cover the primary source's 4,750 internal
   occurrences. The finite checker and whole-tape framing argument establish
   internal traversal. The primitive operations themselves need separate
   runtime contracts; this is not an already compiled replacement for the
   entire site-coverage proof.
3. **Concrete proof refactors:** reuse positive simulation for small machine
   edits; port the existing Lean mirror-certificate idea to Rocq's still
   duplicated source checks; share decoder contexts. The report credits
   the three simplification phases already present in the pinned repository.
4. **A compiled logical obstruction:** the missing low-binder atomic vacuity
   cannot follow from the retained logical subsystem alone. The countermodel
   and Lean proof exclude nonlogical seed bundles, and do not decide the
   full large-matrix experiment's equiconsistency.
5. **No verified 214-state construction:** a bounded 1,761,648-row search
   and a separate 88,395-case helper family found none. These are limited
   families, not a lower bound. An explicitly rejected 214-state trial and
   a concrete runtime-contract counterexample are retained under
   `machine/research/` and must not be treated as an accepted candidate.

## Exact FM215 identity

| Artifact | SHA-256 |
|---|---|
| Parent native K215 | `9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2` |
| `machine/fm215.native.tm` | `3ece1233f11d33375425221c5bcedba941e073763912990eabf321197772dce5` |
| `machine/fm215.tm` | `1b602d3b37887060ce2d992cf3036f540e8ccff5d37ab06c80f19f1edd38cbc6` |

The exact patch, proof and canonicalization are in `machine/README.md`.
The native start/dispatcher/halt labels are 0/84/254; dense labels are
0/83/215. There are 215 working controls and 430 working transition rows.
All source tables are pinned by Git blob and SHA-256 in
`machine/source_index.json`. The all-tape theorem uses native labels;
`Fin 512` is only an ambient index type and does not change the working-state count.

## Reproduce the ordinary checks

Python 3.10 or later, standard library only:

```sh
python3 -B verify_all.py
```

This verifies the archive manifest, builds the exact native/dense FM215,
checks all 1,712 local obligations and the synchronized full blank prefix,
audits literal Lean bindings, verifies the decoder certificate (including
malformed-certificate rejection), checks the CM215 comparison, reruns the
finite tail countermodel, checks the rejected trial's concrete counterexample,
and matches saved compiler receipts to shipped sources and logs. Temporary
reproduction outputs are placed outside the packet. A PASS here is an ordinary
executable audit, not a newly executed Lean kernel check. Do not run these
assertion-based checkers under optimized Python (`-O` or `PYTHONOPTIMIZE`).

The startup check establishes exact tape equality after 95,714 parent steps
and 95,840 FM215 steps. The unbounded conclusion follows from the compiled
simulation theorem, not from this finite prefix.

## Replay the kernel proofs

Use the official **Lean 4.32.0** release. No Mathlib or ProveIt project build
is needed for these standalone files.

```sh
python3 formal/check_fm215.py --lean /absolute/path/to/lean
/absolute/path/to/lean research/tail-quantifiers/TailQuantifiers.lean
```

With a configured Elan installation, `lean-toolchain` pins the version and
`--lean lean` also works. The first command generates `.olean` objects and
refreshes the formal compile logs/receipt. The second prints the tail
theorem's axiom reports. Saved logs and source hashes record the successful
compilations performed for this packet; generated binary objects are not
shipped. Regeneration can change logs/receipts, so check `MANIFEST.json`
before rebuilding. The current `check_fm215.py` invokes the compiler
sequentially and then the independent 430+430-row data audit.

## Reproduce optional searches and corpus audit

Standard Node.js, no packages:

```sh
node machine/search_full_windows.mjs /tmp/fm215-full-window-search.json
node machine/search_markers.mjs /tmp/fm215-marker-search.json
```

The full seven-bit search has 1,029 eligible pairs and 1,761,648 proposed
replacement rows. Its 710,480-row adjacent-marker subfamily is included in
that count and must not be added. The marker script also runs the separate
88,395-case helper-resynthesis family. Bounds and rejection categories are
recorded in the scripts and receipts; bound exhaustion is inconclusive.

To repeat the novelty comparison, use a complete checkout at the pinned
revision:

```sh
python3 -B machine/verify_novelty.py --repo /path/to/ProveIt \
  --output /tmp/fm215-novelty.json
```

The saved audit covers all 622 `.tm` paths, including 321 complete reachable
215-state tables and 84 rooted transition graphs. FM215 matches none,
including global left/right reflection. This is a comparison with that
finite pinned corpus, not a universal priority statement.

## Build the PDF

A standard TeX Live installation with Latin Modern, AMS, hyperref, microtype,
booktabs, enumitem, fancyhdr and fancyvrb suffices:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The PDF supplied here was rendered and visually inspected. All report
sections are local; no network, external figure or bibliography download
is needed. PDF metadata and compression may vary across TeX installations.

## Incorporation

Keep the packet in one directory to preserve script-relative paths, or
adapt those paths as part of a reviewed integration. A suitable location is
`candidate-k215/alternatives/four-row-marker/` or a new dated research packet.
The report describes the small remaining native-label/tape-semantics adapter
for composing `FM215.blank_halts_iff` with `KEndpoint215`. The full original
calculus, source simulation, site coverage and startup proofs remain shared
dependencies; a short delta proof does not erase that inherited work.

`NOTICE.md`, `machine/NOTICE.md`, `machine/inherited_notices/`, and the source
indices preserve attribution and licenses. `provenance/` contains selected
pinned audit records and endpoint sources for convenient review, not a new
complete checkout or claim that the original formal development was freshly
rebuilt in this session.
