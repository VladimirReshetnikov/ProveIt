COMPARISON AND REDUCTION SEARCH FOR Con(PA) TURING MACHINES
13 November 2026

RESULT: NO VERIFIED MACHINE WITH FEWER THAN 196 WORKING STATES.

This archive does not fulfill the strict state-count target. It records the
comparison, two experimental 196-state command variants, paper proofs, exact
finite checks, and rejected candidates. The smallest certified baseline in
the archive is the published 196-state machine. Do not treat a failed or
experimental table as a certified improvement.

START HERE
  report.pdf       Full manuscript, including proof status and limitations.
  report.tex       Main LaTeX source; three additional .tex inclusions are
                   alongside it.
  code/verify.py   Portable replay (Python 3 standard library).

RUN
  python3 code/verify.py

The replay checks literal table identities, state counts, rooted graph
classes, eighteen local 208-state helper equivalences, exact blank startup,
the two one-row MP changes, source counts, bounded command/frame checks,
and the blank-tape halt of rejected Shift layouts. It also runs the upstream
publication/table checks. It does NOT build Lean or establish the new
end-to-end PA biconditional.

REBUILD THE REPORT
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

SOURCE SNAPSHOTS
  BusyBeaver PA196: 407cdc356f6b586635e71ac92be394255f4bfea4
  BusyBeaver PA209: 69d98241a721ead20b4f0b17df9062950b40fbfe
  ProveIt:         239b7a406e24405d464edc526e09d402abce5bc5

CONTENTS
  machines/                  Published tables and labeled 196-state variants.
  rejected/                  Bad Shift layouts; both halt after 43563 steps.
  sources/bb196/             Frozen upstream Lean/Python source and licenses.
  sources/history209/        Historical excerpts and new source experiments.
  sources/incoming208/       Census, main tables, local helper replay, proofs.
  sources/theory_audit/      Command proofs and PA-converse proof schema.
  research/                 Bounded exploratory searches and their receipts.
  licenses/                 Additional upstream license notice.
  SHA256SUMS                Delivered file identities.

IMPORTANT PROOF DISTINCTIONS
* The upstream source establishes PA |- Nonhalt -> Con(PA), and external
  nonhalting/independence. Its full Lean build was not rerun here; its
  publication/table checks were run successfully.
* report.tex includes an ordinary mathematical syntactic proof schema for
  PA |- Con(PA) -> Nonhalt. The new syntax-to-PA-proof compiler, its internal
  correctness theorem, the proof-code store invariant, and the final
  composition have not been implemented and checked in Lean.
* The MP command modifications have mathematical soundness/completeness
  arguments. Their concrete primitive-frame runs are bounded tests,
  not uniform proofs for all register values.
* Negative searches prove no state-count lower bound.
* The 208-state corpus contains many exploratory and rejected files.
  File count and graph-class count are not counts of accepted constructions.

The original incoming ZIP bytes are not duplicated. Their pinned URLs,
Git blob hashes and SHA-256 identities are in the full input manifest.
Only the compact subset needed by the included replay is extracted here.
Several optional exploratory scripts expect additional original material
or NumPy/SciPy/C++; the core replay has no such requirements.

LICENSES AND ATTRIBUTION
The BusyBeaver material is copyright 2026 James Chang and supplied under
its retained MIT license. Bundled Foundation/support material retains its
own notices. ProveIt material is under the retained MIT No Attribution
license. The newly written research scripts and manuscript portions in
this package may be used, modified and redistributed without restriction;
this statement does not replace or alter any upstream license.
