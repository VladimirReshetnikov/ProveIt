TWO MARKER-SEPARATED 194-STATE MACHINES FOR PA CONSISTENCY
Research report for Vladimir Reshetnikov
14 November 2026, Pacific time (15 November UTC)

RESULT

No justified machine with fewer than 194 working states was obtained.
This archive delivers the requested fallback: two materially different
194-state machines, PA194LCGMS and PA194LCGSMS, new within the recognized
corpus pinned to ProveIt commit:

  793c68737d94bffa4e32a75bce6cc8058d6d22f0

Both machines use one two-way infinite tape, alphabet {0,1}, blank zero,
and only left/right moves. Start at state 0, head coordinate 0, all cells
zero. Working states are 0 through 193. Label 194 is the separate halt
label and is NOT counted as a working state. There are 388 rows per table.
Each text row is: state read write direction next-state.

Definitive tables and SHA-256:

  machines/PA194LCGMS/machine.tm
  a168e6264a3963dec96a5f6f5dffd75d9f45cc4ed4cb31c80f3d2e8f23bcc312

  machines/PA194LCGSMS/machine.tm
  cdaa8211a08619263a0dc3cd5a6a3a62a02f506b360d738d20b25975246badf6

Native tables and dense/native label bijections are beside each table.
Native start is 74, native halt is 254. Native label 194 is a working state;
do not confuse the native numbering with the delivered dense numbering.

THEOREM AND PROOF STATUS

The complete new written relative proof is in proof/relative_proof.tex and
Section 3 of report/report.pdf. With totalized absorbing halting, it proves
in intuitionistic primitive recursive arithmetic (iPRA), for each exact
parent-child pair:

  H_parent(t) -> H_child(5*t)
  H_child(t)  -> H_parent(t)
  NH(parent) <-> NH(child)

The primitive-recursive simulation clock has increments 1, 3, or 5.
The proof uses exact row identities, a predecessor-bit invariant, and
quantifier-free induction. It covers every time, including intermediate
child times. The absolute written conclusion

  iPRA proves NH(child) <-> Con(PA)

composes this new theorem with the specifically identified revised AX11H
written calibration and the GH/GHS and LCG/LCGS relative transfers. This
is an inherited mathematical dependency, not an assumption that PA is
consistent. We reviewed the proof architecture and identified no concrete
error, but did not independently reconstruct every transitive proof recipe.
No new end-to-end Lean or Rocq kernel theorem is claimed.

The existing PA194B marker-separation idea is credited. The new result is
its compatible composition with the latest PA194LCG and PA194LCGS tables,
including their loop layout and return shortcuts. The changed decoder
branches recur after initialization. The tables are not mere renamings,
reflections, alternate roots, symbol exchanges, or halt-action changes of
any of the 520 recognized prior spanning 194-state action graphs, or of
each other. This is novelty in the pinned recognized corpus, not a claim
about all possible prior unpublished constructions.

READ FIRST

  report/report.pdf           Full report, proof, comparison and tables.
  report/report.tex           Main LaTeX source; includes other .tex files.
  RESULTS.json                Concise machine-readable result and status.
  PROVENANCE.json              Source commit, ancestry and attribution.
  comparison/families.csv      All 29 comparison families.
  comparison/named_designs.csv All 83 named baseline constructions/supplements.
  comparison/packet_ledger.csv All 97 delivery records (93 filed + 4 incoming).

The comparison also recognizes experimental, failed and diagnostic tables.
Its 520 spanning 194-state classes are NOT 520 proved consistency machines.
All 54 recognized spanning 193-state classes were separately examined.
Full ledgers, identities, literal representatives and limitations are retained.

VERIFY THE POSITIVE DELIVERABLES

Python 3.10 or later with the standard library is sufficient. Do not use
Python -O, since assertions are part of the certificate checks.
From the extracted archive root:

  python3 -B verify.py

The command checks every release-manifest hash; reconstructs both tables
in a fresh temporary directory; byte-compares native/dense tables and label
maps; runs the independent checker; and repeats novelty against all 520
prior recognized 194-state graph classes. It writes its logs and receipts
outside this frozen release. Optionally select that location:

  python3 -B verify.py --output /absolute/path/to/new-replay-directory

To replay the retained parents' full symbolic source contracts as well:

  python3 -B verify.py --full-parent

The exact original parent ZIP is bundled under references/. A full parent
replay passed during preparation: 9,552 source outcomes and 19,104 parent/
child duration contracts, with all local premises and startup checks.
Its recorded receipts are in verification/parent_replay/. That verification
binds physical interfaces; it does not complete the inherited PA proof in
a proof assistant.

The independent positive checker imports no construction code. It checks
all ordinary rows, all incoming-history edges, all four local traces, the
complete blank startup tape, and a further 10,000 synchronized parent steps
which include active use of the changed branch. The all-time mathematical
theorem follows from the written induction, not from extrapolating those
finite executions.

REPRODUCE THE ADDITIONAL RESEARCH

These searches were unsuccessful in the stated domains. They are not a
lower bound for arbitrary 193-state machines.

  python3 -B research/logical/replay_prices.py

This deterministically replays 4,222 frozen compiler-price cases. The four
600-second grammar searches made 42,111,449 proposals in total. Their C++
sources, exact seeds, templates, full logs and best grammars are included;
see research/logical/README.md. Elapsed-time runs can produce different
iteration counts on different hardware. Compiler prices are not completed
TM correctness or consistency certificates.

  python3 -B research/physical/search/reproduce.py --output /tmp/pa-ms-search

Requires Python and a C++17 compiler named g++ (or use --compiler). Rebuilds
the finite source closures and replays five stated table/envelope screens:
93,605 control-pair examinations and 965 single-control deletion targets,
all without a candidate. Adding --regenerate also rebuilds the symbolic
window envelopes. See research/physical/search/README.txt for exact domains.

  python3 -B research/coefficient3/replay.py

Replays the inherited 73,393-step numerical contradiction certificate which
rejects the coefficient-three calculus. Its final formula is numerical code
one; this is not a PA refutation. The coefficient-three experiment is not
a positive deliverable.

  python3 -B comparison/audit193.py --census comparison/census.json \
      --output /tmp/pa-ms-193-diagnosis.json

Examines all 10,422 blank starts of the 54 recognized 193-state graphs.
The recorded outcomes are 110 halts, 10,308 certified outward rays, and four
100,000-step caps. The caps are not claimed resolved by simulation; their
two originating proposals have separate logical/source-control failures.

To repeat the entire corpus scan, obtain the pinned ProveIt paths and run:

  python3 -B comparison/audit_corpus.py --root /path/to/pinned/ProveIt \
      --manifest comparison/source_manifest.json --output /tmp/pa-ms-census

The complete source repository is not duplicated here. Frozen census keys
and representative tables are sufficient for the offline positive novelty
check. The scanner's recognized table formats are explicitly documented;
it does not discover every table hidden only in arbitrary executable code.

BUILD THE REPORT

A standard TeX Live or MiKTeX installation with the packages named in
report/report.tex is sufficient:

  cd report
  python3 -B generate_appendices.py
  pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error report.tex

Appendices are generated from the delivered literal rows and CSV ledgers.
The PDF includes every transition of both new machines, all 29 families,
all 83 named baseline records, and all 97 delivery records.

INTEGRITY AND ATTRIBUTION

MANIFEST.sha256.json covers every release file except itself. Recordings in
research/ retain their additional original manifests and provenance. Some
original log receipts retain the preparation machine's paths; those are
provenance, not dependencies of the advertised portable commands.

The unchanged parent ZIP and original license/notices are retained. The
credited runtime and proof-search lineage includes James Chang, Andrew
James Wade, Elliot Glazer, Vladimir Reshetnikov and other ProveIt contributors
as attributed in the supplied packets. New work, inherited work, open
obligations and failed proposals are distinguished throughout the report.
