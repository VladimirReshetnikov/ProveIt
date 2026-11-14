# U208: a finite-history decoder fold for Con(PA)

Research prepared for Vladimir Reshetnikov, 29 October 2026.

**Result: a concrete 208-working-state, binary, single-tape candidate**, including
blank initialization. The primary dense table is machine/u208.tm; working
states are 0–207 and halt is the separate label 208. It starts in state 0,
head coordinate 0, with a two-way infinite all-zero tape. Every one of the
416 transitions moves left or right.

Open report.pdf for the comparison, complete proof, evidence boundaries,
rejected research attempt, exact identities, and every transition. Editable
LaTeX source is in report.tex and paper/.

## New reduction

Start from the exact Plain U209 native table. Delete state 211, redirect
every target 211 to 172, and change 172/read0 to (0, L, 214).
Exactly three retained rows change; no source instruction or address changes.

Two guards follow from all incoming histories of the old table:

* At state 172, the two cells to the left contain 10.
* At state 211 scanning zero, the cell immediately left contains 1.

The new representative simulates old 172/read0 in seven steps, old 211/read0
in three steps, and either read-one row in one step. The full tape, head,
and quotient state agree at every macro endpoint. All other 414 old rows
commute directly with the quotient.

This establishes halting equivalence with the supplied parent **from state 0
on every common initial tape**. For aligned runs:

    T208 = T209 + 6*N(172,0) + 2*N(211,0)
    T209 <= T208 <= 7*T209

The blank-input equivalence is PA-formalizable. Composing it with the retained
conventional numerical-calculus and U/PA calibration gives the intended endpoint:

    PA proves: not Halt(U208, blank) iff Con(U) iff Con(PA).

This package does not contain a newly exported PA proof or a new end-to-end
Lean, Rocq, or MM0 certificate. The local theorem is independent of that
calibration, which remains a documented inherited dependency. No unconditional
nonhalting, minimality, or historical priority claim is made.

## Comparison result

Five complete U209 submissions yield two rooted transition-graph classes:

| Submission | Graph class | Source depth |
| --- | --- | --- |
| Plain | A | 42 |
| Compatibility | B | 41 |
| Compatible Folds | A | 42 |
| Composed | A | 42 |
| Joint | A | 42 |

Compatible Folds and Joint are byte-identical; Plain and Composed are state
renamings. All five preserve 3,909 primitives and 5,083 control edges. The
PDF-only Joint supplement identifies the Plain machine and adds no sixth table.
The new local fold works on all five. The alternative 208-state Compatibility
variant is under machine/compatibility_variant/.

## Fresh verification

* Two independent local checkers, both normal and optimized Python.
* Complete depth-two/depth-three guard histories; four arbitrary-exterior macros.
* Eleven deliberately corrupted constructions rejected.
* Exact source bytes, all source control edges, totality, graph reachability.
* Complete 48,140-step identical blank trace to an admissible canonical frame.
* 5,084 fresh arbitrary-natural primitive contracts, four list/block laws.
* All 416 rows covered; 1,251,865 symbolic inference applications.
* 15,252 independent finite C++ cases, 6,778,830 literal primitive steps.
* All five parent quick replays and a full runtime replay for each graph class.

The primary U208 received a complete new final-table runtime replay. The
Compatibility U208 is supported by the portable local proof and its freshly
replayed parent; it did not receive a separate full final-table runtime replay.

## Offline reproduction

Python 3.10+ and the standard library, with assertions enabled:

    python3 -B reproduce.py

This validates the manifest, reconstructs the literal machine, checks local
proofs and all five parent comparisons, verifies source/startup, and freshly
rederives every arbitrary-value primitive contract. Fresh case records must
match the saved compressed records. Outputs are temporary by default.

    python3 -B reproduce.py --quick
    python3 -B reproduce.py --output /tmp/u208-replay

The quick option explicitly skips the fresh universal runtime derivation.
It still checks the complete new local preservation proof. Do not run the
main driver or the symbolic engine with optimized Python or PYTHONOPTIMIZE.

Optional finite C++ regression:

    g++ -std=c++17 -O3 checks/check_finite_runtime.cpp -o /tmp/u208-finite
    /tmp/u208-finite machine/u208.native.tm machine/sites.tsv

Rebuild the PDF in a working copy:

    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

## Identities

Primary dense table SHA-256:

    926d15c43daebdafd099723f265b073c25bf21a15e4c5593e669ccac6f70f8d0

Primary native table SHA-256:

    36b58fea7a184b1050914170e8f5240c8a13da218dbbfa7e1985cd73d516e5c7

Repository snapshot:

    343da82d7384d10ec9fd1c17361fc923b2d1d117

The complete primary parent archive, unary-theory archive, and PDF supplement
are preserved unchanged. Exact snapshots from the other four tables and
sources, archive hashes, and member provenance make the comparison auditable.
Original licenses and attribution are retained.

## Rejected research artifacts

The research/rejected_source_fold/ directory is explicitly an unsuccessful
attempt. It preserves the source control graph but damages shared
arithmetic-runtime decoders. Its standalone counterexample returns to
instruction 44 instead of instruction 28. Files named rejected208.* are
not the delivered candidate. The report explains the exact failure and why
it does not determine that exploratory machine's eventual blank-input behavior.
