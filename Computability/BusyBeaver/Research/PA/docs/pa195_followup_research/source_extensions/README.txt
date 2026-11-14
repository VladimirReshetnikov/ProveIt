FINITE SOURCE SEARCH EXTENSIONS TO PA195
======================================

Result
------
No sub-195 physical machine was found by these finite searches. This directory
contains new, explicitly equivalent source-calculus families, reproducible
search inputs, checked finite deduction templates, and exact run receipts.
It does not assert PA consistency, a new kernel-checked PA biconditional,
minimality of 195, or acceptance of a small table on a search score alone.

The source results are:
* 54 head-local parameter/antecedent choices, with the six heads permutable.
* Gamma(a) and Gamma(b) can replace Gamma(c) in the guarded diagonal gate.
  Both directions have explicit primitive-recursive proof translations.
* Outer antecedent exchange, a/b gate reparameterization, and four separation
  matrices give 48 distinct gate words, including the original PA195 word.
* Gamma can instead be bundled into the existing equality-witness head,
  restoring the old gate and preserving all nine pushed entries. Three
  parameter choices are supplied.
* All 51 distinct full words contain 191 macro tokens. Complete expression,
  register and stack identities are checked over a free algebra. The three
  Gamma-only grammars also expand to 3,700 source sites and 4,815 primitive
  cases, checked by independent path and interval CFG resolvers.
* Four concrete finite deduction trees prove the two projections, conjunction
  recombination, and outer antecedent exchange. A negative control is rejected.
* A syntactic argument rules out literal coincidence of an arbitrary Gamma
  clause with any retained head; it is not a nonderivability result.

Fast replay (Python 3, standard library)
---------------------------------------
From this directory:

  python3 verify.py --out /tmp/pa-source-family-replay.json

This runs all three independent finite checkers with and without Python -O,
compares their exact semantic receipts, writes only to temporary/output paths,
and leaves this directory unchanged. It does not rerun the heuristic searches
or certify physical scanner/runtime contracts.

The complete mathematical arguments are gamma_relocation.tex,
gate_extensions.tex, witness_bundle.tex, and coincidence_obstruction.tex.
They are report fragments, not standalone documents. The full report includes
them as appropriate. The actual AX parameter interface is addressed explicitly:
a=h+y and b=d+x, followed by reset d=h=0. The standard initial AX reset makes
every required auxiliary tuple reachable with nonnegative increments. Heads
are pushed even when the gate guard fails. No a!=b guard is assumed.

Search replay (C++17)
--------------------
Every subdirectory of search/ has its complete numeric header and source.
Build from the indicated subdirectory so the local header is used. Each run
writes .json and .ndjson files to the supplied output prefix. Suggested
commands, from this directory:

  c++ -O3 -std=c++17 search/head_search/search.cpp -o /tmp/pa-head-search
  /tmp/pa-head-search 1000000 147528 /tmp/pa-head-replay

  c++ -O3 -std=c++17 search/head_search/forced_search.cpp -o /tmp/pa-head-forced
  /tmp/pa-head-forced 160 198415 /tmp/pa-head-forced-replay

  c++ -O3 -std=c++17 search/gamma_search/gamma_search.cpp -o /tmp/pa-gamma-search
  /tmp/pa-gamma-search 240 244107 /tmp/pa-gamma-replay

  c++ -O3 -std=c++17 search/gate_search/gate_search.cpp -o /tmp/pa-gate-search
  /tmp/pa-gate-search 480 961138 /tmp/pa-gate-replay

  c++ -O3 -std=c++17 search/bundle_search/bundle_search.cpp -o /tmp/pa-bundle-search
  /tmp/pa-bundle-search 240 441572 /tmp/pa-bundle-replay

The first run exhausts 373,248 fixed-association head-role assignments plus
720 head orders, then executes its bounded stochastic phase. The other runs
use the displayed finite numbers of 10,000-proposal restart cycles. Proposal
slots, actual scored evaluations, accepted moves, seeds, and elapsed times
are separately recorded. Failed/irrelevant proposal slots need not invoke
the scorer. Elapsed time is machine-dependent.

Meaning of a score
------------------
The fixed inherited part has 134 controls; PA195 has 68 new reader controls
and seven compatible folds, giving effective score 61 and 195 total controls.
The scorer uses a geometry penalty for inadmissible layouts. In unpenalized
layouts, it first computes a maximum matching of local fold opportunities.
If the resulting optimistic effective-reader count is at most 64, it
exhaustively checks disjoint fold choices and whole two-cell trace contracts
within its specified local template. Scores above 64 may still use the
optimistic matching bound; they are not certified state counts. Every
potential score below 61 passes that exact local compatibility stage.
No such score occurred in these recorded runs. Even one that did would still
need full word/CFG binding, complete physical scanner and primitive-runtime
contracts, exact blank startup, and the arithmetic proof transport.

Provenance and limitations
--------------------------
provenance.json records exact source archive hashes and the repository pin.
OriginalProgram.lean is an unchanged inherited PA196 source snapshot. The
54 head variants follow the earlier incoming seven-head research, restricted
to the six ordinary heads. The new Gamma and witness-bundle proof translations
and source checks are supplied here. No historical-priority claim is made.
The inherited PA195 ordinary proof supplies the Con(PA) calibration; these
source-calculus equivalences do not replace it with a new Lean/Rocq endpoint.
