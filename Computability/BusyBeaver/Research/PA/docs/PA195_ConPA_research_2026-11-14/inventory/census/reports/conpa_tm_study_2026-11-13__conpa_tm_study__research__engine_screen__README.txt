ENGINE-INCLUSIVE LOCAL DELETION SCREEN FOR COMBINED196

Result: no survivor among the three explicitly specified finite templates.
The broadest template deletes one working state and changes at most two rows.
For every admitted five-cell context it must reproduce the original one-step
endpoint within 16 child transitions without reading beyond offsets -2..2.
This is not a lower bound on the number of states in equivalent machines.

The input context certificate has 2,214 state/window pairs. It was collected
by adapting source_contexts.py from the supplied pa196_research_2026-11-13.zip,
pa196_research/search/local_folds/source_contexts.py. Its unchanged unary/list
engine infrastructure independently rederives the generic list lemmas from
the candidate table. The adapted inputs are exactly machines/h_only_mp_h.tm
and source.json here, and the literal startup length is 57,922. The collector
passed all 4,928 source outcomes and recorded 1,204,510 symbolic events.
Its source-derived contexts were intersected with an independent blank-window
closure. The original notices are preserved in the packet's provenance tree.

source_contexts_receipt.json records the exact table/context hashes and census.
screen_receipt.json records all three completed runs and their scope.
The first two *_results.txt files contain REJECTED representative trials;
they are not accepted machines. The broadest result file is empty.

To repeat the C++ screens against this exact admitted-context input:
  python3 research/engine_screen/reproduce.py

This takes a few minutes on a typical machine and needs g++. The script checks
both input hashes and requires zero survivors. It does not rederive the context
certificate. The packet's primary verify.py independently checks all source
contracts and the exact startup using its compact symbolic engine summaries.
