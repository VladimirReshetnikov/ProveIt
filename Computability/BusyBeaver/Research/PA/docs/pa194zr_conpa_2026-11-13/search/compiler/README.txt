Decoder and compiler research summary
=====================================

No machine below 194 states was obtained. The best retained score is 194.
The accepted PA194ZR construction is established separately, by the main
package proofs and checks, rather than by the searches recorded here.

Trusted accounted total: 90,819,000 iteration slots across 15 runs.
Unlogged tails of interrupted runs are excluded. Completed runs include
all configured cycles; progress is otherwise counted only to the last
fully logged 3,000-slot cycle. These are not distinct-machine counts and
not a lower-bound proof.

Run                                      Counted slots   Best score
original_68                                12,723,000          194
cached_67                                   9,963,000          194
symmetric_67                                9,903,000          194
h3_exchanged                                1,383,000          200
h6_exchanged                                3,600,000          196
h3_h6_exchanged                             1,383,000          199
h3_parameters                               2,763,000          198
h6_parameters                               6,000,000          196
h3_h6_parameters                            2,523,000          198
cached_return3_close6                       8,403,000          194
symmetric_return3_close6                    8,403,000          194
symmetric_return3_close3                    7,383,000          194
symmetric_return3_close3_alt                7,143,000          194
all_control_67                              4,743,000          194
all_control_68                              4,503,000          194

Normalization correction
------------------------
An early same-word normalization reused original leaf indices. Subsequent parameter/head-order mutations could assign different symbols to those indices, so the actual tree word could differ from its declared word.
Independent tree flattening rejected an apparent score-193 witness before any acceptance or consistency claim.
Normalization now renumbers every leaf in left-to-right order and asserts preservation of its terminal value; all parameter-search seeds are renumbered before mutation.
All seven affected dynamic runs are excluded completely from these totals.
Fixed-word runs remain valid; the final portable sources contain the fix.
Internal-DEC6 return cores that failed blank initialization are also excluded.

Reproduction
------------
Python 3 checks the input encodings and ledger:
  python3 check_inputs.py

Compile one of the C++17 programs under code/, then replay a run using its
input, replay_cycles, seed, and optional fixed argument in search_summary.json.
Use a fresh working directory: programs write parameter_best.json and its
.shape/.word companions there. The record includes source and input SHA-256.
For example, from this directory:
  g++ -O3 -std=c++17 code/search193all.cpp -o /tmp/pa_decoder_search
  mkdir replay_all67
  cd replay_all67
  /tmp/pa_decoder_search ../inputs/core103a_CS_close3.txt 1581 19310337 fixed

All-control search extends the one-history-bit fold test from AX readers to
all working controls other than the designated start. Every non-preserving
or non-right-moving incoming row marks its target ineligible for that
history assumption. Competing simultaneous folds are checked together.
The final two runs ended at 1,581 and 1,501 logged completed cycles.

The mathematical variants exchange the two antecedents of h3 and/or h6,
then optionally permute each schema's parameters and the six head positions.
Those exchanges have ordinary implicational proof translations. Their
search scores were not promoted to newly validated consistency machines.

Environment note: the compiler/version is recorded in evidence/environment.json.
Heuristic trajectories may differ across C++ standard libraries or floating-point
environments; reconstructing the accepted machine does not require these searches.
