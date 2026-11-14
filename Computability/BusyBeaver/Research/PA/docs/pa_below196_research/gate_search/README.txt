INDEPENDENT REVIEW OF THE GATE/GRAMMAR DISCOVERY SCORE

Run:

    python3 verify_gate_score.py

This portable check reads inputs.json, gate_variants.json, witnesses/*.json,
and the small attributed Python reference package included under reference/.
It does not require a repository checkout, network connection, C++ compiler,
or external Python dependency.

WHAT IS CHECKED

1. The symbols, prefix, six head families and suffix match the original
   supplied configuration. All eight exported gate words match the separate
   gate-variant generator's data, for both equality flips.
2. Every grammar production is topologically ordered, reachable, and distinct.
   Expanding the grammar yields exactly the selected 201-token macro word.
3. The symbol path attributes are independently recomputed by expanding the
   retained primitive source definitions. The full grammar's path attributes
   agree with the C++ witness; complete-program attributes are also recorded.
4. The physical reader table is reconstructed using the separately supplied
   Python layout builder. Fast and exhaustive helper enumeration agree on
   the eligible opposite-context pair set. Maximum matching agrees with the
   C++ fold count and effective reader score.
5. The baseline's complete ordinal source CFG equals the published program.

The baseline has 68 distinct reader nodes, seven eligible helper edges,
maximum matching six, and effective score 62. Adding the fixed 134-state
term gives 196. Its expanded AX height is 30; the complete program's maximum
path length is 38. These are different measures. The C++ field height is
the AX height, not the complete-program path length.

MODEL LIMITS

A maximum matching only identifies disjoint pairwise reader-fold
opportunities. Different folds can interfere through helpers, successors,
or changed incoming contexts. Consequently this score is a discovery
heuristic, not a certificate that all chosen folds work simultaneously.
No arbitrary-register physical instruction contracts, blank startup, or
PA consistency endpoint are checked by this review. Generating symbolic
case specifications does not mean executing or proving those cases.

AUDITED SEARCH REPLAY

The delivered run includes corrected recording of initial seeding and every
restart assignment/repair score. Replaying the same fixed iteration budget
and random seed preserves all eight final grammar witnesses byte for byte.
replay_stability.json records that independent comparison; search_summary.json
contains the corrected counters. The C++ header is parsed independently and
all nine arrays/scalars are checked against the JSON configuration used by
the review. The delivered witnesses are the audited replay's output files.

The final saved gates 1, 3, 5 and 7 have maximum zero runs 7, 8, 8 and 8,
respectively, outside the imposed six-zero filter. Their cost fields are
penalties, not physical state estimates. Invalid main-loop proposals are
not retained in the eligible witness pools; therefore a saved invalid seed
can be worse than the best raw diagnostic score observed for that gate.
For this run the saved gate-1 and gate-3 costs are 76 and 79, while the
summary reports observed diagnostic costs 75 and 77. These are compatible
measurements with different scopes, not valid candidate-machine counts.

ATTRIBUTION

reference_provenance.json binds the copied Python layout/checker and source
data to pa_tm_extended_research_2026-11-13.zip. These are supplied reference
implementations, not newly authored code. Their original licenses and notices
are retained. verify_gate_score.py is the newly authored independent review
driver. The original authors have not reviewed this new experiment.
