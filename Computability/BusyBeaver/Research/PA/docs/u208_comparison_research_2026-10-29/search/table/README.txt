Additional table-level searches for a machine below 208 states
============================================================
These searches did not produce an accepted smaller machine. They are bounded
heuristic searches, not lower bounds or exhaustive impossibility proofs.
They are newly authored code, not execution of supplied external programs.

Inputs: the two earlier verified U208 classes, native tables at
u209_reduction_20261029/table_search/candidate_4564c487/native.tm (Compatibility)
and candidate_89145587/native.tm (Plain). The current public proposals were
independently found to represent the same two graph classes.

1. general_one.py relaxes the previous literal-identity requirement on the
unchanged branch of a one-row merger. It tests multistep complete-tape identities
under eight-edge predecessor contexts; up to40 steps, head radius8, with unknown
bits explored universally. Compatibility:117,576 new action trials; Plain:
116,748. No hits. The unedited branch is required not to read the edited branch
before its first successful endpoint, then the final full edit is rechecked.

2. coupled_all.cpp allows both read branches of a merged retained state to
change, and allows paths to cross between these changed branches. Unlike the
prior two-row search, it does not require common unconditional conflicting
markers. Each parent:35,307,576 first-action trials. Compatibility:73,428,696
second-action trials; Plain:73,026,288. No hits. Bound:40 transitions, head
radius8,1000 symbolic search-node budget per context. Failure at a bound is
rejection by this search only. Predecessor facts are generated at depth8 by
export_cpp.py, with variables for all unknown tape cells. Removed state0 is
excluded. All ordinary rows commute under the candidate state identification;
the two exceptional states are checked for complete-tape/head/state endpoints.
The preliminary coupled.cpp run only kept first branches that actually entered
the unknown second edited row, and is subsumed by coupled_all.cpp. Its separate
counts should not be added to claim distinct candidates.

3. halt.cpp relaxes endpoint head/tape equality for old halt actions, and also
allows edited transition targets to be halt254. Only pairs involving state68,
the sole parent state with an immediate halt row, are considered. Each parent:
342,784 first-action and840,320 second-action trials. No hits. Other limits match
(2). This is not a general search over different halting predicates.

4. repair.cpp tries to repair a separate provisional207-state source-rotation
candidate (not accepted) by changing118/0 and one other helper row. The target
macro has input positions[-1,0,1,2]=[1,0,0,b], ends at head3 and state98 for b=0,
12 for b=1, leaving the complete tape unchanged. All old helper contexts must
retain their ordinary one-step endpoints through bounded blocks.341,964 inlet
trials and1,554,984 helper actions; no hits. Bound60 steps, radius8,2000 nodes.
The helper contexts come from the provisional table. A positive search output
would additionally require checking final-table contexts and a complete source
and runtime proof; none occurred.

5. repair3.cpp targets that same provisional source candidate with three edited
rows:118/0 and both rows of85. New source entries to85 have predecessor1, whereas
the deleted virtual old85 function requires predecessor0.685,584 inlet/zero-row
pairs and54,648 one-row trials; no hits. Same bounds and caveats as(4).

The raw input .dat files include literal tables and context facts. Logs record
actual search counters. g++ -O3 -std=c++17 builds the self-contained C++ programs;
pass the corresponding .dat file as argv[1]. All outputs in this directory are
negative search evidence only. No claimed PA/TM equivalence follows merely from
a search pass or finite simulation; any future hit needs an explicit invariant,
complete local proof, source calibration and independent universal audit.
