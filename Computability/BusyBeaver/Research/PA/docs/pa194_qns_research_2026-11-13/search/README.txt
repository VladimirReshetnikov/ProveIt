BOUNDED REDUCTION AND SOURCE-CODING EXPERIMENTS
============================================

This packet records unsuccessful attempts to go below 194 states. The accepted
194-state construction and the fully checked secondary 196-state construction
are outside this optional search packet. None of these negative results proves
that 194 is minimal.

The repository reference is VladimirReshetnikov/ProveIt at commit
317b07268681b44ff352d173a162e2a8c241b2fe. FINAL_RESULTS.json is the authoritative
ledger of completed counters, interrupted-run lower bounds, scores and scopes.
Recorded output, exact final-run inputs and best grammar files are retained.
A mutation slot is not a distinct grammar or a distinct TM.

1. FINITE COMPOSITION SCREEN

  python3 -B combinations.py

This deterministically screens all 64 combinations of:
  * primary/Q exchanged-distribution AX grammar;
  * formula coefficient 4, 5, 6 or 8;
  * original/cached/symmetric-sum/cached-symmetric controller;
  * final emitter break or known-zero decrement of scratch register 6.

For each fixed unfolded table it enumerates the inherited three-step fold
opportunities, then all disjoint subsets and action choices, checking local
traces in the final simultaneously folded table. The best count is 194.
The coefficient-5/6 symmetric combinations have competing folds that both
remove native control 41, so their straightforward combination has 195 states.
The tested coefficient-8 layouts also have 195 states. This screen is only a
finite analysis of these particular tables and this sufficient folding rule.
It is not a complete search over all programs, source associations or quotients.

The portable replay reproduces recorded/combinations.json byte for byte.
It writes reconstructed tables and a fresh ledger under replay/combinations/.
Those tables include inherited and merely experimental combinations; their
presence is not a claim of a newly proved consistency equivalence for each.

2. COEFFICIENT-EIGHT LOCAL CONTRACTIONS

  node local_search.cjs data/radix8_195.native.tm 74 6 256

The 195-control candidate encodes proposed coefficient-eight increment bodies
and retains the seven primary AX folds. No complete source-correctness or
consistency theorem for this candidate is claimed here. The command tests three bounded sufficient contraction
rules: a same-head detour, a two-cell head displacement, and an adjacent
marker-bit toggle. The abstract window radius is 6 and the trace limit 256.
The initial window ranges over all bit patterns; newly exposed boundary bits
are nondeterministic. The recorded closure contains 274,355 contexts.
No contraction is returned. The shifted and marker rules consider 32,923 and
32,728 ordered pairs, with 1,569,120 and 952,917 candidate-action tests.
These numbers are scope descriptions, not lower bounds on unrestricted TMs.

3. ALTERNATIVE CONSTRUCTOR TAGS

The source word swaps the universal/equality tags (3/2) while keeping
implication/membership tags 0/1 and the coefficient four. The word expands
from 190 to 202 macro tokens. Ordinary fixed-control compression reached 198
states. Rebracketing the coefficient-four body exposes a triple-increment
helper and allows it to be reused in the AX emitter. The checked best uses
135 fixed controls + 71 AX readers - 10 simultaneous folds = 196 states.
Its grammar is best_grammars/tag_triple_196.json.

The final search allows occurrence-specific rotations, shared-subtree
rotations, six independent variable-role permutations in universal heads,
and Gamma(A), Gamma(D), Gamma(H) choices. Its score is reader states minus
compatible folds; add 135 fixed controls to obtain a projected total. The
physical construction and mathematical audit of the selected 196-state table
are in the main deliverable, not inferred from this optimizer score alone.

4. EXCHANGED EQUALITY-SUBSTITUTION PREMISES

The ordinary 190-token word is changed by exchanging curried premises in
head 3 and/or head 4, optionally also in head 6. The six new masks are
1,2,3,5,6,7; mask 4 is the already supplied Q design and is excluded from the
new search pool. Universal-head parameter permutations and the three Gamma
choices are allowed. These changes are licensed by the finite K/S/MP
premise-exchange derivation and the independent diagonal-head selector.
The final optimization score adds 134 fixed controls. Its best projected
count is 197 (134 fixed + 71 readers - 8 folds), retained in
best_grammars/exchanged_heads_197.json. These best grammars are search artifacts, not newly
certified smaller machines.

5. REPLAY THE MAIN COMPLETED SEARCHES

A C++17 compiler suffices. Compile from this packet directory:

  mkdir -p replay
  g++ -O3 -std=c++17 cpp/tag_fixed.cpp -o replay/tag_fixed
  g++ -O3 -std=c++17 cpp/tag_triple.cpp -o replay/tag_triple
  g++ -O3 -std=c++17 cpp/exchanges.cpp -o replay/exchanges
  g++ -O3 -std=c++17 cpp/screen_triple.cpp -o replay/parameters

Then run:

  replay/tag_fixed data/tag_fixed_input.txt data/leaf_attrs.txt replay/tag_fixed 180 271828
  replay/tag_triple data/tag_triple_input.txt data/leaf_attrs.txt replay/tag_triple 330 173205
  replay/exchanges data/exchange_input.txt data/leaf_attrs.txt replay/exchanges 330 141421
  replay/parameters data/tag_parameters.txt replay/parameters 3 46656 compatible

The three anneals are time-limited, so proposal counts can differ across
machines and with concurrent load. The fixed seeds determine the sequence of
random choices; the archive retains the observed logs. The parameter screen
completes exactly 3 * 6^6 = 139,968 cases. The two 330-second final anneals use
exact retained inputs. Earlier interrupted exploratory runs retain their logs;
only their last completed progress counters are reported as lower bounds.
The early discovery grammar is retained independently of those interrupted
runs. Replaying heuristic discovery is unnecessary for checking the accepted
physical machine, whose builder begins from its frozen grammar.

6. LIMITATIONS AND NEXT QUESTIONS

The search excludes different numerical calculi, alternate register encodings,
new primitive instructions, larger local simulations and arbitrary interacting
quotients. In particular, the fixed source grammar bounds do not imply a bound
on every consistency machine. Further progress could come from removing an
axiom-emitter head by a proved calculus simplification, or from a new tape
encoding that permits several control identifications at once. The changed-tag
emitter needs two additional states saved to meet 194, and three to reach 193.

Attribution and inherited licenses are in NOTICE.txt and licenses/. The Python
symbolic runtime retains its imported arithmetic-box contracts. No new Lean or
Rocq theorem is claimed by this search packet.

COMPLETED FINAL COUNTERS

Tag/Gamma: 1,647,198 proposal slots; 268,038 accepted; 330 seconds; best196.
Exchanged heads/Gamma: 1,727,732 slots; 342,713 accepted; 330 seconds; best197.
Neither final run produced a candidate at or below194.
