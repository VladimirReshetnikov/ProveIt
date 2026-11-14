Logical-emitter searches: bounded unsuccessful research
======================================================

Six completed heuristic searches explored mathematically equivalent changes
of the source axioms. No 194-state or smaller allocation was found in these
runs, and none of their endpoint grammars was promoted to a literal machine.
They are supplementary research evidence; PA194QH does not depend on them.

                               Proposals       Best proposed count
h3 exchange, fixed parameters   1,800,000          200 = 134+72-6
h3 exchange, local permutations 3,600,000          198 = 134+70-6
h4 exchange, local permutations 5,400,000          197 = 134+70-7
h3+h4 exchanges                 5,400,000          198 = 134+72-8
separation matrix variants 1/2   7,200,000          196 = 134+69-7
separation matrix variants 1/3   7,200,000          196 = 134+69-7
TOTAL                         30,600,000

Counts include proposed mutations that do nothing and duplicate grammars.
They are not counts of distinct machines and establish no lower bound.
The evaluator's field effective_lower is inherited terminology for raw
readers minus jointly compatible folds; it is not a lower-bound theorem.
A zero scanner penalty is only a necessary screen, not physical correctness.
No full source-CFG or literal universal-runtime certificates were produced
for these unsuccessful endpoints. For scores at most 62 with zero penalty, the evaluator also checks the
two-cell fold sets for simultaneous compatibility. Thus the two best matrix
endpoints have that local check. The four h3/h4 endpoints are only optimistic
pair-matching scores; joint compatibility is not claimed for them.

Logical families
----------------
The two membership heads are
 h3: M(H,D) -> (E(H,A) -> M(A,D)),
 h4: E(H,D) -> (M(A,H) -> M(A,D)).
The exchanges reverse the first two antecedents, with the conclusion fixed.
The implicational exchange theorem provides both translations. The optional
local parameter permutations are bijections of each unrestricted schema.

For the guarded separation matrix put
 P=A -> M(A,D), L=M(H,D) -> P, R=M(A,D) -> A.
Variant 1 exchanges the conjuncts L,R; variant 2 replaces L by
 A -> (M(H,D) -> M(A,D)); variant 3 does both. The outer separation gate,
its guard and the separate diagonal head are retained. The equivalent-gate
mathematics was already described in pa195_followup_research; these are
fresh allocation searches, not a new logical equivalence theorem.

Inputs and semantic checks
--------------------------
All source words have 190 macro tokens. inputs/verify_head_words.py uses a
separate free-term evaluator to check the exchanged head, stack and register
effects for every generated local parameter choice. Run it with Python 3,
without -O. inputs/generate_gate_inputs.py similarly checks all four entire
AX emitter words, including their ten stack entries and top. The latter
regenerates its input/receipt files, so run it on a temporary copy.

The supplied A.param.input.txt has duplicate words for its two head-flip
values. We caught this by comparing the flattened word, and generated the
actual h3/h4 exchange words explicitly. The initial exploratory no-change
run is excluded. In the gate searches the inherited head-flip bits remain
no-ops; their metadata is not evidence of additional logical changes.

Reproduction
------------
Use a C++17 compiler. For example, with absolute paths to this directory:

 c++ -O3 -std=c++17 code/h4_search.cpp -o /tmp/pa_h4_search
 mkdir /tmp/pa_h4_replay
 cd /tmp/pa_h4_replay
 /tmp/pa_h4_search /absolute/path/inputs/h34.input.txt 1800 799137

Every source/input/cycle/seed tuple is recorded in summary.json. Run in a
fresh directory: these inherited executables write initial.json and
parameter_best.json with companion .shape and .word witnesses. No stochastic
search is needed to reproduce the accepted PA194QH table. Cycle caps here
were completed with exit code zero; each cycle has exactly 3,000 proposal
iterations. The captured log prints progress every 20 cycles and thus ends
before the final cycle number; successful process completion establishes
the full count rather than extrapolating an interrupted progress log.

Provenance
----------
code/*.cpp are task adaptations of
 PA/docs/pa194c_conpa_2026-11-13_1/research/association/code/
 association_search193.cpp.
inputs/input.txt is its exact inputs/A.param.input.txt. The changes freeze
selected nonbaseline logical variants, allow their specified permutations,
retain a broader near-optimal pool, and stop on a 194-state candidate. The
search and compatible-fold mechanism are inherited, not new algorithms.
helpers/free_term_reference.py is the unmodified supplied
 PA/docs/pa195_followup_research/source_extensions/verify_source_family.py.
The new input generators and receipts make the changed formula semantics
explicit. Parent package license notices apply to these inherited sources.
