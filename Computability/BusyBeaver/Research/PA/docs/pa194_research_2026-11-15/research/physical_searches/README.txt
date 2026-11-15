Physical reduction searches, 14 November 2026 (Pacific date)

No accepted 193-state machine was obtained by the completed searches here.
These are finite checker searches, not lower bounds on possible Turing machines.

Inputs
- Primary PA194: ProveIt d8d4fb10149d6a76a56e615a35648c8c32847cf4,
  Computability/BusyBeaver/Research/PA/docs/pa194_conpa_2026-11-13/
  construction/tables/pa194.tm and pa194.labels.json, with source sites and
  instructions from construction/source. The native table is reconstructed
  from the supplied dense/native bijection.
- H5X/JH5X: docs/incoming/pa194_witness_research_2026-11-15.zip at the same
  commit; machines/PA194H5X and machines/PA194JH5X in its wrapper directory.
- MF: the newly delivered exact accelerated, marker-separated compositions.

Inherited engine assumptions
Within each input subdirectory, symbolic_runtime.py is the attributed existing symbolic executor. It models
arbitrary register lists using imported arithmetic-box contracts. It is not
an independent physical verification of those blocks and is not a Lean proof.
The MF copy makes only the proved marker-label change 51 -> 400 in SK and
BOXSTATES: native 51 then denotes the separate reader-history selector.
The original and MF arithmetic-box rows are identical under that renaming.

Search algorithms
1. whole_instruction_search.py identifies two non-box, non-boundary controls.
   Each replacement row is selected from one of the two original rows for
   that read bit. It checks first-occurrence continuation snapshots against
   complete primitive-instruction endpoints and then full contracts for any
   survivor. This was a fresh primary replay; comparable prior searches are
   documented in pa194c_conpa/search/local/SEARCH_NOTES.md.
2. one_row_search.py considers every pair with one literally shared read-bit
   row, keeps that row, and gives the other row every possible write symbol,
   movement and target among the remaining working controls. The finite
   continuation check allows 2,048 symbolic rules. Arithmetic-box controls
   and boundary control 84 cannot be removed or retained by these searches.
3. incoming_thread_search.py attempts deletion of a non-box reader. For each
   incoming literal row it separately tests every action over the remaining
   working targets against the instruction's original symbolic endpoint,
   forbidding any later visit to the removed reader. A survivor would require
   a simultaneous full-contract check and then a blank-start check. No
   completed run had any all-edge option set. This does NOT exclude repairs
   requiring several simultaneous rewrites to pass the preliminary check,
   a different representation invariant, or longer unrecognized traces.

Reproduce from a chosen input directory using Python 3.10+:
  python3 one_row_search.py
  python3 incoming_thread_search.py
Each script writes its receipt beside the script. Run without Python -O:
assertions in the inherited symbolic executor are certificate checks.
Runtime-dependent timings in receipts need not match. Counts and hit sets
are deterministic for these fixed inputs. No randomness is used.

Every negative result means no candidate passed the stated executable test,
not that every rejected table was proved incorrect. Primitive-instruction
contracts cover the displayed interface with arbitrary natural registers;
they do not establish the absolute PA-calibration theorem.

New 195-state auxiliary inputs
H5XD195 is the new h5X plus Gamma(D) logical-emitter research construction.
Its literal table has 195 controls. H5XD195_MF applies the same proved
acceleration/marker-separation transformations and still has 195 controls.
These two searches target 194 states, not 193; neither produced a reduction.
They are research inputs, not additional successful fallback deliverables.

Additional finite-window synthesis
joint_return_merge.cpp is copied unchanged from the prior
PA194B_PA194G_research_2026-11-14/research/physical_searches/src packet.
It propagates an overapproximation of radius-six local windows from the
blank start, then considers every unordered pair of working controls. Both
retained rows may use any write bit, move, and remaining working target.
The test requires the original one-step complete-window endpoint in at most
160 steps without reading outside the window, permitting repeated visits
to the replacement state. It checks jointly surviving row choices.
No transition into the halt label is newly synthesized. The positive
criterion is sufficient, and a negative result is not a lower bound.

Compile and replay, for example:
  g++ -O3 -std=c++17 joint_return_merge.cpp -o /tmp/pa194-joint-search
  /tmp/pa194-joint-search PA194H5X_MF/pa194.native.tm 6 160
The program writes hit JSON to stdout and deterministic counters plus
runtime to stderr. The empty hit files are retained intentionally.

SUMMARY.json gives every completed suite separately, with the actual input
state count. Do not add overlapping search counters and call them a count
of distinct Turing machines. INPUT_HASHES.json pins all literal inputs.
