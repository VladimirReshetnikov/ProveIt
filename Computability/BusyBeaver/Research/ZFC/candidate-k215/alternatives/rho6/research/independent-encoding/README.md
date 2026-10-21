# Independent encoding investigation

This packet accompanies the positive construction in the main report. It records one decisive rejected 215-state construction and a controlled global allocator experiment. It contains no new accepted 214-state machine.

## A command-order counterexample

The primary K215 source uses NIP0, DROP1, MP2. Swap the two direct routing targets

- `134/1: 1R12 -> 1R135`;
- `174/1: 1R135 -> 1R12`.

This gives NIP0, MP1, DROP2 with the same 215 states and 430 rows. All source prefixes remain decodable. A separate observed symbolic run completed all 6,176 primitive cases, but this does not establish correct blank initialization.

The literal blank run reaches its first complete source root at step 494,760 with registers `[2,0,4,0,1,0,0,0,0]`, gap 128, and 172 unit spare blocks. The stack value is 4 = P(1,1), so its next head is falsity1. Since NIP has tag0 and no fields, candidate2 = P(0,1) represents `NIP; NIP`. The first NIP exposes the bad stack head, and the second halts. The binary machine halts after exactly **646,553 transitions**. The whole final tape has 409 one cells; every other cell is zero.

Run `python3 negative/reproduce.py` to reproduce the complete finite tape boundary and halt using a standalone literal simulator. The two row changes and all 430 rows are checked. This exact rejection does not depend on the separate primitive-check observation, whose per-case records were not retained here.

## Global contextual-role allocator

The two trial sources `combo001` and `combo003` are complete schema-parameter permutations from the formalism investigation. Each has 202 distinct source subtrees (including leaves), 179 internal subtrees, and 4,751 primitive occurrences.

The allocator allows all source nodes to move between existing physical states and lets an existing contextual provider represent multiple transformed logical roles. It derives fixed helper transitions from every original known-prefix traversal. It uses the inherited engine row catalogue only as a synthesis filter. An explicit local alias admits state108 for the `(CD6,CC2)` node under its `101` suffix, with state13 as the canonical representative.

The frozen model protects 207 rows: engine/helper rows plus the nonpure contextual entry rows. A source-identity control passes every one of the 4,750 internal prefixes and retains 215 physical states. Its table differs in one permitted routing row, `103/0 -> 0R13`, so this is a **source-identity control**, not byte identity or a fresh complete runtime theorem. The baseline table remains included unchanged among the inputs.

Under this precisely restricted model, HiGHS reports infeasibility for both trials: 17,711 variables/15,503 constraints for combo001; 17,718/15,514 for combo003. This is not a lower bound on all 215-state allocations, still less on all Turing machines.

The optional model keeps 188 engine/helper rows fixed and gives the remaining 19 contextual entry rows a keep-or-reassign choice. Its combo001 attempt used 20,745 role variables plus the 19 keep decisions and 319,239 constraints. It reached its 60-second solver limit (63.05 seconds measured) without a feasible incumbent. This is a **timeout**, not an infeasibility result.

Earlier experimental models v1-v3 rejected the source-identity control. Those unsuccessful models are excluded from this packet, and their outputs support no mathematical negative claim.

## Reproduction

Python 3, NumPy, and SciPy with `scipy.optimize.milp` are needed for allocation. The negative binary replay uses only the standard library. All inputs and inherited readers used by the portable allocator are included.

```sh
python3 negative/reproduce.py
python3 allocation/allocate_frozen.py --source allocation/inputs/sites215.json --output fresh-identity --seconds 60
python3 allocation/allocate_frozen.py --source allocation/inputs/combo001.json --output fresh-combo001 --seconds 60
python3 allocation/allocate_frozen.py --source allocation/inputs/combo003.json --output fresh-combo003 --seconds 60
python3 allocation/allocate_optional.py --source allocation/inputs/combo001.json --output fresh-optional --seconds 60
```

Each allocation output directory must be fresh. MILP timings and selected allocations may vary with solver versions. Every emitted table is subjected to a complete prefix check. Full quantified primitive runtime, safe blank initialization, and the source/calculus theorem remain separate obligations for any new successful allocation.

See `ATTRIBUTION.md`, `licenses/`, and `summary.json` for provenance and exact scope.
