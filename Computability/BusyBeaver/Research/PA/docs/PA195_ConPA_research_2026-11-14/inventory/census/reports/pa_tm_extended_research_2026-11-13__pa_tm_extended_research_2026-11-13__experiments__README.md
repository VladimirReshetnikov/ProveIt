# Additional fixed-table searches

The source/grammar searches are documented separately in `README.grammar.md`.
The logical-presentation and spare-tail screens are in `README.additional.md`.

No machine with fewer than 196 working states was validated by these searches.
The exact counts and scope are in `search_receipt.json`. These finite searches
are not lower-bound proofs. They supplement the upstream PA196 result at commit
`407cdc356f6b586635e71ac92be394255f4bfea4`.

The Python drivers import the sibling `verification` directory. Run the commands
below from the package root. Python 3.10+ and a C++20 compiler suffice; no network
requests are made. Large local-context files and executables are regenerated,
not included. The symbolic executor's use of register-file lemmas is discussed
in the main report; a successful Python check is not a Lean kernel certificate.

## Coupled row and selector searches

```
python3 experiments/export_contexts.py
g++ -O3 -std=c++20 experiments/simultaneous.cpp -o experiments/simultaneous
experiments/simultaneous > experiments/simultaneous.log
g++ -O3 -std=c++20 experiments/direct.cpp -o experiments/direct
experiments/direct > experiments/actions.dat
g++ -O3 -std=c++20 experiments/general_selector.cpp -o experiments/general_selector
experiments/general_selector > experiments/general_selector.log
python3 experiments/check_selectors_all.py
python3 experiments/check_existing_selector.py
python3 experiments/make_coupled_cases.py
g++ -O3 -std=c++20 experiments/coupled.cpp -o experiments/coupled
experiments/coupled > experiments/coupled.log
```

The default export reproduces the original radius-12 context analysis. Passing
`--known-blank` to the export additionally uses the fact that cells beyond a
fully known finite tape suffix are zero. An affine gap whose length is not yet
known, and the interior of the arbitrary register file, remain unknown. This
second export changes the search space and hence the counts. The receipt records
both runs separately; the coupled search was completed for the first export.

`simultaneous.cpp` permits the retained state to recur while jointly selecting
its two rows. `general_selector.cpp` permits a new selector to write either
symbol and move in either direction. Two disjoint state identifications using
one new selector would save one state. The Python drivers test the complete
symbolic instruction contracts for the proposed table, including interactions
between the modifications. `coupled.cpp` additionally synthesizes the two rows
of an existing selector under the already-modified table, rather than treating
its original rows as immutable.

Each local run must preserve the complete known tape window and reach the state
and head position of the original transition. This requirement can miss valid
larger-scale simulations. Unknown cells conservatively reject a local path.
Local success is only a candidate screen: it does not replace the complete
symbolic instruction checks, the reachable source invariant, or blank startup.

## Reachability-aware quotient search

```
python3 experiments/flex_quotients.py > experiments/flex_quotients.log
```

For each eligible pair of states, this tests all four choices obtained by taking
its read-0 row from either member and its read-1 row from either member. Targets
are consistently renamed. Engine rows required by the register-file lemmas
remain protected. The final run uses the reduced source invariant and full
interval bounds supplied by `verification/flexible_core.py`: 4,954 reachable
contracts, 63,595 admissible tables, and no survivor. Repeated register-file
excursions, compensating increments/decrements, extra spare registers, and an
increased gap are permitted by that evaluator. Blank startup would still have
to be checked for a surviving table.

## The four closing-test variants

The four native tables in `auxiliary196/` replace the last AX `breakTo 1`
by a decrement test of a register known to be zero there. No discovery JSON is
needed: the exporter derives the unchanged paths and all other source
instructions from `verification/core.py`, changes site 3692, and excludes that
site's impossible positive branch. Select logical register 3, 4, 5, or 6:

```
python3 experiments/variant_export.py --register 3 --check-only
python3 experiments/variant_export.py --register 3
```

The first command checks all 4,959 constrained instruction contracts without
writing large context files. The second also exports the contexts and a derived
`experiments/variant.json` for subsequent searches. A supplied discovery JSON
remains supported through `python3 experiments/variant_export.py FILE.json`.

The C++ screens can then be run as above. For the two complete symbolic selector
checks, use `variant_check_selectors_all.py` and
`variant_check_existing_selector.py`. This export overwrites the derived files
in `experiments`; export the baseline again before returning to a baseline run.
All four variants remain at 196 states; none yielded a verified smaller table
in the additional searches. This mode reproduces the bundled one-row patches.
The receipt also records searches over regenerated DAG allocations of the same
source variants; allocation-dependent proposal counts may differ.

## Physical-register permutation observation

The eleven routing rows that read 1, write 0, and move right into the nine-state
skip chain can be retargeted by a physical-register permutation. Swapping
physical registers 1 and 3 was checked against all 4,959 ordinary instruction
contracts, with the corresponding logical-to-physical map. All 36 transpositions
were also screened for new ordinary three-step context folds; none appeared.
There is a structural reason why this particular allocator cannot benefit from
any of the 9! permutations:

1. A neutral selector row reads `b`, writes `b`, and moves right. The modified
   routing rows read 1 and write 0, so no neutral selector or its two successors
   changes.
2. Read-0 rows do not change. Every read-1 action in the class
   `(write 0, move right, skip state r)` undergoes the same injective relabeling
   `r -> permutation(r)`; all other read-1 actions are unchanged.
3. All action equalities used by a three-step context fold are therefore
   preserved. Incoming contexts obtained from neutral rows are preserved too.

This is an invariance statement for that allocator, not a claim that arbitrary
register permutations can never help a more substantial redesign.

The automatic-fresh-parameter idea `C = c + H + D + 1` was also considered.
It makes the gate's two inequality checks unnecessary, but property padding
only recovers separation. It does not recover atomic vacuity for every smaller
fresh variable label. Completeness of that modified calculus was not proved,
and it is not an accepted consistency-machine construction.
