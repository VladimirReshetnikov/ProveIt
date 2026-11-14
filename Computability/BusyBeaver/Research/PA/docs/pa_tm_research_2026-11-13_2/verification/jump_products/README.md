# Products of validated zero-jump actions

No machine below 196 states is certified here.

Run `python3 replay.py` to reconstruct the inductive zero invariant, synthesize
the 12 / 6 / 13 recognized actions at native rows 27/1, 103/1 and 1365/1,
and check all 936 combinations including the original table. Among the 935
modified combinations, 264 fail because replacements interact; 671 pass
all affected uniform instruction contracts. Unaffected contracts retain
their literal baseline trace. The register-engine rows are unchanged.

Run `python3 replay.py --folds` to additionally rebuild and run the scoped
C++ fold search on all 671 runtime-valid combinations. It requires g++ and
takes several minutes. The recorded run found zero survivors. This search
uses one equal projected branch, one arbitrary helper-row repair, five-cell
simulations of at most 16 steps, and windows projected from the radius-six
inductively closed blank-tape abstraction. The result is not a lower bound.

`recorded_products.json` is the original complete receipt. The default replay
writes `reproduced_products.json` and does not pretend to rerun the larger
fold search. Individual runtime validity is not a claim of valid startup
for all 671 combinations.

`scan_local_folds.py` is copied from the pinned ProveIt PA research source.
`focused_helper.cpp` is a focused adaptation of its local-simulation search
family. `replay.py` is new work for this packet. The baseline table and
symbolic executor are supplied by the sibling `zero_jump_machine` folder,
with their attribution and licenses.
