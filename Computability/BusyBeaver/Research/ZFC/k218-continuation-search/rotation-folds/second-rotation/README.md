# Exact row duplicates after a second closed rotation

The experiment completed all 25 frozen first-rotation parents in
2.015 seconds. It found 2,000 pure, unique-child physical orientations, of
which 1,387 have closed, halt-free source factors. None creates two working
states whose complete pairs of transition rows are literally identical.

These are rotation specifications, not necessarily distinct resulting tables:
the family can include inverse rotations and repeated layouts. It does not
include general fold synthesis, equality after remapping self references,
three rotations, or arbitrary re-encoding.

The second rotation uses the same four-row rewrite as the reviewed root
experiment. Every first parent has the previously checked source and internal
prefix binding. Literal duplicate detection is run before the additional
first-37-address and zero-run constraints: since no duplicate exists even in
this larger physical family, no candidate can pass the more restricted family.
Consequently, the conditional new CFG and decoder checks were never invoked,
and no second-rotation source files or putative 217-state machines were emitted.

The script uses the already read K221 source/decoder utility modules, with
exact input hashes retained in [result.json](result.json). It executes no submitted
wrapper, compiler, general fold checker, or symbolic-runtime suite. New parent
runtime and blank initialization would remain necessary for a future positive
source construction. No lower bound or impossibility beyond this finite family
is claimed.

Reproduce from the repository root using the already published first layouts:

```sh
timeout 125s python3 -B Computability/BusyBeaver/Research/ZFC/k218-continuation-search/rotation-folds/second-rotation/search.py \
  --repo . \
  --inputs Computability/BusyBeaver/Research/ZFC/k218-continuation-search/rotation-folds/results \
  --output /tmp/k218-two-rotation-fresh
```

The 120-second internal bound is soft; the actual run completed all 25 parents
far below it. The separate 125-second process limit was not reached.
`drop_contract` authored and executed this census. `root` read the complete
driver, checked its stated superset argument and reviewed the existing output
accounting without repeating the search. No source, filter or theorem result
beyond the literal-duplicate family is asserted.
