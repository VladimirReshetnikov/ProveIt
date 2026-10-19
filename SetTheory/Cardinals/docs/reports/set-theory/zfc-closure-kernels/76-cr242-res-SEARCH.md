# Discovery and verification of a 242-state local reduction

The successful construction deletes inherited state 15 from the pinned
Combined243 table, redirects `11/0` to 27, and repurposes `27/1` as
`1 R 22`. The source program and all other retained transitions stay
the same. The artifact is `../machine/zfc_context242_old.tm`.

`verify_reuse_independently.py` checks only exact literal tables, finite
incoming-edge inventories, and five complete local identities with arbitrary
exterior tape. It is independent of `local_fold.cpp` and the inherited
register interpreter. `local_reuse_proof.tex` gives the ordinary induction
converting these finite checks into halting equivalence from state 95 on
every initial binary tape and at every head position. No Lean/Rocq replay
is claimed by these files.

Run the independent proof checks with:

```sh
python verify_reuse_independently.py \
  ../reference/zfc_combined243_old.tm \
  ../machine/zfc_context242_old.tm --output independent_local_verification.json
```

## Search family

`local_fold.cpp` is exploratory C++17 code. Given a table, radius, and a
step bound, it first computes an inductive local-window overapproximation
from state 95 on **every** initial binary tape. The window has `2*r+1`
bits. After each literal transition the unseen new fringe bit can be
either zero or one. Thus the resulting finite pattern sets are an
inductive invariant, rather than a sample of a long run.

The search chooses a deleted state and a reused state, selects each row
of the reused state from one of those two original states, and redirects
incoming edges of the deleted state to the reused state. It first checks
all deleted-state entries, then tries to repair old entries of the reused
state by changing their target. With `full-repair`, write and direction
may change as well. It accepts a proposal only if all incoming boundary
rows admit positive complete old/new blocks ending with exactly the same
control state, head position and whole local tape, and neither execution
reads outside the fixed context. Endpoints exclude both internal states.
All repaired entries are rechecked with the resulting common patch.

This is a bounded discovery family. Failure to find a common endpoint
within the supplied window or step bound does not refute semantic
equivalence, and absence of a survivor is not a lower bound on machine
size. The independent proof is the preferred correctness evidence for
the successful explicit candidate.

Compile and rerun the principal discovery search:

```sh
g++ -O3 -std=c++17 local_fold.cpp -o local_fold
./local_fold \
  ../reference/zfc_combined243_old.tm \
  5 24
```

The initial radius-5 invariant has 91,549 state/window patterns. The
search tested 172,901 row-mixture proposals. There are six directed
survivors: two label orientations for each merger of state 27 with state
15, 50, or 171. These are three alternative machines, each with 242
working states. They consume the same unused branch and do not imply a
240-state combination.

Subsequent searches found no additional survivor:

| Input | Radius | Step bound | Repair choices | Proposals | Entry-screen passes | Survivors |
| --- | ---: | ---: | --- | ---: | ---: | ---: |
| Delete 15 variant | 5 | 24 | Target | 171,467 | 53,270 | 0 |
| Delete 50 variant | 5 | 24 | Target | 171,463 | 53,277 | 0 |
| Delete 171 variant | 5 | 24 | Target | 171,467 | 53,271 | 0 |
| Delete 15 variant | 6 | 32 | Target | 171,467 | 53,270 | 0 |
| Delete 15 variant | 6 | 32 | Write, move, target | 171,467 | 53,270 | 0 |

The corresponding output files are `*_results.txt` and `*_progress.txt`.
The stable delete-15 radius-6 invariant has 298,497 state/window patterns.

## Literal initialization check

The old table was run for 407,967 transitions from blank. Six old
`11/read0` events have a zero following bit. The new table was actually
executed for 407,979 transitions, and the resulting state, head and
entire set of one-cells agree exactly with the old result. The endpoint
is inherited state 96, head -5, with 351 ones from minimum coordinate
-6 through maximum coordinate 701. These coordinates give only bounds;
the check compared the complete sparse tape. The result is recorded in
`blank_comparison_d15.json`. The old event counts for the alternative
delete-50 and delete-171 variants are respectively 144 and 9, making
delete-15 the fastest initializer of these three variants.

The reproducible independent bootstrap script is
`check_blank_independently.py`. It performs both actual runs and compares
the entire tape; `independent_blank_verification.json` records its result.

The original source/compiler credit remains with Mira-Cult, Jeff
Ketchersid, and Andrew James Wade, with the subsequent reductions
credited as in ProveIt's pinned Combined243 provenance. This packet's
new contribution is the explicit state-reuse patch and its local proof.

Run these commands from the `research/` directory. The selected delete-15 table is maintained only at `../machine/zfc_context242_old.tm`; the two alternative tables here are search artifacts and spend the same branch.
