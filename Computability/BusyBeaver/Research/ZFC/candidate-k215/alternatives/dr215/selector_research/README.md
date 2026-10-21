# Bounded shared-selector research

This self-contained directory records a failed attempt to obtain 214 states
by sharing one selector between two conditional-marker mergers. The input
`inputs/dr215.native.tm` is the new DR215 candidate. The second input is the
pinned primary K215 and is used for the earlier two-family receipts and a
synthetic search sanity control. This directory supplies no accepted
214-state ZFC candidate.

## Reproduction

Python 3 and a C++17 compiler suffice. No repository checkout, network,
third-party Python package, or optional SMT solver is needed.

```sh
python run_census.py --verify-recorded
python run_census.py --suite all
python positive_control.py
```

The first command checks hashes, pair inventories, and all recorded
accounting. The second freshly compiles the two small scanners and reruns
both censuses. It took about 95 seconds with two worker processes in the
original environment; the elapsed time is not part of the claim. The third
checks discovery on an artificially modified base. Its generated machines
are labelled as controls and have no ZFC calibration. Do not place them
among accepted candidate machines.

Use `--suite opposite` or `--suite same` for one census; `--limit 1` gives
a small wrapper check. `--output DIR` keeps new outputs elsewhere, and
`--compiler clang++` selects a compiler. Original receipts are never
overwritten. `--all-entry-directions` is a distinct larger experiment,
outside the recorded 200-family census.

Both original scanner versions are retained so the source hashes in the
receipts remain exact. `shared_selector_joint.cpp` fixes the first pair's
exceptional symbol to zero and the second's to one. The later
`shared_selector_general.cpp` infers either symbol from the shared branch
and permits two pairs with the same exceptional symbol. Otherwise the
algorithms are identical.

To run one family directly:

```sh
g++ -std=c++17 -O3 shared_selector_general.cpp -o selector
./selector inputs/dr215.native.tm 0 result 0 124 127 160 190
```

The four trailing integers are the retained and merged roles of each pair.
The preceding zero makes both exceptional entries move left; a one permits
either direction. The earlier special family shortcuts are 124 for
124/127 plus160/190, and 52 for52/176 plus160/190.

## Inventory and exact counts

`inventory/marker_pairs.json` records 21 pairs with a shared branch and
opposite predecessor markers on their exceptional branch, selected using
an inductive radius-five context analysis. This is a selected search
inventory, not a classification of all possible useful role pairs.
The scanner does not assume these inferred marker facts: it recomputes its
own radius-seven domain from all initial 15-bit windows and checks every
changed old role on every reachable abstract context.

`inventory/opposite.json` lists all 105 disjoint pairs of these pairs with
opposite exceptional symbols. `inventory/same.json` lists all 95 disjoint
pairs with the same exceptional symbol. Their orders match the receipt
arrays exactly. For every such family, the construction merges two pairs,
repurposes one old second-role label as the shared selector, and deletes
the other, giving a proposed 214-state table.

Each family contains

```
NUMSPEC = 2 * 4 * (2 * 2 * 214)^2 = 5,861,888
```

parameter specifications: two choices of retained selector label; two
choices for each of the two temporary current-cell writes; and, for each
selector branch, two writes, two directions and 214 working-state targets.
Both exceptional entry rows move left. NUMSPEC counts parameter
specifications; it does not assert that all resulting tables or behaviors
are distinct. Direction-widened runs multiply NUMSPEC by four.

| Census | Families | NUMSPEC total | Evaluated | Uniformly pruned | Survivors |
|---|---:|---:|---:|---:|---:|
| Opposite symbols | 105 | 615,498,240 | 368,996,023 | 246,502,217 | 0 |
| Same symbol | 95 | 556,879,360 | 338,410,309 | 218,469,051 | 0 |
| Combined | 200 | 1,172,377,600 | 707,406,332 | 464,971,268 | 0 |

The loop varies the selector/read-one row innermost. If a failed new path
never reads that row, every remaining assignment to that row has exactly
the same failed path while the outer parameters stay fixed. The scanner
counts those remaining assignments as uniformly pruned. This optimization
preserves the outcome of the bounded test. The receipts separate these
assignments from individually evaluated specifications.

## Matching test and limits

The abstract domain is the least finite closure of all initial binary
15-bit windows in start state0, shifting a new arbitrary boundary bit in
after each transition. It therefore overapproximates all binary-tape runs
from state0. For each old role affected by either merger, the scanner seeks
a common old/new endpoint reached after a positive number of transitions,
with mapped control and equal local tape and head, before either read
escapes the radius-seven window and within 97 transitions on each side.
The complete changed table is used, including possible reentry into a
changed state. Halting endpoints are matched as halting. Unchanged rows
are literal target-mapped copies.

Zero survivors means this bounded sufficient test found no candidate.
It does not prove that all tested machines have different halting behavior,
that shared selectors are impossible, or that 214 states are impossible.
Finite-window overapproximation, the 97-step limit, the selected role
inventory, and the prescribed edit shape all limit the conclusion.
Any positive result would require independent replay and a complete
unbounded simulation argument before acceptance.

## Other recorded experiments

The `recorded/` directory also retains two direction-widened family
receipts for each of DR215 and primary K215. Each pair of receipts covers
46,895,104 specifications, with no survivors. These can be reproduced with
the scanner's special family arguments124 and52 and direction argument1.
The primary receipts precede the pruning optimization and omit its separate
accounting fields; candidate counts, scope and survivor counts agree.

`recorded/synthetic_general_positive_control.json` records the expected
two hits after two provider rows are deliberately rewritten in primary
K215. `positive_control.py` regenerates that artificial input, compiles
the generalized scanner, and requires the same two hits. The control is
not a proof of completeness of the search implementation.

## Provenance

The primary table and comparison baseline pin ProveIt commit
`b6fb232916d008383e7cf2990d68ddb30fded7db`.
DR215 native SHA-256:
`fac930e9bc89fed41b631de2f12ef4e48e1c8625ef31ef093d4f14b340f113ad`.
Primary K215 native SHA-256:
`9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2`.
`manifest.json` hashes the exact inputs, code, inventories and recorded
receipts. Scratch paths preserved in old receipts are provenance only;
the reproduction wrapper uses paths relative to this directory.
