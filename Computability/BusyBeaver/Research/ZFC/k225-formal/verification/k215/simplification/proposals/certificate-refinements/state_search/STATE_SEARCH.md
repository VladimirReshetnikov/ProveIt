# Fresh restricted state-fold search

## Result and scope

No 214-state machine was obtained. The fresh screen covers 21 current native
215-state tables, 155,277 eligible state-pair/table combinations, and
133,827,040 replacement-action checks. Every complete pair failed this
particular sufficient local proof test. This does not assert that every
trial machine has different blank behavior, and it gives no minimum-state
bound.

The algorithm extends the scope of the older one-identical-row search to
allow both read-symbol rows to change, provided each changed row's proof
does not use the other changed row. This is a new run and implementation,
not a claim to have invented two-row folding. The repository already records
a 3,567-pair, 20-step both-row screen in
`candidate-k215/alternatives/zero-spare/proof/engine_search_notes.md` and a
much larger shared-selector search in
`candidate-k215/alternatives/dr215/selector_research/README.md`.

## Precise family

For an input table T and a pair q < r, neither equal to the declared initial
state, identify r with q. For each read symbol b, compare the old actions
after this target identification. A literally shared action is retained. If
the two actions differ, their graph-history context families for that read
symbol must be disjoint. Search all two possible writes, two directions,
and retained working-state targets for a replacement action at (q,b).

Graph histories have length four. A history may stop early on reaching the
initial state, at which point the rest of the tape is unconstrained. Read
guards discard inconsistent histories. Each write updates the known cell,
and movement shifts all known relative coordinates. The resulting finite
sets overapproximate tape contexts at every actual reachable occurrence.

For every compatible history from each old role, the symbolic microblock
branches on every unknown initial tape bit. Success requires a positive
number of steps, exactly the old single-step head displacement, exactly
the target-mapped old successor, and exactly the old whole-tape mutation.
All other modified cells must be restored. Bounds are 45 microsteps and
200 explored symbolic nodes per local block. Halting before a matching
endpoint, leaving the finite represented range, or exceeding a bound fails
this proof attempt.

When both rows differ, a microblock for read b may not inspect (q,1-b).
This guarantees that accepting independent choices for the two rows would
compose. The search does not cover mutually dependent new rows, arbitrary
additional edits, new helper states, longer microblocks, deeper contexts,
overlapping origin contexts with more subtle stuttering equivalences, or
changes to the source program, arithmetic encoding, startup, or calculus.

The recorded action-check count is not a count of distinct complete
candidate machines. A pair with no passing first-row choice is abandoned
before searching the second row.

## Why a positive certificate would suffice

Suppose every old one-step transition on a reachable configuration has a
matching new positive finite microblock. Unchanged states satisfy this by
one literal step with renamed targets. For each merged role, the four-step
backward-history invariant supplies one of the checked context cases.
Unknown-bit branching proves the block for every completion of that
context; exact tape restoration makes the conclusion independent of the
rest of the tape. Row independence makes the selected block valid in the
complete new table.

Induction on old execution length constructs a new execution with the
same tape and head at each boundary and the identified control. An old
halting execution reaches the corresponding halt. An infinite old execution
produces infinitely many new steps because every simulated block is
positive. Determinism then gives equivalent halting behavior from the
common start. This argument explains the intended certificate semantics;
the C++ and Python implementations are not kernel-checked proofs.

## Controls and reproducibility

`controls.cpp` checks the known 69/400 marker fold, rejects an early-halt
corruption, rejects the cyclic 8/127 provider, and checks an artificial
two-row marker fold. Wrong and unspecified predecessor markers are
rejected in that artificial example. This tests meaningful positive and
negative behaviors; it does not establish exhaustive implementation
correctness.

Run, from this directory:

```sh
python3 run_search.py --repo /absolute/path/to/ProveIt --out fresh-results
```

Python 3 and a C++17 compiler are sufficient. Inputs are taken only from
the exact paths in `run_search.py`. `results.json` records
each table hash and complete counts; `provenance.json`
pins the repository commit and the exact executed source hashes. These two
files were copied from the completed `results-depth4/` run directory.
`counts.md` is the human-readable table. The original .input files and
binaries are regenerable intermediates, not required deliverables.

## Separate M125 inventory

`compare_m125.py` compares the literal four-row M125 instantiation against
available `.tm` files, including direct members of incoming archives,
under rooted state bijections with an optional global L/R reflection.
The resulting inventory is only about explicit table occurrences.
The parent investigation found that an earlier M124 note already permits
provider 125. Therefore this comparison must not be used to claim a new
mathematical family or an unanticipated construction, even when no literal
matching table is found.
