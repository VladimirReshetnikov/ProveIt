# New source and physical-allocation search

## Result

No machine with fewer than 196 working states was obtained by this subtask.
The new experiments use the actual diagonal-vacuity and separate-diagonal
196-state source grammars from
`pa_consistency_comparison_and_new196_2026-11-13.zip`, rather than the older
201-token PA196 source word. Their respective macro word lengths are 191
and 190, including the final control token.

The imported allocator has 134 fixed working controls. Its two supplied
grammars have 68 generated AX reader controls and six compatible local
folds, for 196 total. This is a physical count, not the expanded primitive
instruction count or the source DAG count.

## New logical freedom examined

For each of the six unconditional logical heads independently, permute
its three numeric parameter roles D, H and A. The set of instances of each
head is exactly unchanged: every permutation is a bijection of N^3, and
the head is emitted for every numeric triple. Reordering these six heads
only changes their bounded stack selectors. The prefix, guarded gate,
separate diagonal head (where present), and trailing commands are retained.
The mixed search additionally uses the three already justified exchanges
of curried antecedents. It does not use the unsafe first-head
contraposition replacement.

## Exhaustive finite families

`direct_head_permutations.py` exhausts 6^6 = 46,656 choices for each of the
two fixed binary associations, for 93,312 parameter-substitution cases.
`direct_head_orders.py` exhausts all 720 orders for each association, for
1,440 additional cases. Both replace macro leaves in their existing positions;
they do not enumerate all possible newly associated source trees.

The allocator identifies its potential two-control context folds. These
form a bipartite graph between generated readers entered with preceding bit
zero and those entered with preceding bit one. If n is the number of new
AX readers and nu is the maximum matching cardinality of that graph, any
disjoint selection of the permitted pair folds leaves at least n - nu AX
controls. Helper interference can only reduce the usable subset; the exact
simultaneous local verifier checks that interference for promising scores.

For both fixed associations, the unique identity parameter choice has
n - nu = 62. Every nonidentity parameter choice has n - nu >= 66.
For both fixed associations, the unique original head order has n - nu = 62;
every other order has a larger bound. Therefore neither finite family gives
195 states through this particular allocator and pair-fold template. No
marker penalty was added to these matching bounds. The complete histograms
are in `head_permutation_exhaustive/receipt.json` and
`head_order_direct.json`.

This is not a lower bound for arbitrary source associations, other local
simulations, additional helper rewrites, or arbitrary Turing machines.

## Joint heuristic search

`anneal_head_variants.py` extends the archived fixed-word rotation search
with three kinds of semantic change: independent head-parameter
permutations, head-order swaps, and the three curried-antecedent exchanges.
The run uses `PYTHONHASHSEED=0` and random seed 2026111341, beginning with the
two checked grammars and 98 archived association ties.

Forty cycles with 2,000 attempted proposals each produced 72,629 applicable
proposals: 53,591 shared-subtree rotations, 11,844 parameter changes, 4,023
head-order changes, and 3,171 antecedent exchanges. Inapplicable rotations
are skipped and are not counted as checked proposals. The best reference
score remained 62. The best explored nonidentity-head variant had score
65. The score includes physical folding and explicit address/context
penalties; it is not itself a verified machine state count.

A second run held one selected nonidentity head permutation fixed during
each cycle, so the rotation search could not retreat immediately to the
original word. It used seed 2026111342 and 12 cycles of 6,000 proposals,
producing 62,001 applicable rotations. Its best changed-word score was 66.
Neither heuristic run reached the <=61 zero-penalty trigger for the complete
symbolic primitive-contract checker, so no new runtime or blank-start
machine certificate is claimed. Receipts and best witnesses are retained in
`head_association_search/` and `forced_head_rotation_search/`.

## Reproduction

The source bundle expects this directory beside `proof_agent/`, which contains
the formula emitter `axiom_variants.py`, and retains the self-contained
imported allocator under `selected_sources/`. The imported allocator's
license notices must accompany redistribution.

```sh
python3 comparison_agent/direct_head_permutations.py --limit 46656 --out comparison_agent/head_permutation_exhaustive
python3 comparison_agent/direct_head_orders.py
PYTHONHASHSEED=0 python3 comparison_agent/anneal_head_variants.py --cycles 40 --steps 2000
PYTHONHASHSEED=0 python3 comparison_agent/anneal_head_variants.py --force-single-head --cycles 12 --steps 6000 --seed 2026111342 --out comparison_agent/forced_head_rotation_search
```

The archive census and the 195-state diagnostic graph comparison are separate:

```sh
python3 comparison_agent/census.py --repo /path/to/ProveIt
python3 comparison_agent/build_comparison_summary.py
python3 comparison_agent/verify195_groups.py --repo /path/to/ProveIt
```

The repository must be at commit
`906367250a7f96c923147b10df392294bced7be5` to reproduce the pinned inventory.
The complete recursion opens every nested ZIP encountered; the resulting
`skipped_archives` list is empty. The table census recognizes complete
numeric binary tables in `.tm` and `.txt` members and repository `.tm` files.
It does not interpret arbitrary source code or JSON as a table format.
