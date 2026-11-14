# Bounded searches below 194 states

No 193-state witness was found. These records are not a state lower bound.
The separately verified cached-controller 194-state construction is the
positive deliverable; search fitness and sampled runs are not its proof.

`search_ledger.json` is the authoritative summary. Interrupted runs were
stopped after freezing their logs; their last completed cycle gives a lower
bound on attempted mutation slots, not an exact terminal iteration count.
Across the seven stochastic runs the logged total is at least 24,295,755
mutation-proposal slots. Some slots skip a node without evaluating a new tree.
Do not describe this count as distinct trees, distinct tables, or proofs.

## Completed local-rewrite closures

The original, second, and cached raw parents have respectively 201, 202, and
201 working controls. The bounded rewrite closure visited respectively 192,
640, and 192 distinct labeled tables and exhausted each queue. Every closure
had best size 194. The rule uses radius-five (11-cell) all-tape abstract
reachable windows, at most 150 local steps, and pairwise control identification
with arbitrary first-action choices. It excludes the inherited arithmetic-box
states from merge endpoints. This is one sufficient rewrite rule, not all
correct machine transformations.

## Broader screening of decoder variants

The collector saved 1,000 194-fitness grammar files. Deduplicating reconstructed
raw tables left 606 tables. Each was compiled with an explicit simultaneously
checked two-cell fold witness to a 194-control table. The more general
11-cell/150-step local-action merger found no additional merge on any of them.
The per-sample record is `receipts/sample_receipt.json`. The hash list binds the
sampled grammar files; the bulky temporary sample files are omitted. They can
be regenerated using the fixed collector seed. The collector reached its
1,000-file cap after 461,038 iteration slots, before its time budget.

## Reproduce selected searches

Use C++17 and Python 3.10 or later. Work from `code/` below. None of these
commands needs network access or a repository checkout. Compilation output
and search outputs are temporary research material.

```sh
cd code
g++ -O3 -std=c++17 action_merge.cpp -o action_merge
python3 quotients.py reference_primary/tables/unfolded201.native.tm primary_replay 10000
python3 quotients.py ../inputs/second_unfolded202.native.tm second_replay 10000
python3 quotients.py ../inputs/primary_rawcached.tm cached_replay 10000

g++ -O3 -std=c++17 anneal.cpp -o anneal
./anneal ../inputs/seeds.txt ../inputs/leaf_attrs.txt joint_replay 600 202611141931

g++ -O3 -std=c++17 flat.cpp -o flat
./flat ../inputs/expanded_seeds_cached.txt ../inputs/leaf_attrs.txt flat_replay 5000 1200

g++ -O3 -std=c++17 collector.cpp -o collector
./collector ../inputs/expanded_seeds_cached.txt ../inputs/leaf_attrs.txt collect 600 202611142031
python3 sample_screen.py

g++ -O3 -std=c++17 screen.cpp -o screen
python3 order_templates.py
./screen order_templates.txt orders_replay 1440 1 compatible
```

The time-budgeted stochastic programs are not expected to reproduce exact
counts on different machines. The logged random seeds and exact input files
are retained. The interrupted runs used `occurrence.cpp`, `parameters.cpp`,
`headorder.cpp`, and `fast_order.cpp`; invocation shape is identical to
`anneal.cpp`. Their seeds, cached-controller setting, and logged stopping
points are in the ledger. Whole-head and parameter mutations were exploratory
schema-set-preserving search directions; no new candidate depending on them
is delivered or claimed proved.

## Provenance and dependencies

The starting repository commit is
`768c2be1a8e4d2fcf8aa3443c7b0f084d145734c`. The two input packets are
`docs/incoming/pa194_conpa_2026-11-13.zip` and its `(2)` companion. The cached
controller patch is recorded explicitly in the ledger. `reference_primary/`
retains the primary packet's compiler, helper verifiers, source material,
and original license notices. The search sources derive from that packet's
`screen.cpp`, `search_plateau.cpp`, `action_merge.cpp`, and
`search_quotients.py`, with modifications for combined seeds, occurrence
rotations, wider parameter exploration, and the declared bounded searches.
