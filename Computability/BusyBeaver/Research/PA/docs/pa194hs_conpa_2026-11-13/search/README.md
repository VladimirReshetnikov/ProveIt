# Bounded reduction searches

This directory reproduces the unsuccessful transition-reduction searches
performed for the PA194HS research packet. It is not a claim that 194
states is minimal.

```sh
python3 verify_reductions.py
python3 verify_reductions.py --search-merges
```

The first command verifies both frozen input machines' symbolic source
contracts and exact blank initializations. It checks that all 194 PA194HS
controls occur in the source/arithmetic/startup proof domain, reproduces
113 failed contracts for a shortened six-zero scanner, and replays a
finite witness of incorrect source-frame alignment. The second command
also repeats 62,073 specified state-merging candidates on each input.
Neither search finds a candidate passing all required source contracts.

The imported `symbolic_runtime.py` is copied unchanged from the pinned
ProveIt primary PA194 packet. Its arithmetic-block contracts are inherited
assumptions justified separately in that development. The new checker
changes none of the protected register-block rows. This executable search
is not an end-to-end formal consistency proof.

`evidence/negative_search_receipt.json` defines the exact finite search
space, bounds, hashes and limitations. `evidence/` also contains the raw
recorded logs and the complete shortened-scanner failures.

Two smaller local action searches can be repeated as follows:

```sh
g++ -O3 -std=c++17 local_search/action_merge.cpp -o action_merge
./action_merge inputs/primary/machine.native.tm 5 300 local_search/symbolic_patterns_k5.txt
./action_merge inputs/primary/machine.native.tm 6 1000 local_search/symbolic_patterns_k6.txt
```

Both produce no candidate on standard output; diagnostic lines go to
standard error. The frozen window sets are screening inputs, not a
separately certified complete reachable-context invariant.

The source snapshot is ProveIt commit
`1e407ae841e4666f932777fad977ba784ebbcfd5`; PA194HS is the new hybrid table
constructed in this task. Copyright notices and licenses for retained
source material are in `licenses/`.
