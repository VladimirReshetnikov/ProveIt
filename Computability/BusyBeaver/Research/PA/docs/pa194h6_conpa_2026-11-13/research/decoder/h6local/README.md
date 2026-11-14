# Local contraction screens on PA194H6

The input native table has SHA-256
`9c1daeb54c6e2e402bc5a0405925c1137c19e26280bcf455efe4c91d9a61111d`.
Both searches use conservative reachable windows of radius five (eleven
cells), initialized with every window at native start control 74. Unknown
exterior bits are overapproximated after each shift. Local simulations must
close within 300 transitions while reproducing the original tape, head and
continuation exactly. Neither search returned a contraction.

The common-action search processed all 194 working controls. It asks whether
two controls can share new first actions, with continuations through unchanged
rows. The incoming-edge bypass search processed 172 non-start controls without
self-loops, allowing each incoming row to choose a separate replacement action.
Its continuation avoids the eliminated state and all modified incoming rows.

These are finite sufficient contraction rules, not a global minimality test.
The preserved source code comes from the supplied PA194N research packet,
`research/physical/source/`, pinned in the parent report's repository snapshot.

```sh
c++ -O3 -std=c++17 action_merge_all.cpp -o action_merge_all
c++ -O3 -std=c++17 edge_bypass.cpp -o edge_bypass
./action_merge_all ../h6merge/inputs/PA194H6/machine.native.tm 5 300 > replay_merges.jsonl 2> replay_merges.log
./edge_bypass ../h6merge/inputs/PA194H6/machine.native.tm 5 300 > replay_bypass.jsonl 2> replay_bypass.log
```

The empty recorded JSONL files mean that no candidate was returned; the logs
record all processed controls. The complete candidate construction and its
universal certificates are separate from these unsuccessful searches.
