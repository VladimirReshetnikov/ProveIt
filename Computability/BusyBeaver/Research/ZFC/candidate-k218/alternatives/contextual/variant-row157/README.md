# One-row variant of the contextual218 alternative

Only native `157/1` changes from `1 L 148` to `1 L 187`. The fresh [result](result.json) passed the unchanged Source139 positive-block checker:1,001,257 inductive contexts,1,280 nontrivial contexts, old/new blocks at most2/3, and rejection of the corrupted initial-halt negative control. The [raw log](raw.log) is retained.

The invariant is independently recomputed from every binary initial tape; the positive diagrams preserve complete tape and head at their endpoints. This establishes halting equivalence with the contextual alternative for every initial tape. Both tables have218 working states. There is no newly measured startup clock for the variant and no217-state claim.

From this directory, use fresh outputs:

```sh
python3 -B reconstruct.py --output /tmp/k218-contextual-row157-fresh
python3 -B check_joint_fold.py --old ../machine/k218.native.tm \
  --new /tmp/k218-contextual-row157-fresh/k218-contextual-row157.native.tm \
  --radius 7 --fuel 97 --output /tmp/k218-contextual-row157-check-fresh.json
```

The generic checker is byte-identical to Source139's submission. The reconstruction, composition, and fresh invocation are intake work by `drop_contract`. Canonical numbering is a complete BFS relabeling of the checked native table; [map.json](map.json) includes halt254→218. No proof-assistant execution is claimed.
