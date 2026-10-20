# One-row alternate 218-state layout

Only native `157/1` changes, from `1 L 148` to `1 L 187`. The [result](result.json) is a fresh invocation of the unchanged Source139 positive-diagram checker. It recomputes an inductive radius-7 window domain from every initial tape, checks all changed-row contexts with positive block fuel 97, and rejects an intentionally corrupted initial halt.

The result proves halting equivalence with K218 on every initial tape. It is another 218-state machine, with no new literal startup-time measurement. The canonical table is an exact breadth-first relabelling of this checked native table, including the terminal label.

From this directory, with fresh output paths:

```sh
python3 -B reconstruct.py --output /tmp/k218-row157-reconstructed
python3 -B check_joint_fold.py \
  --old ../k218.native.tm \
  --new /tmp/k218-row157-reconstructed/k218-row157.native.tm \
  --radius 7 --fuel 97 --output /tmp/k218-row157-check.json
```

The generic checker is copied unchanged from Source139. The reconstruction and composition are intake work by drop_contract. These executable mathematical certificates are not a Lean/Rocq theorem.
