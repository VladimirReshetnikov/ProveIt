# Shortened scanner: conditional proof and exact rejection

**No accepted 224-state machine is present in this directory.** The patch
redirects normalized row `34/0` from `0 L 50` to `0 L 75` and deletes state 50.
It fails both a required primitive contract and an independent blank-start
obligation. All state numbers below are normalized K-labels.

## Replay the complete finite counterexamples

After running the main `reproduce.py`, use the extracted original archive and
the accepted DN4 table. From this directory:

```sh
python3 -B verify_short_scanner_rejection.py \
  --baseline /absolute/path/to/OUT/inherited/K225_Construction_2026-10-19/portable/results/candidate225.klabels.tm \
  --dn4 ../../machine/k225_dn.klabels.tm \
  --output /tmp/zfc_scanner_rejection.json
```

The standalone checker pins both inputs by SHA-256 and records the entire
finite tape supports. The retained receipt is `short_scanner_rejection.json`.

For original source leaf 40, with all nine registers zero and a zero first
spare, the original table returns to the correct successor after 586
transitions. The shortened table returns to a different PC after 662. The
earlier targeted symbolic run found failures in all 95 guarded cases on the
48 original source leaves containing six consecutive zero bits.

During DN4 initialization, the two tables reach exactly the same complete
configuration at state 34, head 0, after 47,000 and 46,198 transitions. The
tape has exactly seven zeros at positions 0 through 6. Two transitions later,
the original is still scanning at state 2, head -2, while the shortened table
falsely dispatches at state 84, head 0. A retained million-step diagnostic is
explicitly finite and asserts no eventual behavior.

## Replay the conditional unbounded runtime proof

The conditional checker uses the unchanged verification engine from the
pinned K225 archive. Pass its `baseline226` directory explicitly:

```sh
python3 -B short_scanner_conditional.py \
  ../../machine/k225_dn.legacy.tm ../../machine/sites.json \
  /tmp/zfc_scanner_conditional.json \
  --proof-root /absolute/path/to/OUT/inherited/K225_Construction_2026-10-19/portable/baseline226
```

All **6,083 guarded DN4 cases whose PC avoids six consecutive zeros pass**.
The proof covers arbitrary natural registers, arbitrary gap, and arbitrary
finite spare tails; all four traversal induction rules remain valid. Exactly
85 cases on 43 source leaves are excluded. The complete case array in
`dn4_short_scanner_conditional_cases.json` has SHA-256:

```text
9b624f451acc4948a914c6b2e84f7163325a12ca4cbc7e9a8a2d7cbc16da05ff
```

This proves the stated conditional local contracts. A new layout avoiding the
excluded paths would need a fresh full runtime proof, and the separate
seven-zero initializer defect would also need repair. Neither obligation is
claimed solved here. The complete zero-objective source walk is retained in
`../decoder/`; its best 225-state table has 39 six-zero source leaves.
