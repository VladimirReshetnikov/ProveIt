# Five-gate constant-folding addendum

Read [ADDENDUM.md](ADDENDUM.md) for the identity and complete ledgers. This separately frozen package supplies folded alternatives while preserving the original 44-file base packet.

Both native/spatial and phase4 now cost **603/478/476/479** operations for INC2;DEC2, ZERO3, NOP and POSITIVE3 respectively, with unchanged **60/58/58/58** positive witnesses and exact degrees **2344/1192/1192/1192**.

The whole native affine bridge is `192*(F+x)+2*theta+208`; phase4 is `768*(F+x)+8*theta+832`. Each costs 2M+3A. These are all-tuple polynomial identities with the corresponding original complete circuits, preserving every positive witness fiber. No optimality claim is made.

- `circuits/`: eight complete folded JSON circuits and eight textual arithmetic DAGs
- `reference/`: exact original native/phase4 circuit JSON files and the pinned base manifest, all self-contained and relatively addressed
- `emit_folded_clocks.py`: standard-library data-only deterministic emitter; use `--check` for read-only replay
- `receipts/`: deterministic generation/replay receipts
- `audit/`: separately written independent checker, note and receipt
- `MANIFEST.json`: this addendum's separate freeze

No repository, prior report, or frozen base artifact is modified. No author/base Python is run. The earlier zero-step circuits already have folded constants and remain unchanged.

Reproduce from this folder with standard Python3:

```sh
python emit_folded_clocks.py --check
python audit/check_folded_clocks.py --expect audit/independent_folded_clock_audit.json
python verify_manifest.py
```

All three are read-only replays. The independent checker uses only the relative reference files. Its optional `--check-live-base` argument can additionally verify the original 44 frozen files when the base package is available; portable replay does not require it.
