# Rejected intermediate allocation — not positive final evidence

`candidate.native.tm` has SHA-256 `289737cb4729000f9a68fa1a55a947189e9bfa1e833998590d168036c0c85598`. It is an earlier 215-state allocation using an invalid context shortcut at two CB1 wrappers. It is **not** the delivered consistency machine.

The initial decoder-prefix check did not inspect the full primitive return. The universal runtime replay rejected ordinal 4697 (`pc=11010011`, CB1). A direct finite replay subsequently established the actual error: with all logical registers zero, gap zero, and spare list `[0]`, the table returns to a complete dispatcher frame after 44 steps with control one-offsets `{0,1,2,6}` instead of `{0,1,3,4}`.

The final table corrects rows `117/1` and `214/1` to `0 L 302`; it returns the exact required complete frame after 156 steps and passes the entire universal replay.

```sh
python3 -B check_rejected_shortcut.py candidate.native.tm ../../machine/k215.native.tm
```

Run the command from this directory. The old startup receipts are historical diagnostics only. Although their nonzero top was independently identifiable as a native theorem, that logical observation cannot fix the invalid binary simulation. The final table instead initializes the standard clean zero-theorem seed in 95,726 steps.
