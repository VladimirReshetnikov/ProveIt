# Rejected tables: neither is a consistency-machine result

Both files contain 245 working states in the original labeling, with start 95, dispatcher 96, and halt 254. They are retained so their exact failures can be reproduced. Run `python3 -B code/verify_all.py` from the package root, or inspect the individual checkers described below.

## `tail_trap245.tm`

Starting from the old-label reference246 table, remove state 255 and replace:

```text
75 0 0 R 63
48 0 1 L 131
```

This was the sole survivor of the recorded finite register-macro screens across 21 two-row families. It is nonetheless invalid for the requested purpose. After three transitions of its own blank run it is in state 63. Both rows of every state in `{48,63,112,131}` move left and remain in that set. Consequently its nonhalting is provable by elementary finite-control induction. If ZFC is consistent, ZFC cannot also prove its nonhalting equivalent to `Con(ZFC)`, because that would prove its own consistency.

`code/check_rejected.py` reconstructs the table, checks every row of the closed set, and checks the three-transition blank prefix. This is an unconditional nonhalting proof for this particular rejected machine, not evidence for a Busy Beaver independence claim.

## `short_detector245.tm`

Starting from the old-label reference246 table, remove state 74 and replace:

```text
58 0 0 L 84
```

The shortened gap detector fails 36 original guarded instruction cases. A concrete failure is reached after 1,700 source instructions and 6,012,481 binary transitions of the **reference** blank execution. The comparison then starts the modified table at that reference configuration; it does not assert that the modified table's own blank execution has the same prefix.

The reference reaches normalized PC `11101001001000001` after 5,738 transitions. The modification reaches `11101001001001` after 5,818 transitions. The original source first reaches the latter PC 146 source instructions later with `W=10`, whereas the modified frame has `W=0`. The primary-register mismatch survives the workspace abstraction.

`code/threshold_literal_witness.py` replays the reference prefix and exact comparison. `results/threshold-literal-witness.json` retains the complete finite tape support at the witness. This rejects the claimed original-source simulation at that frame. It does not prove that every conceivable alternate calibration of the modified machine is impossible.
