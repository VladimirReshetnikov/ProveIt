# Fixed85 omega source-context triage: second slice

This is a separate, non-overlapping source-context review of 83 selected
`omega`-containing lines in 20 local modules. No additional abstract-model
`omega` goal was identified at those individually inspected sites. This
is not evidence that Lean elaborates the tactics or that the fixed85 proof,
providers, axioms, or PDF connection are valid.

The slice deliberately favors files whose surrounding declarations mention
an arbitrary model V. The inspected subgoals use different, standard finite
values:

* `ArithmeticControlFrame215`, `ArithmeticHome215`,
  `ArithmeticMachineTape215`, and `ArithmeticRegisterBoxes215` use natural
  finite-control indices, scan budgets or list lengths. For example,
  `scanBound_actual` has model-valued tapes but explicitly declares its
  control indices as `Nat`.
* `ArithmeticSymbolicCore215` labels the inspected `bitsCode_prefix` and
  `repeat3_nat` bindings as ordinary-Nat equalities. `ArithmeticTilingTable`
  handles finite row numbers extracted as standard naturals before casts.
* The selected compact mask, byte, sparse-count, relabel and table sites use
  natural support positions, byte offsets, `Fin` values or list lengths. In
  `CompactWordFieldCyclic` and related constructed-word modules, the
  `omega` goal is explicitly a natural offset bound passed through
  `exact_mod_cast`; the adjacent target itself may involve V.
* `CompactRowComplete` derives model color bounds by first extracting a
  standard finite row; its other selected sites bound natural tile or rail
  data.

The receipt pins each selected source and records the exact line and local
classification. Anchors cover representative natural declarations. Source
inspection cannot determine all elaborator behavior, and a standard-natural
use of `omega` could fail for an unrelated reason. No compiled objects,
external modules, or axioms were checked.

The first triage packet inspected 63 lines in 26 different modules. This
second packet checks 83 lines in 20 additional modules. Both are selective:
there are unreviewed sites even inside some inspected modules, and the
remaining lexical inventory is substantially larger. The separately drafted
nine alternatives and the full fixed85 provider chain also remain
unelaborated.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-fixed85-model-omega-triage-slice2/check.py
```

The checker reads only pinned local source and inventory files; it does not
run Lean, stage a source, or inspect object providers.
