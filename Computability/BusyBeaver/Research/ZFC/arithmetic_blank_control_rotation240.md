# Blank240 and its packed control interpreter halt together in IΣ₁

[`ArithmeticBlankControlRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticBlankControlRotation240.lean)
proves the binary/control halting equivalence in **every model of IΣ₁**:

```text
∃ t, first (ArithmeticMachineRunRotation240.run t) = 0
  ↔
∃ k, ArithmeticControlTable.controlRun ControlCatalogueRotation240.table k
       (ArithmeticControlFile.liveValue 1 seedFile) = 0
```

Both `t` and `k` range over the model, including nonstandard elements.
The physical seed is exactly `[0,0,0,3,0,0,3,0,0]`. The theorem
`pairs_iff_blank_halts` also spells out its eight nested Cantor pairs, and
`blankSentence_iff_control_halts` connects the result to the existing fixed
`ArithmeticMachineRunRotation240.haltingSentence`.

The proof composes the [exact startup frame](arithmetic_startup_frame_rotation240.md),
the [arbitrary-entry simulation](arithmetic_control_simulation_rotation240.md)
and the previously checked startup shift. Whole-configuration halt absorption
handles a hypothetical halt before the 409,691-step prefix ends. There is no
time bound or additional simulation premise.

The [actual check](results/arithmetic-blank-control-rotation240-verification.json)
passes six axiom probes and eight typed callers with zero warnings and only
standard axioms. Source and audit took 2.078 and 2.087 seconds, using default
proof limits, one thread, 4,096 MiB and a shared 120-second limit. The exact
closure has 797 project prerequisites; no dependency family was rebuilt.
The [publication record](results/arithmetic-blank-control-rotation240-publication.json)
and [history](arithmetic-blank-control-rotation240/history.json.gz) preserve
the source, audit, guard, raw logs and independent source/API review.

This closes the internal binary/control equivalence at the explicit packed
table and physical seed interface. The final PA consistency sentence is a
separate composition with the upstream register/validator proofs. Those
upstream source claims and their fresh local verification retain distinct
statuses; this check does not assert a completed PA endpoint or unconditional
nonhalting. The already checked external Lean endpoint remains documented
[separately](rotation240_binary.md).

Attribution remains with Mira-Cult, Jeff Ketchersid, Andrew James Wade and
ProveIt, including the original calculus, machine and compiler framework.
