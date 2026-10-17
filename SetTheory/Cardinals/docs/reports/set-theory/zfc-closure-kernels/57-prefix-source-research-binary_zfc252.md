# Two checked external ZFC calibrations

[BinaryZFC252.lean](../../Lean/BusyBeaver/ZFC/BinaryZFC252.lean) and [ChoiceCalibration254.lean](../../Lean/BusyBeaver/ZFC/ChoiceCalibration254.lean) independently compose the same literal 252-state blank-machine/ZF endpoint with the constructible-model comparison. Both prove

```text
(¬ ∃ t, (machinePerm252.run t).state = none)
  ↔ ¬ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot.
```

The first uses the merged [ConstructibleChoice](../../Lean/BusyBeaver/ZFC/ConstructibleChoice.lean) bridge; the second retains the separately checked [ChoiceCalibration254](choice_calibration254.md) implementation. In both, Choice follows inside the actual constructible subtype from its own ZF, Power, Regularity, and `V=L`. An explicit constructible object supplies a valuation. External first-order soundness and completeness yield the refutation comparison; no model, Choice, `V=L`, coverage or runtime premise remains in the final machine statements. The updated [Endpoint254](../../Lean/BusyBeaver/ZFC/Endpoint254.lean) also gives the literal register program's ZFC-refutation equivalence.

The [167-unit integration](results/binary-zfc252-integration-verification.json) freshly checked all seven affected modules in dependency order: ConstructibleChoice, Endpoint254, BinaryPerm252, ZFCBoundPerm252, ChoiceCalibration254, BinaryZFC252, and the umbrella. It reused 160 source- and object-matched imports from the checked 165-unit closure. A header correction in BinaryPerm252 required refreshing all of its affected consumers even though its theorem bodies were unchanged.

The absolute official Lean 4.32.0 checks passed with no warnings. Eighteen named axiom reports and twelve meaningful callers passed, including both independent endpoints, the unfolded actual blank run, and the literal register-program endpoint. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Every current source and reused object identity was checked again afterwards. The [embedded independent review](results/binary-zfc252-review.json) distinguishes the original remote typed-stub test boundary from this successful actual-runtime integration.

These remain external Lean metatheorems. They do not provide the separate effective arithmetic proof-code and finite-trace comparison inside PA, an unconditional consistency/nonhalting theorem, or a new machine state reduction. The frozen machine table is unchanged.
