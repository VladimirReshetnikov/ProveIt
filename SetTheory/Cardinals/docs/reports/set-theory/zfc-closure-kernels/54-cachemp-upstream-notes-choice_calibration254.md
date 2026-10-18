# Standard-ZFC calibration of the literal 252-state machine

[ChoiceCalibration254.lean](../../Lean/BusyBeaver/ZFC/ChoiceCalibration254.lean) proves the closed external Lean metatheorem

```text
(¬ ∃ t, (machinePerm252.run t).state = none)
  ↔ ¬ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot.
```

This is the actual 252-state canonical table, with state 0, head 0 and a blank tape. The preceding binary/ZF endpoint includes its entire 82,552-step bootstrap, all 8,391 guarded instruction cases, the no-stray frame invariant, and positive-segment simulation. This adapter changes no machine row.

`constructible_choice` applies the [canonical-order theorem](constructible_order.md) inside the actual constructible subtype. That subtype supplies its own six-field ZF bundle, Power, Regularity, and the checked inside-L theorem `V=L`. Choice is derived there; it is not assumed in the ambient model. `constructible_models_ZFC` combines the checked ZF model with the exact sealed selector-Choice bridge, covering both branches of the repository's literal `ZFCax_s` theory.

`constructible_nonempty` exhibits a constructible empty ordinal. Its witness supplies an actual valuation for soundness of a finite ZFC refutation. From an arbitrary ZF model, the resulting inhabited L model contradicts that refutation; the existing external first-order completeness theorem then yields a finite ZF refutation. The converse follows by theory monotonicity. This is a refutation comparison through a different carrier, not same-domain model inclusion or all-sentence conservativity.

The final `blank_halts_iff_zfc_refutation` and `nonhalting_iff_zfc_consistency` declarations retain no model, Choice, `V=L`, nonempty-domain, coverage, bootstrap or runtime premise. They compose the exact ZF/ZFC refutation comparison with `BinaryPerm252.blank_halts_iff_zf_refutation`.

The [165-unit integration](results/choice-calibration254-integration-verification.json) freshly checked the maintained module and umbrella in 0.487 and 0.437 seconds, then passed 12 named axiom probes and eight meaningful callers in 0.472 seconds. It reused 163 source- and object-matched imports from the checked 164-unit closure. All 165 source identities and reused objects matched that checked snapshot. The absolute official Lean 4.32.0 compiler emitted no warnings; only `propext`, `Classical.choice`, and `Quot.sound` occur.

The [review record](results/choice-calibration254-review.json) also embeds the independent complete source audit and the initial scratch source/audit check: nine axiom reports and 15 callers passed. Earlier cache-overlay and optional-caller namespace failures are preserved as harness nonpasses, separate from those successful checks. The maintained source is byte-identical to the checked scratch source, SHA256 `c161c1b12599a6f60929fdc66f47dcfc77d78a12adf5ca8e2ca46c9e144787ae`.

The requested PA-internal proof-code and finite-trace comparison remains separate. Semantic completeness does not itself supply an effective coded proof translator or a PA proof of its totality and correctness. No internally serialized ZFC machine statement, unconditional nonhalting, or unconditional consistency theorem is asserted here.

The subsequent [167-unit integration](results/binary-zfc252-integration-verification.json) checks the independently supplied `ConstructibleChoice` and `BinaryZFC252` modules from `b3d82c2966`, the extended register endpoint, and every affected binary consumer. Both external ZFC routes pass against the actual binary objects and complete source-matched certificates. The original remote typed-stub check is superseded by this integration; the [remote-source review](results/binary-zfc252-review.json) preserves its scope.

