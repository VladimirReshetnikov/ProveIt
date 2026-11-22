# PA1944L source simulation

The [delivered PA1944L table](../../../../../docs/pa1944l_research_2026-11-14/machine/machine.tm)
has 194 working states and SHA-256
`c5787c6f2350e77183ca0d3ff25d2733ba87e8bb52cd54092d7fa26fcf4d5253`.
Its decoder reassociates four increments, changing the trie addresses
while preserving the 3,673 resolved primary source instructions.
The generator pins its table, label map, and sites and compares the
delivered instruction list byte-for-byte with the primary list.

Lean checks [the exact dense rows](PA1944LRows.lean), the model-valued
[register operations](PA1944LBoxAgreement.lean), and the
[58,320-step blank run to the source root](PA1944LInitializer.lean).
The [native iPRA theorem](PA1944LNative.lean) derives both directions of
the consistency equivalence conditional on the finite site checks.
[`PA1944LFinal.consistency_iff_literal_nonhalt`](PA1944LFinal.lean)
applies the checked certificate for all 3,673 sites and proves the
unconditional iPRA equivalence.

From the repository root, use the checked
[arbitrary-trie controller stage](../pa194lcc/README.md).

```sh
variants=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants
four_l=/dev/shm/pa1944l-model
four_l_coverage=/dev/shm/pa1944l-coverage
bash "$variants/pa1944l/check.sh" /dev/shm/pa194lcc-controller "$four_l"
bash "$variants/check-linear-coverage.sh" PA1944L "$four_l" "$four_l_coverage"
bash "$variants/check-controller-final.sh" PA1944L "$four_l" "$four_l_coverage" /dev/shm/pa1944l-final
```

## ConciseIPRA export

The [iPRA unification plan](../../../../../../../../../Logic/PrimitiveRecursiveArithmetic/UNIFICATION-PLAN.md)
uses this literal endpoint as a pilot for proof transport and shared arithmetic.

[`PA1944LConcise.consistency_iff_literal_nonhalt`](PA1944LConcise.lean)
transports the exact Foundation endpoint to a closed derivation in
`Prf PRAAx`. Its source sentence retains the same PA refutation predicate
and `machineHaltSentence PA1944LData.table 194`.

Use the final stage from the preceding replay. The export verifies the
delivered table hash above, preserves the stage's provider order, and
rebuilds the standard bridge against the selected Foundation objects.

```sh
lake build +IPRABridge.Standard
bash "$variants/pa1944l/check-concise-export.sh" /dev/shm/pa1944l-final /path/to/fresh-concise-export
```

## Replay with shared arithmetic

The PA refutation comparison in the literal 4L proof uses bounded equality
decidability. Its subtraction helper `IPRASubSuccSelfNonzero.native` now
uses the shared ConciseIPRA proof `LeanProofs.IPRA.not_succ_le_self`.
The bounded existential comparison uses `IPRABoundedSelector.selectorOpen`,
which reaches the shared finite search proof `LeanProofs.IPRA.Search.Finite.search_found`.
[`PA1944LSharedArithmeticChecks.lean`](PA1944LSharedArithmeticChecks.lean)
checks those paths in the proof values of the literal endpoint. It also checks
that the add-one, predecessor subtraction, and successor subtraction proofs
reach `LeanProofs.IPRA.succ_eq_add_one`, `LeanProofs.IPRA.monus_succ`, and
`LeanProofs.IPRA.le_succ_self`, respectively.

Build the current arithmetic modules, then reuse the checked machine and
coverage stages in the replay above.

```sh
lake build +DiophantineConsistency.IPRADifferenceStepClosure +DiophantineConsistency.IPRABoundedSelector
bash "$variants/pa1944l/check-shared-arithmetic.sh" "$four_l" "$four_l_coverage" /path/to/fresh-shared-arithmetic-replay
```

This replay snapshots the selected arithmetic and bridge objects and records
their hashes. It checks the unconditional Foundation theorem and its arithmetic
dependency and exports the same literal sentence to ConciseIPRA.
An optional fourth argument selects a compiled current arithmetic and bridge
provider instead of the workspace's `.lake/build/lib/lean`. The mixed replay
with the pinned model and coverage stages checked the source-current syntax
split in this way.

## Shared startup for LC_A and M4R

Lean checks that the 58,320-step PA1944L startup avoids dense controls
107 and 123. The [row comparisons](../PA194CommonStartupRows.lean) show
that LC_A and M4R agree with PA1944L on every other working control.
The [model startup theorems](../PA194CommonModelStartup.lean) transfer the
same trace to the two pinned tables in every arithmetic `IΣ₁` model.

The [LC_A](../pa194lca/PA194LCANative.lean) and
[M4R](../pa194m4r/PA194M4RNative.lean) native derivations use their exact
trie, register operations, and source root. The final theorems for
[LC_A](../pa194lca/PA194LCAFinal.lean) and
[M4R](../pa194m4r/PA194M4RFinal.lean) apply the checked aggregate for all
3,673 sites and prove both directions in iPRA.

```sh
common=/dev/shm/pa194-common-startup
bash "$variants/check-common-startup.sh" "$four_l" "$common"
bash "$variants/check-shared-trie-model.sh" PA194LCA "$common" /dev/shm/pa194lca-model
bash "$variants/check-shared-trie-model.sh" PA194M4R "$common" /dev/shm/pa194m4r-model
bash "$variants/check-linear-coverage.sh" PA194LCA /dev/shm/pa194lca-model /dev/shm/pa194lca-coverage
bash "$variants/check-linear-coverage.sh" PA194M4R /dev/shm/pa194m4r-model /dev/shm/pa194m4r-coverage
bash "$variants/check-controller-final.sh" PA194LCA /dev/shm/pa194lca-model /dev/shm/pa194lca-coverage /dev/shm/pa194lca-final
bash "$variants/check-controller-final.sh" PA194M4R /dev/shm/pa194m4r-model /dev/shm/pa194m4r-coverage /dev/shm/pa194m4r-final
```

The [seven archived variants](companions/README.md) have their own literal
row certificates and unconditional iPRA equivalences. Their proofs use
the verified PA1944L endpoint and model-valued simulations of the timing,
selector, and history-dependent changes.
