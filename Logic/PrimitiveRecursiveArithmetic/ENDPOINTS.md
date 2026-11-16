# iPRA migration endpoints and replay inventory

This is the working inventory for the [unification plan](UNIFICATION-PLAN.md).
It records the exact proof boundary for each pilot and links to project
inventories for other variants and historical replays. Baseline source
reference is `99221756b5`, with the PA196 command-level result updated from
`c92515a005`. The root toolchain is Lean `v4.32.0`, with
Mathlib at `81a5d257c8e410db227a6665ed08f64fea08e997` and Foundation
at `32e1a0956a8622fad067328ca1959729a7634428`.

## Bridge and arithmetic

| Source declaration | Exact boundary | Check |
| --- | --- | --- |
| [`IPRABridge.standardToConcise` and `conciseToStandard`](Bridge/Lean/IPRABridge/Standard.lean) | For a closed source sentence and derivation, derive its translated sentence in `Prf PRAAx []` or Foundation `standardTheory`, respectively. `conciseProvable_iff` reflects derivability for Concise sentences and their Foundation images. | `lake build IPRABridge`. Audit the exported theorem types and use `#print axioms` on theorem dependencies. |
| [`IPRABridge.Checks.addCore_left_cancel`](Bridge/Lean/IPRABridge/Checks/Arithmetic.lean) | Foundation `standardTheory` proves `∀ a b c, addCore(a,b) = addCore(a,c) → b = c`, by transporting the ordinary Concise proof. This example uses the recursion-first symbol `PRALanguage.addCore`. | `lake build +IPRABridge.Checks.Arithmetic`. The baseline reports `propext`, `Classical.choice`, and `Quot.sound`. |
| [`pra_iff_native`](ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean) | Ordinary Concise derivability of an arbitrary finite-context sequent is equivalent to `NPrf` of its scalar reading. | `lake build +ConciseIPRA.NativeBiInterpretation`. The [ConciseIPRA index](ConciseIPRA/README.md) identifies the article and checker benchmarks. |

### Integrated replay of the lighter bridge

The following focused runs used the normal root Lake providers after the
standard-theory import split. They reused compiled toolchain, Mathlib and
Foundation dependencies. The measurements use `/usr/bin/time -v` on each
`lake build +<module>` command, with memory rounded to the nearest MiB.

| Module | Elapsed | Peak resident memory |
| --- | --- | --- |
| `IPRABridge.Checks.Roundtrip` | 13.6 s | 1,732 MiB |
| `IPRABridge.Checks.OpenSequents` | 9.3 s | 1,747 MiB |
| `IPRABridge.Checks.ScopedSequents` | 5.9 s | 1,747 MiB |
| `IPRABridge.Checks.Arithmetic` | 9.1 s | 1,757 MiB |
| `BusyBeaver.PA196.IPRAAssembly` | 4.7 s | 1,729 MiB |
| `IPRABridge` | 1.7 s | 791 MiB |
| `DiophantineConsistency.IPRASubSuccSelfNonzeroChecks` | 14.4 s | 1,764 MiB |
| `DiophantineConsistency.IPRADifferenceSuccEq` | 51.7 s | 1,797 MiB |

All runs exited successfully. The axiom checks for the migrated proofs
reported `propext`, `Classical.choice`, and `Quot.sound`. The
[source closure check](Bridge/check-import-closure.lean) also passed for
the full portable library, the Foundation statement layer, and the
public bridge and order-symbol comparison.

## BusyBeaver PA

The standalone BusyBeaver default build was checked separately from the root
workspace. From a Git archive containing `lean-toolchain` and the three
tracked Lean source directories for BusyBeaver, FirstOrder and ZF, run
`lake build` in `Computability/BusyBeaver/Lean`. The fresh build completed
five jobs in 3.13 seconds and peaked at 510 MiB resident memory. The second
run took 0.15 seconds and peaked at 107 MiB. The standalone `.lake` directory
used 1.9 MiB. The source closure report also matched the root `BusyBeaver`
target's 603 transitive imports and resolved the standalone `Core` and
`KnownValues` sources.

- **Primary PA194.** [`PA194NativeLiteralFinal.consistency_iff_literal_nonhalt`](../../Computability/BusyBeaver/Research/PA/verification/pa194/ipra/native-endpoint/PA194NativeLiteralFinal.lean)
  proves `standardTheory ⊢ nativePAConsistency 🡘 ∼PA194ExplicitEndpoint.haltSentence`.
  The two-way blank-tape table has SHA-256
  `4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f`.
  The [Concise export](../../Computability/BusyBeaver/Research/PA/verification/pa194/ipra/native-endpoint/PA194NativeLiteralConcise.lean)
  proves its exact translated sentence in `Prf PRAAx []`. The baseline
  [native and Concise replay commands](../../Computability/BusyBeaver/Research/PA/verification/pa194/ipra/native-endpoint/README.md#conciseipra-export)
  use ordered staged providers. For the checked Concise export at commit
  `2569da8be4`, the direct `PA194NativeLiteralFinal.olean` SHA-256 was
  `d81158ad314dbec493a8008fc15e6b80284eea7323b3af301d111ea429af39a3`
  and the export object SHA-256 was
  `ec777e8762969dce7e5c007b9312b9d5b4017657331b7253067b3665bd470f82`.
  The replay reported the three standard Lean axioms. The updated shared
  launcher also replayed the primary export after the standard-theory
  split, compiling the closed bridge against the original ordered
  PA194 providers. It reported the same axioms.
- **Separate PA1944L pilot.** [`PA1944LFinal.consistency_iff_literal_nonhalt`](../../Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa1944l/PA1944LFinal.lean)
  proves `standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA1944LData.table 194`.
  The table hash is
  `c5787c6f2350e77183ca0d3ff25d2733ba87e8bb52cd54092d7fa26fcf4d5253`.
  Use the [variant replay](../../Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa1944l/README.md)
  for its Lean inputs and coverage check. The
  [Concise export](../../Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa1944l/PA1944LConcise.lean)
  passed over the independently recompiled native variant endpoint. Its
  checked source and object receipt records the original table hash and
  the selected Foundation theory and bridge provider. The export's
  axioms were `propext`, `Classical.choice`, and `Quot.sound`. The
  [PA inventory](../../Computability/BusyBeaver/Research/PA/README.md) links
  its other independently checked variants.
  The [shared arithmetic replay](../../Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa1944l/README.md#replay-with-shared-arithmetic)
  traverses the literal theorem's proof values through bounded equality
  decidability and `IPRASubSuccSelfNonzero.native` to
  `LeanProofs.IPRA.not_succ_le_self`. It verifies the original table hash
  and checks both endpoint judgments with the same three Lean axioms.
  The native and Concise objects had SHA-256
  `3213f3a5b57fed8392e1d0050f811fa9a73459d1a80c2ef1ea442b1a2970f664` and
  `6504cd585235a08dbc3e92854a34cbceaf7ee899e34f752e9615ce5acdb055cf`.
  With the model and coverage stages already compiled, the replay took
  6 minutes 53 seconds, used 2,595 MiB peak resident memory, and wrote
  24 MiB of replay artifacts including the selected provider snapshot.
- **Original PA195.** The
  [emitter and scheduler proof](../../Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-controller-schedulers/README.md)
  gives `PA194EmitterSchedulerPA.consistency_iff_scheduler_nonhalt`, a
  Foundation proof of `nativePAConsistency 🡘 ∼haltSentenceE e k ct a`
  for arbitrary emitter, control and layout parameters. The original PA195
  command row chooses the bundled gate, `.push`, and the two false
  halting-test and layout flags. The [literal PA195 checks](../../Computability/BusyBeaver/Research/PA/verification/other-machines/pa195/ipra/README.md)
  bind the supplied table and retain explicit proof premises for the
  consistency endpoint. A verified link from the literal table to the
  command scheduler is a separate obligation.
- **PA196.** The [emitter and scheduler proof](../../Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-controller-schedulers/README.md)
  now includes the PA196 equality-vacuity gate. It proves the internal
  equivalence at `haltSentenceE { delta := true } .push false false`.
  [`PA196Endpoint.consistency_iff_nonhalting`](../../Computability/BusyBeaver/Research/PA/verification/other-machines/pa196-vs-u208/ipra/PA196Endpoint.lean)
  proves the biconditional for `PA196Bounded.haltSentence` from standard iPRA
  proofs of `Ref(PA) → Halt` and `Halt → ¬¬Ref(PA)`. Its second theorem
  accepts double negation in both conclusions. Reproduce with the
  [PA196 iPRA guide](../../Computability/BusyBeaver/Research/PA/verification/other-machines/pa196-vs-u208/ipra/README.md).
  The standalone logical assembly is buildable as
  `+BusyBeaver.PA196.IPRAAssembly` and takes the two formulas and proof
  premises as arguments. The literal PA196 equivalence remains conditional
  at this boundary.

The [Concise scheduler exports](../../Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-controller-schedulers/PA194EmitterSchedulerConcise.lean)
prove the translated biconditional in `Prf PRAAx []` both for arbitrary
parameters and for those two exact command schedulers. The named instances
carry no extra premises. The ordered staged Lean replay compiled
`PA194EmitterSchedulerPA` (SHA-256
`07fdb62cd57dec79c8e161f69ae3feae6ab659f7b453356c31f6bd41fd159c19`),
then rebuilt `IPRABridge.Standard` against the same Foundation provider before
compiling the export (SHA-256
`19e271ce708bd72abb9b8eb41d499005894b39b369932d79181d3b2162f1ee1a`).
All three export audits report `propext`, `Classical.choice`, and `Quot.sound`.
Use the [scheduler replay guide](../../Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-controller-schedulers/README.md#conciseipra-export)
to check this boundary.

## BusyBeaver ZFC and DiophantineConsistency

- **K215.** `KEndpoint215.blank_halts_iff_zfc_refutation` (Lean) and
  `tm215_halts_iff_ZFC_inconsistent` (Rocq) are closed external theorems
  about the blank start of the exact 215-state machine. The
  [verification record](../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md)
  records table binding, pinned replay closures, and axioms for both systems.
- **Rotation240.** [`BinaryConsistencyRotation240`](../Interpretability/ZFCinPA/Lean/ZFCinPA/BinaryConsistencyRotation240.lean)
  checks `iSigma2_proves_con_ZFC_iff_not_binary_halts` and
  `peano_proves_con_ZFC_iff_not_binary_halts` in the stated object theories,
  with separate ZF theorems. Use
  `lake build +ZFCinPA.BinaryConsistencyRotation240` on the matching closure
  and follow the
  [ZFC project index](../../Computability/BusyBeaver/Research/ZFC/README.md)
  for table and replay evidence.
- **C222 arithmetic evaluator.**
  [`ArithmeticHistory222.step_defined`](../../Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticHistory222.lean)
  proves `𝚺₁-Function₂[V] stepValue via stepDef` for an arbitrary model `V`
  of `IΣ₁`. Its positive code row uses the
  [IOpen interpretation](../../Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticPredecessorWitness.lean)
  of `Prf.guardedWitness`, the same inference used by the ordinary iPRA
  `LeanProofs.IPRA.predecessor_witness`. In the IOpen interpretation the row
  states `x ≤ code ∧ code = x + 1` and the body is any `Q : V → Prop`.
  The resulting guard is `code ≠ 0` and the witness is `code − 1`.
  The exact `stepDef` formula and `IΣ₁ ⊢ totalitySentence` stay in the
  evaluator's original theory. Check the source with the root Lake
  environment using `lake build +BusyBeaver.ZFC.ArithmeticHistory222`.
  The focused source replay checked both declarations with `propext`,
  `Classical.choice`, and `Quot.sound`.
  The historical `ArithmeticRow254` witness statement continues to serve
  its existing callers. That file is bound by source-hash receipts for
  ZFCinPA and K215 stages. The focused C222 replay used the migrated
  evaluator source with SHA-256
  `eab9a10f9cda777f5db0b207c9df60a4491198018bd878f7f2e1bac6b8df9f5e`.
- **Explicit nine-variable equation.**
  [`IPRAExplicitZFCFinal.standard_equivalence`](../../Computability/DiophantineConsistency/Lean/DiophantineConsistency/IPRAExplicitZFCFinal.lean)
  proves `standardTheory ⊢ nativeNoZero ExplicitZFCSyntax.expression 🡘
  ∼mappedNativeRefutation embedding` with no additional premises.
  `ExplicitZFC.expression_eq_syntax` identifies the expression with the
  [published recipe](../../Computability/DiophantineConsistency/EXPLICIT_EQUATION.md).
  The [equation proof record](../../Computability/DiophantineConsistency/README.md)
  documents the historical provider replay and the exact model obligations.
  The focused Lake target is
  `+DiophantineConsistency.IPRAExplicitZFCFinal`.
- **Nine-variable maintained-equation reduction.**
  [`IPRANineCurrent.standard_equivalence`](../../Computability/DiophantineConsistency/Lean/DiophantineConsistency/IPRANineCurrent.lean)
  uses the same mapped refutation formula with `nativeNoZero expression`
  where `expression` is this module's Jones reduction of the quartic gates
  for the natural split of `ObjectCurrentEquation2011.naturalExpression`.
  Its audit target is
  `+DiophantineConsistency.IPRANineChecks`. The
  [local proof plan](../../Computability/DiophantineConsistency/IPRA_PROVABILITY_PLAN.md)
  records the separate maintained 14-variable formula and replay checks.

The [Concise ZFC exports](Bridge/Lean/IPRABridge/Checks/ZFCEquations.lean)
prove `Fm.iff explicitNoZero consistency` and
`Fm.iff currentNoZero consistency` in `Prf PRAAx []`. Each no-zero
formula translates its own equation, and each consistency formula
translates `∼mappedNativeRefutation PRALanguage.embedding`. Both passed
against the ordered historical providers of the
[104-stage replay](../../Computability/DiophantineConsistency/reviews/nine-variable-ipra-complete-author-ledger/README.md).
The two native endpoint sources matched the current endpoint files
byte-for-byte in that replay. The import objects had SHA-256
`187060bd35f1ee3c0afc66c53d1079652e3f3de3e9db9218536f3640810425ce`
and `552fef65bae85ee3bfe8aabbf0f92cbfe8e2dc4d170e957770eabab8e47f9069`,
respectively. The new export object had SHA-256
`5c3e8d6b9f54b0d82a308f341c17e6d639779a13da76197d1fbd911f38c67341`.
The exported proofs use `propext`, `Classical.choice`, and `Quot.sound`.
The root-source replay command is
`lake build +IPRABridge.Checks.ZFCEquations`.

A separate initial root Lake run of `+DiophantineConsistency.IPRAExplicitZFCFinal`
completed all 2,746 jobs and matched the expected axiom audit. With the
previously compiled general dependencies, it took 48 minutes 9 seconds
and peaked at about 11.0 GiB of resident memory. This is the initial ZFC
endpoint baseline. The root replay of the new exports also checks their
dependencies after the arithmetic migration. It completed all 3,347 jobs in
26 minutes 1 second using 2,782 MiB peak resident memory, reusing the
previously built independent branches. Both exports reported the same three
Lean axioms. The exact root export object had SHA-256
`c8933a20f5eafa14f1b39ffc20a3614200ef8020bb46670fcd073eeaed3bd6a8`.

The explicit equation's compiled proof values reach
`IPRABoundedRhoZFC.zfcEquiv` through `IPRAExpressionNative.comparison_of_pra`.
The reduction's backward bounded induction reaches native equality
decidability, `IPRASubSuccSelfNonzero.native` and the shared ordinary
`LeanProofs.IPRA.not_succ_le_self`. This is the same arithmetic comparison
used by the independently replayed literal PA1944L proof.

## Adjacent providers

The [MRDP proof guide](../../Computability/HilbertTenthProblem/Lean/MRDP.md)
covers `Diophantine.mrdp` and `mrdp_iff` over standard natural numbers.
Use `lake build Diophantine` and the published `MRDPAxioms.lean` audit.
The focused `lake env lean -j1` run of that audit passed all 18 axiom
checks and the three explicit interface checks.
The [Pell slack row](../../Computability/DiophantineConsistency/Lean/DiophantineConsistency/IPRAPellSlack.lean)
is the first object-theory client. It uses `Sys90.E10b` with
`k = η + ζ` and a positive natural witness `ζ`, and proves both
directions of the strict bound, using `k ∸ η` for the forward witness.
The exact source ports also give the adjacent upper interval in ordinary
iPRA. Independently build `+Diophantine.Paper1980.System90` and
`+DiophantineConsistency.IPRAPellSlack`, then run
`lake env lean -j1 Computability/DiophantineConsistency/Lean/checks/IPRAPellSlack.lean`
to check the existing native consumer's interface. All three checks passed.

| Interface | Preserved boundary and focused check |
| --- | --- |
| [PA list coding](../PeanoArithmetic/ListCoding/Lean/PAListCoding/ExactTrace.lean) | For every `R : ℕ → ℕ → Prop` and `h x y : ℕ`, `exactIter_iff_exists_sequence` represents `ExactIter R h x y` by adjacent steps in a sequence, and `exactIter_iff_exists_betaTrace` represents it by `∃ code step, BetaTrace R code step h x y`. These are natural-number theorems used by [H10's trace adapter](../../Computability/HilbertTenthProblem/Lean/Diophantine/Common/DiophantineTrace.lean). Both passed source-current type and axiom checks with the Lake providers. |
| [ZFCinPA free renaming](../Interpretability/ZFCinPA/Lean/ZFCinPA/ModelCodedFreeRenamingAudit.lean) | Renaming, shift and substitution hold for arbitrary `IΣ₁` model elements and coded syntax, including nonstandard values. For example, `renameIndex_lift_succ` proves `renameIndex chosen (level + 1) offset (x + 1) = renameIndex chosen level offset x + 1`. The current-source `ModelCodedFreeRenamingAudit` passed all 15 axiom reports and the exact type probes. The [older hash-bound receipt](../Interpretability/ZFCinPA/results/model-coded-free-renaming-verification.json) refers to its pinned source and remains separate. |
| [Uniform bounded PA provability](../PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/UniformInternalProvabilityTheoremAudit.lean) | The audited declaration states `Peano ⊢ paUniformRestrictedConsistencyProvabilitySentence`. Its proof uses actual PA proof codes at arbitrary internal levels. Reproduce with `lake build +BoundedPAConsistency.UniformInternalProvabilityTheoremAudit`. The current focused probe lacked the endpoint object and 111 other local prerequisite objects. |
| [Bounded ZFC endpoint](../../SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Endpoint.lean) | For each external `n : Nat`, `zfc_proves_conZFC_unfolded` gives `BProv ZFCax_s [] (conZFCForm n)` in the sealed calculus. The current source check passed both ZFC theorem forms and the sentence seal. |

The three successful checks used the standard Lean axioms. The bounded ZFC
sentence seal used only `propext` and `Quot.sound`. The provider source and
object hashes for [BoundedDioph](../PeanoArithmetic/ListCoding/Lean/PAListCoding/BoundedDioph.lean),
the ZFC axiom truth file and the ZFCinPA free-renaming module matched their
Lake traces.

The nearest arithmetic use sites in the model-coded proofs are additive
cancellation in [`TermEvaluationTransport`](../PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/TermEvaluationTransport.lean)
and [`ModelCodedFreeRenaming`](../Interpretability/ZFCinPA/Lean/ZFCinPA/ModelCodedFreeRenaming.lean).
They already share Foundation's `AddCancelCommMonoid` instance derived
from PA⁻ ordered-ring semantics. The current `IΣ₁` inputs range over the
ambient model. An ordinary iPRA proof could be used at this interface with
a checked symbol and axiom interpretation over every such model. Retain
the existing shared model theorem at these call sites.

When adding a migration entry, record the original and translated types,
proof premises, exact table or expression identifier, provider order,
replay command, and the proof's axiom audit. A running or partial build
can be recorded with its completed stages and retained outputs. Record
elapsed time, peak memory and disk use when the measured replay completes.
