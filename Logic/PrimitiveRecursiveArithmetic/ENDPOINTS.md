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
  The replay reported the three standard Lean axioms.
- **Separate PA1944L pilot.** [`PA1944LFinal.consistency_iff_literal_nonhalt`](../../Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa1944l/PA1944LFinal.lean)
  proves `standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA1944LData.table 194`.
  The table hash is
  `c5787c6f2350e77183ca0d3ff25d2733ba87e8bb52cd54092d7fa26fcf4d5253`.
  Use the [variant replay](../../Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa1944l/README.md)
  for its Lean inputs and coverage check. The
  [PA inventory](../../Computability/BusyBeaver/Research/PA/README.md) links
  its other independently checked variants.
- **Original PA195.** The
  [emitter and scheduler proof](../../Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-controller-schedulers/README.md)
  gives `PA194EmitterSchedulerPA.consistency_iff_scheduler_nonhalt`, a
  Foundation proof of `nativePAConsistency 🡘 ∼haltSentenceE e k ct a`
  for arbitrary emitter, control and layout parameters. The original PA195
  command row chooses the bundled gate, `.push`, and the two false
  layout flags. The [literal PA195 checks](../../Computability/BusyBeaver/Research/PA/verification/other-machines/pa195/ipra/README.md)
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

## Adjacent providers

The [MRDP proof guide](../../Computability/HilbertTenthProblem/Lean/MRDP.md)
covers `Diophantine.mrdp` and `mrdp_iff` over standard natural numbers.
Use `lake build Diophantine` and the published `MRDPAxioms.lean` audit.
The [PA list-coding project](../PeanoArithmetic/ListCoding/README.md) provides
the `ExactTrace` interface for this closure. The
[ZFCinPA project](../Interpretability/ZFCinPA/README.md) and
[bounded consistency projects](../PeanoArithmetic/BoundedConsistency/README.md)
provide their declared proof codings and theory judgments. New object
translations at those boundaries should have their own inventory entries.

When adding a migration entry, record the original and translated types,
proof premises, exact table or expression identifier, provider order,
replay command, and the proof's axiom audit. A running or partial build
can be recorded with its completed stages and retained outputs. Record
elapsed time, peak memory and disk use when the measured replay completes.
