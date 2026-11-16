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

After extracting the new syntax providers, the normal root Lake build
of `IPRABridge` checked all 1,188 jobs. With its toolchain and general
dependencies already built, the run took 90.68 seconds and peaked at
1,739 MiB. The immediate `lake --no-build build IPRABridge` rerun found all
targets up to date in 1.26 seconds at 799 MiB peak resident memory. The
installed `IPRABridge` objects and companions used 7.0 MiB. The round trip,
open and scoped sequent, arithmetic, and PA196 assembly targets each
passed after the new sources were built. Their elapsed times ranged from
3.19 to 4.99 seconds.

The [zero-test comparison](Bridge/Lean/IPRABridge/ComparisonBits.lean)
proves the translated `isZeroCode` application equal to `eqb a zero` at
any `a : PTm n` in any finite context. The Foundation
[`notBitConvention`](../../Computability/DiophantineConsistency/Lean/DiophantineConsistency/IPRANotBit.lean)
retains its `extended nativeTheory` derivation for arbitrary PR code `c`
and term family `v`. The bounded-child proof reaches it through
`transferZeroCorrectness` and reaches the ordinary `eqb_of_ne` in the proof
value. The source replay compiled the comparison, the native corollary,
`IPRACharacteristicTransfer`, and `IPRABoundedChild`, with the standard
three Lean axioms. The opt-in
[comparison-bit audit](Bridge/Lean/IPRABridge/Checks/ComparisonBits.lean)
checks those exact judgments. Run `lake build +IPRABridge.Checks.ComparisonBits`.
The root build of this audit after the syntax and import changes completed
all 1,438 jobs in 5 minutes 32 seconds with 1,852 MiB peak resident memory.

The root `+ConciseIPRA.NativeBiInterpretation` target completed all 671 jobs.
Its exact `pra_iff_native` check audited both sides for arbitrary scope,
context and formula. The scalar reading applies `NFm.ofPRA` to every
hypothesis and the conclusion. The proof reports `propext`,
`Classical.choice`, and `Quot.sound`.

The root `IPRADerivations` build completed 1,678 jobs with the
finite-parameter search interface. After syncing with upstream arithmetic
sources, `+IPRADerivations.Checks.Axioms` completed 1,682 jobs at
`dedd94e853` in 11.42 seconds and peaked at 2,042 MiB. Its five new
finite-search reports use the standard Lean axioms.

The [Foundation bounded-search comparison](Bridge/Lean/IPRABridge/BoundedSearch.lean)
relates the original `searchCode good` to `Search.Finite.mu` at arbitrary
bound and parameter terms in any context. The migrated
[`selectorOpen`](../../Computability/DiophantineConsistency/Lean/DiophantineConsistency/IPRABoundedSelector.lean)
keeps exactly `extended nativeTheory ⊢! native (Rew.embSubsts v ▹ matrix good)`.
Its assumptions about a witness below the bound and the two conclusions
about the found witness stay in the original formula. A coherent staged
rebuild through `IPRABoundedRhoZFC` passed. The explicit ZFC endpoint's
proof values reach the ordinary `Search.search_found` through its
bounded-refutation comparison and this selector. The
[bounded-search audit](Bridge/Lean/IPRABridge/Checks/BoundedSearch.lean)
reported the standard Lean axioms and checked the zero bound, failed
search, arbitrary parameters and existing native consumer judgments.
The normal `lake build +IPRABridge.Checks.BoundedSearch` run completed
all 1,447 jobs.

| Representative arithmetic check | Rebuild elapsed and peak RSS | Warm check elapsed and peak RSS | Comparison and audit artifacts |
| --- | ---: | ---: | ---: |
| `IPRABridge.Checks.ComparisonBits` | 10.70 s, 1,783 MiB | 1.52 s, 803 MiB | 108 KiB |
| `IPRABridge.Checks.BoundedSearch` | 46.82 s, 1,863 MiB | 1.76 s, 805 MiB | 496 KiB |

These builds use the already compiled toolchain and package dependencies.
The warm timings use `lake --no-build build` on the same targets.

The [signum provider](Derivations/Lean/IPRADerivations/Core/Signum.lean)
keeps the nonzero test next to truncated subtraction. The original
`CubeRootTwo` signum declarations remain as aliases with their old types.
The direct caller replay checked the bounded-search bridge, Euclidean
arithmetic, and the modules using the earlier transitive imports. The
source gate verifies that search, Gcd, Bézout, and the bounded-search
bridge now share the core signum proof independently of `CubeRootTwo`.
The root `IPRADerivations` build and its named axiom audit passed after
the extraction. The integrated rebuild also passed `IPRABridge`, its
arithmetic audit, and the comparison-bit and bounded-search audits.

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
  The syntax extraction replay selected the same pinned native object
  and freshly compiled the bridge through import-only modules for the old
  declaration owners. The check passed with the same axiom set, and the
  export object had SHA-256
  `582b08696ee1cbe20754ea374bf8e228c5c15f57ff803f613aa072dedf802993`.
  A fresh stage run of `check-literal.sh` took 89.04 seconds at 2,563 MiB
  peak resident memory. `check-concise-export.sh` over that stage took
  7 minutes 22 seconds at 2,595 MiB. Both used the guide's ordered pinned
  prerequisites and checked the original literal table. Importing both
  outputs and printing types and axioms in a warm audit took 44.11 seconds
  at 2,581 MiB. The fresh replay outputs and their receipts used 6.9 MiB.
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
  After the syntax split, a second full replay used the source-current
  bridge and arithmetic overlay with the same pinned model and coverage
  providers. The checks passed, with both endpoint object hashes unchanged.
  A further replay after the subtraction cleanup checked the same hashes
  and proof dependency in 11 minutes 26 seconds at 2,597 MiB peak resident
  memory. The native `IPRASubSuccSelfNonzero` and its actual difference
  caller load without `PRASubSuccSelfNonzero.proved`. The old classical
  term names forward to [`SubSuccSelfNonzeroSyntax`](../../Computability/DiophantineConsistency/Lean/DiophantineConsistency/SubSuccSelfNonzeroSyntax.lean).
  The old exact native formula, the separate classical theorem, and the
  current native proof all passed the focused type and axiom checks.
  The [next pinned replay](../../Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa1944l/README.md#replay-with-shared-arithmetic)
  also follows a second proof path. The literal proof reaches the bounded
  existential comparison, then `selectorOpen`, `translatedSearch_found`
  and `Search.Finite.search_found`. The wrapper checked both proof paths,
  the original machine hash, the two endpoint judgments and their
  standard axiom sets. It took 3 minutes 46 seconds at 2,619 MiB peak
  resident memory. Both endpoint object hashes match the replay above.
  The replay with the shared signum and three native equality proofs
  checked five proof paths in the exact literal theorem. It took
  8 minutes 45 seconds at 2,615 MiB peak resident memory. The table check and
  both axiom audits passed, and both endpoint object hashes again matched.
  A separate proof-value check followed the bounded-search comparison to
  `Signum.sg_succ` in the portable provider.
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
  The [source inventory](DEPENDENCIES.md#pinned-and-experimental-providers)
  records the input comparison for the unification series and identifies
  the source closure of the current endpoint separately from those receipts.
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
  The focused C222 replay used the migrated
  evaluator source with SHA-256
  `eab9a10f9cda777f5db0b207c9df60a4491198018bd878f7f2e1bac6b8df9f5e`.
  A later root Lake build of the migrated endpoint completed 1,155 jobs
  in 26 seconds with 800 MiB peak resident memory, reusing compiled
  dependencies.
- **C254 predecessor forwarding.** The original qualified names
  `ArithmeticRow254.{pred_add_one,pred_le,predecessor_witness}` now use the
  shared [IOpen interpretation](../../Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticPredecessorWitness.lean).
  Their public signatures match byte-for-byte in Lean's audit output. Fresh
  isolated compilation checked the C254 and C222 history source and the
  permuted C222 proof-word evaluator, including its call through the old
  qualified name. The existing historical
  [validator](../Interpretability/ZFCinPA/validator_quantifier_core254.md)
  and [R2Gic](../Interpretability/ZFCinPA/r2gic.md) guards retain their
  frozen row input. Their replay guides name the original source and
  object hashes, source locations and currently missing historical
  providers. The literal K215 closure excludes this model arithmetic.
  The normal root builds `+BusyBeaver.ZFC.ArithmeticHistory254`,
  `+BusyBeaver.ZFC.ArithmeticHistory222Checks` and
  `+DiophantineConsistency.ArithmeticProofWordPerm222Checks` passed
  1,149, 1,156 and 1,174 jobs respectively.
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

The next normal root build ran after the syntax, zero-test and subtraction
changes. It completed 3,353 jobs in 9 minutes with 2,780 MiB peak resident
memory. Both equation proofs and both exports passed. The root export
object kept the SHA-256 shown above.

The normal root replay after the finite-selector and C254 changes completed
3,360 jobs in 21 minutes 40 seconds, with 11,262 MiB peak resident memory.
It rebuilt the permuted arithmetic proof-word and control dependencies as
part of checking both exact exports. The warm `lake --no-build build
+IPRABridge.Checks.ZFCEquations` completed in 39.54 seconds with 823 MiB
peak resident memory. The two native endpoint objects and the bridge
export, with their companions, used 208 KiB. The exact root export hash
again matches the receipt above.

### Maintained fourteen-variable endpoint

[`IPRAStandardCurrentEndpoint`](../../Computability/DiophantineConsistency/Lean/DiophantineConsistency/IPRAStandardCurrentEndpoint.lean)
has two closed results in `standardTheory`, each with no Lean proof
premises. `ipra_current_iff_consistency` proves `noZero14 🡘
∼mappedNativeRefutation PRALanguage.embedding`.
`ipra_current_iff_translated_consistency` uses the Gödel–Gentzen translation
of the embedded `FoundationZFCConsistencyNat.sourceSentence` as its right
side. The statement `noZero14` universally negates equality of the two
mapped sides of `ObjectCurrentEquation2011.naturalExpression` over the
fourteen natural variable slots.
[`IPRAReferenceCurrentEndpoint`](../../Computability/DiophantineConsistency/Lean/DiophantineConsistency/IPRAReferenceCurrentEndpoint.lean)
checks both results in the equality-only reference theory after erasing
the native order atoms to equations of their comparison codes.

The current four wrapper and audit sources replayed against the exact
November 4 project and package providers of the
[fresh standard rebuild](../../Computability/DiophantineConsistency/research/current14-standard-fresh-rebuild-preflight/README.md).
The reference replay also used 19 source-current reference objects and
one import-only module for the older finite-code owner. All four endpoint
results and three transfer audits report the standard Lean axioms. The
standard and reference audit objects had SHA-256
`a4f9dc7d187c3ba673c9a4bcf4a22d316a116a3fd193132fdf484eef3ceeabc3` and
`253dd9ed5c5bca4eb1cb39571ef74b8b81174fe430110fa05e5627e18f90a9c4`.
For a normal Lake build, use the two `CurrentEndpointChecks` targets in
the [verification routine](UNIFICATION-PLAN.md#verification-routine).
Both root targets subsequently completed 3,157 jobs after the finite search
and C254 migrations. All four endpoint theorems and the three transfer
reports again use the standard Lean axioms.
Both targets passed again after the signum and native equality migrations.
The standard audit took 10.29 seconds and the reference audit 7.13 seconds.
The same root replay rebuilt the two nine-variable exports in 3 minutes
0.32 seconds over 3,360 jobs, with 2,856,776 KiB peak resident memory.
The export object retained the SHA-256 of the preceding run.

## Adjacent providers

The [MRDP proof guide](../../Computability/HilbertTenthProblem/Lean/MRDP.md)
covers `Diophantine.mrdp` and `mrdp_iff` over standard natural numbers.
Use `lake build Diophantine` and the published `MRDPAxioms.lean` audit.
The focused `lake env lean -j1` run of that audit passed all 18 axiom
checks and the three explicit interface checks.
The [September 21 complete build receipt](../../Computability/HilbertTenthProblem/Lean/STATUS.md#validation--2026-09-21-concise-mrdp-proof-transplanted-into-the-article-library),
published at `f336c11954`, records 3,773 jobs. `Paper1974.TableBounds`
and its six local dependencies match that snapshot byte for byte, as do
the twelve PAListCoding modules in the current H10 closure. The current
umbrella and Pell ratio sources differ from the historical snapshot.
The root Lean toolchain and package manifest match the publication
snapshot byte for byte.
The fresh independent build is still at `Paper1974.TableBounds`.
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
| [C254 quantifier validator](../Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorQuantifierCore254.lean) | `all_relational` ranges over arbitrary `IΣ₁` models. It derives `CProv (wim h (wim (wal x p) (wal y q)))` from `CProv (wim h (wim (weq x y) (wim p q)))` and the four existing `Vac` assumptions on `x`, `y`, `h`, `p` and `q`. The audit over the current Lake objects passed 25 axiom probes and 18 typed clients. |
| [R2Gic model-coded proof](../Interpretability/ZFCinPA/Lean/ZFCinPA/R2Gic.lean) | `gic_bridge_core` ranges over the ambient `IΣ₁` and `IΣ₂` model. Its `CProv` conclusion uses `K : SF 2`, `OddEnv F`, the seven odd labels and the eight strict-order premises. The audit over the current Lake objects passed 15 axiom probes and 15 typed clients. |
| [Uniform bounded PA provability](../PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/UniformInternalProvabilityTheoremAudit.lean) | The audited declaration states `Peano ⊢ paUniformRestrictedConsistencyProvabilitySentence`. Its proof uses actual PA proof codes at arbitrary internal levels. The source-current `lake build +BoundedPAConsistency.UniformInternalProvabilityTheoremAudit` at `22d8f4dc8d` passed for this theorem, `paRestrictedConsistencyProofSelectorIn_compiled`, and `paRestrictedConsistencyProofSelectorInAllModels_compiled`. The run completed 1,332 jobs in 5m22s with a peak of 2,250,944 KiB. |
| [Bounded ZFC endpoint](../../SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Endpoint.lean) | For each external `n : Nat`, `zfc_proves_conZFC_unfolded` gives `BProv ZFCax_s [] (conZFCForm n)` in the sealed calculus. The current source check passed both ZFC theorem forms and the sentence seal. |

The successful checks used the standard Lean axioms. The C254 and R2Gic
checks used source and object hashes matching the current Lake traces,
including the forwarded C254 predecessor proof. The bounded ZFC
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

## Forwarding imports and shared proofs

| Existing entry point | Current callers and implementation | Compatibility and regression check |
| --- | --- | --- |
| Foundation finite codes, equality-only language, and open syntax | `IPRABridge.Syntax` and the arithmetic image modules import the small code and syntax providers directly. | The original `PRAFiniteFunctionCodes`, `PRATheory`, `IPRAEqualityOnlyReference`, and `IPRAQuantifierFree` imports still expose their declarations. The literal PA launcher checks compiled declaration ownership and supplies import-only modules for legacy providers. The bridge and both pinned literal replays check these paths. |
| Foundation `standardTheory` and native conversion | The bridge's standard transport uses the statement layer and the checked reference and native conversions. | The original `IPRAStandardTheory` import retains the theory and `provable_iff`. The source closure gate and the closed and open bridge checks cover the new import boundary. |
| `CubeRootTwo.{sg,sg_zero,sg_succ}` | The portable search, GCD and Bézout proofs now use `Core.Signum` directly. The retained algebra aliases also serve existing geometry, primality and Euclidean proofs. | The exact types of all 21 public algebra declarations matched the earlier object. The immediate affected geometry and arithmetic callers rebuilt. The source gate excludes `Algebra.CubeRootTwo` from the new portable search and Euclidean closures, and the bounded-search and PA1944L checks cover the shared proof. |
| `IPRASubSuccSelfNonzero.native` | The difference proofs, the PA1944L comparison, and the ZFC reduction reach `not_succ_le_self`. | The original classical term names forward to the common syntax provider. The exact native formula and classical theorem were checked together. The closure gate excludes `PRASubSuccSelfNonzero` from the native proof path, and the PA1944L proof-value check reaches the shared lemma. |
| `IPRAAddOneTransfer.transfer`, `IPRASubPredZeroNative.native`, and `IPRASubSuccZeroNative.native` | Zero decidability, the reconstruction bridge, and the successor-difference step use `succ_eq_add_one`, `monus_succ`, and the ordinary order derivations. | The replacement replay verified the exact public declarations, seven current caller modules, and the explicit ZFC proof paths. The original classical add-one theorem and the subtraction Gödel–Gentzen interfaces retain their own audits. The immutable historical bounded-induction checkout also matches all three earlier proof sources. |
| `IPRANotBit.notBitConvention` | `IPRACharacteristicTransfer.transferZeroCorrectness` and the bounded-child stability proof use the checked equality-bit comparison. | `IPRANotBitChecks` still checks both the native result and `PRANotBit.PRA_proves_sentence`. The closure gate checks the native proof's independence from `PRANotBit`. The [historical bounded-induction replay](../../Computability/DiophantineConsistency/reviews/ipra-bounded-induction-postmerge-replay/README.md) identifies the immutable checkout for that proof family. |
| `IPRABoundedSelector.selectorOpen` | The bounded-refutation clients for the ZFC equation and PA1944L use `Search.Finite.search_found` through the exact code comparison. | The existing Foundation search code and native statement both retain their original names. `IPRABoundedSelectorChecks` still audits the classical theorem. The bounded-search audit and PA1944L proof-value check cover the new derivation. The same historical bounded-induction checkout preserves the earlier selector proof. |
| `ArithmeticRow254.{pred_add_one,pred_le,predecessor_witness}` | The C222 and C254 evaluators and the permuted proof-word history share the IOpen interpretation. | The old qualified statements forward with their original model assumptions. The active evaluator builds and proof-word check passed. The validator and R2Gic historical receipts refer to their frozen row source and object. |

The control-step caller `ArithmeticControlStep254.live_decode` also uses
`ArithmeticRow254.pred_add_one`. The root build of
`+BusyBeaver.ZFC.ArithmeticControlStep254` passed 1,215 jobs in 40m50s with
5,762,904 KiB peak memory. The archived audit also passed its 27 axiom
probes and 30 typed callers against the fresh objects, with hashes checked
against the current Lake inputs and outputs. The
[maintained control-step audit](../../Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticControlStep254Checks.lean),
run with `lake build +BusyBeaver.ZFC.ArithmeticControlStep254Checks`,
follows the proof values to `ArithmeticPredecessorWitness.pred_add_one`.
It checks the nonzero-state hypothesis, the `Σ₁` and `Δ₁` step graphs, and
unique existence of the output for arbitrary `IOpen` models.

When adding a migration entry, record the original and translated types,
proof premises, exact table or expression identifier, provider order,
replay command, and the proof's axiom audit. A running or partial build
can be recorded with its completed stages and retained outputs. Record
elapsed time, peak memory and disk use when the measured replay completes.
