# Fixed Foundation ZFC consistency sentence — standard-Nat author receipt

Status: **PASS**, 2026-10-26. This is a concrete, unconditional standard-model
comparison. It is not an HA proof comparing the fixed GG sentence to an
untranslated proof checker, nor an arithmetic theorem about the current
machine or equation.

## Frozen pair

| File | Lines | SHA256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/FoundationZFCConsistencyNat.lean` | 86 | `c9e90e5861848ece065a410ad2b0012617e481b9d4fbfccd37436b2ebf40b613` |
| `Lean/DiophantineConsistency/FoundationZFCConsistencyNatChecks.lean` | 49 | `5f80a6e149770fc7eb8920199a5ee76cf609512a09743be6db83164ad2b6bbb3` |

The author read the entire pair and driver before execution, and checked the
actual source theorem/validator/axiom definitions. Root read the original
86/49 source before author compilation. The only subsequent source change
corrected the namespace of the actual conventional ZFC axiom predicate; all
formulas and proof steps remained otherwise identical.

## Actual sentence and theorem chain

`sourceSentence` is exactly Foundation's
`(LO.FirstOrder.SetTheory.ZermeloFraenkelChoice : LO.FirstOrder.SetTheory).consistent`.
`ggConsistency` is its existing Gödel–Gentzen translation followed by the
existing `FoundationPAHFSyntax.sentence` map. No consistency predicate is
supplied as a parameter or substituted for that fixed source theory.

The final theorem, for every valuation `ee : ℕ → ℕ`, is

```lean
Formula.Sat FoundationPAHFNatSemantics.natStructure ee ggConsistency ↔
  ¬ SetTheory.BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] SetTheory.Form.fBot
```

The right side is the same syntactic consistency proposition used by the
existing `DiophantineConsistency.ConZFC` definition. The new pair does not
import the broad `Bridge` module or identify the different syntax types.
The `ggConsistency_environment` corollary records valuation independence.

The proof composes these actual, fixed results:

1. `ValidatorConsistencyEquivalence.peano_proves_con_ZFC_iff_validator`,
   standard-Nat PA modelhood, and `Theory.Proof.sound`, to interpret the
   Foundation consistency sentence as absence of `ArithmeticHistory254.value
   code = 2`.
2. The actual `ArithmeticHistory254.check_defined` and
   `c254_iff_represented`, at conclusion one (`Code254.F`), to identify that
   all-code acceptance existential with `Code254.C254 Code254.F`. The value
   two is exactly the checker's successor tag of falsity code one.
3. `WFTheory.c254_refutation_iff_zf` and
   `ConstructibleChoice.zf_refutation_iff_zfc_refutation`, to reach the literal
   conventional `BProv` axiom set, including Choice.
4. The accepted `FoundationPAHFNatSemantics.sat_sentence_GG`, to interpret the
   actual translated PAHF sentence in standard naturals.

These are metatheoretic semantic and finite-refutation comparisons. The
upstream PA source theorem uses classical arithmetic completeness; the ZF/ZFC
refutation comparison uses the established constructible-model transport.
Neither is mislabeled a constructive HA derivation here. C254 is used only to
compare the two fixed consistency conventions, not as a replacement for the
215-state runtime or the actual C222 enumerator.

## Fresh execution and dependency scope

Both final fresh compiles passed: main 2.10s, checks
1.95s. The main log is empty. All eight requested
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
No new axiom, `sorry`, or `native_decide` appears in the final sources. Peak
child-process RSS reported across the pair was 2240044 KiB.

The two new objects are:

- Main: `8167f7850fc2c2cfe900d7a9140f4038961c111b152a61c8dd672fd3cf947530`.
- Checks: `4ef3094c5c5203e2bbe4f6dfa186a790224821d6730591ca6dacfce5e34db294`.

Execution started only after root announced terminal PASS for the scoped
73-module legacy refresh. The private author overlay
`/tmp/fixed-zfc-nat-author-taun_kqd/lib` reuses exactly 410 prerequisites: root's 73 newly checked
local objects plus 337 accepted cached objects, including the generic Nat
semantics leaf. The inventory includes 139 Foundation modules and 51 explicit
external names. All 827 reused artifact hashes and all selected current source
hashes were checked; 1762 deduplicated files were pinned before and after each
new compilation. The driver independently checks current import headers,
requires source identity for every root-fresh pair, and rejects a reused client
that imports a root-fresh dependency. It builds no prerequisite or Foundation
module and does not write into root's 73-module overlay.

Root accepted plan SHA256:
`749ec00cb495521f77f8f929dff99673c6bd3cfd458be64ac7a2cf307cdc715e`; terminal state SHA256:
`21985211e7d0e7ffaf41d87332f8f4a082c727e45d11d74ad2a74c7f233d0943`. Those files and the exact root driver were copied
into each author attempt bundle. Root's earlier warning-policy stop followed
nineteen successful compilations; its preserved historical plan/state and
continuation are reported by root's refresh packet. This author does not claim
to have independently rebuilt those 73 modules or all external packages.

The compiler is Lean 4.32.0, SHA256
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. Commands use actual source filenames and
`-M6000 -j1 -DElab.async=false`, explicit private LEAN_PATH, and a 512 MiB free
disk guard. Each attempt uses a new private overlay; new output files are
absent and nonsymlink paths. No accepted source/cache/Git state was changed.

Durable summary: `reviews/foundation-zfc-consistency-nat-replay.json`, SHA256
`7581f389d7dc97d95257c514617dd550454bfb3dd6c43746b22d5ca9787d901a`. Full bundle: `reviews/foundation-zfc-consistency-nat-replay/`.
Final RESULT SHA256 `fc587b2679ba27a18c979347431daa1902599ae7728acf54d33988560417aad1`; inputs SHA256 `743ff1efd8748329ba828193f8c172b1f93bd4527e55cec75aede50c911478b6`.

## Preserved first failure

Attempt `1793060717002629572` was a 2.05s failed main compile because the initial
explicit predicate name was `_root_.SetTheory.ZFCax_s`. Its real owner is
`LeanProofs.BoundedZFCConsistency`, as confirmed in
`SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Choice.lean:188` and by
the existing refutation theorem's type. Only this qualification was corrected
in main/checks. Lean's downstream recovery warning about `sorry` belongs to
that failed run; there was no written source `sorry`, and the final reports
contain no `sorryAx`. The failure's source/log/record are retained; the original
checks are saved with their original hash and explicitly marked unexecuted.

Authorship: circuit_reduction authored the new pair and previously authored
the generic Nat semantics/syntax adapters. Root executed and accepted the
73-module prerequisite refresh. The existing C254/calibration and constructible
proofs are reused, not newly proved by this leaf.
