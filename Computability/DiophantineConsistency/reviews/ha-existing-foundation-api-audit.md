# Existing intuitionistic translation and arithmetic-machine APIs

Read-only audit by `circuit_reduction`, 2026-10-26. The user now asks for a Lean proof that an HA proof of the desired equivalence exists; no serialized HA derivation is required. This audit does not establish that equivalence.

## Findings

The existing Foundation library already proves the logical Gödel–Gentzen translation in Lean. It should be reused instead of reimplementing the logical algorithm. The inspected sources do not yet provide a conventional HA arithmetic theory or the arithmetic axiom translation from PA into HA. A separate, freshly checked HA proof relation is now available in this repository's `HAProofs.lean`.

There is an existing **object-level PA consistency equivalence for the exact Rotation240 machine**. The maintained equation instead uses the exact K215 machine, through the checked 715-digit decoder and its explicit state conjugacy. The K215 documentation expressly distinguishes its external Lean equivalence from an internal PA endpoint. Neither substituting the 240-state theorem nor interpreting external Lean quantifiers as internal arithmetic quantifiers is justified.

## Primary source and build scope

Foundation was inspected at `/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation`, git commit `32e1a0956a8622fad067328ca1959729a7634428`. This is the checkout referenced by the repository's ZFC-in-PA research. It is **not** a current worktree Lake dependency. Its `lean-toolchain` says v4.31.0; the active project uses v4.32.0. No Foundation object was loaded, copied, rebuilt or accepted in this audit. Existing compilation claims in historical research documents were read as provenance, not repeated as fresh checks.

I read the entire 199-line Foundation `FirstOrder/NegationTranslation/GoedelGentzen.lean`, the full relevant intuitionistic deduction source, classical proof constructors and theory-proof representation, the arithmetic axiom/schema definitions, and all three repository consistency-composition modules listed below. The search for existing HA theory/PA-to-HA adapters covered Foundation's Lean sources and `Logic/Interpretability/ZFCinPA/Lean`; no arithmetic HA definition or use of `Theory.ToTheoryᵢ` outside its defining file was found. This is a scoped search result, not a claim about every possible external library.

## Existing logic APIs

Paths in this section are relative to the pinned Foundation checkout.

| Source anchor | Actual interface |
|---|---|
| `FirstOrder/Intuitionistic/Deduction.lean:60` | `HilbertProofᵢ`: intuitionistic first-order Hilbert proof trees; `Hilbertᵢ.Intuitionistic` supplies ex falso, while excluded middle belongs to a separately named classical system. |
| `FirstOrder/Intuitionistic/Deduction.lean:177` | `dneOfNegative`, and `DN_of_isNegative`: double-negation elimination only for the syntactically negative fragment. |
| `FirstOrder/Intuitionistic/Deduction.lean:275` | `Theoryᵢ` holds a set of intuitionistic sentences. |
| `FirstOrder/Intuitionistic/Deduction.lean:306` | `Theoryᵢ.Proof` is actual context derivability from embedded axioms; it has axiom, weakening and deduction adapters. |
| `FirstOrder/NegationTranslation/GoedelGentzen.lean:11` | `Semiformula.doubleNegation` maps classical NNF formulas to intuitionistic formulas. |
| Same file, lines 41, 54, 57, 60 | Negative-fragment membership and exact rewriting, substitution and embedding compatibility. |
| Same file, line 85 | `Theory.ToTheoryᵢ T Λ` takes the image of the axioms under negative translation. This definition alone is not a proof-translation theorem. |
| Same file, line 155 | `Derivation.gödelGentzen` recursively translates an actual classical LK derivation into intuitionistic finite-context contradiction. |
| Same file, line 194 | `Provable.gödel_gentzen : 𝐋𝐊¹ ⊢ φ → Λ ⊢ φᴺ`. This is pure logical theoremhood, not a PA/HA theorem with arithmetic axioms. |
| `FirstOrder/Basic/Calculus.lean:300` | `Theory.Proof` stores an explicit finite list of theory axioms and an LK derivation. `Theory.Proof.provable_iff` at line 335 exposes that list. |

The final GG wrapper uses classical Lean infrastructure to obtain its metatheoretic proof wrapper. That does not add excluded middle to the target proof calculus. Conversely, a standard-only Lean axiom report does not itself certify an HA derivation: the target must actually be a theorem of the intuitionistic proof relation.

The smallest useful missing generic adapter appears to be:

```lean
-- Proposed interface; not implemented or claimed as a theorem here.
theorem theory_godelGentzen {T : Theory L} {φ : Sentence L} :
    T ⊢ φ → T.ToTheoryᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ L) ⊢ φᴺ
```

Its proof can use the finite axiom list already stored by `Theory.Proof`, the existing `Derivation.gödelGentzen`, `emb_doubleNegation`, negative stability, and `Theoryᵢ` context rules. This avoids duplicating GG. A small adapter is plausible, but its compiler/environment preparation and proof have not been attempted.

Arithmetic remains a separate obligation. Foundation `Arithmetic/Schemata.lean:53` defines PA as ordered-ring-language `PeanoMinus` plus universal closures of all `succInd` instances. `Arithmetic/PeanoMinus/Basic.lean:15–55` lists equality and seventeen arithmetic/order axioms, including trichotomy. This is not definitionally the same syntax or axiom predicate as `PAHF.PASyntax` or the new `HA.Proves`. A conventional HA theorem must establish an interpretation of equality, order, these base axioms and arbitrary induction, rather than simply name the translated-axiom image “HA.” One may either construct that Foundation arithmetic adapter or prove an explicit syntax/proof bridge to `HAProofs`.

The Coq port also retains an actual GG proof at `Logic/FoundationPort/Coq/FirstOrder/NegationTranslation/GoedelGentzen.v` (`ifo_goedel_gentzen`, `ifo_goedel_gentzen_provable`). Since the Lean primary theorem exists, porting this Coq foundation is unnecessary for the logical step.

## Existing internal arithmetic calibration

The following are actual statements in `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/`:

1. `ValidatorConsistencyEquivalence.lean`, `peano_proves_con_ZFC_iff_validator`: PA proves that the represented consistency of Foundation ZFC is equivalent to no internal code having `ArithmeticHistory254.value = 2`. Its model-wise proof is quantified over arbitrary models of IΣ₂, using the internal R2/LSchema chain; it is not restricted to standard proof codes.
2. `RotationInterpreterConsistency240.lean`, `peano_proves_con_ZFC_iff_not_rotation_halts`: PA proves the corresponding nonhalting statement for the literal represented Rotation240 control interpreter and explicit nested-pair seed.
3. `BinaryConsistencyRotation240.lean`, `peano_proves_con_ZFC_iff_not_binary_halts`: PA proves the equivalence for `ArithmeticMachineRunRotation240.haltingSentence.val`. The source identifies the actual table and seed and composes `ArithmeticBlankControlRotation240` at arbitrary internal times.

`Computability/BusyBeaver/Research/ZFC/pa_internalization.md:5–31` records this endpoint and its layered validation history. `Computability/BusyBeaver/Research/ZFC/candidate-k215/README.md:9–13` explicitly says its external formal theorems do **not** give an internal PA endpoint. The exact current external theorem is `KEndpoint215.blank_halts_iff_zfc_refutation`, comparing ordinary Lean `BlankHalts machine215` with `SetTheory.BProv ZFCax_s [] Form.fBot`.

The machine gap is therefore concrete: represent the actual215 run/validator simulation in arithmetic, or prove an internal simulation to an already calibrated represented machine/interpreter, with all finite tables and startup data bound. The source-only filename search found no `Arithmetic*215`/`215*Arithmetic` module. Existing all-standard-runtime correctness or a decidable finite action-table equality is not the missing arbitrary-internal-time theorem.

There is also a consistency-syntax gap to state explicitly: Foundation's arithmetic sentence `(𝗭𝗙𝗖 : SetTheory).consistent` and external `DiophantineConsistency.ConZFC` use different presentations. The intended final arithmetic refutation predicate must be fixed and its interpretation/comparison proved; notation alone does not identify them.

## Current equation and the HA target

`ObjectCurrentEquation2011.expression` already binds the literal 14-variable Carrier65 expression to the exact current four ports. Its `positiveShift` and `naturalExpression` implement positive witnesses by `v = x + 1`; splitting signed expressions into two natural expressions gives an equality over naturals. These finite expression identities are useful here. Its current `unsolvabilitySentence`, however, is a **set-theoretic `SetTheory.Form`**, not a PA arithmetic formula.

A new arithmetic expression compiler remains necessary. It should preserve the actual integer ports without unfolding enormous unary numerals. Binary/Horner arithmetic terms can use `2 * t + bit`, containing only one copy of the previously constructed term. Defining doubling as `t + t` in a tree representation risks exponential duplication. No such current-equation arithmetic compiler is asserted by this audit.

For the GG route, the final target's negative translation must be related inside HA to the intended no-witness/no-refutation equivalence. A negated existential with a concrete decidable arithmetic matrix is a promising stable target, but its represented matrix and the HA proof of the required stability/translation identity must be established. “Π₁” or “finitary” is not a substitute for that proof. Classical all-model completeness can supply an actual **PA** proof where its premises are proved for all arithmetic models; it cannot directly supply intuitionistic theoremhood.

The checked external current polynomial equivalence and the new direct witness-equivalence work are valuable guides, but neither is automatically an arithmetical derivation in PA or HA. The native tiling, carry/controller and Pell constructions still need their internal arithmetic binding; no model-standardness or desired-equivalence premise may replace it.

## Frozen local checkpoint and recommended order

`HAProofs.lean` and `HAProofsChecks.lean` are freshly checked in Lean v4.32.0. They define genuine intuitionistic first-order arithmetic proof existence over the existing PAHF syntax, conventional formula induction, and only a one-way erasure into the existing classical calculus. Their complete dependency/replay scope is in `ha-proofs-author.md` and `ha-proofs-dependency-replay.json`. This audit leaves that packet unchanged and does not start a second GG implementation.

Recommended independent steps are: (1) prepare a compatible, authenticated Foundation logical closure and prove the small theory GG adapter; (2) choose and prove the conventional HA arithmetic/syntax adapter, including induction and target stability; (3) bind the exact current equation and refutation predicate to arithmetic sentences; (4) supply the actual215 and native/Pell arithmetic equivalence. The existing240/validator internal results are reusable calibration, not a replacement for step (4).

The earlier incomplete internal-ZF integer-completion draft is isolated at `research/object-integer-completion-draft/`, explicitly unaccepted; it has no accepted Lean object. No further effort on that ZF-only draft is needed for this audit.

## Inspected source pins

| Source | SHA-256 |
|---|---|
| Foundation GG | `52fabd00a01e1f5671e1f078c36f9848f2e219e0a4e616deaad4e523057586ea` |
| Foundation intuitionistic deduction | `c657f4f2f1789c6731ef93db03585d72c095051c116b8ed4c3a563b73f68c41b` |
| Foundation classical calculus | `03ede19d7a450f4f9f8d6925406c6e6509768ebdea4179fa70418436d47fe08a` |
| Foundation arithmetic schemata | `5b1a1d84b71c3f943a0867c14d3b0c8c381062ec742d984fefdacf9f2209a6fd` |
| Foundation PeanoMinus | `856a38ddda30c1505f6d991e6033ef7c41ebc82418b503ab711dfe173dc72303` |
| ValidatorConsistencyEquivalence | `e0502e78a7c1a4a8c6d3f242279ae557ce91678dfd9cb52aa628bf38c0fbd242` |
| RotationInterpreterConsistency240 | `a07acc1fc3b84aa55281f9fa590246b365353867157e54c5a027436d19e777b1` |
| BinaryConsistencyRotation240 | `e045e91d01a61857bee0852fa50c16399ca89130c05c6b5be2e2ca15750d08fa` |
| candidate-k215 README | `b1383a9a77353539c0b8873a38fb2d7511c0c3f999445930eb2462709068176d` |
