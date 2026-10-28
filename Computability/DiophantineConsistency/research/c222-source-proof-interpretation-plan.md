# Actual C222 source-proof interpretation: remaining kernel and axiom obligations

Source-only audit by `circuit_reduction`, 26 October 2026. The companion
`c222-source-proof-interpretation-plan.json` pins the inspected sources and
records the snapshot. No Lean compilation, object-cache reuse, proof-source
edit, or Git mutation was performed for this audit. Proposed declarations
below are not existing theorems.

The next small implementation should be an **internal sequent-context
calculus for the actual C222 predicate**. This is followed by source NNF
negation compatibility and the ten-case internal derivation induction. Those
steps do not, by themselves, discharge the source set-theory axiom images.
In particular, the old C254 CP/GIC interpretation cannot be renamed to C222.

## 1. Exact current objects

The actual module is `ZFCinPA.ValidatorProvability222`, not
`ArithmeticProvability222`. In every model of IΣ₁ it defines

```lean
CProv (conclusion : V) :=
  ∃ code : V, ArithmeticHistory222.value code = conclusion + 1
```

Its fixed `cProvDef` is Σ₁. Its MP, GEN, rho1–rho6, growG, rho8, and guarded
bundle closures contain witnesses for that actual history checker. Row 7 is
growG, not an assumed primitive-equality-vacuity rule. `cProv_classical`
already supplies the finite classical propositional calculus internally.
This is classical logic of the interpreted set calculus; it does not add a
classical rule to the separate HA proof system.

`ValidatorFormulaEncoder222.encode F B s p` is the represented encoder for
arbitrary internal source formula codes. Equality atoms are `Eind`, membership
atoms are `wel`, truth is 0, falsity is 1, and the binder stream advances by 2.
The shared modules ending in `Labels254`/`FormulaEncoder254` supply syntax
recursion and term environments only in this dependency path; their names
do not identify the new CProv predicate with C254.

Already available, with actual C222 conclusions:

| Resource | Exact source/API | Use |
|---|---|---|
| Substitution/opening | `ValidatorEnvironmentSubstitution222.encode_subst`, `encode_substs1`, `encode_free` | Arbitrary internal typed terms and nested binders; no new substitution compiler needed. |
| Free shift | `ValidatorFormulaEncoder222.encode_shift` | Tails the free environment, preserving bound stack and stream. |
| Atomic equality | `ValidatorAtomicTransport222.eind_refl`, `eind_symm`, `eind_trans`, `eind_congr`, `rel_congr` | Equality images use Eind, without an Eind→weq converse. |
| Freshness/alpha | `ValidatorEnvironmentVacuity222.encode_formula_vac`; `ValidatorEnvironmentStreams222.encode_formula_relabel` | IΣ₂ uniform proof witnesses with explicit original stream safety. |
| Universal rule | `ValidatorQuantifierRules222.all_opened_equiv`, `all_rule_under`, `fresh_resources` | GEN under a hypothesis requires its proved vacuity. |
| Existential term rule | `ValidatorExistentialRules222.ex_term_imp`, `ex_term_rule_under` | Already handles arbitrary internally typed source terms, including zero/repeated/fallback labels. |
| Finite seed deductions | `ValidatorSeedWitness222`, `ValidatorSeedClosure222`, `ValidatorSeedImage222` | Actual gates, empty object, Eind-singletons, and subset-indexed request; scope discussed below. |

`ValidatorEindContext222.eindContext B B'` is a conjunction of corresponding
bound-label Eind equalities. It is **not** the implication-chain context of
an internally sized source sequent. Similarly, the Lean `List V` used by
finite `Kalmar.Der` certificates is not a substitute for a vector of length
`n : V` in a nonstandard arithmetic model.

## 2. Precise logical target and induction strength

Foundation's `FirstOrder.Bootstrapping.Syntax.Proof.Basic` defines internal
`Derivation T d` by its actual Δ₁ finite fixed point,
`Proof T d p := DerivationOf T d {p}`, and
`Provable T p := ∃ d, Proof T d p`. The relevant case theorem is
`Derivation.case_iff`, lines 534–547 of the pinned source.

A proposed generic target, using fresh NEW C222 definitions, is:

```lean
AxOK222 T V := ∀ p : V, IsFormula ℒₛₑₜ p → p ∈ T.Δ₁Class →
  ∀ F s : V, StreamFree s F → CProv (encode F 0 s p)

Inv222 T d := Derivation T d → ∀ F s L : V,
  StreamFree s F → Enum222 L (fstIdx d) → CProv (seqC222 F s L)

translate222 (hAx : AxOK222 T V) : ∀ d : V, Inv222 T d
cProv_falsum_of_provable222 (hAx : AxOK222 T V)
  (h : Provable T (^⊥ : V)) : CProv (1 : V)
```

Here `seqC222 F s L` is the internal implication chain of the negated
encodings of the formulas in L, ending in 1. `Enum222 L A` says that the
internal vector L lists exactly the members of the internal finite set A.
Duplicates and arbitrary ordering are allowed.

The logical invariant is Π₂, not Π₁: CProv is Σ₁, all environment/list
parameters are internally quantified, and `StreamFree` is Π₁. The existing
Alpha222 proof explicitly handles this polarity by lifting the Π₁ freshness
premise to Σ₂ and the CProv consequent to Π₂. The same pattern gives an
IΣ₂ order induction for this kernel. `Derivation`, typing and enumeration
are Δ₁. Do not use induction over an arbitrary Lean predicate or replace
internal derivation codes by standard finite Lean proof trees.

The final source-theory interpretation is not yet justified at IΣ₂ merely
because this logical kernel is. Its additional represented schema and
interpretation invariants must each be classified; PA remains the intended
overall source theory.

The actual ten source cases are:

| Case | C222 proof step | Remaining local obligation |
|---|---|---|
| `axL` | Formula and source-NNF-negated formula yield contradiction | Uniform `encode_neg` compatibility. |
| truth | Encoding is 0 and `cProv_truth` | Internal context membership. |
| conjunction | Recover both conjuncts by classical contradiction in context | Context MP/deduction and existing finite conjunction certificate. |
| disjunction | One premise has both source alternatives | Context deduction plus the actual encoded disjunction. |
| universal | Premise contains `free p` and `setShift Γ` | Fold genuine vacuity over all encoded hypotheses, extend F by `eigen F s`, and use `all_opened_equiv`. |
| existential | Premise contains `substs1 t p` | Existing `ex_term_imp`; lift its implication through the internal context. |
| weakening | Inclusion of finite source sets | Context subsumption; covers exchange/contraction as well. |
| free shift | Source set is `setShift Γ` | `shiftList`, `encode_shift`, and preservation of StreamFree under `tail F`. |
| cut | Opposite source formulas in two premises | Context contradiction plus uniform `encode_neg`. |
| theory axiom | Actual `p ∈ T.Δ₁Class` | A proved image of this actual axiom; not an oracle inferred from typing. |

At the falsum endpoint choose F=0, s=2, and the singleton enumeration of
`^⊥`. Prove `StreamFree 2 0` with fallback1 explicitly. The resulting chain
is `(1→1)→1`, so one actual C222 self-implication discharges it.

## 3. Small implementation decomposition

1. **`ValidatorProofContext222` + focused checks**, recommended first leaf.
   Import the accepted `ValidatorFormulaEncoder222` (which already supplies
   RelationalCore/Eind and numeric vector recursion). Define fresh `imps`,
   `Der`, `negEnc`, `seqC`, `shiftList`, `Enum` in the new namespace, with
   fixed Σ₁ graphs and total constructions. Prove context theorem lifting,
   MP, hypothesis lookup, deduction/undeduction, subsumption, classical
   contradiction, encoded-list lookup/shift, and enumeration existence by
   the actual IΣ₁ vector inductions. Expected about 280–350 main lines;
   split graph/list and proof rules if necessary. Checks should retain
   empty context, duplicate hypotheses, internal index/length parameters,
   fallback1, and exact actual `ArithmeticHistory222.value` witnesses.
   No arithmetic history-to-command compilation belongs in this leaf.

2. **`ValidatorSourceNegation222`**: for arbitrary internal typed p and
   arbitrary F/B/s, prove both CProv implications between
   `encode F B s (Bootstrapping.neg ℒₛₑₜ p)` and
   `ValidatorRelationalCore222.neg (encode F B s p)`. Source negation is NNF
   duality, not definitionally the numeric implication-to-1. Eight source
   formula cases, Π₂ code induction, C222 finite propositional certificates,
   `all_mono` and negation duality suffice. No freshness hypothesis should
   be added to this theorem. The old 208-line R2Neg is a guide, not an import.

3. **`ValidatorSourceQuantifierContext222`**: fold
   `wal eigen (imps G g) → imps G (wal eigen g)` over the internal list
   `G=negEnc F s L`. Derive every hypothesis's vacuity from its actual source
   typing, `fresh_resources` and `encode_formula_vac`; do not accept a new
   blanket GEN-under-hypotheses rule. The finite fold uses Σ₁ induction
   once those witnesses are available. Lift the existing ALL/EXS rules.

4. **`ValidatorSourceDerivation222`**: import actual Foundation Proof.Basic
   and prove the displayed generic ten-case target with the exact Π₂
   invariant. It is a real internal proof transformation with an explicit
   modular axiom-image premise, not a closed ZF/C222 equivalence.

5. **`ValidatorSourceEquality222`**, a small independently useful axiom leaf:
   literal quoted images of Foundation equality reflexivity, symmetry,
   transitivity, relation congruence for equality and membership, plus raw
   irreflexivity. There are no function symbols in ℒₛₑₜ. Use the actual Eind
   certificates above and literal NNF encodings, then genuine repeated GEN.
   Primitive equality is used only in already-proved witness machinery;
   do not import old primitive-equality-vacuity or identify Eind with weq.
   The internal `Theory.Eq` membership split must be bound separately; the
   finite source relation set is exactly equality/membership of arity 2.

This splits reviewable proof engineering from the substantial set-theory
axiom problem. The first leaf needs no old R2 proof import. Foundation
Proof.Basic is needed only for the later derivation leaf, and its exact
object/dependency provenance must be authenticated before that build.

## 4. What is genuinely missing for Collection/Container

The old source theory is explicitly

```text
NativeSet.nativeTheory = EQ(set language) ∪ {containerAx, irAx} ∪ gicTheory.
```

Its CP axiom requires, for every a, a transitive container v containing a,
and for every x∈v a p∈v bounding **every raw subset** of x. Membership in
some container alone does not prove this.

Its GIC instance for an arbitrary internal two-variable matrix Q requires
an image container whose members have Q-preimages and which supplies a
Q-image of **every x∈a having any Q-image**. Its recognizer includes arbitrary
internal universal closure and arbitrary internal matrix codes, not just a
standard finite list of selected instances.

`ValidatorSeedImage222.matrix_image` instead proves an actual seed with
support, a request at the root, and coverage conditional on a **subset**
relation to a current collected member. Its binder is the self-labelled
matrix/container code. The module expressly does not assume `Vac k p`, raw
CP/GIC, or tagged comprehension. It cannot discharge the old `gic_body` or
`container_ax` targets by merely renaming the checker namespace.

The current external C222 lower proof follows a different source-bound path:

```text
KEndpoint.c222_of_zf_refutation
  KEind222.c222_complete                    (ordinary semantic completeness)
  KSeedDirect222.fullSeed_direct_of_derivable
  KLowerSeed.formSeed_of_fullSeed
  KLowerRaw: exact empty/singleton/pair, transitive sets, raw powers,
             augmented and tagged comprehension
  KLowerTag: tagged-domain separation and Collection
  KLowerEqv + KLowerQHyp.tag_qhyp
  KQ1ZF.zf_consistent                       (quotient/well-founded model route)
```

These are standard Lean structures, standard formula recursion and semantic
proofs. They are not `Provable T p` transformations on arbitrary internal
codes. In particular `KLowerTag.tag_collection` is over the tagged domain;
`Eind` in the current encoder is elementary membership indiscernibility and
must not silently be identified with the later bisimulation `Eqv` quotient.
The external route is good mathematical guidance, not an arithmetic proof
oracle or an already represented interpretation.

A concrete additional bridge is needed before promising native axiom images:

* Bind an actual represented full seed schema for source matrices, with
  literal self-code freshness and capture-safe parameter/role changes. The
  external proof uses `free_lt_enc` for the padded matrix. Existing
  `StreamFree`/`StreamAvoid` vacuity does not automatically prove freshness
  at that matrix's own code: it quantifies the **whole future** stream.
  A source occurrence/code-bound lemma or a carefully bounded binder
  transport must be proved, rather than postulated as `Vac k p`.
* Represent the seed-to-tagged comprehension/collection construction and
  the intended membership/equality/domain interpretation. Fixed standard
  matrices do not cover an internally coded arbitrary schema instance.
* Either establish the actual raw CP/GIC axiom images by a new explicit
  deduction, or use the correct tagged interpretation and its domain
  obligations. No raw CP impossibility is claimed here; neither route is
  supplied by the inspected C222 packets.
* `NativeSchema.provable_falsum_native_of_ZF` is reusable only if the actual
  native theory has genuinely been connected to C222. It supplies ZF→native
  under IΣ₁, not native→C222. `R2Ax.closure` is an old C254 proof of arbitrary
  closure and must be rebuilt with the actual C222 quantifier interface
  for whichever schema is selected.

The eventual substantive target is an unconditional all-internal theorem
`Provable (ZF : SetTheory) (^⊥ : V) → CProv222 1` under a stated arithmetic
fragment sufficient for **all** these invariants. This audit proves neither
that theorem nor its converse.

## 5. PA/HA and runtime boundaries

Once an unconditional all-model arithmetic theorem is proved with the
actual fixed source predicates, Foundation arithmetic completeness can
produce the corresponding PA proof existence, as in old R2Native. Standard
Nat `c222_iff_zf_refutation`, standard Tarski completeness alone, or checking
selected proof trees cannot replace the all-model/internal argument.

`FoundationHAPeano` and `FoundationHACurrentTransfer.current_iff_translated`
then offer an existing route from a **proved** actual PA equivalence to the
maintained HA equation sentence. The explicit PA-equivalence premise is
still missing. Accepted HA consistency normalization compares the literal
GG consistency with negation of the ordinary positive proof predicate; it
does not fill in this C222/source/machine calibration. The closed
`FoundationHAZFCValidator` comparison concerns the old actual C254 checker.

The separately owned actual history/proofword compiler connects CProv
witnesses with command execution. Root reports a new all-internal compiler
author PASS while this audit freezes; this note does not independently
review that new packet. It cannot replace source-theory axiom
interpretation, and the sequent/context work must not assume that compiler.
Neither lane yet supplies the complete internal machine/tableau/Diophantine
equivalence.

## 6. Provenance and build boundary

The accompanying JSON records exact source bytes and inspection scope. The
existing encoder/quantifier/existential replay summaries are pinned as
provider leads only. This audit did not authenticate or replay their objects,
did not construct a new closure, and asserts no new compiler result.

Before implementing the first leaf, traverse only its actual imports and
reauthenticate their current sources, accepted private 4.32 objects and
explicit external boundaries. The first context/negation work should reuse
the accepted C222 encoder/logical closure, without importing the old R2
proof modules or rebuilding Foundation. A later Proof.Basic import must be
included explicitly in that leaf's provenance. Existing frozen files remain
unchanged.
