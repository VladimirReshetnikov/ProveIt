import ZFCinPA.LocalStepSuccessor
import ZFCinPA.SetCongruence

/-!
# The first field's source derivation: interface, design answer, and boundary

`ZFCinPA.LocalStepSuccessor` reduced the `localStep` field of
`ZFCinPA.StagedSuccessor.ZFCSuccessorImplications` to one ordinary Lean
proof over a theory with no model and no index in it:

> `templateZFC 2 levelArities ⊢! srcLocalStepStep`

This module does three things.

1. It **corrects the interface**.  The only general tool for producing a
   source derivation is `SetPlaceholderQuotient.complete_underSetPlaceholderCongruence`,
   and what that tool produces is never `templateZFC … ⊢! σ` but always
   `templateZFC … ⊢! congruence 🡒 σ`.  The congruence antecedent is a
   statement *about the placeholders* and is therefore not discharged at
   source level; it is discharged after translation, on the internalized
   side, by `SetCongruence.translatedCongruenceProof`.  This is exactly the
   shape of goal 1's arithmetic productions
   (`BoundedPAConsistency.DynamicTruthCrossLevelPositiveRankProduction.compiledDerivedStrongStepProof`,
   which consumes `complete_underPlaceholderCongruence` and discharges the
   translated antecedent with
   `TernaryCongruencePrototype.translatedTwoPredicateCongruenceContextProof`).
   `localStepSuccessor_of_congruentDerivation` below is the mirrored
   statement for this project.  **This is a strengthening of what a future
   source proof must supply, not a weakening of the obligation**: the
   hypothesis it asks for is strictly weaker than
   `localStepSuccessor_of_derivation`'s, and its conclusion is the same
   `localStep` field of `ZFCSuccessorImplications`.

2. It records the **design answer** that the `Residue` section of
   `ZFCinPA.LocalStepSuccessor` left open — which of goal 2's two
   conjuncts survives when the level-truth predicate is an arbitrary
   relation satisfying only the previous level's laws.  See
   `## The design answer` below.  The answer is: the first conjunct
   survives, the second does not.

3. It records the **boundary**: `srcLocalStepStep` as currently stated is
   *not* provable over `templateZFC 2 levelArities` (relative to the
   consistency of `𝗭𝗙𝗖`), and neither is the variant whose antecedent is
   widened by the previous certificate's `crossLevel` conjunct.  Two
   explicit countermodels are given below.  Nothing in this module or
   anywhere in the project assumes the unprovable sentence; the residual
   obligation stays an explicit argument.

## The design answer

Write the two placeholders as relations of a template structure
`X ⊧* templateZFC 2 ![1, 2]`: `Num` unary, `Clos` binary.  Unfolding the
source layer of `ZFCinPA.SuccessorSources` gives, with `⟨c, e, b⟩` for
`satTriple`:

* `LS₁ c e b :≡ ∃ n C, Num n ∧ Clos n C ∧ ⟨c, e, b⟩ ∈ C`
  — the specialization of `srcLevelSat`, i.e. level-`(x+1)` satisfaction;
* `Num₂ n' :≡ ∃ n, Num n ∧ n' = n⁺` — the specialization of
  `srcNumChainSucc`;
* `Cl₂ n C :≡ ∀ c e b, ⟨c, e, b⟩ ∈ C → IsUnivEnv e ∧ LevelJustified LS₁ n C c e b`
  — the specialization of `srcClosStep`, i.e. `BoundedZFCConsistency.LevelClosed`
  with the *previous level* taken to be `LS₁`;
* `LS₂ c e b :≡ ∃ n' C, Num₂ n' ∧ Cl₂ n' C ∧ ⟨c, e, b⟩ ∈ C`
  — the specialization of `srcLevelSatSucc`, i.e. level-`(x+2)`
  satisfaction.

`Σᵢ c e :≡ LSᵢ c e 1` and `Πᶠᵢ c e :≡ LSᵢ c e 0`.  `srcLocalStep` is then

> `∀ c e, IsUnivEnv e → (c = ⟨2, ∅⟩ → ¬ Σ₁ c e) ∧ (IsFormCode c → Σ₁ c e → ¬ Πᶠ₁ c e)`

and `srcLocalStepSucc` is the same with `Σ₂`, `Πᶠ₂`.

### Conjunct 1 survives

The falsity code `⟨2, ∅⟩` carries head tag `2`, and the five structural
rows of `BoundedZFCConsistency.LevelJustified` each force a head tag
in `{3, …, 7}`.  So `⟨⟨2, ∅⟩, e, 1⟩ ∈ C` with `Cl₂ n C` can only be
justified by the *delegation* row, which yields `Σ₁ ⟨2, ∅⟩ e` outright —
contradicting the antecedent's first conjunct.  That is exactly
`BoundedZFCConsistency.levelJustified_of_tag_low`, and its proof
(`formCode_tag_ne` at each of the five rows) is about the fixed macros
`fLevelImpF`, `fLevelAndF`, `fLevelOrF`, `fTagUnF` only.  It mentions the
previous level solely through the opaque parameter `L`, so it transfers
verbatim to an arbitrary interpretation of the placeholders.  Goal 2's
`sigmaTrue_bot` is literally this argument, run as an induction on the
metatheoretic level; here the induction step is supplied once, by the
antecedent.

### Conjunct 2 does not survive

Goal 2's `LevelCollapse.sigmaTrue_not_piFalse` proves the second conjunct
at level `m+1` from three things that the antecedent does *not* provide:

* the Tarski **elimination** clauses at the level
  (`sigmaTrue_imp_elim`, `piFalse_and_elim`, `sigmaTrue_or_elim`, …), each
  proved in `UniverseTruthLevel` by its own induction on the level;
* the **collapse** lemmas `piFalse_collapse_le` and
  `sigmaTrue_collapse_le`, which relate a level to *every* lower level and
  are what close the two quantifier rows;
* the level-`(m+1)` statement at every subcode, obtained by
  `isFormCodeSem_ind'`.

Only the third is cheap here.  The internal form-code induction is *not*
the obstruction, contrary to the guess recorded in
`LocalStepSuccessor`'s `Residue`: the induction predicate can be taken to
be

> `P c :≡ ∀ e, IsUnivEnv e → ¬ (⟨c, e, 1⟩ ∈ C₁ ∧ ⟨c, e, 0⟩ ∈ C₀)`

with the two witnessing *sets* `C₁`, `C₀` as parameters, and that is a
pure `ℒₛₑₜ` formula — an ordinary Separation instance of the lifted
theory, needing neither `SeparationKernel.compileOmegaTemplate` nor any
placeholder Separation.  The obstruction is the missing content of the
antecedent, and it is fatal:

**Countermodel A** (refutes conjunct 2 outright).  Let `M ⊧ 𝗭𝗙𝗖`,
`Num := {natV 5}`, `Clos := ∅`.  Then `LS₁` is empty, so `srcLocalStep`
holds vacuously.  But `Num₂ = {natV 6}`, and with `L := LS₁` empty the
side conditions `¬ L c e 0` and `¬ L c e 1` of the two quantifier rows of
`LevelJustified` hold *for free*.  Take `c := ⟨6, ⟨7, ⟨2, ∅⟩⟩⟩`, the code
of `∀∃⊥`, and `e` any universe environment.  Then

* `C₁ := {⟨c, e, 1⟩}` satisfies `Cl₂ (natV 6) C₁`, by the `∀`-row at
  `b = 1`: `PiBounded (natV 6) c` holds because `piRank (∀∃⊥) = 2 ≤ 5 + 1`
  (`piBounded_formCode_iff`), and `¬ LS₁ c e 0` is vacuous.  Hence
  `Σ₂ c e`.
* `C₀ := {⟨c, e, 0⟩, ⟨⟨7, ⟨2, ∅⟩⟩, econs d e, 0⟩}` satisfies
  `Cl₂ (natV 6) C₀`, by the `∀`-row at `b = 0` for the first record and
  the `∃`-row at `b = 0` for the second (`SigmaBounded (natV 6) (∃⊥)`
  holds, `¬ LS₁ · · 1` is vacuous).  Hence `Πᶠ₂ c e`.

`c` is a genuine form code, so `srcLocalStepSucc`'s second conjunct fails.
By soundness, `templateZFC 2 levelArities ⊬ srcLocalStepStep` — provided
`𝗭𝗙𝗖` has a model at all, which is why this cannot be turned into a Lean
refutation without `Con(𝗭𝗙𝗖)`.

**Countermodel B** (refutes the `crossLevel`-widened variant too, and
localizes the obstruction).  Same `M`, `Num := {natV 5}`, and

> `Clos n C :≡ n = natV 5 ∧ ∀ t ∈ C, ∃ c e, t = ⟨c, e, 0⟩`.

Then `LS₁ c e b ↔ b = 0`, so `Σ₁` is empty and `Πᶠ₁` is total.  Hence

* `srcLocalStep` holds — conjunct 1 vacuously, conjunct 2 vacuously;
* the source form of `crossLevelF` holds — `Σ₁ ∨ Πᶠ₁` is `false ∨ true`;
* the source forms of `shiftInvariantF` and `substitutionInvariantF` hold
  — every biconditional is `false ↔ false` or `true ↔ true`;
* conjunct 1 of `srcLocalStepSucc` still holds, since a tag-`2` code
  reaches only the delegation row and `LS₁ ⟨2, ∅⟩ e 1` is false.  (The
  design answer's two halves are visible in the same structure.)

But take `c := ⟨3, ⟨⟨2, ∅⟩, ⟨2, ∅⟩⟩⟩`, the code of `⊥ 🡒 ⊥`.  Then
`C₁ := {⟨c, e, 1⟩, ⟨⟨2, ∅⟩, e, 0⟩}` is `Cl₂ (natV 6)`-closed — the first
record by the implication row at `b = 1` (whose `b = 1` disjunct asks only
for the *antecedent at bit 0*, which is present), the second by
delegation, since `LS₁ ⟨2, ∅⟩ e 0` holds.  And `C₀ := {⟨c, e, 0⟩}` is
`Cl₂ (natV 6)`-closed by delegation alone.  So `Σ₂ c e ∧ Πᶠ₂ c e` at a
genuine form code: conjunct 2 of `srcLocalStepSucc` fails.

So the missing content is precisely the Tarski *elimination* clauses at
level `x+1` (here: `Σ₁ (a 🡒 b) e → ¬ Πᶠ₁ a e ∨ Σ₁ b e`) together with the
adjacent-level collapse for the two quantifier rows.  Neither is among the
five fields of `ZFCinPA.CertificateFields`, and neither follows from them:
adding them means enlarging `ZFCTruthCertificateFields`, since at level
`x+1` the closure relation is the *opaque* placeholder `Clos` and no
closed set can be constructed there — only inspected.

`ZFCSuccessorImplications` is not weakened anywhere by this analysis, and
no part of the unprovable sentence is assumed: both reductions below take
the source proof as an explicit argument.
-/

set_option autoImplicit false

namespace LeanProofs
namespace ZFCinPA
namespace LocalStepDerivation

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SetPlaceholderQuotient
open LeanProofs.ZFCinPA.LocalStepSuccessor

/-! ## The design answer, machine-checked

The two statements of this section are the abstract kernel of the design
answer.  They are stated in goal 2's own vocabulary — `LevelClosed`,
`LevelJustified`, with the *previous level* an arbitrary relation `L`,
which is exactly the generality that an abstract interpretation of the two
placeholders provides — so they settle the transfer question without any
reference to the source language.

What they do **not** do is bridge the source formulas to these predicates:
that evaluation layer (the set-theoretic counterpart of goal 1's
`eval_source…` family) is not built here.  The bridge is a routine, if
long, unfolding of `srcClosStep`/`srcJustRow`/`srcLvlInstP` through
`Translation.eval_toSet`; nothing below depends on it, and nothing below
is used to justify a claim about `srcLocalStepStep` other than the
informal reading recorded in the module header. -/

section DesignAnswer

universe u

open SetTheory (ZFAxioms vempty vsingle vcup vcup_spec vsingle_spec)
open BoundedZFCConsistency

variable {W : Type u} {mem : W → W → Prop}

local notation "kpair'" => _root_.SetTheory.kpair

/-- **Conjunct 1 transfers to an arbitrary previous level.**

If the previous level `L` — an arbitrary ternary relation, in particular
any interpretation of the two placeholders — never makes the falsity code
Sigma-true, then no `L`-step-closed set contains the falsity record at
bit `1`, whatever the bound.  Equivalently: `srcLocalStep`'s first
conjunct implies `srcLocalStepSucc`'s first conjunct.

The whole argument is `levelJustified_of_tag_low`: the five structural
rows of `LevelJustified` each force a head tag in `{3, …, 7}`, and the
falsity code carries head tag `2`, so only the delegation row survives.
No property of `L` beyond the hypothesis is used, and no closed set is
ever constructed — which matters, because at the placeholder level none
can be. -/
theorem bot_notSigma_step (H : ZFAxioms mem) {L : W → W → W → Prop}
    (hL : ∀ e, ¬ L (kpair' H (natV H 2) (vempty H)) e (natV H 1))
    {bnd C e : W} (hC : LevelClosed H L bnd C)
    (hmem : mem (satTriple H (kpair' H (natV H 2) (vempty H)) e (natV H 1)) C) :
    False :=
  hL e (levelJustified_of_tag_low H (t := 2) (by omega) (hC _ _ _ hmem).2)

/-- **Conjunct 2 does not transfer.**

There is a previous level `L` whose Sigma side is *empty* — so both
conjuncts of `srcLocalStep` hold at `L`, vacuously, and so does the source
form of the `crossLevel` field, since `L`'s Pi-false side is total — for
which the next level's exclusivity nevertheless fails: a genuine form code
`c` sits at bit `1` in one `L`-step-closed set and at bit `0` in another.

The witness is `c = ⊥ 🡒 ⊥`.  Its bit-`1` record is justified by the
implication row, whose positive disjunct asks only for the *antecedent at
bit `0`* — and that record is justified by delegation, because `L` makes
everything Pi-false.  Its bit-`0` record is justified by delegation
outright.

This is countermodel B of the module header, transported into the abstract
closure semantics, and it is the exact reason the second conjunct of the
local-step field cannot be produced by the source-template route from a
single level's polarity laws: what is missing is the Tarski *elimination*
clause for the implication tag at the previous level, which is not among
the five fields of `ZFCinPA.CertificateFields`. -/
theorem exclusivity_not_step_transferable (H : ZFAxioms mem) {e : W}
    (he : IsUnivEnv H e) (bnd : W) :
    ∃ (L : W → W → W → Prop) (c C₁ C₀ : W),
      (∀ c' e', ¬ L c' e' (natV H 1)) ∧
      IsFormCodeSem H c ∧
      (LevelClosed H L bnd C₁ ∧ mem (satTriple H c e (natV H 1)) C₁) ∧
      (LevelClosed H L bnd C₀ ∧ mem (satTriple H c e (natV H 0)) C₀) := by
  set L : W → W → W → Prop := fun _ _ b ↦ b = natV H 0 with hLdef
  set bot : W := kpair' H (natV H 2) (vempty H) with hbot
  set c : W := kpair' H (natV H 3) (kpair' H bot bot) with hc
  -- The antecedent record, justified by delegation.
  have hCa : LevelClosed H L bnd
      (vcup H (vempty H) (vsingle H (satTriple H bot e (natV H 0)))) :=
    levelClosed_insert H (levelClosed_empty H L bnd) he (Or.inl rfl)
  set Ca : W := vcup H (vempty H) (vsingle H (satTriple H bot e (natV H 0)))
    with hCadef
  have hmemBot : mem (satTriple H bot e (natV H 0)) Ca :=
    (vcup_spec H _ _ _).mpr (Or.inr ((vsingle_spec H _ _).mpr rfl))
  -- The implication record at bit one, justified by the implication row.
  have hjust : LevelJustified H L bnd Ca c e (natV H 1) :=
    Or.inr (Or.inl ⟨bot, bot, rfl, Or.inl ⟨rfl, Or.inl hmemBot⟩⟩)
  refine ⟨L, c, vcup H Ca (vsingle H (satTriple H c e (natV H 1))),
    vcup H (vempty H) (vsingle H (satTriple H c e (natV H 0))),
    fun _ _ h ↦ natV_ne H (by decide) h,
    isFormCodeSem_imp H (isFormCodeSem_bot H) (isFormCodeSem_bot H),
    ⟨levelClosed_insert H hCa he hjust,
      (vcup_spec H _ _ _).mpr (Or.inr ((vsingle_spec H _ _).mpr rfl))⟩,
    ⟨levelClosed_insert H (levelClosed_empty H L bnd) he (Or.inl rfl),
      (vcup_spec H _ _ _).mpr (Or.inr ((vsingle_spec H _ _).mpr rfl))⟩⟩

end DesignAnswer

/-! ## The congruence antecedent at the level-tower arities -/

/-- The two placeholder congruence laws of the level tower, as one source
sentence.  This is the antecedent that
`SetPlaceholderQuotient.complete_underSetPlaceholderCongruence` always
leaves in front of a semantically obtained source sentence. -/
noncomputable def srcCongruence : Sentence srcL :=
  setPlaceholderCongruence 2 levelArities

/-- **The congruence-widened source obligation of the first field.**  This,
not `srcLocalStepStep`, is what the completeness route can produce: the
congruence laws are statements about the placeholders and cannot be
discharged at source level. -/
noncomputable def srcCongruentLocalStepStep : Sentence srcL :=
  srcCongruence 🡒 srcLocalStepStep

/-! ## Discharging the congruence antecedent after translation -/

section Congruence

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The two model-coded leaves satisfy their internal congruence laws.
The numeral chain is unary (`SetCongruence.congruenceProof₁`) and the
closure kernel binary (`SetCongruence.congruenceProof₂`); no property of
the — possibly nonstandard — codes is used beyond their arity. -/
theorem congruenceProof_levelLeaves (x : V) : ∀ i : Fin 2,
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢
      SetCongruence.congruenceFormula (levelArities i) (levelLeaves x i)
  | ⟨0, _⟩ => SetCongruence.congruenceProof₁ _ _
  | ⟨1, _⟩ => SetCongruence.congruenceProof₂ _ _

/-- **The translated congruence antecedent is internally provable.**  This
is the set-theoretic counterpart of goal 1's
`TernaryCongruencePrototype.translatedTwoPredicateCongruenceContextProof`. -/
theorem translated_srcCongruence (x : V) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢
      translateFormula (levelLeaves x)
        (Rewriting.emb srcCongruence : Proposition srcL) :=
  SetCongruence.translatedCongruenceProof (𝗭𝗙𝗖 : SetTheory) (levelLeaves x)
    (congruenceProof_levelLeaves x)

end Congruence

/-! ## The corrected reduction -/

section Reduction

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **From a congruence-guarded source template to the local-step
successor.**  Identical to
`LocalStepSuccessor.localStepSuccessor_of_source` except that the source
derivation may carry the placeholder congruence laws as an antecedent —
which is what the completeness route actually yields.  The antecedent is
discharged on the internalized side by `translated_srcCongruence`, so the
conclusion is unchanged. -/
noncomputable def localStepSuccessor_of_congruentSource
    (σ : Sentence srcL)
    (hσ : ∀ x : V, translateFormula (levelLeaves x) (Rewriting.emb σ) =
      (localStepFormula x 🡒 localStepFormula (x + 1)))
    (d : templateZFC 2 levelArities ⊢! (srcCongruence 🡒 σ))
    (n : V) (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n)) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      ((concreteZFCTruthCertificateFamily (V := V)).fields n h).sentence 🡒
        localStepFormula (n + 1) := by
  have hc := compileSetTemplate (levelLeaves n) (shift_levelLeaves n) d
  rw [show (Rewriting.emb (srcCongruence 🡒 σ) : Proposition srcL) =
        ((Rewriting.emb srcCongruence : Proposition srcL) 🡒
          (Rewriting.emb σ : Proposition srcL)) from by
      simp only [LogicalConnective.HomClass.map_imply],
    translateFormula_imp, hσ n] at hc
  exact LO.Entailment.C_trans (previous_imp_localStep n h)
    (hc ⨀ (translated_srcCongruence (V := V) n).some)

/-- **The first field's successor, reduced to the congruence-widened
derivation.**  Every other ingredient is proved: the source sentence, its
specialization identity at every possibly nonstandard index
(`translate_srcLocalStepStep`), shift-fixedness of the two model-coded
leaves (`SuccessorSources.shift_levelLeaves`), and the translated
congruence antecedent (`translated_srcCongruence`).

The remaining hypothesis is an explicit argument and is **not** assumed
anywhere.  It is also, as the module header shows, *false* relative to
`Con(𝗭𝗙𝗖)`: see `## The design answer`.  The declaration is kept because
it is the exact statement whose antecedent a future enlargement of
`ZFCTruthCertificateFields` has to make derivable. -/
noncomputable def localStepSuccessor_of_congruentDerivation
    (d : templateZFC 2 levelArities ⊢! srcCongruentLocalStepStep)
    (n : V) (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n)) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      ((concreteZFCTruthCertificateFamily (V := V)).fields n h).sentence 🡒
        localStepFormula (n + 1) :=
  localStepSuccessor_of_congruentSource srcLocalStepStep
    translate_srcLocalStepStep d n h

end Reduction

end LocalStepDerivation
end ZFCinPA
end LeanProofs
