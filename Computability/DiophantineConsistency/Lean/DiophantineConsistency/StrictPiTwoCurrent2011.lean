import DiophantineConsistency.StrictPiTwoBridge
import DiophantineConsistency.FoundationHACurrentNoZero2011
import ZFCinPA.ZFDelta1

/-!
# The strict Π₂ form of the current equation's consistency equivalence

The current fourteen-variable no-zero sentence is
`classicalSentence = ∀⁰* noZeroBody`, with an open matrix, and Foundation's
`Con(ZFC)` is `conSentence = ∼provSentence` with `provSentence` a `Σ₁` sentence.
`StrictPiTwoBridge` therefore applies with `θ := noZeroBody` and
`π := provSentence`, giving

* `nf`: the strict `Π₂` normal form (`nf_shape`: `∀⁰* (∃⁰^[15] D)` with `D` `Σ₀`);
* `strictCon`: the strict `Π₁` consistency sentence `∀ w, ¬bnd provSentence w`,
  built from Foundation's own ZFC proof predicate with its witnesses bounded;
* `isigma1_strictCon`: `𝗜𝚺₁ ⊢ conSentence ↔ strictCon`;
* `strict_nf`: from the `𝗜𝚺₁` endpoint, a proof of `nf` from `𝗣𝗔⁻` and strict
  `Σ₁` induction, the input of `ParsonsStrictInitial.strict_fragment`;
* `nf_valid`: `nf → (classicalSentence ↔ strictCon)` in pure equality logic.

The `𝗜𝚺₁` endpoint enters only as the hypothesis of `isigma1_nf` and
`strict_nf`; `StrictPiTwoCurrentEndpoint2011` discharges it with
`HACurrentEquation2011.isigma1_proves_current_iff_consistency`.
-/
set_option autoImplicit false

namespace DiophantineConsistency.StrictPiTwoCurrent2011

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.SetTheory
open StrictPiTwoBridge StrictSigmaOneInduction

/-- The open matrix of a no-zero sentence. -/
def noZeroBody {n : ℕ} (e : Expr (Fin n)) : Semisentence ℒₒᵣ n :=
  Semiformula.nrel .eq
    ![FoundationHANoZero.sourceTerm n (ArithmeticExpression.term Fin.val e.splitNatural.1),
      FoundationHANoZero.sourceTerm n (ArithmeticExpression.term Fin.val e.splitNatural.2)]

theorem noZeroBody_sigma0 {n : ℕ} (e : Expr (Fin n)) : Hierarchy 𝚺 0 (noZeroBody e) := by
  simp [noZeroBody]

/-- The current matrix. -/
def body : Semisentence ℒₒᵣ 14 := noZeroBody ObjectCurrentEquation2011.naturalExpression

theorem classicalSentence_eq : FoundationHACurrentNoZero2011.classicalSentence = ∀⁰* body := rfl

/-- Foundation's `Con(ZFC)`. -/
noncomputable def conSentence : ArithmeticSentence := (𝗭𝗙𝗖 : SetTheory).consistent

/-- The `Σ₁` refutability sentence. -/
noncomputable def provSentence : ArithmeticSentence := ∼conSentence

theorem provSentence_sigma1 : Hierarchy 𝚺 1 provSentence :=
  Hierarchy.neg (HierarchySymbol.Semiformula.pi_prop (𝗭𝗙𝗖 : SetTheory).consistent)

theorem neg_provSentence : ∼provSentence = conSentence := by simp [provSentence]

/-- **The strict `Π₂` normal form of the current equivalence.** -/
noncomputable def nf : ArithmeticSentence := normalForm body provSentence

/-- **The strict `Π₁` consistency sentence.** -/
noncomputable def strictCon : ArithmeticSentence := conB provSentence

theorem nf_shape : ∃ D : Semisentence ℒₒᵣ (15 + 15), Hierarchy 𝚺 0 D ∧ nf = ∀⁰* (∃⁰^[15] D) :=
  ⟨matrix body provSentence, matrix_sigma0 body provSentence (noZeroBody_sigma0 _)
    provSentence_sigma1, rfl⟩

theorem isigma1_strictCon : 𝗜𝚺₁ ⊢ conSentence 🡘 strictCon := by
  have h := isigma1_conB provSentence provSentence_sigma1
  rwa [neg_provSentence] at h

theorem isigma1_nf (h : 𝗜𝚺₁ ⊢ FoundationHACurrentNoZero2011.classicalSentence 🡘 conSentence) :
    𝗜𝚺₁ ⊢ nf := by
  refine isigma1_normalForm body provSentence provSentence_sigma1 ?_
  rwa [neg_provSentence, ← classicalSentence_eq]

/-- **A proof of the normal form from `𝗣𝗔⁻` and strict `Σ₁` induction.** -/
theorem strict_nf (h : 𝗜𝚺₁ ⊢ FoundationHACurrentNoZero2011.classicalSentence 🡘 conSentence) :
    𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ StrictSigma ⊢ nf :=
  isigma1_provable (isigma1_nf h)

/-- **Transport back**: the normal form gives the equivalence with `strictCon`. -/
theorem nf_valid :
    𝗘𝗤 ℒₒᵣ ⊢ nf 🡒 (FoundationHACurrentNoZero2011.classicalSentence 🡘 strictCon) := by
  rw [classicalSentence_eq]
  exact normalForm_valid body provSentence

end DiophantineConsistency.StrictPiTwoCurrent2011
