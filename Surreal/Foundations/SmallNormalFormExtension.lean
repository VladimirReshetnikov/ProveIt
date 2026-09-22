import Surreal.Foundations.SmallNormalFormComparison

/-!
# Extending a partial normal form by the next residual term

A partial form approximates an actual surreal when that surreal satisfies
all of its recursive center bounds. If the residual is nonzero, its leading
exponent is below every existing exponent. Appending its leading term
preserves the bounds and strictly extends the evaluated sign prefix.
This is a successor step for extraction, not a transfinite termination proof.
-/

universe u

namespace Surreal.Foundations.SmallNormalForm

open SignSequence

noncomputable section

/-- All recursive center constraints of a formal form hold for the given value. -/
def Approximates (F : SmallNormalForm.{u}) (x : SignSequence.{u}) : Prop :=
  ∀ a ∈ support F, (-a : WithTop SignSequence.{u}) <
    valuation (x - cutEvaluationCenter F a)

theorem approximates_cutEvaluation (F : SmallNormalForm.{u}) : Approximates F (cutEvaluation F) :=
  cutEvaluation_remainder F

@[simp] theorem approximates_zero (x : SignSequence.{u}) : Approximates 0 x := by
  intro a ha
  simp at ha

/-- A partial approximation is a sign prefix of the target. -/
theorem Approximates.isPrefix {F : SmallNormalForm.{u}} {x : SignSequence.{u}}
    (h : Approximates F x) : IsPrefix (cutEvaluation F) x :=
  cutEvaluation_isPrefix F x h

/-- The residual lies beyond every exponent already represented. -/
theorem Approximates.valuation_sub_gt {F : SmallNormalForm.{u}} {x : SignSequence.{u}}
    (h : Approximates F x) {a : SignSequence.{u}} (ha : a ∈ support F) :
    (-a : WithTop SignSequence.{u}) < valuation (x - cutEvaluation F) := by
  apply valuation_sub_gt_trans (h a ha)
  rw [valuation_sub_comm]
  exact cutEvaluation_remainder F a ha

/-- A nonzero residual has a growth exponent strictly below the existing support. -/
theorem Approximates.leadingExponent_lt {F : SmallNormalForm.{u}} {x : SignSequence.{u}}
    (h : Approximates F x) (hne : x - cutEvaluation F ≠ 0)
    {a : SignSequence.{u}} (ha : a ∈ support F) :
    SignSequence.leadingExponent (x - cutEvaluation F) < a := by
  have hv := h.valuation_sub_gt ha
  rw [valuation_of_ne_zero hne] at hv
  exact neg_lt_neg_iff.mp (WithTop.coe_lt_coe.mp hv)

/-- A new term below a cutoff has no effect on its earlier truncation. -/
theorem trunc_add_single_of_le (F : SmallNormalForm.{u}) (a b : SignSequence.{u}) (r : ℝ)
    (hab : a ≤ b) : trunc (F + single a r) b = trunc F b := by
  apply ext
  intro c
  simp only [coeff_trunc, coeff_add, coeff_single]
  by_cases hbc : b < c
  · have hca : c ≠ a := ne_of_gt (hab.trans_lt hbc)
    simp only [if_pos hbc, if_neg hca, _root_.add_zero]
  · simp only [if_neg hbc]

/-- Appending an exponent below the whole support leaves the original form
as the strict earlier truncation at that exponent. -/
theorem trunc_add_single_eq (F : SmallNormalForm.{u}) (a : SignSequence.{u}) (r : ℝ)
    (ha : ∀ b ∈ support F, a < b) : trunc (F + single a r) a = F := by
  rw [trunc_add_single_of_le F a a r le_rfl, trunc_eq_self_of_forall_lt F a ha]

/-- Append the leading term of the current actual residual. -/
def residualExtension (F : SmallNormalForm.{u}) (x : SignSequence.{u}) : SmallNormalForm.{u} :=
  F + single (SignSequence.leadingExponent (x - cutEvaluation F))
    (SignSequence.leadingCoeff (x - cutEvaluation F))

/-- The original partial form is the truncation of its residual extension. -/
theorem Approximates.trunc_residualExtension {F : SmallNormalForm.{u}} {x : SignSequence.{u}}
    (h : Approximates F x) (hne : x - cutEvaluation F ≠ 0) :
    trunc (residualExtension F x) (SignSequence.leadingExponent (x - cutEvaluation F)) = F :=
  trunc_add_single_eq F _ _ (fun _ hb => h.leadingExponent_lt hne hb)

/-- The newly appended coefficient is nonzero, so extension changes the formal form. -/
theorem Approximates.residualExtension_ne {F : SmallNormalForm.{u}} {x : SignSequence.{u}}
    (h : Approximates F x) (hne : x - cutEvaluation F ≠ 0) : residualExtension F x ≠ F := by
  let a := SignSequence.leadingExponent (x - cutEvaluation F)
  have ha : coeff F a = 0 := by
    by_contra ha
    exact (lt_irrefl a) (h.leadingExponent_lt hne ha)
  intro he
  have hc := congrArg (fun G => coeff G a) he
  change coeff (F + single a (SignSequence.leadingCoeff (x - cutEvaluation F))) a = coeff F a at hc
  simp [coeff_add, coeff_single, ha] at hc
  exact hne hc

/-- Removing the next leading residual term preserves every approximation constraint. -/
theorem Approximates.extend {F : SmallNormalForm.{u}} {x : SignSequence.{u}}
    (h : Approximates F x) (hne : x - cutEvaluation F ≠ 0) :
    Approximates (residualExtension F x) x := by
  let a := SignSequence.leadingExponent (x - cutEvaluation F)
  let r := SignSequence.leadingCoeff (x - cutEvaluation F)
  have ha : coeff F a = 0 := by
    by_contra ha
    exact (lt_irrefl a) (h.leadingExponent_lt hne ha)
  intro b hb
  by_cases hba : b = a
  · subst b
    change (-a : WithTop SignSequence.{u}) < valuation
      (x - (cutEvaluation (trunc (residualExtension F x) a) +
        ofReal (coeff (residualExtension F x) a) * omegaPower a))
    rw [h.trunc_residualExtension hne]
    have hc : coeff (residualExtension F x) a = r := by
      change coeff (F + single a r) a = r
      simp [coeff_add, coeff_single, ha]
    rw [hc]
    have hr := valuation_lt_sub_leadingTerm hne
    rw [valuation_of_ne_zero hne] at hr
    have he : x - (cutEvaluation F + ofReal r * omegaPower a) =
        (x - cutEvaluation F) - SignSequence.leadingTerm (x - cutEvaluation F) := by
      change x - (cutEvaluation F + ofReal r * omegaPower a) =
        (x - cutEvaluation F) - ofReal r * omegaPower a
      abel
    rw [he]
    exact hr
  · have hc : coeff (residualExtension F x) b = coeff F b := by
      change coeff (F + single a r) b = coeff F b
      simp only [coeff_add, coeff_single, if_neg hba, _root_.add_zero]
    have hbF : b ∈ support F := by simpa only [mem_support, hc] using hb
    have hab : a < b := h.leadingExponent_lt hne hbF
    have ht : trunc (residualExtension F x) b = trunc F b :=
      trunc_add_single_of_le F a b r hab.le
    change (-b : WithTop SignSequence.{u}) < valuation
      (x - (cutEvaluation (trunc (residualExtension F x) b) +
        ofReal (coeff (residualExtension F x) b) * omegaPower b))
    rw [ht, hc]
    exact h b hbF

/-- Every unfinished partial approximation admits a strictly longer evaluated
sign prefix which still approximates the same target. -/
theorem Approximates.exists_strict_extension {F : SmallNormalForm.{u}} {x : SignSequence.{u}}
    (h : Approximates F x) (hne : x - cutEvaluation F ≠ 0) :
    ∃ G : SmallNormalForm.{u}, Approximates G x ∧
      Simpler (cutEvaluation F) (cutEvaluation G) := by
  refine ⟨residualExtension F x, h.extend hne, ?_⟩
  have hp : IsPrefix (cutEvaluation F) (cutEvaluation (residualExtension F x)) := by
    simpa only [h.trunc_residualExtension hne] using
      cutEvaluation_trunc_isPrefix (residualExtension F x)
        (SignSequence.leadingExponent (x - cutEvaluation F))
  have hn : cutEvaluation F ≠ cutEvaluation (residualExtension F x) :=
    cutEvaluation_injective.ne (h.residualExtension_ne hne).symm
  refine ⟨hp, lt_of_le_of_ne hp.1 ?_⟩
  intro he
  apply hn
  apply hp.antisymm
  exact ⟨he.ge, fun i hi => (hp.2 i (hi.trans_le he.ge)).symm⟩

end

end Surreal.Foundations.SmallNormalForm
