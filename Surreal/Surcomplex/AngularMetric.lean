import Surreal.Surcomplex.AngularDistance

/-!
# Metric axioms for the actual angular distance

The metric assertion before `trigonometry:thm:metric` follows from the
least-absolute-angle property. Its distances are actual surreals, so this
is not a real-valued `MetricSpace` instance.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

private theorem unitCircleAngle_eq_of_cos (z : UnitCircle.{u})
    (θ : SignSequence.FiniteElement.{u})
    (hθ : θ.val ∈ Set.Icc 0 (SignSequence.ofReal Real.pi))
    (hc : finiteCos θ = z.val.re) : unitCircleAngle z = θ := by
  have he := arccos_finiteCos θ hθ
  simpa only [unitCircleAngle, hc] using he

/-- Any representative in the closed principal interval has the least absolute angle. -/
theorem unitCircleAngle_eq_abs_of_phase (z : UnitCircle.{u})
    (θ : SignSequence.FiniteElement.{u}) (he : finitePhase θ = z.val)
    (hθ : |θ.val| ≤ SignSequence.ofReal Real.pi) :
    (unitCircleAngle z).val = |θ.val| := by
  have hc : finiteCos θ = z.val.re := congrArg (fun w : Surcomplex.{u} => w.re) he
  by_cases hp : 0 ≤ θ.val
  · rw [abs_of_nonneg hp] at hθ ⊢
    rw [unitCircleAngle_eq_of_cos z θ ⟨hp, hθ⟩ hc]
  · have hn : θ.val ≤ 0 := (lt_of_not_ge hp).le
    rw [abs_of_nonpos hn] at hθ ⊢
    have hm : (-θ).val ∈ Set.Icc 0 (SignSequence.ofReal Real.pi) := ⟨neg_nonneg.mpr hn, hθ⟩
    have hcn : finiteCos (-θ) = z.val.re := by rw [finiteCos_neg, hc]
    rw [unitCircleAngle_eq_of_cos z (-θ) hm hcn]
    rfl

/-- Taking the unsigned principal angle cannot increase the absolute value of a representative. -/
theorem unitCircleAngle_le_abs_of_phase (z : UnitCircle.{u})
    (θ : SignSequence.FiniteElement.{u}) (he : finitePhase θ = z.val) :
    (unitCircleAngle z).val ≤ |θ.val| := by
  by_cases hθ : |θ.val| ≤ SignSequence.ofReal Real.pi
  · exact (unitCircleAngle_eq_abs_of_phase z θ he hθ).le
  · exact (unitCircleAngle_mem z).2.trans (le_of_not_ge hθ)

/-- Angular distance is the absolute value of any principal relative-angle representative. -/
theorem angularDistance_eq_abs_of_phase (z w : UnitCircle.{u})
    (θ : SignSequence.FiniteElement.{u}) (he : finitePhase θ = (z⁻¹ * w).val)
    (hθ : |θ.val| ≤ SignSequence.ofReal Real.pi) :
    angularDistance z w = |θ.val| := unitCircleAngle_eq_abs_of_phase _ θ he hθ

/-- The relative direction always has a principal representative realizing angular distance. -/
theorem exists_angularDistance_representative (z w : UnitCircle.{u}) :
    ∃ θ : SignSequence.FiniteElement.{u}, IsPrincipalAngle θ ∧
      finitePhase θ = (z⁻¹ * w).val ∧ angularDistance z w = |θ.val| := by
  obtain ⟨θ, ⟨hθ, he⟩, _⟩ := existsUnique_principal_phase (z⁻¹ * w).val (modulus_unitCircle _)
  exact ⟨θ, hθ, he, angularDistance_eq_abs_of_phase z w θ he (abs_le.mpr ⟨hθ.1.le, hθ.2⟩)⟩

/-- Angular distance is symmetric. -/
theorem angularDistance_comm (z w : UnitCircle.{u}) : angularDistance z w = angularDistance w z := by
  have he : (z⁻¹ * w).val.re = (w⁻¹ * z).val.re := by
    simp only [coe_unitCircle_relative, mul_re, conj_re, conj_im]
    ring
  unfold angularDistance unitCircleAngle
  congr 2
  exact Subtype.ext he

/-- The only zero angular distances are between identical directions. -/
@[simp] theorem angularDistance_eq_zero_iff (z w : UnitCircle.{u}) :
    angularDistance z w = 0 ↔ z = w := by
  constructor
  · intro h
    have he := (angularDistance_chord_bounds z w).1
    rw [h] at he
    exact Subtype.ext (sub_eq_zero.mp ((modulus_eq_zero_iff _).mp
      (le_antisymm he (modulus_nonneg _))))
  · rintro rfl
    have he := (angularDistance_chord_bounds z z).2
    simp only [sub_self, modulus_zero, mul_zero] at he
    exact le_antisymm he (angularDistance_nonneg z z)

@[simp] theorem angularDistance_self (z : UnitCircle.{u}) : angularDistance z z = 0 :=
  (angularDistance_eq_zero_iff z z).mpr rfl

/-- The actual surreal-valued angular distance satisfies the triangle inequality. -/
theorem angularDistance_triangle (z w v : UnitCircle.{u}) :
    angularDistance z v ≤ angularDistance z w + angularDistance w v := by
  obtain ⟨θ, _, hθ, heθ⟩ := exists_angularDistance_representative z w
  obtain ⟨φ, _, hφ, heφ⟩ := exists_angularDistance_representative w v
  have he : finitePhase (θ + φ) = (z⁻¹ * v).val := by
    rw [finitePhase_add, hθ, hφ]
    change ((z⁻¹ * w) * (w⁻¹ * v)).val = (z⁻¹ * v).val
    congr 1
    group
  have h := unitCircleAngle_le_abs_of_phase (z⁻¹ * v) (θ + φ) he
  change angularDistance z v ≤ |θ.val + φ.val| at h
  rw [heθ, heφ]
  exact h.trans (abs_add_le _ _)

end
end Surreal.Surcomplex
