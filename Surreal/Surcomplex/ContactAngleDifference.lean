import Surreal.Surcomplex.InverseTrigonometricDerivative

/-!
# Exact signed differences of interior inverse-cosine angles

Sum-to-product identities express the signed difference of two interior inverse-cosine
angles as twice an inverse tangent. This exact formula is the geometric prerequisite for
the relative perturbation estimate in `trigonometry:eq:contactstability`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

private theorem contact_arccos_mem_Ioo (x : Set.Icc (-1 : SignSequence.{u}) 1)
    (hx : x.val ∈ Set.Ioo (-1) 1) :
    (arccos x).val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi) := by
  have hm := arccos_mem x
  constructor
  · apply lt_of_le_of_ne hm.1
    intro he
    have ha : arccos x = 0 := ArchimedeanClass.FiniteElement.ext he.symm
    have hc := finiteCos_arccos x
    rw [ha, finiteCos_zero] at hc
    exact hx.2.ne hc.symm
  · apply lt_of_le_of_ne hm.2
    intro he
    have ha : arccos x = SignSequence.finiteOfReal Real.pi :=
      ArchimedeanClass.FiniteElement.ext he
    have hc := finiteCos_arccos x
    rw [ha, finiteCos_constant, Real.cos_pi, map_neg, map_one] at hc
    exact hx.1.ne hc

/-- The sine coordinate of inverse cosine uses the nonnegative square root, including endpoints. -/
theorem finiteSin_arccos (x : Set.Icc (-1 : SignSequence.{u}) 1) :
    finiteSin (arccos x) = SignSequence.sqrt (1 - x.val ^ 2) := by
  rw [arccos_eq_pi_div_two_sub_arcsin, finiteSin_sub]
  simp only [finiteSin_constant, finiteCos_constant, Real.sin_pi_div_two,
    Real.cos_pi_div_two, map_one, map_zero, one_mul, zero_mul, sub_zero, finiteCos_arcsin]

/-- Interior inverse-cosine differences have an exact half-angle tangent formula,
with the sign of `x - y` retained. -/
theorem arccosFunction_difference_eq_two_arctan (x y : SignSequence.{u})
    (hx : x ∈ Set.Ioo (-1) 1) (hy : y ∈ Set.Ioo (-1) 1) :
    arccosFunction y - arccosFunction x =
      2 * arctanFunction ((x - y) /
        (SignSequence.sqrt (1 - x ^ 2) + SignSequence.sqrt (1 - y ^ 2))) := by
  let α := arccos ⟨x, hx.1.le, hx.2.le⟩
  let β := arccos ⟨y, hy.1.le, hy.2.le⟩
  have hα := contact_arccos_mem_Ioo ⟨x, hx.1.le, hx.2.le⟩ hx
  have hβ := contact_arccos_mem_Ioo ⟨y, hy.1.le, hy.2.le⟩ hy
  change α.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi) at hα
  change β.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi) at hβ
  have hhalf : (finiteHalf (β - α)).val ∈
      Set.Ioo (SignSequence.ofReal (-(Real.pi / 2))) (SignSequence.ofReal (Real.pi / 2)) := by
    rw [val_finiteHalf, map_neg, map_div₀, map_ofNat]
    change -(SignSequence.ofReal Real.pi / 2) < (β.val - α.val) / 2 ∧
      (β.val - α.val) / 2 < SignSequence.ofReal Real.pi / 2
    constructor <;> linarith only [hα.1, hα.2, hβ.1, hβ.2]
  have hcos := finiteCos_pos_of_mem_Ioo _ hhalf
  have hsum : 0 < finiteSin β + finiteSin α :=
    add_pos (finiteSin_pos_of_mem_Ioo _ hβ) (finiteSin_pos_of_mem_Ioo _ hα)
  have ht : finiteTan (finiteHalf (β - α)) =
      (finiteCos α - finiteCos β) / (finiteSin β + finiteSin α) := by
    unfold finiteTan
    apply (div_eq_div_iff hcos.ne' hsum.ne').mpr
    have hs := finiteSin_add_finiteSin β α
    have hc := finiteCos_sub_finiteCos β α
    linear_combination finiteSin (finiteHalf (β - α)) * hs +
      finiteCos (finiteHalf (β - α)) * hc
  have ha := congrArg (fun θ : SignSequence.FiniteElement.{u} => θ.val)
    (arctan_finiteTan (finiteHalf (β - α)) hhalf)
  rw [ht, val_finiteHalf] at ha
  have hcα : finiteCos α = x := finiteCos_arccos _
  have hcβ : finiteCos β = y := finiteCos_arccos _
  have hsα : finiteSin α = SignSequence.sqrt (1 - x ^ 2) :=
    finiteSin_arccos _
  have hsβ : finiteSin β = SignSequence.sqrt (1 - y ^ 2) :=
    finiteSin_arccos _
  change arctanFunction ((finiteCos α - finiteCos β) /
    (finiteSin β + finiteSin α)) = (β.val - α.val) / 2 at ha
  rw [hcα, hcβ, hsα, hsβ, add_comm (SignSequence.sqrt (1 - y ^ 2))] at ha
  have hxa : arccosFunction x = α.val := arccosFunction_eq ⟨x, hx.1.le, hx.2.le⟩
  have hya : arccosFunction y = β.val := arccosFunction_eq ⟨y, hy.1.le, hy.2.le⟩
  rw [hxa, hya]
  linarith only [ha]

/-- The signed endpoint-defect version has the sum of the two positive circle heights
as its denominator. -/
theorem arccosFunction_one_sub_difference (τ σ : SignSequence.{u})
    (hτ : τ ∈ Set.Ioo 0 2) (hσ : σ ∈ Set.Ioo 0 2) :
    arccosFunction (1 - σ) - arccosFunction (1 - τ) =
      2 * arctanFunction ((σ - τ) /
        (SignSequence.sqrt (τ * (2 - τ)) + SignSequence.sqrt (σ * (2 - σ)))) := by
  have hx : 1 - τ ∈ Set.Ioo (-1 : SignSequence.{u}) 1 := by
    constructor <;> linarith only [hτ.1, hτ.2]
  have hy : 1 - σ ∈ Set.Ioo (-1 : SignSequence.{u}) 1 := by
    constructor <;> linarith only [hσ.1, hσ.2]
  rw [arccosFunction_difference_eq_two_arctan _ _ hx hy,
    show 1 - τ - (1 - σ) = σ - τ by ring,
    show 1 - (1 - τ) ^ 2 = τ * (2 - τ) by ring,
    show 1 - (1 - σ) ^ 2 = σ * (2 - σ) by ring]

end Surreal.Surcomplex
