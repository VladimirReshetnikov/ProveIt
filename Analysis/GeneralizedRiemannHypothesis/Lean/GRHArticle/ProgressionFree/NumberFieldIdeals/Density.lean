import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Natural density of sets of nonzero integral ideals

The denominator counts all nonzero integral ideals through the same norm.
Multiplication by a fixed nonzero ideal divides the density of an arbitrary
set by the ideal norm.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open Filter Topology NumberField Ideal
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- Number of ideals in the given set with absolute norm at most `X`. -/
noncomputable def countUpTo (A : Set (Ideal (𝓞 K))⁰) (X : ℝ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ // I ∈ A ∧ (absNorm I.val : ℝ) ≤ X}

/-- Count relative to all nonzero integral ideals in the norm ball. -/
noncomputable def densityUpTo (A : Set (Ideal (𝓞 K))⁰) (X : ℝ) : ℝ :=
  (countUpTo A X : ℝ) / countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) X

/-- Natural density in norm order, as in Section GPI of the article. -/
def HasNaturalDensity (A : Set (Ideal (𝓞 K))⁰) (d : ℝ) : Prop :=
  Tendsto (densityUpTo A) atTop (𝓝 d)

private theorem countUpTo_univ_eq (X : ℝ) :
    countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) X =
      Nat.card {I : (Ideal (𝓞 K))⁰ // (absNorm I.val : ℝ) ≤ X} := by
  simp [countUpTo]

theorem tendsto_countUpTo_univ_div :
    Tendsto (fun X : ℝ ↦ (countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) X : ℝ) / X) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  simpa only [countUpTo_univ_eq, dedekindZeta_residue_def] using
    NumberField.Ideal.tendsto_norm_le_div_atTop₀ K

/-- The relative normalization is equivalent to a linear counting asymptotic. -/
theorem hasNaturalDensity_iff_tendsto_div (A : Set (Ideal (𝓞 K))⁰) (d : ℝ) :
    HasNaturalDensity A d ↔ Tendsto (fun X : ℝ ↦ (countUpTo A X : ℝ) / X) atTop
      (𝓝 (d * dedekindZeta_residue K)) := by
  have h := tendsto_countUpTo_univ_div (K := K)
  have hp := dedekindZeta_residue_pos K
  constructor
  · intro hd
    apply (hd.mul h).congr'
    filter_upwards [h.eventually_const_lt hp] with X hX
    have hc : (countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) X : ℝ) ≠ 0 := by
      intro hz
      simp [hz] at hX
    simp only [densityUpTo, div_mul_div_cancel₀ hc]
  · intro hd
    have hlim := hd.div h hp.ne'
    rw [mul_div_cancel_right₀ _ hp.ne'] at hlim
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
    change (_ / X) / (_ / X) = _ / _
    exact div_div_div_cancel_right₀ hX.ne' _ _

theorem hasNaturalDensity_univ : HasNaturalDensity (Set.univ : Set (Ideal (𝓞 K))⁰) 1 :=
  (hasNaturalDensity_iff_tendsto_div _ _).mpr (by simpa using tendsto_countUpTo_univ_div (K := K))

/-- Multiplication by `J` transports each norm ball to the rescaled ball. -/
theorem countUpTo_mul_image (A : Set (Ideal (𝓞 K))⁰) (J : (Ideal (𝓞 K))⁰) (X : ℝ) :
    countUpTo ((J * ·) '' A) X = countUpTo A (X / absNorm J.val) := by
  classical
  symm
  apply Nat.card_congr
  apply Equiv.ofBijective (fun (I : {I : (Ideal (𝓞 K))⁰ // I ∈ A ∧ (absNorm I.val : ℝ) ≤ X / absNorm J.val}) ↦
    (⟨J*I.val, ⟨I.val,I.property.1,rfl⟩, by
      rw [Submonoid.coe_mul, map_mul, Nat.cast_mul, mul_comm]
      exact (le_div_iff₀ (Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors J))).mp I.property.2⟩ :
      {I : (Ideal (𝓞 K))⁰ // I ∈ ((J * ·) '' A) ∧ (absNorm I.val : ℝ) ≤ X}))
  constructor
  · intro i j h
    exact Subtype.ext (mul_left_cancel (congrArg Subtype.val h))
  · rintro ⟨_, ⟨I,hI,rfl⟩,hX⟩
    rw [Submonoid.coe_mul, map_mul, Nat.cast_mul, mul_comm] at hX
    exact ⟨⟨I,hI,(le_div_iff₀ (Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors J))).mpr hX⟩,rfl⟩

theorem HasNaturalDensity.mul_image {A : Set (Ideal (𝓞 K))⁰} {d : ℝ} (hA : HasNaturalDensity A d)
    (J : (Ideal (𝓞 K))⁰) : HasNaturalDensity ((J * ·) '' A) (d / absNorm J.val) := by
  have hp : (0:ℝ) < absNorm J.val := Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors J)
  have hd := (hasNaturalDensity_iff_tendsto_div A d).mp hA
  have ht := (hd.comp (tendsto_id.atTop_mul_const' (inv_pos.mpr hp))).div_const (absNorm J.val : ℝ)
  apply (hasNaturalDensity_iff_tendsto_div _ _).mpr
  convert ht using 1
  · funext X
    rw [countUpTo_mul_image]
    simp [div_eq_mul_inv, mul_assoc]
    left
    rw [mul_left_comm, mul_inv_cancel₀ hp.ne', mul_one]
  · ring

/-- The multiples of a fixed nonzero integral ideal have reciprocal-norm density. -/
theorem hasNaturalDensity_dvd (J : (Ideal (𝓞 K))⁰) :
    HasNaturalDensity {I | J ∣ I} (1 / absNorm J.val) := by
  have hset : (J * ·) '' (Set.univ : Set (Ideal (𝓞 K))⁰) = {I | J ∣ I} := by
    ext I
    constructor
    · rintro ⟨a,_,rfl⟩; exact ⟨a,rfl⟩
    · rintro ⟨a,rfl⟩; exact ⟨a,Set.mem_univ _,rfl⟩
  rw [← hset]
  exact hasNaturalDensity_univ.mul_image J

end GRHArticle.ProgressionFree.NumberFieldIdeals
