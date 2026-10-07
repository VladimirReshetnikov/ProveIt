import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

open scoped BigOperators

namespace Erdos3

noncomputable def finiteCorrelation {Ω : Type*} (Q : Finset Ω) (f u : Ω → ℂ) : ℂ :=
  𝔼 x ∈ Q, f x * star (u x)

theorem finiteCorrelation_sub_right {Ω : Type*} (Q : Finset Ω) (f u v : Ω → ℂ) :
    finiteCorrelation Q f (fun x => u x - v x) =
      finiteCorrelation Q f u - finiteCorrelation Q f v := by
  simp only [finiteCorrelation, star_sub, mul_sub, Finset.expect_sub_distrib]

theorem finiteCorrelation_sum_right {Ω J : Type*} [Fintype J]
    (Q : Finset Ω) (f : Ω → ℂ) (u : J → Ω → ℂ) :
    finiteCorrelation Q f (fun x => ∑ j, u j x) = ∑ j, finiteCorrelation Q f (u j) := by
  simp only [finiteCorrelation, star_sum, Finset.mul_sum, Finset.expect_sum_comm]

theorem norm_finiteCorrelation_le {Ω : Type*} {Q : Finset Ω} (hQ : Q.Nonempty)
    (f u : Ω → ℂ) {B : ℝ} (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hu : ∀ x ∈ Q, ‖u x‖ ≤ B) :
    ‖finiteCorrelation Q f u‖ ≤ B := by
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply (Finset.expect_le_expect _).trans_eq (Finset.expect_const hQ B)
  intro x hx
  simpa only [norm_mul, norm_star, one_mul] using
    mul_le_mul (hf x hx) (hu x hx) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem norm_finiteCorrelation_sub_le {Ω : Type*} {Q : Finset Ω} (hQ : Q.Nonempty)
    (f u v : Ω → ℂ) {δ : ℝ} (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1)
    (huv : ∀ x ∈ Q, ‖u x - v x‖ ≤ δ) :
    ‖finiteCorrelation Q f u - finiteCorrelation Q f v‖ ≤ δ := by
  rw [← finiteCorrelation_sub_right]
  exact norm_finiteCorrelation_le hQ f _ hf huv

theorem exists_correlating_summand {Ω J : Type*} [Fintype J]
    {Q : Finset Ω} (hQ : Q.Nonempty) (f u : Ω → ℂ) (v : J → Ω → ℂ)
    {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 < M) (hcard : (Fintype.card J : ℝ) ≤ M)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1)
    (happrox : ∀ x ∈ Q, ‖(∑ j, v j x) - u x‖ ≤ ρ / 2)
    (hcorr : ρ ≤ ‖finiteCorrelation Q f u‖) :
    ∃ j, ρ / (2 * M) ≤ ‖finiteCorrelation Q f (v j)‖ := by
  classical
  have herr := norm_finiteCorrelation_sub_le hQ f (fun x => ∑ j, v j x) u hf happrox
  rw [finiteCorrelation_sum_right] at herr
  have htriangle := norm_le_norm_add_norm_sub
    (∑ j, finiteCorrelation Q f (v j)) (finiteCorrelation Q f u)
  have hsum : ρ / 2 ≤ ∑ j, ‖finiteCorrelation Q f (v j)‖ := by
    have hn := norm_sum_le (Finset.univ : Finset J) (fun j => finiteCorrelation Q f (v j))
    linarith
  have hJ : (Finset.univ : Finset J).Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.sum_empty] at hsum
    linarith
  have hthreshold : 0 ≤ ρ / (2 * M) := le_of_lt (div_pos hρ (by positivity))
  have hconstants : (∑ _j : J, ρ / (2 * M)) ≤ ρ / 2 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc
      _ ≤ M * (ρ / (2 * M)) := mul_le_mul_of_nonneg_right hcard hthreshold
      _ = ρ / 2 := by field_simp
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le hJ (hconstants.trans hsum)
  exact ⟨j, hj⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteSiteExtension {T X : Type*} [Nonempty T]
    (e : T → X) (f : T → ℂ) : X → ℂ := fun x => f (Function.invFun e x)

theorem finiteSiteExtension_apply {T X : Type*} [Nonempty T]
    (e : T → X) (he : Function.Injective e) (f : T → ℂ) (t : T) :
    finiteSiteExtension e f (e t) = f t := by
  rw [finiteSiteExtension, Function.leftInverse_invFun he t]

theorem finiteSiteExtension_norm_le {T X : Type*} [Nonempty T]
    (e : T → X) (f : T → ℂ) {B : ℝ} (hf : ∀ t, ‖f t‖ ≤ B) (x : X) :
    ‖finiteSiteExtension e f x‖ ≤ B := hf _

theorem finiteSiteExtension_test_mean {T X : Type*} [Nonempty T] [DecidableEq X]
    (e : T → X) (he : Function.Injective e) (A : Finset T)
    (f w : T → ℂ) (ψ : X → ℂ) (hw : ∀ t ∈ A, w t = star (ψ (e t))) :
    (𝔼 t ∈ A, f t * w t) = finiteCorrelation (A.image e) (finiteSiteExtension e f) ψ := by
  unfold finiteCorrelation
  rw [Finset.expect_image he.injOn]
  apply Finset.expect_congr rfl
  intro t ht
  rw [finiteSiteExtension_apply e he, hw t ht]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_correlating_weighted_summand {Ω J : Type*} [Fintype J]
    {Q : Finset Ω} (hQ : Q.Nonempty) (f u : Ω → ℂ) (v : J → Ω → ℂ) (c : J → ℂ)
    {ρ M B : ℝ} (hρ : 0 < ρ) (hM : 0 < M) (hB : 0 < B)
    (hcard : (Fintype.card J : ℝ) ≤ M) (hc : ∀ j, ‖c j‖ ≤ B)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1)
    (happrox : ∀ x ∈ Q, ‖(∑ j, c j * v j x) - u x‖ ≤ ρ / 2)
    (hcorr : ρ ≤ ‖finiteCorrelation Q f u‖) :
    ∃ j, ρ / (2 * M * B) ≤ ‖finiteCorrelation Q f (v j)‖ := by
  obtain ⟨j, hj⟩ := exists_correlating_summand hQ f u (fun j x => c j * v j x)
    hρ hM hcard hf happrox hcorr
  have heq : finiteCorrelation Q f (fun x => c j * v j x) =
      star (c j) * finiteCorrelation Q f (v j) := by
    unfold finiteCorrelation
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    simp only [star_mul]
    ring
  rw [heq, norm_mul, norm_star] at hj
  refine ⟨j, ?_⟩
  rw [← div_div]
  apply (div_le_iff₀ hB).mpr
  simpa only [mul_comm] using hj.trans
    (mul_le_mul_of_nonneg_right (hc j) (norm_nonneg _))

end Erdos3

end

end OAI
