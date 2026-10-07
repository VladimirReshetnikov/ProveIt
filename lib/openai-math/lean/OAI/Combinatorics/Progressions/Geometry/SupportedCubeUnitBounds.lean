/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.SampledCommonSlice

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem normalizedSupportedCubeSum_norm_le_one {A : Type*} [AddCommGroup A]
    (j : ℕ) (Q : Finset A) (F : (Fin j → Bool) → A → ℂ)
    (hF : ∀ ω x, x ∈ Q → ‖F ω x‖ ≤ 1) :
    ‖normalizedSupportedCubeSum j Q F‖ ≤ 1 := by
  have hprod (c : SupportedCube j (Q : Set A)) :
      ‖mixedCubeProduct F c.val.1 c.val.2‖ ≤ 1 := by
    simp only [mixedCubeProduct, norm_prod, conjugationPower_norm]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun ω _ => hF ω _ (c.property ω))
  have hsum : ‖supportedCubeSum j (Q : Set A) F‖ ≤
      (Nat.card (SupportedCube j (Q : Set A)) : ℝ) := by
    apply (norm_sum_le _ _).trans
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card] using Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hprod c)
  rw [normalizedSupportedCubeSum, norm_div, Complex.norm_natCast]
  by_cases hc : Nat.card (SupportedCube j (Q : Set A)) = 0
  · simp only [hc, Nat.cast_zero, div_zero, zero_le_one]
  · have hpos : (0 : ℝ) < Nat.card (SupportedCube j (Q : Set A)) := by
      exact_mod_cast Nat.pos_of_ne_zero hc
    exact (div_le_iff₀ hpos).mpr (by simpa only [one_mul] using hsum)

theorem finiteSupportGowersNorm_le_one_of_embedding
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype B] [DecidableEq B]
    {φ : A →+ B} {Q : Finset A} (hφ : ReflectsPairSums φ (Q : Set A))
    (j : ℕ) (f : A → ℂ) (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) :
    finiteSupportGowersNorm (j + 1) Q f ≤ 1 := by
  apply le_of_pow_le_pow_left₀ (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) zero_le_one
  rw [one_pow, ← normalizedSupportedCubeSum_self_re hφ]
  exact (Complex.re_le_norm _).trans
    (normalizedSupportedCubeSum_norm_le_one (j + 1) Q (fun _ => f) (fun _ => hf))

theorem normalizedSupportedCubeSum_le_vertex
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype B] [DecidableEq B]
    {φ : A →+ B} {Q : Finset A} (hφ : ReflectsPairSums φ (Q : Set A))
    (j : ℕ) (F : (Fin (j + 1) → Bool) → A → ℂ)
    (hF : ∀ ω x, x ∈ Q → ‖F ω x‖ ≤ 1) (ω₀ : Fin (j + 1) → Bool) :
    ‖normalizedSupportedCubeSum (j + 1) Q F‖ ≤ finiteSupportGowersNorm (j + 1) Q (F ω₀) := by
  have hnonneg (ω) : 0 ≤ finiteSupportGowersNorm (j + 1) Q (F ω) := by
    rw [finiteSupportGowersNorm_eq_restricted hφ]
    exact restrictedGowersNorm_nonneg _ _ _
  have hprod : (∏ ω, finiteSupportGowersNorm (j + 1) Q (F ω)) ≤
      ∏ ω, if ω = ω₀ then finiteSupportGowersNorm (j + 1) Q (F ω₀) else 1 := by
    apply Finset.prod_le_prod₀ (fun ω _ => hnonneg ω)
    intro ω _
    split_ifs with h
    · subst ω; exact le_rfl
    · exact finiteSupportGowersNorm_le_one_of_embedding hφ j (F ω) (hF ω)
  have hcs : ‖normalizedSupportedCubeSum (j + 1) Q F‖ ≤
      ∏ ω, finiteSupportGowersNorm (j + 1) Q (F ω) := by
    simpa only [normalizedSupportedCubeSum, norm_div, Complex.norm_natCast] using
      norm_supportedCubeSum_le_of_embedding hφ j F
  exact hcs.trans (by simpa using hprod)

end Erdos3

end

end OAI
