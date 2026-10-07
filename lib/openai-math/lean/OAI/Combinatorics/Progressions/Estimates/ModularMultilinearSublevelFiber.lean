import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem zmod_affine_zero_card_le_gcd (N : ℕ) [NeZero N] (c d : ZMod N) :
    (Finset.univ.filter fun x : ZMod N => c * x + d = 0).card ≤ Nat.gcd c.val N := by
  by_cases h : ∃ y : ZMod N, c * y + d = 0
  · obtain ⟨y, hy⟩ := h
    let f : {x : ZMod N // c * x + d = 0} →
        (nsmulAddMonoidHom c.val : ZMod N →+ ZMod N).ker := fun x =>
      ⟨x.val - y, by
        change c.val • (x.val - y) = 0
        rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_sub]
        have hx := x.property
        linear_combination hx - hy⟩
    have hf : Function.Injective f := by
      intro x z hxz
      apply Subtype.ext
      have he := congrArg Subtype.val hxz
      change x.val - y = z.val - y at he
      exact sub_left_injective he
    have hc := Nat.card_le_card_of_injective f hf
    rw [IsAddCyclic.card_nsmulAddMonoidHom_ker] at hc
    simp only [Nat.card_eq_fintype_card, ZMod.card, Nat.gcd_comm N c.val] at hc
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hc
  · have he : (Finset.univ.filter fun x : ZMod N => c * x + d = 0) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact h ⟨x, (Finset.mem_filter.mp hx).2⟩
    rw [he, Finset.card_empty]
    exact Nat.zero_le _

theorem zmod_mul_zero_card_eq_gcd (N : ℕ) [NeZero N] (c : ZMod N) :
    (Finset.univ.filter fun x : ZMod N => c * x = 0).card = Nat.gcd c.val N := by
  have hk := IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod N) c.val
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype, nsmul_eq_mul,
    ZMod.card, Nat.gcd_comm] using hk

theorem zmod_mul_zero_expect_eq_gcd (N : ℕ) [NeZero N] (c : ZMod N) :
    (𝔼 x : ZMod N, if c * x = 0 then (1 : ℝ) else 0) =
      (Nat.gcd c.val N : ℝ) / N := by
  rw [Fintype.expect_eq_sum_div_card, ZMod.card]
  have hsum : (∑ x : ZMod N, if c * x = 0 then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun x : ZMod N => c * x = 0).card : ℝ) := by simp
  rw [hsum, zmod_mul_zero_card_eq_gcd]

theorem zmod_affine_zero_expect_le_gcd (N : ℕ) [NeZero N] (c d : ZMod N) :
    (𝔼 x : ZMod N, if c * x + d = 0 then (1 : ℝ) else 0) ≤
      (Nat.gcd c.val N : ℝ) / N := by
  rw [Fintype.expect_eq_sum_div_card, ZMod.card]
  have hsum : (∑ x : ZMod N, if c * x + d = 0 then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun x : ZMod N => c * x + d = 0).card : ℝ) := by simp
  rw [hsum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast zmod_affine_zero_card_le_gcd N c d

theorem zmod_affine_zero_conditional_expect_le_gcd {Ω : Type*} [Fintype Ω]
    (N : ℕ) [NeZero N] (c d : Ω → ZMod N) :
    (𝔼 y : Ω, 𝔼 x : ZMod N, if c y * x + d y = 0 then (1 : ℝ) else 0) ≤
      𝔼 y : Ω, (Nat.gcd (c y).val N : ℝ) / N := by
  apply Finset.expect_le_expect
  intro y _
  exact zmod_affine_zero_expect_le_gcd N (c y) (d y)

theorem zmod_gcd_expect_eq_mul_zero_expect {Ω : Type*} [Fintype Ω]
    (N : ℕ) [NeZero N] (c : Ω → ZMod N) :
    (𝔼 y : Ω, (Nat.gcd (c y).val N : ℝ) / N) =
      𝔼 y : Ω, 𝔼 x : ZMod N, if c y * x = 0 then (1 : ℝ) else 0 := by
  apply Finset.expect_congr rfl
  intro y _
  exact (zmod_mul_zero_expect_eq_gcd N (c y)).symm

theorem zmod_prime_power_affine_zero_card_le {p a b : ℕ} [NeZero p] (hp : p.Prime)
    (c d : ZMod (p ^ a)) (hc : ¬p ^ b ∣ c.val) :
    (Finset.univ.filter fun x : ZMod (p ^ a) => c * x + d = 0).card ≤ p ^ (b - 1) := by
  refine (zmod_affine_zero_card_le_gcd (p ^ a) c d).trans ?_
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right c.val (p ^ a))
  have hjb : j < b := by
    by_contra hn
    have hbj : b ≤ j := by omega
    exact hc ((pow_dvd_pow p hbj).trans (hj ▸ Nat.gcd_dvd_left c.val (p ^ a)))
  rw [hj]
  exact Nat.pow_le_pow_right hp.pos (by omega)

theorem zmod_prime_power_affine_zero_expect_le {p a b : ℕ} [NeZero p]
    (hp : p.Prime) (hba : b ≤ a) (c d : ZMod (p ^ a))
    (hc : ZMod.castHom (pow_dvd_pow p hba) (ZMod (p ^ b)) c ≠ 0) :
    (𝔼 x : ZMod (p ^ a), if c * x + d = 0 then (1 : ℝ) else 0) ≤
      (p : ℝ) ^ (b - 1) / (p : ℝ) ^ a := by
  have hc' : ¬p ^ b ∣ c.val := by
    intro hd
    apply hc
    rw [← ZMod.natCast_zmod_val c, map_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have hcard := zmod_prime_power_affine_zero_card_le hp c d hc'
  rw [Fintype.expect_eq_sum_div_card, ZMod.card]
  have hsum : (∑ x : ZMod (p ^ a), if c * x + d = 0 then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun x : ZMod (p ^ a) => c * x + d = 0).card : ℝ) := by
    simp
  rw [hsum, Nat.cast_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast hcard

theorem zmod_prime_power_affine_zero_expect_le_rpow {p a b : ℕ} [NeZero p]
    (hp : p.Prime) (hb : 1 ≤ b) (hba : b ≤ a) (c d : ZMod (p ^ a))
    (hc : ZMod.castHom (pow_dvd_pow p hba) (ZMod (p ^ b)) c ≠ 0) :
    (𝔼 x : ZMod (p ^ a), if c * x + d = 0 then (1 : ℝ) else 0) ≤
      (p : ℝ) ^ ((b : ℝ) - 1 - a) := by
  have hr : (p : ℝ) ^ ((b : ℝ) - 1 - a) =
      (p : ℝ) ^ (b - 1) / (p : ℝ) ^ a := by
    have he : (b : ℝ) - 1 = ((b - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hb, Nat.cast_one]
    rw [Real.rpow_sub (by exact_mod_cast hp.pos), he,
      Real.rpow_natCast, Real.rpow_natCast]
  rw [hr]
  exact zmod_prime_power_affine_zero_expect_le hp hba c d hc

end Erdos3

end

end OAI
