/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.Combinatorics.Progressions.Estimates.ModularTagGap

namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem modularTagGap_exponent {s a d B n : ℕ} (hn : n < s)
    (ha : a ≤ (2 ^ s * s.factorial) * d) (hd : d ≤ 2 * B)
    {C : ℝ} (hC : 0 ≤ C) :
    (C / ((2 ^ s * s.factorial : ℕ) : ℝ) / (2 ^ s : ℕ)) * a ≤
      C * B / (2 ^ n : ℕ) := by
  let D := 2 ^ s * s.factorial
  have hD : (0 : ℝ) < D := by dsimp only [D]; positivity
  have hpow : 2 * 2 ^ n ≤ 2 ^ s := by
    rw [mul_comm, ← pow_succ]
    exact Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt hn)
  have hprod : a * 2 ^ n ≤ D * B * 2 ^ s := by
    calc
      _ ≤ (D * (2 * B)) * 2 ^ n :=
        Nat.mul_le_mul_right _ (ha.trans (Nat.mul_le_mul_left _ hd))
      _ = D * B * (2 * 2 ^ n) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hpow
  have hprodR : (a : ℝ) * (2 ^ n : ℕ) ≤ (D : ℝ) * B * (2 ^ s : ℕ) := by
    exact_mod_cast hprod
  have hn0 : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  have hs0 : (0 : ℝ) < (2 ^ s : ℕ) := by positivity
  change (C / (D : ℝ) / (2 ^ s : ℕ)) * a ≤ _
  rw [div_div, div_mul_eq_mul_div, div_le_div_iff₀ (mul_pos hD hs0) hn0]
  calc
    _ = C * ((a : ℝ) * (2 ^ n : ℕ)) := by ring
    _ ≤ C * ((D : ℝ) * B * (2 ^ s : ℕ)) := mul_le_mul_of_nonneg_left hprodR hC
    _ = _ := by ring

theorem exists_modular_uncharged_decay_parameters {s : ℕ} (hs : 0 < s)
    (depth : Fin s → ℕ) (a b e : ℕ)
    (hmax : ∀ i, depth i ≤ a) (hattained : ∃ i, depth i = a)
    (hlarge : 4 * s * (2 ^ s * s.factorial) * (b + e) < a)
    (p C : ℝ) (hp : 1 ≤ p) (hC : 0 ≤ C) :
    ∃ (h : Fin s) (k B : ℕ),
      e ≤ k ∧ (∀ j : Fin s, h.val < j.val → depth j ≤ k) ∧
      B = depth h - (h.val + 1) * k ∧ b < B ∧ B ≤ a - k ∧
      p ^ (-C * B / (2 ^ h.val : ℕ)) ≤
        p ^ (-(C / ((2 ^ s * s.factorial : ℕ) : ℝ) / (2 ^ s : ℕ)) * a) := by
  obtain ⟨h, k, B, ha, he, hj, _, hB, hd, hb, hBa⟩ :=
    exists_modular_uncharged_depth hs depth a b e hmax hattained hlarge
  refine ⟨h, k, B, he, hj, hB, hb, hBa, ?_⟩
  apply Real.rpow_le_rpow_of_exponent_le hp
  have hexp := modularTagGap_exponent h.isLt ha hd.le hC
  simpa only [neg_mul, neg_div] using neg_le_neg hexp

theorem modular_local_decay_budget {p P K charge a x : ℝ}
    (hp : 1 ≤ p) (hP : 0 ≤ P) (hK : 0 ≤ K) (hcharge : 0 ≤ charge)
    (hx : x ≤ 1) (hlarge : K * charge < a → x ≤ p ^ (-P * a)) :
    x ≤ p ^ (P * K * charge) * p ^ (-P * a) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  by_cases ha : K * charge < a
  · apply (hlarge ha).trans
    have hfactor : 1 ≤ p ^ (P * K * charge) := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hp
        (show (0 : ℝ) ≤ P * K * charge by positivity)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor
      (Real.rpow_nonneg hp0.le (-P * a))
  · apply hx.trans
    rw [← Real.rpow_add hp0]
    have hnonneg : 0 ≤ P * K * charge + -P * a := by
      have := mul_le_mul_of_nonneg_left (le_of_not_gt ha) hP
      nlinarith
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hp hnonneg

theorem modular_prod_rpow {ι : Type*} (S : Finset ι) (v : ι → ℝ)
    (hv : ∀ i ∈ S, 0 ≤ v i) (P : ℝ) :
    (∏ i ∈ S, v i ^ P) = (∏ i ∈ S, v i) ^ P := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Real.mul_rpow
      (hv i (Finset.mem_insert_self _ _))
      (Finset.prod_nonneg (fun j hj => hv j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hv j (Finset.mem_insert_of_mem hj))]

theorem modular_product_decay_budget {ι : Type*} (S : Finset ι)
    (c q : ι → ℝ) (z : ι → ℂ) (P₁ P : ℝ)
    (hc : ∀ i ∈ S, 0 ≤ c i) (hq : ∀ i ∈ S, 0 ≤ q i)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ c i ^ P₁ * q i ^ (-P)) :
    ‖∏ i ∈ S, z i‖ ≤ (∏ i ∈ S, c i) ^ P₁ * (∏ i ∈ S, q i) ^ (-P) := by
  rw [norm_prod]
  calc
    _ ≤ ∏ i ∈ S, (c i ^ P₁ * q i ^ (-P)) :=
      Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) hz
    _ = _ := by
      rw [Finset.prod_mul_distrib, modular_prod_rpow S c hc, modular_prod_rpow S q hq]

end Erdos3

end

end OAI
