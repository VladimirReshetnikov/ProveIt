import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem preparedFreezingRadiusBudget_of_terms {m D : ℕ} {Lip gain δ : ℝ}
    (term : Fin m → ℝ) (hLip : 0 ≤ Lip) (hgain : 0 < gain) (hgain1 : gain ≤ 1)
    (hterm : ∀ j, term j ≤ gain / (128 * ((D : ℝ) + 1) * (Lip + 1) * ((m : ℝ) + 1)))
    (hδ : δ ≤ gain / (128 * ((D : ℝ) + 1) * (Lip + 1))) :
    (D : ℝ) * 2 * ((∑ j, term j) + δ) < 1 / 12 ∧
      Lip * ((D : ℝ) * 2 * ((∑ j, term j) + δ)) ≤ gain / 16 := by
  let b := gain / (128 * ((D : ℝ) + 1) * (Lip + 1))
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hsum : (∑ j, term j) ≤ b := by
    calc
      _ ≤ ∑ _j : Fin m, gain / (128 * ((D : ℝ) + 1) * (Lip + 1) * ((m : ℝ) + 1)) :=
        Finset.sum_le_sum (fun j _ => hterm j)
      _ = (m : ℝ) * (b / ((m : ℝ) + 1)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, b, div_div]
      _ ≤ ((m : ℝ) + 1) * (b / ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hb (by positivity))
      _ = b := by field_simp
  have hoscb : (D : ℝ) * 2 * ((∑ j, term j) + δ) ≤ gain / (32 * (Lip + 1)) := by
    calc
      _ ≤ (D : ℝ) * 2 * (b + b) :=
        mul_le_mul_of_nonneg_left (add_le_add hsum hδ) (by positivity)
      _ = 4 * (D : ℝ) * b := by ring
      _ ≤ 4 * ((D : ℝ) + 1) * b := mul_le_mul_of_nonneg_right (by linarith) hb
      _ = gain / (32 * (Lip + 1)) := by
        dsimp [b]
        field_simp
        ring
  have hLp : 0 < Lip + 1 := by positivity
  refine ⟨hoscb.trans_lt ?_, (mul_le_mul_of_nonneg_left hoscb hLip).trans ?_⟩
  · apply (div_lt_iff₀ (by positivity : 0 < 32 * (Lip + 1))).mpr
    nlinarith
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 32 * (Lip + 1))).mpr
    nlinarith [mul_nonneg hgain.le hLip]

theorem preparedFreezingRadiusBudget_of_inflated_chart {m D : ℕ} {Lip gain δ : ℝ}
    (N I : Fin m → ℕ) (C R : Fin m → ℝ)
    (hLip : 0 ≤ Lip) (hgain : 0 < gain) (hgain1 : gain ≤ 1)
    (hchart : ∀ j,
      ((32 * ((D : ℝ) + 1) * (Lip + 1) * ((m : ℝ) + 1) / gain) * (N j : ℝ) * C j) *
        ((I j : ℝ) + 1) * R j ≤ 1 / 4)
    (hδ : δ ≤ gain / (128 * ((D : ℝ) + 1) * (Lip + 1))) :
    (D : ℝ) * 2 * ((∑ j, (N j : ℝ) * C j * ((I j : ℝ) + 1) * R j) + δ) < 1 / 12 ∧
      Lip * ((D : ℝ) * 2 * ((∑ j, (N j : ℝ) * C j * ((I j : ℝ) + 1) * R j) + δ)) ≤ gain / 16 := by
  apply preparedFreezingRadiusBudget_of_terms _ hLip hgain hgain1 _ hδ
  intro j
  have hf : 0 < 32 * ((D : ℝ) + 1) * (Lip + 1) * ((m : ℝ) + 1) / gain := by positivity
  have hj : (32 * ((D : ℝ) + 1) * (Lip + 1) * ((m : ℝ) + 1) / gain) *
      ((N j : ℝ) * C j * ((I j : ℝ) + 1) * R j) ≤ 1 / 4 := by
    convert hchart j using 1; ring
  have h : (N j : ℝ) * C j * ((I j : ℝ) + 1) * R j ≤
      (1 / 4) / (32 * ((D : ℝ) + 1) * (Lip + 1) * ((m : ℝ) + 1) / gain) :=
    (le_div_iff₀ hf).mpr (by simpa only [mul_comm] using hj)
  refine h.trans_eq ?_
  field_simp
  ring

theorem preparedFreezingRadiusBudget_of_radius {m D maxN maxI : ℕ}
    {Lip gain δ maxC : ℝ} (N I : Fin m → ℕ) (C R : Fin m → ℝ)
    (hLip : 0 ≤ Lip) (hgain : 0 < gain) (hgain1 : gain ≤ 1) (hmaxC : 0 ≤ maxC)
    (hN : ∀ j, N j ≤ maxN) (hI : ∀ j, I j ≤ maxI)
    (hC0 : ∀ j, 0 ≤ C j) (hC : ∀ j, C j ≤ maxC) (hR0 : ∀ j, 0 ≤ R j)
    (hR : ∀ j, R j ≤ gain /
      (128 * ((D : ℝ) + 1) * (Lip + 1) * ((m : ℝ) + 1) *
        ((maxN : ℝ) + 1) * (maxC + 1) * ((maxI : ℝ) + 1)))
    (hδ : δ ≤ gain / (128 * ((D : ℝ) + 1) * (Lip + 1))) :
    (D : ℝ) * 2 * ((∑ j, (N j : ℝ) * C j * ((I j : ℝ) + 1) * R j) + δ) < 1 / 12 ∧
      Lip * ((D : ℝ) * 2 * ((∑ j, (N j : ℝ) * C j * ((I j : ℝ) + 1) * R j) + δ)) ≤ gain / 16 := by
  apply preparedFreezingRadiusBudget_of_terms _ hLip hgain hgain1 _ hδ
  intro j
  have hn : (N j : ℝ) ≤ (maxN : ℝ) + 1 := by exact_mod_cast (Nat.le_succ_of_le (hN j))
  have hc : C j ≤ maxC + 1 := by linarith [hC j]
  have hi : (I j : ℝ) + 1 ≤ (maxI : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right (hI j) 1
  have hcoeff : (N j : ℝ) * C j * ((I j : ℝ) + 1) ≤
      ((maxN : ℝ) + 1) * (maxC + 1) * ((maxI : ℝ) + 1) :=
    mul_le_mul (mul_le_mul hn hc (hC0 j) (by positivity)) hi (by positivity) (by positivity)
  calc
    _ ≤ (((maxN : ℝ) + 1) * (maxC + 1) * ((maxI : ℝ) + 1)) * R j :=
      mul_le_mul_of_nonneg_right hcoeff (hR0 j)
    _ ≤ (((maxN : ℝ) + 1) * (maxC + 1) * ((maxI : ℝ) + 1)) *
        (gain / (128 * ((D : ℝ) + 1) * (Lip + 1) * ((m : ℝ) + 1) *
          ((maxN : ℝ) + 1) * (maxC + 1) * ((maxI : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left (hR j) (by positivity)
    _ = _ := by
      have hcpos : 0 < maxC + 1 := by positivity
      field_simp

theorem preparedFreezingInflation_exp_bound {F N C gF gN gC : ℝ}
    (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hFexp : F ≤ Real.exp gF) (hNexp : N ≤ Real.exp gN) (hCexp : C ≤ Real.exp gC) :
    F * N * C ≤ Real.exp (gF + gN + gC) := by
  rw [Real.exp_add, Real.exp_add]
  exact mul_le_mul (mul_le_mul hFexp hNexp hN (Real.exp_nonneg _)) hCexp hC (by positivity)

end Erdos3

end

section

namespace Erdos3

private theorem exp_succ_bounds_add_one {x p : ℝ} (hp : 0 ≤ p)
    (hx : x ≤ Real.exp p) : x + 1 ≤ Real.exp (p + 1) := by
  have h1 : 1 ≤ Real.exp p := Real.one_le_exp hp
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [Real.exp_add]
  nlinarith [Real.exp_pos p]

theorem preparedFreezingEarlyLogBudget {D m N : ℕ} {Lip C gain δ p : ℝ}
    (hp : 0 ≤ p) (hLip : 0 ≤ Lip) (hC : 0 ≤ C)
    (hD : (D : ℝ) ≤ Real.exp p) (hm : (m : ℝ) ≤ Real.exp p)
    (hL : Lip ≤ Real.exp p) (hN : (N : ℝ) ≤ Real.exp p)
    (hCexp : C ≤ Real.exp p) (hgain : Real.exp (-p) ≤ gain)
    (hδ : δ ≤ Real.exp (-(3 * p + 130))) :
    (32 * ((D : ℝ) + 1) * (Lip + 1) * ((m : ℝ) + 1) / gain) *
      (N : ℝ) * C ≤ Real.exp (6 * p + 35) ∧
      δ ≤ gain / (128 * ((D : ℝ) + 1) * (Lip + 1)) := by
  have hgain0 : 0 < gain := (Real.exp_pos _).trans_le hgain
  have hD' := exp_succ_bounds_add_one hp hD
  have hm' := exp_succ_bounds_add_one hp hm
  have hL' := exp_succ_bounds_add_one hp hL
  have hi : gain⁻¹ ≤ Real.exp p := by
    have h := one_div_le_one_div_of_le (Real.exp_pos (-p)) hgain
    simpa only [one_div, Real.exp_neg, inv_inv] using h
  have h32 : (32 : ℝ) ≤ Real.exp 32 := by linarith [Real.add_one_le_exp (32 : ℝ)]
  have h128 : (128 : ℝ) ≤ Real.exp 128 := by linarith [Real.add_one_le_exp (128 : ℝ)]
  have hF : 32 * ((D : ℝ) + 1) * (Lip + 1) * ((m : ℝ) + 1) / gain ≤
      Real.exp (4 * p + 35) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp 32 * Real.exp (p+1) * Real.exp (p+1) * Real.exp (p+1) * Real.exp p := by
        exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h32 hD'
          (by positivity) (Real.exp_nonneg _)) hL' (by positivity) (by positivity))
          hm' (by positivity) (by positivity)) hi (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  refine ⟨?_, ?_⟩
  · have h := preparedFreezingInflation_exp_bound (Nat.cast_nonneg N) hC hF hN hCexp
    convert h using 1
    congr 1
    ring
  · have hden : (128 * ((D : ℝ) + 1) * (Lip + 1)) * gain⁻¹ ≤ Real.exp (3*p+130) := by
      calc
        _ ≤ Real.exp 128 * Real.exp (p+1) * Real.exp (p+1) * Real.exp p := by
          exact mul_le_mul (mul_le_mul (mul_le_mul h128 hD' (by positivity)
            (Real.exp_nonneg _)) hL' (by positivity) (by positivity)) hi
            (by positivity) (by positivity)
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hden0 : 0 < 128 * ((D : ℝ) + 1) * (Lip + 1) := by positivity
    apply hδ.trans
    have hinv := one_div_le_one_div_of_le (mul_pos hden0 (inv_pos.mpr hgain0)) hden
    simpa only [one_div, mul_inv_rev, inv_inv, Real.exp_neg, div_eq_mul_inv, one_mul] using hinv

end Erdos3

end

end OAI
