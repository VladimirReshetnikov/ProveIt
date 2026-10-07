import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.Combinatorics.Progressions.Dynamics.ReplacementCellPotential

namespace OAI

section

namespace Erdos3

theorem affine_recurrence_le {f : ℕ → ℝ} {q B : ℝ} (hq : 1 < q) (hB : 0 ≤ B)
    (hstep : ∀ n, f (n + 1) ≤ q * f n + B) (n : ℕ) :
    f n ≤ q ^ n * (f 0 + B / (q - 1)) := by
  have hq0 : 0 ≤ q := by linarith
  have hden : q - 1 ≠ 0 := by linarith
  have hoff : B + B / (q - 1) = q * (B / (q - 1)) := by
    field_simp
    ring
  have h : f n + B / (q - 1) ≤ q ^ n * (f 0 + B / (q - 1)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        f (n + 1) + B / (q - 1) ≤ q * f n + B + B / (q - 1) :=
          add_le_add (hstep n) le_rfl
        _ = q * (f n + B / (q - 1)) := by rw [add_assoc, hoff, mul_add]
        _ ≤ q * (q ^ n * (f 0 + B / (q - 1))) :=
          mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ (n + 1) * (f 0 + B / (q - 1)) := by rw [pow_succ]; ring
  exact (le_add_of_nonneg_right (div_nonneg hB (by linarith))).trans h

theorem log_rank_step {R R' C q : ℝ} (hR : 1 ≤ R) (hR' : 0 < R')
    (hC : 0 < C) (hq : 0 ≤ q) (hstep : R' ≤ C * (1 + R) ^ q) :
    Real.log R' ≤ q * Real.log R + (Real.log C + q * Real.log 2) := by
  have hR0 : 0 < R := by linarith
  have hbase : 0 < 1 + R := by linarith
  have hlog := Real.log_le_log hR' hstep
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hbase q).ne', Real.log_rpow hbase] at hlog
  have hsum : Real.log (1 + R) ≤ Real.log 2 + Real.log R := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hR0.ne']
    apply Real.log_le_log hbase
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hq
  linarith

theorem log_rank_recurrence_le {R : ℕ → ℝ} {C q : ℝ}
    (hR : ∀ n, 1 ≤ R n) (hC : 1 ≤ C) (hq : 1 < q)
    (hstep : ∀ n, R (n + 1) ≤ C * (1 + R n) ^ q) (n : ℕ) :
    Real.log (R n) ≤ q ^ n *
      (Real.log (R 0) + (Real.log C + q * Real.log 2) / (q - 1)) := by
  apply affine_recurrence_le (f := fun n => Real.log (R n)) hq _ _ n
  · exact add_nonneg (Real.log_nonneg hC)
      (mul_nonneg (by linarith) (Real.log_nonneg (by norm_num)))
  · intro n
    exact log_rank_step (hR n) (by linarith [hR (n + 1)]) (by linarith)
      (by linarith) (hstep n)

theorem log_rank_at_selected_level {R : ℕ → ℝ} {C q K p : ℝ}
    (hR : ∀ n, 1 ≤ R n) (hC : 1 ≤ C) (hq : 1 < q)
    (hK : 1 < K) (hp : 1 ≤ p)
    (hstep : ∀ n, R (n + 1) ≤ C * (1 + R n) ^ q) :
    Real.log (R ⌊levelCoefficient K * Real.log p⌋₊) ≤
      p ^ (levelCoefficient K * Real.log q) *
        (Real.log (R 0) + (Real.log C + q * Real.log 2) / (q - 1)) := by
  apply (log_rank_recurrence_le hR hC hq hstep _).trans
  apply mul_le_mul_of_nonneg_right
    (pow_floor_log_le hq hp (levelCoefficient_pos hK).le)
  exact add_nonneg (Real.log_nonneg (hR 0))
    (div_nonneg (add_nonneg (Real.log_nonneg hC)
      (mul_nonneg (by linarith) (Real.log_nonneg (by norm_num)))) (by linarith))

theorem subquadratic_rank_exponents {K q : ℝ} (hK : 2 ≤ K)
    (hq : 1 ≤ q) (hq2 : q < 2) :
    let t := levelCoefficient K
    let ν := gainExponent K
    let μ := t * Real.log q
    let β := 1 - (ν - μ) / 2
    0 < t ∧ 0 < ν ∧ 0 ≤ μ ∧ μ < ν ∧ 1 / 4 < β ∧ β < 1 ∧ μ < β + ν - 1 := by
  dsimp only
  have ht := levelCoefficient_pos (show 1 < K by linarith)
  obtain ⟨hν, hνq⟩ := gainExponent_pos_le_quarter hK
  have hμ : 0 ≤ levelCoefficient K * Real.log q :=
    mul_nonneg ht.le (Real.log_nonneg hq)
  have hμν : levelCoefficient K * Real.log q < gainExponent K := by
    exact mul_lt_mul_of_pos_left
      (Real.log_lt_log (by linarith : 0 < q) hq2) ht
  refine ⟨ht, hν, hμ, hμν, ?_, ?_, ?_⟩ <;> linarith

theorem density_invariant_with_general_loss {p p' L L' A C₀ loss β ν c : ℝ}
    (hp : 0 < p) (hp' : 0 ≤ p') (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hA : 0 ≤ A)
    (hinvariant : A * p ^ β + C₀ ≤ L)
    (hdrop : p' ≤ p - c * p ^ ν)
    (hlength : L - loss ≤ L')
    (hpayment : loss ≤ A * (β * c * p ^ (β + ν - 1))) :
    A * p' ^ β + C₀ ≤ L' := by
  have hpotential := mul_le_mul_of_nonneg_left
    (concave_power_drop hp hp' hβ0 hβ1 hdrop) hA
  linarith

end Erdos3

end

section

namespace Erdos3

theorem log_one_add_rank_recurrence {R : ℕ → ℝ} {C q : ℝ}
    (hR : ∀ n, 0 ≤ R n) (hC : 0 ≤ C) (hq : 1 < q)
    (hstep : ∀ n, R (n + 1) ≤ C * (1 + R n) ^ q) (n : ℕ) :
    Real.log (1 + R n) ≤ q ^ n * (Real.log (1 + R 0) + Real.log (C + 1) / (q - 1)) := by
  apply affine_recurrence_le (f := fun j => Real.log (1 + R j)) hq
    (Real.log_nonneg (by linarith)) _ n
  intro j
  have hbase : 0 < 1 + R j := by linarith [hR j]
  have hpow : 1 ≤ (1 + R j) ^ q := Real.one_le_rpow (by linarith [hR j]) (by linarith)
  have hbound : 1 + R (j + 1) ≤ (C + 1) * (1 + R j) ^ q := by
    nlinarith [hstep j]
  have hl := Real.log_le_log (by linarith [hR (j + 1)]) hbound
  rw [Real.log_mul (by linarith) (by positivity), Real.log_rpow hbase] at hl
  linarith

theorem log_one_add_rank_at_selected_level {R : ℕ → ℝ} {C q K p : ℝ}
    (hR : ∀ n, 0 ≤ R n) (hC : 0 ≤ C) (hq : 1 < q) (hK : 1 < K) (hp : 1 ≤ p)
    (hstep : ∀ n, R (n + 1) ≤ C * (1 + R n) ^ q) :
    Real.log (1 + R ⌊levelCoefficient K * Real.log p⌋₊) ≤
      p ^ (levelCoefficient K * Real.log q) *
        (Real.log (1 + R 0) + Real.log (C + 1) / (q - 1)) := by
  apply (log_one_add_rank_recurrence hR hC hq hstep _).trans
  apply mul_le_mul_of_nonneg_right (pow_floor_log_le hq hp (levelCoefficient_pos hK).le)
  exact add_nonneg (Real.log_nonneg (by linarith [hR 0]))
    (div_nonneg (Real.log_nonneg (by linarith)) (by linarith))

end Erdos3

end

section

namespace Erdos3

open Filter

theorem eventually_rpow_log_le {μ δ A B : ℝ}
    (hgap : μ < δ) (hA : 0 < A) (hB : 0 < B) :
    ∀ᶠ p : ℝ in atTop, B * p ^ μ * Real.log (2 + p) ≤ A * p ^ δ := by
  have heps : 0 < A / (2 * B) := div_pos hA (by positivity)
  have hsmall := (isLittleO_log_rpow_atTop (sub_pos.mpr hgap)).bound heps
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with p hsmall hp
  have hp0 : 0 < p := by linarith
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hpow0 : 0 ≤ p ^ (δ - μ) := Real.rpow_nonneg hp0.le _
  simp only [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hpow0] at hsmall
  have hlog : Real.log (2 + p) ≤ 2 * Real.log p := by
    rw [show 2 * Real.log p = Real.log (p * p) by rw [Real.log_mul hp0.ne' hp0.ne']; ring]
    apply Real.log_le_log (by linarith)
    nlinarith
  have hco : 0 ≤ B * p ^ μ := mul_nonneg hB.le (Real.rpow_nonneg hp0.le _)
  calc
    B * p ^ μ * Real.log (2 + p) ≤ B * p ^ μ * (2 * Real.log p) :=
      mul_le_mul_of_nonneg_left hlog hco
    _ = (2 * B * p ^ μ) * Real.log p := by ring
    _ ≤ (2 * B * p ^ μ) * (A / (2 * B) * p ^ (δ - μ)) :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = A * p ^ δ := by
      have hpow : p ^ μ * p ^ (δ - μ) = p ^ δ := by
        rw [← Real.rpow_add hp0]
        congr 1
        ring
      calc
        _ = A * (p ^ μ * p ^ (δ - μ)) := by field_simp
        _ = _ := by rw [hpow]

theorem eventually_subquadratic_rank_loss_paid {K q A c B : ℝ}
    (hK : 2 ≤ K) (hq : 1 ≤ q) (hq2 : q < 2)
    (hA : 0 < A) (hc : 0 < c) (hB : 0 < B) :
    let μ := levelCoefficient K * Real.log q
    let ν := gainExponent K
    let β := 1 - (ν - μ) / 2
    ∀ᶠ p : ℝ in atTop,
      B * p ^ μ * Real.log (2 + p) ≤ A * (β * c * p ^ (β + ν - 1)) := by
  dsimp only
  obtain ⟨_, _, _, _, hβ, _, hgap⟩ := subquadratic_rank_exponents hK hq hq2
  have hcoef : 0 < A * ((1 - (gainExponent K - levelCoefficient K * Real.log q) / 2) * c) :=
    mul_pos hA (mul_pos (by linarith) hc)
  simpa only [mul_assoc] using eventually_rpow_log_le hgap hcoef hB

end Erdos3

end

end OAI
