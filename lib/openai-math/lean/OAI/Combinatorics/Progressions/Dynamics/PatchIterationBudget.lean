import OAI.Combinatorics.Progressions.Linear.SubquadraticRankPayment
import OAI.Combinatorics.Progressions.Polynomial.PolynomialProductReset

namespace OAI

section

namespace Erdos3

theorem exists_reset_scale_of_log_bound {Q N : ℕ} (hQ : 0 < Q)
    {B : ℝ} (hB : 1 ≤ B)
    (hsize : 2 * (Q : ℝ) * Real.log (2 * B) ≤ Real.log N) :
    1 < N ∧ ∃ T : ℕ, 0 < T ∧ B ≤ T ∧ T ^ Q ≤ N ∧
      Real.exp (Real.log N / (2 * Q)) ≤ T := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hB0 : 0 < 2 * B := by linarith
  have hlogB : 0 < Real.log (2 * B) := Real.log_pos (by linarith)
  have hlogN : 0 < Real.log N := (mul_pos (by positivity) hlogB).trans_le hsize
  have hN1 : (1 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp hlogN
  have hN0 : (0 : ℝ) < N := by linarith
  let x := Real.log N / (2 * Q)
  let Y := Real.exp x
  have hBY : 2 * B ≤ Y := by
    apply (Real.log_le_iff_le_exp hB0).mp
    exact (le_div_iff₀ (by positivity)).mpr (by nlinarith [hsize])
  have hY2 : 2 ≤ Y := by linarith
  let T := ⌈Y⌉₊
  have hYT : Y ≤ (T : ℝ) := Nat.le_ceil Y
  have hT0 : 0 < T := by exact_mod_cast (show (0 : ℝ) < T by linarith)
  have hTY : (T : ℝ) ≤ Y ^ 2 := by
    have hc : (T : ℝ) < Y + 1 := Nat.ceil_lt_add_one (by linarith)
    nlinarith
  have hpower : (Y ^ 2) ^ Q = (N : ℝ) := by
    dsimp only [Y]
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    have heq : (Q : ℝ) * ((2 : ℕ) * x) = Real.log N := by
      dsimp [x]
      field_simp
    rw [heq, Real.exp_log hN0]
  have hTN : T ^ Q ≤ N := by
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) T) hTY Q
    rw [hpower] at hp
    exact_mod_cast hp
  exact ⟨by exact_mod_cast hN1, T, hT0, by linarith, hTN, hYT⟩

theorem log_log_length_loss {N M : ℕ} {Q : ℝ}
    (hN : 1 < N) (hQ : 0 < Q)
    (hM : Real.exp (Real.log N / Q) ≤ M) :
    1 < M ∧ Real.log (Real.log N) - Real.log Q ≤ Real.log (Real.log M) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have hx : 0 < Real.log N / Q := div_pos hlogN hQ
  have hM1 : (1 : ℝ) < M := (Real.one_lt_exp_iff.mpr hx).trans_le hM
  have hlogM : Real.log N / Q ≤ Real.log M :=
    (Real.le_log_iff_exp_le (by linarith)).mpr hM
  have h := Real.log_le_log hx hlogM
  rw [Real.log_div hlogN.ne' hQ.ne'] at h
  exact ⟨by exact_mod_cast hM1, h⟩

end Erdos3

end

section

namespace Erdos3

theorem log_patch_reset_cost_le {C L σ U : ℝ} (hC : 0 < C) (hL : 0 ≤ L)
    (hσ : 0 < σ) (hLip : L + 1 ≤ Real.exp U) (hscore : Real.exp (-U) ≤ σ)
    (d : ℕ) :
    Real.log (2 * C * ((d : ℝ) + 1) * (L + 1) / σ) ≤
      Real.log (2 * C) + Real.log ((d : ℝ) + 1) + 2 * U := by
  have hLp : 0 < L + 1 := by linarith
  have hd : (0 : ℝ) < d + 1 := by positivity
  have hlogL : Real.log (L + 1) ≤ U := (Real.log_le_iff_le_exp hLp).mpr hLip
  have hlogσ : -U ≤ Real.log σ := (Real.le_log_iff_exp_le hσ).mpr hscore
  rw [Real.log_div (by positivity) hσ.ne',
    Real.log_mul (by positivity) hLp.ne', Real.log_mul (by positivity) hd.ne']
  linarith

theorem slice_reset_log_room {Q C U : ℝ} {d N M : ℕ}
    (hQ : 1 ≤ Q) (hC : 1 ≤ C) (hU : 1 ≤ U)
    (hslice : Real.log N - U ≤ Real.log M)
    (hsize : 4 * Q * (Real.log (2 * C) + Real.log ((d : ℝ) + 1) + 2 * U) ≤ Real.log N) :
    1 < N ∧ Real.log N / 2 ≤ Real.log M ∧
      2 * Q * (Real.log (2 * C) + Real.log ((d : ℝ) + 1) + 2 * U) ≤ Real.log M := by
  have hlogC : 0 ≤ Real.log (2 * C) := Real.log_nonneg (by linarith)
  have hlogd : 0 ≤ Real.log ((d : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
  have hlogN : 2 * U ≤ Real.log N := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ Q) (add_nonneg hlogC hlogd)]
  have hN : (1 : ℝ) < N :=
    (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith)
  refine ⟨by exact_mod_cast hN, by linarith, ?_⟩
  linarith

end Erdos3

end

section

namespace Erdos3

theorem patch_reset_cutoff_bound {C P U : ℝ} (hC : 1 ≤ C) (hP : 0 ≤ P)
    (hU : 1 ≤ U) (d a : ℕ) :
    4 * P * ((d : ℝ) + 1) ^ a * (Real.log (2 * C) + Real.log ((d : ℝ) + 1) + 2 * U) ≤
      (4 * P * (Real.log (2 * C) + 3)) * ((d : ℝ) + 1) ^ (a + 1) * U := by
  have hd : (1 : ℝ) ≤ d + 1 := by have := Nat.cast_nonneg (α := ℝ) d; linarith
  have hlogC : 0 ≤ Real.log (2 * C) := Real.log_nonneg (by linarith)
  have hprod : 1 ≤ ((d : ℝ) + 1) * U := one_le_mul_of_one_le_of_one_le hd hU
  have hD : (d : ℝ) + 1 ≤ ((d : ℝ) + 1) * U := le_mul_of_one_le_right (by positivity) hU
  have hU' : U ≤ ((d : ℝ) + 1) * U := le_mul_of_one_le_left (by linarith) hd
  have hlogD : Real.log ((d : ℝ) + 1) ≤ ((d : ℝ) + 1) * U :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hC' : Real.log (2 * C) ≤ Real.log (2 * C) * (((d : ℝ) + 1) * U) :=
    le_mul_of_one_le_right hlogC hprod
  have hsum : Real.log (2 * C) + Real.log ((d : ℝ) + 1) + 2 * U ≤
      (Real.log (2 * C) + 3) * ((d : ℝ) + 1) * U := by nlinarith
  calc
    _ ≤ (4 * P * ((d : ℝ) + 1) ^ a) * ((Real.log (2 * C) + 3) * ((d : ℝ) + 1) * U) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by rw [pow_succ]; ring

theorem patch_reset_cutoff_of_loglog {C P U R V : ℝ} {N : ℕ}
    (hC : 1 ≤ C) (hP : 0 < P) (hU : 1 ≤ U) (hN : 1 < N) (d a : ℕ)
    (hR : Real.log ((d : ℝ) + 1) ≤ R) (hV : Real.log U ≤ V)
    (hsize : Real.log (4 * P * (Real.log (2 * C) + 3)) + (a + 1 : ℕ) * R + V ≤
      Real.log (Real.log N)) :
    4 * P * ((d : ℝ) + 1) ^ a * (Real.log (2 * C) + Real.log ((d : ℝ) + 1) + 2 * U) ≤
      Real.log N := by
  have hlogC : 0 ≤ Real.log (2 * C) := Real.log_nonneg (by linarith)
  have hconst : 0 < 4 * P * (Real.log (2 * C) + 3) := by positivity
  have hd : (0 : ℝ) < d + 1 := by positivity
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  apply (patch_reset_cutoff_bound hC hP.le hU d a).trans
  have hlog : Real.log ((4 * P * (Real.log (2 * C) + 3)) * ((d : ℝ) + 1) ^ (a + 1) * U) ≤
      Real.log (Real.log N) := by
    rw [Real.log_mul (by positivity) (by linarith),
      Real.log_mul hconst.ne' (by positivity), Real.log_pow]
    have hr := mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg (α := ℝ) (a + 1))
    linarith
  exact (Real.log_le_log_iff (by positivity) hlogN).mp hlog

end Erdos3

end

section

namespace Erdos3

open Filter

theorem eventually_two_resource_costs_fit {μ γ β A B D : ℝ}
    (hμ : μ < β) (hγ : γ < β) (hA : 0 < A) (hB : 0 < B) (hD : 0 < D) :
    ∀ᶠ p : ℝ in atTop,
      B * p ^ μ * Real.log (2 + p) + D * p ^ γ * Real.log (2 + p) ≤ A * p ^ β := by
  have hfirst := eventually_rpow_log_le hμ (by linarith : 0 < A / 2) hB
  have hsecond := eventually_rpow_log_le hγ (by linarith : 0 < A / 2) hD
  filter_upwards [hfirst, hsecond] with p hp hq
  linarith

theorem eventually_constant_add_rank_loss_paid {μ δ A B L₀ : ℝ}
    (hμ : 0 ≤ μ) (hgap : μ < δ) (hA : 0 < A) (hB : 0 ≤ B) (hL : 0 ≤ L₀) :
    ∀ᶠ p : ℝ in atTop, L₀ + B * p ^ μ * Real.log (2 + p) ≤ A * p ^ δ := by
  have hlarge := eventually_rpow_log_le hgap hA (by linarith : 0 < B + L₀ + 1)
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (Real.exp 1)] with
    p hlarge hp he
  have hpow : 1 ≤ p ^ μ := Real.one_le_rpow hp hμ
  have hlog : 1 ≤ Real.log (2 + p) :=
    (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith)
  have hprod : 1 ≤ p ^ μ * Real.log (2 + p) := one_le_mul_of_one_le_of_one_le hpow hlog
  have hconstant := mul_le_mul_of_nonneg_left hprod hL
  nlinarith

theorem subquadratic_patch_iteration_budgets {K q A c B D L₀ : ℝ}
    (hK : 2 ≤ K) (hq : 1 ≤ q) (hq2 : q < 2) (hA : 0 < A) (hc : 0 < c)
    (hB : 0 < B) (hD : 0 < D) (hL : 0 ≤ L₀) (a : ℕ) :
    let μ := levelCoefficient K * Real.log q
    let ν := gainExponent K
    let β := 1 - (ν - μ) / 2
    ∀ᶠ p : ℝ in atTop,
      ((a + 1 : ℕ) * B * p ^ μ * Real.log (2 + p) +
        D * p ^ (1 / 4 : ℝ) * Real.log (2 + p) ≤ A * p ^ β) ∧
      (L₀ + (a : ℝ) * B * p ^ μ * Real.log (2 + p) ≤
        A * (β * c * p ^ (β + ν - 1))) := by
  dsimp only
  obtain ⟨_, _, hμ, hμν, hβ, _, hgap⟩ := subquadratic_rank_exponents hK hq hq2
  have hν4 := (gainExponent_pos_le_quarter hK).2
  have hfit := eventually_two_resource_costs_fit
    (by linarith : levelCoefficient K * Real.log q < 1 - (gainExponent K - levelCoefficient K * Real.log q) / 2)
    hβ hA (by positivity : 0 < (a + 1 : ℕ) * B) hD
  have hco : 0 < A * ((1 - (gainExponent K - levelCoefficient K * Real.log q) / 2) * c) :=
    mul_pos hA (mul_pos (by linarith) hc)
  have hpaid := eventually_constant_add_rank_loss_paid hμ hgap hco
    (by positivity : 0 ≤ (a : ℝ) * B) hL
  filter_upwards [hfit, hpaid] with p hfit hpaid
  exact ⟨hfit, by simpa only [mul_assoc] using hpaid⟩

end Erdos3

end

end OAI
