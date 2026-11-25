import IPRADerivations.Probability.Variance
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.LinearCombination

/-!
# The first-crossing step of Kolmogorov's maximal inequality

Packet: `probability/expected_value_ipra_2026-11-16`, `paper/sections/08_samples_lln.tex`,
Theorem `thm:kolmogorov` ("Finite Kolmogorov maximal inequality"). Its proof bounds each first-crossing
event `A_k` by `a² P(A_k) ≤ E[S_k² 1_{A_k}] ≤ E[S_n² 1_{A_k}]`, because "`A_k` depends only on the first `k`
coordinates and the tail increment is independent of them with mean zero", so the cross term
`E[S_k (S_n − S_k) 1_{A_k}]` vanishes and `E[(S_n − S_k)² 1_{A_k}] ≥ 0`.

Here the sample space is the product law of `Probability/Independence`: the past outcomes `i < M` carry the
weight `w_i` (which may include the indicator of `A_k`), the future outcomes `j < K` the weight `v_j`, with
`W = ∑ w_i` and `V = ∑ v_j`. The partial sum `S_k = P_i − N_i` and the increment `Y_j = P'_j − N'_j` are
signed, given by their natural parts, and `S_n = S_k + Y` is cleared to the natural number
`|(P_i + P'_j) − (N_i + N'_j)|` (`Probability/Variance.ad`).

* `cleared_square`: pointwise, `|a − b|² + (a + b)² = 2a² + 2b²`, which turns the signed square into three
  squares of sums of independent coordinates;
* `past_bound`: if `w_i a_i² ≤ w_i (P_i − N_i)²` for `i < M` (on the crossing event `S_k² ≥ a²`), then
  `∑ w a² + ∑ w (P + N)² ≤ 2 ∑ w P² + 2 ∑ w N²`;
* `future_bound`: `∑ v (P' + N')² ≤ 2 ∑ v P'² + 2 ∑ v N'²`;
* `crossing_step`: if moreover the increment has mean zero, `∑ v P' = ∑ v N'`, then
  `V ∑_i w_i a_i² ≤ ∑_i ∑_j w_i v_j S_n(i, j)²`, i.e. (dividing by the total weight `W_tot V`)
  `a² P(A_k) ≤ E[S_n² 1_{A_k}]`. The difference is `V ∑ w (S_k² − a²) + W ∑ v Y²`: the cross term
  `2 (∑ w S_k)(∑ v Y)` vanishes by the mean-zero hypothesis.

Summing the steps over the disjoint first-crossing events and the variance identity for `E[S_n²]` on the
`n`-fold product are not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.KolmogorovStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Expectation (Ew Wt inst2_mul' inst2_add' exp_add)
open LeanProofs.IPRA.Probability.Independence (dsum dsum_congr dsum_add pmB inst3_pmB spB inst3_spB
  inst3_mul' inst3_add' ind_sum_second)
open LeanProofs.IPRA.Probability.Variance (ad ad_sq)
open LeanProofs.IPRA.Analysis.PowerSums (sum_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem inst3_monus (a b : PTm 3) (i j x : PTm n) :
    inst3 (monus a b) i j x = monus (inst3 a i j x) (inst3 b i j x) := by
  simp [inst3]

theorem inst2_monus (a b : PTm 2) (i x : PTm n) :
    inst2 (monus a b) i x = monus (inst2 a i x) (inst2 b i x) := by
  simp [inst2]

/-- `|a − b|² + (a + b)² = 2a² + 2b²`. -/
theorem cleared_square (a b : PTm n) :
    Γ ⊢[PRAAx] ad a b * ad a b + (a + b) * (a + b) ≐ (a * a + a * a) + (b * b + b * b) := by
  ipra_lc natEq (ad_sq (Γ := Γ) a b)

variable (w v P N P' N' a : PTm 2)

/-- The cleared square `S_n² = |(P_i + P'_j) − (N_i + N'_j)|²`, weighted by `w_i v_j`. -/
abbrev Zf : PTm 3 :=
  pmB w v * ((monus (spB P P') (spB N N') + monus (spB N N') (spB P P')) *
    (monus (spB P P') (spB N N') + monus (spB N N') (spB P P')))

/-- On the crossing event, `∑ w a² + ∑ w (P + N)² ≤ 2 ∑ w P² + 2 ∑ w N²`. -/
theorem past_bound (M x : PTm n)
    (hc : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      le (inst2 w (var 0) (Syn.shift x) * (inst2 a (var 0) (Syn.shift x) * inst2 a (var 0) (Syn.shift x)))
        (inst2 w (var 0) (Syn.shift x) *
          (ad (inst2 P (var 0) (Syn.shift x)) (inst2 N (var 0) (Syn.shift x)) *
            ad (inst2 P (var 0) (Syn.shift x)) (inst2 N (var 0) (Syn.shift x)))))) :
    Γ ⊢[PRAAx] le (Ew w (a * a) M x + Ew w ((P + N) * (P + N)) M x)
      ((Ew w (P * P) M x + Ew w (P * P) M x) + (Ew w (N * N) M x + Ew w (N * N) M x)) := by
  have s := sum_le (w * (a * a + (P + N) * (P + N))) (w * ((P * P + P * P) + (N * N + N * N))) x M
    (.allI (.impI (by
      have h := Prf.impE hc.allOpen.wk Prf.hyp0
      simp only [inst2_mul', inst2_add']
      have e := natEq (ad_sq (Γ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift)
        (inst2 P (var 0) (Syn.shift x)) (inst2 N (var 0) (Syn.shift x)))
      ipra_le sl h using linear_combination (-𝔟 (inst2 w (var 0) (Syn.shift x))) * e)))
  exact le_congr (exp_add w (a * a) ((P + N) * (P + N)) M x)
    ((exp_add w (P * P + P * P) (N * N + N * N) M x).eqTrans
      (congrAdd (exp_add w (P * P) (P * P) M x) (exp_add w (N * N) (N * N) M x))) s

/-- `∑ v (P' + N')² ≤ 2 ∑ v P'² + 2 ∑ v N'²`. -/
theorem future_bound (K x : PTm n) :
    Γ ⊢[PRAAx] le (Ew v ((P' + N') * (P' + N')) K x)
      ((Ew v (P' * P') K x + Ew v (P' * P') K x) + (Ew v (N' * N') K x + Ew v (N' * N') K x)) := by
  have s := sum_le (v * ((P' + N') * (P' + N'))) (v * ((P' * P' + P' * P') + (N' * N' + N' * N'))) x K
    (.allI (.impI (by
      simp only [inst2_mul', inst2_add']
      have e := natEq (ad_sq (Γ := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift)
        (inst2 P' (var 0) (Syn.shift x)) (inst2 N' (var 0) (Syn.shift x)))
      refine le_of_eq_add (d := inst2 v (var 0) (Syn.shift x) *
        (ad (inst2 P' (var 0) (Syn.shift x)) (inst2 N' (var 0) (Syn.shift x)) *
          ad (inst2 P' (var 0) (Syn.shift x)) (inst2 N' (var 0) (Syn.shift x)))) ?_
      ipra_lc (-𝔟 (inst2 v (var 0) (Syn.shift x))) * e)))
  exact le_congr (.eqRefl _)
    ((exp_add v (P' * P' + P' * P') (N' * N' + N' * N') K x).eqTrans
      (congrAdd (exp_add v (P' * P') (P' * P') K x) (exp_add v (N' * N') (N' * N') K x))) s

/-- The first-crossing step: `V ∑_i w_i a_i² ≤ ∑_i ∑_j w_i v_j S_n(i, j)²` for a mean-zero increment. -/
theorem crossing_step (M K x : PTm n)
    (hc : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      le (inst2 w (var 0) (Syn.shift x) * (inst2 a (var 0) (Syn.shift x) * inst2 a (var 0) (Syn.shift x)))
        (inst2 w (var 0) (Syn.shift x) *
          (ad (inst2 P (var 0) (Syn.shift x)) (inst2 N (var 0) (Syn.shift x)) *
            ad (inst2 P (var 0) (Syn.shift x)) (inst2 N (var 0) (Syn.shift x))))))
    (hm : Γ ⊢[PRAAx] Ew v P' K x ≐ Ew v N' K x) :
    Γ ⊢[PRAAx] le (Wt v K x * Ew w (a * a) M x) (dsum (Zf w v P N P' N') M K x) := by
  have C := natEq (dsum_congr (Γ := Γ)
    (Zf w v P N P' N' + pmB w v * (spB (P + N) (P' + N') * spB (P + N) (P' + N')))
    ((pmB w v * (spB P P' * spB P P') + pmB w v * (spB P P' * spB P P')) +
      (pmB w v * (spB N N' * spB N N') + pmB w v * (spB N N' * spB N N')))
    (fun {m} {Δ} i j x => by
      ipra_lc [inst3_add', inst3_mul', inst3_pmB, inst3_spB, inst3_monus, inst2_add'] (𝔟 (inst2 w i x) * 𝔟 (inst2 v j x)) * natEq (cleared_square (Γ := Δ) (inst2 P i x + inst2 P' j x) (inst2 N i x + inst2 N' j x))) M K x)
  have d₁ := natEq (dsum_add (Γ := Γ) (Zf w v P N P' N')
    (pmB w v * (spB (P + N) (P' + N') * spB (P + N) (P' + N'))) M K x)
  have d₂ := natEq (dsum_add (Γ := Γ)
    (pmB w v * (spB P P' * spB P P') + pmB w v * (spB P P' * spB P P'))
    (pmB w v * (spB N N' * spB N N') + pmB w v * (spB N N' * spB N N')) M K x)
  have d₃ := natEq (dsum_add (Γ := Γ) (pmB w v * (spB P P' * spB P P')) (pmB w v * (spB P P' * spB P P')) M K x)
  have d₄ := natEq (dsum_add (Γ := Γ) (pmB w v * (spB N N' * spB N N')) (pmB w v * (spB N N' * spB N N')) M K x)
  have sP := natEq (ind_sum_second (Γ := Γ) (w := w) (X := P) (v := v) (Y := P') M K x)
  have sN := natEq (ind_sum_second (Γ := Γ) (w := w) (X := N) (v := v) (Y := N') M K x)
  have sA := natEq (ind_sum_second (Γ := Γ) (w := w) (X := P + N) (v := v) (Y := P' + N') M K x)
  have eA := natEq (exp_add (Γ := Γ) w P N M x)
  have eA' := natEq (exp_add (Γ := Γ) v P' N' K x)
  have em := natEq hm
  have hp := past_bound w P N a M x hc
  have hf := future_bound v P' N' K x (Γ := Γ)
  ipra_le 𝔟 (Wt v K x) * sl hp + 𝔟 (Wt w M x) * sl hf using
    linear_combination -d₁ + C + d₂ + d₃ + d₄ + 2 * sP + 2 * sN - sA
      - 2 * 𝔟 (Ew v (P' + N') K x) * eA - 2 * (𝔟 (Ew w P M x) + 𝔟 (Ew w N M x)) * eA'
      + 2 * (𝔟 (Ew w P M x) - 𝔟 (Ew w N M x)) * em

end LeanProofs.IPRA.Probability.KolmogorovStep
