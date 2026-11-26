import IPRADerivations.AnalyticNumberTheory.ChebyshevAbel
import IPRADerivations.AnalyticNumberTheory.FloorTelescope
import IPRADerivations.AnalyticNumberTheory.SumReindex
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# `Σ log k / k = (log x)²/2 + O(1)` exactly (`pnt_ipra_constructive_2026-11-14`, `con:one-step`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, proof of `con:one-step`:
the main term `∫_0^t (t − u)|r(u)| du ≤ a t²/2 + …` of the weighted inequality. In the discrete form used here
(`WeightedAbel.weighted_sum`, a sum over `n ≤ x` of `u_n |R(x/n)|`) the corresponding main term is
`Σ_{n≤x} log n / n = (log x)²/2 + O(1)`. With the harmonic logarithm `u_k = F λ_K(k)` and its increments
`Δ_k = u_k − u_{k−1}` (`Δ_k = F(H_{Kk} − H_{K(k−1)})`, about `F/k`), this is an exact identity in ℕ plus a bounded
remainder:

* `half_square`: `2 Σ_{2≤k≤N+1} u_k Δ_k = u_{N+1}² + Σ_{2≤k≤N+1} Δ_k²` (one closed QF induction, from
  `u_{k} = u_{k−1} + Δ_k`);
* `dd_le`: `Σ_{2≤k≤N+1} Δ_k² ≤ 2F²`, since `(k−1)Δ_k ≤ F` (`ChebyshevAbel.dlt_k`) and
  `Σ_{j≥1} ⌊F²/j²⌋ ≤ 2F²` (`FloorTelescope.floor_square_sum`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.HarmonicHalfSquare

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U U_paired delta_paired U_increment)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevAbel (dlt_k)
open LeanProofs.IPRA.AnalyticNumberTheory.ComparisonEnvelope (le_mul2)
open LeanProofs.IPRA.AnalyticNumberTheory.FloorTelescope (qB inst2_qB floor_square_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (le_quo_of_mul_le)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHarmonic (shift_fact')

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `Δ_{j+2} = S(K(j+2)) − S(K(j+1))` with parameter `(K, F)`. -/
abbrev dlB : PTm 2 :=
  monus (S (fstT (var 1) * succ (succ (var 0))) (sndT (var 1))) (S (fstT (var 1) * succ (var 0)) (sndT (var 1)))
/-- `u_{j+2}`. -/
abbrev u2B : PTm 2 := monus (S (fstT (var 1) * succ (succ (var 0))) (sndT (var 1))) (S (fstT (var 1)) (sndT (var 1)))
/-- `u_{j+2} Δ_{j+2}`. -/
abbrev udB : PTm 2 := u2B * dlB
/-- `Δ_{j+2}²`. -/
abbrev ddB : PTm 2 := dlB * dlB

/-- `Δ_{j+2}` at `(K, F)`. -/
abbrev Dl (j K F : PTm n) : PTm n := monus (S (K * succ (succ j)) F) (S (K * succ j) F)

theorem dl_at (j K F : PTm n) : Γ ⊢[PRAAx] inst2 dlB j (pairT K F) ≐ Dl j K F := by
  rw [show inst2 dlB j (pairT K F) = monus (S (fstT (pairT K F) * succ (succ j)) (sndT (pairT K F)))
    (S (fstT (pairT K F) * succ j) (sndT (pairT K F))) by simp [inst2]]
  exact delta_paired (succ j) K F

theorem u2_at (j K F : PTm n) : Γ ⊢[PRAAx] inst2 u2B j (pairT K F) ≐ U (succ (succ j)) K F := by
  rw [show inst2 u2B j (pairT K F) = monus (S (fstT (pairT K F) * succ (succ j)) (sndT (pairT K F)))
    (S (fstT (pairT K F)) (sndT (pairT K F))) by simp [inst2]]
  exact U_paired (succ (succ j)) K F

/-- `u_{j+2} = u_{j+1} + Δ_{j+2}`. -/
theorem u_step (j K F : PTm n) : Γ ⊢[PRAAx] U (succ (succ j)) K F ≐ U (succ j) K F + Dl j K F :=
  (U_increment (succ j) K F (Common.one_le_succ j)).eqSymm

theorem half_alg {S1 Sd u1 u2 d : PTm n} (ih : Γ ⊢[PRAAx] two * S1 ≐ u1 * u1 + Sd) (e : Γ ⊢[PRAAx] u2 ≐ u1 + d) :
    Γ ⊢[PRAAx] two * (S1 + u2 * d) ≐ u2 * u2 + (Sd + d * d) := by
  ipra_lc natEq ih - (𝔞 u2 + 𝔞 u1 - 𝔞 d) * natEq e

/-- The invariant, over `0 = M`, `1 = K`, `2 = F`. -/
abbrev hsF : Fm PTm 3 :=
  two * ap2 (sumF udB) (var 0) (pairT (var 1) (var 2)) ≐
    U (succ (var 0)) (var 1) (var 2) * U (succ (var 0)) (var 1) (var 2) + ap2 (sumF ddB) (var 0) (pairT (var 1) (var 2))

theorem hs_zero (K F : PTm n) : Γ ⊢[PRAAx]
    two * ap2 (sumF udB) zero (pairT K F) ≐ U (succ zero) K F * U (succ zero) K F + ap2 (sumF ddB) zero (pairT K F) := by
  have z1 := natEq (sum_zero (Γ := Γ) udB (pairT K F)); have z2 := natEq (sum_zero (Γ := Γ) ddB (pairT K F))
  have k1 : Γ ⊢[PRAAx] K * succ zero ≐ K := by ipra_ring
  have u1 : Γ ⊢[PRAAx] U (succ zero) K F ≐ zero :=
    (congrMonus (congrAp2 (sumF hB) k1 (.eqRefl F)) (.eqRefl _)).eqTrans (le_refl _)
  ipra_lc 2 * z1 - z2 - 𝔞 (U (succ zero) K F) * natEq u1

theorem hs_step {M K F : PTm n} (ih : Γ ⊢[PRAAx]
      two * ap2 (sumF udB) M (pairT K F) ≐ U (succ M) K F * U (succ M) K F + ap2 (sumF ddB) M (pairT K F)) :
    Γ ⊢[PRAAx] two * ap2 (sumF udB) (succ M) (pairT K F) ≐
      U (succ (succ M)) K F * U (succ (succ M)) K F + ap2 (sumF ddB) (succ M) (pairT K F) := by
  have s1 := sum_succ' (Γ := Γ) udB M (pairT K F)
  have s2 := sum_succ' (Γ := Γ) ddB M (pairT K F)
  have t1 : Γ ⊢[PRAAx] inst2 udB M (pairT K F) ≐ U (succ (succ M)) K F * Dl M K F := by
    rw [show inst2 udB M (pairT K F) = inst2 u2B M (pairT K F) * inst2 dlB M (pairT K F) by simp [inst2]]
    exact congrMul (u2_at _ _ _) (dl_at _ _ _)
  have t2 : Γ ⊢[PRAAx] inst2 ddB M (pairT K F) ≐ Dl M K F * Dl M K F := by
    rw [show inst2 ddB M (pairT K F) = inst2 dlB M (pairT K F) * inst2 dlB M (pairT K F) by simp [inst2]]
    exact congrMul (dl_at _ _ _) (dl_at _ _ _)
  have h := half_alg ih (u_step M K F)
  refine (congrMul (.eqRefl _) (s1.eqTrans (congrAdd (.eqRefl _) t1))).eqTrans (h.eqTrans ?_)
  exact congrAdd (.eqRefl _) (s2.eqTrans (congrAdd (.eqRefl _) t2)).eqSymm

private theorem hs₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] hsF := by
  ipra_ind [subst_ap2, subst_pairT]
  · exact hs_zero _ _
  · exact hs_step Prf.hyp0

/-- `2 Σ_{2≤k≤M+1} u_k Δ_k = u_{M+1}² + Σ_{2≤k≤M+1} Δ_k²`. -/
theorem half_square (M K F : PTm n) :
    Γ ⊢[PRAAx] two * ap2 (sumF udB) M (pairT K F) ≐
      U (succ M) K F * U (succ M) K F + ap2 (sumF ddB) M (pairT K F) := by
  have i := inst (Γ := Γ) hs₀ (![M, K, F] : Fin 3 → PTm n)
  simpa using i

/-- `Δ_{j+2}² ≤ ⌊F²/(j+1)²⌋`. -/
theorem dd_pt {K : PTm n} (j F : PTm n) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] le (Dl j K F * Dl j K F) (quo (F * F) (succ j * succ j)) := by
  have d := dlt_k hK (succ j) F
  have p := le_mul2 d d
  refine le_quo_of_mul_le (FloorTelescope.sq_pos j) ?_
  ipra_le sl p

/-- `Σ_{2≤k≤M+1} Δ_k² ≤ 2F²`. -/
theorem dd_le {K : PTm n} (M F : PTm n) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] le (ap2 (sumF ddB) M (pairT K F)) (two * (F * F)) := by
  have hK' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift, Syn.shift] using hK.shift
  have p := sum_le_params (Γ := Γ) ddB qB (pairT K F) (F * F) M (.allI (.impI (by
    rw [shift_pairT, show inst2 ddB (var 0) (pairT (Syn.shift K) (Syn.shift F)) =
      inst2 dlB (var 0) (pairT (Syn.shift K) (Syn.shift F)) * inst2 dlB (var 0) (pairT (Syn.shift K) (Syn.shift F)) by
      simp [inst2], inst2_qB, show Syn.shift (F * F) = Syn.shift F * Syn.shift F by simp [Syn.shift]]
    exact le_congr (congrMul (dl_at _ _ _) (dl_at _ _ _)).eqSymm (.eqRefl _) (dd_pt _ _ hK'.wk))))
  exact le_trans p (le_trans (SumReindex.sum_le_bound qB (le_succ_self M)) (floor_square_sum M (F * F)))

end LeanProofs.IPRA.AnalyticNumberTheory.HarmonicHalfSquare
