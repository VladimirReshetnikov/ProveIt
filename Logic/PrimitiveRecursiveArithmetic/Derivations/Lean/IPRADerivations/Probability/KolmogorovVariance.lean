import IPRADerivations.Probability.KolmogorovIidGlue
import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Core.LinearCombination

/-!
# Kolmogorov's maximal inequality with the variance of the sum

Packet: `probability/expected_value_ipra_2026-11-16`, `thm:kolmogorov`, the last step of the proof: "The final
second moment is `∑_{j<n} Var(X_j)` by independence and centering", for an iid sample on the `n`-fold product
law of `Probability/ProductPower` (`W = ∑ w`, `S = ∑ w X`, `Q = ∑ w X²`, `T = ∑_t P_n = W^n`).

* `point_square`: pointwise, `P_n D_n + 2 W n S · P_n S_n = W² P_n S_n² + n² S² P_n` for the cleared level
  `D_n = (W S_n − n S)²`;
* `square_sums`: `∑ P_n D_n + 2 n W S A = W² B + n² S² T` with `A = ∑ P_n S_n`, `B = ∑ P_n S_n²`;
* `dn_moment`: for `W ≥ 1`, `∑ P_n D_n + n S² T = n W Q T`, i.e. `E[W² (S_n − n μ)²] = n (W Q − S²) = n W² σ²`
  (from `sample_moments`, cancelling `T = W^n`);
* `kolmogorov_variance` (`thm:kolmogorov` for an iid sample, final form):
  `∑_{k≤n} ∑_t P_n a² I_k + n S² T ≤ n W Q T`, i.e. `a² P(max_{k≤n} W² (S_k − k μ)² ≥ a²) ≤ n W² σ²`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.KolmogorovVariance

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Expectation (Ew Wt inst2_mul' inst2_add')
open LeanProofs.IPRA.Probability.Independence (dsum sum_scale shift_sum)
open LeanProofs.IPRA.Probability.Variance (ad ad_sq)
open LeanProofs.IPRA.Probability.ProductPower (Pr Sr TB SB TB_at SB_at AB BB At Bt Tt sample_moments total_pow wdB xdB)
open LeanProofs.IPRA.Probability.KolmogorovIid (Cs Cs_at rv rv_at kB kB_at DB DB_at)
open LeanProofs.IPRA.Probability.KolmogorovIidGlue (A1 Cv kolmogorov_iid shift_pw)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

section Moments

variable (w X : PTm 2)

/-- `2 W n S`, over `(t, ⟨n, ⟨M, x⟩⟩)`. -/
abbrev Kc : PTm 2 := two * (Cs w * (rv * Cs (w * X)))
/-- `W²` and `n² S²`. -/
abbrev Kw : PTm 2 := Cs w * Cs w
abbrev Kn : PTm 2 := (rv * Cs (w * X)) * (rv * Cs (w * X))

/-- The pointwise square identity. -/
theorem point_square (t r M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (TB w * kB (DB w X) + Kc w X * (TB w * SB X)) t (pairT r (pairT M x)) ≐
      inst2 (Kw w * (TB w * (SB X * SB X)) + Kn w X * TB w) t (pairT r (pairT M x)) := by
  simp only [inst2_mul', inst2_add']
  have e2 : inst2 (two : PTm 2) t (pairT r (pairT M x)) = two := by simp [inst2]
  rw [e2]
  have p := natEq (TB_at (Γ := Γ) w t r M x)
  have s := natEq (SB_at (Γ := Γ) X t r M x)
  have cw := natEq (Cs_at (Γ := Γ) w t r M x)
  have cs := natEq (Cs_at (Γ := Γ) (w * X) t r M x)
  have rr := natEq (rv_at (Γ := Γ) t r (pairT M x))
  have d := natEq ((kB_at (Γ := Γ) (DB w X) t r (pairT M x)).eqTrans (DB_at w X r t M x))
  have q := natEq (ad_sq (Γ := Γ) (ap2 (sumF w) M x * Sr X r t M x) (r * ap2 (sumF (w * X)) M x))
  apply deriveNat; ipra_simps
  rw [p, s, cw, cs, rr, d]
  linear_combination 𝔟 (Pr w r t M x) * q

/-- `∑ P_n D_n + 2 n W S A = W² B + n² S² T`. -/
theorem square_sums (M x r : PTm n) :
    Γ ⊢[PRAAx] Ew (TB w) (kB (DB w X)) (pw M r) (pairT r (pairT M x)) +
        two * (ap2 (sumF w) M x * (r * ap2 (sumF (w * X)) M x)) * At w X r M x ≐
      ap2 (sumF w) M x * ap2 (sumF w) M x * Bt w X r M x +
        (r * ap2 (sumF (w * X)) M x) * (r * ap2 (sumF (w * X)) M x) * Tt w r M x := by
  have c := natEq (sum_congr_bounded (Γ := Γ) (TB w * kB (DB w X) + Kc w X * (TB w * SB X))
    (Kw w * (TB w * (SB X * SB X)) + Kn w X * TB w) (pairT r (pairT M x)) (pairT r (pairT M x)) (pw M r)
    (.allI (.impI (by
      simp only [shift_pairT]
      exact point_square w X _ _ _ _))))
  have a₁ : Γ ⊢[PRAAx] ap2 (sumF (TB w * kB (DB w X) + Kc w X * (TB w * SB X))) (pw M r) (pairT r (pairT M x)) ≐
      ap2 (sumF (TB w * kB (DB w X))) (pw M r) (pairT r (pairT M x)) +
        ap2 (sumF (Kc w X * (TB w * SB X))) (pw M r) (pairT r (pairT M x)) := sum_add _ _ _ _
  have a₂ : Γ ⊢[PRAAx] ap2 (sumF (Kw w * (TB w * (SB X * SB X)) + Kn w X * TB w)) (pw M r) (pairT r (pairT M x)) ≐
      ap2 (sumF (Kw w * (TB w * (SB X * SB X)))) (pw M r) (pairT r (pairT M x)) +
        ap2 (sumF (Kn w X * TB w)) (pw M r) (pairT r (pairT M x)) := sum_add _ _ _ _
  have k₁ := natEq (sum_scale (Γ := Γ) (Kc w X * (TB w * SB X)) (AB w X) (pw M r)
    (two * (ap2 (sumF w) M x * (r * ap2 (sumF (w * X)) M x))) (pairT r (pairT M x)) (pairT r (pairT M x))
    (.allI (.impI (by
      simp only [shift_pairT, inst2_mul']
      have e : Syn.shift (two * (ap2 (sumF w) M x * (r * ap2 (sumF (w * X)) M x))) =
          two * (ap2 (sumF w) (Syn.shift M) (Syn.shift x) *
            (Syn.shift r * ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x))) := by simp [Syn.shift]
      have e2 : inst2 (two : PTm 2) (var 0) (pairT (Syn.shift r) (pairT (Syn.shift M) (Syn.shift x))) = two := by
        simp [inst2]
      rw [e, e2]
      exact congrMul (congrMul (.eqRefl _) (congrMul (Cs_at _ _ _ _ _) (congrMul (rv_at _ _ _) (Cs_at _ _ _ _ _))))
        (.eqRefl _)))))
  have k₂ := natEq (sum_scale (Γ := Γ) (Kw w * (TB w * (SB X * SB X))) (BB w X) (pw M r)
    (ap2 (sumF w) M x * ap2 (sumF w) M x) (pairT r (pairT M x)) (pairT r (pairT M x)) (.allI (.impI (by
      simp only [shift_pairT, inst2_mul']
      have e : Syn.shift (ap2 (sumF w) M x * ap2 (sumF w) M x) =
          ap2 (sumF w) (Syn.shift M) (Syn.shift x) * ap2 (sumF w) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
      rw [e]
      exact congrMul (congrMul (Cs_at _ _ _ _ _) (Cs_at _ _ _ _ _)) (.eqRefl _)))))
  have k₃ := natEq (sum_scale (Γ := Γ) (Kn w X * TB w) (TB w) (pw M r)
    ((r * ap2 (sumF (w * X)) M x) * (r * ap2 (sumF (w * X)) M x)) (pairT r (pairT M x)) (pairT r (pairT M x))
    (.allI (.impI (by
      simp only [shift_pairT, inst2_mul']
      have e : Syn.shift ((r * ap2 (sumF (w * X)) M x) * (r * ap2 (sumF (w * X)) M x)) =
          (Syn.shift r * ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x)) *
            (Syn.shift r * ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x)) := by simp [Syn.shift]
      rw [e]
      exact congrMul (congrMul (congrMul (rv_at _ _ _) (Cs_at _ _ _ _ _)) (congrMul (rv_at _ _ _) (Cs_at _ _ _ _ _)))
        (.eqRefl _)))))
  have b₁ := natEq a₁
  have b₂ := natEq a₂
  apply deriveNat; ipra_simps
  linear_combination -b₁ + c + b₂ - k₁ + k₂ + k₃

/-- `E[W² (S_n − n μ)²] = n (W Q − S²)`: `∑ P_n D_n + n S² T = n W Q T` for `W ≥ 1`. -/
theorem dn_moment {M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hW : Γ ⊢[PRAAx] ap2 (sumF w) M x ≐ succ (pred (ap2 (sumF w) M x))) (r : PTm n) :
    Γ ⊢[PRAAx] Ew (TB w) (kB (DB w X)) (pw M r) (pairT r (pairT M x)) +
        r * (ap2 (sumF (w * X)) M x * ap2 (sumF (w * X)) M x) * Tt w r M x ≐
      r * (ap2 (sumF w) M x * ap2 (sumF (w * (X * X))) M x) * Tt w r M x := by
  have sm := sample_moments (Γ := Γ) (x := x) w X hM r
  have hT : Γ ⊢[PRAAx] Tt w r M x ≐ succ (pred (Tt w r M x)) :=
    (total_pow w hM r).eqTrans ((pw_pos' hW r).eqTrans (congrSucc (congrPred (total_pow w hM r).eqSymm)))
  refine mul_cancel hT ?_
  ipra_lc 𝔟 (Tt w r M x) * natEq (square_sums (Γ := Γ) w X M x r) + natEq (Prf.andE₂ sm) +
    (𝔟 (ap2 (sumF w) M x) * 𝔟 (At w X r M x) - 𝔟 r * 𝔟 (ap2 (sumF (w * X)) M x) * 𝔟 (Tt w r M x)) * natEq (Prf.andE₁ sm)

end Moments

/-- `thm:kolmogorov` for an iid sample, with the variance: for `W ≥ 1`,
`∑_{k≤n} ∑_{t<M^n} P_n a² I_k + n S² T ≤ n W Q T`, i.e. `a² P(max_{k≤n} W² (S_k − k μ)² ≥ a²) ≤ n W² σ²`. -/
theorem kolmogorov_variance (w X a : PTm 2) {M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hW : Γ ⊢[PRAAx] ap2 (sumF w) M x ≐ succ (pred (ap2 (sumF w) M x))) (r : PTm n) :
    Γ ⊢[PRAAx] le (dsum (A1 w X a) (succ r) (pw M r) (pairT r (pairT M x)) +
        r * (ap2 (sumF (w * X)) M x * ap2 (sumF (w * X)) M x) * Tt w r M x)
      (r * (ap2 (sumF w) M x * ap2 (sumF (w * (X * X))) M x) * Tt w r M x) := by
  have k := kolmogorov_iid w X a hM r x
  have d := natEq (dn_moment (Γ := Γ) w X hM hW r)
  ipra_le sl k using linear_combination -d

end LeanProofs.IPRA.Probability.KolmogorovVariance
