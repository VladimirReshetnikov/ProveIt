import IPRADerivations.AnalyticNumberTheory.RobinThreePos

/-!
# The width of `LogI(q, k)` (`robin_ipra_research_2026-11-19`, §"A logarithm enclosure from a finite geometric identity")

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/report.tex`: "`0 ≤ log q − S_K(z) ≤ r_K :=
9/(4(2K+1)3^{2K+1})` (`eq:uniform-log-tail`) … The enclosure is the sum of `a` copies of the enclosure of `log 2` and the
enclosure of `log y`. … Taking `K = k + a + 4` makes the interval width at most `(a + 1)3^{-2K} ≤ 2^{-k}`. … This defines a
fixed primitive-recursive rational interval `LogI(q, k)` of width at most `2^{-k}`."

* `name_tail`: each name has `U_K − S_K ≤ 9/(4(2K+1)3^{2K+1})` (`RobinLogName.uniform_tail`, for `z ≤ 1/3`);
* `lo_hi_width`: `hi(q, K) − lo(q, K) ≤ 9(e + 1)/(4(2K+1)3^{2K+1})`;
* `prec_bound`: `9(e + 1) 2^k ≤ 4(2K+1) 3^{2K+1}` at `K = k + e + 4`;
* `logI_width`: `hi(q, K) − lo(q, K) ≤ 2^{-k}` at the precision `K = k + e + 4` of `LogI(q, k)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinLogWidth

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma (Pv)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName (Nz Dz Un Ud Lz uniform_tail Dz_pos Ud_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval
  (eb loN loD hiN hiD Kp dt st Wt c3 c8 c3_sq c3_pos c8_pos st_sq st_pos Wt_pos z_third loD_pos hiD_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinThreePos (pw_lit)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (lt_pw pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.RobinThreePos (one_le_of_pos)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `U_K − S_K ≤ 9/(4(2K+1)3^{2K+1})` for `z = p/s ≤ 1/3`, cleared over `Ud·Dz`. -/
theorem name_tail {K p s W : PTm n} (hW : Γ ⊢[PRAAx] s * s ≐ W + p * p) (h3 : Γ ⊢[PRAAx] le (c3 * p) s) :
    Γ ⊢[PRAAx] le (num 4 * succ (two * K) * Pv K c3 * (Un K p s W * Dz K p s))
      (num 4 * succ (two * K) * Pv K c3 * (Nz K p s * Ud K p s W) + num 9 * (Ud K p s W * Dz K p s)) := by
  have ut := uniform_tail (K := K) hW h3
  ipra_le 𝔞 (succ (two * K) * Lz K p s * Lz K p s * Pv K s) * sl ut

/-- `hi(q, K) − lo(q, K) ≤ 9(e + 1)/(4(2K+1)3^{2K+1})`. -/
theorem lo_hi_width {a b : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a) (K : PTm n) :
    Γ ⊢[PRAAx] le (num 4 * succ (two * K) * Pv K c3 * (hiN a b K * loD a b K))
      (num 4 * succ (two * K) * Pv K c3 * (loN a b K * hiD a b K) + num 9 * succ (eb a b) * (hiD a b K * loD a b K)) := by
  have t3 := name_tail (K := K) (c3_sq (Γ := Γ)) (by ipra_le 0 : Γ ⊢[PRAAx] le (c3 * one) c3)
  have z := z_third hb hab
  have tt := name_tail (K := K) (st_sq hb hab) (by ipra_le sl z : Γ ⊢[PRAAx] le (c3 * dt a b) (st a b))
  ipra_le 𝔞 (eb a b * Ud K (dt a b) (st a b) (Wt a b) * Dz K (dt a b) (st a b)) * sl t3 +
    𝔞 (Ud K one c3 c8 * Dz K one c3) * sl tt

/-- Generic numerics: `9(e + 1)x ≤ 4A·19683·X²Y²` from `x ≤ X`, `e + 1 ≤ Y`, `A, X, Y ≥ 1`. -/
theorem prec_gen {e x X Y A : PTm n} (h1 : Γ ⊢[PRAAx] le x X) (h2 : Γ ⊢[PRAAx] le (succ e) Y)
    (hX : Γ ⊢[PRAAx] le one X) (hY : Γ ⊢[PRAAx] le one Y) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] le (num 9 * succ e * x) (num 4 * A * (X * X * Y * Y * num 19683)) := by
  have m := le_mul_mono h2 h1
  have m2 := le_mul_mono (le_mul_mono hA hX) hY
  ipra_le 78732 * 𝔞 (X * Y) * sl m2 + 78723 * 𝔞 (X * Y) + 9 * sl m

/-- `9(e + 1) 2^k ≤ 4(2K+1) 3^{2K+1}` at `K = k + e + 4`. -/
theorem prec_bound (k e : PTm n) :
    Γ ⊢[PRAAx] le (num 9 * succ e * pw two k)
      (num 4 * succ (two * (k + e + succ (succ (succ (succ zero))))) *
        pw c3 (succ (two * (k + e + succ (succ (succ (succ zero))))))) := by
  have h23 : Γ ⊢[PRAAx] le (two : PTm n) c3 := by ipra_le 1
  have h1 := pw_le_pw (Γ := Γ) k h23
  have h2 : Γ ⊢[PRAAx] le (succ e) (pw c3 e) := lt_pw h23 e
  have hX := one_le_of_pos (pw_pos' (Γ := Γ) c3_pos k)
  have hY := one_le_of_pos (pw_pos' (Γ := Γ) c3_pos e)
  have hA : Γ ⊢[PRAAx] le one (succ (two * (k + e + succ (succ (succ (succ zero)))))) := by
    ipra_le 𝔞 (two * (k + e + succ (succ (succ (succ zero)))))
  have g := prec_gen h1 h2 hX hY hA
  -- `3^{2K+1} = 3^k 3^k 3^e 3^e 3^9`
  have ex : Γ ⊢[PRAAx] succ (two * (k + e + succ (succ (succ (succ zero))))) ≐ k + (k + (e + (e + num 9))) := by
    apply deriveNat; ipra_simps; ring
  have e0 := natEq (congrAp2 powF ex (.eqRefl (c3 : PTm n)))
  have e1 := natEq (pw_add (Γ := Γ) c3 k (k + (e + (e + num 9))))
  have e2 := natEq (pw_add (Γ := Γ) c3 k (e + (e + num 9)))
  have e3 := natEq (pw_add (Γ := Γ) c3 e (e + num 9))
  have e4 := natEq (pw_add (Γ := Γ) c3 e (num 9))
  have p9 := pw_lit (Γ := Γ) (c3 : PTm n) 9
  have eT : Γ ⊢[PRAAx] pw c3 k * pw c3 k * pw c3 e * pw c3 e * num 19683 ≐
      pw c3 (succ (two * (k + e + succ (succ (succ (succ zero)))))) := by
    apply deriveNat; ipra_simps; rw [e0, e1, e2, e3, e4, p9]; ring
  exact le_congr (.eqRefl _) (by
    refine withEq eT fun f => ?_
    apply deriveNat; ipra_simps; rw [← f]) g

/-- The width of `LogI(q, k)`: `hi − lo ≤ 2^{-k}` at `K = k + e + 4`, cleared:
`2^k hiN·loD ≤ 2^k loN·hiD + hiD·loD`. -/
theorem logI_width {a b : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a) (k : PTm n) :
    Γ ⊢[PRAAx] le (pw two k * (hiN a b (Kp a b k) * loD a b (Kp a b k)))
      (pw two k * (loN a b (Kp a b k) * hiD a b (Kp a b k)) + hiD a b (Kp a b k) * loD a b (Kp a b k)) := by
  have w := lo_hi_width hb hab (Kp a b k)
  have p := prec_bound (Γ := Γ) k (eb a b)
  have m1 := le_mul_mono w (le_refl (pw two k))
  have m2 := le_mul_mono p (le_refl (hiD a b (Kp a b k) * loD a b (Kp a b k)))
  have hp : Γ ⊢[PRAAx] num 4 * succ (two * Kp a b k) * Pv (Kp a b k) c3 ≐
      succ (pred (num 4 * succ (two * Kp a b k) * Pv (Kp a b k) c3)) :=
    pos_mul (pos_mul (pos_of_one_le (by ipra_le 3)) (pos_of_one_le (by ipra_le 𝔞 (two * Kp a b k))))
      (pw_pos' c3_pos _)
  have c : Γ ⊢[PRAAx] le (num 4 * succ (two * Kp a b k) * Pv (Kp a b k) c3 *
        (pw two k * (hiN a b (Kp a b k) * loD a b (Kp a b k))))
      (num 4 * succ (two * Kp a b k) * Pv (Kp a b k) c3 *
        (pw two k * (loN a b (Kp a b k) * hiD a b (Kp a b k)) + hiD a b (Kp a b k) * loD a b (Kp a b k))) := by
    ipra_le sl m1 + sl m2
  exact mul_le_cancel (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _)) c)

end LeanProofs.IPRA.AnalyticNumberTheory.RobinLogWidth
