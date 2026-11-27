import IPRADerivations.AnalyticNumberTheory.SieveWeightOne
import IPRADerivations.AnalyticNumberTheory.SievePrimes
import IPRADerivations.Foundations.SumPositive

/-!
# The sum of the absolute values of the explicit sieve weights

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, `eq:weight-bound`:
"`|λ_d| ≤ 1`, `Σ_{d ∈ D} |λ_d| ≤ |D| ≤ z`".

The cleared weights are `λ = λ⁺ − λ⁻` with natural parts `lB UPw`, `lB UNw` (`SieveWeightForm`), so `|λ_d|` is at
most `λ⁺_d + λ⁻_d`. With `|Y_r| = Y⁺_r + Y⁻_r = [r ≥ 1] μ(r)² [gcd(r, q) = 1] z!/φ(r)` and

  `W_d = Σ_{r ≤ z} [r ≥ 1] [d ∣ r] |Y_r|`                                    (`wS YP + wS YN`),

this module derives the triangle inequality for the Möbius inversion,

  `U⁺_d + U⁻_d ≤ W_d`,   `Σ_{d ≤ z} (λ⁺_d + λ⁻_d) ≤ Σ_{d ≤ z} d [d ≥ 1] [gcd(d, q) = 1] W_d`     (`U_abs`, `tri`),

from `μ⁺ + μ⁻ ≤ 1` (`mu_sum_le`), and reduces `eq:weight-bound` to one statement about each `d`:

  if `d · W_d ≤ A` for `1 ≤ d ≤ z` (and `q ≥ 1`), then `Σ_{d ≤ z} (λ⁺_d + λ⁻_d) ≤ z · A`         (`weights_le`),

by `Foundations/SumPositive.sum_le_pos_const` (the summand at `d = 0` vanishes).

The statement `d · W_d ≤ A` is `|λ_d| ≤ 1` of the paper in the cleared normalization (`A = z! G`); it is a hypothesis
of `weights_le` and is not derived here.

* `ind_sum_le`, `scaled_le`, `mul_le_one`, `pair_le`, `regroup`, `scale_le`, `drop_le`: the certificates over opaque
  terms;
* `w_form`: the summand of the inverted weight;
* `pair_bound`: `Σ_r [d ∣ r] (μ⁺ + μ⁻)(r/d) [r ≥ 1] y_r ≤ Σ_r [r ≥ 1] [d ∣ r] y_r`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightAbs

open_ipra exports
open LeanProofs.IPRA.Signum (sg sg_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (muP muN)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveInversion (hS inst2_hS wB wB_at)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveDiagonal (Ab Ab_at)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveExpansion (lB inst2_lB)
open LeanProofs.IPRA.AnalyticNumberTheory.SievePrimes (sg_le_one eqb_le1)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightRows (uB inst2_uB)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightValues (YP YN eqb_zero_one)
open LeanProofs.IPRA.Probability.Independence (row_pt)
export PowerDivisorGrowth (mu_sum_le)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Certificates over opaque terms -/

/-- Two indicators with product `0` have sum at most `1`. -/
theorem ind_sum_le {e0 e1 : PTm n} (h0 : Γ ⊢[PRAAx] le e0 one) (h1 : Γ ⊢[PRAAx] le e1 one)
    (hd : Γ ⊢[PRAAx] e0 * e1 ≐ zero) : Γ ⊢[PRAAx] le (e0 + e1) one := by
  have x := natEq hd
  ipra_le sl h0 * sl h1 with x

theorem scaled_le {E e0 e1 : PTm n} (hE : Γ ⊢[PRAAx] le E one) (h : Γ ⊢[PRAAx] le (e0 + e1) one) :
    Γ ⊢[PRAAx] le (E * e0 + E * e1) one := by
  ipra_le sl hE + 𝔞 E * sl h

theorem mul_le_one {a b : PTm n} (ha : Γ ⊢[PRAAx] le a one) (hb : Γ ⊢[PRAAx] le b one) :
    Γ ⊢[PRAAx] le (a * b) one := by
  ipra_le sl ha + 𝔞 a * sl hb

/-- The two summands of the inversion with `μ⁺` and `μ⁻` are together at most `[r ≥ 1] [d ∣ r] y_r`. -/
theorem pair_le {S e e1 mP mN s t : PTm n} (hS : Γ ⊢[PRAAx] le S one) (h1 : Γ ⊢[PRAAx] le e1 one)
    (hm : Γ ⊢[PRAAx] le (mP + mN) one) :
    Γ ⊢[PRAAx] le (((S * e) * (e1 * mP)) * (s * t) + ((S * e) * (e1 * mN)) * (s * t)) (s * e * t) := by
  ipra_le 𝔞 s * 𝔞 e * 𝔞 t * (sl hS + 𝔞 S * (sl h1 + 𝔞 e1 * sl hm))

theorem regroup {a b c e WP WN : PTm n} (hP : Γ ⊢[PRAAx] le (a + e) WP) (hN : Γ ⊢[PRAAx] le (c + b) WN) :
    Γ ⊢[PRAAx] le ((a + b) + (c + e)) (WP + WN) := by
  ipra_le sl hP + sl hN

theorem scale_le {d k u1 u2 W : PTm n} (h : Γ ⊢[PRAAx] le (u1 + u2) W) :
    Γ ⊢[PRAAx] le (d * (k * u1) + d * (k * u2)) (d * (k * W)) := by
  ipra_le 𝔞 d * 𝔞 k * sl h

theorem drop_le {D k W A : PTm n} (hk : Γ ⊢[PRAAx] le k one) (h : Γ ⊢[PRAAx] le (D * W) A) :
    Γ ⊢[PRAAx] le (D * (k * W)) A := by
  ipra_le sl h + 𝔞 D * 𝔞 W * sl hk

/-! ## `μ⁺ + μ⁻ ≤ 1` -/

theorem a_sum_le (i p : PTm n) : Γ ⊢[PRAAx] le (inst2 aPB i p + inst2 aNB i p) one := by
  rw [inst2_aP, inst2_aN]
  exact mu_sum_le _ _

/-! ## The triangle inequality for the inverted weight -/

/-- The summand of the inverted weight at `d`, `r`. -/
theorem w_form (y a : PTm 2) (d r p : PTm n) :
    Γ ⊢[PRAAx] inst3 (wB y a) d r (pairT one p) ≐
      ((sg d * eqb (rem r d) zero) * (eqb (rem d one) zero * inst2 a (quo r d) one)) * (sg r * inst2 y r p) := by
  have h := (wB_at (Γ := Γ) y a d r one p).eqTrans (congrMul (cv_at hS a d r one) (.eqRefl _))
  rw [inst2_hS] at h
  exact h

theorem row_form (y a : PTm 2) (d r p : PTm n) :
    Γ ⊢[PRAAx] inst2 (rowB (wB y a)) r (pairT d (pairT one p)) ≐
      ((sg d * eqb (rem r d) zero) * (eqb (rem d one) zero * inst2 a (quo r d) one)) * (sg r * inst2 y r p) :=
  (row_pt (wB y a) d r (pairT one p)).eqTrans (w_form y a d r p)

/-- `Σ_{r ≤ z} [r ≥ 1] [d ∣ r] y_r` over `0 = d`, `1 = P`, `z = snd (snd P)`. -/
def wS (y : PTm 2) : PTm 2 := ap2 (sumF (Ab y)) (succ (sndT (sndT (var 1)))) (pairT (var 0) (var 1))

theorem inst2_wS (y : PTm 2) (d P : PTm n) :
    inst2 (wS y) d P = ap2 (sumF (Ab y)) (succ (sndT (sndT P))) (pairT d P) := by
  simp [inst2, wS]

/-- `Σ_r [d ∣ r] (μ⁺ + μ⁻)(r/d) [r ≥ 1] y_r ≤ Σ_r [r ≥ 1] [d ∣ r] y_r`. -/
theorem pair_bound (y : PTm 2) (d P : PTm n) :
    Γ ⊢[PRAAx] le (inst2 (uB aPB y) d P + inst2 (uB aNB y) d P) (inst2 (wS y) d P) := by
  rw [inst2_uB, inst2_uB, inst2_wS]
  refine le_congr (sum_add _ _ _ _) (.eqRefl _) (sum_le_params _ _ _ _ _ (.allI (.impI ?_)))
  have s1 : Syn.shift (pairT d (pairT one P)) = pairT (Syn.shift d) (pairT one (Syn.shift P)) := by
    simp [Syn.shift]
  rw [s1, shift_pairT, inst2_addBody]
  exact le_congr (congrAdd (row_form y aPB _ _ _) (row_form y aNB _ _ _)).eqSymm (Ab_at y _ _ _).eqSymm
    (pair_le (sg_le_one _) (eqb_le1 _ _) (a_sum_le _ _))

/-- `U⁺_d + U⁻_d ≤ W_d`. -/
theorem U_abs (d P : PTm n) :
    Γ ⊢[PRAAx] le (inst2 UPw d P + inst2 UNw d P) (inst2 (wS YP) d P + inst2 (wS YN) d P) := by
  rw [UPw, UNw, inst2_addBody, inst2_addBody]
  exact regroup (pair_bound YP d P) (pair_bound YN d P)

/-- `λ⁺_d + λ⁻_d ≤ d [d ≥ 1] [gcd(d, q) = 1] W_d`. -/
theorem lam_abs (d P : PTm n) :
    Γ ⊢[PRAAx] le (inst2 (lB UPw) d P + inst2 (lB UNw) d P) (inst2 (lB (addBody (wS YP) (wS YN))) d P) := by
  rw [inst2_lB, inst2_lB, inst2_lB, inst2_addBody]
  exact scale_le (U_abs d P)

/-- `Σ_{d ≤ z} (λ⁺_d + λ⁻_d) ≤ Σ_{d ≤ z} d [d ≥ 1] [gcd(d, q) = 1] W_d`. -/
theorem tri (X P : PTm n) :
    Γ ⊢[PRAAx] le
      (ap2 (sumF (sndB (lB UPw))) (succ (sndT (sndT P))) (pairT X P) +
        ap2 (sumF (sndB (lB UNw))) (succ (sndT (sndT P))) (pairT X P))
      (ap2 (sumF (lB (addBody (wS YP) (wS YN)))) (succ (sndT (sndT P))) P) := by
  refine le_congr (sum_add _ _ _ _) (.eqRefl _) (sum_le_params _ _ _ _ _ (.allI (.impI ?_)))
  rw [shift_pairT, inst2_addBody, inst2_sndB, inst2_sndB]
  exact le_congr (congrAdd (congrInst2 _ (.eqRefl _) (snd_pair _ _)) (congrInst2 _ (.eqRefl _) (snd_pair _ _))).eqSymm
    (.eqRefl _) (lam_abs _ _)

/-! ## Reduction of the weight bound to one statement about each `d` -/

/-- `eq:weight-bound` from `|λ_d| ≤ 1`: if `d W_d ≤ A` for `1 ≤ d ≤ z`, then `Σ_{d ≤ z} (λ⁺_d + λ⁻_d) ≤ z A`. -/
theorem weights_le (X : PTm n) {P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P))
    (hpt : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (d P : PTm k), (Δ ⊢[PRAAx] le one (fstT P)) →
      (Δ ⊢[PRAAx] lt d (sndT (sndT P))) →
      (Δ ⊢[PRAAx] le (succ d * (inst2 (wS YP) (succ d) P + inst2 (wS YN) (succ d) P)) (Asum P))) :
    Γ ⊢[PRAAx] le
      (ap2 (sumF (sndB (lB UPw))) (succ (sndT (sndT P))) (pairT X P) +
        ap2 (sumF (sndB (lB UNw))) (succ (sndT (sndT P))) (pairT X P))
      (sndT (sndT P) * Asum P) := by
  refine le_trans (tri X P) (sum_le_pos_const _ ?_ ?_)
  · rw [inst2_lB]
    exact zero_mul _
  · have hq' : (Γ.map Fm.shift) ⊢[PRAAx] le one (fstT (Syn.shift P)) := by
      simpa [Fm.shift, Syn.shift] using hq.shift
    have sN : Syn.shift (sndT (sndT P)) = sndT (sndT (Syn.shift P)) := by simp [Syn.shift]
    have sA : Syn.shift (Asum P) = Asum (Syn.shift P) := by simp [Syn.shift]
    rw [sN, sA, inst2_lB, inst2_addBody]
    exact drop_le (mul_le_one (sg_le_one _) (eqb_le1 _ _)) (hpt _ _ hq'.wk Prf.hyp0)

end LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightAbs
