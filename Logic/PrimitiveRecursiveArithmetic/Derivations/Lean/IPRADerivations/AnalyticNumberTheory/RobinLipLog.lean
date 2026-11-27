import IPRADerivations.AnalyticNumberTheory.RobinLipArg

/-!
# Two-sided Lipschitz bounds for the lower names of `LogI` (`robin_ipra_research_2026-11-19`)

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/report.tex`, §"Explicit interval arithmetic".
For `1 ≤ x = a/b ≤ x' = a'/b' ≤ 2x` (`a'b = ab' + Δ`, so `(x' − x)/x = Δ/(ab')`), the lower names
`lo(x, K) = e·S_K(1/3) + S_K(z(y))` of `RobinLogInterval` satisfy, at every precision `K`,

* `lo_lip_up`: `lo(x', K) ≤ lo(x, K) + (x' − x)/x`;
* `lo_lip_low`: `lo(x, K) + (x' − x)/x' ≤ lo(x', K) + (x' − x)/(x · 9^K)`.

The binary exponents differ by at most one (`exp_step`). In the same binade the bounds are `RobinLipArg.arg_up/arg_low`
(scaled by `2^e`); across a binade boundary the difference `S_K(1/3) + S_K(z(y')) − S_K(z(y))` is split at the boundary
point (`y → 2`, then `1 → y'`), and the two pieces are combined by `(2 − y)(y' − 1) ≥ 0`. The four combinations are
abstract cleared-fraction lemmas (`same_up`, `same_low`, `adj_up`, `adj_low`).
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinLipLog

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName (Nz Dz Lz Dz_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipName (Rv)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipArg (Nz_p0 arg_up arg_low)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval
  (eb eb_spec exp_le Bt dt st c3 a_eq one_le_Bt loN loD)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds (two_pos')
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

alias mul1 := Common.mul_one_right

/-! ## The four combinations (abstract cleared fractions) -/

theorem same_up {e e' N3 D3 Nr Dr Nr' Dr' a b' P P' D : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P))
    (e1 : Γ ⊢[PRAAx] e' ≐ e) (e2 : Γ ⊢[PRAAx] P' ≐ P)
    (p : Γ ⊢[PRAAx] le (Nr' * Dr * (a * (b' * P'))) (Nr * Dr' * (a * (b' * P')) + D * P * Dr * Dr')) :
    Γ ⊢[PRAAx] le ((e' * N3 * Dr' + Nr' * D3) * (D3 * Dr) * (a * b'))
      ((e * N3 * Dr + Nr * D3) * (D3 * Dr') * (a * b') + D * (D3 * Dr) * (D3 * Dr')) := by
  have e1 := natEq e1
  have e2 := natEq e2
  have c : Γ ⊢[PRAAx] le (P * ((e' * N3 * Dr' + Nr' * D3) * (D3 * Dr) * (a * b')))
      (P * ((e * N3 * Dr + Nr * D3) * (D3 * Dr') * (a * b') + D * (D3 * Dr) * (D3 * Dr'))) := by
    ipra_le 𝔞 (D3 * D3) * sl p with ((-𝔞 D3 * 𝔞 Dr * 𝔞 Dr' * 𝔞 N3 * 𝔞 P * 𝔞 a * 𝔞 b')) * e1 + (((𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Nr' * 𝔞 a * 𝔞 b') + (-(𝔞 D3) ^ 2 * 𝔞 Dr' * 𝔞 Nr * 𝔞 a * 𝔞 b')) * e2
  exact mul_le_cancel (le_congr (congrMul hP (.eqRefl _)) (congrMul hP (.eqRefl _)) c)

theorem same_low {e e' N3 D3 Nr Dr Nr' Dr' a b a' b' P P' D G : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P))
    (e1 : Γ ⊢[PRAAx] e' ≐ e) (e2 : Γ ⊢[PRAAx] P' ≐ P)
    (p : Γ ⊢[PRAAx] le (Nr * Dr' * ((a' * (b * P)) * (a * (b' * P') * G)) + D * P * Dr * Dr' * (a * (b' * P') * G))
      (Nr' * Dr * ((a' * (b * P)) * (a * (b' * P') * G)) + D * P * Dr * Dr' * (a' * (b * P)))) :
    Γ ⊢[PRAAx] le ((e * N3 * Dr + Nr * D3) * (D3 * Dr') * ((a' * b) * (a * b' * G)) +
        D * (D3 * Dr) * (D3 * Dr') * (a * b' * G))
      ((e' * N3 * Dr' + Nr' * D3) * (D3 * Dr) * ((a' * b) * (a * b' * G)) + D * (D3 * Dr) * (D3 * Dr') * (a' * b)) := by
  have e1 := natEq e1
  have e2 := natEq e2
  have c : Γ ⊢[PRAAx] le (P * P * ((e * N3 * Dr + Nr * D3) * (D3 * Dr') * ((a' * b) * (a * b' * G)) +
        D * (D3 * Dr) * (D3 * Dr') * (a * b' * G)))
      (P * P * ((e' * N3 * Dr' + Nr' * D3) * (D3 * Dr) * ((a' * b) * (a * b' * G)) +
        D * (D3 * Dr) * (D3 * Dr') * (a' * b))) := by
    ipra_le 𝔞 (D3 * D3) * sl p with ((𝔞 D3 * 𝔞 Dr * 𝔞 Dr' * 𝔞 G * 𝔞 N3 * (𝔞 P) ^ 2 * 𝔞 a * 𝔞 a' * 𝔞 b * 𝔞 b')) * e1 + ((𝔞 D * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 G * 𝔞 P * 𝔞 a * 𝔞 b') + (-(𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 G * 𝔞 Nr' * 𝔞 P * 𝔞 a * 𝔞 a' * 𝔞 b * 𝔞 b') + ((𝔞 D3) ^ 2 * 𝔞 Dr' * 𝔞 G * 𝔞 Nr * 𝔞 P * 𝔞 a * 𝔞 a' * 𝔞 b * 𝔞 b')) * e2
  have hPP := pos_mul hP hP
  exact mul_le_cancel (le_congr (congrMul hPP (.eqRefl _)) (congrMul hPP (.eqRefl _)) c)

theorem adj_up {e e' N3 D3 Nr Dr Nr' Dr' N0 D0 a b a' b' P P' D Dy1 Dy2 : PTm n}
    (hM : Γ ⊢[PRAAx] D0 * (b' * P') ≐ succ (pred (D0 * (b' * P'))))
    (e1 : Γ ⊢[PRAAx] e' ≐ succ e) (e0 : Γ ⊢[PRAAx] N0 ≐ zero) (e2 : Γ ⊢[PRAAx] P' ≐ two * P)
    (eD : Γ ⊢[PRAAx] a' * b ≐ a * b' + D) (h1 : Γ ⊢[PRAAx] two * (b * P) ≐ a + Dy1)
    (h2 : Γ ⊢[PRAAx] a' * one ≐ one * (b' * P') + Dy2)
    (p1 : Γ ⊢[PRAAx] le (N3 * Dr * (a * one)) (Nr * D3 * (a * one) + Dy1 * Dr * D3))
    (p2 : Γ ⊢[PRAAx] le (Nr' * D0 * (one * (b' * P'))) (N0 * Dr' * (one * (b' * P')) + Dy2 * D0 * Dr')) :
    Γ ⊢[PRAAx] le ((e' * N3 * Dr' + Nr' * D3) * (D3 * Dr) * (a * b'))
      ((e * N3 * Dr + Nr * D3) * (D3 * Dr') * (a * b') + D * (D3 * Dr) * (D3 * Dr')) := by
  have e1 := natEq e1
  have e0 := natEq e0
  have e2 := natEq e2
  have eD := natEq eD
  have h1 := natEq h1
  have h2 := natEq h2
  have c : Γ ⊢[PRAAx] le (D0 * (b' * P') * ((e' * N3 * Dr' + Nr' * D3) * (D3 * Dr) * (a * b')))
      (D0 * (b' * P') * ((e * N3 * Dr + Nr * D3) * (D3 * Dr') * (a * b') + D * (D3 * Dr) * (D3 * Dr'))) := by
    ipra_le 𝔞 (D3 * Dr' * b' * D0 * (b' * P')) * sl p1 + 𝔞 (D3 * D3 * Dr * a * b') * sl p2 +
      𝔞 (D3 * D3 * Dr * Dr' * D0 * b' * Dy1 * Dy2) with ((-𝔞 D0 * 𝔞 D3 * 𝔞 Dr * 𝔞 Dr' * 𝔞 N3 * 𝔞 P' * 𝔞 a * (𝔞 b') ^ 2)) * e1 + ((-(𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 P' * 𝔞 a * (𝔞 b') ^ 2)) * e0 + ((𝔞 D * 𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 b') + (-𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 Dy1 * (𝔞 b') ^ 2) + (2 * 𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 P * 𝔞 b * (𝔞 b') ^ 2)) * e2 + ((-2 * 𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 P * 𝔞 b')) * eD + ((𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 Dy2 * 𝔞 b') + (2 * 𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 P * (𝔞 b') ^ 2)) * h1 + ((2 * 𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 P * 𝔞 b * 𝔞 b')) * h2
  exact mul_le_cancel (le_congr (congrMul hM (.eqRefl _)) (congrMul hM (.eqRefl _)) c)

theorem adj_low {e e' N3 D3 Nr Dr Nr' Dr' N0 D0 a b a' b' P P' D Dy1 Dy2 G : PTm n}
    (hM : Γ ⊢[PRAAx] two * (b * P) * (b' * P') * D0 ≐ succ (pred (two * (b * P) * (b' * P') * D0)))
    (e1 : Γ ⊢[PRAAx] e' ≐ succ e) (e0 : Γ ⊢[PRAAx] N0 ≐ zero) (e2 : Γ ⊢[PRAAx] P' ≐ two * P)
    (eD : Γ ⊢[PRAAx] a' * b ≐ a * b' + D) (h1 : Γ ⊢[PRAAx] two * (b * P) ≐ a + Dy1)
    (h2 : Γ ⊢[PRAAx] a' * one ≐ one * (b' * P') + Dy2)
    (q1 : Γ ⊢[PRAAx] le (Nr * D3 * ((two * (b * P)) * (a * one * G)) + Dy1 * Dr * D3 * (a * one * G))
      (N3 * Dr * ((two * (b * P)) * (a * one * G)) + Dy1 * Dr * D3 * (two * (b * P))))
    (q2 : Γ ⊢[PRAAx] le (N0 * Dr' * ((a' * one) * (one * (b' * P') * G)) + Dy2 * D0 * Dr' * (one * (b' * P') * G))
      (Nr' * D0 * ((a' * one) * (one * (b' * P') * G)) + Dy2 * D0 * Dr' * (a' * one))) :
    Γ ⊢[PRAAx] le ((e * N3 * Dr + Nr * D3) * (D3 * Dr') * ((a' * b) * (a * b' * G)) +
        D * (D3 * Dr) * (D3 * Dr') * (a * b' * G))
      ((e' * N3 * Dr' + Nr' * D3) * (D3 * Dr) * ((a' * b) * (a * b' * G)) + D * (D3 * Dr) * (D3 * Dr') * (a' * b)) := by
  have e1 := natEq e1
  have e0 := natEq e0
  have e2 := natEq e2
  have eD := natEq eD
  have h1 := natEq h1
  have h2 := natEq h2
  have c : Γ ⊢[PRAAx] le (two * (b * P) * (b' * P') * D0 * ((e * N3 * Dr + Nr * D3) * (D3 * Dr') *
        ((a' * b) * (a * b' * G)) + D * (D3 * Dr) * (D3 * Dr') * (a * b' * G)))
      (two * (b * P) * (b' * P') * D0 * ((e' * N3 * Dr' + Nr' * D3) * (D3 * Dr) * ((a' * b) * (a * b' * G)) +
        D * (D3 * Dr) * (D3 * Dr') * (a' * b))) := by
    ipra_le 𝔞 (D3 * Dr' * a' * b * b' * (b' * P') * D0) * sl q1 + 𝔞 (D3 * D3 * Dr * b * a * b' * two * (b * P)) * sl q2 +
      𝔞 (D3 * D3 * Dr * Dr' * b * a * b' * G * (b' * P') * D0 * Dy1 * Dy2) +
      𝔞 (D3 * D3 * Dr * Dr' * a' * b * b' * two * (b * P) * D0 * Dy1 * Dy2) with ((2 * 𝔞 D0 * 𝔞 D3 * 𝔞 Dr * 𝔞 Dr' * 𝔞 G * 𝔞 N3 * 𝔞 P * 𝔞 P' * 𝔞 a * 𝔞 a' * (𝔞 b) ^ 2 * (𝔞 b') ^ 2)) * e1 + ((2 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 G * 𝔞 P * 𝔞 P' * 𝔞 a * 𝔞 a' * (𝔞 b) ^ 2 * (𝔞 b') ^ 2)) * e0 + ((-2 * 𝔞 D * 𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 G * 𝔞 P * 𝔞 a * 𝔞 b * (𝔞 b') ^ 2) + (2 * 𝔞 D * 𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 P * 𝔞 a' * (𝔞 b) ^ 2 * 𝔞 b') + (-𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 Dy1 * 𝔞 Dy2 * 𝔞 G * 𝔞 a * 𝔞 b * (𝔞 b') ^ 2) + (𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 Dy1 * 𝔞 G * 𝔞 a * 𝔞 a' * 𝔞 b * (𝔞 b') ^ 2) + (-2 * 𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 Dy1 * 𝔞 P * 𝔞 a' * (𝔞 b) ^ 2 * (𝔞 b') ^ 2) + (2 * 𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 Dy2 * 𝔞 G * 𝔞 P * 𝔞 a * (𝔞 b) ^ 2 * (𝔞 b') ^ 2) + (-2 * 𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 G * 𝔞 P * (𝔞 a) ^ 2 * 𝔞 b * (𝔞 b') ^ 3) + (4 * 𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * (𝔞 P) ^ 2 * 𝔞 a' * (𝔞 b) ^ 3 * (𝔞 b') ^ 2)) * e2 + ((4 * 𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 G * (𝔞 P) ^ 2 * 𝔞 a * 𝔞 b * (𝔞 b') ^ 2) + (-4 * 𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * (𝔞 P) ^ 2 * 𝔞 a' * (𝔞 b) ^ 2 * 𝔞 b')) * eD + ((2 * 𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 Dy2 * 𝔞 G * 𝔞 P * 𝔞 a * 𝔞 b * (𝔞 b') ^ 2) + (2 * 𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 Dy2 * 𝔞 P * 𝔞 a' * (𝔞 b) ^ 2 * 𝔞 b') + (-2 * 𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 G * 𝔞 P * 𝔞 a * 𝔞 a' * 𝔞 b * (𝔞 b') ^ 2) + (4 * 𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * (𝔞 P) ^ 2 * 𝔞 a' * (𝔞 b) ^ 2 * (𝔞 b') ^ 2)) * h1 + ((-2 * 𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * 𝔞 G * 𝔞 P * (𝔞 a) ^ 2 * 𝔞 b * (𝔞 b') ^ 2) + (4 * 𝔞 D0 * (𝔞 D3) ^ 2 * 𝔞 Dr * 𝔞 Dr' * (𝔞 P) ^ 2 * 𝔞 a' * (𝔞 b) ^ 3 * 𝔞 b')) * h2
  exact mul_le_cancel (le_congr (congrMul hM (.eqRefl _)) (congrMul hM (.eqRefl _)) c)

/-! ## Binary exponents of nearby arguments -/

theorem lt_double {a b e : PTm n} (h : Γ ⊢[PRAAx] lt a (b * pw two (succ e))) :
    Γ ⊢[PRAAx] lt (two * a) (b * pw two (succ (succ e))) := by
  have eP := natEq (pw_succ (Γ := Γ) two (succ e))
  ipra_le 2 * sl h + 1 with 𝔞 b * eP

theorem le_double {a b e : PTm n} (h : Γ ⊢[PRAAx] lt a (b * pw two (succ e))) :
    Γ ⊢[PRAAx] le a (two * (b * pw two e)) := by
  have eP := natEq (pw_succ (Γ := Γ) two e)
  ipra_le sl h + 1 with -(𝔞 b) * eP

/-- For `x ≤ x' ≤ 2x` the exponents satisfy `e ≤ e' ≤ e + 1`. -/
theorem exp_step {a b a' b' D : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a)
    (hb' : Γ ⊢[PRAAx] le one b') (hab' : Γ ⊢[PRAAx] le b' a') (hD : Γ ⊢[PRAAx] a' * b ≐ a * b' + D)
    (h2 : Γ ⊢[PRAAx] le (a' * b) (two * (a * b'))) :
    Γ ⊢[PRAAx] le (eb a b) (eb a' b') ⋏ le (eb a' b') (succ (eb a b)) := by
  have s := eb_spec hb hab
  have s' := eb_spec hb' hab'
  have eD := natEq hD
  have hq : Γ ⊢[PRAAx] le (a * b') (a' * b) := by ipra_le 𝔞 D with eD
  have hq2 : Γ ⊢[PRAAx] le (a' * b) ((two * a) * b') := by ipra_le sl h2
  exact .andI (exp_le hb (Prf.andE₁ s) (Prf.andE₂ s') hq) (exp_le hb' (Prf.andE₁ s') (lt_double (Prf.andE₂ s)) hq2)

theorem pw_succ_two (e : PTm n) : Γ ⊢[PRAAx] pw two (succ e) ≐ two * pw two e :=
  (pw_succ _ _).eqTrans (by ipra_ring)

/-! ## The Lipschitz bounds -/

/-- `lo(x', K) ≤ lo(x, K) + (x' − x)/x` for `1 ≤ x ≤ x' ≤ 2x`, cleared: `x = a/b`, `x' = a'/b'`, `a'b = ab' + Δ`. -/
theorem lo_lip_up {a b a' b' D : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a)
    (hb' : Γ ⊢[PRAAx] le one b') (hab' : Γ ⊢[PRAAx] le b' a') (hD : Γ ⊢[PRAAx] a' * b ≐ a * b' + D)
    (h2 : Γ ⊢[PRAAx] le (a' * b) (two * (a * b'))) (K : PTm n) :
    Γ ⊢[PRAAx] le (loN a' b' K * loD a b K * (a * b')) (loN a b K * loD a' b' K * (a * b') + D * loD a b K * loD a' b' K) := by
  have st2 := exp_step hb hab hb' hab' hD h2
  have s := eb_spec hb hab
  have hBb := one_le_Bt (a := a) hb
  have hBb' := one_le_Bt (a := a') hb'
  refine .orE (lt_or_eq_of_le (Prf.andE₁ st2)) ?_ ?_
  · -- adjacent binades
    let C : List (Fm PTm n) := lt (eb a b) (eb a' b') :: Γ
    have e1 : C ⊢[PRAAx] eb a' b' ≐ succ (eb a b) := le_antisymm (Prf.andE₂ st2).wk Prf.hyp0
    have e2 : C ⊢[PRAAx] pw two (eb a' b') ≐ two * pw two (eb a b) :=
      (congrAp2 powF e1 (.eqRefl _)).eqTrans (pw_succ_two _)
    have h2y : C ⊢[PRAAx] le a (two * (b * pw two (eb a b))) := le_double (Prf.andE₂ s).wk
    have h1 := eq_add_of_le h2y
    have ha := a_eq (Γ := C) hb.wk hab.wk
    have ha' := a_eq (Γ := C) hb'.wk hab'.wk
    have p1 := arg_up (Γ := C) (a := a) (B := Bt a b) (d := dt a b) (s := st a b) (a' := two) (B' := one) (d' := one)
      (s' := c3) (Dy := monus (two * Bt a b) a) hBb.wk (le_refl _) ha (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (h1.eqTrans (congrAdd (mul1 _).eqSymm (.eqRefl _))) K
    have p2 := arg_up (Γ := C) (a := one) (B := one) (d := zero) (s := two) (a' := a') (B' := Bt a' b') (d' := dt a' b')
      (s' := st a' b') (Dy := dt a' b') (le_refl _) hBb'.wk (by ipra_ring) (by ipra_ring) ha' (.eqRefl _)
      ((mul1 _).eqTrans (ha'.eqTrans (congrAdd (one_mul _).eqSymm (.eqRefl _)))) K
    have hM : C ⊢[PRAAx] Dz K zero two * (b' * pw two (eb a' b')) ≐ succ (pred (Dz K zero two * (b' * pw two (eb a' b')))) :=
      pos_mul (Dz_pos two_pos' K zero) (pos_of_one_le hBb'.wk)
    exact adj_up hM e1 (Nz_p0 K two) e2 hD.wk h1 ((mul1 _).eqTrans (ha'.eqTrans (congrAdd (one_mul _).eqSymm (.eqRefl _))))
      p1 p2
  · -- the same binade
    let C : List (Fm PTm n) := (eb a b ≐ eb a' b') :: Γ
    have e1 : C ⊢[PRAAx] eb a' b' ≐ eb a b := Prf.hyp0.eqSymm
    have e2 : C ⊢[PRAAx] pw two (eb a' b') ≐ pw two (eb a b) := congrAp2 powF e1 (.eqRefl _)
    have e2' := natEq e2
    have eD' := natEq (hD.wk : C ⊢[PRAAx] _)
    have hDy : C ⊢[PRAAx] a' * Bt a b ≐ a * Bt a' b' + D * pw two (eb a b) := by
      ipra_lc 𝔞 (pw two (eb a b)) * eD' - 𝔞 a * 𝔞 b' * e2'
    have p := arg_up (Γ := C) hBb.wk hBb'.wk (a_eq hb.wk hab.wk) (.eqRefl _) (a_eq hb'.wk hab'.wk) (.eqRefl _) hDy K
    exact same_up (pw_pos' two_pos' _) e1 e2 p

/-- `lo(x, K) + (x' − x)/x' ≤ lo(x', K) + (x' − x)/(x · 9^K)` for `1 ≤ x ≤ x' ≤ 2x`, cleared. -/
theorem lo_lip_low {a b a' b' D : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a)
    (hb' : Γ ⊢[PRAAx] le one b') (hab' : Γ ⊢[PRAAx] le b' a') (hD : Γ ⊢[PRAAx] a' * b ≐ a * b' + D)
    (h2 : Γ ⊢[PRAAx] le (a' * b) (two * (a * b'))) (K : PTm n) :
    Γ ⊢[PRAAx] le (loN a b K * loD a' b' K * ((a' * b) * (a * b' * Rv K c3)) + D * loD a b K * loD a' b' K * (a * b' * Rv K c3))
      (loN a' b' K * loD a b K * ((a' * b) * (a * b' * Rv K c3)) + D * loD a b K * loD a' b' K * (a' * b)) := by
  have st2 := exp_step hb hab hb' hab' hD h2
  have s := eb_spec hb hab
  have hBb := one_le_Bt (a := a) hb
  have hBb' := one_le_Bt (a := a') hb'
  refine .orE (lt_or_eq_of_le (Prf.andE₁ st2)) ?_ ?_
  · let C : List (Fm PTm n) := lt (eb a b) (eb a' b') :: Γ
    have e1 : C ⊢[PRAAx] eb a' b' ≐ succ (eb a b) := le_antisymm (Prf.andE₂ st2).wk Prf.hyp0
    have e2 : C ⊢[PRAAx] pw two (eb a' b') ≐ two * pw two (eb a b) :=
      (congrAp2 powF e1 (.eqRefl _)).eqTrans (pw_succ_two _)
    have h2y : C ⊢[PRAAx] le a (two * (b * pw two (eb a b))) := le_double (Prf.andE₂ s).wk
    have h1 := eq_add_of_le h2y
    have ha := a_eq (Γ := C) hb.wk hab.wk
    have ha' := a_eq (Γ := C) hb'.wk hab'.wk
    have q1 := arg_low (Γ := C) (a := a) (B := Bt a b) (d := dt a b) (s := st a b) (a' := two) (B' := one) (d' := one)
      (s' := c3) (Dy := monus (two * Bt a b) a) hBb.wk (le_refl _) ha (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (h1.eqTrans (congrAdd (mul1 _).eqSymm (.eqRefl _))) h2y K
    have q2 := arg_low (Γ := C) (a := one) (B := one) (d := zero) (s := two) (a' := a') (B' := Bt a' b') (d' := dt a' b')
      (s' := st a' b') (Dy := dt a' b') (le_refl _) hBb'.wk (by ipra_ring) (by ipra_ring) ha' (.eqRefl _)
      ((mul1 _).eqTrans (ha'.eqTrans (congrAdd (one_mul _).eqSymm (.eqRefl _)))) (by ipra_le 1) K
    have hM : C ⊢[PRAAx] two * (b * pw two (eb a b)) * (b' * pw two (eb a' b')) * Dz K zero two ≐
        succ (pred (two * (b * pw two (eb a b)) * (b' * pw two (eb a' b')) * Dz K zero two)) :=
      pos_mul (pos_mul (pos_mul two_pos' (pos_of_one_le hBb.wk)) (pos_of_one_le hBb'.wk)) (Dz_pos two_pos' K zero)
    exact adj_low hM e1 (Nz_p0 K two) e2 hD.wk h1 ((mul1 _).eqTrans (ha'.eqTrans (congrAdd (one_mul _).eqSymm (.eqRefl _))))
      q1 q2
  · let C : List (Fm PTm n) := (eb a b ≐ eb a' b') :: Γ
    have e1 : C ⊢[PRAAx] eb a' b' ≐ eb a b := Prf.hyp0.eqSymm
    have e2 : C ⊢[PRAAx] pw two (eb a' b') ≐ pw two (eb a b) := congrAp2 powF e1 (.eqRefl _)
    have e2' := natEq e2
    have eD' := natEq (hD.wk : C ⊢[PRAAx] _)
    have hDy : C ⊢[PRAAx] a' * Bt a b ≐ a * Bt a' b' + D * pw two (eb a b) := by
      ipra_lc 𝔞 (pw two (eb a b)) * eD' - 𝔞 a * 𝔞 b' * e2'
    have h2y : C ⊢[PRAAx] le a (two * (b * pw two (eb a b))) := le_double (Prf.andE₂ s).wk
    have q := arg_low (Γ := C) hBb.wk hBb'.wk (a_eq hb.wk hab.wk) (.eqRefl _) (a_eq hb'.wk hab'.wk) (.eqRefl _) hDy h2y K
    exact same_low (pw_pos' two_pos' _) e1 e2 q

end LeanProofs.IPRA.AnalyticNumberTheory.RobinLipLog
