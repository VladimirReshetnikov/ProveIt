import IPRADerivations.AnalyticNumberTheory.RobinLipBound
import IPRADerivations.AnalyticNumberTheory.RobinLogWidth
import IPRADerivations.AnalyticNumberTheory.LcmBridgeSide
import IPRADerivations.AnalyticNumberTheory.LcmBridgeTransfer

/-!
# `ψ ≤ ϑ + m log P` on the logarithm names (`robin_ipra_research_2026-11-19`, `paper/lcm_bridge.tex`)

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/lcm_bridge.tex`, Lemma "Losses at a square
frontier": "Only primes `p ≤ m` contribute to `ψ(P) − ϑ(P)` … `0 ≤ ψ(P) − ϑ(P) ≤ m log P`." For `P = m²`,
`L = lcm(1, …, P)` and the upper end `ψ̂ = C₁/D₁ = hi(log L, K₁)` used by the Robin upper end `U(L, k)`
(`RobinUpperEnd`):

* `psi_le`: `ψ̂ ≤ Θ + m·λ + 1`, where `Θ = hi(log ∏_{p≤P} p, K_θ)` is an upper name of `ϑ(P)` at *any* precision and
  `λ = lo(log P, K₁)`. The chain is `ψ̂ ≤ lo(log L) + 2^{−r}` (`RobinLogWidth.logI_width`),
  `L ≤ P^m ∏p` (`PrimorialLower.lcm_primorial`, `RobinLogInterval.lo_mono`),
  `lo(log(∏p·P^m)) ≤ lo(log ∏p) + m λ + m(P − 1)/9^{K₁}` (`RobinLipBound.lo_pow`, i.e. `m` applications of the addition
  theorem) and `lo(log ∏p, K₁) ≤ Θ`; the two errors are each at most `1/2` (`err_G`, `err_R`);
* `theta_hi`: `Θ ≥ P/4` for `m ≥ 16`, `K_θ ≥ 2` (`LcmBridgeSide.theta_m16`);
* `lam_ge`: `λ = lo(log P, K) ≥ 448/81` for `m ≥ 16`, `K ≥ 2` (`LcmBridgeTheta.lo_ge`, `eb(P) ≥ 8`);
* `pw_mono_exp`, `eb_ge`: monotonicity of `p^a` in `a`, and `2^j ≤ a ⇒ j ≤ e(a)`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeDPsi

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipName (Rv)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipSum (one_le_mul one_le_of_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipBound (lo_pow)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval
  (eb eb_spec exp_le Kp c3 loN loD hiN hiD lo_mono lo_le_hi_any loD_pos hiD_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinThreePos (rr K1 pw_lit)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinUpperEnd (C1 D1)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGammaInterval (k2)
open LeanProofs.IPRA.AnalyticNumberTheory.PrimorialLower (prim prim_pos lcm_primorial)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds (two_pos')
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Powers and exponents -/

theorem pw_mono_exp {p a b : PTm n} (hp : Γ ⊢[PRAAx] le one p) (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (pw p a) (pw p b) := by
  have e1 : Γ ⊢[PRAAx] pw p b ≐ pw p a * pw p (monus b a) :=
    (congrAp2 powF (eq_add_of_le h) (.eqRefl _)).eqTrans (pw_add _ _ _)
  have x := natEq (pw_pos' (Γ := Γ) (pos_of_one_le hp) (monus b a))
  refine le_congr (.eqRefl _) e1.eqSymm ?_
  ipra_le 𝔞 (pw p a * pred (pw p (monus b a))) with 𝔞 (pw p a) * x

/-- `2^j ≤ a` gives `j ≤ e(a)`. -/
theorem eb_ge {a j : PTm n} (h1 : Γ ⊢[PRAAx] le one a) (h : Γ ⊢[PRAAx] le (pw two j) a) :
    Γ ⊢[PRAAx] le j (eb a one) := by
  have s := eb_spec (le_refl one) h1
  exact exp_le (a := pw two j) (b := one) (a' := a) (b' := one) (le_refl one) (by ipra_le 0) (Prf.andE₂ s)
    (by ipra_le sl h)

/-! ## The two errors -/

/-- `2m(P − 1) ≤ 9^{K₁}`: `m⁴ ≤ L² < 4^{e+1} ≤ 3^{2K₁}`. -/
theorem err_G {m k : PTm n} (hm2 : Γ ⊢[PRAAx] le two m) :
    Γ ⊢[PRAAx] le (two * m * monus (m * m) one) (Rv (K1 (lcmu (m * m)) k) c3) := by
  have hm1 : Γ ⊢[PRAAx] m ≐ succ (pred m) := pos_of_one_le (le_trans (by ipra_le 1) hm2)
  have hP := pos_mul hm1 hm1
  have hL1 : Γ ⊢[PRAAx] le one (lcmu (m * m)) := one_le_of_pos' (lcmu_pos _)
  have hmL := LcmBridgeTransfer.le_lcmu hP
  have s := Prf.andE₂ (eb_spec (le_refl one) hL1)
  have h23 : Γ ⊢[PRAAx] le (two : PTm n) c3 := by ipra_le 1
  have p23 := pw_le_pw (Γ := Γ) (succ (eb (lcmu (m * m)) one)) h23
  have h1 : Γ ⊢[PRAAx] le (m * m) (pw c3 (succ (eb (lcmu (m * m)) one))) := by
    ipra_le sl hmL + sl s + sl p23 + 1
  have h4 := le_mul_mono h1 h1
  have h5 := pw_add (Γ := Γ) (c3 : PTm n) (succ (eb (lcmu (m * m)) one)) (succ (eb (lcmu (m * m)) one))
  have h6 := pw_mono_exp (Γ := Γ) (p := c3) (by ipra_le 2)
    (by ipra_le 2 * 𝔞 k + 2 * 𝔞 (eb (lcmu (m * m)) one) + 40 :
      Γ ⊢[PRAAx] le (succ (eb (lcmu (m * m)) one) + succ (eb (lcmu (m * m)) one)) (two * K1 (lcmu (m * m)) k))
  have ec := natEq (eq_add_of_le (one_le_of_pos' hP))
  have h7 : Γ ⊢[PRAAx] le (two * m * monus (m * m) one) ((m * m) * (m * m)) := by
    ipra_le 𝔞 (m * m * m) * sl hm2 + 2 * 𝔞 m with 2 * 𝔞 m * ec
  exact le_trans h7 (le_trans h4 (le_congr h5 (.eqRefl _) h6))

/-- `2 ≤ 2^r` at `r = k + e(L) + 17`. -/
theorem err_R (N k : PTm n) : Γ ⊢[PRAAx] le two (pw two (rr N k)) := by
  have h := pw_mono_exp (Γ := Γ) (p := two) (by ipra_le 1)
    (by ipra_le 𝔞 k + 𝔞 (eb N one) + 16 : Γ ⊢[PRAAx] le one (rr N k))
  have e1 := natEq (pw_succ (Γ := Γ) (two : PTm n) zero)
  have e0 := natEq (pw_zero (Γ := Γ) (two : PTm n))
  ipra_le sl h with e1 + 2 * e0

/-! ## `ψ̂ ≤ Θ + mλ + 1` -/

theorem psi_alg {C D lLn lLd Yn Yd An Ad ln ld tn td G R m c : PTm n}
    (hM : Γ ⊢[PRAAx] two * R * lLd * Yd * Ad * G ≐ succ (pred (two * R * lLd * Yd * Ad * G)))
    (w1 : Γ ⊢[PRAAx] le (R * (C * lLd)) (R * (lLn * D) + D * lLd))
    (mono : Γ ⊢[PRAAx] le (lLn * Yd) (Yn * lLd))
    (pw : Γ ⊢[PRAAx] le (Yn * Ad * ld * G) (An * Yd * ld * G + m * ln * Yd * Ad * G + m * c * Yd * Ad * ld))
    (hle : Γ ⊢[PRAAx] le (An * td) (tn * Ad)) (e1 : Γ ⊢[PRAAx] le (two * m * c) G) (e2 : Γ ⊢[PRAAx] le two R) :
    Γ ⊢[PRAAx] le (C * td * ld) (D * (tn * ld + m * ln * td + td * ld)) := by
  have cc : Γ ⊢[PRAAx] le (two * R * lLd * Yd * Ad * G * (C * td * ld))
      (two * R * lLd * Yd * Ad * G * (D * (tn * ld + m * ln * td + td * ld))) := by
    ipra_le 2 * 𝔞 (Yd * Ad * G * td * ld) * sl w1 + 2 * 𝔞 (R * Ad * G * D * td * ld) * sl mono +
      2 * 𝔞 (R * lLd * D * td) * sl pw + 2 * 𝔞 (R * lLd * Yd * G * D * ld) * sl hle +
      𝔞 (R * lLd * Yd * Ad * D * td * ld) * sl e1 + 𝔞 (lLd * Yd * Ad * G * D * td * ld) * sl e2
  exact mul_le_cancel (le_congr (congrMul hM (.eqRefl _)) (congrMul hM (.eqRefl _)) cc)

/-- `lcm_bridge.tex`: `ψ(P) − ϑ(P) ≤ m log P` on the names, with the precision errors absorbed in `+1`:
`C₁/D₁ ≤ Θ + m λ + 1`, `Θ = hi(log ∏_{p≤m²} p, K_θ)`, `λ = lo(log m², K₁)`. -/
theorem psi_le {m k Kθ : PTm n} (hm2 : Γ ⊢[PRAAx] le two m) :
    Γ ⊢[PRAAx] le (C1 (lcmu (m * m)) k * hiD (prim (m * m)) one Kθ * loD (m * m) one (K1 (lcmu (m * m)) k))
      (D1 (lcmu (m * m)) k * (hiN (prim (m * m)) one Kθ * loD (m * m) one (K1 (lcmu (m * m)) k) +
        m * loN (m * m) one (K1 (lcmu (m * m)) k) * hiD (prim (m * m)) one Kθ +
        hiD (prim (m * m)) one Kθ * loD (m * m) one (K1 (lcmu (m * m)) k))) := by
  have hm1 : Γ ⊢[PRAAx] m ≐ succ (pred m) := pos_of_one_le (le_trans (by ipra_le 1) hm2)
  have hP := pos_mul hm1 hm1
  have hP1 : Γ ⊢[PRAAx] le one (m * m) := one_le_of_pos' hP
  have hL1 : Γ ⊢[PRAAx] le one (lcmu (m * m)) := one_le_of_pos' (lcmu_pos _)
  have hPi1 : Γ ⊢[PRAAx] le one (prim (m * m)) := one_le_of_pos' (prim_pos _)
  have hPm := one_le_of_pos' (pw_pos' (Γ := Γ) hP m)
  have hY1 : Γ ⊢[PRAAx] le one (prim (m * m) * pw (m * m) m) := one_le_mul hPi1 hPm
  have w1 := RobinLogWidth.logI_width (le_refl one) hL1 (rr (lcmu (m * m)) k)
  have lp := lcm_primorial hm1
  have mono := lo_mono (le_refl one) hL1 (le_refl one) hY1
    (by ipra_le sl lp : Γ ⊢[PRAAx] le (lcmu (m * m) * one) ((prim (m * m) * pw (m * m) m) * one)) (K1 (lcmu (m * m)) k)
  have hpw := lo_pow (le_refl one) hPi1 hP1 (eq_add_of_le hP1) (K1 (lcmu (m * m)) k) m
  have hle := lo_le_hi_any (le_refl one) hPi1 (K1 (lcmu (m * m)) k) Kθ
  have e1 := err_G (k := k) hm2
  have e2 := err_R (Γ := Γ) (lcmu (m * m)) k
  have hR := pw_pos' (Γ := Γ) two_pos' (rr (lcmu (m * m)) k)
  have hM : Γ ⊢[PRAAx] two * pw two (rr (lcmu (m * m)) k) * loD (lcmu (m * m)) one (K1 (lcmu (m * m)) k) *
      loD (prim (m * m) * pw (m * m) m) one (K1 (lcmu (m * m)) k) * loD (prim (m * m)) one (K1 (lcmu (m * m)) k) *
      Rv (K1 (lcmu (m * m)) k) c3 ≐ succ (pred (two * pw two (rr (lcmu (m * m)) k) *
      loD (lcmu (m * m)) one (K1 (lcmu (m * m)) k) * loD (prim (m * m) * pw (m * m) m) one (K1 (lcmu (m * m)) k) *
      loD (prim (m * m)) one (K1 (lcmu (m * m)) k) * Rv (K1 (lcmu (m * m)) k) c3)) :=
    pos_mul (pos_mul (pos_mul (pos_mul (pos_mul two_pos' hR) (loD_pos (le_refl one) hL1 _))
      (loD_pos (le_refl one) hY1 _)) (loD_pos (le_refl one) hPi1 _))
      (pw_pos' (pos_of_one_le (by ipra_le 2 : Γ ⊢[PRAAx] le one (c3 : PTm n))) _)
  exact psi_alg hM w1 mono hpw hle e1 e2

/-! ## The two lower bounds -/

/-- `Θ = hi(log ∏_{p≤m²} p, K_θ) ≥ m²/4` for `m ≥ 16`, `K_θ ≥ 2`. -/
theorem theta_hi {m Kθ : PTm n} (hm : Γ ⊢[PRAAx] le (num 16) m) (hK : Γ ⊢[PRAAx] le k2 Kθ) :
    Γ ⊢[PRAAx] le (m * m * hiD (prim (m * m)) one Kθ) (num 4 * hiN (prim (m * m)) one Kθ) := by
  have t := LcmBridgeSide.theta_m16 hm hK
  have hPi1 : Γ ⊢[PRAAx] le one (prim (m * m)) := one_le_of_pos' (prim_pos _)
  have h := lo_le_hi_any (le_refl one) hPi1 Kθ Kθ
  have c : Γ ⊢[PRAAx] le (loD (prim (m * m)) one Kθ * (m * m * hiD (prim (m * m)) one Kθ))
      (loD (prim (m * m)) one Kθ * (num 4 * hiN (prim (m * m)) one Kθ)) := by
    ipra_le 𝔞 (hiD (prim (m * m)) one Kθ) * sl t + 4 * sl h
  have hp := loD_pos (Γ := Γ) (le_refl one) hPi1 Kθ
  exact mul_le_cancel (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _)) c)

abbrev four : PTm n := succ (succ (succ (succ zero)))

theorem pw2_4 : Γ ⊢[PRAAx] pw two (four : PTm n) ≐ (num 16 : PTm n) := by
  ipra_lc natEq (pw_succ (two : PTm n) (succ (succ (succ zero)))) + 2 *
    natEq (pw_succ (two : PTm n) (succ (succ zero))) + 4 * natEq (pw_succ (two : PTm n) (succ zero)) + 8 *
    natEq (pw_succ (two : PTm n) zero) + 16 * natEq (pw_zero (two : PTm n))

theorem pw_two_eight : Γ ⊢[PRAAx] pw two ((four : PTm n) + four) ≐ (num 256 : PTm n) :=
  (pw_add _ _ _).eqTrans ((congrMul pw2_4 pw2_4).eqTrans (by ipra_ring))

/-- `λ = lo(log m², K) ≥ 448/81` for `m ≥ 16`, `K ≥ 2`. -/
theorem lam_ge {m K : PTm n} (hm : Γ ⊢[PRAAx] le (num 16) m) (hK : Γ ⊢[PRAAx] le k2 K) :
    Γ ⊢[PRAAx] le (num 448 * loD (m * m) one K) (num 81 * loN (m * m) one K) := by
  have m2 := le_mul_mono hm hm
  have hP1 : Γ ⊢[PRAAx] le one (m * m) := by ipra_le sl m2 + 255
  have e8 := natEq (pw_two_eight (Γ := Γ))
  have h8 := eb_ge hP1 (by ipra_le sl m2 with -e8 : Γ ⊢[PRAAx] le (pw two (four + four)) (m * m))
  have lg := LcmBridgeTheta.lo_ge (le_refl one) hP1 hK
  ipra_le 56 * 𝔞 (loD (m * m) one K) * sl h8 + sl lg

end LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeDPsi
