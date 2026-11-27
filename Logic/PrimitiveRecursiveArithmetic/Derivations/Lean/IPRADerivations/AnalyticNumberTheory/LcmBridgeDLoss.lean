import IPRADerivations.AnalyticNumberTheory.LcmBridgeDPsi

/-!
# The loss `D(m²) ≤ 8/m` and the `ϑ`-form of the lcm-bridge transfer (`robin_ipra_research_2026-11-19`)

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/lcm_bridge.tex`, Lemma "Losses at a square
frontier", `D(P) = log log ψ(P) − log log ϑ(P) ≤ 8/m`, and Theorem "Explicit finite counterexample transfer":
"If `−log F(m²) > 12/m` then … `σ(N) > e^γ N log log N`."

On the names, for `m ≥ 16`, `P = m²`, `L = lcm(1, …, P)`:

* `Θ = hi(log ∏_{p≤P} p, K_θ)` (`K_θ ≥ 2`) is an upper name of `ϑ(P)`, and `H_θ = hi(log Θ, K_h)` (any `K_h`) an upper name of
  `log ϑ(P)`; `UH = hi(log ψ̂, K₃)` is the double-logarithm upper name used by the Robin upper end `U(L, k)`
  (`RobinUpperEnd`), with `ψ̂ = hi(log L, K₁)`;
* `dloss`: `UH ≤ (1 + 8/m)·H_θ` — the multiplicative form of `D(m²) ≤ 8/m`, since
  `log log ψ − log log ϑ = log(log ψ/log ϑ)`. The proof: `ψ̂ ≤ Θ + mλ + 1` (`LcmBridgeDPsi.psi_le`); the addition
  theorem gives `UH ≤ H_θ + (1 + 9^{−K₃})(mλ + 1)/Θ + 2^{−r}` (`uh_le`); `Θ ≥ m²/4` (`theta_hi`);
  `λ ≤ H_θ + 3/2 + 1/27` (`hth_le`, from `lo(m²) ≤ lo(m²/4) + lo(4) + 3/9^{K₁}` and `lo(4) ≤ 3/2`); `λ ≥ 448/81`
  (`lam_ge`); `num_final` closes the rational inequality;
* `transfer_theta`: if `∏_{p∣L}(1 − 1/p) · [e^γ]_hi · H_θ · (1 + 8/m) < 1 − 2/m`, then `NegR(L, k)`;
* `transfer_theta12`: the packet's form. If `F_hi(m²) = ∏(1 − 1/p)·[e^γ]_hi·H_θ < 1 − 12/m` (which gives
  `−log F(m²) > 12/m`), then `NegR(L, k)`, because `(1 − 12/m)(1 + 8/m) < 1 − 2/m`.

`[e^γ]_hi = EhN/EhD` is the exponential upper name of the Robin upper end at `(L, k)`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeDLoss

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipName (Rv)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipSum (one_le_mul one_le_of_pos' lo_val lo_sub_up)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipBound (lo_le_pred lo_four)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeDPsi (pw_mono_exp eb_ge psi_le theta_hi lam_ge pw_two_eight)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval
  (eb eb_spec Kp c3 loN loD hiN hiD lo_mono lo_le_hi_any loD_pos hiD_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinThreePos (rr K1)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinUpperEnd (C1 D1 K3 UHn UHd EhN EhD cndU Uup Uud NegR)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGammaInterval (k2)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (PP F₂)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds (two_pos')
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Numerical facts -/

theorem pw3_4 : Γ ⊢[PRAAx] pw c3 (succ (succ (succ (succ zero)))) ≐ (num 81 : PTm n) := by
  ipra_lc natEq (pw_succ (c3 : PTm n) (succ (succ (succ zero)))) + 3 * natEq (pw_succ (c3 : PTm n) (succ (succ zero))) +
    9 * natEq (pw_succ (c3 : PTm n) (succ zero)) + 27 * natEq (pw_succ (c3 : PTm n) zero) + 81 *
    natEq (pw_zero (c3 : PTm n))

/-- `9^K ≥ 81` for `K ≥ 2`. -/
theorem G81 {K : PTm n} (hK : Γ ⊢[PRAAx] le two K) : Γ ⊢[PRAAx] le (num 81) (Rv K c3) := by
  have h := pw_mono_exp (Γ := Γ) (p := c3) (by ipra_le 2)
    (by ipra_le 2 * sl hK : Γ ⊢[PRAAx] le (succ (succ (succ (succ zero)))) (two * K))
  exact le_congr pw3_4 (.eqRefl _) h

theorem le_lcm {m : PTm n} (hm2 : Γ ⊢[PRAAx] le two m) : Γ ⊢[PRAAx] le (m * m) (lcmu (m * m)) := by
  have hm1 : Γ ⊢[PRAAx] m ≐ succ (pred m) := pos_of_one_le (le_trans (by ipra_le 1) hm2)
  exact LcmBridgeTransfer.le_lcmu (pos_mul hm1 hm1)

/-- `16 m ≤ 2^r`, `r = k + e(L) + 17`. -/
theorem R_ge {m k : PTm n} (hm2 : Γ ⊢[PRAAx] le two m) : Γ ⊢[PRAAx] le (num 16 * m) (pw two (rr (lcmu (m * m)) k)) := by
  have hL1 : Γ ⊢[PRAAx] le one (lcmu (m * m)) := one_le_of_pos' (lcmu_pos _)
  have hmL := le_lcm hm2
  have s := Prf.andE₂ (eb_spec (le_refl one) hL1)
  have ea := natEq (pw_add (Γ := Γ) (two : PTm n) (succ (eb (lcmu (m * m)) one)) (succ (succ (succ (succ zero)))))
  have e16 := natEq (LcmBridgeDPsi.pw2_4 (Γ := Γ))
  have h := pw_mono_exp (Γ := Γ) (p := two) (by ipra_le 1)
    (by ipra_le 𝔞 k + 12 :
      Γ ⊢[PRAAx] le (succ (eb (lcmu (m * m)) one) + succ (succ (succ (succ zero)))) (rr (lcmu (m * m)) k))
  have em := natEq (pos_of_one_le (le_trans (by ipra_le 1) hm2) : Γ ⊢[PRAAx] m ≐ succ (pred m))
  ipra_le sl h + 16 * sl s + 16 * sl hmL + 16 * 𝔞 (m * pred m) + 16 with
    ea + 𝔞 (pw two (succ (eb (lcmu (m * m)) one))) * e16 + 16 * 𝔞 m * em

/-- `D₁ ≤ C₁`: the upper name of `log L` is at least `1`. -/
theorem C_ge_D {m k : PTm n} (hm : Γ ⊢[PRAAx] le (num 16) m) : Γ ⊢[PRAAx] le (D1 (lcmu (m * m)) k) (C1 (lcmu (m * m)) k) := by
  have hm2 : Γ ⊢[PRAAx] le two m := le_trans (by ipra_le 14) hm
  have hL1 : Γ ⊢[PRAAx] le one (lcmu (m * m)) := one_le_of_pos' (lcmu_pos _)
  have hK : Γ ⊢[PRAAx] le k2 (K1 (lcmu (m * m)) k) := by ipra_le 𝔞 k + 2 * 𝔞 (eb (lcmu (m * m)) one) + 19
  have lg := LcmBridgeTheta.lo_ge (le_refl one) hL1 hK
  have m2 := le_mul_mono hm hm
  have e8 := natEq (pw_two_eight (Γ := Γ))
  have h8 := eb_ge hL1 (le_trans (by ipra_le sl m2 with -e8 : Γ ⊢[PRAAx] le (pw two (LcmBridgeDPsi.four + LcmBridgeDPsi.four)) (m * m)) (le_lcm hm2))
  have hle := lo_le_hi_any (le_refl one) hL1 (K1 (lcmu (m * m)) k) (K1 (lcmu (m * m)) k)
  have c : Γ ⊢[PRAAx] le (num 81 * loD (lcmu (m * m)) one (K1 (lcmu (m * m)) k) * D1 (lcmu (m * m)) k)
      (num 81 * loD (lcmu (m * m)) one (K1 (lcmu (m * m)) k) * C1 (lcmu (m * m)) k) := by
    ipra_le 81 * sl hle + 𝔞 (D1 (lcmu (m * m)) k) * sl lg +
      56 * 𝔞 (D1 (lcmu (m * m)) k * loD (lcmu (m * m)) one (K1 (lcmu (m * m)) k)) * sl h8 +
      367 * 𝔞 (D1 (lcmu (m * m)) k * loD (lcmu (m * m)) one (K1 (lcmu (m * m)) k))
  have hp := pos_mul (pos_of_one_le (by ipra_le 80 : Γ ⊢[PRAAx] le one (num 81 : PTm n)))
    (loD_pos (Γ := Γ) (le_refl one) hL1 (K1 (lcmu (m * m)) k))
  exact mul_le_cancel_at hp c

/-! ## Abstract algebra -/

theorem uh_alg {UHn UHd pn pd On Od Xn Xd An Ad Cn Cd hn hd c1 c2 kk R G : PTm n}
    (hM : Γ ⊢[PRAAx] pd * Od * Xd * Ad * Cd ≐ succ (pred (pd * Od * Xd * Ad * Cd)))
    (b1 : Γ ⊢[PRAAx] le (R * (UHn * pd)) (R * (pn * UHd) + UHd * pd))
    (b2 : Γ ⊢[PRAAx] le (pn * Od) (On * pd)) (ev : Γ ⊢[PRAAx] Xn * Od ≐ On * Xd)
    (b3 : Γ ⊢[PRAAx] le (Xn * Ad * Cd * (c2 * G)) (An * Xd * Cd * (c2 * G) + Cn * Xd * Ad * (c2 * G) + kk * (Xd * Ad * Cd)))
    (b4 : Γ ⊢[PRAAx] le (Cn * c2 + c2 * Cd) (c1 * Cd)) (hc : Γ ⊢[PRAAx] c1 ≐ c2 + kk)
    (b5 : Γ ⊢[PRAAx] le (An * hd) (hn * Ad)) :
    Γ ⊢[PRAAx] le (UHn * hd * (c2 * G * R)) (hn * UHd * (c2 * G * R) + kk * (G + one) * R * UHd * hd + c2 * G * UHd * hd) := by
  have ev := natEq ev
  have hc := natEq hc
  have c : Γ ⊢[PRAAx] le (pd * Od * Xd * Ad * Cd * (UHn * hd * (c2 * G * R)))
      (pd * Od * Xd * Ad * Cd * (hn * UHd * (c2 * G * R) + kk * (G + one) * R * UHd * hd + c2 * G * UHd * hd)) := by
    ipra_le 𝔞 (Od * Xd * Ad * Cd * hd * c2 * G) * sl b1 + 𝔞 (Xd * Ad * Cd * hd * c2 * G * R * UHd) * sl b2 +
      𝔞 (pd * Od * hd * R * UHd) * sl b3 + 𝔞 (pd * Od * Xd * Ad * hd * G * R * UHd) * sl b4 +
      𝔞 (pd * Od * Xd * Cd * c2 * G * R * UHd) * sl b5 with
      (𝔞 Ad * 𝔞 Cd * 𝔞 G * 𝔞 R * 𝔞 UHd * 𝔞 c2 * 𝔞 hd * 𝔞 pd) * ev +
        (-𝔞 Ad * 𝔞 Cd * 𝔞 G * 𝔞 Od * 𝔞 R * 𝔞 UHd * 𝔞 Xd * 𝔞 hd * 𝔞 pd) * hc
  exact mul_le_cancel_at hM c

theorem hth_alg {Xn Xd ln ld Qn Qd Fn Fd Tn Td hn hd G : PTm n}
    (hM : Γ ⊢[PRAAx] Xd * Qd * Fd * G * Td ≐ succ (pred (Xd * Qd * Fd * G * Td)))
    (ev : Γ ⊢[PRAAx] Xn * ld ≐ ln * Xd)
    (sub : Γ ⊢[PRAAx] le (Xn * Qd * Fd * (one * G)) (Qn * Xd * Fd * (one * G) + Fn * Xd * Qd * (one * G) + num 3 * (Xd * Qd * Fd)))
    (four : Γ ⊢[PRAAx] le (two * Fn) (succ two * Fd)) (mono : Γ ⊢[PRAAx] le (Qn * Td) (Tn * Qd))
    (hle : Γ ⊢[PRAAx] le (Tn * hd) (hn * Td)) (hG : Γ ⊢[PRAAx] le (num 81) G) :
    Γ ⊢[PRAAx] le (num 54 * ln * hd) (num 54 * hn * ld + num 83 * ld * hd) := by
  have ev := natEq ev
  have c : Γ ⊢[PRAAx] le (Xd * Qd * Fd * G * Td * (num 54 * ln * hd)) (Xd * Qd * Fd * G * Td * (num 54 * hn * ld + num 83 * ld * hd)) := by
    ipra_le 54 * 𝔞 (ld * hd * Td) * sl sub + 27 * 𝔞 (ld * hd * Xd * Qd * G * Td) * sl four +
      54 * 𝔞 (ld * hd * Xd * Fd * G) * sl mono + 54 * 𝔞 (ld * Xd * Qd * Fd * G) * sl hle +
      2 * 𝔞 (ld * hd * Xd * Qd * Fd * Td) * sl hG with (54 * 𝔞 Fd * 𝔞 G * 𝔞 Qd * 𝔞 Td * 𝔞 hd) * ev
  exact mul_le_cancel_at hM c

theorem num_final {UHn UHd hn hd ln ld m tn td G R : PTm n}
    (hM : Γ ⊢[PRAAx] num 8503056 * m * tn * ld * G * R * td ≐ succ (pred (num 8503056 * m * tn * ld * G * R * td)))
    (U : Γ ⊢[PRAAx] le (UHn * hd * (td * ld * tn * G * R))
      (hn * UHd * (td * ld * tn * G * R) + (m * ln * td + td * ld) * td * (G + one) * R * UHd * hd + td * ld * tn * G * UHd * hd))
    (hG : Γ ⊢[PRAAx] le (num 81) G) (hR : Γ ⊢[PRAAx] le (num 16 * m) R) (hθ : Γ ⊢[PRAAx] le (m * m * td) (num 4 * tn))
    (F2 : Γ ⊢[PRAAx] le (num 54 * ln * hd) (num 54 * hn * ld + num 83 * ld * hd))
    (F3 : Γ ⊢[PRAAx] le (num 448 * ld) (num 81 * ln)) (hm : Γ ⊢[PRAAx] le (num 16) m) :
    Γ ⊢[PRAAx] le (UHn * hd * m) ((m + num 8) * hn * UHd) := by
  have c : Γ ⊢[PRAAx] le (num 8503056 * m * tn * ld * G * R * td * (UHn * hd * m))
      (num 8503056 * m * tn * ld * G * R * td * ((m + num 8) * hn * UHd)) := by
    ipra_le 8503056 * 𝔞 (m * m) * sl U + 104976 * 𝔞 (R * UHd * hd * m * m * td * td * (ld + ln * m)) * sl hG +
      531441 * 𝔞 (G * UHd * hd * ld * m * td * tn) * sl hR + 8608032 * 𝔞 (G * R * UHd * hd * td * (ld + ln * m)) * sl hθ +
      1259712 * 𝔞 (G * R * UHd * m * td * tn) * sl F2 + 414720 * 𝔞 (G * R * UHd * hd * m * td * tn) * sl F3 +
      2152008 * 𝔞 (G * R * UHd * hd * ld * td * tn) * sl hm + 78555015 * 𝔞 (G * R * UHd * hd * ld * m * td * tn)
  exact mul_le_cancel_at hM c

/-! ## The loss -/

/-- `Θ ≥ 1`: `hiD ≤ hiN` for the primorial name. -/
theorem td_le_tn {m Kθ : PTm n} (hm : Γ ⊢[PRAAx] le (num 16) m) (hK : Γ ⊢[PRAAx] le k2 Kθ) :
    Γ ⊢[PRAAx] le (hiD (prim (m * m)) one Kθ) (hiN (prim (m * m)) one Kθ) := by
  have hθ := theta_hi hm hK
  have m2 := le_mul_mono hm hm
  have m2td := le_mul_mono m2 (le_refl (hiD (prim (m * m)) one Kθ))
  refine .orE (lt_or_le (hiN (prim (m * m)) one Kθ) (hiD (prim (m * m)) one Kθ)) ?_ Prf.hyp0
  let C : List (Fm PTm n) := lt (hiN (prim (m * m)) one Kθ) (hiD (prim (m * m)) one Kθ) :: Γ
  have hlt : C ⊢[PRAAx] lt (hiN (prim (m * m)) one Kθ) (hiD (prim (m * m)) one Kθ) := Prf.hyp0
  have hθ' : C ⊢[PRAAx] _ := hθ.wk
  have m2td' : C ⊢[PRAAx] _ := m2td.wk
  have h : C ⊢[PRAAx] le (num 4) zero := by
    ipra_le 4 * sl hlt + sl hθ' + sl m2td' + 252 * 𝔞 (hiD (prim (m * m)) one Kθ)
  exact le_lt_absurd _ h (by ipra_le 3)

/-- `λ ≤ H_θ + 3/2 + 1/27`, with `λ = lo(log m², K₁)` and `H_θ = hi(log Θ, K_h)`. -/
theorem hth_le {m k Kθ Kh : PTm n} (hm : Γ ⊢[PRAAx] le (num 16) m) (hK : Γ ⊢[PRAAx] le k2 Kθ) :
    Γ ⊢[PRAAx] le (num 54 * loN (m * m) one (K1 (lcmu (m * m)) k) *
        hiD (hiN (prim (m * m)) one Kθ) (hiD (prim (m * m)) one Kθ) Kh)
      (num 54 * hiN (hiN (prim (m * m)) one Kθ) (hiD (prim (m * m)) one Kθ) Kh * loD (m * m) one (K1 (lcmu (m * m)) k) +
        num 83 * loD (m * m) one (K1 (lcmu (m * m)) k) * hiD (hiN (prim (m * m)) one Kθ) (hiD (prim (m * m)) one Kθ) Kh) := by
  have hθ := theta_hi hm hK
  have m2 := le_mul_mono hm hm
  have hPi1 : Γ ⊢[PRAAx] le one (prim (m * m)) := one_le_of_pos' (prim_pos _)
  have htd1 : Γ ⊢[PRAAx] le one (hiD (prim (m * m)) one Kθ) := one_le_of_pos' (hiD_pos (le_refl one) hPi1 Kθ)
  have htn := td_le_tn hm hK
  have h4 : Γ ⊢[PRAAx] le one (num 4 : PTm n) := by ipra_le 3
  have h4P : Γ ⊢[PRAAx] le (num 4) (m * m) := by ipra_le sl m2 + 252
  have hP1 : Γ ⊢[PRAAx] le one (m * m) := by ipra_le sl m2 + 255
  have mono := lo_mono h4 h4P htd1 htn (by ipra_le sl hθ) (K1 (lcmu (m * m)) k)
  have hle := lo_le_hi_any htd1 htn (K1 (lcmu (m * m)) k) Kh
  have sub := lo_sub_up (a := m * m) (b := num 4) (c1 := num 4) (c2 := one) (k := num 3) h4 h4P (le_refl one)
    (by ipra_ring) (K1 (lcmu (m * m)) k)
  have ev := lo_val (a := (m * m) * num 4) (b := num 4 * one) (a' := m * m) (b' := one) (by ipra_le 3)
    (by ipra_le 4 * sl m2 + 1020) (le_refl one) hP1 (by ipra_ring) (K1 (lcmu (m * m)) k)
  have four := lo_four (Γ := Γ) (K1 (lcmu (m * m)) k)
  have hG := G81 (Γ := Γ) (K := K1 (lcmu (m * m)) k) (by ipra_le 𝔞 k + 2 * 𝔞 (eb (lcmu (m * m)) one) + 19)
  have hM : Γ ⊢[PRAAx] loD (m * m * num 4) (num 4 * one) (K1 (lcmu (m * m)) k) * loD (m * m) (num 4) (K1 (lcmu (m * m)) k) *
      loD (num 4) one (K1 (lcmu (m * m)) k) * Rv (K1 (lcmu (m * m)) k) c3 *
      loD (hiN (prim (m * m)) one Kθ) (hiD (prim (m * m)) one Kθ) (K1 (lcmu (m * m)) k) ≐
      succ (pred (loD (m * m * num 4) (num 4 * one) (K1 (lcmu (m * m)) k) * loD (m * m) (num 4) (K1 (lcmu (m * m)) k) *
      loD (num 4) one (K1 (lcmu (m * m)) k) * Rv (K1 (lcmu (m * m)) k) c3 *
      loD (hiN (prim (m * m)) one Kθ) (hiD (prim (m * m)) one Kθ) (K1 (lcmu (m * m)) k))) :=
    pos_mul (pos_mul (pos_mul (pos_mul (loD_pos (by ipra_le 3) (by ipra_le 4 * sl m2 + 1020) _)
      (loD_pos h4 h4P _)) (loD_pos (le_refl one) h4 _)) (pos_of_one_le (by ipra_le sl hG + 80)))
      (loD_pos htd1 htn _)
  exact hth_alg hM ev sub four mono hle hG

/-! ## Names used in the statements -/

/-- `Θ = hi(log ∏_{p≤m²} p, K_θ)`. -/
abbrev tN (m Kθ : PTm n) : PTm n := hiN (prim (m * m)) one Kθ
abbrev tD (m Kθ : PTm n) : PTm n := hiD (prim (m * m)) one Kθ
/-- `λ = lo(log m², K₁)`. -/
abbrev lN (m k : PTm n) : PTm n := loN (m * m) one (K1 (lcmu (m * m)) k)
abbrev lD (m k : PTm n) : PTm n := loD (m * m) one (K1 (lcmu (m * m)) k)
/-- `H_θ = hi(log Θ, K_h)`. -/
abbrev hN (m Kθ Kh : PTm n) : PTm n := hiN (tN m Kθ) (tD m Kθ) Kh
abbrev hD (m Kθ Kh : PTm n) : PTm n := hiD (tN m Kθ) (tD m Kθ) Kh
/-- `Θ' = Θ + mλ + 1 = Tn'/Td'`. -/
abbrev Tn' (m k Kθ : PTm n) : PTm n := tN m Kθ * lD m k + m * lN m k * tD m Kθ + tD m Kθ * lD m k
abbrev Td' (m k Kθ : PTm n) : PTm n := tD m Kθ * lD m k

/-- Chain B: `UH ≤ H_θ + (1 + 9^{−K₃})(mλ + 1)/Θ + 2^{−r}`, cleared. -/
theorem uh_le {m k Kθ Kh : PTm n} (hm : Γ ⊢[PRAAx] le (num 16) m) (hK : Γ ⊢[PRAAx] le k2 Kθ) :
    Γ ⊢[PRAAx] le (UHn (lcmu (m * m)) k * hD m Kθ Kh *
        (tD m Kθ * lD m k * tN m Kθ * Rv (K3 (lcmu (m * m)) k) c3 * pw two (rr (lcmu (m * m)) k)))
      (hN m Kθ Kh * UHd (lcmu (m * m)) k *
          (tD m Kθ * lD m k * tN m Kθ * Rv (K3 (lcmu (m * m)) k) c3 * pw two (rr (lcmu (m * m)) k)) +
        (m * lN m k * tD m Kθ + tD m Kθ * lD m k) * tD m Kθ * (Rv (K3 (lcmu (m * m)) k) c3 + one) *
          pw two (rr (lcmu (m * m)) k) * UHd (lcmu (m * m)) k * hD m Kθ Kh +
        tD m Kθ * lD m k * tN m Kθ * Rv (K3 (lcmu (m * m)) k) c3 * UHd (lcmu (m * m)) k * hD m Kθ Kh) := by
  have hm2 : Γ ⊢[PRAAx] le two m := le_trans (by ipra_le 14) hm
  have hPi1 : Γ ⊢[PRAAx] le one (prim (m * m)) := one_le_of_pos' (prim_pos _)
  have htd1 : Γ ⊢[PRAAx] le one (tD m Kθ) := one_le_of_pos' (hiD_pos (le_refl one) hPi1 Kθ)
  have htn := td_le_tn hm hK
  have m2 := le_mul_mono hm hm
  have hP1 : Γ ⊢[PRAAx] le one (m * m) := by ipra_le sl m2 + 255
  have hld1 : Γ ⊢[PRAAx] le one (lD m k) := one_le_of_pos' (loD_pos (le_refl one) hP1 _)
  have hL1 : Γ ⊢[PRAAx] le one (lcmu (m * m)) := one_le_of_pos' (lcmu_pos _)
  have hD1 : Γ ⊢[PRAAx] le one (D1 (lcmu (m * m)) k) := one_le_of_pos' (hiD_pos (le_refl one) hL1 _)
  have cge := C_ge_D (k := k) hm
  have psi := psi_le (k := k) (Kθ := Kθ) hm2
  have hTd : Γ ⊢[PRAAx] le one (Td' m k Kθ) := one_le_mul htd1 hld1
  have hTT : Γ ⊢[PRAAx] le (Td' m k Kθ) (Tn' m k Kθ) := by ipra_le 𝔞 (tN m Kθ * lD m k) + 𝔞 (m * lN m k * tD m Kθ)
  have hc2 : Γ ⊢[PRAAx] le one (Td' m k Kθ * tN m Kθ) := one_le_mul hTd (le_trans htd1 htn)
  have hc : Γ ⊢[PRAAx] Tn' m k Kθ * tD m Kθ ≐ Td' m k Kθ * tN m Kθ + (m * lN m k * tD m Kθ + tD m Kθ * lD m k) * tD m Kθ := by
    ipra_ring
  have hc12 : Γ ⊢[PRAAx] le (Td' m k Kθ * tN m Kθ) (Tn' m k Kθ * tD m Kθ) := le_of_eq_add hc
  have b1 := RobinLogWidth.logI_width hD1 cge (rr (lcmu (m * m)) k)
  have b2 := lo_mono hD1 cge hTd hTT (by ipra_le sl psi :
    Γ ⊢[PRAAx] le (C1 (lcmu (m * m)) k * Td' m k Kθ) (Tn' m k Kθ * D1 (lcmu (m * m)) k)) (K3 (lcmu (m * m)) k)
  have b3 := lo_sub_up htd1 htn hc2 hc (K3 (lcmu (m * m)) k)
  have hxc1 : Γ ⊢[PRAAx] le one (tD m Kθ * (Td' m k Kθ * tN m Kθ)) := one_le_mul htd1 hc2
  have hxc2 : Γ ⊢[PRAAx] le (tD m Kθ * (Td' m k Kθ * tN m Kθ)) (tN m Kθ * (Tn' m k Kθ * tD m Kθ)) := le_mul_mono htn hc12
  have ev := lo_val hxc1 hxc2 hTd hTT (by ipra_ring) (K3 (lcmu (m * m)) k)
  have b4 := lo_le_pred hc2 hc12 (K3 (lcmu (m * m)) k)
  have b5 := lo_le_hi_any htd1 htn (K3 (lcmu (m * m)) k) Kh
  have hM : Γ ⊢[PRAAx] loD (C1 (lcmu (m * m)) k) (D1 (lcmu (m * m)) k) (K3 (lcmu (m * m)) k) *
      loD (Tn' m k Kθ) (Td' m k Kθ) (K3 (lcmu (m * m)) k) *
      loD (tN m Kθ * (Tn' m k Kθ * tD m Kθ)) (tD m Kθ * (Td' m k Kθ * tN m Kθ)) (K3 (lcmu (m * m)) k) *
      loD (tN m Kθ) (tD m Kθ) (K3 (lcmu (m * m)) k) *
      loD (Tn' m k Kθ * tD m Kθ) (Td' m k Kθ * tN m Kθ) (K3 (lcmu (m * m)) k) ≐
      succ (pred (loD (C1 (lcmu (m * m)) k) (D1 (lcmu (m * m)) k) (K3 (lcmu (m * m)) k) *
      loD (Tn' m k Kθ) (Td' m k Kθ) (K3 (lcmu (m * m)) k) *
      loD (tN m Kθ * (Tn' m k Kθ * tD m Kθ)) (tD m Kθ * (Td' m k Kθ * tN m Kθ)) (K3 (lcmu (m * m)) k) *
      loD (tN m Kθ) (tD m Kθ) (K3 (lcmu (m * m)) k) *
      loD (Tn' m k Kθ * tD m Kθ) (Td' m k Kθ * tN m Kθ) (K3 (lcmu (m * m)) k))) :=
    pos_mul (pos_mul (pos_mul (pos_mul (loD_pos hD1 cge _) (loD_pos hTd hTT _)) (loD_pos hxc1 hxc2 _))
      (loD_pos htd1 htn _)) (loD_pos hc2 hc12 _)
  exact uh_alg hM b1 b2 ev b3 b4 hc b5

/-- `lcm_bridge.tex`, `D(m²) ≤ 8/m`, multiplicative form on the names: for `m ≥ 16`, `K_θ ≥ 2` and every `K_h`,
`UH ≤ (1 + 8/m) H_θ`, cleared: `UHn · hD · m ≤ (m + 8) · hN · UHd`. -/
theorem dloss {m k Kθ Kh : PTm n} (hm : Γ ⊢[PRAAx] le (num 16) m) (hK : Γ ⊢[PRAAx] le k2 Kθ) :
    Γ ⊢[PRAAx] le (UHn (lcmu (m * m)) k * hD m Kθ Kh * m) ((m + num 8) * hN m Kθ Kh * UHd (lcmu (m * m)) k) := by
  have hm2 : Γ ⊢[PRAAx] le two m := le_trans (by ipra_le 14) hm
  have hPi1 : Γ ⊢[PRAAx] le one (prim (m * m)) := one_le_of_pos' (prim_pos _)
  have htd1 : Γ ⊢[PRAAx] le one (tD m Kθ) := one_le_of_pos' (hiD_pos (le_refl one) hPi1 Kθ)
  have htn := td_le_tn hm hK
  have m2 := le_mul_mono hm hm
  have hP1 : Γ ⊢[PRAAx] le one (m * m) := by ipra_le sl m2 + 255
  have U := uh_le (Kh := Kh) (k := k) hm hK
  have hG := G81 (Γ := Γ) (K := K3 (lcmu (m * m)) k) (by ipra_le 𝔞 k + 𝔞 (eb (C1 (lcmu (m * m)) k) (D1 (lcmu (m * m)) k)) +
    𝔞 (eb (lcmu (m * m)) one) + 19)
  have hR := R_ge (k := k) hm2
  have hθ := theta_hi hm hK
  have F2 := hth_le (k := k) (Kh := Kh) hm hK
  have F3 := lam_ge hm (by ipra_le 𝔞 k + 2 * 𝔞 (eb (lcmu (m * m)) one) + 19 :
    Γ ⊢[PRAAx] le k2 (K1 (lcmu (m * m)) k))
  have hld := loD_pos (Γ := Γ) (le_refl one) hP1 (K1 (lcmu (m * m)) k)
  have hM : Γ ⊢[PRAAx] num 8503056 * m * tN m Kθ * lD m k * Rv (K3 (lcmu (m * m)) k) c3 * pw two (rr (lcmu (m * m)) k) *
      tD m Kθ ≐ succ (pred (num 8503056 * m * tN m Kθ * lD m k * Rv (K3 (lcmu (m * m)) k) c3 *
        pw two (rr (lcmu (m * m)) k) * tD m Kθ)) :=
    pos_mul (pos_mul (pos_mul (pos_mul (pos_mul (pos_mul (pos_of_one_le (by ipra_le 8503055))
      (pos_of_one_le (le_trans (by ipra_le 1) hm2))) (pos_of_one_le (le_trans htd1 htn))) hld)
      (pos_of_one_le (by ipra_le sl hG + 80))) (pw_pos' two_pos' _)) (pos_of_one_le htd1)
  exact num_final hM U hG hR hθ F2 F3 hm

/-! ## The transfer through `ϑ(m²)` -/

theorem tr_alg {m Φ Pi E Ed UHn UHd Hn Hd : PTm n} (hU : Γ ⊢[PRAAx] UHd ≐ succ (pred UHd))
    (dl : Γ ⊢[PRAAx] le (UHn * Hd * m) ((m + num 8) * Hn * UHd))
    (H : Γ ⊢[PRAAx] lt (m * Φ * E * Hn * (m + num 8) + two * Pi * Ed * Hd * m) (m * Pi * Ed * Hd * m)) :
    Γ ⊢[PRAAx] lt ((Hd * m) * (m * Φ * (E * UHn) + two * Pi * (Ed * UHd))) ((Hd * m) * (m * Pi * (Ed * UHd))) := by
  have eU := natEq hU
  ipra_le 𝔞 (m * Φ * E) * sl dl + 𝔞 UHd * sl H + 𝔞 (pred UHd) with eU

/-- The finite counterexample transfer through `ϑ(m²)`: for `m ≥ 16`, `K_θ ≥ 2`, any `K_h` and `L = lcm(1, …, m²)`, if
`∏_{p∣L}(1 − 1/p) · [e^γ]_hi · H_θ · (1 + 8/m) < 1 − 2/m`, then `NegR(L, k)`. -/
theorem transfer_theta {m k Kθ Kh : PTm n} (hm : Γ ⊢[PRAAx] le (num 16) m) (hK : Γ ⊢[PRAAx] le k2 Kθ)
    (H : Γ ⊢[PRAAx] lt (m * PP F₂ (lcmu (m * m)) * EhN (lcmu (m * m)) k * hN m Kθ Kh * (m + num 8) +
        two * PP (var 0) (lcmu (m * m)) * EhD (lcmu (m * m)) k * hD m Kθ Kh * m)
      (m * PP (var 0) (lcmu (m * m)) * EhD (lcmu (m * m)) k * hD m Kθ Kh * m)) :
    Γ ⊢[PRAAx] NegR (lcmu (m * m)) k := by
  have hm2 : Γ ⊢[PRAAx] le two m := le_trans (by ipra_le 14) hm
  have hL1 : Γ ⊢[PRAAx] le one (lcmu (m * m)) := one_le_of_pos' (lcmu_pos _)
  have cge := C_ge_D (k := k) hm
  have hD1 : Γ ⊢[PRAAx] le one (D1 (lcmu (m * m)) k) := one_le_of_pos' (hiD_pos (le_refl one) hL1 _)
  -- the positive branch of the upper end
  have e1 : Γ ⊢[PRAAx] cndU (lcmu (m * m)) k ≐ zero := (Mobius.congrSg cge).eqTrans Signum.sg_zero
  have e2 : Γ ⊢[PRAAx] monus one (cndU (lcmu (m * m)) k) ≐ one := (congrMonus (.eqRefl _) e1).eqTrans (monus_zero _)
  have eUp : Γ ⊢[PRAAx] Uup (lcmu (m * m)) k ≐ EhN (lcmu (m * m)) k * UHn (lcmu (m * m)) k :=
    (congrMul e2 (.eqRefl _)).eqTrans (one_mul _)
  have eUd : Γ ⊢[PRAAx] Uud (lcmu (m * m)) k ≐ EhD (lcmu (m * m)) k * UHd (lcmu (m * m)) k :=
    (congrAdd ((congrMul e2 (.eqRefl _)).eqTrans (one_mul _)) ((congrMul e1 (.eqRefl _)).eqTrans (zero_mul _))).eqTrans
      (add_zero _)
  have hU := hiD_pos (Γ := Γ) hD1 cge (K3 (lcmu (m * m)) k)
  have dl := dloss (Kh := Kh) (k := k) hm hK
  have c := tr_alg hU dl H
  have hPi1 : Γ ⊢[PRAAx] le one (prim (m * m)) := one_le_of_pos' (prim_pos _)
  have htd1 : Γ ⊢[PRAAx] le one (tD m Kθ) := one_le_of_pos' (hiD_pos (le_refl one) hPi1 Kθ)
  have htn := td_le_tn hm hK
  have hHm := pos_mul (hiD_pos htd1 htn Kh) (pos_of_one_le (le_trans (by ipra_le 1) hm2))
  have c' := LcmBridgeTransfer.lt_cancel hHm c
  exact LcmBridgeTransfer.transfer hm2
    (lt_congr (congrAdd (congrMul (.eqRefl _) eUp.eqSymm) (congrMul (.eqRefl _) eUd.eqSymm))
      (congrMul (.eqRefl _) eUd.eqSymm) c')

theorem t12_alg {m Φ Pi E Ed Hn Hd : PTm n} (H : Γ ⊢[PRAAx] lt (m * Φ * E * Hn + num 12 * Pi * Ed * Hd) (m * Pi * Ed * Hd)) :
    Γ ⊢[PRAAx] lt (m * Φ * E * Hn * (m + num 8) + two * Pi * Ed * Hd * m) (m * Pi * Ed * Hd * m) := by
  ipra_le 𝔞 (m + num 8) * sl H + 𝔞 ((two * m + num 96) * Pi * Ed * Hd) + 𝔞 m + 7

/-- The packet's form of the transfer: if `F_hi(m²) = ∏_{p∣L}(1 − 1/p)·[e^γ]_hi·H_θ < 1 − 12/m` — so that
`−log F(m²) > −log(1 − 12/m) ≥ 12/m` — then `NegR(L, k)`; `(1 − 12/m)(1 + 8/m) < 1 − 2/m`. -/
theorem transfer_theta12 {m k Kθ Kh : PTm n} (hm : Γ ⊢[PRAAx] le (num 16) m) (hK : Γ ⊢[PRAAx] le k2 Kθ)
    (H : Γ ⊢[PRAAx] lt (m * PP F₂ (lcmu (m * m)) * EhN (lcmu (m * m)) k * hN m Kθ Kh +
        num 12 * PP (var 0) (lcmu (m * m)) * EhD (lcmu (m * m)) k * hD m Kθ Kh)
      (m * PP (var 0) (lcmu (m * m)) * EhD (lcmu (m * m)) k * hD m Kθ Kh)) :
    Γ ⊢[PRAAx] NegR (lcmu (m * m)) k :=
  transfer_theta hm hK (t12_alg H)

end LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeDLoss
