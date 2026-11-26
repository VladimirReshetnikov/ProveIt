import IPRADerivations.AnalyticNumberTheory.RobinWidthNum
import IPRADerivations.AnalyticNumberTheory.RobinLipWidth
import IPRADerivations.AnalyticNumberTheory.RobinUpperEnd
import IPRADerivations.Core.Header

/-!
# The width of the Robin interval `[L(n, k), U(n, k)]` (`robin_ipra_research_2026-11-19`, §"Composing the double logarithm")

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/report.tex`: "Multiply it by the `[1, 3]`-bounded
enclosure of `e^γ` … The resulting rational interval `[L(n, k), U(n, k)]` contains `B(n)` and has width at most
`(n + 12)2^{−r} ≤ 2^{−k}`."

For `n ≥ 4` (so that `log n ≥ 1` on the names and both programs take their positive branch), with the programs `L(n, k)`
of `RobinThreePos` and `U(n, k)` of `RobinUpperEnd`:

* `w1`: the double logarithm, `UH ≤ LL + 3·2^{−r}` (`RobinLipWidth.comp_width` at `K₃`, the nesting `lo(K₃) ≤ hi(K₂)`,
  the width at `K₂`, and `(x' − x)/x ≤ 2^{−r}` from the width at `K₁`);
* `exp_part`: `T_{K_e}(γ_hi) ≤ E_{K_e}(γ_lo) + 2/(K_e+1)! + 3(9t/Z + 1/(12(1+t)²))` (`RobinExpName.exp_tail`,
  `RobinExpWidth.exp_lip`, `RobinUpperEnd.e_le_three`, `RobinGammaWidth.gamma_width`), and `T ≤ 5`, `E ≤ T`;
* `ll_le`: `LL ≤ n`;
* `width`: `U(n, k) − L(n, k) ≤ 2^{−k}`, cleared: `2^k·Uup·Ld ≤ 2^k·Lp·Uud + Uud·Ld`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinWidthCompose

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma (Pv Pt Qt)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName (frac_trans)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinExpName
  (Ev Ed Fv Tn Td F_succ e_up e_mono exp_tail Ed_pos Td_pos Ev_congr Ed_congr Tn_congr Td_congr F_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGammaInterval (An Ad k2)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGammaUpper (gloN gloD ghiN ghiD gamma_consistent gamma_hi_le)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGammaWidth (Zg gamma_width)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinExpWidth (exp_lip)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinWidthNum (n_one n_two n_three n_four num_alg)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipWidth (comp_width)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipBound (lo_le_pred pw_two_two)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipSum (one_le_of_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeDPsi (eb_ge)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval (eb Kp loN loD hiN hiD lo_le_hi_any loD_pos hiD_pos c3)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinThreePos
  (rr K1 A1 B1 K2 LLn LLd tg Kg gN gD Ke EN ED cnd Lp Lm Ld)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinUpperEnd
  (C1 D1 K3 UHn UHd gHn gHd EhN EhD cndU Uup Uum Uud ghiD_pos gloD_pos e_le_three)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds (two_pos')
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Abstract algebra -/

theorem fin_alg {TN TD EN' ED' HN HD LN LD N R P X Y : PTm n} (hM : Γ ⊢[PRAAx] Y * R ≐ succ (pred (Y * R)))
    (h1 : Γ ⊢[PRAAx] le (HN * LD * R) (LN * HD * R + num 3 * HD * LD))
    (h2 : Γ ⊢[PRAAx] le (TN * ED' * Y) (EN' * TD * Y + X * TD * ED')) (h3 : Γ ⊢[PRAAx] le TN (num 5 * TD))
    (h4 : Γ ⊢[PRAAx] le LN (N * LD)) (h5 : Γ ⊢[PRAAx] le (EN' * TD) (TN * ED'))
    (h6 : Γ ⊢[PRAAx] le (N * X * R * P + num 15 * Y * P) (Y * R)) :
    Γ ⊢[PRAAx] le (P * (TN * HN) * (ED' * LD)) (P * (EN' * LN) * (TD * HD) + (TD * HD) * (ED' * LD)) := by
  have c : Γ ⊢[PRAAx] le (Y * R * (P * (TN * HN) * (ED' * LD))) (Y * R * (P * (EN' * LN) * (TD * HD) + (TD * HD) * (ED' * LD))) := by
    ipra_le 𝔞 (TD * HD * ED' * LD) * sl h6 + 𝔞 (P * HD * LD * N * R) * sl h2 + 𝔞 (P * HD * Y * R) * sl h4 * sl h5 +
      𝔞 (P * ED' * Y * TN) * sl h1 + 3 * 𝔞 (P * HD * ED' * LD * Y) * sl h3
  exact mul_le_cancel (le_congr (congrMul hM (.eqRefl _)) (congrMul hM (.eqRefl _)) c)

theorem w1_alg {HN HD aN aD hN2 hD2 LN LD A1' D1' Dx R : PTm n}
    (hM : Γ ⊢[PRAAx] aD * hD2 * A1' * D1' ≐ succ (pred (aD * hD2 * A1' * D1')))
    (comp : Γ ⊢[PRAAx] le (R * (HN * aD * (A1' * D1'))) (R * (aN * HD * (A1' * D1') + Dx * aD * HD) + HD * aD * (A1' * D1')))
    (lh : Γ ⊢[PRAAx] le (aN * hD2) (hN2 * aD)) (w2 : Γ ⊢[PRAAx] le (R * (hN2 * LD)) (R * (LN * hD2) + hD2 * LD))
    (wx : Γ ⊢[PRAAx] le (R * Dx) (D1' * A1')) :
    Γ ⊢[PRAAx] le (HN * LD * R) (LN * HD * R + num 3 * HD * LD) := by
  have c : Γ ⊢[PRAAx] le (aD * hD2 * A1' * D1' * (HN * LD * R)) (aD * hD2 * A1' * D1' * (LN * HD * R + num 3 * HD * LD)) := by
    ipra_le 𝔞 (LD * hD2) * sl comp + 𝔞 (HD * LD * R * A1' * D1') * sl lh + 𝔞 (HD * aD * A1' * D1') * sl w2 +
      𝔞 (HD * LD * aD * hD2) * sl wx
  exact mul_le_cancel (le_congr (congrMul hM (.eqRefl _)) (congrMul hM (.eqRefl _)) c)

theorem wx_alg {C B A D Dx R : PTm n} (w0 : Γ ⊢[PRAAx] le (R * (C * B)) (R * (A * D) + D * B))
    (hBA : Γ ⊢[PRAAx] le B A) (hDx : Γ ⊢[PRAAx] C * B ≐ A * D + Dx) : Γ ⊢[PRAAx] le (R * Dx) (D * A) := by
  have e := natEq hDx
  ipra_le sl w0 + 𝔞 D * sl hBA with 𝔞 R * e

theorem x2_alg {C B A D R : PTm n} (hR : Γ ⊢[PRAAx] R ≐ succ (pred R)) (w0 : Γ ⊢[PRAAx] le (R * (C * B)) (R * (A * D) + D * B))
    (hBA : Γ ⊢[PRAAx] le B A) : Γ ⊢[PRAAx] le (C * B) (two * (A * D)) := by
  have e := natEq hR
  have c : Γ ⊢[PRAAx] le (R * (C * B)) (R * (two * (A * D))) := by
    ipra_le sl w0 + 𝔞 D * sl hBA + 𝔞 (pred R * D * A) with (𝔞 D * 𝔞 A) * e
  exact mul_le_cancel (le_congr (congrMul hR (.eqRefl _)) (congrMul hR (.eqRefl _)) c)

theorem tail_alg {E F Fp Q0 Q1 P1 q K : PTm n} (eF : Γ ⊢[PRAAx] Fp ≐ succ K * F) (eQ : Γ ⊢[PRAAx] Q1 ≐ Q0 * q)
    (w : Γ ⊢[PRAAx] le P1 Q1) :
    Γ ⊢[PRAAx] le ((succ K * q * E + two * P1) * (F * Q0) * Fp) (E * (Fp * Q1) * Fp + two * (Fp * Q1) * (F * Q0)) := by
  have eF := natEq eF
  have eQ := natEq eQ
  ipra_le 2 * 𝔞 (F * Q0 * Fp) * sl w with
    ((-𝔞 E * 𝔞 F * 𝔞 K * 𝔞 Q0 * 𝔞 q) + (𝔞 E * 𝔞 F * 𝔞 K * 𝔞 Q1) + (-𝔞 E * 𝔞 F * 𝔞 Q0 * 𝔞 q) + (𝔞 E * 𝔞 F * 𝔞 Q1) + (𝔞 E * 𝔞 Fp * 𝔞 Q1)) * eF + ((𝔞 E * (𝔞 F) ^ 2 * (𝔞 K) ^ 2) + (2 * 𝔞 E * (𝔞 F) ^ 2 * 𝔞 K) + (𝔞 E * (𝔞 F) ^ 2)) * eQ

theorem gw_alg {A B C D d Z W1 W2 : PTm n} (hd : Γ ⊢[PRAAx] A * B ≐ C * D + d)
    (gw : Γ ⊢[PRAAx] le (A * B * Z) (C * D * Z + W1 + W2)) : Γ ⊢[PRAAx] le (d * Z) (W1 + W2) := by
  have e := natEq hd
  ipra_le sl gw with 𝔞 Z * e

theorem exp_alg {TN TD Eu El F Q Qp q qp d K1 Eu0 F0 Q0 Fp Z W : PTm n}
    (hM : Γ ⊢[PRAAx] Q * Q0 ≐ succ (pred (Q * Q0)))
    (tail : Γ ⊢[PRAAx] le (TN * (F * Q) * Fp) (Eu * TD * Fp + two * TD * (F * Q)))
    (lip : Γ ⊢[PRAAx] le (Eu * Qp * q * qp) (El * Q * q * qp + d * K1 * Eu0 * q * Qp))
    (three : Γ ⊢[PRAAx] le Eu0 (num 3 * (F0 * Q0))) (gw : Γ ⊢[PRAAx] le (d * Z) W)
    (eF : Γ ⊢[PRAAx] F ≐ K1 * F0) (eQ : Γ ⊢[PRAAx] Q ≐ Q0 * q) :
    Γ ⊢[PRAAx] le (TN * (F * Qp) * (Fp * Z * q * qp)) (El * TD * (Fp * Z * q * qp) + (two * (Z * q * qp) + num 3 * W * Fp) * TD * (F * Qp)) := by
  have eF := natEq eF
  have eQ := natEq eQ
  have c : Γ ⊢[PRAAx] le (Q * Q0 * (TN * (F * Qp) * (Fp * Z * q * qp)))
      (Q * Q0 * (El * TD * (Fp * Z * q * qp) + (two * (Z * q * qp) + num 3 * W * Fp) * TD * (F * Qp))) := by
    ipra_le 𝔞 (Q0 * Z * q * qp * Qp) * sl tail + 𝔞 (Q0 * Fp * Z * TD) * sl lip + 𝔞 (Q * Fp * Z * TD * K1 * Qp * d) * sl three +
      3 * 𝔞 (Q * Q0 * Fp * TD * F * Qp) * sl gw with
      (3 * 𝔞 Fp * 𝔞 Q * 𝔞 Q0 * 𝔞 Qp * 𝔞 TD * 𝔞 Z * 𝔞 d) * eF + (𝔞 Eu0 * 𝔞 Fp * 𝔞 K1 * 𝔞 Qp * 𝔞 TD * 𝔞 Z * 𝔞 d) * eQ
  exact mul_le_cancel (le_congr (congrMul hM (.eqRefl _)) (congrMul hM (.eqRefl _)) c)

theorem t5_alg {TN TD Eu F Q Fp : PTm n} (hM : Γ ⊢[PRAAx] F * Q * Fp ≐ succ (pred (F * Q * Fp)))
    (tail : Γ ⊢[PRAAx] le (TN * (F * Q) * Fp) (Eu * TD * Fp + two * TD * (F * Q)))
    (e3 : Γ ⊢[PRAAx] le Eu (num 3 * (F * Q))) (hFp : Γ ⊢[PRAAx] le one Fp) : Γ ⊢[PRAAx] le TN (num 5 * TD) := by
  have c : Γ ⊢[PRAAx] le (F * Q * Fp * TN) (F * Q * Fp * (num 5 * TD)) := by
    ipra_le sl tail + 𝔞 (TD * Fp) * sl e3 + 2 * 𝔞 (TD * F * Q) * sl hFp
  exact mul_le_cancel (le_congr (congrMul hM (.eqRefl _)) (congrMul hM (.eqRefl _)) c)

theorem ll_alg {LN LD A B N : PTm n} (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (s1 : Γ ⊢[PRAAx] le (LN * B + B * LD) (A * LD))
    (s2 : Γ ⊢[PRAAx] le (A * one + one * B) (N * B)) : Γ ⊢[PRAAx] le LN (N * LD) := by
  have c : Γ ⊢[PRAAx] le (B * LN) (B * (N * LD)) := by ipra_le sl s1 + 𝔞 LD * sl s2 + 2 * 𝔞 (B * LD)
  exact mul_le_cancel (le_congr (congrMul hB (.eqRefl _)) (congrMul hB (.eqRefl _)) c)

/-! ## The program at `n ≥ 4` -/

abbrev Kq (N k : PTm n) : PTm n := num 31 + two * rr N k

theorem ke_eq (N k : PTm n) : Γ ⊢[PRAAx] Ke N k ≐ succ (Kq N k) := by ipra_ring

theorem n_one' {N : PTm n} (hN : Γ ⊢[PRAAx] le (num 4) N) : Γ ⊢[PRAAx] le one N := by ipra_le sl hN + 3

/-- `B₁ ≤ A₁`: the lower name of `log n` is at least `1` for `n ≥ 4`. -/
theorem hBA {N k : PTm n} (hN : Γ ⊢[PRAAx] le (num 4) N) : Γ ⊢[PRAAx] le (B1 N k) (A1 N k) := by
  have hN1 := n_one' hN
  have hK : Γ ⊢[PRAAx] le k2 (K1 N k) := by ipra_le 𝔞 k + 2 * 𝔞 (eb N one) + 19
  have lg := LcmBridgeTheta.lo_ge (le_refl one) hN1 hK
  have e4 := natEq (pw_two_two (Γ := Γ))
  have h2 := eb_ge hN1 (by ipra_le sl hN with -e4 : Γ ⊢[PRAAx] le (pw two two) N)
  have c : Γ ⊢[PRAAx] le (num 81 * B1 N k) (num 81 * A1 N k) := by
    ipra_le sl lg + 56 * 𝔞 (B1 N k) * sl h2 + 31 * 𝔞 (B1 N k)
  have hp := pos_of_one_le (Γ := Γ) (by ipra_le 80 : Γ ⊢[PRAAx] le one (num 81 : PTm n))
  exact mul_le_cancel (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _)) c)

theorem hAD {N k : PTm n} (hN : Γ ⊢[PRAAx] le (num 4) N) :
    Γ ⊢[PRAAx] le (A1 N k * D1 N k) (C1 N k * B1 N k) :=
  lo_le_hi_any (le_refl one) (n_one' hN) (K1 N k) (K1 N k)

theorem hDC {N k : PTm n} (hN : Γ ⊢[PRAAx] le (num 4) N) : Γ ⊢[PRAAx] le (D1 N k) (C1 N k) := by
  have h := hAD (k := k) hN
  have b := hBA (k := k) hN
  have c : Γ ⊢[PRAAx] le (B1 N k * D1 N k) (B1 N k * C1 N k) := by ipra_le sl h + 𝔞 (D1 N k) * sl b
  have hp := loD_pos (Γ := Γ) (le_refl one) (n_one' hN) (K1 N k)
  exact mul_le_cancel (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _)) c)

/-- The double logarithm: `UH ≤ LL + 3·2^{−r}`, cleared. -/
theorem w1 {N k : PTm n} (hN : Γ ⊢[PRAAx] le (num 4) N) :
    Γ ⊢[PRAAx] le (UHn N k * LLd N k * pw two (rr N k)) (LLn N k * UHd N k * pw two (rr N k) + num 3 * UHd N k * LLd N k) := by
  have hN1 := n_one' hN
  have hB1 : Γ ⊢[PRAAx] le one (B1 N k) := one_le_of_pos' (loD_pos (le_refl one) hN1 _)
  have hD1 : Γ ⊢[PRAAx] le one (D1 N k) := one_le_of_pos' (hiD_pos (le_refl one) hN1 _)
  have ba := hBA (k := k) hN
  have dc := hDC (k := k) hN
  have hDx := eq_add_of_le (hAD (k := k) hN)
  have w0 := RobinLogWidth.logI_width (le_refl one) hN1 (rr N k)
  have hR := pw_pos' (Γ := Γ) two_pos' (rr N k)
  have h2x := x2_alg hR w0 ba
  have comp := comp_width hB1 ba hD1 dc hDx h2x (rr N k)
  have lh := lo_le_hi_any hB1 ba (K3 N k) (K2 N k)
  have w2 := RobinLogWidth.logI_width hB1 ba (rr N k)
  have wx := wx_alg w0 ba hDx
  have hM : Γ ⊢[PRAAx] loD (A1 N k) (B1 N k) (K3 N k) * hiD (A1 N k) (B1 N k) (K2 N k) * A1 N k * D1 N k ≐
      succ (pred (loD (A1 N k) (B1 N k) (K3 N k) * hiD (A1 N k) (B1 N k) (K2 N k) * A1 N k * D1 N k)) :=
    pos_mul (pos_mul (pos_mul (loD_pos hB1 ba _) (hiD_pos hB1 ba _)) (pos_of_one_le (le_trans hB1 ba)))
      (pos_of_one_le hD1)
  exact w1_alg hM comp lh w2 wx

/-- `LL ≤ n`. -/
theorem ll_le {N k : PTm n} (hN : Γ ⊢[PRAAx] le (num 4) N) : Γ ⊢[PRAAx] le (LLn N k) (N * LLd N k) := by
  have hN1 := n_one' hN
  have ba := hBA (k := k) hN
  have hB1 : Γ ⊢[PRAAx] le one (B1 N k) := one_le_of_pos' (loD_pos (le_refl one) hN1 _)
  exact ll_alg (loD_pos (le_refl one) hN1 _) (lo_le_pred hB1 ba (K2 N k)) (lo_le_pred (le_refl one) hN1 (K1 N k))

/-! ## The exponential part -/

theorem assoc3 (a b c : PTm n) : Γ ⊢[PRAAx] a * b * c ≐ a * (b * c) := by ipra_ring

/-- `γ_hi ≤ 1` on the names. -/
theorem hu1 (N k : PTm n) : Γ ⊢[PRAAx] le (gHn N k) (gHd N k) := by
  have g := gamma_hi_le (Γ := Γ) (tg N k) (two * rr N k)
  have c : Γ ⊢[PRAAx] le (num 12 * gHn N k) (num 12 * gHd N k) := by ipra_le sl g + 5 * 𝔞 (gHd N k)
  have hp := pos_of_one_le (Γ := Γ) (by ipra_le 11 : Γ ⊢[PRAAx] le one (num 12 : PTm n))
  exact mul_le_cancel (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _)) c)

/-- `U(n, k) − L(n, k) ≤ 2^{−k}` for `n ≥ 4`, cleared: `2^k·Uup·Ld ≤ 2^k·Lp·Uud + Uud·Ld`. -/
theorem width {N k : PTm n} (hN : Γ ⊢[PRAAx] le (num 4) N) :
    Γ ⊢[PRAAx] le (pw two k * (Uup N k * Ld N k)) (pw two k * (Lp N k * Uud N k) + Uud N k * Ld N k) := by
  have hN1 := n_one' hN
  have hq := ghiD_pos (Γ := Γ) (tg N k) (Kg N k)
  have hqp := gloD_pos (Γ := Γ) (tg N k) (Kg N k)
  have u1 := hu1 (Γ := Γ) N k
  have hcons := gamma_consistent (Γ := Γ) (tg N k) (Kg N k) (Kg N k)
  have hd := eq_add_of_le hcons
  have lip := exp_lip hd (Kq N k)
  have three := e_le_three hq u1 (Kq N k)
  have tl := tail_alg (E := Ev (succ (Kq N k)) (gHn N k) (gHd N k)) (F_succ (succ (Kq N k)))
    (pw_succ (gHd N k) (succ (Kq N k))) (pw_le_pw (succ (succ (Kq N k))) u1)
  have gw := gw_alg hd (gamma_width (Γ := Γ) (tg N k) (Kg N k))
  have hM1 := pos_mul (Γ := Γ) (LeanProofs.IPRA.AnalyticNumberTheory.SigmaPrimePower.pos_pw hq (succ (Kq N k)))
    (LeanProofs.IPRA.AnalyticNumberTheory.SigmaPrimePower.pos_pw hq (Kq N k))
  have h2 := exp_alg hM1 tl lip three gw (F_succ (Kq N k)) (pw_succ (gHd N k) (Kq N k))
  have hFp : Γ ⊢[PRAAx] le one (Fv (succ (succ (Kq N k)))) := one_le_of_pos' (F_pos _)
  have hM2 := pos_mul (pos_mul (Γ := Γ) (F_pos (succ (Kq N k)))
    (LeanProofs.IPRA.AnalyticNumberTheory.SigmaPrimePower.pos_pw hq (succ (Kq N k)))) (F_pos (succ (succ (Kq N k))))
  have h3 := t5_alg hM2 tl (e_le_three hq u1 (succ (Kq N k))) hFp
  have h5 := frac_trans (Ed_pos hq (succ (Kq N k))) (e_mono hcons (succ (Kq N k))) (e_up (succ (Kq N k)) (gHn N k) (gHd N k))
  have h4 := ll_le (k := k) hN
  have h1 := w1 (k := k) hN
  have h6 := num_alg (Qt := Qt (tg N k) (pairT one (Kg N k))) (Ad := Ad (tg N k) (Kg N k)) (n_one hN1 k) (n_two hN1 k) (n_three hN1 k) (n_four N k)
  have hZ : Γ ⊢[PRAAx] Zg (Kg N k) ≐ succ (pred (Zg (Kg N k))) :=
    pos_mul (pos_mul (pos_of_one_le (by ipra_le 3)) (pos_of_one_le (by ipra_le 𝔞 (two * Kg N k))))
      (pw_pos' (pos_of_one_le (by ipra_le 2 : Γ ⊢[PRAAx] le one (c3 : PTm n))) _)
  have hM3 := pos_mul (pos_mul (pos_mul (pos_mul (F_pos (succ (succ (Kq N k)))) hZ) hq) hqp) (pw_pos' (Γ := Γ) two_pos' (rr N k))
  have fin := fin_alg hM3 h1 h2 h3 h4 h5 h6
  -- the positive branches of both programs
  have ba := hBA (k := k) hN
  have dc := hDC (k := k) hN
  have e1 : Γ ⊢[PRAAx] cnd N k ≐ zero := (Mobius.congrSg ba).eqTrans Signum.sg_zero
  have e2 : Γ ⊢[PRAAx] monus one (cnd N k) ≐ one := (congrMonus (.eqRefl _) e1).eqTrans (monus_zero _)
  have f1 : Γ ⊢[PRAAx] cndU N k ≐ zero := (Mobius.congrSg dc).eqTrans Signum.sg_zero
  have f2 : Γ ⊢[PRAAx] monus one (cndU N k) ≐ one := (congrMonus (.eqRefl _) f1).eqTrans (monus_zero _)
  have eke := ke_eq (Γ := Γ) N k
  have eLp : Γ ⊢[PRAAx] Ev (succ (Kq N k)) (gN N k) (gD N k) * LLn N k ≐ Lp N k :=
    ((congrMul (Ev_congr _ _ eke).eqSymm (.eqRefl _)).eqTrans ((congrMul e2 (.eqRefl _)).eqTrans (one_mul _)).eqSymm)
  have eLd : Γ ⊢[PRAAx] Ed (succ (Kq N k)) (gD N k) * LLd N k ≐ Ld N k :=
    ((congrMul (Ed_congr _ eke).eqSymm (.eqRefl _)).eqTrans
      ((congrAdd ((congrMul e2 (.eqRefl _)).eqTrans (one_mul _)) ((congrMul e1 (.eqRefl _)).eqTrans (zero_mul _))).eqTrans
        (add_zero _)).eqSymm)
  have eUp : Γ ⊢[PRAAx] Tn (succ (Kq N k)) (gHn N k) (gHd N k) * UHn N k ≐ Uup N k :=
    ((congrMul (Tn_congr _ _ eke).eqSymm (.eqRefl _)).eqTrans ((congrMul f2 (.eqRefl _)).eqTrans (one_mul _)).eqSymm)
  have eUd : Γ ⊢[PRAAx] Td (succ (Kq N k)) (gHd N k) * UHd N k ≐ Uud N k :=
    ((congrMul (Td_congr _ eke).eqSymm (.eqRefl _)).eqTrans
      ((congrAdd ((congrMul f2 (.eqRefl _)).eqTrans (one_mul _)) ((congrMul f1 (.eqRefl _)).eqTrans (zero_mul _))).eqTrans
        (add_zero _)).eqSymm)
  exact le_congr ((congrMul (congrMul (.eqRefl _) eUp) eLd).eqTrans (assoc3 _ _ _))
    (congrAdd ((congrMul (congrMul (.eqRefl _) eLp) eUd).eqTrans (assoc3 _ _ _)) (congrMul eUd eLd)) fin

end LeanProofs.IPRA.AnalyticNumberTheory.RobinWidthCompose
