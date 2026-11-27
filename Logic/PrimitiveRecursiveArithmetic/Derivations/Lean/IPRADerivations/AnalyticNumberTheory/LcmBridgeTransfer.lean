import IPRADerivations.AnalyticNumberTheory.LcmBridgeExact
import IPRADerivations.AnalyticNumberTheory.RobinUpperEnd

/-!
# The finite counterexample transfer of the lcm bridge, product form

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/lcm_bridge.tex`, Theorem "Explicit finite
counterexample transfer": an explicit inequality at the frontier `P = m²` yields the integer `N = L_P = lcm(1, …, P)`
with `σ(N) > e^γ N log log N`, i.e. the negative certificate `Neg(N, k)` of the Robin interval programs
(`RobinUpperEnd.NegR`).

The bridge's `T` loss enters through `∏_{p∣L}(1 − p^{−a_p−1}) ≥ 1 − 2/m` (`LcmBridgeLoss`), and the exact identity
`A(L) = ∏_{p∣L}(1 − p^{−a_p−1})/(1 − 1/p)` through `SigmaProduct.sigma_product`. With `Φ = ∏_{p∣L}(p − 1)`
(`PP F₂ L`) and `Π = ∏_{p∣L} p` (`PP id L`), the transfer is:

* `transfer`: for `m ≥ 2`, if `m Φ Uup + 2 Π Uud < m Π Uud` at `(L, k)` — that is,
  `∏_{p∣L}(1 − 1/p) · [e^γ log log L]_hi < 1 − 2/m` on the upper names — then `NegR(L, k)`.

The comparison of `[e^γ log log L]_hi` with `e^γ log ϑ(m²)` (the loss `D(m²) ≤ 8/m`) is separate.

Pieces: the Weierstrass inequality over the range `q ≤ L` of `EulerProduct.PP` with `u'_q = e(q)⌊L²/q^{a_q+1}⌋`
(`w_range`), the sum bound transported from `q ≤ P` (`sum_tail`, `sum_low`), the products
`∏(L² − u'_q) · ∏ (q^{a_q+1})^{e(q)} = L^{2(L+1)} ∏_{p∣L}(p^{a+1} − 1)` (`cy`) and
`∏ (q^{a_q+1})^{e(q)} = L · Π` (`y_eq`, via `FactorVector.reconstruct`).
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeTransfer

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP isP_01 prime_of_isP pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeLoss (LD uB U inst2_uB u_le loss_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeExact (prod_mul eL e_low e_high factor_id)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (PP eB inst2_e F₂ mul_one')
open LeanProofs.IPRA.AnalyticNumberTheory.SigmaProduct (G inst2_G sigma_product monus_succ_one)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinUpperEnd (NegR Uup Uud Uum uud_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (fB reconstruct one_le_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrSg)
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos)
open LeanProofs.IPRA.Signum (sg sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `q^{v_q(L)+1}`, as in `LcmBridgeLoss.ex` (a local name: `LeanProofs.IPRA.ex` is the existential). -/
abbrev ex (i P : PTm n) : PTm n := pw i (succ (val i (lcmu P)))

/-! ## Bodies over `0 = q`, `1 = P` -/

abbrev u2B : PTm 2 := isP (var 0) * eqb (rem (lcmu (var 1)) (var 0)) zero *
  quo (lcmu (var 1) * lcmu (var 1)) (pw (var 0) (succ (val (var 0) (lcmu (var 1)))))
abbrev c2B : PTm 2 := monus (lcmu (var 1) * lcmu (var 1)) u2B
abbrev yB : PTm 2 := pw (pw (var 0) (succ (val (var 0) (lcmu (var 1))))) (isP (var 0) * eqb (rem (lcmu (var 1)) (var 0)) zero)
abbrev gB : PTm 2 :=
  pw (monus (pw (var 0) (succ (val (var 0) (lcmu (var 1))))) one) (isP (var 0) * eqb (rem (lcmu (var 1)) (var 0)) zero)
abbrev ldB : PTm 2 := lcmu (var 1) * lcmu (var 1)
abbrev iB : PTm 2 := pw (var 0) (isP (var 0) * eqb (rem (lcmu (var 1)) (var 0)) zero)
abbrev vB2 : PTm 2 := pw (pw (var 0) (val (var 0) (lcmu (var 1)))) (isP (var 0) * eqb (rem (lcmu (var 1)) (var 0)) zero)

theorem inst2_mul (f g : PTm 2) (a b : PTm n) : inst2 (f * g) a b = inst2 f a b * inst2 g a b := by simp [inst2]
theorem inst2_u2 (i P : PTm n) : inst2 u2B i P = eL i P * quo (LD P) (ex i P) := by simp [inst2]
theorem inst2_c2 (i P : PTm n) : inst2 c2B i P = monus (LD P) (eL i P * quo (LD P) (ex i P)) := by simp [inst2]
theorem inst2_y (i P : PTm n) : inst2 yB i P = pw (ex i P) (eL i P) := by simp [inst2]
theorem inst2_g (i P : PTm n) : inst2 gB i P = pw (monus (ex i P) one) (eL i P) := by simp [inst2]
theorem inst2_ld (i P : PTm n) : inst2 ldB i P = LD P := by simp [inst2]
theorem inst2_i (i P : PTm n) : inst2 iB i P = pw i (eL i P) := by simp [inst2]
theorem inst2_v (i P : PTm n) : inst2 vB2 i P = pw (pw i (val i (lcmu P))) (eL i P) := by simp [inst2]
theorem inst2_id (i x : PTm n) : inst2 (var 0 : PTm 2) i x = i := by simp [inst2]
theorem inst2_fB (i x : PTm n) : inst2 fB i x = pw i (isP i * val i x) := by simp [inst2]
theorem inst2_F2 (i x : PTm n) : inst2 F₂ i x = monus i one := by simp [inst2]

theorem shift_lcmu (P : PTm n) : Syn.shift (lcmu P) = lcmu (Syn.shift P) := by simp [Syn.shift]
theorem shift_LD (P : PTm n) : Syn.shift (LD P) = LD (Syn.shift P) := by simp [Syn.shift]

/-! ## The exponent `e(q)` -/

theorem e_zero_high {i P : PTm n} (h : Γ ⊢[PRAAx] lt P i) : Γ ⊢[PRAAx] eL i P ≐ zero := by
  refine .orE (isP_01 i) ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)) ?_
  exact (congrMul Prf.hyp0 (e_high (prime_of_isP Prf.hyp0) h.wk)).eqTrans (mul_zero _)

theorem e_low' {i P : PTm n} (h : Γ ⊢[PRAAx] le i P) : Γ ⊢[PRAAx] eL i P ≐ isP i := by
  refine .orE (isP_01 i) ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans ((zero_mul _).eqTrans Prf.hyp0.eqSymm)) ?_
  exact (congrMul (.eqRefl _) (e_low (prime_of_isP Prf.hyp0) h.wk)).eqTrans (mul_one' _)

/-- `u'_q ≤ L²`. -/
theorem u2_le {P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) (i : PTm n) :
    Γ ⊢[PRAAx] le (eL i P * quo (LD P) (ex i P)) (LD P) := by
  refine .orE (lt_or_le P i) ?_ ?_
  · exact le_congr ((congrMul (e_zero_high Prf.hyp0) (.eqRefl _)).eqTrans (zero_mul _)).eqSymm (.eqRefl _) (zero_le _)
  · exact le_congr (congrMul (e_low' Prf.hyp0).eqSymm (.eqRefl _)) (.eqRefl _) (u_le hP.wk i)

/-! ## The sum -/

theorem le_lcmu {P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) : Γ ⊢[PRAAx] le P (lcmu P) := by
  have d := Prf.andE₂ (LcmUpto.lcmu_dvd (Γ := Γ) (pred P))
  have d' : Γ ⊢[PRAAx] dvd P (lcmu P) := (congrAp2 remF (congrAp2 LcmUpto.lcmuF hP (.eqRefl _)) hP).eqTrans d
  exact DiophantineNumberTheory.Coprime.dvd_le' hP d' (lcmu_pos P)

abbrev U2 (N P : PTm n) : PTm n := ap2 (sumF u2B) N P

theorem sum_tail {P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) :
    Γ ⊢[PRAAx] U2 (succ (lcmu P)) P ≐ U2 (succ P) P := by
  refine MobiusBounds.sum_ext u2B (B := P) ?_ ((succ_monus_succ _ _).eqTrans (le_lcmu hP))
  intro Δ a _ h
  rw [inst2_u2]
  exact (congrMul (e_zero_high h) (.eqRefl _)).eqTrans (zero_mul _)

theorem sum_low (P : PTm n) : Γ ⊢[PRAAx] le (U2 (succ P) P) (U (succ P) P) := by
  refine sum_le_params u2B uB P P (succ P) (.allI (.impI ?_))
  rw [inst2_u2, inst2_uB]
  have h : (lt (var 0) (Syn.shift (succ P)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift P) :=
    (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  exact le_congr (congrMul (e_low' h).eqSymm (.eqRefl _)) (.eqRefl _) (le_refl _)

theorem sum_bound {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] le (m * U2 (succ (lcmu (m * m))) (m * m)) (two * LD (m * m)) := by
  have hP := Combinatorics.Binomial.pos_mul hm hm
  exact le_congr (congrMul (.eqRefl _) (sum_tail hP)).eqSymm (.eqRefl _)
    (le_trans (le_mul_mono (le_refl m) (sum_low (m * m))) (loss_sum hm))

/-! ## The Weierstrass inequality over `q ≤ L` -/

abbrev Pc (P : PTm n) : PTm n := ap2 (prodF c2B) (succ (lcmu P)) P

/-- Abstract algebra: `D^{N+1} ≤ D^N U + D C`, `m U ≤ 2 D` give `m D^N ≤ m C + 2 D^N`. -/
theorem w_alg {m D N Us C : PTm n} (hD : Γ ⊢[PRAAx] D ≐ succ (pred D))
    (W : Γ ⊢[PRAAx] le (pw D (succ N)) (pw D N * Us + D * C)) (hL : Γ ⊢[PRAAx] le (m * Us) (two * D)) :
    Γ ⊢[PRAAx] le (m * pw D N) (m * C + two * pw D N) := by
  refine le_cancel_pos hD (le_of_eq_add (d := m * monus (pw D N * Us + D * C) (pw D (succ N)) +
    pw D N * monus (two * D) (m * Us)) ?_)
  ipra_lc 𝔞 m * natEq (eq_add_of_le W) + 𝔞 (pw D N) * natEq (eq_add_of_le hL) + 𝔞 m * natEq (pw_succ D N)

theorem w_range {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] le (m * pw (LD (m * m)) (succ (lcmu (m * m))))
      (m * Pc (m * m) + two * pw (LD (m * m)) (succ (lcmu (m * m)))) := by
  have hP := Combinatorics.Binomial.pos_mul hm hm
  have hb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ (lcmu (m * m)))) ⟶
      (inst2 u2B (var 0) (Syn.shift (m * m)) + inst2 c2B (var 0) (Syn.shift (m * m)) ≐ Syn.shift (LD (m * m)))) := by
    refine .allI (.impI ?_)
    rw [inst2_u2, inst2_c2, shift_LD]
    have hP' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift (m * m) ≐ succ (pred (Syn.shift (m * m))) := by
      have b := hP.shift
      simp only [Fm.shift, Fm.subst_eq, ConciseIPRA.PTm.subst_succ, LeanProofs.IPRA.PTm.subst_pred] at b
      exact b
    exact (eq_add_of_le (u2_le hP'.wk (var 0))).eqSymm
  have W := Analysis.WeierstrassProduct.weierstrass_lower (a := u2B) (c := c2B) (D := LD (m * m)) (x := m * m)
    (N := succ (lcmu (m * m))) hb
  have Dpos := Combinatorics.Binomial.pos_mul (lcmu_pos (Γ := Γ) (m * m)) (lcmu_pos (m * m))
  exact w_alg Dpos W (sum_bound hm)

/-! ## The products -/

theorem cy (P : PTm n) :
    Γ ⊢[PRAAx] Pc P * ap2 (prodF yB) (succ (lcmu P)) P ≐ pw (LD P) (succ (lcmu P)) * PP G (lcmu P) := by
  refine (prod_mul c2B yB (succ (lcmu P)) P).eqSymm.eqTrans ?_
  have h1 : Γ ⊢[PRAAx] ap2 (prodF (c2B * yB)) (succ (lcmu P)) P ≐ ap2 (prodF (ldB * gB)) (succ (lcmu P)) P := by
    refine prod_congr_bounded (c2B * yB) (ldB * gB) P P (succ (lcmu P)) (.allI (.impI ?_))
    rw [inst2_mul, inst2_mul, inst2_c2, inst2_y, inst2_ld, inst2_g]
    exact factor_id (var 0) (Syn.shift P)
  refine h1.eqTrans ((prod_mul ldB gB (succ (lcmu P)) P).eqTrans (congrMul ?_ ?_))
  · refine prod_const_of ldB (succ (lcmu P)) (LD P) P (.allI (.impI ?_))
    rw [inst2_ld, shift_LD]
    exact .eqRefl _
  · refine prod_congr_bounded gB (EulerProduct.pB G) P (lcmu P) (succ (lcmu P)) (.allI (.impI ?_))
    rw [inst2_g, EulerProduct.inst2_pB, inst2_G, inst2_e, shift_lcmu]
    exact .eqRefl _

/-- A prime `q > P` has `v_q(L) = 0`. -/
theorem val_zero_high {i P : PTm n} (hi : Γ ⊢[PRAAx] prime i) (hPi : Γ ⊢[PRAAx] lt P i) :
    Γ ⊢[PRAAx] val i (lcmu P) ≐ zero := by
  refine .orE (zero_or_succ (val i (lcmu P))) Prf.hyp0 ?_
  let C : List (Fm PTm n) := (val i (lcmu P) ≐ succ (pred (val i (lcmu P)))) :: Γ
  have I1 := Prf.andE₁ (lcm_valuation (Γ := C) hi.wk P)
  have s1 : C ⊢[PRAAx] sg (val i (lcmu P)) ≐ one := (congrSg Prf.hyp0).eqTrans (sg_succ _)
  have a : C ⊢[PRAAx] le (pw i (val i (lcmu P))) P :=
    le_congr ((congrMul s1 (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _) I1
  have b : C ⊢[PRAAx] le i (pw i (val i (lcmu P))) :=
    le_congr (pw_one i) (.eqRefl _) (PowerCleared.pw_le_exp (p_pos (prime_two hi.wk)) (one_le_pos Prf.hyp0))
  exact le_lt_absurd _ (le_trans b a) hPi.wk

theorem v_point (i P : PTm n) :
    Γ ⊢[PRAAx] pw (pw i (val i (lcmu P))) (eL i P) ≐ pw i (isP i * val i (lcmu P)) := by
  refine .orE (isP_01 i) ?_ ?_
  · have e0 : ((isP i ≐ zero) :: Γ) ⊢[PRAAx] eL i P ≐ zero := (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
    exact ((congrAp2 powF e0 (.eqRefl _)).eqTrans (pw_zero _)).eqTrans
      ((congrAp2 powF ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)) (.eqRefl _)).eqTrans (pw_zero _)).eqSymm
  · let C : List (Fm PTm n) := (isP i ≐ one) :: Γ
    have hi : C ⊢[PRAAx] prime i := prime_of_isP Prf.hyp0
    have r1 : C ⊢[PRAAx] isP i * val i (lcmu P) ≐ val i (lcmu P) := (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (one_mul _)
    refine .orE (lt_or_le P i) ?_ ?_
    · have v0 := val_zero_high hi.wk (Prf.hyp0 : (lt P i :: C) ⊢[PRAAx] lt P i)
      exact ((congrAp2 powF (e_zero_high Prf.hyp0) (.eqRefl _)).eqTrans (pw_zero _)).eqTrans
        ((congrAp2 powF (r1.wk.eqTrans v0) (.eqRefl _)).eqTrans (pw_zero _)).eqSymm
    · have e1 : (le i P :: C) ⊢[PRAAx] eL i P ≐ one := (e_low' Prf.hyp0).eqTrans Prf.hyp1
      exact ((congrAp2 powF e1 (.eqRefl _)).eqTrans (pw_one _)).eqTrans (congrAp2 powF r1.wk (.eqRefl _)).eqSymm

theorem y_eq {P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) :
    Γ ⊢[PRAAx] ap2 (prodF yB) (succ (lcmu P)) P ≐ lcmu P * PP (var 0) (lcmu P) := by
  have h1 : Γ ⊢[PRAAx] ap2 (prodF yB) (succ (lcmu P)) P ≐ ap2 (prodF (vB2 * iB)) (succ (lcmu P)) P := by
    refine prod_congr_bounded yB (vB2 * iB) P P (succ (lcmu P)) (.allI (.impI ?_))
    rw [inst2_mul, inst2_y, inst2_v, inst2_i]
    exact (congrAp2 powF (.eqRefl _) (pw_succ _ _)).eqTrans (LocalFactor.pw_mul_base _ _ _)
  refine h1.eqTrans ((prod_mul vB2 iB (succ (lcmu P)) P).eqTrans (congrMul ?_ ?_))
  · have h2 : Γ ⊢[PRAAx] ap2 (prodF vB2) (succ (lcmu P)) P ≐ ap2 (prodF fB) (succ (lcmu P)) (lcmu P) := by
      refine prod_congr_bounded vB2 fB P (lcmu P) (succ (lcmu P)) (.allI (.impI ?_))
      rw [inst2_v, inst2_fB, shift_lcmu]
      exact v_point (var 0) (Syn.shift P)
    exact h2.eqTrans (reconstruct (lcmu_pos P) (le_refl _))
  · refine prod_congr_bounded iB (EulerProduct.pB (var 0)) P (lcmu P) (succ (lcmu P)) (.allI (.impI ?_))
    rw [inst2_i, EulerProduct.inst2_pB, inst2_id, inst2_e, shift_lcmu]
    exact .eqRefl _

/-! ## Positivity of `Φ = ∏_{p∣L}(p − 1)` -/

theorem phi_pos (N : PTm n) : Γ ⊢[PRAAx] PP F₂ N ≐ succ (pred (PP F₂ N)) := by
  refine prod_pos_bounded (EulerProduct.pB F₂) N (succ N) (.allI (.impI ?_))
  rw [EulerProduct.inst2_pB, inst2_F2, inst2_e]
  let Δ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift
  refine .orE (isP_01 (var 0)) ?_ ?_
  · exact pos_of_eq_succ (c := zero) ((congrAp2 powF ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _))
      (.eqRefl _)).eqTrans (pw_zero _))
  · let C : List (Fm PTm (n + 1)) := (isP (var 0) ≐ one) :: Δ
    have h2 : C ⊢[PRAAx] le two (var 0) := prime_two (prime_of_isP Prf.hyp0)
    have e := eq_add_of_le h2
    have e1 : C ⊢[PRAAx] two + monus (var 0) two ≐ succ (succ (monus (var 0) two)) := by
      ipra_ring
    have e' : C ⊢[PRAAx] monus (var 0) one ≐ succ (monus (var 0) two) :=
      (congrMonus (e.eqTrans e1) (.eqRefl one)).eqTrans (monus_succ_one _)
    exact pw_pos' (pos_of_eq_succ e') _

/-! ## The transfer -/

/-- Abstract algebra of the last step. -/
theorem key_alg {m Φ s L Up Ud Pi Gp : PTm n} (hL : Γ ⊢[PRAAx] L ≐ succ (pred L))
    (SP : Γ ⊢[PRAAx] s * Φ ≐ Gp) (S1 : Γ ⊢[PRAAx] le (m * (L * Pi)) (m * Gp + two * (L * Pi)))
    (H : Γ ⊢[PRAAx] lt (m * Φ * Up + two * Pi * Ud) (m * Pi * Ud)) :
    Γ ⊢[PRAAx] lt (m * Φ * (L * Up)) (m * Φ * (s * Ud)) := by
  refine le_of_eq_add (d := pred L + L * monus (m * Pi * Ud) (succ (m * Φ * Up + two * Pi * Ud)) +
    monus (m * Gp + two * (L * Pi)) (m * (L * Pi)) * Ud) ?_
  ipra_lc 𝔞 m * 𝔞 Ud * natEq SP + 𝔞 Ud * natEq (eq_add_of_le S1) + 𝔞 L * natEq (eq_add_of_le H) + natEq hL

/-- Abstract algebra: `m X ≤ m C + 2X` and `C Y = X G` give `m Y ≤ m G + 2 Y`. -/
theorem s1_alg {m X C Y Gp : PTm n} (hX : Γ ⊢[PRAAx] X ≐ succ (pred X)) (w : Γ ⊢[PRAAx] le (m * X) (m * C + two * X))
    (cy : Γ ⊢[PRAAx] C * Y ≐ X * Gp) : Γ ⊢[PRAAx] le (m * Y) (m * Gp + two * Y) := by
  refine le_cancel_pos hX (le_of_eq_add (d := Y * monus (m * C + two * X) (m * X)) ?_)
  ipra_lc 𝔞 Y * natEq (eq_add_of_le w) - 𝔞 m * natEq cy

theorem lt_cancel {c a b : PTm n} (_hc : Γ ⊢[PRAAx] c ≐ succ (pred c)) (h : Γ ⊢[PRAAx] lt (c * a) (c * b)) :
    Γ ⊢[PRAAx] lt a b :=
  .orE (lt_or_le a b) Prf.hyp0 (le_lt_absurd _ (le_mul_mono (le_refl c) Prf.hyp0) h.wk)

/-- `lcm_bridge.tex`, finite counterexample transfer, product form: for `m ≥ 2` and `L = lcm(1, …, m²)`, if
`m Φ Uup + 2 Π Uud < m Π Uud` at `(L, k)` — `∏_{p∣L}(1 − 1/p) · [e^γ log log L]_hi < 1 − 2/m` — then `NegR(L, k)`:
`σ(L) > [e^γ L log log L]_hi`. -/
theorem transfer {m k : PTm n} (hm : Γ ⊢[PRAAx] le two m)
    (H : Γ ⊢[PRAAx] lt (m * PP F₂ (lcmu (m * m)) * Uup (lcmu (m * m)) k + two * PP (var 0) (lcmu (m * m)) *
      Uud (lcmu (m * m)) k) (m * PP (var 0) (lcmu (m * m)) * Uud (lcmu (m * m)) k)) :
    Γ ⊢[PRAAx] NegR (lcmu (m * m)) k := by
  have hm1 : Γ ⊢[PRAAx] m ≐ succ (pred m) := BinomialThree.pos_of_one_le (le_trans (by ipra_le 1) hm)
  have hP := Combinatorics.Binomial.pos_mul hm1 hm1
  have hLp := lcmu_pos (Γ := Γ) (m * m)
  have hmP : Γ ⊢[PRAAx] le m (m * m) := by
    exact le_of_eq_add (d := m * pred m) (by ipra_lc 𝔞 m * natEq hm1)
  have hL2 : Γ ⊢[PRAAx] le two (lcmu (m * m)) := le_trans hm (le_trans hmP (le_lcmu hP))
  -- `m Y ≤ m ∏G + 2 Y`, `Y = L Π`
  have w := w_range hm1
  have c := cy (Γ := Γ) (m * m)
  have Xpos := pw_pos' (Combinatorics.Binomial.pos_mul hLp hLp) (succ (lcmu (m * m)))
  have S0 := s1_alg Xpos w c
  have S1 := le_congr (congrMul (.eqRefl _) (y_eq hP)) (congrAdd (.eqRefl _) (congrMul (.eqRefl _) (y_eq hP))) S0
  have SP := sigma_product hLp
  have k1 := key_alg hLp SP S1 H
  have mp := Combinatorics.Binomial.pos_mul hm1 (phi_pos (lcmu (m * m)))
  have k2 := lt_cancel mp k1
  exact .andI hL2 (le_trans k2 (le_add_right _ _))

end LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeTransfer
