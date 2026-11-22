import IPRADerivations.AnalyticNumberTheory.RobinLipSum

/-!
# Elementary bounds and powers for the lower names of `LogI` (`robin_ipra_research_2026-11-19`, `lcm_bridge.tex`)

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/lcm_bridge.tex`, Lemma "Losses at a square
frontier": "two applications of `log(1+t) ≤ t`". With `lo(·, K)` the lower names of `RobinLogInterval`:

* `S_le`: every name `S_K(z) ≤ U_K(z) ≤ 2z/(1 − z²)`;
* `lo_le_pred`: `lo(q, K) ≤ q − 1` for every rational `q ≥ 1` and every `K` (`(3/4)e + (y − 1) ≤ 2^e y − 1`);
* `lo_four`: `lo(4, K) ≤ 3/2`;
* `lo_pow`: `lo(x P^j, K) ≤ lo(x, K) + j·lo(P, K) + j(P − 1)/9^K`, by `j` applications of the addition theorem
  `RobinLipSum.lo_sub_up`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinLipBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma (Lv Pv)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName (Nz Dz Lz Un Ud low_up Dz_pos Ud_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogDiff (up_le)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipName (Rv)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipArg (Nz_p0)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipLog (mul1)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipSum (lo_val lo_sub_up le_shift one_le_mul one_le_of_pos' G_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval
  (eb eb_spec eb_eq Bt dt st Wt c3 c8 c3_sq c3_pos c8_pos st_sq st_pos Wt_pos a_eq loN loD loD_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos' lt_pw)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds (two_pos')
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## `S_K(z) ≤ 2z/(1 − z²)` -/

theorem S_le {p s W : PTm n} (hs : Γ ⊢[PRAAx] s ≐ succ (pred s)) (hWp : Γ ⊢[PRAAx] W ≐ succ (pred W))
    (hW : Γ ⊢[PRAAx] s * s ≐ W + p * p) (K : PTm n) :
    Γ ⊢[PRAAx] le (Nz K p s * W) (two * p * s * Dz K p s) := by
  have lu := low_up (Γ := Γ) K p s W
  have ul := up_le (Γ := Γ) hW K
  have c : Γ ⊢[PRAAx] le (Ud K p s W * (Nz K p s * W)) (Ud K p s W * (two * p * s * Dz K p s)) := by
    ipra_le 𝔞 W * sl lu + 𝔞 (Dz K p s) * sl ul
  have hp := Ud_pos hs hWp K p
  exact mul_le_cancel (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _)) c)

/-! ## `lo(q) ≤ q − 1` -/

theorem q1_alg {e N3 D3 Nr Dr a b P d : PTm n}
    (hM : Γ ⊢[PRAAx] num 8 * (two * two * (b * P) * a) * (b * P) ≐ succ (pred (num 8 * (two * two * (b * P) * a) * (b * P))))
    (h3 : Γ ⊢[PRAAx] le (N3 * (two * two * two)) (two * one * c3 * D3))
    (hS : Γ ⊢[PRAAx] le (Nr * (two * two * (b * P) * a)) (two * d * (a + b * P) * Dr))
    (hp : Γ ⊢[PRAAx] le (succ e) P) (ea : Γ ⊢[PRAAx] a ≐ b * P + d) (ep : Γ ⊢[PRAAx] P ≐ succ (pred P)) :
    Γ ⊢[PRAAx] le ((e * N3 * Dr + Nr * D3) * b + b * (D3 * Dr)) (a * (D3 * Dr)) := by
  have ea := natEq ea
  have ep := natEq ep
  have c : Γ ⊢[PRAAx] le (num 8 * (two * two * (b * P) * a) * (b * P) * ((e * N3 * Dr + Nr * D3) * b + b * (D3 * Dr)))
      (num 8 * (two * two * (b * P) * a) * (b * P) * (a * (D3 * Dr))) := by
    ipra_le 8 * 𝔞 ((two * two * (b * P) * a) * D3 * Dr * b * b * P) * sl hp +
      2 * 𝔞 ((two * two * (b * P) * a) * D3 * Dr * b * b * P * e) +
      8 * 𝔞 ((two * two * (b * P) * a) * D3 * Dr * b * d * pred P) +
      𝔞 ((two * two * (b * P) * a) * (b * P) * b * e * Dr) * sl h3 + 8 * 𝔞 ((b * P) * b * D3) * sl hS +
      16 * 𝔞 (b * D3 * Dr * d * d * (b * P)) with
      ((32 * 𝔞 D3 * 𝔞 Dr * (𝔞 P) ^ 2 * 𝔞 a * (𝔞 b) ^ 2) + (32 * 𝔞 D3 * 𝔞 Dr * (𝔞 P) ^ 2 * (𝔞 b) ^ 2 * 𝔞 d) + (-32 * 𝔞 D3 * 𝔞 Dr * 𝔞 P * (𝔞 b) ^ 2 * 𝔞 d * 𝔞 (pred P)) + (-16 * 𝔞 D3 * 𝔞 Dr * 𝔞 P * (𝔞 b) ^ 2 * 𝔞 d)) * ea + ((32 * 𝔞 D3 * 𝔞 Dr * (𝔞 P) ^ 2 * (𝔞 b) ^ 3 * 𝔞 d) + (32 * 𝔞 D3 * 𝔞 Dr * 𝔞 P * (𝔞 b) ^ 2 * (𝔞 d) ^ 2)) * ep
  exact mul_le_cancel (le_congr (congrMul hM (.eqRefl _)) (congrMul hM (.eqRefl _)) c)

/-- `lo(a/b, K) ≤ a/b − 1`, cleared: `loN·b + b·loD ≤ a·loD`. -/
theorem lo_le_pred {a b : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a) (K : PTm n) :
    Γ ⊢[PRAAx] le (loN a b K * b + b * loD a b K) (a * loD a b K) := by
  have h3 := S_le (Γ := Γ) (p := one) c3_pos c8_pos c3_sq K
  have hS := S_le (Γ := Γ) (st_pos hb hab) (Wt_pos hb hab) (st_sq hb hab) K
  have hp : Γ ⊢[PRAAx] le (succ (eb a b)) (pw two (eb a b)) := lt_pw (le_refl _) _
  have ep := pw_pos' (Γ := Γ) two_pos' (eb a b)
  have hB := LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval.one_le_Bt (a := a) hb
  have ha1 := le_trans hb hab
  have hM : Γ ⊢[PRAAx] num 8 * (two * two * (b * pw two (eb a b)) * a) * (b * pw two (eb a b)) ≐
      succ (pred (num 8 * (two * two * (b * pw two (eb a b)) * a) * (b * pw two (eb a b)))) := by
    have m := le_mul_mono (le_mul_mono hB ha1) hB
    exact pos_of_one_le (by ipra_le 32 * sl m + 31)
  exact q1_alg hM h3 hS hp (a_eq hb hab) ep

/-! ## `lo(4) ≤ 3/2` -/

theorem pw_two_two : Γ ⊢[PRAAx] pw two (two : PTm n) ≐ num 4 := by
  have e1 := natEq (pw_succ (Γ := Γ) (two : PTm n) one)
  have e2 := natEq (pw_succ (Γ := Γ) (two : PTm n) zero)
  have e3 := natEq (pw_zero (Γ := Γ) (two : PTm n))
  apply deriveNat; ipra_simps
  linear_combination e1 + 2 * e2 + 4 * e3

theorem pw_two_three : Γ ⊢[PRAAx] pw two (succ (two : PTm n)) ≐ num 8 :=
  (pw_succ _ _).eqTrans ((congrMul pw_two_two (.eqRefl _)).eqTrans (by ipra_ring))

theorem lo_four (K : PTm n) : Γ ⊢[PRAAx] le (two * loN (num 4) one K) (succ two * loD (num 4) one K) := by
  have h4 : Γ ⊢[PRAAx] le one (num 4 : PTm n) := by ipra_le 3
  have p2 := natEq (pw_two_two (Γ := Γ))
  have p3 := natEq (pw_two_three (Γ := Γ))
  have e0 : Γ ⊢[PRAAx] eb (num 4) one ≐ two :=
    eb_eq (le_refl one) h4 (by ipra_le 0 with -p2) (by ipra_le 3 with p3)
  have ePe := natEq (congrAp2 powF e0 (.eqRefl (two : PTm n)))
  have ea := natEq (a_eq (Γ := Γ) (le_refl one) h4)
  have hdt : Γ ⊢[PRAAx] dt (num 4) one ≐ zero := by
    apply deriveNat; ipra_simps
    linear_combination -ea - ePe - p2
  have hN : Γ ⊢[PRAAx] Nz K (dt (num 4) one) (st (num 4) one) ≐ zero :=
    (congrAp2 _ (.eqRefl _) (congrPairT hdt (.eqRefl _))).eqTrans (Nz_p0 K _)
  have h3 := S_le (Γ := Γ) (p := one) c3_pos c8_pos c3_sq K
  have e1 := natEq e0
  have e2 := natEq hN
  have c : Γ ⊢[PRAAx] le (two * (two * loN (num 4) one K)) (two * (succ two * loD (num 4) one K)) := by
    ipra_le 𝔞 (Dz K (dt (num 4) one) (st (num 4) one)) * sl h3 with
      -(4 * 𝔞 (Nz K one c3) * 𝔞 (Lv K zero) * 𝔞 (Pv K (st (num 4) one))) * e1 -
        4 * 𝔞 (Lv K zero) * 𝔞 (Pv K c3) * e2
  exact mul_le_cancel c

/-! ## Powers -/

/-- `lo(x P^j) ≤ lo(x) + j lo(P) + j(P − 1)/9^K`, cleared. -/
abbrev LPF (j a b P c K : PTm n) : Fm PTm n :=
  le (loN (a * pw P j) b K * loD a b K * loD P one K * Rv K c3)
    (loN a b K * loD (a * pw P j) b K * loD P one K * Rv K c3 + j * loN P one K * loD (a * pw P j) b K * loD a b K * Rv K c3 +
      j * c * loD (a * pw P j) b K * loD a b K * loD P one K)

theorem pow_alg {Xn Xd Xn1 Xd1 Yn Yd An Ad Ln Ld G c j : PTm n} (hM : Γ ⊢[PRAAx] Xd * Yd ≐ succ (pred (Xd * Yd)))
    (inv : Γ ⊢[PRAAx] le (Xn * Ad * Ld * G) (An * Xd * Ld * G + j * Ln * Xd * Ad * G + j * c * Xd * Ad * Ld))
    (sub : Γ ⊢[PRAAx] le (Yn * Xd * Ld * (one * G)) (Xn * Yd * Ld * (one * G) + Ln * Yd * Xd * (one * G) + c * (Yd * Xd * Ld)))
    (ev : Γ ⊢[PRAAx] Yn * Xd1 ≐ Xn1 * Yd) :
    Γ ⊢[PRAAx] le (Xn1 * Ad * Ld * G) (An * Xd1 * Ld * G + succ j * Ln * Xd1 * Ad * G + succ j * c * Xd1 * Ad * Ld) := by
  have ev := natEq ev
  have c' : Γ ⊢[PRAAx] le (Xd * Yd * (Xn1 * Ad * Ld * G))
      (Xd * Yd * (An * Xd1 * Ld * G + succ j * Ln * Xd1 * Ad * G + succ j * c * Xd1 * Ad * Ld)) := by
    ipra_le 𝔞 (Yd * Xd1) * sl inv + 𝔞 (Xd1 * Ad) * sl sub with (𝔞 Ad * 𝔞 G * 𝔞 Ld * 𝔞 Xd) * ev
  exact mul_le_cancel (le_congr (congrMul hM (.eqRefl _)) (congrMul hM (.eqRefl _)) c')

theorem pow_base {X0n X0d An Ad Ln Ld G c : PTm n} (ev : Γ ⊢[PRAAx] X0n * Ad ≐ An * X0d) :
    Γ ⊢[PRAAx] le (X0n * Ad * Ld * G) (An * X0d * Ld * G + zero * Ln * X0d * Ad * G + zero * c * X0d * Ad * Ld) := by
  have e := natEq ev
  ipra_le 0 with 𝔞 Ld * 𝔞 G * e

theorem pow_step {j a b P c K : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a)
    (hP : Γ ⊢[PRAAx] le one P) (hc : Γ ⊢[PRAAx] P ≐ one + c) (ih : Γ ⊢[PRAAx] LPF j a b P c K) :
    Γ ⊢[PRAAx] LPF (succ j) a b P c K := by
  have pj := one_le_of_pos' (pw_pos' (Γ := Γ) (pos_of_one_le hP) j)
  have pj1 := one_le_of_pos' (pw_pos' (Γ := Γ) (pos_of_one_le hP) (succ j))
  have hbj : Γ ⊢[PRAAx] le b (a * pw P j) := by
    have m := le_mul_mono hab pj
    ipra_le sl m
  have hbj1 : Γ ⊢[PRAAx] le b (a * pw P (succ j)) := by
    have m := le_mul_mono hab pj1
    ipra_le sl m
  have sub := lo_sub_up (a := a * pw P j) (c1 := P) (c2 := one) (k := c) hb hbj (le_refl one)
    (hc.eqTrans (.eqRefl _)) K
  have eP := natEq (pw_succ (Γ := Γ) P j)
  have hbP : Γ ⊢[PRAAx] le (b * one) ((a * pw P j) * P) := le_mul_mono hbj hP
  have ev := lo_val (a := (a * pw P j) * P) (b := b * one) (a' := a * pw P (succ j)) (b' := b)
    (by ipra_le sl hb) hbP hb hbj1 (by apply deriveNat; ipra_simps; linear_combination -(𝔞 a * 𝔞 b) * eP) K
  have hM := pos_mul (loD_pos hb hbj K) (loD_pos (by ipra_le sl hb) hbP K)
  exact pow_alg hM ih sub ev

theorem lo_pow {a b P c : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a)
    (hP : Γ ⊢[PRAAx] le one P) (hc : Γ ⊢[PRAAx] P ≐ one + c) (K j : PTm n) : Γ ⊢[PRAAx] LPF j a b P c K := by
  have hall : Γ ⊢[PRAAx] Fm.all (LPF (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift P) (Syn.shift c) (Syn.shift K)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, LeanProofs.IPRA.PTm.subst_monus,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have p0 := one_le_of_pos' (pw_pos' (Γ := Γ) (pos_of_one_le hP) zero)
      have hb0 : Γ ⊢[PRAAx] le b (a * pw P zero) := by
        have m := le_mul_mono hab p0
        ipra_le sl m
      have e0 := natEq (pw_zero (Γ := Γ) P)
      exact pow_base (lo_val hb hb0 hb hab (by apply deriveNat; ipra_simps; linear_combination 𝔞 a * 𝔞 b * e0) K)
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, LeanProofs.IPRA.PTm.subst_monus,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      have hc' : (LPF (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift P) (Syn.shift c) (Syn.shift K) :: Γ.map Fm.shift)
          ⊢[PRAAx] Syn.shift P ≐ one + Syn.shift c := by
        have b := hc.shift
        simp only [Fm.shift, Fm.subst_eq, PTm.subst_add, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at b
        exact b.wk
      exact pow_step (RobinLipSum.le_shift_one hb).wk (le_shift hab).wk (RobinLipSum.le_shift_one hP).wk hc' Prf.hyp0
  have r := Prf.allE j hall
  simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, LeanProofs.IPRA.PTm.subst_monus,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at r
  exact r

end LeanProofs.IPRA.AnalyticNumberTheory.RobinLipBound
