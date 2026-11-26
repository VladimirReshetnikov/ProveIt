import IPRADerivations.AnalyticNumberTheory.PowerResidueInversion
import IPRADerivations.AnalyticNumberTheory.PowerResidueForward
import IPRADerivations.Core.Header

/-!
# The backward transfer for progression rows (`riemann_ipra_prime_criteria_2026-11-20`, `thm:powerdivisor`)

Packet: `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`, `new-growth.tex`, proof of Theorem
`thm:powerdivisor`: "The reverse formula uses `μ(d) B_{h,q,b_d}` … In both directions the input bound applies to the
index chosen at each term because its constant precedes all residue choices."

For signed bodies `a⁺, a⁻`, `q ≥ 2`, a reduced residue `b < q` and `h ≥ 2`:

* `unit_pow`: `|u X − u Y|^K ≤ R` for an indicator `u ∈ {0, 1}` when `|X − Y|^K ≤ R` follows from `u = 1` (`K ≥ 1`);
* `rs_shift_g`, `rBg_succ`: the weighted row sums of `PowerAbstractInversion` start at `d = 1`;
* `tPr`, `tNr`, `t_sums_res`: the signed terms `μ⁺R⁺ + μ⁻R⁻` and `μ⁺R⁻ + μ⁻R⁺` with
  `R^±(d) = [gcd(d^h,q)=1] B^±_{h;q,b_{d^h}}(⌊N/d^h⌋)` (`PowerResidueInversion.Rt`);
* `backward_res_core`: `|A_{q,b}(N)|^{2r} ≤ (c+1)(8r)^{2r} N^{r+1}` from the residue-uniform row bound
  `∀b' reduced ∀M |B_{h;q,b'}(M)|^{4r} ≤ c M^{2r+1}` (`PowerResidueForward.InR` for the bodies `b_h`), by
  `PowerResidueInversion.inversion_res` and `PowerTransfer.transfer`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PowerResidueBackward

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PowerAbstractInversion (rBg RSg inst2_rBg)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerResidueInversion (Rt Rt_at inversion_res)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerResidueForward (InR inR_at)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerResidueRows (mask bvB Xp MB hyps_shift)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerResidue (res res_lt res_cop)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorPrefix (Apre)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorInversion (Zp wP wN)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorGrowth (InA mqB mq_at arg_bound mPB mNB mu_at inst2_wP_succ
  mu_mix mu_sum_le)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerTransfer (transfer TermBound k4 r8)
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd absd_le le_absd_l le_absd_r)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases eq_of_eqb)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.DiophantineNumberTheory.PrimitiveReduction (pw_zero_base)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (muP muN)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `|uX − uY|^K ≤ R` for an indicator `u`, given the bound at `u = 1` (`K ≥ 1`). -/
theorem unit_pow {u X Y K R : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hu : Γ ⊢[PRAAx] (u ≐ zero) ⋎ (u ≐ one))
    (h : ((u ≐ one) :: Γ) ⊢[PRAAx] le (pw (absd X Y) K) R) :
    Γ ⊢[PRAAx] le (pw (absd (u * X) (u * Y)) K) R := by
  refine .orE hu ?_ ?_
  · let C : List (Fm PTm n) := (u ≐ zero) :: Γ
    have z1 : C ⊢[PRAAx] u * X ≐ zero := (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
    have z2 : C ⊢[PRAAx] u * Y ≐ zero := (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
    have z : C ⊢[PRAAx] absd (u * X) (u * Y) ≐ zero :=
      (congrAdd (congrMonus z1 z2) (congrMonus z2 z1)).eqTrans
        ((congrAdd (monus_zero _) (monus_zero _)).eqTrans (add_zero _))
    have hk : C ⊢[PRAAx] K ≐ succ (pred K) := pos_of_one_le hK.wk
    exact le_congr ((congrPw z (.eqRefl _)).eqTrans (pw_zero_base hk)).eqSymm (.eqRefl _) (zero_le _)
  · let C : List (Fm PTm n) := (u ≐ one) :: Γ
    have o1 : C ⊢[PRAAx] u * X ≐ X := (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (one_mul _)
    have o2 : C ⊢[PRAAx] u * Y ≐ Y := (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (one_mul _)
    exact le_congr (congrPw (congrAdd (congrMonus o1 o2) (congrMonus o2 o1)) (.eqRefl _)).eqSymm (.eqRefl _) h

/-! ## The weighted row sums from `d = 1` -/

theorem rs_shift_g (R w : PTm 2) (N h y : PTm n) :
    Γ ⊢[PRAAx] RSg R w N h y ≐ ap2 (sumF (shiftBody (rBg R w))) N (Zp N h y) := by
  refine (sum_shift _ _ _).eqTrans ((congrAdd ?_ (.eqRefl _)).eqTrans (zero_add _))
  rw [inst2_rBg]
  exact (congrMul (congrMul sg_zero (.eqRefl _)) (.eqRefl _)).eqTrans
    ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _))

theorem rBg_succ (R w : PTm 2) (i P : PTm n) :
    Γ ⊢[PRAAx] inst2 (shiftBody (rBg R w)) i P ≐ inst2 w (succ i) P * inst2 R (succ i) P := by
  rw [inst2_shiftBody, inst2_rBg]
  exact congrMul ((congrMul (sg_succ _) (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _)

variable (aP aN : PTm 2)

/-- `t⁺ = μ⁺ R⁺ + μ⁻ R⁻` and `t⁻ = μ⁺ R⁻ + μ⁻ R⁺` at `d = i + 1`. -/
def tPr : PTm 2 := mPB * shiftBody (Rt aP) + mNB * shiftBody (Rt aN)
def tNr : PTm 2 := mPB * shiftBody (Rt aN) + mNB * shiftBody (Rt aP)

/-- `Σ_{i<N} t⁺ = R_{μ⁺}(a⁺) + R_{μ⁻}(a⁻)` and `Σ_{i<N} t⁻ = R_{μ⁺}(a⁻) + R_{μ⁻}(a⁺)`. -/
theorem t_sums_res (N h y : PTm n) :
    Γ ⊢[PRAAx] (ap2 (sumF (tPr aP aN)) N (Zp N h y) ≐ RSg (Rt aP) wP N h y + RSg (Rt aN) wN N h y) ⋏
      (ap2 (sumF (tNr aP aN)) N (Zp N h y) ≐ RSg (Rt aN) wP N h y + RSg (Rt aP) wN N h y) := by
  have pt : ∀ (Δ : List (Fm PTm (n + 1))) (i : PTm (n + 1)),
      Δ ⊢[PRAAx] (inst2 (tPr aP aN) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) ≐
          inst2 (shiftBody (rBg (Rt aP) wP)) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) +
          inst2 (shiftBody (rBg (Rt aN) wN)) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y))) ⋏
        (inst2 (tNr aP aN) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) ≐
          inst2 (shiftBody (rBg (Rt aN) wP)) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) +
          inst2 (shiftBody (rBg (Rt aP) wN)) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y))) := by
    intro Δ i
    let P : PTm (n + 1) := Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)
    have hP : inst2 (tPr aP aN) i P = inst2 (mPB : PTm 2) i P * inst2 (shiftBody (Rt aP)) i P +
        inst2 (mNB : PTm 2) i P * inst2 (shiftBody (Rt aN)) i P := by simp [inst2, tPr]
    have hN : inst2 (tNr aP aN) i P = inst2 (mPB : PTm 2) i P * inst2 (shiftBody (Rt aN)) i P +
        inst2 (mNB : PTm 2) i P * inst2 (shiftBody (Rt aP)) i P := by simp [inst2, tNr]
    rw [hP, hN, inst2_shiftBody, inst2_shiftBody]
    have mu := mu_at (Γ := Δ) i (Syn.shift N) (Syn.shift h) (Syn.shift y)
    have wu := inst2_wP_succ (Γ := Δ) i (Syn.shift N) (Syn.shift h) (Syn.shift y)
    refine .andI ?_ ?_
    · exact (congrAdd (congrMul (Prf.andE₁ mu) (.eqRefl _)) (congrMul (Prf.andE₂ mu) (.eqRefl _))).eqTrans
        (congrAdd ((rBg_succ (Rt aP) wP _ _).eqTrans (congrMul (Prf.andE₁ wu) (.eqRefl _))).eqSymm
          ((rBg_succ (Rt aN) wN _ _).eqTrans (congrMul (Prf.andE₂ wu) (.eqRefl _))).eqSymm)
    · exact (congrAdd (congrMul (Prf.andE₁ mu) (.eqRefl _)) (congrMul (Prf.andE₂ mu) (.eqRefl _))).eqTrans
        (congrAdd ((rBg_succ (Rt aN) wP _ _).eqTrans (congrMul (Prf.andE₁ wu) (.eqRefl _))).eqSymm
          ((rBg_succ (Rt aP) wN _ _).eqTrans (congrMul (Prf.andE₂ wu) (.eqRefl _))).eqSymm)
  have sh : Syn.shift (Zp N h y) = Zp (Syn.shift N) (Syn.shift h) (Syn.shift y) := by simp [Syn.shift]
  refine .andI ?_ ?_
  · refine (sum_add2 (shiftBody (rBg (Rt aP) wP)) (shiftBody (rBg (Rt aN) wN)) (tPr aP aN) (.allI (.impI ?_))).eqTrans
      (congrAdd (rs_shift_g (Rt aP) wP N h y).eqSymm (rs_shift_g (Rt aN) wN N h y).eqSymm)
    rw [sh]; exact Prf.andE₁ (pt _ _)
  · refine (sum_add2 (shiftBody (rBg (Rt aN) wP)) (shiftBody (rBg (Rt aP) wN)) (tNr aP aN) (.allI (.impI ?_))).eqTrans
      (congrAdd (rs_shift_g (Rt aN) wP N h y).eqSymm (rs_shift_g (Rt aP) wN N h y).eqSymm)
    rw [sh]; exact Prf.andE₂ (pt _ _)

/-- `|A_{q,b}(N)|^{2r} ≤ (c+1)(8r)^{2r} N^{r+1}` from `∀b' reduced ∀M |B_{h;q,b'}(M)|^{4r} ≤ c M^{2r+1}`. -/
theorem backward_res_core {q b h r c : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hb : Γ ⊢[PRAAx] lt b q)
    (hc : Γ ⊢[PRAAx] gcd b q ≐ one) (hh : Γ ⊢[PRAAx] le two h) (hr : Γ ⊢[PRAAx] le one r) (y : PTm n)
    (hB : Γ ⊢[PRAAx] InR (bvB aP) (bvB aN) q (pairT h y) r c) (N : PTm n) :
    Γ ⊢[PRAAx] le (pw (absd (Apre (mask aP) N (pairT (pairT q b) y)) (Apre (mask aN) N (pairT (pairT q b) y)))
      (two * r)) (succ c * pw (r8 r) (two * r) * pw N (succ r)) := by
  have hh1 : Γ ⊢[PRAAx] le one h := by ipra_le sl hh + 1
  have ht : Γ ⊢[PRAAx] TermBound (tPr aP aN) (tNr aP aN) mqB N (Zp N h (Xp q b h y)) r c := by
    refine .allI (.impI ?_)
    rw [show Syn.shift (Zp N h (Xp q b h y)) =
      Zp (Syn.shift N) (Syn.shift h) (Xp (Syn.shift q) (Syn.shift b) (Syn.shift h) (Syn.shift y)) by simp [Syn.shift]]
    let Λ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    obtain ⟨hq', hb', hc'⟩ := hyps_shift hq hb hc
    have hr' : Λ ⊢[PRAAx] le one (Syn.shift r) := by
      have b : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift r) := by simpa [Fm.shift, Syn.shift] using hr.shift
      exact b.wk
    let P : PTm (n + 1) := Zp (Syn.shift N) (Syn.shift h) (Xp (Syn.shift q) (Syn.shift b) (Syn.shift h) (Syn.shift y))
    let D : PTm (n + 1) := pw (succ (var 0)) (Syn.shift h)
    let M : PTm (n + 1) := quo (Syn.shift N) D
    let bD : PTm (n + 1) := res D (Syn.shift q) (Syn.shift b)
    let u : PTm (n + 1) := eqb (gcd D (Syn.shift q)) one
    have hP : inst2 (tPr aP aN) (var 0) P = inst2 (mPB : PTm 2) (var 0) P * inst2 (shiftBody (Rt aP)) (var 0) P +
        inst2 (mNB : PTm 2) (var 0) P * inst2 (shiftBody (Rt aN)) (var 0) P := by simp [inst2, tPr]
    have hN : inst2 (tNr aP aN) (var 0) P = inst2 (mPB : PTm 2) (var 0) P * inst2 (shiftBody (Rt aN)) (var 0) P +
        inst2 (mNB : PTm 2) (var 0) P * inst2 (shiftBody (Rt aP)) (var 0) P := by simp [inst2, tNr]
    rw [hP, hN, inst2_shiftBody, inst2_shiftBody]
    have mu := mu_at (Γ := Λ) (var 0) (Syn.shift N) (Syn.shift h)
      (Xp (Syn.shift q) (Syn.shift b) (Syn.shift h) (Syn.shift y))
    have rP : Λ ⊢[PRAAx] inst2 (Rt aP) (succ (var 0)) P ≐ u * MB aP M (Syn.shift q) bD (Syn.shift h) (Syn.shift y) :=
      Rt_at aP _ _ _ _ _ _
    have rN : Λ ⊢[PRAAx] inst2 (Rt aN) (succ (var 0)) P ≐ u * MB aN M (Syn.shift q) bD (Syn.shift h) (Syn.shift y) :=
      Rt_at aN _ _ _ _ _ _
    have em := mq_at (Γ := Λ) (var 0) (Syn.shift N) (Syn.shift h)
      (Xp (Syn.shift q) (Syn.shift b) (Syn.shift h) (Syn.shift y))
    let XP : PTm (n + 1) := u * MB aP M (Syn.shift q) bD (Syn.shift h) (Syn.shift y)
    let XN : PTm (n + 1) := u * MB aN M (Syn.shift q) bD (Syn.shift h) (Syn.shift y)
    have ep : Λ ⊢[PRAAx] inst2 (mPB : PTm 2) (var 0) P * inst2 (Rt aP) (succ (var 0)) P +
        inst2 (mNB : PTm 2) (var 0) P * inst2 (Rt aN) (succ (var 0)) P ≐
        muP (succ (Syn.shift N)) (succ (var 0)) * XP + muN (succ (Syn.shift N)) (succ (var 0)) * XN :=
      congrAdd (congrMul (Prf.andE₁ mu) rP) (congrMul (Prf.andE₂ mu) rN)
    have en : Λ ⊢[PRAAx] inst2 (mPB : PTm 2) (var 0) P * inst2 (Rt aN) (succ (var 0)) P +
        inst2 (mNB : PTm 2) (var 0) P * inst2 (Rt aP) (succ (var 0)) P ≐
        muP (succ (Syn.shift N)) (succ (var 0)) * XN + muN (succ (Syn.shift N)) (succ (var 0)) * XP :=
      congrAdd (congrMul (Prf.andE₁ mu) rN) (congrMul (Prf.andE₂ mu) rP)
    have mix := mu_mix (Γ := Λ) (b := XP) (c := XN) (mu_sum_le (succ (Syn.shift N)) (succ (var 0)))
    have pw1 := pw_le_pw (k4 (Syn.shift r)) mix
    have hk : Λ ⊢[PRAAx] le one (k4 (Syn.shift r)) := by
      ipra_le sl hr' + 𝔞 (Syn.shift r) + 𝔞 (Syn.shift r) + 𝔞 (Syn.shift r)
    have ub : Λ ⊢[PRAAx] le (pw (absd XP XN) (k4 (Syn.shift r))) (Syn.shift c * pw M (succ (two * Syn.shift r))) := by
      refine unit_pow hk (eqb_cases _ _) ?_
      let C : List (Fm PTm (n + 1)) := (u ≐ one) :: Λ
      have hu : C ⊢[PRAAx] gcd D (Syn.shift q) ≐ one := eq_of_eqb Prf.hyp0
      have hq'' : C ⊢[PRAAx] le two (Syn.shift q) := hq'.wk.wk
      have i := inR_at (bvB aP) (bvB aN) hB bD
      have iA := Prf.impE (Prf.impE (i.wk.wk : C ⊢[PRAAx] _) (res_lt hq'')) (res_cop hq'' hu hc'.wk.wk)
      have b := Prf.allE M iA
      simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_monus, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at b
      rw [shift_pairT h y] at b
      exact b
    refine le_congr (congrPw (congrAdd (congrMonus ep en) (congrMonus en ep)) (.eqRefl _)).eqSymm
      (congrMul (.eqRefl _) (congrPw em (.eqRefl _))).eqSymm (le_trans pw1 ub)
  have tr := transfer (tPr aP aN) (tNr aP aN) mqB hr (arg_bound hh N (Xp q b h y)) ht
  have ts := t_sums_res aP aN (Γ := Γ) N h (Xp q b h y)
  have iP := natEq (inversion_res aP hq hb hc hh1 N y)
  have iN := natEq (inversion_res aN hq hb hc hh1 N y)
  have s1 := natEq (Prf.andE₁ ts)
  have s2 := natEq (Prf.andE₂ ts)
  have la := le_absd_l (Γ := Γ) (ap2 (sumF (tPr aP aN)) N (Zp N h (Xp q b h y)))
    (ap2 (sumF (tNr aP aN)) N (Zp N h (Xp q b h y)))
  have lb := le_absd_r (Γ := Γ) (ap2 (sumF (tPr aP aN)) N (Zp N h (Xp q b h y)))
    (ap2 (sumF (tNr aP aN)) N (Zp N h (Xp q b h y)))
  have hA : Γ ⊢[PRAAx] le (absd (Apre (mask aP) N (pairT (pairT q b) y)) (Apre (mask aN) N (pairT (pairT q b) y)))
      (absd (ap2 (sumF (tPr aP aN)) N (Zp N h (Xp q b h y))) (ap2 (sumF (tNr aP aN)) N (Zp N h (Xp q b h y)))) := by
    refine absd_le ?_ ?_
    · ipra_le sl la with s1 - s2 + iP - iN
    · ipra_le sl lb with s2 - s1 - iP + iN
  exact le_trans (pw_le_pw _ hA) tr

end LeanProofs.IPRA.AnalyticNumberTheory.PowerResidueBackward
