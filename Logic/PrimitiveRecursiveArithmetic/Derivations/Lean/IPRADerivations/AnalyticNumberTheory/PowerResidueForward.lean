import IPRADerivations.AnalyticNumberTheory.PowerResidueRows
import IPRADerivations.AnalyticNumberTheory.PowerDivisorGrowth
import IPRADerivations.DiophantineNumberTheory.PrimitiveReduction
import IPRADerivations.Core.Header

/-!
# The forward transfer for progression rows (`riemann_ipra_prime_criteria_2026-11-20`, `thm:powerdivisor`)

Packet: `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`, `new-growth.tex`, proof of Theorem
`thm:powerdivisor`: "The forward formula now uses `A_{q,b_d}` at its `d`th term and skips the nonunits … In both
directions the input bound applies to the index chosen at each term because its constant precedes all residue choices …
use `t_d = 0` at an excluded residue."

* `subst_InA`: substitution commutes with the input-bound formula `PowerDivisorGrowth.InA`;
* `InR`: the input bound uniform over the reduced residues `b' < q`:
  `∀b' (b' < q → gcd(b', q) = 1 → ∀M |A_{q,b'}(M)|^{4r} ≤ c M^{2r+1})`;
* `forward_res_core`: for `q ≥ 2`, reduced `b < q`, `h ≥ 2`, `r ≥ 1`, `InR` gives
  `|B_{h;q,b}(N)|^{2r} ≤ (c+1)(8r)^{2r} N^{r+1}`: by `PowerResidueRows.masked_B` the row is the twisted sum, its `d`th
  term is `[gcd(d^h, q) = 1] A_{q,b_{d^h}}(⌊N/d^h⌋)` (`PowerResidueRows.tw_A`), which is `0` at a nonunit and is bounded
  by `InR` at the reduced residue `b_{d^h}` (`PowerResidue.res_lt`, `PowerResidue.res_cop`) otherwise; then
  `PowerTransfer.transfer`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PowerResidueForward

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorPrefix (Apre)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerTwistPrefix (tBt tbtB tbtB_at)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerResidue (res res_lt res_cop)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerResidueRows
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorGrowth (InA mqB mq_at arg_bound allE_shift subst_cons_shift)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorInversion (Zp)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerTransfer (transfer TermBound k4 r8)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases eq_of_eqb)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.DiophantineNumberTheory.PrimitiveReduction (pw_zero_base)
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

variable (aP aN : PTm 2)

theorem subst_InA {m : ℕ} (σ : Fin n → PTm m) (x r c : PTm n) :
    (InA aP aN x r c).subst σ = InA aP aN (Syn.subst σ x) (Syn.subst σ r) (Syn.subst σ c) := by
  simp [InA, Fm.subst_all, subst_le, subst_ap2, subst_up_shift_pal, Syn.up_zero]

/-- The input bound at every reduced residue `b' < q`. -/
abbrev InR (q y r c : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift q) ⟶ (gcd (var 0) (Syn.shift q) ≐ one) ⟶
    InA (mask aP) (mask aN) (pairT (pairT (Syn.shift q) (var 0)) (Syn.shift y)) (Syn.shift r) (Syn.shift c))

/-- `InR` at a residue term `t` of the shifted context. -/
theorem inR_at {q y r c : PTm n} (hA : Γ ⊢[PRAAx] InR aP aN q y r c) (t : PTm (n + 1)) :
    (Γ.map Fm.shift) ⊢[PRAAx] lt t (Syn.shift q) ⟶ (gcd t (Syn.shift q) ≐ one) ⟶
      InA (mask aP) (mask aN) (pairT (pairT (Syn.shift q) t) (Syn.shift y)) (Syn.shift r) (Syn.shift c) := by
  have b := allE_shift hA t
  simp only [Fm.subst_imp, lt, subst_le, Fm.subst_eq, subst_ex2, subst_InA, subst_pairT, Syn.subst_var,
    Fin.cases_zero, subst_cons_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at b
  exact b

/-- `|B_{h;q,b}(N)|^{2r} ≤ (c+1)(8r)^{2r} N^{r+1}` from the residue-uniform bound `|A_{q,b'}(M)|^{4r} ≤ c M^{2r+1}`. -/
theorem forward_res_core {q b h r c : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hb : Γ ⊢[PRAAx] lt b q)
    (hc : Γ ⊢[PRAAx] gcd b q ≐ one) (hh : Γ ⊢[PRAAx] le two h) (hr : Γ ⊢[PRAAx] le one r) (y : PTm n)
    (hA : Γ ⊢[PRAAx] InR aP aN q y r c) (N : PTm n) :
    Γ ⊢[PRAAx] le (pw (absd (MB aP N q b h y) (MB aN N q b h y)) (two * r))
      (succ c * pw (r8 r) (two * r) * pw N (succ r)) := by
  have hh1 : Γ ⊢[PRAAx] le one h := by ipra_le sl hh + 1
  have ht : Γ ⊢[PRAAx] TermBound (tbtB (tw aP)) (tbtB (tw aN)) mqB N (Zp N h (Xp q b h y)) r c := by
    refine .allI (.impI ?_)
    rw [show Syn.shift (Zp N h (Xp q b h y)) =
      Zp (Syn.shift N) (Syn.shift h) (Xp (Syn.shift q) (Syn.shift b) (Syn.shift h) (Syn.shift y)) by simp [Syn.shift]]
    let Λ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    obtain ⟨hq', hb', hc'⟩ := hyps_shift hq hb hc
    have hr' : Λ ⊢[PRAAx] le one (Syn.shift r) := by
      have b : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift r) := by simpa [Fm.shift, Syn.shift] using hr.shift
      exact b.wk
    let M : PTm (n + 1) := quo (Syn.shift N) (pw (succ (var 0)) (Syn.shift h))
    let D : PTm (n + 1) := pw (succ (var 0)) (Syn.shift h)
    let bD : PTm (n + 1) := res D (Syn.shift q) (Syn.shift b)
    let u : PTm (n + 1) := eqb (gcd D (Syn.shift q)) one
    let xD : PTm (n + 1) := pairT (pairT (Syn.shift q) bD) (Syn.shift y)
    have eP : Λ ⊢[PRAAx] inst2 (tbtB (tw aP)) (var 0)
        (Zp (Syn.shift N) (Syn.shift h) (Xp (Syn.shift q) (Syn.shift b) (Syn.shift h) (Syn.shift y))) ≐
        u * Apre (mask aP) M xD :=
      (tbtB_at (tw aP) _ _ _ _).eqTrans (tw_A aP _ _ _ _ _ _)
    have eN : Λ ⊢[PRAAx] inst2 (tbtB (tw aN)) (var 0)
        (Zp (Syn.shift N) (Syn.shift h) (Xp (Syn.shift q) (Syn.shift b) (Syn.shift h) (Syn.shift y))) ≐
        u * Apre (mask aN) M xD :=
      (tbtB_at (tw aN) _ _ _ _).eqTrans (tw_A aN _ _ _ _ _ _)
    have em := mq_at (Γ := Λ) (var 0) (Syn.shift N) (Syn.shift h)
      (Xp (Syn.shift q) (Syn.shift b) (Syn.shift h) (Syn.shift y))
    refine le_congr (congrPw (congrAdd (congrMonus eP eN) (congrMonus eN eP)) (.eqRefl _)).eqSymm
      (congrMul (.eqRefl _) (congrPw em (.eqRefl _))).eqSymm ?_
    refine .orE (eqb_cases (Γ := Λ) (gcd D (Syn.shift q)) one) ?_ ?_
    · -- a nonunit: the term vanishes
      let C : List (Fm PTm (n + 1)) := (u ≐ zero) :: Λ
      have z : C ⊢[PRAAx] absd (u * Apre (mask aP) M xD) (u * Apre (mask aN) M xD) ≐ zero := by
        have z1 : C ⊢[PRAAx] u * Apre (mask aP) M xD ≐ zero :=
          (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
        have z2 : C ⊢[PRAAx] u * Apre (mask aN) M xD ≐ zero :=
          (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
        exact (congrAdd (congrMonus z1 z2) (congrMonus z2 z1)).eqTrans
          ((congrAdd (monus_zero _) (monus_zero _)).eqTrans (add_zero _))
      have hk : C ⊢[PRAAx] k4 (Syn.shift r) ≐ succ (pred (k4 (Syn.shift r))) :=
        pos_of_one_le (by ipra_le sl hr'.wk + 𝔞 (Syn.shift r) + 𝔞 (Syn.shift r) + 𝔞 (Syn.shift r))
      exact le_congr ((congrPw z (.eqRefl _)).eqTrans (pw_zero_base hk)).eqSymm (.eqRefl _) (zero_le _)
    · -- a unit: the input bound at the reduced residue `b_D`
      let C : List (Fm PTm (n + 1)) := (u ≐ one) :: Λ
      have hu : C ⊢[PRAAx] gcd D (Syn.shift q) ≐ one := eq_of_eqb Prf.hyp0
      have hq'' : C ⊢[PRAAx] le two (Syn.shift q) := hq'.wk.wk
      have i := inR_at aP aN hA bD
      have iA : C ⊢[PRAAx] InA (mask aP) (mask aN) xD (Syn.shift r) (Syn.shift c) :=
        Prf.impE (Prf.impE (i.wk.wk : C ⊢[PRAAx] _) (res_lt hq'')) (res_cop hq'' hu hc'.wk.wk)
      have b := Prf.allE M iA
      simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_monus, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at b
      have o1 : C ⊢[PRAAx] u * Apre (mask aP) M xD ≐ Apre (mask aP) M xD :=
        (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (one_mul _)
      have o2 : C ⊢[PRAAx] u * Apre (mask aN) M xD ≐ Apre (mask aN) M xD :=
        (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (one_mul _)
      exact le_congr (congrPw (congrAdd (congrMonus o1 o2) (congrMonus o2 o1)) (.eqRefl _)).eqSymm (.eqRefl _) b
  have tr := transfer (tbtB (tw aP)) (tbtB (tw aN)) mqB hr (arg_bound hh N (Xp q b h y)) ht
  have s1 := masked_B aP hq hb hc hh1 N y
  have s2 := masked_B aN hq hb hc hh1 N y
  exact le_congr (congrPw (congrAdd (congrMonus s1 s2) (congrMonus s2 s1)) (.eqRefl _)).eqSymm (.eqRefl _) tr

end LeanProofs.IPRA.AnalyticNumberTheory.PowerResidueForward
