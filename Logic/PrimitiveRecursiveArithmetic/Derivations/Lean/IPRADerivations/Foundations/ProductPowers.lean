import IPRADerivations.AnalyticNumberTheory.Euler
import IPRADerivations.Foundations.SignedSums
import IPRADerivations.Combinatorics.BinomialTheorem
import IPRADerivations.Core.Fubini
import IPRADerivations.Core.ProdLemmas
import IPRADerivations.AnalyticNumberTheory.Mobius
import IPRADerivations.Core.CommonLemmas

/-!
# Products of powers with a constant base, and delta products

Framework layer (first use: Wilson's product and Euler's criterion for
`diophantine-number-theory/quadratic_reciprocity_ipra`).

* `prod_pw_of`: `∏_{i<N} B(i, x) = c^{Σ_{i<N} e(i, y)}` when `B(i, x) = c^{e(i, y)}` for `i < N`. It is
  `Euler.prod_pw`, whose base is the first component of the parameter, with the base and the parameters made
  arbitrary.
* `prod_delta`: `∏_{i<N} F(i, x)^{[c = i]} = F(c, x)` for `c < N`: the product analogue of
  `Core/Fubini.sum_delta`. No new induction is needed: `F(i)^{[c = i]} = F(c)^{[c = i]}`, so the base is
  constant, and `Σ_{i<N} [c = i] = 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (prod_pw)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem inst2_pwfst (e : PTm 2) (i y : PTm n) :
    inst2 (pw (fstT (var 1)) e) i y = pw (fstT y) (inst2 e i y) := by simp [inst2]

/-- `∏_{i<N} B(i, x) = c^{Σ_{i<N} e(i, y)}` when `B(i, x) = c^{e(i, y)}` for `i < N`. -/
theorem prod_pw_of (B e : PTm 2) {N c x y : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 B (var 0) (Syn.shift x) ≐ pw (Syn.shift c) (inst2 e (var 0) (Syn.shift y))))) :
    Γ ⊢[PRAAx] ap2 (prodF B) N x ≐ pw c (ap2 (sumF e) N y) := by
  have t1 : Γ ⊢[PRAAx] ap2 (prodF B) N x ≐ ap2 (prodF (pw (fstT (var 1)) (sndB e))) N (pairT c y) := by
    refine prod_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, inst2_pwfst, inst2_sndB]
    exact (Prf.impE h.allOpen.wk Prf.hyp0).eqTrans
      (congrPw (fst_pair _ _).eqSymm (congrInst2 e (.eqRefl _) (snd_pair _ _)).eqSymm)
  have t2 : Γ ⊢[PRAAx] ap2 (sumF (sndB e)) N (pairT c y) ≐ ap2 (sumF e) N y := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, inst2_sndB]
    exact congrInst2 e (.eqRefl _) (snd_pair _ _)
  exact t1.eqTrans ((prod_pw (sndB e) N (pairT c y)).eqTrans (congrPw (fst_pair _ _) t2))

/-! ## Delta products -/

/-- `F(i, snd z)^{[fst z = i]}` over `0 = i`, `1 = z = ⟨c, x⟩`. -/
abbrev pdB (F : PTm 2) : PTm 2 := pw (sndB F) (eqb (fstT (var 1)) (var 0))

theorem inst2_pdB (F : PTm 2) (i z : PTm n) :
    inst2 (pdB F) i z = pw (inst2 F i (sndT z)) (eqb (fstT z) i) := by
  have e : inst2 (pdB F) i z = pw (inst2 (sndB F) i z) (eqb (fstT z) i) := by simp [inst2]
  rw [e, inst2_sndB]

alias mul_one_e := Common.mul_one_right'

/-- `f(i)^{[c = i]} = f(c)^{[c = i] · 1}`. -/
theorem delta_pt (F : PTm 2) (i c x : PTm n) :
    Γ ⊢[PRAAx] pw (inst2 F i x) (eqb c i) ≐ pw (inst2 F c x) (eqb c i * one) := by
  refine .orE (eq_or_ne c i) ?_ ?_
  · have e : ((c ≐ i) :: Γ) ⊢[PRAAx] c ≐ i := Prf.hyp0
    exact congrPw (congrInst2 F e.eqSymm (.eqRefl _)) (mul_one_e _)
  · have z : (neg (c ≐ i) :: Γ) ⊢[PRAAx] eqb c i ≐ zero := eqb_of_ne Prf.hyp0
    exact ((congrPw (.eqRefl _) z).eqTrans (pw_zero _)).eqTrans
      ((congrPw (.eqRefl _) ((congrMul z (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (pw_zero _)).eqSymm

/-- `∏_{i<N} F(i, x)^{[c = i]} = F(c, x)` for `c < N`. -/
theorem prod_delta (F : PTm 2) {N c x : PTm n} (hc : Γ ⊢[PRAAx] lt c N) :
    Γ ⊢[PRAAx] ap2 (prodF (pdB F)) N (pairT c x) ≐ inst2 F c x := by
  have one_i : inst2 (one : PTm 2) c x = one := by simp [inst2]
  have s : Γ ⊢[PRAAx] ap2 (sumF (dB (one : PTm 2))) N (pairT c x) ≐ one := by
    have h := sum_delta (Γ := Γ) (one : PTm 2) (x := x) hc
    rw [one_i] at h
    exact h
  refine (prod_pw_of (pdB F) (dB (one : PTm 2)) (c := inst2 F c x) (y := pairT c x) (.allI (.impI ?_))).eqTrans
    ((congrPw (.eqRefl _) s).eqTrans (pw_one _))
  have sc : Syn.shift (inst2 F c x) = inst2 F (Syn.shift c) (Syn.shift x) := by
    simp only [Syn.shift, subst_inst2]
  have one_v : inst2 (one : PTm 2) (var 0 : PTm (n + 1)) (sndT (pairT (Syn.shift c) (Syn.shift x))) = one := by
    simp [inst2]
  rw [shift_pairT, sc, inst2_pdB, inst2_dB, one_v]
  exact (congrPw (congrInst2 F (.eqRefl _) (snd_pair _ _)) (AnalyticNumberTheory.Mobius.congrEqb' (fst_pair _ _) (.eqRefl _))).eqTrans
    ((delta_pt F _ _ _).eqTrans (congrPw (.eqRefl _) (congrMul (AnalyticNumberTheory.Mobius.congrEqb' (fst_pair _ _) (.eqRefl _)).eqSymm (.eqRefl _))))

end LeanProofs.IPRA
