import IPRADerivations.Probability.MedianWeighted
import IPRADerivations.Foundations.EigenvalueBound
import IPRADerivations.Foundations.MixedRadix

/-!
# Finite error budgets

Packet: `analysis/beta_function_ipra_2026-11-16`, `paper/sections/02_foundations.tex`, Lemma "Finite error
budgets": if `|a_j − b_j| ≤ ε` for `j < s`, then

`|∑_{j<s} a_j − ∑_{j<s} b_j| ≤ s ε`, `|∏_{j<s} a_j − ∏_{j<s} b_j| ≤ s M^{s−1} ε` if `|a_j|, |b_j| ≤ M`, and
`|a^{−1} − b^{−1}| ≤ ε/d²` if `|a|, |b| ≥ d`;

"the telescope is proved by quantifier-free induction on `s`". Values are natural numerators over a common
denominator, `|x − y|` is `ad x y` (`Probability/Variance`), and the approximations are bodies `a(j, x)`,
`b(j, x)`:

* `ad_tri`: `|x − z| ≤ |x − y| + |y − z|`;
* `ad_prod_step`: `|x u − y v| ≤ x |u − v| + v |x − y|`, the step of the product telescope;
* `sum_budget`: `|∑_{j<s} a_j − ∑_{j<s} b_j| ≤ s ε`;
* `prod_budget`: for `s + 1` factors with `a_j, b_j ≤ M`, `|∏ a − ∏ b| ≤ (s + 1) M^s ε`, together with
  `∏ a ≤ M^{s+1}` and `∏ b ≤ M^{s+1}`;
* `inv_budget`: for `a, b ≥ d`, `d² |a − b| ≤ ε a b`, i.e. `|1/a − 1/b| = |a − b|/(a b) ≤ ε/d²`.

These are reusable for any finite approximation argument (they are the budgets of the Beta packet's
precision allocation).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.ErrorBudgets

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_add_le ad_mul)
open LeanProofs.IPRA.Foundations.EigenvalueBound (ad_le_of le_add_ad)
open LeanProofs.IPRA.Foundations.MixedRadix (prod_succ')
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem congrAd' {a a' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] ad a b ≐ ad a' b' :=
  congrAdd (congrMonus h₁ h₂) (congrMonus h₂ h₁)

/-- `|x − z| ≤ |x − y| + |y − z|`. -/
theorem ad_tri (x y z : PTm n) : Γ ⊢[PRAAx] le (ad x z) (ad x y + ad y z) := by
  refine ad_le_of ?_ ?_
  · have a := le_add_ad (Γ := Γ) x y
    have b := le_add_ad (Γ := Γ) y z
    ipra_le sl a + sl b
  · have c := le_add_ad (Γ := Γ) z y
    have d := le_add_ad (Γ := Γ) y x
    ipra_le sl c + sl d

/-- `|x u − y v| ≤ x |u − v| + v |x − y|`. -/
theorem ad_prod_step (x y u v : PTm n) : Γ ⊢[PRAAx] le (ad (x * u) (y * v)) (x * ad u v + v * ad x y) := by
  have t := ad_tri (Γ := Γ) (x * u) (x * v) (y * v)
  have m₁ := natEq (ad_mul (Γ := Γ) x u v)
  have m₂ := natEq ((congrAd' (mul_comm (Γ := Γ) x v) (mul_comm y v)).eqTrans (ad_mul v x y))
  ipra_le sl t using linear_combination -m₁ - m₂

/-! ## Sums -/

section Sums

variable (a b : PTm 2)

theorem sum_budget_step {K x eps : PTm n}
    (hK : Γ ⊢[PRAAx] le (ad (inst2 a K x) (inst2 b K x)) eps)
    (ih : Γ ⊢[PRAAx] le (ad (ap2 (sumF a) K x) (ap2 (sumF b) K x)) (K * eps)) :
    Γ ⊢[PRAAx] le (ad (ap2 (sumF a) (succ K) x) (ap2 (sumF b) (succ K) x)) (succ K * eps) := by
  have c := congrAd' (sum_succ' (Γ := Γ) a K x) (sum_succ' b K x)
  have t := ad_add_le (Γ := Γ) (ap2 (sumF a) K x) (inst2 a K x) (ap2 (sumF b) K x) (inst2 b K x)
  have e := natEq c
  ipra_le sl t + sl ih + sl hK using linear_combination -e

/-- `|∑_{j<s} a_j − ∑_{j<s} b_j| ≤ s ε`. -/
theorem sum_budget (eps s x : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift s) ⟶
      le (ad (inst2 a (var 0) (Syn.shift x)) (inst2 b (var 0) (Syn.shift x))) (Syn.shift eps))) :
    Γ ⊢[PRAAx] le (ad (ap2 (sumF a) s x) (ap2 (sumF b) s x)) (s * eps) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift s) ⟶
      le (ad (ap2 (sumF a) (var 0) (Syn.shift x)) (ap2 (sumF b) (var 0) (Syn.shift x))) (var 0 * Syn.shift eps)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      refine .impI ?_
      have s₁ := sum_zero (Γ := le zero s :: Γ) a x
      have s₂ := sum_zero (Γ := le zero s :: Γ) b x
      have m := natEq (congrAd' s₁ s₂)
      have z := natEq (monus_self (Γ := le zero s :: Γ) (zero : PTm n))
      ipra_le 0 using linear_combination -m - 2 * z
    · simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      have hk : (le (succ (var 0)) (Syn.shift s) ::
          (le (var 0) (Syn.shift s) ⟶
            le (ad (ap2 (sumF a) (var 0) (Syn.shift x)) (ap2 (sumF b) (var 0) (Syn.shift x)))
              (var 0 * Syn.shift eps)) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0)) (Syn.shift s) := Prf.hyp0
      exact sum_budget_step a b (Prf.impE h.allOpen.wk.wk hk) (Prf.impE Prf.hyp1 (le_trans (le_succ_self _) hk))
  have h2 := Prf.allE s hall
  simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl s)

end Sums

/-! ## Products -/

section Products

variable (a b : PTm 2)

/-- The invariant at `K + 1` factors. -/
abbrev PInv (K x M eps : PTm n) : Fm PTm n :=
  (le (ad (ap2 (prodF a) (succ K) x) (ap2 (prodF b) (succ K) x)) (succ K * pw M K * eps) ⋏
    le (ap2 (prodF a) (succ K) x) (pw M (succ K))) ⋏ le (ap2 (prodF b) (succ K) x) (pw M (succ K))

theorem prod_one (f : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] ap2 (prodF f) (succ zero) x ≐ inst2 f zero x := by
  have p := natEq (prod_succ' (Γ := Γ) f zero x)
  have z := natEq (prod_zero (Γ := Γ) f x)
  apply deriveNat; ipra_simps; rw [p, z]; ring

theorem prod_budget_base {x M eps : PTm n}
    (h₀ : Γ ⊢[PRAAx] le (ad (inst2 a zero x) (inst2 b zero x)) eps)
    (ha : Γ ⊢[PRAAx] le (inst2 a zero x) M) (hb : Γ ⊢[PRAAx] le (inst2 b zero x) M) :
    Γ ⊢[PRAAx] PInv a b zero x M eps := by
  have pa := prod_one (Γ := Γ) a x
  have pb := prod_one (Γ := Γ) b x
  have m := natEq (congrAd' pa pb)
  have pa' := natEq pa
  have pb' := natEq pb
  have w₀ := natEq (pw_zero (Γ := Γ) M)
  have w₁ := natEq (pw_succ (Γ := Γ) M zero)
  refine .andI (.andI ?_ ?_) ?_
  · ipra_le sl h₀ using rw [w₀]; linear_combination -m
  · ipra_le sl ha using rw [w₁, w₀, pa']; ring
  · ipra_le sl hb using rw [w₁, w₀, pb']; ring

theorem prod_budget_step {K x M eps : PTm n}
    (hK : Γ ⊢[PRAAx] le (ad (inst2 a (succ K) x) (inst2 b (succ K) x)) eps)
    (ha : Γ ⊢[PRAAx] le (inst2 a (succ K) x) M) (hb : Γ ⊢[PRAAx] le (inst2 b (succ K) x) M)
    (ih : Γ ⊢[PRAAx] PInv a b K x M eps) : Γ ⊢[PRAAx] PInv a b (succ K) x M eps := by
  have i₁ := Prf.andE₁ (Prf.andE₁ ih)
  have i₂ := Prf.andE₂ (Prf.andE₁ ih)
  have i₃ := Prf.andE₂ ih
  have pa := prod_succ' (Γ := Γ) a (succ K) x
  have pb := prod_succ' (Γ := Γ) b (succ K) x
  have st := ad_prod_step (Γ := Γ) (ap2 (prodF a) (succ K) x) (ap2 (prodF b) (succ K) x)
    (inst2 a (succ K) x) (inst2 b (succ K) x)
  have m := natEq (congrAd' pa pb)
  have pa' := natEq pa
  have pb' := natEq pb
  have w := natEq (pw_succ (Γ := Γ) M (succ K))
  have w' := natEq (pw_succ (Γ := Γ) M K)
  have e₁ := le_mul_mono i₂ hK
  have e₂ := le_mul_mono hb i₁
  refine .andI (.andI ?_ ?_) ?_
  · ipra_le sl st + sl e₁ + sl e₂ using
      rw [w']
      linear_combination -m
  · have e := le_mul_mono i₂ ha
    ipra_le sl e using rw [pa', w]
  · have e := le_mul_mono i₃ hb
    ipra_le sl e using rw [pb', w]

/-- `|∏_{j≤s} a_j − ∏_{j≤s} b_j| ≤ (s + 1) M^s ε` for `a_j, b_j ≤ M` (the hypotheses at `j = 0` and at
`j = i + 1` for `i < s`), with `∏ a, ∏ b ≤ M^{s+1}`. -/
theorem prod_budget (M eps s x : PTm n)
    (h₀ : Γ ⊢[PRAAx] (le (ad (inst2 a zero x) (inst2 b zero x)) eps ⋏ le (inst2 a zero x) M) ⋏
      le (inst2 b zero x) M)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift s) ⟶
      ((le (ad (inst2 a (succ (var 0)) (Syn.shift x)) (inst2 b (succ (var 0)) (Syn.shift x))) (Syn.shift eps) ⋏
        le (inst2 a (succ (var 0)) (Syn.shift x)) (Syn.shift M)) ⋏
          le (inst2 b (succ (var 0)) (Syn.shift x)) (Syn.shift M)))) :
    Γ ⊢[PRAAx] PInv a b s x M eps := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift s) ⟶
      PInv a b (var 0) (Syn.shift x) (Syn.shift M) (Syn.shift eps)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, ⟨le_QF _ _, le_QF _ _⟩, le_QF _ _⟩ ?_ ?_
    · simp only [PInv, Fm.subst_imp, Fm.subst_and, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      have h0 := h₀.wk (ψ := le zero s)
      exact prod_budget_base a b (Prf.andE₁ (Prf.andE₁ h0)) (Prf.andE₂ (Prf.andE₁ h0)) (Prf.andE₂ h0)
    · simp only [PInv, Fm.subst_imp, Fm.subst_and, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      have hk : (le (succ (var 0)) (Syn.shift s) ::
          (le (var 0) (Syn.shift s) ⟶ PInv a b (var 0) (Syn.shift x) (Syn.shift M) (Syn.shift eps)) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0)) (Syn.shift s) := Prf.hyp0
      have hs := Prf.impE h.allOpen.wk.wk hk
      exact prod_budget_step a b (Prf.andE₁ (Prf.andE₁ hs)) (Prf.andE₂ (Prf.andE₁ hs)) (Prf.andE₂ hs)
        (Prf.impE Prf.hyp1 (le_trans (le_succ_self _) hk))
  have h2 := Prf.allE s hall
  simp only [PInv, Fm.subst_imp, Fm.subst_and, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h2
  exact .impE h2 (le_refl s)

end Products

/-! ## Reciprocals -/

/-- `|1/a − 1/b| ≤ ε/d²` for `a, b ≥ d`: `d² |a − b| ≤ ε a b`. -/
theorem inv_budget {a b d eps : PTm n} (ha : Γ ⊢[PRAAx] le d a) (hb : Γ ⊢[PRAAx] le d b)
    (h : Γ ⊢[PRAAx] le (ad a b) eps) : Γ ⊢[PRAAx] le (d * d * ad a b) (eps * (a * b)) := by
  have q := le_mul_mono (le_mul_mono ha hb) h
  ipra_le sl q

end LeanProofs.IPRA.Analysis.ErrorBudgets
