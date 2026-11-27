import IPRADerivations.Core.MultiSums
import IPRADerivations.AnalyticNumberTheory.Fermat

/-!
# Products over a permuted range

For bodies `F(j, x)`, `σ(i, x)` and `τ(j, x)` with `σ(i) < N` for all `i`, `τ(j) < N`,
`σ(τ(j)) = j` for `j < N` and `τ(σ(i)) = i` for `i < N`:

`∏_{i<N} F(σ(i)) = ∏_{j<N} F(j)` (`prod_perm`).

The proof avoids tracking injectivity through an induction. With the fiber counts
`m_M(j) = ∑_{i<M} [σ(i) = j]`, the fiber identity `∏_{i<M} F(σ(i)) = ∏_{j<N} F(j)^{m_M(j)}`
(`fiber`) holds for every `M` by induction, each step adding one delta factor
(`prod2_delta`). With the inverse `τ`, `[σ(i) = j] = [i = τ(j)]` below `N`, so
`m_N(j) = 1` (`sum2_delta`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Permutation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (subst_up_shift')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

variable (F S : PTm 2)

/-- `[σ(i, x) = j]`, over `0 = i`, `1 = j`, `2 = x`. -/
def mB : PTm 3 := eqb (Syn.subst ![var 0, var 2] S) (var 1)
/-- `F(j, x)^{m_M(j)}`, over `0 = j`, `1 = M`, `2 = x`. -/
def fB : PTm 3 := pw (Syn.subst ![var 0, var 2] F) (ap3 (sum2F (mB S)) (var 1) (var 0) (var 2))
/-- `F(j, x)^{[σ(M, x) = j]}`, over `0 = j`, `1 = M`, `2 = x`. -/
def dB : PTm 3 := pw (Syn.subst ![var 0, var 2] F) (eqb (Syn.subst ![var 1, var 2] S) (var 0))
/-- `F(σ(i, x), x)`, over `0 = i`, `1 = x`. -/
def FS : PTm 2 := Syn.subst ![S, var 1] F

variable {F S}

theorem inst3_mB (i j x : PTm n) : inst3 (mB S) i j x = eqb (inst2 S i x) j := by
  simp only [inst3, mB, inst2, subst_eqb, Syn.subst_subst, Syn.subst_var]
  congr 2; funext k; fin_cases k <;> rfl

theorem inst3_fB (j M x : PTm n) :
    inst3 (fB F S) j M x = pw (inst2 F j x) (ap3 (sum2F (mB S)) M j x) := by
  simp only [inst3, fB, inst2, subst_ap2, subst_ap3, Syn.subst_subst, Syn.subst_var]
  congr 2; funext k; fin_cases k <;> rfl

theorem inst3_dB (j M x : PTm n) :
    inst3 (dB F S) j M x = pw (inst2 F j x) (eqb (inst2 S M x) j) := by
  simp only [inst3, dB, inst2, subst_ap2, subst_eqb, Syn.subst_subst, Syn.subst_var]
  rw [show (fun i => Syn.subst ![j, M, x] (![var 0, var 2] i)) = ![j, x] from by funext k; fin_cases k <;> rfl,
    show (fun i => Syn.subst ![j, M, x] (![var 1, var 2] i)) = ![M, x] from by funext k; fin_cases k <;> rfl]
  rfl

theorem inst2_FS (i x : PTm n) : inst2 (FS F S) i x = inst2 F (inst2 S i x) x := by
  simp only [inst2, FS, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> rfl

theorem inst3_fB_mul (j M x : PTm n) :
    inst3 (fB F S * dB F S) j M x = inst3 (fB F S) j M x * inst3 (dB F S) j M x := by
  simp [inst3]

/-! ## The fiber identity -/

/-- One step of the fiber identity. -/
theorem fiber_step {N M x : PTm n} (hσ : Γ ⊢[PRAAx] lt (inst2 S M x) N) :
    Γ ⊢[PRAAx] ap3 (prod2F (fB F S)) N (succ M) x ≐
      ap3 (prod2F (fB F S)) N M x * inst2 F (inst2 S M x) x := by
  have h₁ : Γ ⊢[PRAAx] ap3 (prod2F (fB F S)) N (succ M) x ≐ ap3 (prod2F (fB F S * dB F S)) N M x := by
    refine prod2_congr_bounded _ _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst3_fB, inst3_fB_mul, inst3_fB, inst3_dB]
    have e : Syn.shift (succ M) = succ (Syn.shift M) := by simp [Syn.shift]
    rw [e]
    refine (congrAp2 powF (sum2_succ _ _ _ _) (.eqRefl _)).eqTrans ?_
    rw [inst3_mB]
    exact pw_add _ _ _
  have h₂ := prod2_mul (Γ := Γ) (fB F S) (dB F S) N M x
  have h₃ : Γ ⊢[PRAAx] ap3 (prod2F (dB F S)) N M x ≐ inst2 F (inst2 S M x) x := by
    refine (prod2_congr_bounded (dB F S) (deltaBody F) M x (inst2 S M x) x N (.allI (.impI ?_))).eqTrans
      (prod2_delta F hσ)
    rw [inst3_dB, inst3_delta]
    simp only [Syn.shift, subst_inst2]
    exact .eqRefl _
  exact h₁.eqTrans (h₂.eqTrans (congrMul (.eqRefl _) h₃))

/-- `∀ i. σ(i, x) < N`. -/
abbrev rangeAll (S : PTm 2) (N x : PTm n) : Fm PTm n := Fm.all (lt (inst2 S (var 0) (Syn.shift x)) (Syn.shift N))

/-- The fiber identity: `∏_{i<M} F(σ(i)) = ∏_{j<N} F(j)^{m_M(j)}`. -/
theorem fiber {N x : PTm n} (hr : Γ ⊢[PRAAx] rangeAll S N x) (M : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF (FS F S)) M x ≐ ap3 (prod2F (fB F S)) N M x := by
  have hall : Γ ⊢[PRAAx] Fm.all (ap2 (prodF (FS F S)) (var 0) (Syn.shift x) ≐
      ap3 (prod2F (fB F S)) (Syn.shift N) (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, subst_ap3, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      refine (prod_zero _ _).eqTrans (prod2_one _ _ _ _ (.allI (.impI ?_))).eqSymm
      rw [inst3_fB]
      have e : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
      rw [e]
      exact (congrAp2 powF (sum2_zero _ _ _) (.eqRefl _)).eqTrans (pw_zero _)
    · simp only [Fm.subst_eq, subst_ap2, subst_ap3, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      have hσ := hr.allOpen
      refine (prod_succ _ _ _).eqTrans ?_
      have e : Syn.subst ![var 0, Syn.shift x] (FS F S) = inst2 F (inst2 S (var 0) (Syn.shift x)) (Syn.shift x) :=
        inst2_FS (var 0) (Syn.shift x)
      rw [e]
      exact (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (fiber_step hσ.wk).eqSymm
  have h := Prf.allE M hall
  simp only [Fm.subst_eq, subst_ap2, subst_ap3, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h
  exact h

/-! ## Counting with an inverse -/

/-- `[σ(i) = j] = [i = τ(j)]` when `σ(τ(j)) = j` and `τ(σ(i)) = i`. -/
theorem eqb_swap {si j i tj : PTm n}
    (h₁ : Γ ⊢[PRAAx] neg (si ≐ j) ⟶ neg (i ≐ tj)) (h₂ : Γ ⊢[PRAAx] (si ≐ j) ⟶ (i ≐ tj)) :
    Γ ⊢[PRAAx] eqb si j ≐ eqb i tj := by
  refine .orE (eq_or_ne si j) ?_ ?_
  · exact (eqb_of_eq Prf.hyp0).eqTrans (eqb_of_eq (.impE h₂.wk Prf.hyp0)).eqSymm
  · exact (eqb_of_ne Prf.hyp0).eqTrans (eqb_of_ne (.impE h₁.wk Prf.hyp0)).eqSymm

/-- `∀ j < N. τ(j) < N ∧ σ(τ(j)) = j`. -/
def invAll (S τ : PTm 2) (N x : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶ (lt (inst2 τ (var 0) (Syn.shift x)) (Syn.shift N) ⋏
    (inst2 S (inst2 τ (var 0) (Syn.shift x)) (Syn.shift x) ≐ var 0)))

/-- `∀ i < N. τ(σ(i)) = i`. -/
def retAll (S τ : PTm 2) (N x : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶ (inst2 τ (inst2 S (var 0) (Syn.shift x)) (Syn.shift x) ≐ var 0))

ipra_subst invAll [subst_up_shift', Syn.up]

ipra_subst retAll [subst_up_shift', Syn.up]

theorem shift_invAll {S τ : PTm 2} {N x : PTm n} (h : Γ ⊢[PRAAx] invAll S τ N x) :
    Γ.map Fm.shift ⊢[PRAAx] invAll S τ (Syn.shift N) (Syn.shift x) := by
  have e := h.shift
  simp only [Fm.shift, subst_invAll] at e
  exact e

theorem shift_retAll {S τ : PTm 2} {N x : PTm n} (h : Γ ⊢[PRAAx] retAll S τ N x) :
    Γ.map Fm.shift ⊢[PRAAx] retAll S τ (Syn.shift N) (Syn.shift x) := by
  have e := h.shift
  simp only [Fm.shift, subst_retAll] at e
  exact e

/-- Below `N`, every fiber has one element. -/
theorem mult_one {τ : PTm 2} {N x j : PTm n} (hj : Γ ⊢[PRAAx] lt j N) (hinv : Γ ⊢[PRAAx] invAll S τ N x)
    (hret : Γ ⊢[PRAAx] retAll S τ N x) : Γ ⊢[PRAAx] ap3 (sum2F (mB S)) N j x ≐ one := by
  have hj' := Prf.allE j hinv
  simp only [invAll, Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_lt, subst_inst2, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] at hj'
  have ht := Prf.andE₁ (Prf.impE hj' hj)
  have hst := Prf.andE₂ (Prf.impE hj' hj)
  refine (sum2_congr_bounded (mB S) indBody j x (inst2 τ j x) x N (.allI (.impI ?_))).eqTrans (sum2_delta ht)
  rw [inst3_mB]
  have e : inst3 indBody (var 0 : PTm (n + 1)) (Syn.shift (inst2 τ j x)) (Syn.shift x) =
      eqb (var 0) (inst2 τ (Syn.shift j) (Syn.shift x)) := by simp [inst3, Syn.shift]
  rw [e]
  have hst' : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
      inst2 S (inst2 τ (Syn.shift j) (Syn.shift x)) (Syn.shift x) ≐ Syn.shift j := by
    have e' := hst.shift
    simp only [Fm.shift, Fm.subst_eq, subst_inst2] at e'
    exact e'.wk
  have hr := hret.allOpen
  have hr' := Prf.impE hr.wk Prf.hyp0
  refine eqb_swap (.impI (.impI ?_)) (.impI ?_)
  · -- `i = τ(j)` gives `σ(i) = j`.
    exact .impE Prf.hyp1 ((congrInst2 S Prf.hyp0 (.eqRefl _)).eqTrans hst'.wk.wk)
  · -- `σ(i) = j` gives `i = τ(σ(i)) = τ(j)`.
    exact hr'.wk.eqSymm.eqTrans (congrInst2 τ Prf.hyp0 (.eqRefl _))

/-- Variables: `0 = N`, `1 = p`, `2 = x`. -/
private abbrev prodEqF (F : PTm 2) : Fm PTm 3 :=
  ap3 (prod2F (Syn.subst ![var 0, var 2] F)) (var 0) (var 1) (var 2) ≐ ap2 (prodF F) (var 0) (var 2)

private theorem prod2_eq_prod₀ (F : PTm 2) : ([] : List (Fm PTm 3)) ⊢[PRAAx] prodEqF F :=
  prod2_eq_prod_ignore_parameter F (var 0) (var 1) (var 2)

theorem prod2_eq_prod (F : PTm 2) (N p x : PTm n) :
    Γ ⊢[PRAAx] ap3 (prod2F (Syn.subst ![var 0, var 2] F)) N p x ≐ ap2 (prodF F) N x := by
  simpa using inst (Γ := Γ) (prod2_eq_prod₀ F) (![N, p, x] : Fin 3 → PTm n)

/-! ## The permutation theorem -/

/-- `∏_{i<N} F(σ(i)) = ∏_{j<N} F(j)` for a permutation `σ` of `[0, N)` with inverse `τ`. -/
theorem prod_perm {τ : PTm 2} {N x : PTm n} (hr : Γ ⊢[PRAAx] rangeAll S N x)
    (hinv : Γ ⊢[PRAAx] invAll S τ N x) (hret : Γ ⊢[PRAAx] retAll S τ N x) :
    Γ ⊢[PRAAx] ap2 (prodF (FS F S)) N x ≐ ap2 (prodF F) N x := by
  refine (fiber hr N).eqTrans (.eqTrans ?_ (prod2_eq_prod F N N x))
  refine prod2_congr_bounded _ _ _ _ _ _ _ (.allI (.impI ?_))
  rw [inst3_fB, inst3_ignore_parameter]
  have m := mult_one (j := var 0) Prf.hyp0 (shift_invAll hinv).wk (shift_retAll hret).wk
  exact (congrAp2 powF m (.eqRefl _)).eqTrans (pw_one _)

end LeanProofs.IPRA.Permutation
