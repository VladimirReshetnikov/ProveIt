import IPRADerivations.Algebra.QuadraticIntegerOrder

/-!
# Nonnegative root uniqueness in the actual integer quadratic stage

This is the source assertion following lem:orderedextension. The SAME
computed sign-zero equality, ideal, order and zero-product reflection
prove uniqueness from the original nonnegative/square equations. The
actual positive root (0,1) is the comparison witness. No equality of raw
outer codes or supplied root/order/domain conclusion is used.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Algebra.QuadraticRootUniqueness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open QuadraticSignCertificates (first second equal add negative multiply)
open QuadraticSignCertificates (multiply_first multiply_second negative_first negative_second)
open QuadraticConeOrder (equal_of_values equal_symm add_first add_second)
open QuadraticIntegerOrder (positive isZero equivalent difference root natural
  positive_add positive_add_zero positive_value_congr positive_zero_absurd
  zero_add zero_negative zero_value_congr zero_product_reflect equivalent_symm equivalent_trans root_positive root_square)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def nonnegative (d x : PTm n) : Fm PTm n := positive d x ⋎ isZero d x
@[simp] theorem subst_nonnegative {l : ℕ} (σ : Fin n → PTm l) (d x : PTm n) :
    (nonnegative d x).subst σ = nonnegative (Syn.subst σ d) (Syn.subst σ x) := by simp [nonnegative]

theorem add_commute (x y : PTm n) : Γ ⊢[PRAAx] equal (add x y) (add y x) := by
  apply equal_of_values <;> simp only [add_first,add_second] <;> ring
theorem square_difference_factor (d x y : PTm n) : Γ ⊢[PRAAx]
    equal (multiply d (difference x y) (add x y)) (difference (multiply d x x) (multiply d y y)) := by
  apply equal_of_values <;> simp only [difference,multiply_first,multiply_second,add_first,add_second,negative_first,negative_second] <;> ring

theorem nonnegative_zero_sum (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] nonnegative d x) (hy : Γ ⊢[PRAAx] nonnegative d y)
    (hs : Γ ⊢[PRAAx] isZero d (add x y)) : Γ ⊢[PRAAx] isZero d x ⋏ isZero d y := by
  refine .orE hx ?_ ?_
  · refine .orE hy.wk ?_ ?_
    · exact .botE _ (positive_zero_absurd _ _ (positive_add _ _ _ hd.wk.wk Prf.hyp1 Prf.hyp0) hs.wk.wk)
    · exact .botE _ (positive_zero_absurd _ _ (positive_add_zero _ _ _ hd.wk.wk Prf.hyp1 Prf.hyp0) hs.wk.wk)
  · refine .orE hy.wk ?_ (.andI Prf.hyp1 Prf.hyp0)
    exact .botE _ (positive_zero_absurd _ _
      (positive_value_congr _ _ _ hd.wk.wk (add_commute y x) (positive_add_zero _ _ _ hd.wk.wk Prf.hyp0 Prf.hyp1)) hs.wk.wk)

theorem square_root_unique (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] nonnegative d x) (hy : Γ ⊢[PRAAx] nonnegative d y)
    (hs : Γ ⊢[PRAAx] equivalent d (multiply d x x) (multiply d y y)) : Γ ⊢[PRAAx] equivalent d x y := by
  have zeroProduct := zero_value_congr d (difference (multiply d x x) (multiply d y y))
    (multiply d (difference x y) (add x y)) hd (equal_symm (square_difference_factor d x y)) hs
  refine .orE (zero_product_reflect d (difference x y) (add x y) hd zeroProduct) Prf.hyp0 ?_
  have both := nonnegative_zero_sum d x y hd.wk hx.wk hy.wk Prf.hyp0
  exact QuadraticIntegerOrder.zero_add d x (negative y) hd.wk (.andE₁ both) (zero_negative d y hd.wk (.andE₂ both))

theorem unique_actual_root (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] nonnegative d x)
    (hs : Γ ⊢[PRAAx] equivalent d (multiply d x x) (natural d)) : Γ ⊢[PRAAx] equivalent d x root :=
  square_root_unique d x root hd hx (.orI₁ (root_positive d hd))
    (equivalent_trans d (multiply d x x) (natural d) (multiply d root root) hd hs
      (equivalent_symm d (multiply d root root) (natural d) hd (root_square d hd)))

def output (d : PTm n) : PTm n := pairT root (pairT (multiply d root root) (natural d))
def outputF : PR 1 := PTm.toPR (output (var 0))
def run (d : PTm n) : PTm n := ap1 outputF d
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (d : PTm n) :
    Syn.subst σ (output d) = output (Syn.subst σ d) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (d : PTm n) :
    Syn.subst σ (run d) = run (Syn.subst σ d) := by simp [run]
theorem program_at (d : PTm n) : Γ ⊢[PRAAx] run d ≐ output d := by
  simpa [run,outputF,ap1] using toPR_eq (Γ := Γ) (output (var 0) : PTm 1) ![d]
theorem returned_root (d : PTm n) : Γ ⊢[PRAAx] fstT (run d) ≐ root :=
  (congrFst (program_at d)).eqTrans (fst_pair _ _)
theorem returned_square (d : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run d)) ≐ multiply d root root :=
  (congrFst (congrSnd (program_at d))).eqTrans ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
theorem returned_natural (d : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run d)) ≐ natural d :=
  (congrSnd (congrSnd (program_at d))).eqTrans ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))

theorem equivalent_code_congr {d x x' y y' : PTm n} (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y')
    (h : Γ ⊢[PRAAx] equivalent d x y) : Γ ⊢[PRAAx] equivalent d x' y' := by
  simpa only [QuadraticIntegerOrder.subst_equivalent,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqSubst (equivalent (var 0) (var 1) (var 2) : Fm PTm 3) ![d,x,y] ![d,x',y']
      (fun i => by fin_cases i; exact .eqRefl _; exact hx; exact hy)
      (by simpa only [QuadraticIntegerOrder.subst_equivalent,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using h)
theorem returned_unique (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] nonnegative d x)
    (hs : Γ ⊢[PRAAx] equivalent d (multiply d x x) (natural d)) : Γ ⊢[PRAAx] equivalent d x (fstT (run d)) :=
  equivalent_code_congr (.eqRefl _) (returned_root d).eqSymm (unique_actual_root d x hd hx hs)

theorem nonnegative_quadratic_zero_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ nonnegative (var 0) (var 1) ⟶ nonnegative (var 0) (var 2) ⟶ isZero (var 0) (add (var 1) (var 2)) ⟶
      (isZero (var 0) (var 1) ⋏ isZero (var 0) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (nonnegative_zero_sum _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem nonnegative_quadratic_root_unique_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ nonnegative (var 0) (var 1) ⟶ nonnegative (var 0) (var 2) ⟶
      equivalent (var 0) (multiply (var 0) (var 1) (var 1)) (multiply (var 0) (var 2) (var 2)) ⟶ equivalent (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (square_root_unique _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_positive_root_unique_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ nonnegative (var 0) (var 1) ⟶ equivalent (var 0) (multiply (var 0) (var 1) (var 1)) (natural (var 0)) ⟶
      equivalent (var 0) (var 1) root) :=
  closeUniv 2 (.impI (.impI (.impI (unique_actual_root _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_positive_root_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (run (var 0) ≐ output (var 0)) := closeUniv 1 (program_at _)
theorem actual_returned_root_unique_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ nonnegative (var 0) (var 1) ⟶ equivalent (var 0) (multiply (var 0) (var 1) (var 1)) (natural (var 0)) ⟶
      equivalent (var 0) (var 1) (fstT (run (var 0)))) :=
  closeUniv 2 (.impI (.impI (.impI (returned_unique _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Algebra.QuadraticRootUniqueness
