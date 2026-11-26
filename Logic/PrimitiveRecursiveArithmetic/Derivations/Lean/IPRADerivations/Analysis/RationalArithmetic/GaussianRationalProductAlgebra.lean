import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalFiniteProduct

/-!
# Local algebra of the actual Gaussian product fold

Bounded original factor equations give an all-one product or absorption
of a genuinely zero factor. Pointwise multiplication is transported by a
true QF recurrence proof using the existing fold and field shuffle. No
raw factor is identified with its canonical value and no desired global
product/evaluator law is a premise. Counts, positions and data remain
numerical, including the empty product.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalProductAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qmul)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteProduct (qprod product_zero product_succ product_index_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def oneTerms (f : PTm 2) (N x : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ inst2 f (var 0) (Syn.shift x) ≐ qone)
@[simp] theorem subst_oneTerms {l : ℕ} (σ : Fin n → PTm l) (f : PTm 2) (N x : PTm n) :
    (oneTerms f N x).subst σ = oneTerms f (Syn.subst σ N) (Syn.subst σ x) := by
  simp [oneTerms,Syn.subst_shift,Syn.shift_subst]

theorem constant_one_product (N x : PTm n) : Γ ⊢[PRAAx] qprod (qone : PTm 2) N x ≐ qone := by
  have all : Γ ⊢[PRAAx] .all (qprod (qone : PTm 2) (var 0) (Syn.shift x) ≐ qone) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,GaussianRationalFiniteProduct.subst_qprod,Syn.subst_var,Syn.inst_zero,
        Syn.subst_inst_shift,GaussianRationalSyntheticDivision.subst_qone]
      exact product_zero _ _
    · simp only [Fm.subst_eq,GaussianRationalFiniteProduct.subst_qprod,Syn.subst_var,Syn.repl_zero,
        subst_repl_shift,GaussianRationalSyntheticDivision.subst_qone]
      have step := product_succ (Γ := (qprod (qone : PTm 2) (var 0) (Syn.shift x) ≐ qone) :: Γ.map Fm.shift)
        (qone : PTm 2) (var 0) (Syn.shift x)
      have qi : inst2 (qone : PTm 2) (var 0) (Syn.shift x) = (qone : PTm (n+1)) := by simp [inst2]
      rw [qi] at step
      exact step.eqTrans ((qmul_congr Prf.hyp0 (.eqRefl _)).eqTrans
        (GaussianReciprocalHorner.qmul_one_right qone qone_canonical))
  simpa only [Fm.subst_eq,GaussianRationalFiniteProduct.subst_qprod,Syn.subst_var,Syn.inst_zero,
    Syn.subst_inst_shift,GaussianRationalSyntheticDivision.subst_qone] using all.allE N

theorem product_one_of_terms (f : PTm 2) (N x : PTm n) (h : Γ ⊢[PRAAx] oneTerms f N x) : Γ ⊢[PRAAx]
    qprod f N x ≐ qone := by
  have entries : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual f (qone : PTm 2) N x x := by
    simpa only [oneTerms,GaussianRationalFiniteSum.termsEqual,inst2,GaussianRationalSyntheticDivision.subst_qone] using h
  exact (GaussianRationalFiniteProduct.product_congr_bounded _ _ _ _ _ entries).eqTrans (constant_one_product N x)

/-- A known bounded zero factor is absorbed; this is not a zero-product oracle. -/
theorem product_zero_at (f : PTm 2) (N c x : PTm n) (hc : Γ ⊢[PRAAx] lt c N)
    (h0 : Γ ⊢[PRAAx] inst2 f c x ≐ qzero) : Γ ⊢[PRAAx] qprod f N x ≐ qzero :=
  (product_index_congr f (eq_add_of_le hc) (.eqRefl _)).eqTrans
    ((GaussianRationalFiniteProduct.product_split f (succ c) (monus N (succ c)) x).eqTrans
      ((qmul_congr ((product_succ f c x).eqTrans ((qmul_congr (.eqRefl _) h0).eqTrans
        (GaussianRationalSyntheticDivision.qmul_zero_right _))) (.eqRefl _)).eqTrans
          (GaussianRationalSyntheticDivision.qmul_zero_left _)))

def multiplyBody (f g : PTm 2) : PTm 2 := qmul f g
@[simp] theorem multiply_body_at (f g : PTm 2) (i x : PTm n) :
    inst2 (multiplyBody f g) i x = qmul (inst2 f i x) (inst2 g i x) := by simp [multiplyBody,inst2]
def multiplyLaw (f g : PTm 2) (N x : PTm n) : Fm PTm n :=
  qprod (multiplyBody f g) N x ≐ qmul (qprod f N x) (qprod g N x)
@[simp] theorem subst_multiplyLaw {l : ℕ} (σ : Fin n → PTm l) (f g : PTm 2) (N x : PTm n) :
    (multiplyLaw f g N x).subst σ = multiplyLaw f g (Syn.subst σ N) (Syn.subst σ x) := by simp [multiplyLaw]

theorem product_multiply (f g : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    qprod (multiplyBody f g) N x ≐ qmul (qprod f N x) (qprod g N x) := by
  have all : Γ ⊢[PRAAx] .all (multiplyLaw f g (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_multiplyLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (product_zero _ _).eqTrans
        ((qmul_congr (product_zero f x) (product_zero g x)).eqTrans
          (GaussianReciprocalHorner.qmul_one_right qone qone_canonical)).eqSymm
    · simp only [subst_multiplyLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      have step := product_succ (Γ := multiplyLaw f g (var 0) (Syn.shift x) :: Γ.map Fm.shift)
        (multiplyBody f g) (var 0) (Syn.shift x)
      rw [multiply_body_at] at step
      exact step.eqTrans ((qmul_congr Prf.hyp0 (.eqRefl _)).eqTrans
        ((GaussianRationalPowerAlgebra.qmul_shuffle _ _ _ _).eqTrans
          (qmul_congr (product_succ f _ _).eqSymm (product_succ g _ _).eqSymm)))
  have result : Γ ⊢[PRAAx] multiplyLaw f g N x := by
    simpa only [subst_multiplyLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact result

def output (f g : PTm 2) (N x : PTm n) : PTm n :=
  pairT (qprod (multiplyBody f g) N x) (pairT (qprod f N x) (qprod g N x))
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (f g : PTm 2) (N x : PTm n) :
    Syn.subst σ (output f g N x) = output f g (Syn.subst σ N) (Syn.subst σ x) := by simp [output]
def outputF (f g : PTm 2) : PR 2 := PTm.toPR (output f g (var 0) (var 1))
def run (f g : PTm 2) (N x : PTm n) : PTm n := ap2 (outputF f g) N x
theorem program_at (f g : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx] run f g N x ≐ output f g N x := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output f g (var 0) (var 1) : PTm 2) ![N,x]
theorem returned_multiply (f g : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    fstT (run f g N x) ≐ qmul (fstT (sndT (run f g N x))) (sndT (sndT (run f g N x))) := by
  have first := (congrFst (program_at (Γ := Γ) f g N x)).eqTrans (fst_pair _ _)
  have rest := (congrSnd (program_at (Γ := Γ) f g N x)).eqTrans (snd_pair _ _)
  exact first.eqTrans ((product_multiply _ _ _ _).eqTrans
    (qmul_congr ((congrFst rest).eqTrans (fst_pair _ _)) ((congrSnd rest).eqTrans (snd_pair _ _))).eqSymm)

theorem actual_one_product_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (oneTerms f (var 0) (var 1) ⟶ qprod f (var 0) (var 1) ≐ qone) := closeUniv 2 (.impI (product_one_of_terms _ _ _ Prf.hyp0))
theorem actual_zero_factor_product_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (var 0) ⟶ inst2 f (var 1) (var 2) ≐ qzero ⟶ qprod f (var 0) (var 2) ≐ qzero) :=
  closeUniv 3 (.impI (.impI (product_zero_at _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_pointwise_product_closed (f g : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (qprod (multiplyBody f g) (var 0) (var 1) ≐ qmul (qprod f (var 0) (var 1)) (qprod g (var 0) (var 1))) := closeUniv 2 (product_multiply _ _ _ _)
theorem actual_product_algebra_program_closed (f g : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((run f g (var 0) (var 1) ≐ output f g (var 0) (var 1)) ⋏
      fstT (run f g (var 0) (var 1)) ≐ qmul (fstT (sndT (run f g (var 0) (var 1)))) (sndT (sndT (run f g (var 0) (var 1))))) :=
  closeUniv 2 (.andI (program_at _ _ _ _) (returned_multiply _ _ _ _))

end LeanProofs.IPRA.Analysis.GaussianRationalProductAlgebra
