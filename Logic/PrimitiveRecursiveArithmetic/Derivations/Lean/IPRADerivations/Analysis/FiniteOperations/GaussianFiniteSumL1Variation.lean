import IPRADerivations.Analysis.Polynomials.GaussianPolynomialCoefficientDifferences
import IPRADerivations.Analysis.Polynomials.GaussianPolynomialDeterminantNorm

/-!
# Finite L1 error for the original Gaussian sum program

A genuine guarded numerical QF induction accumulates actual term
differences in the unchanged Gaussian sum recursor. Both data codes
and all original independently normalized terms remain distinct.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianFiniteSumL1Variation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalFiniteSum (sum)
open GaussianRationalMetric (qsub)
open GaussianRationalL1 (qL1)
open GaussianCoefficientL1 (qL1_congr)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianRationalSyntheticBounds (natCode add_monotone)
open RationalArithmetic (multiply)
open RationalArgmin (rationalLE)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def termsError (f g : PTm 2) (N x y E : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ rationalLE
    (qL1 (qsub (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift y)))) (Syn.shift E))
@[simp] theorem subst_termsError {m : ℕ} (σ : Fin n → PTm m) (f g : PTm 2) (N x y E : PTm n) :
    (termsError f g N x y E).subst σ = termsError f g (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ E) := by
  simp [termsError,Syn.subst_shift,Syn.shift_subst]
theorem term_at (f g : PTm 2) (N x y E i : PTm n) (h : Γ ⊢[PRAAx] termsError f g N x y E)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] rationalLE (qL1 (qsub (inst2 f i x) (inst2 g i y))) E := by
  have gate : Γ ⊢[PRAAx] lt i N ⟶ rationalLE (qL1 (qsub (inst2 f i x) (inst2 g i y))) E := by
    simpa [termsError] using h.allE i
  exact Prf.impE gate hi

def prefixLaw (f g : PTm 2) (N x y E k : PTm n) : Fm PTm n := le k N ⟶
  rationalLE (qL1 (qsub (sum f k x) (sum g k y))) (multiply (natCode k) E)
@[simp] theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (f g : PTm 2) (N x y E k : PTm n) :
    (prefixLaw f g N x y E k).subst σ = prefixLaw f g (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ E) (Syn.subst σ k) := by
  simp [prefixLaw]

theorem prefix_zero (f g : PTm 2) (N x y E : PTm n) : Γ ⊢[PRAAx] prefixLaw f g N x y E zero := by
  refine .impI ?_
  have codes := (qsub_congr (Γ := le zero N :: Γ) (GaussianRationalFiniteSum.sum_zero f x) (GaussianRationalFiniteSum.sum_zero g y)).eqTrans
    (GaussianCoefficientNormOrder.qsub_self _)
  exact RationalArgmin.rationalLE_congr ((qL1_congr codes).eqTrans GaussianRationalLinearProduct.qzero_norm).eqSymm
    (GaussianPolynomialDeterminantNorm.natural_scale_zero _).eqSymm (RationalArgmin.reflexive _)

theorem prefix_step (f g : PTm 2) (N x y E k : PTm n) (h : Γ ⊢[PRAAx] termsError f g N x y E)
    (ih : Γ ⊢[PRAAx] prefixLaw f g N x y E k) : Γ ⊢[PRAAx] prefixLaw f g N x y E (succ k) := by
  refine .impI ?_
  let Δ := le (succ k) N :: Γ
  have previous := Prf.impE ih.wk (le_trans (le_succ_self k) (Prf.hyp0 : Δ ⊢[PRAAx] _))
  have term := term_at f g N x y E k h.wk (Prf.hyp0 : Δ ⊢[PRAAx] _)
  have codes := (qsub_congr (Γ := Δ) (GaussianRationalFiniteSum.sum_succ f k x) (GaussianRationalFiniteSum.sum_succ g k y)).eqTrans
    (GaussianPolynomialCoefficientDifferences.scalar_sum_difference _ _ _ _)
  exact RationalArgmin.rationalLE_congr (qL1_congr codes).eqSymm (GaussianPolynomialDeterminantNorm.natural_scale_succ k E)
    (RationalArgmin.transitive (GaussianRationalL1Algebra.qL1_add _ _) (add_monotone _ _ _ _ previous term))

theorem sum_error (f g : PTm 2) (N x y E : PTm n) (h : Γ ⊢[PRAAx] termsError f g N x y E) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub (sum f N x) (sum g N y))) (multiply (natCode N) E) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] termsError f g (Syn.shift N) (Syn.shift x) (Syn.shift y) (Syn.shift E) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw f g (Syn.shift N) (Syn.shift x) (Syn.shift y) (Syn.shift E) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact prefix_zero _ _ _ _ _ _
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact prefix_step _ _ _ _ _ _ _ hs.wk Prf.hyp0
  have gate : Γ ⊢[PRAAx] prefixLaw f g N x y E N := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact Prf.impE gate (le_refl N)

theorem actual_finite_sum_L1_variation_closed (f g : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (termsError f g (var 0) (var 1) (var 2) (var 3) ⟶
      rationalLE (qL1 (qsub (sum f (var 0) (var 1)) (sum g (var 0) (var 2)))) (multiply (natCode (var 0)) (var 3))) :=
  closeUniv 4 (.impI (sum_error f g _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianFiniteSumL1Variation
