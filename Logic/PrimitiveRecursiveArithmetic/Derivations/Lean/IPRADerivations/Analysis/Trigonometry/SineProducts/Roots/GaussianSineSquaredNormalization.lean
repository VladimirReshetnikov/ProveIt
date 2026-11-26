import IPRADerivations.Analysis.Trigonometry.SineProducts.Roots.GaussianSineSquaredPolynomial

/-!
# Normalization of the finite squared-trace polynomial

At trace two the multiple-angle recurrence returns the natural sequence
1, 2, 3, …. Its even subsequence gives the exact normalization
P_J(4) = 2J+1 for the monic polynomial used in the finite sine product.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineSquaredNormalization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode zeroCode)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalHorner (canonical qzero qadd qmul evaluate canonical_unique ofGaussian_canonical
  ofGaussian_represents zero_represents qadd_canonical qmul_canonical
  qadd_represents represents_congr)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents natScale_as_product natScale_represents)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (qone)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr)
open GaussianReciprocalHorner (qsub_add_cancel qmul_one_right)
open GaussianRootAlgebra (equal_of_values equal_refl re_scale im_scale re_add im_add re_one im_one re_zero im_zero)
open GaussianSineMultipleAngleRecurrence (twoPoint evenValue value previous previous_zero value_zero previous_succ value_succ)
open GaussianSineSquaredPolynomial (coefficients evaluation_square)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem point_canonical (a : PTm n) : Γ ⊢[PRAAx] canonical (naturalPoint a) :=
  ofGaussian_canonical _ _ (le_refl _)

private theorem point_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] naturalPoint a ≐ naturalPoint b := by
  simpa using Prf.eqCongr (naturalPoint (var 0) : PTm 1) (σ := ![a]) (σ' := ![b])
    (fun i => by fin_cases i; exact h)

private theorem point_zero : Γ ⊢[PRAAx] naturalPoint (zero : PTm n) ≐ qzero := by
  apply canonical_unique _ _ zeroCode one (point_canonical _) (ofGaussian_canonical _ _ (le_refl _))
    (le_refl _) _ (zero_represents one)
  apply represents_congr (.eqRefl _) _ (.eqRefl _) (natural_point_represents _)
  apply equal_of_values <;> simp only [re_scale,im_scale,re_one,im_one,re_zero,im_zero] <;> ipra_simps <;> ring

private theorem point_one : Γ ⊢[PRAAx] naturalPoint (one : PTm n) ≐ qone := by
  apply canonical_unique _ _ oneCode one (point_canonical _) (ofGaussian_canonical _ _ (le_refl _))
    (le_refl _) _ (ofGaussian_represents _ _ (le_refl _))
  apply represents_congr (.eqRefl _) _ (.eqRefl _) (natural_point_represents _)
  apply equal_of_values <;> simp only [re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring

private theorem point_add (a b : PTm n) :
    Γ ⊢[PRAAx] qadd (naturalPoint a) (naturalPoint b) ≐ naturalPoint (a+b) := by
  apply canonical_unique _ _ (scale (a+b) oneCode) one (qadd_canonical _ _) (point_canonical _)
    (le_refl _) _ (natural_point_represents _)
  apply represents_congr (.eqRefl _) _ (.eqRefl _)
    (qadd_represents _ _ _ _ _ (le_refl _) (natural_point_represents a) (natural_point_represents b))
  apply equal_of_values <;> simp only [re_add,im_add,re_scale,im_scale] <;> ipra_simps <;> ring

private theorem four_at_trace_two : Γ ⊢[PRAAx]
    qmul twoPoint twoPoint ≐ naturalPoint (num 4 : PTm n) := by
  have hTwo : Γ ⊢[PRAAx] twoPoint ≐ naturalPoint two :=
    (qadd_congr point_one.eqSymm point_one.eqSymm).eqTrans
      ((point_add one one).eqTrans (point_congr (by ipra_ring)))
  have rp := natScale_represents (Γ := Γ) two (naturalPoint two) (scale two oneCode) one
      (le_refl _) (natural_point_represents two)
  have hFour : Γ ⊢[PRAAx] qmul (naturalPoint two) (naturalPoint two) ≐ naturalPoint (num 4) := by
    apply canonical_unique _ _ (scale (num 4) oneCode) one (qmul_canonical _ _) (point_canonical _)
      (le_refl _) _ (natural_point_represents _)
    apply represents_congr (natScale_as_product _ _) _ (.eqRefl _) rp
    apply equal_of_values <;> simp only [re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring
  exact (qmul_congr hTwo hTwo).eqTrans hFour

def countingLaw (k : PTm n) : Fm PTm n :=
  (previous twoPoint k ≐ naturalPoint k) ⋏ (value twoPoint k ≐ naturalPoint (succ k))

@[simp] theorem subst_countingLaw {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    (countingLaw k).subst σ = countingLaw (Syn.subst σ k) := by
  simp [countingLaw, twoPoint]

private theorem counting_zero : Γ ⊢[PRAAx] countingLaw (zero : PTm n) :=
  .andI ((previous_zero twoPoint).eqTrans point_zero.eqSymm)
    ((value_zero twoPoint).eqTrans point_one.eqSymm)

private theorem counting_succ (k : PTm n) (h : Γ ⊢[PRAAx] countingLaw k) :
    Γ ⊢[PRAAx] countingLaw (succ k) := by
  let a := naturalPoint (succ k)
  let b := naturalPoint (succ (succ k))
  let c := naturalPoint k
  have doubled : Γ ⊢[PRAAx] qmul twoPoint a ≐ qadd a a :=
    (qmul_commutative twoPoint a).eqTrans
      ((qmul_add a qone qone).eqTrans (qadd_congr (qmul_one_right _ (point_canonical _))
        (qmul_one_right _ (point_canonical _))))
  have sameSum : Γ ⊢[PRAAx] qadd a a ≐ qadd b c :=
    (point_add _ _).eqTrans ((point_congr (by ipra_ring)).eqTrans (point_add _ _).eqSymm)
  exact .andI ((previous_succ twoPoint k).eqTrans h.andE₂)
    ((value_succ twoPoint k).eqTrans
      ((qsub_congr ((qmul_congr (.eqRefl _) h.andE₂).eqTrans (doubled.eqTrans sameSum)) h.andE₁).eqTrans
        (qsub_add_cancel _ _ (point_canonical _))))

theorem value_at_two (k : PTm n) : Γ ⊢[PRAAx] value twoPoint k ≐ naturalPoint (succ k) := by
  have all : Γ ⊢[PRAAx] .all (countingLaw (var 0)) := by
    refine PRA.qfInd _ ⟨trivial, trivial⟩ ?_ ?_
    · simpa only [subst_countingLaw,Syn.subst_var,Syn.inst_zero] using counting_zero (Γ := Γ)
    · simpa only [subst_countingLaw,Syn.subst_var,Syn.repl_zero] using counting_succ (var 0) Prf.hyp0
  have atK : Γ ⊢[PRAAx] countingLaw k := by
    simpa only [subst_countingLaw,Syn.subst_var,Syn.inst_zero] using all.allE k
  exact atK.andE₂

theorem normalization (J : PTm n) :
    Γ ⊢[PRAAx] evaluate (coefficients J) (naturalPoint (num 4)) ≐ naturalPoint (succ (two*J)) :=
  (GaussianRationalMonicReduction.evaluate_congr (.eqRefl _) four_at_trace_two.eqSymm).eqTrans
    ((evaluation_square twoPoint J (qadd_canonical _ _)).eqTrans (value_at_two (two*J)))

theorem actual_sine_squared_polynomial_normalization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (evaluate (coefficients (var 0)) (naturalPoint (num 4)) ≐ naturalPoint (succ (two*var 0))) :=
  closeUniv 1 (normalization _)

end LeanProofs.IPRA.Analysis.GaussianSineSquaredNormalization
