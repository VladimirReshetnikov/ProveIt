import IPRADerivations.Analysis.Gamma.EulerProducts.Factorials.GaussianGammaHalfRisingFactorial
import IPRADerivations.Analysis.Beta.EulerProducts.GaussianEulerBetaProductValue

/-!
# Exact original finite Euler head at one half

The unchanged original head loop equals (2N+1)!!/[2*(2N)!!].
The actual original factor recurrence is bound to the existing internal
double-factorial recurrences by QF equality induction. Its explicit
positive rational inverse has literal unit product with that same head.
No Gamma or exponential value is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaHalfEulerHead

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaEulerHead (head factor head_zero head_succ run program_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (ofGaussian_represents canonical_unique represents_congr positive_product qmul)
open GaussianRationalSyntheticDivision (qmul_congr qone)
open GaussianCoefficientNameBounds (unit unit_positive)
open LeanProofs.IPRA.Probability.NormalMoments (df edf df_zero df_succ edf_zero edf_succ edf_eq)
open ComplexLogarithmRemainder (oneCode scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (N : PTm n) : PTm n := df (succ N)
def denominator (N : PTm n) : PTm n := two*edf N
def value (N : PTm n) : PTm n := fraction (numerator N) (denominator N)
def inverse (N : PTm n) : PTm n := fraction (denominator N) (numerator N)
def law (N : PTm n) : Fm PTm n := head oneCode two N ≐ value N
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (numerator N) = numerator (Syn.subst σ N) := by simp [numerator,df]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (denominator N) = denominator (Syn.subst σ N) := by simp [denominator,edf]
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (value N) = value (Syn.subst σ N) := by simp [value]
@[simp] theorem subst_inverse {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (inverse N) = inverse (Syn.subst σ N) := by simp [inverse]
@[simp] theorem subst_law {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    (law N).subst σ = law (Syn.subst σ N) := by simp [law]

theorem numerator_positive (N : PTm n) : Γ ⊢[PRAAx] le one (numerator N) :=
  le_congr (.eqRefl _) (LeanProofs.IPRA.Probability.NormalMoments.df_pos (succ N)).eqSymm (zero_lt_succ _)
theorem denominator_positive (N : PTm n) : Γ ⊢[PRAAx] le one (denominator N) :=
  positive_product _ _ (zero_lt_succ one) (le_congr (.eqRefl _) (edf_eq N).eqSymm
    (positive_product _ _ (unit_positive N) (GaussianGammaHalfRisingFactorial.factorial_positive N)))

theorem factor_value (N : PTm n) : Γ ⊢[PRAAx]
    factor N (oneCode : PTm n) two ≐ fraction (succ (two*succ N)) (two*succ N) := by
  have hd := positive_product (Γ := Γ) _ _ (zero_lt_succ one) (zero_lt_succ N)
  apply canonical_unique _ _ _ _ (GaussianRationalHorner.qadd_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hd) hd ?_ (ofGaussian_represents _ _ hd)
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) (GaussianGammaEulerHeadLower.factor_represents N oneCode two (zero_lt_succ one))
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
      GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
  all_goals (ipra_simps; ring)

theorem base : Γ ⊢[PRAAx] law (zero : PTm n) := by
  have num0 : Γ ⊢[PRAAx] numerator (zero : PTm n) ≐ one :=
    (df_succ zero).eqTrans ((congrMul df_zero (.eqRefl _)).eqTrans (by ipra_ring))
  have den0 : Γ ⊢[PRAAx] denominator (zero : PTm n) ≐ two :=
    (congrMul (.eqRefl _) edf_zero).eqTrans (by ipra_ring)
  have unit : Γ ⊢[PRAAx] fraction (one : PTm n) two ≐ GaussianRationalHorner.ofGaussian oneCode two := by
    apply GaussianGammaFiniteValueProperness.fraction_equal _ _ two (zero_lt_succ one)
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale]
    all_goals (ipra_simps; ring)
  exact (head_zero oneCode two (zero_lt_succ one)).eqTrans
    (((GaussianCompactRiemannName.fraction_congr _ _ _ _ num0 den0).eqTrans unit).eqSymm)

theorem step (N : PTm n) (ih : Γ ⊢[PRAAx] law N) : Γ ⊢[PRAAx] law (succ N) := by
  have denominatorStep : Γ ⊢[PRAAx] denominator N*(two*succ N) ≐ denominator (succ N) :=
    (by unfold denominator; ipra_ring : Γ ⊢[PRAAx] denominator N*(two*succ N) ≐ two*(edf N*(two*succ N))).eqTrans
      (congrMul (.eqRefl _) (edf_succ N).eqSymm)
  exact (head_succ oneCode two N).eqTrans ((qmul_congr ih (factor_value N)).eqTrans
    ((GaussianEulerDampedTimeRate.fraction_product (numerator N) (denominator N) (succ (two*succ N)) (two*succ N)
      (denominator_positive N) (positive_product _ _ (zero_lt_succ one) (zero_lt_succ N))).eqTrans
      (GaussianCompactRiemannName.fraction_congr _ _ _ _ (df_succ (succ N)).eqSymm denominatorStep)))

theorem original_head (N : PTm n) : Γ ⊢[PRAAx] law N := by
  have all : Γ ⊢[PRAAx] .all (law (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_law,Syn.subst_var,Syn.inst_zero]
      exact base
    · simp only [subst_law,Syn.subst_var,Syn.repl_zero]
      exact step _ Prf.hyp0
  simpa only [subst_law,Syn.subst_var,Syn.inst_zero] using all.allE N

theorem original_run (N : PTm n) : Γ ⊢[PRAAx] run (oneCode : PTm n) two N ≐ value N :=
  (program_at _ _ _).eqTrans (original_head N)

theorem inverse_product (N : PTm n) : Γ ⊢[PRAAx] qmul (head (oneCode : PTm n) two N) (inverse N) ≐ qone := by
  let A := numerator N
  let B := denominator N
  have product := GaussianEulerDampedTimeRate.fraction_product (Γ := Γ) A B B A (denominator_positive N) (numerator_positive N)
  have denom := positive_product (Γ := Γ) _ _ (numerator_positive N) (denominator_positive N)
  have unit : Γ ⊢[PRAAx] fraction (A*B) (B*A) ≐ qone :=
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring : Γ ⊢[PRAAx] A*B ≐ (A*B)*one)
      (by ipra_ring : Γ ⊢[PRAAx] B*A ≐ (A*B)*one)).eqTrans
      ((GaussianCompactRiemannSplit.fraction_cancel (A*B) one one denom (le_refl one)).eqTrans GaussianGammaFactorialValues.natural_one)
  exact (qmul_congr (original_head N) (.eqRefl _)).eqTrans (product.eqTrans unit)

theorem actual_original_half_Euler_head_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (run oneCode two (var 0) ≐ value (var 0)) := closeUniv 1 (original_run _)
theorem actual_original_half_Euler_head_inverse_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (qmul (head oneCode two (var 0)) (inverse (var 0)) ≐ qone) := closeUniv 1 (inverse_product _)

end LeanProofs.IPRA.Analysis.GaussianGammaHalfEulerHead
