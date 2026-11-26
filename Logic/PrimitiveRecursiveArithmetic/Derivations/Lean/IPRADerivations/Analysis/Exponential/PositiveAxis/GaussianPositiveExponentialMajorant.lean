import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianPositiveExponentialProduct
import IPRADerivations.Analysis.Exponential.Estimates.GaussianExponentialDiskMajorant
import IPRADerivations.Analysis.Exponential.Estimates.GaussianRationalExponentialLipschitz
import IPRADerivations.DiophantineNumberTheory.SuperellipticFamily

/-!
# The all-cutoff finite exponential majorant 3^R

The original finite scalar sum at a nonnegative natural argument R is
bounded above by 3^R at EVERY numerical cutoff K. The proof inducts on R,
using the positive high part of the original rectangular product and the
exact native factorial partial-sum bound at one. The already checked
disk transfer then bounds the same original scalar sum at every Gaussian
rational point of Euclidean modulus at most R. No completion, selected
cutoff, exponential law or output bound is supplied as a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPositiveExponentialMajorant

open_ipra
open GaussianPositiveRealArithmetic (positive sign)
open GaussianPositiveExponentialProduct (positive_scalar_sum scalar_sum_submultiplicative)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents)
open GaussianRationalPolynomialExponential (scalarSum factorial_positive)
open GaussianRationalHorner (qadd)
open GaussianRationalSyntheticBounds (natCode natCode_represents natCode_nonnegative)
open GaussianExponentialDiskMajorant (numerator numerator_zero numerator_succ real_majorant_represents)
open RationalArgmin (rationalLE)
open ExponentialSeries (en)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def value (R K : PTm n) : PTm n := fstT (scalarSum (naturalPoint R) K)
ipra_subst value

theorem natCode_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] natCode a ≐ natCode b := by
  ipra_congr (natCode (var 0) : PTm 1) with [h]

theorem natural_successor_sum (R : PTm n) : Γ ⊢[PRAAx]
    qadd (naturalPoint R) (naturalPoint one) ≐ naturalPoint (succ R) := by
  have a := GaussianRationalHorner.qadd_represents _ _ _ _ one (le_refl one)
    (natural_point_represents (Γ := Γ) R) (natural_point_represents one)
  apply GaussianRationalHorner.canonical_unique _ _ _ one (GaussianRationalHorner.qadd_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one)) (le_refl one) a
  apply GaussianRationalHorner.represents_congr (.eqRefl _) _ (.eqRefl _) (natural_point_represents (succ R))
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,
      GaussianRootAlgebra.im_one,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add] <;> ipra_simps <;> ring

theorem value_successor_product (R K : PTm n) : Γ ⊢[PRAAx]
    rationalLE (value (succ R) K) (RationalArithmetic.multiply (value R K) (value one K)) := by
  have e := congrFst (GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody
    (.eqRefl (succ K)) (natural_successor_sum (Γ := Γ) R))
  exact RationalArgmin.rationalLE_congr e (.eqRefl _)
    (scalar_sum_submultiplicative _ _ K (GaussianPositiveRealArithmetic.positive_natural R)
      (GaussianPositiveRealArithmetic.positive_natural one))

def unitLaw (K : PTm n) : Fm PTm n := numerator one K ≐ succ K*en K
ipra_subst unitLaw [en]

theorem unit_numerator (K : PTm n) : Γ ⊢[PRAAx] unitLaw K := by
  have all : Γ ⊢[PRAAx] .all (unitLaw (var 0)) := by
    ipra_qfind [subst_unitLaw]
    · apply deriveNat; ipra_simps
      linear_combination natEq (numerator_zero (Γ := Γ) one)-natEq (ExponentialSeries.en_zero (Γ := Γ))
    · have a := natEq (numerator_succ (Γ := unitLaw (var 0) :: Γ.map Fm.shift) one (var 0))
      have b := natEq (LeanProofs.IPRA.DiophantineNumberTheory.SuperellipticFamily.one_pw
        (Γ := unitLaw (var 0) :: Γ.map Fm.shift) (succ (var 0)))
      have c := natEq (ExponentialSeries.en_succ (Γ := unitLaw (var 0) :: Γ.map Fm.shift) (var 0))
      have d := natEq (Prf.hyp0 : unitLaw (var 0) :: Γ.map Fm.shift ⊢[PRAAx] unitLaw (var 0))
      apply deriveNat; ipra_simps
      rw [a,b,c,d]
      ring
  simpa only [subst_unitLaw,Syn.subst_var,Syn.inst_zero] using all.allE K

def zeroLaw (K : PTm n) : Fm PTm n := numerator zero K ≐ fact (succ K)
ipra_subst zeroLaw [fact]

theorem zero_numerator (K : PTm n) : Γ ⊢[PRAAx] zeroLaw K := by
  have all : Γ ⊢[PRAAx] .all (zeroLaw (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_zeroLaw,Syn.subst_var,Syn.inst_zero]
      have a := natEq (numerator_zero (Γ := Γ) zero)
      have b := natEq (fact_succ (Γ := Γ) zero zero)
      have c := natEq (fact_zero (Γ := Γ) zero)
      apply deriveNat; ipra_simps
      rw [a,b,c]
      ring
    · simp only [subst_zeroLaw,Syn.subst_var,Syn.repl_zero]
      have a := natEq (numerator_succ (Γ := zeroLaw (var 0) :: Γ.map Fm.shift) zero (var 0))
      have b := natEq (LeanProofs.IPRA.DiophantineNumberTheory.SuperellipticFamily.zero_pw
        (Γ := zeroLaw (var 0) :: Γ.map Fm.shift) (var 0))
      have c := natEq (fact_succ (Γ := zeroLaw (var 0) :: Γ.map Fm.shift) (succ (var 0)) zero)
      apply deriveNat; ipra_simps
      rw [a,b,c,natEq (Prf.hyp0 : zeroLaw (var 0) :: Γ.map Fm.shift ⊢[PRAAx] zeroLaw (var 0))]
      ring
  simpa only [subst_zeroLaw,Syn.subst_var,Syn.inst_zero] using all.allE K

theorem value_at_zero (K : PTm n) : Γ ⊢[PRAAx] value zero K ≐ natCode one := by
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (GaussianRationalFiniteSum.sum_canonical _ _ _).andE₂.andE₁
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    (real_majorant_represents zero K) (natCode_represents one) (factorial_positive _) (le_refl one)
  ipra_lc natEq (zero_numerator (Γ := Γ) K)

theorem value_at_one_bound (K : PTm n) : Γ ⊢[PRAAx] rationalLE (value one K) (natCode (num 3)) := by
  apply GaussianRationalMetric.comparison_of_cleared _ _ _ _ (fact (succ K)) one
    (factorial_positive _) (le_refl one) (real_majorant_represents one K) (natCode_represents (num 3))
  have h : Γ ⊢[PRAAx] le (succ K*en K) (num 3*(fact K*succ K)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (succ K) (GaussianRationalExponentialLipschitz.en_bound K))
  exact le_congr ((unit_numerator K).eqSymm.eqTrans (by ipra_ring))
    (congrMul (.eqRefl _) (fact_succ K zero).eqSymm) h

def boundLaw (K R : PTm n) : Fm PTm n := rationalLE (value R K) (natCode (pw (num 3) R))
ipra_subst boundLaw

theorem bound_zero (K : PTm n) : Γ ⊢[PRAAx] boundLaw K zero :=
  RationalArgmin.rationalLE_congr (value_at_zero K).eqSymm (natCode_congr (pw_zero (num 3))).eqSymm
    (RationalArgmin.reflexive (natCode one))

theorem bound_step (K R : PTm n) (ih : Γ ⊢[PRAAx] boundLaw K R) : Γ ⊢[PRAAx] boundLaw K (succ R) := by
  have first := RationalArgmin.rationalLE_congr (RationalAlgebra.multiply_commutative _ _)
    (RationalAlgebra.multiply_commutative _ _)
    (RationalArithmetic.multiply_monotone (value one K) _ _
      (positive_scalar_sum (naturalPoint one) K (GaussianPositiveRealArithmetic.positive_natural one)).andE₂ ih)
  have second := RationalArithmetic.multiply_monotone (Γ := Γ) (natCode (pw (num 3) R)) _ _
    (natCode_nonnegative _) (value_at_one_bound K)
  have actual := RationalArgmin.transitive (value_successor_product R K) (RationalArgmin.transitive first second)
  exact RationalArgmin.rationalLE_congr (.eqRefl _)
    ((GaussianRationalSyntheticBounds.natCode_multiply _ _).eqTrans (natCode_congr (pw_succ (num 3) R).eqSymm)) actual

/-- Uniform in the actual cutoff K, by genuine QF induction on the numerical radius R. -/
theorem positive_real_majorant (R K : PTm n) : Γ ⊢[PRAAx] boundLaw K R := by
  have all : Γ ⊢[PRAAx] .all (boundLaw (Syn.shift K) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_boundLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using bound_zero K
    · simp only [subst_boundLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact bound_step _ _ Prf.hyp0
  simpa only [subst_boundLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE R

theorem disk_bound (q R K : PTm n) (hq : Γ ⊢[PRAAx] GaussianRationalMetric.bounded q R one) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (scalarSum q K) (pw (num 3) R) one :=
  GaussianExponentialDiskMajorant.magnitude_from_real q R K _ hq (positive_real_majorant R K)

theorem original_all_cutoff_positive_real_exponential_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (rationalLE (value (var 0) (var 1)) (natCode (pw (num 3) (var 0)))) :=
  closeUniv 2 (positive_real_majorant _ _)
theorem original_all_cutoff_gaussian_disk_exponential_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianRationalMetric.bounded (var 0) (var 1) one ⟶
      GaussianRationalMetric.bounded (scalarSum (var 0) (var 2)) (pw (num 3) (var 1)) one) :=
  closeUniv 3 (.impI (disk_bound _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPositiveExponentialMajorant
