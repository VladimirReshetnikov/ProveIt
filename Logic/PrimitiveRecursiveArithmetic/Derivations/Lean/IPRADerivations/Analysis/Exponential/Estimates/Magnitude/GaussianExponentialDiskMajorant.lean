import IPRADerivations.Analysis.Exponential.Estimates.GaussianRationalExponentialTail
import IPRADerivations.Analysis.RationalArithmetic.Scaling.GaussianRationalNaturalScale

/-!
# Transfer from the positive scalar exponential to a Gaussian disk

The actual exponential tail numerator at offset zero represents the
positive real finite exponential at a numerical radius. The same
numerator and denominator bound the norm of the original finite
exponential at every Gaussian rational in the disk.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianExponentialDiskMajorant

open_ipra
open GaussianRationalHorner (qmul qadd represents represents_congr represents_rescale qadd_represents qmul_represents)
open GaussianRationalMetric (bounded comparison_to_cleared)
open GaussianRationalReciprocal (power bound_congr)
open GaussianRationalPolynomialExponential (inverseFactorial inverse_factorial_represents scalarBody scalarSum
  scalar_sum_zero scalar_sum_succ factorial_positive)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents)
open GaussianRootAlgebra (equal_of_values re_scale im_scale re_one im_one re_add im_add re_mul im_mul)
open ComplexLogarithmRemainder (scale oneCode)
open GaussianRationalSyntheticBounds (natCode natCode_represents)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (R K : PTm n) : PTm n := ExponentialTail.tsum zero R (succ K)

ipra_subst numerator [ExponentialTail.tsum]

theorem numerator_zero (R : PTm n) : Γ ⊢[PRAAx] numerator R zero ≐ one := by
  have e₀ := natEq (ExponentialTail.tsum_zero (Γ := Γ) zero R)
  have ep := natEq ((congrAp2 powF (zero_add (Γ := Γ) zero) (.eqRefl R)).eqTrans (pw_zero R))
  apply deriveNat
  unfold numerator
  rw [natEq (ExponentialTail.tsum_succ (Γ := Γ) zero R zero)]
  ipra_simps
  rw [ep, e₀]
  ring

theorem numerator_succ (R K : PTm n) : Γ ⊢[PRAAx]
    numerator R (succ K) ≐ (numerator R K+pw R (succ K))*succ (succ K) :=
  (ExponentialTail.tsum_succ zero R (succ K)).eqTrans
    (congrMul (congrAdd (.eqRefl _) (congrAp2 powF (zero_add _) (.eqRefl _))) (congrSucc (zero_add _)))

theorem natural_power_represents (R k : PTm n) : Γ ⊢[PRAAx]
    represents (power (naturalPoint R) k) (scale (pw R k) oneCode) one := by
  have all : Γ ⊢[PRAAx] .all (represents (power (naturalPoint (Syn.shift R)) (var 0))
      (scale (pw (Syn.shift R) (var 0)) oneCode) one) := by
    ipra_qfind (⟨trivial,trivial⟩) [GaussianRationalHorner.subst_represents, GaussianRationalReciprocal.subst_power,
        GaussianRationalNaturalScale.subst_naturalPoint, ComplexLogarithmRemainder.subst_scale,
        ComplexLogarithmRemainder.subst_oneCode, PTm.subst_succ, PTm.subst_zero, subst_ap2]
    · have rp := GaussianRationalHorner.ofGaussian_represents (Γ := Γ) oneCode one (le_refl _)
      exact represents_congr (GaussianRationalReciprocal.power_zero _).eqSymm (by
        apply equal_of_values
        · rw [re_one, re_scale, re_one, natEq (pw_zero (Γ := Γ) R)]; ipra_simps; ring
        · rw [im_one, im_scale, im_one]; ring) (.eqRefl _) rp
    · let r := Syn.shift R
      let j : PTm (n+1) := var 0
      let ih := represents (power (naturalPoint r) j) (scale (pw r j) oneCode) one
      have old : (ih :: Γ.map Fm.shift) ⊢[PRAAx] ih := Prf.hyp0
      have prod := qmul_represents _ _ _ _ one one (le_refl _) (le_refl _) old
        (natural_point_represents r)
      exact represents_congr (GaussianRationalReciprocal.power_succ _ _).eqSymm (by
        have ep := natEq (pw_succ (Γ := ih :: Γ.map Fm.shift) r j)
        apply equal_of_values
        · simp only [re_mul, re_scale, im_scale, re_one, im_one]
          simp only [Q.mk_mul, map_mul] at ep
          linear_combination -ep
        · simp only [im_mul, re_scale, im_scale, re_one, im_one]; ring) (one_mul _) prod
  simpa only [GaussianRationalHorner.subst_represents,GaussianRationalReciprocal.subst_power,
    GaussianRationalNaturalScale.subst_naturalPoint,ComplexLogarithmRemainder.subst_scale,
    ComplexLogarithmRemainder.subst_oneCode,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,
    PTm.subst_succ,PTm.subst_zero,subst_ap2] using all.allE k

theorem natural_term_represents (R k : PTm n) : Γ ⊢[PRAAx]
    represents (qmul (inverseFactorial k) (power (naturalPoint R) k))
      (scale (pw R k) oneCode) (fact k) := by
  apply represents_congr (.eqRefl _) ?_ (by ipra_ring)
    (qmul_represents _ _ _ _ _ _ (factorial_positive _) (le_refl _) (inverse_factorial_represents k)
      (natural_power_represents R k))
  apply equal_of_values <;> simp only [re_mul, im_mul, re_scale, im_scale, re_one, im_one] <;> ring

def majorantLaw (R K : PTm n) : Fm PTm n :=
  represents (scalarSum (naturalPoint R) K) (scale (numerator R K) oneCode) (fact (succ K))

ipra_subst majorantLaw [fact]

theorem majorant_zero (R : PTm n) : Γ ⊢[PRAAx] majorantLaw R zero := by
  change Γ ⊢[PRAAx] represents _ _ _
  refine represents_congr (scalar_sum_zero _).eqSymm ?_ ?_
    (GaussianRationalHorner.ofGaussian_represents oneCode one (le_refl _))
  · apply equal_of_values
    · rw [re_one,re_scale,re_one,natEq (numerator_zero (Γ := Γ) R)]; ipra_simps; ring
    · rw [im_one,im_scale,im_one]; ring
  · exact (fact_succ zero zero).eqTrans
      ((congrMul (fact_zero zero) (.eqRefl _)).eqTrans (one_mul _)) |>.eqSymm

theorem majorant_step (R K : PTm n) (ih : Γ ⊢[PRAAx] majorantLaw R K) :
    Γ ⊢[PRAAx] majorantLaw R (succ K) := by
  let S := GaussianRationalPolynomialExponential.scalarSum (naturalPoint R) K
  let C := scale (numerator R K) oneCode
  let D := scale (pw R (succ K)) oneCode
  let F := fact (succ K)
  have main := qadd_represents S _ C D F (factorial_positive (succ K)) ih (natural_term_represents R (succ K))
  have p := represents_rescale _ _ F (succ (succ K)) main
  change Γ ⊢[PRAAx] represents _ _ _
  refine represents_congr (scalar_sum_succ _ _).eqSymm ?_ (fact_succ (succ K) zero).eqSymm p
  dsimp only [C,D]
  apply equal_of_values
  · rw [re_scale,re_add,re_scale,re_scale,re_one,re_scale, re_one, natEq (numerator_succ (Γ := Γ) R K)]
    ipra_simps
    ring
  · simp only [im_scale,im_add,im_one]; ring

theorem majorant_represents (R K : PTm n) : Γ ⊢[PRAAx] majorantLaw R K := by
  have all : Γ ⊢[PRAAx] .all (majorantLaw (Syn.shift R) (var 0)) := by
    ipra_qfind (⟨trivial,trivial⟩) [subst_majorantLaw]
    · exact majorant_zero R
    · exact majorant_step _ _ Prf.hyp0
  ipra_simpa_inst [subst_majorantLaw] using all.allE K

theorem real_majorant_represents (R K : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (fstT (scalarSum (naturalPoint R) K))
      (ZT.ofNat (numerator R K)) (fact (succ K)) := by
  refine GaussianRationalHorner.scalar_congr (.eqRefl _) ?_ (.eqRefl _) (majorant_represents R K).andE₁
  apply ZT.derive
  rw [re_scale, re_one, ZT.toZ_ofNat]
  ring

theorem disk_majorant (q R K : PTm n) (hq : Γ ⊢[PRAAx] bounded q R one) : Γ ⊢[PRAAx]
    bounded (scalarSum q K) (numerator R K) (fact (succ K)) := by
  open GaussianRationalExponentialTail in
  have split : Γ ⊢[PRAAx] scalarSum q K ≐ tail q zero (succ K) :=
    (GaussianRationalFiniteSum.sum_index_congr scalarBody (zero_add (succ K)).eqSymm (.eqRefl _)).eqTrans
      ((prefix_split q zero (succ K)).eqTrans
        ((GaussianRationalSyntheticDivision.qadd_congr
          (GaussianRationalFiniteSum.sum_zero scalarBody q) (.eqRefl _)).eqTrans
          (GaussianRationalSyntheticDivision.qzero_add _ (tail_canonical _ _ _))))
  exact bound_congr split.eqSymm (.eqRefl _)
    (congrAp2 factF (zero_add _) (.eqRefl zero))
    (GaussianRationalExponentialTail.tail_bound q zero R (succ K) hq)

/-- A bound on the actual positive real sum transfers to the entire Gaussian disk. -/
theorem magnitude_from_real (q R K A : PTm n) (hq : Γ ⊢[PRAAx] bounded q R one)
    (h : Γ ⊢[PRAAx] RationalArgmin.rationalLE (fstT (scalarSum (naturalPoint R) K)) (natCode A)) :
    Γ ⊢[PRAAx] bounded (scalarSum q K) A one := by
  have hc : Γ ⊢[PRAAx] le (one*numerator R K) (A*fact (succ K)) :=
    comparison_to_cleared _ _ _ _ _ _ (real_majorant_represents R K) (natCode_represents A) h
  exact GaussianCoefficientNameBounds.bounded_radius_mono (scalarSum q K) (numerator R K)
    (fact (succ K)) A one (factorial_positive _) (le_refl _)
    (le_congr (mul_comm _ _) (.eqRefl _) hc)
    (disk_majorant q R K hq)

theorem original_finite_exponential_disk_majorant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (bounded (var 0) (var 1) one ⟶
      RationalArgmin.rationalLE (fstT (scalarSum (naturalPoint (var 1)) (var 2))) (natCode (var 3)) ⟶
      bounded (scalarSum (var 0) (var 2)) (var 3) one) :=
  closeUniv 4 (.impI (.impI (magnitude_from_real _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianExponentialDiskMajorant
