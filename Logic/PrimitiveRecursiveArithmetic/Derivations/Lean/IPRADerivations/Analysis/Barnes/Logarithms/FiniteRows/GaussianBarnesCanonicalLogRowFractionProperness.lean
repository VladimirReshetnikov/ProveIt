import IPRADerivations.Analysis.Barnes.Logarithms.FiniteRows.GaussianBarnesCanonicalLogRow
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalFiniteProperness
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianIntegerFractionPowers

/-!
# Equivalent rational presentations of the original Barnes log rows

The actual common-denominator cubic Mercator numerator obeys a
normalized Gaussian rational recurrence. Consequently the original
finite row has identical rational code at each Taylor length whenever
the two original charts represent the same point.
-/

set_option autoImplicit false
set_option maxHeartbeats 1150000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogRowFractionProperness

open_ipra
open ComplexLogarithmRemainder (add oneCode zeroCode scale series)
open GaussianBarnesCanonicalLogRow (cubic finiteValue)
open GaussianRationalHorner
  (canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents positive_product qadd qadd_canonical
    qadd_represents qmul qmul_represents qzero represents represents_congr zero_represents)
open GaussianRationalMetric (qnegative qnegative_canonical qnegative_represents)
open GaussianRationalReciprocal (power)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qzero_canonical rescale_to)
open GaussianRootAlgebra (equal equal_of_code equal_of_values equal_refl)
open LeanProofs.IPRA.Analysis.Products (fact)
open LogarithmRemainder (denominator denominator_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def nextTerm (z N L : PTm n) : PTm n :=
  qmul (ofGaussian oneCode (L+num 3)) (qnegative (power (qnegative (ofGaussian z N)) (L+num 3)))

private theorem negative_fraction (z N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] qnegative (ofGaussian z N) ≐ ofGaussian (ComplexLogarithmRemainder.neg z) N :=
  canonical_unique _ _ _ _ (qnegative_canonical _) (ofGaussian_canonical _ _ hN) hN
    (qnegative_represents _ _ _ (ofGaussian_represents z N hN)) (ofGaussian_represents _ _ hN)

private theorem next_denominator (N L : PTm n) :
    Γ ⊢[PRAAx] ((L+num 3)*pw N (L+num 3))*fact (L+two) ≐ denominator N (succ L) := by
  have e : Γ ⊢[PRAAx] succ L+two ≐ L+num 3 := by ipra_ring
  have f : Γ ⊢[PRAAx] fact (succ L+two) ≐ fact (L+two)*(L+num 3) :=
    (congrAp2 factF (by ipra_ring : Γ ⊢[PRAAx] succ L+two ≐ succ (L+two)) (.eqRefl zero)).eqTrans
      ((fact_succ (L+two) zero).eqTrans (congrMul (.eqRefl _) (by ipra_ring)))
  exact (show Γ ⊢[PRAAx] ((L+num 3)*pw N (L+num 3))*fact (L+two) ≐
    (fact (L+two)*(L+num 3))*pw N (L+num 3) by ipra_ring).eqTrans
      (congrMul f (congrAp2 powF e (.eqRefl N))).eqSymm

private theorem next_term_represents (z N L : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] represents (nextTerm z N L)
      (ComplexLogarithmRemainder.neg (scale (fact (L+two))
        (ComplexLogarithmRemainder.power (ComplexLogarithmRemainder.neg z) (L+num 3))))
      (denominator N (succ L)) := by
  let j := L+num 3
  let F := fact (L+two)
  let P := pw N j
  let Z := ComplexLogarithmRemainder.power (ComplexLogarithmRemainder.neg z) j
  let v := power (qnegative (ofGaussian z N)) j
  have hj : Γ ⊢[PRAAx] le one j := le_of_eq_add (d := L+two) (by dsimp only [j]; ipra_ring)
  have hp : Γ ⊢[PRAAx] le one P := GaussianFactorBudget.power_positive N j hN
  have ep : Γ ⊢[PRAAx] v ≐ power (ofGaussian (ComplexLogarithmRemainder.neg z) N) j :=
    congrAp2 GaussianRationalReciprocal.powerF (.eqRefl j) (negative_fraction z N hN)
  have rep : Γ ⊢[PRAAx] represents v Z P :=
    represents_congr ep.eqSymm (equal_refl Z) (.eqRefl _)
      (GaussianIntegerFractionPowers.power_represents (ComplexLogarithmRemainder.neg z) N j hN)
  have product := qmul_represents _ _ _ _ _ _ hj hp
    (ofGaussian_represents oneCode j hj) (qnegative_represents _ _ _ rep)
  have align : Γ ⊢[PRAAx] equal
      (scale F (ComplexLogarithmRemainder.mul oneCode (ComplexLogarithmRemainder.neg Z)))
      (ComplexLogarithmRemainder.neg (scale F Z)) := by
    apply equal_of_values <;>
      simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_neg,
        GaussianRootAlgebra.im_neg,GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,
        GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ring
  exact represents_congr (.eqRefl _) align (.eqRefl _)
    (rescale_to _ _ (j*P) F (denominator N (succ L)) product (next_denominator N L))

theorem cubic_succ (z N L : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] cubic z N (succ L) ≐ qadd (cubic z N L) (nextTerm z N L) := by
  let D := denominator N (succ L)
  let j := L+num 3
  have hd := denominator_positive N (succ L) hN
  have near : Γ ⊢[PRAAx] denominator N L*(j*N) ≐ D :=
    (mul_comm _ _).eqTrans (LogarithmRemainder.denominator_succ N L).eqSymm
  have rep := rescale_to (cubic z N L) (series z N L) (denominator N L) (j*N) D
    (ofGaussian_represents _ _ (denominator_positive N L hN)) near
  have addRep := qadd_represents _ _ _ _ _ hd rep (next_term_represents z N L hN)
  exact canonical_unique _ _ (series z N (succ L)) D (ofGaussian_canonical _ _ hd) (qadd_canonical _ _) hd
    (ofGaussian_represents _ _ hd)
    (represents_congr (.eqRefl _) (equal_of_code (ComplexLogarithmRemainder.series_succ z N L).eqSymm) (.eqRefl _) addRep)

private theorem cubic_zero (z N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] cubic z N zero ≐ qzero := by
  have hd := denominator_positive N zero hN
  exact canonical_unique _ _ zeroCode (denominator N zero)
    (ofGaussian_canonical _ _ hd) qzero_canonical hd
    (represents_congr (.eqRefl _) (equal_of_code (ComplexLogarithmRemainder.series_zero z N)) (.eqRefl _)
      (ofGaussian_represents _ _ hd)) (zero_represents _)

private theorem term_congr (z w N D L : PTm n) (he : Γ ⊢[PRAAx] ofGaussian z N ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] nextTerm z N L ≐ nextTerm w D L :=
  qmul_congr (.eqRefl _) (GaussianInverseBinomialRows.negative_congr
    (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl _) (GaussianInverseBinomialRows.negative_congr he)))

theorem cubic_equal (z w N D L : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hD : Γ ⊢[PRAAx] le one D)
    (he : Γ ⊢[PRAAx] ofGaussian z N ≐ ofGaussian w D) : Γ ⊢[PRAAx] cubic z N L ≐ cubic w D L := by
  let s (x : PTm n) := Syn.shift x
  have hns : Γ.map Fm.shift ⊢[PRAAx] le one (s N) := by simpa [s,Fm.shift,Syn.shift] using hN.shift
  have hds : Γ.map Fm.shift ⊢[PRAAx] le one (s D) := by simpa [s,Fm.shift,Syn.shift] using hD.shift
  have hes : Γ.map Fm.shift ⊢[PRAAx] ofGaussian (s z) (s N) ≐ ofGaussian (s w) (s D) := by
    simpa [s,Fm.shift,Syn.shift] using he.shift
  have all : Γ ⊢[PRAAx] .all (cubic (s z) (s N) (var 0) ≐ cubic (s w) (s D) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [Fm.subst_eq,GaussianBarnesCanonicalLogRow.subst_cubic,s,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        (cubic_zero z N hN).eqTrans (cubic_zero w D hD).eqSymm
    · simp only [Fm.subst_eq,GaussianBarnesCanonicalLogRow.subst_cubic,s,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (cubic_succ _ _ _ hns.wk).eqTrans
        ((qadd_congr Prf.hyp0 (term_congr _ _ _ _ _ hes.wk)).eqTrans (cubic_succ _ _ _ hds.wk).eqSymm)
  simpa only [Fm.subst_eq,GaussianBarnesCanonicalLogRow.subst_cubic,s,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE L

theorem finite_row_equal (z w B D k L : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hk : Γ ⊢[PRAAx] le one k) (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] finiteValue z B k L ≐ finiteValue w D k L :=
  qmul_congr (.eqRefl _) (cubic_equal z w (B*k) (D*k) L (positive_product _ _ hB hk) (positive_product _ _ hD hk)
    (GaussianBarnesCanonicalFiniteProperness.scaled_fraction_equal z w B D k hB hD hk he))

theorem actual_Barnes_finite_logarithm_row_fraction_proper_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let z := var 0
     let w := var 1
     let B := var 2
     let D := var 3
     let k := var 4
     let L := var 5
     (le one B ⋏ (le one D ⋏ (le one k ⋏ ofGaussian z B ≐ ofGaussian w D))) ⟶
       finiteValue z B k L ≐ finiteValue w D k L) :=
  closeUniv 6 (.impI (finite_row_equal _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogRowFractionProperness
