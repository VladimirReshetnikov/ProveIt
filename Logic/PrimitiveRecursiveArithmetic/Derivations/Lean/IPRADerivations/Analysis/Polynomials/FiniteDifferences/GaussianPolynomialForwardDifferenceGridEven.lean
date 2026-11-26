import IPRADerivations.Analysis.Polynomials.FiniteDifferences.GaussianPolynomialForwardDifferenceGridLinearity
import IPRADerivations.Analysis.Polynomials.Horner.GaussianRationalHornerLeadingSplit
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalParityPower
import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianDeterminantSignTransport

/-!
# Cancellation of the next polynomial degree by opposite Gaussian steps

Combine the two sampled grids with the parity sign for the order and
normalize using their common step power. The degree-(e+1) monomial
cancels in every row. The doubled result reads the exact factorial-scaled
degree-(e) coefficient of the original polynomial.
-/

set_option autoImplicit false
set_option maxHeartbeats 1150000

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifferenceGridEven

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Analysis.Products (fact)
open GaussianPolynomialForwardDifferenceGrid (point samples sample_lookup leading_coefficient)
open GaussianPolynomialForwardDifferenceGridLinearity (combined combined_equal normalized_combined rowValue)
open GaussianPolynomialForwardDifferenceNormalization (normalized inversePower inverse_power_product)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalEulerCoefficients (parityPoint)
open GaussianRationalHorner (canonical evaluate qadd qmul qmul_canonical qzero)
open GaussianRationalHornerLeadingSplit (evaluation_split leadingTerm lowerCoefficients lower_length lower_at)
open GaussianRationalMatrixFiniteSums (minusOne negative_as_minusOne)
open GaussianRationalMetric (qnegative)
open GaussianRationalNaturalScale (natScale natScale_as_product natScale_canonical natScale_congr natScale_product)
open GaussianRationalParityPower (minus_one_power negative_power parity_succ)
open GaussianRationalPowerAlgebra (qmul_commutative power_product)
open GaussianRationalReciprocal (power)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticCoefficientValues (qmul_recode_right)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qone qone_canonical qzero_add)
open GaussianReciprocalHorner (qadd_commutative qmul_associative qmul_one_right)
open GaussianTranslatedNonconstant (recode recode_canonical)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem swap_mul (a b c : PTm n) : Γ ⊢[PRAAx] qmul a (qmul b c) ≐ qmul b (qmul a c) :=
  (qmul_associative a b c).eqSymm.eqTrans
    ((qmul_congr (qmul_commutative a b) (.eqRefl _)).eqTrans (qmul_associative b a c))

private theorem one_mul (a : PTm n) (ha : Γ ⊢[PRAAx] canonical a) : Γ ⊢[PRAAx] qmul qone a ≐ a :=
  (qmul_commutative qone a).eqTrans (qmul_one_right a ha)

theorem parity_square (e : PTm n) : Γ ⊢[PRAAx] qmul (parityPoint e) (parityPoint e) ≐ qone := by
  have square : Γ ⊢[PRAAx] qmul minusOne minusOne ≐ qone :=
    (negative_as_minusOne minusOne).eqSymm.eqTrans (GaussianDeterminantSignTransport.negative_involution qone qone_canonical)
  have p := (minus_one_power (Γ := Γ) e).eqSymm
  exact (qmul_congr p p).eqTrans ((power_product minusOne minusOne e).eqSymm.eqTrans
    ((congrAp2 GaussianRationalReciprocal.powerF (.eqRefl e) square).eqTrans (GaussianRationalRoundedPower.qone_power e)))

theorem parity_product_succ (e : PTm n) : Γ ⊢[PRAAx] qmul (parityPoint e) (parityPoint (succ e)) ≐ minusOne := by
  let p := parityPoint e
  have step := (parity_succ (Γ := Γ) e).eqTrans (negative_as_minusOne p)
  exact (qmul_congr (.eqRefl p) step).eqTrans ((swap_mul p minusOne p).eqTrans
    ((qmul_congr (.eqRefl minusOne) (parity_square e)).eqTrans
      (qmul_one_right minusOne (GaussianRationalMetric.qnegative_canonical qone))))

private theorem point_at_zero (h j : PTm n) : Γ ⊢[PRAAx] point qzero h j ≐ natScale j h :=
  qzero_add _ (natScale_canonical _ _)

theorem point_negative (h j : PTm n) : Γ ⊢[PRAAx] point qzero (qnegative h) j ≐ qnegative (point qzero h j) := by
  let x := GaussianRationalNaturalScale.naturalPoint j
  have scale : Γ ⊢[PRAAx] natScale j (qnegative h) ≐ qnegative (natScale j h) :=
    (natScale_as_product j _).eqTrans ((qmul_congr (.eqRefl x) (negative_as_minusOne h)).eqTrans
      ((swap_mul x minusOne h).eqTrans (((qmul_congr (.eqRefl minusOne) (natScale_as_product j h).eqSymm)).eqTrans
        (negative_as_minusOne (natScale j h)).eqSymm)))
  exact (point_at_zero (qnegative h) j).eqTrans (scale.eqTrans
    (GaussianInverseBinomialRows.negative_congr (point_at_zero h j).eqSymm))

private theorem leading_negative (C w e : PTm n) :
    Γ ⊢[PRAAx] leadingTerm C (qnegative w) e ≐ qmul (parityPoint e) (leadingTerm C w e) :=
  (qmul_congr (.eqRefl _) (negative_power w e)).eqTrans (swap_mul (entry C zero) (parityPoint e) (power w e))

private theorem exchange_sums (a b c d : PTm n) :
    Γ ⊢[PRAAx] qadd (qadd a b) (qadd c d) ≐ qadd (qadd a c) (qadd b d) :=
  (qadd_associative a b (qadd c d)).eqTrans
    ((qadd_congr (.eqRefl _) (((qadd_associative b c d).eqSymm.eqTrans
      (qadd_congr (qadd_commutative b c) (.eqRefl _))).eqTrans (qadd_associative c b d))).eqTrans
      (qadd_associative a c (qadd b d)).eqSymm)

private theorem drop_opposite (a l m p q : PTm n) (ha : Γ ⊢[PRAAx] canonical a)
    (hp : Γ ⊢[PRAAx] qmul p q ≐ minusOne) :
    Γ ⊢[PRAAx] qadd (qmul qone (qadd a l)) (qmul p (qadd (qmul q a) m)) ≐ qadd (qmul qone l) (qmul p m) := by
  let x := qmul qone l
  let y := qmul p m
  have cancel : Γ ⊢[PRAAx] qadd (qmul qone a) (qmul p (qmul q a)) ≐ qzero :=
    (qadd_congr (one_mul a ha) ((qmul_associative p q a).eqSymm.eqTrans
      ((qmul_congr hp (.eqRefl _)).eqTrans (negative_as_minusOne a).eqSymm))).eqTrans
      (GaussianCoefficientNormOrder.qsub_self a)
  exact (qadd_congr (qmul_add qone a l) (qmul_add p (qmul q a) m)).eqTrans
    ((exchange_sums (qmul qone a) x (qmul p (qmul q a)) y).eqTrans
      ((qadd_congr cancel (.eqRefl _)).eqTrans (qzero_add _ (GaussianRationalHorner.qadd_canonical x y))))

def evenRows (C e h : PTm n) : PTm n :=
  combined (samples C (succ e) qzero h) (samples C (succ e) qzero (qnegative h)) qone (parityPoint e) (succ e)

def doubled (C e h : PTm n) : PTm n := normalized (evenRows C e h) e h

private theorem row_reduction (C e h j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ (succ e))
    (hj : Γ ⊢[PRAAx] lt j (succ e)) :
    let Q := lowerCoefficients C (succ e)
    Γ ⊢[PRAAx] rowValue (samples C (succ e) qzero h) (samples C (succ e) qzero (qnegative h)) qone (parityPoint e) j ≐
      rowValue (samples Q (succ e) qzero h) (samples Q (succ e) qzero (qnegative h)) qone (parityPoint e) j := by
  let Q := lowerCoefficients C (succ e)
  let w := point qzero h j
  let v := point qzero (qnegative h) j
  let a := leadingTerm C w (succ e)
  let p := parityPoint e
  let q := parityPoint (succ e)
  let l := evaluate Q w
  let m := evaluate Q v
  have opposite : Γ ⊢[PRAAx] leadingTerm C v (succ e) ≐ qmul q a :=
    (qmul_congr (.eqRefl _) (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl _) (point_negative h j))).eqTrans
      (leading_negative C w (succ e))
  have front := (sample_lookup C (succ e) qzero h j hj).eqTrans (evaluation_split C w (succ e) hC)
  have back := (sample_lookup C (succ e) qzero (qnegative h) j hj).eqTrans
    ((evaluation_split C v (succ e) hC).eqTrans (qadd_congr opposite (.eqRefl m)))
  exact (qadd_congr (qmul_congr (.eqRefl qone) front) (qmul_congr (.eqRefl p) back)).eqTrans
    ((drop_opposite a l m p q (qmul_canonical _ _) (parity_product_succ e)).eqTrans
      (qadd_congr (qmul_congr (.eqRefl qone) (sample_lookup Q (succ e) qzero h j hj).eqSymm)
        (qmul_congr (.eqRefl p) (sample_lookup Q (succ e) qzero (qnegative h) j hj).eqSymm)))

theorem reduce_even_rows (C e h : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ (succ e)) :
    Γ ⊢[PRAAx] evenRows C e h ≐ evenRows (lowerCoefficients C (succ e)) e h := by
  refine combined_equal _ _ _ _ _ _ _ _ _ ?_
  let sh (t : PTm n) := Syn.shift t
  let j : PTm (n+1) := var 0
  let Δ := lt j (succ (sh e)) :: Γ.map Fm.shift
  have shape : Δ ⊢[PRAAx] length (sh C) ≐ succ (succ (sh e)) := by
    simpa [Δ,sh,j,Fm.shift,Syn.shift] using hC.shift.wk
  have hj : Δ ⊢[PRAAx] lt j (succ (sh e)) := Prf.hyp0
  simpa [sh,j,Δ,Syn.shift,one] using row_reduction (sh C) (sh e) (sh h) j shape hj

private theorem inverse_parity_cancel (a e h R : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hh : Γ ⊢[PRAAx] GaussianNameReciprocal.lower h R) :
    Γ ⊢[PRAAx] qmul (parityPoint e) (qmul (inversePower h e) (qmul a (power (qnegative h) e))) ≐ recode a := by
  let p := parityPoint e
  let s := inversePower h e
  let w := power h e
  have move : Γ ⊢[PRAAx] qmul p (qmul s (qmul a (qmul p w))) ≐ qmul (qmul p p) (qmul s (qmul w a)) :=
    (qmul_congr (.eqRefl p) (qmul_congr (.eqRefl s)
      ((swap_mul a p w).eqTrans (qmul_congr (.eqRefl p) (qmul_commutative a w))))).eqTrans
      ((qmul_congr (.eqRefl p) (swap_mul s p (qmul w a))).eqTrans
        (qmul_associative p p (qmul s (qmul w a))).eqSymm)
  have cancel : Γ ⊢[PRAAx] qmul s (qmul w a) ≐ recode a :=
    (qmul_associative s w a).eqSymm.eqTrans
      ((qmul_congr (inverse_power_product h e R hR hh) (.eqRefl _)).eqTrans
        (GaussianRationalFiniteProduct.raw_one_left a))
  exact (qmul_congr (.eqRefl p) (qmul_congr (.eqRefl s) (qmul_congr (.eqRefl a) (negative_power h e)))).eqTrans
    (move.eqTrans ((qmul_congr (parity_square e) cancel).eqTrans (one_mul _ (recode_canonical a))))

private theorem scale_recode (e a : PTm n) : Γ ⊢[PRAAx] natScale e (recode a) ≐ natScale e a :=
  (natScale_as_product e (recode a)).eqTrans ((qmul_recode_right _ _).eqTrans (natScale_as_product e a).eqSymm)

private theorem negative_orientation (C e h R : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ e)
    (hR : Γ ⊢[PRAAx] le one R) (hh : Γ ⊢[PRAAx] GaussianNameReciprocal.lower h R) :
    Γ ⊢[PRAAx] qmul (parityPoint e) (normalized (samples C (succ e) qzero (qnegative h)) e h) ≐
      natScale (fact e) (entry C zero) := by
  let a := entry C zero
  let p := parityPoint e
  let s := inversePower h e
  let z := qmul a (power (qnegative h) e)
  have read := leading_coefficient C e qzero (qnegative h) hC
  exact (qmul_congr (.eqRefl p) (qmul_congr (.eqRefl s) read)).eqTrans
    ((qmul_congr (.eqRefl p) (natScale_product (fact e) s z)).eqTrans
      ((natScale_product (fact e) p (qmul s z)).eqTrans
        ((natScale_congr (.eqRefl _) (inverse_parity_cancel a e h R hR hh)).eqTrans (scale_recode (fact e) a))))

theorem coefficient (C e h R : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ (succ e))
    (hR : Γ ⊢[PRAAx] le one R) (hh : Γ ⊢[PRAAx] GaussianNameReciprocal.lower h R) :
    Γ ⊢[PRAAx] doubled C e h ≐ natScale two (natScale (fact e) (entry C one)) := by
  let Q := lowerCoefficients C (succ e)
  let b := natScale (fact e) (entry Q zero)
  have hQ : Γ ⊢[PRAAx] length Q ≐ succ e := lower_length C (succ e)
  have positive := GaussianPolynomialForwardDifferenceNormalization.coefficient Q e qzero h R hQ hR hh
  have negative := negative_orientation Q e h R hQ hR hh
  have reduce : Γ ⊢[PRAAx] doubled C e h ≐ doubled Q e h := by
    ipra_congr (normalized (var 0) (var 1) (var 2) : PTm 3)
      with [reduce_even_rows C e h hC, .eqRefl e, .eqRefl h] using [doubled,Q]
  have read : Γ ⊢[PRAAx] doubled C e h ≐ qadd b b :=
    reduce.eqTrans
      ((normalized_combined (samples Q (succ e) qzero h) (samples Q (succ e) qzero (qnegative h))
        qone (parityPoint e) e h).eqTrans
        (qadd_congr ((qmul_congr (.eqRefl qone) positive).eqTrans (one_mul b (natScale_canonical _ _))) negative))
  have low : Γ ⊢[PRAAx] qadd b b ≐ natScale two b :=
    ((natScale_congr (by ipra_ring : Γ ⊢[PRAAx] two ≐ one+one) (.eqRefl b)).eqTrans
      ((GaussianRationalNaturalScale.natScale_add one one b).eqTrans
        (qadd_congr (GaussianRationalNaturalScale.natScale_one_canonical b (natScale_canonical _ _))
          (GaussianRationalNaturalScale.natScale_one_canonical b (natScale_canonical _ _))))).eqSymm
  have atOne := (lower_at C (succ e) zero (zero_lt_succ (Γ := Γ) e)).eqTrans
    (GaussianTranslatedNonconstant.recode_congr (show Γ ⊢[PRAAx] entry C (succ zero) ≐ entry C one from .eqRefl _))
  exact read.eqTrans (low.eqTrans (natScale_congr (.eqRefl _) ((natScale_congr (.eqRefl _) atOne).eqTrans (scale_recode _ _))))

theorem actual_Gaussian_even_grid_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let C := var 0
     let e := var 1
     let h := var 2
     let R := var 3
     length C ≐ succ (succ e) ⟶ le one R ⟶ GaussianNameReciprocal.lower h R ⟶
       doubled C e h ≐ natScale two (natScale (fact e) (entry C one))) :=
  closeUniv 4 (.impI (.impI (.impI (coefficient _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifferenceGridEven
