import IPRADerivations.Analysis.Polynomials.FiniteDifferences.GaussianPolynomialForwardDifferenceGridEvenError

/-!
# The leading coefficient on two opposite grids with independent origins

At the polynomial degree, the normalized difference has the same value
at every starting point. The encoded sign compensates for the negative
step when both grids use the positive inverse step power.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifferenceGridOppositeCoefficient

open_ipra
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Analysis.Products (fact)
open GaussianNameReciprocal (lower)
open GaussianPolynomialForwardDifferenceGrid (samples leading_coefficient)
open GaussianPolynomialForwardDifferenceGridEven (parity_square)
open GaussianPolynomialForwardDifferenceGridEvenError (observedDouble)
open GaussianPolynomialForwardDifferenceGridLinearity (normalized_combined)
open GaussianPolynomialForwardDifferenceNormalization (inversePower normalized inverse_power_product)
open GaussianRationalEulerCoefficients (parityPoint)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (qnegative)
open GaussianRationalNaturalScale (natScale natScale_add natScale_as_product natScale_canonical natScale_congr natScale_one_canonical natScale_product)
open GaussianRationalParityPower (negative_power)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (power)
open GaussianRationalSyntheticCoefficientValues (qmul_recode_right)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qone qone_canonical)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianTranslatedNonconstant (recode recode_canonical)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem swap_mul (a b c : PTm n) : Γ ⊢[PRAAx] qmul a (qmul b c) ≐ qmul b (qmul a c) :=
  (qmul_associative a b c).eqSymm.eqTrans
    ((qmul_congr (qmul_commutative a b) (.eqRefl _)).eqTrans (qmul_associative b a c))

private theorem cancel_orientation (a N h R : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hh : Γ ⊢[PRAAx] lower h R) :
    Γ ⊢[PRAAx] qmul (parityPoint N) (qmul (inversePower h N) (qmul a (power (qnegative h) N))) ≐ recode a := by
  let p := parityPoint N
  let b := inversePower h N
  let c := power h N
  let d := power (qnegative h) N
  have sign : Γ ⊢[PRAAx] qmul p (qmul b d) ≐ qone :=
    (qmul_congr (.eqRefl p) (qmul_congr (.eqRefl b) (negative_power h N))).eqTrans
      ((qmul_congr (.eqRefl p) (swap_mul b p c)).eqTrans
        ((qmul_associative p p (qmul b c)).eqSymm.eqTrans
          ((qmul_congr (parity_square N) (inverse_power_product h N R hR hh)).eqTrans (qmul_one_right qone qone_canonical))))
  exact (qmul_congr (.eqRefl p) (swap_mul b a d)).eqTrans
    ((swap_mul p a (qmul b d)).eqTrans
      ((qmul_congr (.eqRefl a) sign).eqTrans
        ((qmul_commutative a qone).eqTrans (GaussianRationalFiniteProduct.raw_one_left a))))

theorem negative_orientation (C N x h R : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hR : Γ ⊢[PRAAx] le one R) (hh : Γ ⊢[PRAAx] lower h R) :
    Γ ⊢[PRAAx] qmul (parityPoint N) (normalized (samples C (succ N) x (qnegative h)) N h) ≐
      natScale (fact N) (entry C zero) := by
  let a := entry C zero
  let p := parityPoint N
  let b := inversePower h N
  let d := qmul a (power (qnegative h) N)
  have read := leading_coefficient C N x (qnegative h) hC
  have recode_scale : Γ ⊢[PRAAx] natScale (fact N) (recode a) ≐ natScale (fact N) a :=
    (natScale_as_product (fact N) (recode a)).eqTrans
      ((qmul_recode_right _ _).eqTrans (natScale_as_product (fact N) a).eqSymm)
  exact (qmul_congr (.eqRefl p) (qmul_congr (.eqRefl b) read)).eqTrans
    ((qmul_congr (.eqRefl p) (natScale_product (fact N) b d)).eqTrans
      ((natScale_product (fact N) p (qmul b d)).eqTrans
        ((natScale_congr (.eqRefl _) (cancel_orientation a N h R hR hh)).eqTrans recode_scale)))

theorem coefficient (C N x y h R : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hR : Γ ⊢[PRAAx] le one R) (hh : Γ ⊢[PRAAx] lower h R) :
    Γ ⊢[PRAAx] observedDouble (samples C (succ N) x h) (samples C (succ N) y (qnegative h)) N h ≐
      natScale two (natScale (fact N) (entry C zero)) := by
  let b := natScale (fact N) (entry C zero)
  have hB := natScale_canonical (Γ := Γ) (fact N) (entry C zero)
  have left := GaussianPolynomialForwardDifferenceNormalization.coefficient C N x h R hC hR hh
  have right := negative_orientation C N y h R hC hR hh
  have first := (qmul_congr (.eqRefl qone) left).eqTrans ((qmul_commutative qone b).eqTrans (qmul_one_right b hB))
  have twice := (natScale_congr (by ipra_ring : Γ ⊢[PRAAx] two ≐ one+one) (.eqRefl b)).eqTrans
    ((natScale_add one one b).eqTrans (qadd_congr (natScale_one_canonical b hB) (natScale_one_canonical b hB)))
  exact (normalized_combined (samples C (succ N) x h) (samples C (succ N) y (qnegative h)) qone (parityPoint N) N h).eqTrans
    ((qadd_congr first right).eqTrans twice.eqSymm)

theorem actual_Gaussian_opposite_grid_leading_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let C := var 0
     let N := var 1
     let x := var 2
     let y := var 3
     let h := var 4
     let R := var 5
     length C ≐ succ N ⟶ le one R ⟶ lower h R ⟶
       observedDouble (samples C (succ N) x h) (samples C (succ N) y (qnegative h)) N h ≐
         natScale two (natScale (fact N) (entry C zero))) :=
  closeUniv 6 (.impI (.impI (.impI (coefficient _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifferenceGridOppositeCoefficient
