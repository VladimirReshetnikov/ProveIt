import IPRADerivations.Analysis.Polynomials.CompanionMatrices.GaussianRationalCharacteristicPolynomial
import IPRADerivations.Analysis.Polynomials.Coefficients.Norms.GaussianCoefficientNormOrder
import IPRADerivations.Analysis.Polynomials.Coefficients.Norms.GaussianPolynomialNormBuffers

/-!
# Norm bounds for the original characteristic entry polynomials

The entry is the existing two-coefficient cellPolynomial, without a new
entry constructor. Original Euclidean cell bounds give coefficient L1
bounds; the actual coefficient difference has zero head and exactly the
L1 norm of the original cell difference. Raw matrix cells are permitted.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCharacteristicEntryNorm

open_ipra
open GaussianRationalCharacteristicPolynomial (cellPolynomial cell_length cell_head cell_tail)
open GaussianPolynomialDeterminantTerms (cell)
open GaussianCoefficientL1 (coefficientNorm prefixNorm prefix_succ qL1_congr subCoefficients sub_lookup)
open GaussianRationalHorner (qzero canonical_unique represents_congr)
open GaussianRationalMetric (qsub qnegative bounded distanceBounded qnegative_represents qsub_represents)
open GaussianRationalL1 (qL1 qL1_guard)
open GaussianRationalL1Algebra (qL1_negative qL1_of_bounded)
open GaussianRationalSyntheticBounds (natCode natCode_add natCode_order qL1_qone add_monotone)
open GaussianRationalLinearProduct (norm_length scalar_zero_code scalar_zero_add qzero_norm)
open RationalArithmetic (add)
open RationalArgmin (rationalLE rationalLE_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem two_coefficient_norm (C : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ two) :
    Γ ⊢[PRAAx] coefficientNorm C ≐ add (qL1 (entry C zero)) (qL1 (entry C one)) := by
  have first := (prefix_succ (Γ := Γ) C zero).eqTrans
    ((RationalAlgebra.add_congr ((GaussianCoefficientL1.prefix_zero C).eqTrans scalar_zero_code.eqSymm) (.eqRefl _)).eqTrans
      (scalar_zero_add _ (qL1_guard _)))
  exact (norm_length C two hC).eqTrans
    ((prefix_succ C one).eqTrans (RationalAlgebra.add_congr first (.eqRefl _)))

theorem entry_norm_identity (A r j : PTm n) : Γ ⊢[PRAAx]
    coefficientNorm (cellPolynomial A r j) ≐ add (qL1 (GaussianRationalFiberVandermonde.delta r j)) (qL1 (cell A r j)) :=
  (two_coefficient_norm _ (cell_length A r j)).eqTrans
    (RationalAlgebra.add_congr (qL1_congr (cell_head A r j))
      ((qL1_congr (cell_tail A r j)).eqTrans (qL1_negative _)))

theorem delta_norm_bound (r j : PTm n) : Γ ⊢[PRAAx]
    rationalLE (qL1 (GaussianRationalFiberVandermonde.delta r j)) (natCode one) := by
  refine .orE (eq_or_ne r j) ?_ ?_
  · have e : (r ≐ j) :: Γ ⊢[PRAAx] qL1 (GaussianRationalFiberVandermonde.delta r j) ≐ natCode one :=
      (qL1_congr (RationalArithmetic.select_one _ _ _ (eqb_of_eq Prf.hyp0))).eqTrans qL1_qone
    exact rationalLE_congr e.eqSymm (.eqRefl _) (RationalArgmin.reflexive _)
  · have e : neg (r ≐ j) :: Γ ⊢[PRAAx] qL1 (GaussianRationalFiberVandermonde.delta r j) ≐ natCode zero :=
      (qL1_congr (RationalArithmetic.select_zero _ _ _ (eqb_of_ne Prf.hyp0))).eqTrans qzero_norm
    exact rationalLE_congr e.eqSymm (.eqRefl _) (natCode_order zero one (zero_le one))

theorem entry_norm_bound (A r j B D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] bounded (cell A r j) B D) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (cellPolynomial A r j))
      (add (natCode one) (RationalIntegerNormalization.normalize (ZT.ofNat (two*B)) D)) :=
  rationalLE_congr (entry_norm_identity A r j).eqSymm (.eqRefl _)
    (add_monotone _ _ _ _ (delta_norm_bound r j) (qL1_of_bounded _ _ _ hD h))

theorem entry_natural_norm_bound (A r j B : PTm n) (h : Γ ⊢[PRAAx] bounded (cell A r j) B one) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (cellPolynomial A r j)) (natCode (one+two*B)) :=
  rationalLE_congr (.eqRefl _) (natCode_add one (two*B)) (entry_norm_bound A r j B one (le_refl one) h)

theorem entry_relaxed_norm_bound (A r j B : PTm n) (h : Γ ⊢[PRAAx] bounded (cell A r j) B one) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (cellPolynomial A r j)) (natCode (two*(B+one))) :=
  RationalArgmin.transitive (entry_natural_norm_bound A r j B h)
    (natCode_order _ _ (le_of_eq_add (d := one) (by ipra_ring)))

theorem negative_difference (a b : PTm n) : Γ ⊢[PRAAx]
    qsub (qnegative a) (qnegative b) ≐ qnegative (qsub a b) := by
  let E := GaussianRationalValueEquality.commonDen a b
  have hE := GaussianRationalValueEquality.common_den_positive (Γ := Γ) a b
  have lhs := qsub_represents _ _ _ _ E hE
    (qnegative_represents _ _ _ (GaussianRationalValueEquality.common_left_represents a b))
    (qnegative_represents _ _ _ (GaussianRationalValueEquality.common_right_represents a b))
  have rhs := qnegative_represents _ _ _ (GaussianRationalValueEquality.difference_represents (Γ := Γ) a b)
  apply canonical_unique _ _ _ _ (GaussianRationalMetric.qsub_canonical _ _)
    (GaussianRationalMetric.qnegative_canonical _) hE (hrv := rhs)
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) lhs
  apply GaussianRootAlgebra.equal_of_values
  all_goals simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
    GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg]; ring

def difference (A B r j : PTm n) : PTm n := subCoefficients (cellPolynomial A r j) (cellPolynomial B r j) two
ipra_subst difference
theorem difference_length (A B r j : PTm n) : Γ ⊢[PRAAx] length (difference A B r j) ≐ two :=
  GaussianCoefficientL1.zip_length _ _ _ _
theorem difference_head (A B r j : PTm n) : Γ ⊢[PRAAx] entry (difference A B r j) zero ≐ qzero :=
  (sub_lookup _ _ _ _ (zero_lt_succ one)).eqTrans
    ((GaussianRationalSyntheticDivision.qsub_congr (cell_head A r j) (cell_head B r j)).eqTrans
      (GaussianCoefficientNormOrder.qsub_self _))
theorem difference_tail (A B r j : PTm n) : Γ ⊢[PRAAx] entry (difference A B r j) one ≐ qnegative (qsub (cell A r j) (cell B r j)) :=
  (sub_lookup _ _ _ _ (le_refl two)).eqTrans
    ((GaussianRationalSyntheticDivision.qsub_congr (cell_tail A r j) (cell_tail B r j)).eqTrans (negative_difference _ _))
theorem difference_norm_identity (A B r j : PTm n) : Γ ⊢[PRAAx]
    coefficientNorm (difference A B r j) ≐ qL1 (qsub (cell A r j) (cell B r j)) :=
  (two_coefficient_norm _ (difference_length A B r j)).eqTrans
    ((RationalAlgebra.add_congr ((qL1_congr (difference_head A B r j)).eqTrans qzero_norm)
      ((qL1_congr (difference_tail A B r j)).eqTrans (qL1_negative _))).eqTrans (scalar_zero_add _ (qL1_guard _)))
theorem entry_difference_bound (A B r j P Q : PTm n) (hQ : Γ ⊢[PRAAx] le one Q)
    (h : Γ ⊢[PRAAx] distanceBounded (cell A r j) (cell B r j) P Q) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (difference A B r j))
      (RationalIntegerNormalization.normalize (ZT.ofNat (two*P)) Q) :=
  rationalLE_congr (difference_norm_identity A B r j).eqSymm (.eqRefl _) (qL1_of_bounded _ _ _ hQ h)

theorem actual_characteristic_entry_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 4) ⟶ bounded (cell (var 0) (var 1) (var 2)) (var 3) (var 4) ⟶
      rationalLE (coefficientNorm (cellPolynomial (var 0) (var 1) (var 2)))
        (add (natCode one) (RationalIntegerNormalization.normalize (ZT.ofNat (two*var 3)) (var 4)))) :=
  closeUniv 5 (.impI (.impI (entry_norm_bound _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_characteristic_entry_relaxed_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (bounded (cell (var 0) (var 1) (var 2)) (var 3) one ⟶
      rationalLE (coefficientNorm (cellPolynomial (var 0) (var 1) (var 2))) (natCode (two*(var 3+one)))) :=
  closeUniv 4 (.impI (entry_relaxed_norm_bound _ _ _ _ Prf.hyp0))
theorem actual_characteristic_entry_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 5) ⟶ distanceBounded (cell (var 0) (var 2) (var 3)) (cell (var 1) (var 2) (var 3)) (var 4) (var 5) ⟶
      rationalLE (coefficientNorm (difference (var 0) (var 1) (var 2) (var 3)))
        (RationalIntegerNormalization.normalize (ZT.ofNat (two*var 4)) (var 5))) :=
  closeUniv 6 (.impI (.impI (entry_difference_bound _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianCharacteristicEntryNorm
