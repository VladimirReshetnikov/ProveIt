import IPRADerivations.Analysis.LinearAlgebra.RationalCofactorSupport
import IPRADerivations.Analysis.LinearAlgebra.RationalMatrixInputHeight

/-!
# Exact values of the returned signed cofactor coefficients

The actual vector stores the signed integer numerator of its cofactor
minor. Normalizing that integer over one gives its rational value. At
each retained column the Gaussian embedding agrees with the determinant
of the corresponding actual minor multiplied by the relative sign.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCofactorCoefficientValues

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open RationalSupMetric (coordinate numeratorOf denominatorOf)
open RationalIntegerNormalization (normalize normalize_preserves_value)
open RationalCofactorVector (vector coefficientCode signedCode unsignedEntry positionParity integerPair
  vector_lookup vector_zero unpack_congr unpack_pair code_of_free code_off_free)
open RationalCofactorSupport (supportedColumn supported_label support_position_parity free_position_parity)
open RationalCofactorMinorBounds (minorValue cofactor_minor_bound)
open RationalMatrixInputHeight (height height_positive input_height)
open RationalIntegerMinorDeterminants (denominator_one_representation)
open RationalNormalForm (wellFormed normalize_well_formed)
open RationalGaussianEmbedding (embed scalarZero embed_zero embed_negative embed_canonical)
open RationalPolynomialGaussianEmbedding (embed_congr)
open RationalArithmetic (represents select_zero select_one)
open RationalSelectedMinors (count)
open RationalMinorAugmentation (extendedColumn)
open RationalMinorFreeColumn (free)
open RationalMaximalMinors (rank)
open RationalSubtupleSpan (bit)
open GaussianScalarDeterminantLaplace (unitSign sign_bit_even sign_bit_odd)
open GaussianRationalHorner (qmul qzero scalar_congr)
open GaussianRationalSyntheticDivision (qmul_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficientValue (P d j : PTm n) : PTm n := normalize (coordinate (vector P d) j) one

@[simp] theorem subst_coefficientValue {k : ℕ} (σ : Fin n → PTm k) (P d j : PTm n) :
    Syn.subst σ (coefficientValue P d j) = coefficientValue (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ j) := by
  simp [coefficientValue,RationalSupMetric.coordinate,ZT.subst,one]

theorem output_from_signed_code (P d j : PTm n) (hj : Γ ⊢[PRAAx] lt j d)
    (hs : Γ ⊢[PRAAx] bit (extendedColumn P d) j ≐ one) (a : ZT n)
    (e : Γ ⊢[PRAAx] signedCode P d j ≐ integerPair a) : Γ ⊢[PRAAx] ZT.eq (coordinate (vector P d) j) a := by
  have select : Γ ⊢[PRAAx] coefficientCode P d j ≐ signedCode P d j := select_one _ _ _ hs
  have out := unpack_congr ((vector_lookup P d j hj).eqTrans (select.eqTrans e))
  exact ZT.derive ((ZT.toZ_eq out).trans (ZT.toZ_eq (unpack_pair a)))

theorem even_code (P d j : PTm n) (h : Γ ⊢[PRAAx] positionParity P d j ≐ zero) :
    Γ ⊢[PRAAx] signedCode P d j ≐ integerPair (unsignedEntry P d j) := by
  refine .orE (eq_or_ne j (free P d)) (code_of_free P d j Prf.hyp0) ?_
  exact (code_off_free P d j Prf.hyp0).eqTrans (select_one _ _ _ (eqb_of_eq h.wk))

theorem parity_congr (P d : PTm n) {j k : PTm n} (e : Γ ⊢[PRAAx] j ≐ k) :
    Γ ⊢[PRAAx] positionParity P d j ≐ positionParity P d k := by
  have counts : Γ ⊢[PRAAx] count j (extendedColumn P d) ≐ count k (extendedColumn P d) :=
    congrAp2 (sumF (Foundations.BoundedReflection.sgB RationalSubtupleSpan.bitBody)) e (.eqRefl _)
  exact congrAp2 remF (congrAdd (.eqRefl _) counts) (.eqRefl two)

theorem odd_code (P d j : PTm n) (hr : Γ ⊢[PRAAx] lt (rank P d) d) (h : Γ ⊢[PRAAx] positionParity P d j ≐ one) :
    Γ ⊢[PRAAx] signedCode P d j ≐ integerPair (-(unsignedEntry P d j)) := by
  have different : Γ ⊢[PRAAx] neg (j ≐ free P d) :=
    .impI (succ_ne_zero (h.wk.eqSymm.eqTrans ((parity_congr P d Prf.hyp0).eqTrans (free_position_parity P d hr.wk))))
  have nonzero : Γ ⊢[PRAAx] neg (positionParity P d j ≐ zero) := .impI (succ_ne_zero (h.wk.eqSymm.eqTrans Prf.hyp0))
  exact (code_off_free P d j different).eqTrans (select_zero _ _ _ (eqb_of_ne nonzero))

theorem normalized_equals_representative (a : PTm n) (u v : ZT n) (ha : Γ ⊢[PRAAx] wellFormed a)
    (h : Γ ⊢[PRAAx] represents a v one) (e : Γ ⊢[PRAAx] ZT.eq u v) : Γ ⊢[PRAAx] normalize u one ≐ a := by
  refine RationalFiniteSum.canonical_equal _ a u v one one (normalize_well_formed _ _ (le_refl _)) ha
    (normalize_preserves_value _ _ (le_refl _)) h (le_refl _) (le_refl _) ?_
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_eq e]

theorem cofactor_denominator_one (P d j : PTm n) (hr : Γ ⊢[PRAAx] lt (rank P d) d) (hj : Γ ⊢[PRAAx] lt j d)
    (hs : Γ ⊢[PRAAx] bit (extendedColumn P d) j ≐ one) : Γ ⊢[PRAAx] denominatorOf (minorValue P d j) ≐ one :=
  (cofactor_minor_bound P d j (height P d) hr hj hs (height_positive P d) (input_height P d)).andE₁

theorem positive_value (P d j : PTm n) (hr : Γ ⊢[PRAAx] lt (rank P d) d) (hj : Γ ⊢[PRAAx] lt j d)
    (hs : Γ ⊢[PRAAx] bit (extendedColumn P d) j ≐ one) (h : Γ ⊢[PRAAx] positionParity P d j ≐ zero) :
    Γ ⊢[PRAAx] coefficientValue P d j ≐ minorValue P d j :=
  normalized_equals_representative _ _ _ (RationalScalarDeterminantGaussianEmbedding.determinant_well_formed _ _)
    (denominator_one_representation _ (cofactor_denominator_one P d j hr hj hs))
    (output_from_signed_code P d j hj hs _ (even_code P d j h))

theorem negative_value (P d j : PTm n) (hr : Γ ⊢[PRAAx] lt (rank P d) d) (hj : Γ ⊢[PRAAx] lt j d)
    (hs : Γ ⊢[PRAAx] bit (extendedColumn P d) j ≐ one) (h : Γ ⊢[PRAAx] positionParity P d j ≐ one) :
    Γ ⊢[PRAAx] coefficientValue P d j ≐ RationalArithmetic.negative (minorValue P d j) := by
  let a := minorValue P d j
  have qr : Γ ⊢[PRAAx] represents (RationalArithmetic.negative a) (-numeratorOf a) one :=
    scalar_congr (.eqRefl _) (ZT.derive rfl) (cofactor_denominator_one P d j hr hj hs) (RationalArithmetic.negative_value a)
  exact normalized_equals_representative _ _ _ (RationalArithmetic.negative_guard a) qr
    (output_from_signed_code P d j hj hs _ (odd_code P d j hr h))

theorem zero_value (P d j : PTm n) (hj : Γ ⊢[PRAAx] lt j d) (hz : Γ ⊢[PRAAx] bit (extendedColumn P d) j ≐ zero) :
    Γ ⊢[PRAAx] coefficientValue P d j ≐ scalarZero :=
  normalized_equals_representative _ _ _ (normalize_well_formed _ _ (le_refl _))
    (normalize_preserves_value (ZT.ofNat zero) one (le_refl _)) (vector_zero P d j hj hz)

theorem cofactor_embedded_at (P d r : PTm n) (hr : Γ ⊢[PRAAx] lt (rank P d) d)
    (hs : Γ ⊢[PRAAx] lt r (count d (extendedColumn P d))) : Γ ⊢[PRAAx]
    embed (coefficientValue P d (supportedColumn P d r)) ≐
      qmul (unitSign (free P d+r)) (embed (minorValue P d (supportedColumn P d r))) := by
  let j := supportedColumn P d r
  let k := free P d+r
  let a := minorValue P d j
  have selected := supported_label P d r hs
  have parity := support_position_parity P d r hs
  refine .orE (par_cases k) ?_ ?_
  · have value := positive_value P d j hr.wk selected.andE₁.wk selected.andE₂.andE₁.wk (parity.wk.eqTrans Prf.hyp0)
    have identity := (GaussianRationalPowerAlgebra.qmul_commutative (Γ := (par k ≐ zero) :: Γ) (embed a) _).eqSymm.eqTrans
      (GaussianReciprocalHorner.qmul_one_right (embed a) (embed_canonical a))
    exact (embed_congr value).eqTrans (identity.eqSymm.eqTrans (qmul_congr (sign_bit_even _ Prf.hyp0).eqSymm (.eqRefl _)))
  · have value := negative_value P d j hr.wk selected.andE₁.wk selected.andE₂.andE₁.wk (parity.wk.eqTrans Prf.hyp0)
    exact (embed_congr value).eqTrans ((embed_negative a).eqTrans
      ((GaussianRationalMatrixFiniteSums.negative_as_minusOne (embed a)).eqTrans
        (qmul_congr (sign_bit_odd _ Prf.hyp0).eqSymm (.eqRefl _))))

theorem actual_cofactor_coefficient_embedded_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (rank (var 0) (var 1)) (var 1) ⟶ lt (var 2) (count (var 1) (extendedColumn (var 0) (var 1))) ⟶
      embed (coefficientValue (var 0) (var 1) (supportedColumn (var 0) (var 1) (var 2))) ≐
        qmul (unitSign (free (var 0) (var 1)+var 2)) (embed (minorValue (var 0) (var 1) (supportedColumn (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.impI (.impI (cofactor_embedded_at _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_cofactor_off_support_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 1) ⟶ bit (extendedColumn (var 0) (var 1)) (var 2) ≐ zero ⟶
      embed (coefficientValue (var 0) (var 1) (var 2)) ≐ qzero) :=
  closeUniv 3 (.impI (.impI ((embed_congr (zero_value _ _ _ Prf.hyp1 Prf.hyp0)).eqTrans embed_zero)))

end LeanProofs.IPRA.Analysis.RationalCofactorCoefficientValues
