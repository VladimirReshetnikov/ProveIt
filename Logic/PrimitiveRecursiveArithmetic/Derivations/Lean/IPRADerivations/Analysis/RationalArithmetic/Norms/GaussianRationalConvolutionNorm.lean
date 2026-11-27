import IPRADerivations.Analysis.Polynomials.Coefficients.Norms.GaussianPolynomialNormBuffers
import IPRADerivations.Analysis.Polynomials.Products.GaussianRationalPolynomialProduct

/-!
# The coefficient L1 bound for the original convolution

The actual coefficient fold is compared with coefficientwise addition
of its delayed prefix and the next scaled row. The bound uses the same
stored polynomial product in every numerical degree.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalConvolutionNorm

open_ipra
open GaussianCoefficientL1 (normBody prefixNorm coefficientNorm prefix_succ)
open GaussianPolynomialNormBuffers (norm_entries zero_prefix norm_append norm_padding norm_scaled norm_added)
open GaussianRationalLinearProduct (norm_length scalar_zero_code)
open GaussianRationalPolynomialProduct
  (stage stage_length stage_lookup coefficient_zero coefficient_succ append_stage_lookup padded_scaled_lookup
    product)
open GaussianRationalPolynomialBuffers (appendZero append_length leftPad pad_length added added_length added_lookup)
open GaussianRationalCoefficientScaling (scaled scaled_length)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalSyntheticBounds (natCode add_monotone)
open GaussianRationalHorner (qzero)
open GaussianRationalL1 (qL1)
open GaussianRationalSumSegments (entriesEqual)
open RationalArithmetic (add multiply)
open RationalArgmin (rationalLE rationalLE_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem stage_entries_succ (P Q M t : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) :
    Γ ⊢[PRAAx] entriesEqual (stage P Q M (succ t))
      (added (appendZero (stage P Q M t)) (leftPad (scaled Q (entry P t)) t) (M + succ t)) (M + succ t) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift Q) ≐ succ (Syn.shift M) := by
    simpa [Fm.shift, Syn.shift] using hQ.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift M + succ (Syn.shift t)) :: Γ.map Fm.shift
  have range : Δ ⊢[PRAAx] lt (var 0) (Syn.shift M + succ (Syn.shift t)) := Prf.hyp0
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift M + Syn.shift t) :=
    (succ_monus_succ _ _).eqSymm.eqTrans
      (lt_congr (.eqRefl _) (by ipra_ring : Δ ⊢[PRAAx] Syn.shift M + succ (Syn.shift t) ≐ succ (Syn.shift M + Syn.shift t)) range)
  have e := (stage_lookup (Γ := Δ) (Syn.shift P) (Syn.shift Q) (Syn.shift M) (succ (Syn.shift t)) (var 0) range).eqTrans
    ((coefficient_succ _ _ _ _ _).eqTrans
      ((qadd_congr (append_stage_lookup _ _ _ _ _ hi).eqSymm
        (padded_scaled_lookup _ _ _ _ _ hs.wk range).eqSymm).eqTrans
          (added_lookup _ _ _ _ range).eqSymm))
  simpa only [Δ, Syn.shift, GaussianRationalPolynomialProduct.subst_stage,
    GaussianRationalPolynomialBuffers.subst_added, GaussianRationalPolynomialBuffers.subst_appendZero,
    GaussianRationalPolynomialBuffers.subst_leftPad, GaussianRationalCoefficientScaling.subst_scaled,
    Foundations.MasterCertificate.subst_entry, PTm.subst_add, ConciseIPRA.PTm.subst_succ] using e

theorem stage_norm_succ (P Q M t : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) :
    Γ ⊢[PRAAx] rationalLE (coefficientNorm (stage P Q M (succ t)))
      (add (coefficientNorm (stage P Q M t)) (multiply (qL1 (entry P t)) (coefficientNorm Q))) := by
  let L := M + succ t
  let A := appendZero (stage P Q M t)
  let B := leftPad (scaled Q (entry P t)) t
  have hA : Γ ⊢[PRAAx] length A ≐ L := (append_length _).eqTrans
    ((congrSucc (stage_length P Q M t)).eqTrans (by unfold L; ipra_ring))
  have hB : Γ ⊢[PRAAx] length B ≐ L := (pad_length _ _).eqTrans
    ((congrAdd (.eqRefl _) ((scaled_length _ _).eqTrans hQ)).eqTrans (by unfold L; ipra_ring))
  have eq := norm_entries (stage P Q M (succ t)) (added A B L) L
    (stage_length _ _ _ _) (added_length _ _ _) (stage_entries_succ P Q M t hQ)
  have sumBound := rationalLE_congr eq.eqSymm (RationalAlgebra.add_congr (norm_append _) (norm_padding _ _))
    (norm_added A B L hA hB)
  exact RationalArgmin.transitive sumBound (add_monotone _ _ _ _ (RationalArgmin.reflexive _)
    (norm_scaled Q (entry P t)))

theorem stage_norm_zero (P Q M : PTm n) :
    Γ ⊢[PRAAx] coefficientNorm (stage P Q M zero) ≐ natCode zero := by
  have ht : Γ ⊢[PRAAx] length (stage P Q M zero) ≐ M := (stage_length _ _ _ _).eqTrans (add_zero M)
  refine (norm_length _ _ ht).eqTrans (zero_prefix _ _ (.allI (.impI ?_)))
  let Δ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift
  have index : Δ ⊢[PRAAx] lt (var 0) (Syn.shift M + zero) := lt_congr
    (.eqRefl _) (add_zero (Syn.shift M)).eqSymm Prf.hyp0
  simpa only [Δ, Syn.shift, GaussianRationalPolynomialProduct.subst_stage, ConciseIPRA.PTm.subst_zero] using
    (stage_lookup (Γ := Δ) (Syn.shift P) (Syn.shift Q) (Syn.shift M) zero (var 0) index).eqTrans
      (coefficient_zero _ _ _ _)

def normLaw (P Q M t : PTm n) : Fm PTm n :=
  rationalLE (coefficientNorm (stage P Q M t)) (multiply (coefficientNorm Q) (prefixNorm P t))

ipra_subst normLaw

theorem norm_base (P Q M : PTm n) : Γ ⊢[PRAAx] normLaw P Q M zero := by
  have rhs : Γ ⊢[PRAAx] multiply (coefficientNorm Q) (prefixNorm P zero) ≐ natCode zero :=
    (RationalSumLinearity.sum_homogeneous normBody zero (coefficientNorm Q) P).eqSymm.eqTrans
      ((RationalFiniteSum.sum_zero _ _).eqTrans scalar_zero_code.eqSymm)
  exact rationalLE_congr (stage_norm_zero P Q M).eqSymm rhs.eqSymm (RationalArgmin.reflexive _)

theorem norm_step (P Q M t : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ M)
    (ih : Γ ⊢[PRAAx] normLaw P Q M t) : Γ ⊢[PRAAx] normLaw P Q M (succ t) := by
  have e := (RationalAlgebra.multiply_congr (.eqRefl (coefficientNorm Q)) (prefix_succ (Γ := Γ) P t)).eqTrans
    (RationalAlgebra.multiply_add _ _ _)
  have comparison := add_monotone (Γ := Γ) _ _ _ _ ih
    (rationalLE_congr (RationalAlgebra.multiply_commutative (qL1 (entry P t)) (coefficientNorm Q)).eqSymm
      (.eqRefl _) (RationalArgmin.reflexive _))
  exact RationalArgmin.transitive (stage_norm_succ P Q M t hQ)
    (rationalLE_congr (.eqRefl _) e.eqSymm comparison)

theorem stage_norm (P Q M t : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) :
    Γ ⊢[PRAAx] normLaw P Q M t := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift Q) ≐ succ (Syn.shift M) := by
    simpa [Fm.shift, Syn.shift] using hQ.shift
  have all : Γ ⊢[PRAAx] .all (normLaw (Syn.shift P) (Syn.shift Q) (Syn.shift M) (var 0)) := by
    ipra_qfind (le_QF _ _) [subst_normLaw]
    · exact norm_base _ _ _
    · exact norm_step _ _ _ _ hs.wk Prf.hyp0
  simpa only [subst_normLaw, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using all.allE t

theorem product_norm (P Q N M : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N) (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) :
    Γ ⊢[PRAAx] rationalLE (coefficientNorm (product P Q N M)) (multiply (coefficientNorm P) (coefficientNorm Q)) :=
  rationalLE_congr (.eqRefl _) ((RationalAlgebra.multiply_congr (.eqRefl _) (norm_length P _ hP).eqSymm).eqTrans
    (RationalAlgebra.multiply_commutative _ _)) (stage_norm P Q M (succ N) hQ)

theorem actual_convolution_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 2) ⟶ length (var 1) ≐ succ (var 3) ⟶
      rationalLE (coefficientNorm (product (var 0) (var 1) (var 2) (var 3)))
        (multiply (coefficientNorm (var 0)) (coefficientNorm (var 1)))) :=
  closeUniv 4 (.impI (.impI (product_norm _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalConvolutionNorm
