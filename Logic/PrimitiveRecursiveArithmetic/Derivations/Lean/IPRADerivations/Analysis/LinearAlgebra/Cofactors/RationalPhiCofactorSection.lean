import IPRADerivations.Analysis.LinearAlgebra.Cofactors.RationalBoundedCofactorAnnihilator
import IPRADerivations.Analysis.RationalArithmetic.GoldenRatio.RationalPhiSection

/-!
# The finite section bound via the bounded integer cofactors

The determinantal rank of the supplied spanning matrix gives the bounded
integer annihilator. Its original rational interpretation is the same for
every listed feature vector. The hyperplane bound then applies to the
original list of points and its original polynomial.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPhiCofactorSection

open_ipra
open RationalMaximalMinors (rank bestColumn)
open RationalMinorFreeColumn (free free_column_spec)
open RationalMinorAugmentation (extendedColumn)
open RationalCofactorSupport (free_position_parity)
open RationalCofactorMinorBounds (minorValue free_minor_nonzero)
open RationalCofactorCoefficientValues (positive_value)
open RationalBoundedCofactorAnnihilator (rationalVector subst_rationalVector rational_vector_lookup original_null_rows)
open RationalGaussianEmbedding (embed_equal scalarZero)
open RationalArgmin (rationalEq rationalEq_congr)
open RationalPhiFeatures (dimension equation features span_equation)
open RationalPhiSectionNonzero (curveInput lineEquations members member_at)
open RationalPhiSectionZero (nonzero)
open RationalCurvePointsGaussianEmbedding (distinct)
open RationalSuperellipticNormDegree (pointPowers)
open GaussianRationalFiberGrouping (abscissa ordinate)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem free_rational_coordinate (A d : PTm n) (hp : Γ ⊢[PRAAx] lt (rank A d) d) :
    Γ ⊢[PRAAx] entry (rationalVector A d) (free A d) ≐ minorValue A d (free A d) := by
  have hf := (free_column_spec A d hp).andE₁
  have hb := RationalMinorMaskExtension.new_bit d (bestColumn A d) (free A d) hf
  exact (rational_vector_lookup A d (free A d) hf).eqTrans
    (positive_value A d (free A d) hp hf hb (free_position_parity A d hp))

theorem free_rational_nonzero (A d : PTm n) (hp : Γ ⊢[PRAAx] lt (rank A d) d) :
    Γ ⊢[PRAAx] neg (rationalEq (entry (rationalVector A d) (free A d)) scalarZero) := by
  let a := minorValue A d (free A d)
  refine .impI (.impE (free_minor_nonzero A d).wk ?_)
  have e : rationalEq (entry (rationalVector A d) (free A d)) scalarZero :: Γ ⊢[PRAAx] rationalEq a scalarZero :=
    rationalEq_congr (free_rational_coordinate A d hp).wk (.eqRefl scalarZero) Prf.hyp0
  exact RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding a scalarZero
    (RationalScalarDeterminantGaussianEmbedding.determinant_well_formed _ _)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one)) (embed_equal a scalarZero e)

theorem cofactor_nonzero (A s : PTm n) (hp : Γ ⊢[PRAAx] lt (rank A (dimension s)) (dimension s)) :
    Γ ⊢[PRAAx] nonzero (rationalVector A (dimension s)) s := by
  let d := dimension s
  refine .exI (free A d) ?_
  simpa [nonzero,d] using Prf.andI (free_column_spec A d hp).andE₁ (free_rational_nonzero A d hp)

theorem cofactor_lines (A s L : PTm n) (hp : Γ ⊢[PRAAx] lt (rank A (dimension s)) (dimension s))
    (hm : Γ ⊢[PRAAx] members A (length A) s L) :
    Γ ⊢[PRAAx] lineEquations (rationalVector A (dimension s)) s L := by
  let A' := Syn.shift A
  let s' := Syn.shift s
  let L' := Syn.shift L
  let d' := dimension s'
  have hp' : Γ.map Fm.shift ⊢[PRAAx] lt (rank A' d') d' := by
    simpa only [A',s',d',Fm.shift,Syn.shift,subst_lt,RationalMaximalMinors.subst_rank,
      RationalPhiFeatures.subst_dimension] using hp.shift
  have hm' : Γ.map Fm.shift ⊢[PRAAx] members A' (length A') s' L' := by
    simpa only [A',s',L',Fm.shift,Syn.shift,subst_length,RationalPhiSectionNonzero.subst_members] using hm.shift
  refine .allI (.impI ?_)
  simpa only [A',s',L',d',Syn.shift,subst_rationalVector,RationalPhiFeatures.subst_dimension] using
    span_equation A' (length A') (rationalVector A' d') s' (abscissa L' (var 0)) (ordinate L' (var 0))
      (original_null_rows A' d' hp'.wk) (member_at A' (length A') s' L' (var 0) hm'.wk Prf.hyp0)

theorem determinantal_span_bound (A f s r m L : PTm n) (h : Γ ⊢[PRAAx] curveInput f s r m)
    (hp : Γ ⊢[PRAAx] lt (rank A (dimension s)) (dimension s)) (hd : Γ ⊢[PRAAx] distinct L)
    (hc : Γ ⊢[PRAAx] pointPowers f r L) (hm : Γ ⊢[PRAAx] members A (length A) s L) :
    Γ ⊢[PRAAx] le (length L) m :=
  RationalPhiSection.section_from_lines (rationalVector A (dimension s)) f s r m L h
    (cofactor_nonzero A s hp) hd (cofactor_lines A s L hp hm) hc

theorem actual_cofactor_span_lines_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (rank (var 0) (dimension (var 1))) (dimension (var 1)) ⟶ members (var 0) (length (var 0)) (var 1) (var 2) ⟶
      lineEquations (rationalVector (var 0) (dimension (var 1))) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (cofactor_lines _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_determinantal_span_section_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (curveInput (var 1) (var 2) (var 3) (var 4) ⟶ lt (rank (var 0) (dimension (var 2))) (dimension (var 2)) ⟶
      distinct (var 5) ⟶ pointPowers (var 1) (var 3) (var 5) ⟶ members (var 0) (length (var 0)) (var 2) (var 5) ⟶
      le (length (var 5)) (var 4)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI (determinantal_span_bound _ _ _ _ _ _
    (.hyp (by simp)) (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.RationalPhiCofactorSection
