import IPRADerivations.Analysis.Polynomials.Annihilators.RationalAnnihilatorPolynomial
import IPRADerivations.Analysis.RationalArithmetic.Spans.RationalOriginalAnnihilator
import IPRADerivations.Analysis.Polynomials.Elimination.Superelliptic.RationalSuperellipticSubspace
import IPRADerivations.Analysis.Polynomials.Elimination.Superelliptic.GaussianSuperellipticSubspaceFromSpan

/-!
# The actual rational annihilator polynomial vanishes on the original span

Preserve the original finite row dot products under scalar embedding.
The original existential row coefficients therefore give a zero of the
actual compiled rational polynomial at each original monomial vector.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalAnnihilatorOnSpan

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalOriginalAnnihilator (rowDot dotBody dot_body_at nullRows)
open RationalRowSpanGaussianEmbedding (matrix matrix_lookup hasCoefficients span_embedding)
open RationalPolynomialGaussianEmbedding (coefficients coefficient_lookup)
open RationalGaussianEmbedding (embed scalarZero)
open GaussianRationalRowElimination (dotData subst_dotData)
open GaussianWeightedMonomialBasis (count)
open RationalWeightedMonomialEvaluation (vector vector_embedding)
open RationalAnnihilatorPolynomial (polynomial evaluation_embedding)
open RationalCurvePointsGaussianEmbedding (functionZeros)
open GaussianRationalFiberGrouping (abscissa ordinate)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

@[simp] theorem subst_nullRows {q : ℕ} (σ : Fin n → PTm q) (A R N a : PTm n) :
    (nullRows A R N a).subst σ = nullRows (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ a) := by
  simp [nullRows,Syn.subst_shift,Syn.shift_subst]

theorem row_dot_embedding (A R N a r : PTm n) (hr : Γ ⊢[PRAAx] lt r R) : Γ ⊢[PRAAx]
    embed (rowDot A N a r) ≐ GaussianRationalRowElimination.rowDot (matrix A R N) N (coefficients a N) r := by
  refine (RationalGaussianRealPart.embed_sum dotBody N (dotData A a r)).eqTrans
    (GaussianRationalFiniteSum.sum_congr_bounded _ _ N _ _ ?_)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  let A' := Syn.shift A
  let R' := Syn.shift R
  let N' := Syn.shift N
  let a' := Syn.shift a
  let r' := Syn.shift r
  have hRow : Δ ⊢[PRAAx] lt r' R' := by simpa only [Δ,r',R',Fm.shift,subst_lt,Syn.shift] using hr.shift.wk
  have hCol : Δ ⊢[PRAAx] lt (var 0) N' := Prf.hyp0
  have left := (RationalPolynomialGaussianEmbedding.embed_congr (dot_body_at (Γ := Δ) A' a' r' (var 0))).eqTrans
    (RationalGaussianEmbedding.embed_multiply _ _)
  have right := (GaussianRationalRowElimination.dot_body_at (Γ := Δ) (matrix A' R' N') (coefficients a' N') r' (var 0)).eqTrans
    (GaussianRationalSyntheticDivision.qmul_congr (matrix_lookup _ _ _ _ _ hRow hCol) (coefficient_lookup _ _ _ hCol))
  simpa only [Δ,A',R',N',a',r',Syn.shift,subst_dotData,RationalRowSpanGaussianEmbedding.subst_matrix,
    RationalPolynomialGaussianEmbedding.subst_coefficients,RationalGaussianRealPart.embedBody,inst2,RationalGaussianEmbedding.subst_embed] using
    left.eqTrans ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans right.eqSymm)

theorem null_at (A R N a r : PTm n) (h : Γ ⊢[PRAAx] nullRows A R N a) (hr : Γ ⊢[PRAAx] lt r R) :
    Γ ⊢[PRAAx] rowDot A N a r ≐ scalarZero := by
  have rule : Γ ⊢[PRAAx] lt r R ⟶ rowDot A N a r ≐ scalarZero := by
    simpa [nullRows] using h.allE r
  exact .impE rule hr

theorem null_rows_embedding (A R N a : PTm n) (h : Γ ⊢[PRAAx] nullRows A R N a) : Γ ⊢[PRAAx]
    GaussianRationalRowElimination.nullRows (matrix A R N) R N (coefficients a N) := by
  have h' : Γ.map Fm.shift ⊢[PRAAx] nullRows (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift a) := by
    simpa only [Fm.shift,Syn.shift,subst_nullRows] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift R) :: Γ.map Fm.shift
  have hr : Δ ⊢[PRAAx] lt (var 0) (Syn.shift R) := Prf.hyp0
  have eq := null_at (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift a) (var 0) h'.wk hr
  simpa only [Δ,Syn.shift,RationalRowSpanGaussianEmbedding.subst_matrix,
    RationalPolynomialGaussianEmbedding.subst_coefficients,GaussianRationalRowElimination.subst_rowDot,
    GaussianRationalHorner.subst_qzero] using
    (row_dot_embedding (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift a) (var 0) hr).eqSymm.eqTrans
      ((RationalPolynomialGaussianEmbedding.embed_congr eq).eqTrans RationalGaussianEmbedding.embed_zero)

theorem polynomial_zero (A R a m e L x y : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hNull : Γ ⊢[PRAAx] nullRows A R (count m e L) a)
    (hSpan : Γ ⊢[PRAAx] hasCoefficients A R (count m e L) (vector m e L x y)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalEq (RationalBivariateGaussianEmbedding.bivariate (polynomial a m e L) m x y) scalarZero := by
  let N := count m e L
  let a' := coefficients a N
  let v := coefficients (vector m e L x y) N
  have bound := GaussianSuperellipticSubspaceFromSpan.span_dot_zero (matrix A R N) R N v a'
    (span_embedding A R N (vector m e L x y) hSpan) (null_rows_embedding A R N a hNull)
  have dot := GaussianRationalRowSpan.vector_dot_congr (Γ := Γ) (.eqRefl N) (vector_embedding m e L x y).eqSymm (.eqRefl a')
  exact (RationalGaussianEmbedding.zero_iff _).iffMp
    ((evaluation_embedding a m e L x y).eqTrans
      ((GaussianAnnihilatorPolynomialEvaluation.evaluation_equals_dot a' m e L (embed x) (embed y) hm).eqTrans
        (dot.eqTrans bound)))

theorem polynomial_zeros (A R a m e L P : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hNull : Γ ⊢[PRAAx] nullRows A R (count m e L) a)
    (hSpan : Γ ⊢[PRAAx] RationalSuperellipticSubspace.pointMembership m e L P A R) :
    Γ ⊢[PRAAx] functionZeros (polynomial a m e L) m P := by
  have hm' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
    simpa [Fm.shift,Syn.shift] using hm.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] nullRows (Syn.shift A) (Syn.shift R) (count (Syn.shift m) (Syn.shift e) (Syn.shift L)) (Syn.shift a) := by
    simpa [Fm.shift,Syn.shift] using hNull.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] RationalSuperellipticSubspace.pointMembership
      (Syn.shift m) (Syn.shift e) (Syn.shift L) (Syn.shift P) (Syn.shift A) (Syn.shift R) := by
    simpa [Fm.shift,Syn.shift] using hSpan.shift
  refine .allI (.impI ?_)
  have here := RationalSuperellipticSubspace.membership_at (Syn.shift m) (Syn.shift e) (Syn.shift L) (Syn.shift P)
    (Syn.shift A) (Syn.shift R) (var 0) hs.wk Prf.hyp0
  simpa [Syn.shift] using polynomial_zero (Syn.shift A) (Syn.shift R) (Syn.shift a) (Syn.shift m) (Syn.shift e)
    (Syn.shift L) (abscissa (Syn.shift P) (var 0)) (ordinate (Syn.shift P) (var 0)) hm'.wk hn.wk here

theorem computed_polynomial_zeros (A R m e L P : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hDeficit : Γ ⊢[PRAAx] RationalOriginalAnnihilator.deficit A R (count m e L))
    (hSpan : Γ ⊢[PRAAx] RationalSuperellipticSubspace.pointMembership m e L P A R) : Γ ⊢[PRAAx]
    functionZeros (polynomial (RationalOriginalAnnihilator.vector A R (count m e L)) m e L) m P :=
  polynomial_zeros A R _ m e L P hm (.andE₂ (.andE₂ (.andE₂ (RationalOriginalAnnihilator.certificate_of_deficit _ _ _ hDeficit)))) hSpan

theorem actual_rational_annihilator_span_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (le one (var 3) ⟶ nullRows (var 0) (var 1) (count (var 3) (var 4) (var 5)) (var 2) ⟶
      hasCoefficients (var 0) (var 1) (count (var 3) (var 4) (var 5)) (vector (var 3) (var 4) (var 5) (var 6) (var 7)) ⟶
      RationalArgmin.rationalEq (RationalBivariateGaussianEmbedding.bivariate (polynomial (var 2) (var 3) (var 4) (var 5))
        (var 3) (var 6) (var 7)) scalarZero) :=
  closeUniv 8 (.impI (.impI (.impI (polynomial_zero _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_computed_rational_annihilator_zeros_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 2) ⟶ RationalOriginalAnnihilator.deficit (var 0) (var 1) (count (var 2) (var 3) (var 4)) ⟶
      RationalSuperellipticSubspace.pointMembership (var 2) (var 3) (var 4) (var 5) (var 0) (var 1) ⟶
      functionZeros (polynomial (RationalOriginalAnnihilator.vector (var 0) (var 1) (count (var 2) (var 3) (var 4)))
        (var 2) (var 3) (var 4)) (var 2) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (computed_polynomial_zeros _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalAnnihilatorOnSpan
