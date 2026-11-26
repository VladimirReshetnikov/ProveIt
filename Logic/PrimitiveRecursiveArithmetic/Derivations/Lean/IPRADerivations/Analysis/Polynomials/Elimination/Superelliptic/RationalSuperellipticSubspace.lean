import IPRADerivations.Analysis.Polynomials.Elimination.Superelliptic.RationalSuperellipticNormDegree
import IPRADerivations.Analysis.Inequalities.RationalWeightedMonomialEvaluation
import IPRADerivations.Analysis.RationalArithmetic.Spans.GaussianRationalOriginalSpanRank

/-!
# Original rational proper spans on the superelliptic curve

A numerical rational vector outside the original row span stays outside
after embedding. Any Gaussian representation of that vector would give
an original rational representation by taking its real coefficients.
The original point memberships use their actual rational evaluation vectors.
The embedded distinct curve points then satisfy the finite subspace bound.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalSuperellipticSubspace

open_ipra
open RationalRowSpanGaussianEmbedding (matrix matrix_shape hasCoefficients span_real_part)
open RationalPolynomialGaussianEmbedding (coefficients coefficients_length coefficientBody embed_congr)
open RationalSuperellipticNormDegree (d f_degree_embedding)
open GaussianWeightedMonomialBasis (count)
open RationalWeightedMonomialEvaluation (vector)
open RationalGaussianEmbedding (embed scalarZero scalarOne)
open RationalCurvePointsGaussianEmbedding (points points_length abscissa_at ordinate_at)
open GaussianRationalFiberGrouping (abscissa ordinate)
open GaussianRationalRankNullityCriterion (rank)
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence sequence_decode sequence_length)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.SequenceEquality (sequence_equal)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def properSpan (A R N : PTm n) : Fm PTm n := .ex
  ((length (var 0) ≐ Syn.shift N) ⋏ neg (hasCoefficients (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0)))

ipra_subst properSpan [Syn.subst_shift, Syn.shift_subst]

private theorem gaussian_proper_intro (A R N v : PTm n) (hv : Γ ⊢[PRAAx] length v ≐ N)
    (h : Γ ⊢[PRAAx] neg (GaussianSuperellipticSubspaceFromSpan.hasCoefficients A R N v)) :
    Γ ⊢[PRAAx] GaussianRationalOriginalSpanRank.properSpan A R N := by
  refine .exI v ?_
  simpa only [GaussianRationalOriginalSpanRank.properSpan,Fm.subst_and,Fm.subst_eq,subst_neg,
    Foundations.SequenceComposition.subst_length,GaussianSuperellipticSubspaceFromSpan.subst_hasCoefficients,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.andI hv h

theorem proper_embedding (A R N : PTm n) (h : Γ ⊢[PRAAx] properSpan A R N) :
    Γ ⊢[PRAAx] GaussianRationalOriginalSpanRank.properSpan (matrix A R N) R N := by
  refine .exE h ?_
  let A' := Syn.shift A
  let R' := Syn.shift R
  let N' := Syn.shift N
  let v : PTm (n + 1) := var 0
  let Δ := ((length v ≐ N') ⋏ neg (hasCoefficients A' R' N' v)) :: Γ.map Fm.shift
  have noWeights : Δ ⊢[PRAAx] neg (hasCoefficients A' R' N' v) := .andE₂ Prf.hyp0
  have noGaussian : Δ ⊢[PRAAx] neg (GaussianSuperellipticSubspaceFromSpan.hasCoefficients
      (matrix A' R' N') R' N' (coefficients v N')) :=
    .impI (.impE noWeights.wk (span_real_part A' R' N' v Prf.hyp0))
  have result := gaussian_proper_intro _ _ _ _ (coefficients_length v N') noGaussian
  simpa only [Δ,A',R',N',v,Fm.shift,Syn.shift,RationalRowSpanGaussianEmbedding.subst_matrix,
    GaussianRationalOriginalSpanRank.subst_properSpan,properSpan] using result

theorem rank_deficit (A R N : PTm n) (h : Γ ⊢[PRAAx] properSpan A R N) :
    Γ ⊢[PRAAx] lt (rank (matrix A R N) R N) N :=
  GaussianRationalOriginalSpanRank.proper_implies_deficit _ _ _ (matrix_shape A R N) (proper_embedding A R N h)

def unitBody : PTm 2 := RationalArithmetic.select (eqb (var 1) (var 0)) scalarZero scalarOne
def unit (N s : PTm n) : PTm n := sequence unitBody N s

private theorem embed_delta (s j : PTm n) : Γ ⊢[PRAAx]
    embed (inst2 unitBody j s) ≐ inst2 GaussianRationalProperSpanWitness.unitBody j s := by
  simp only [unitBody,inst2,RationalArithmetic.subst_select,subst_eqb,RationalGaussianEmbedding.subst_scalarZero,
    RationalGaussianEmbedding.subst_scalarOne,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    GaussianRationalProperSpanWitness.unitBody,GaussianRationalFiberVandermonde.subst_delta]
  refine .orE (eq_or_ne s j) ?_ ?_
  · exact (embed_congr (RationalArithmetic.select_one _ _ _ (eqb_of_eq Prf.hyp0))).eqTrans
      (RationalGaussianEmbedding.embed_one.eqTrans (GaussianRationalLagrangeCardinals.delta_equal s j Prf.hyp0).eqSymm)
  · exact (embed_congr (RationalArithmetic.select_zero _ _ _ (eqb_of_ne Prf.hyp0))).eqTrans
      (RationalGaussianEmbedding.embed_zero.eqTrans (GaussianRationalLagrangeCardinals.delta_unequal s j Prf.hyp0).eqSymm)

theorem unit_embedding (N s : PTm n) : Γ ⊢[PRAAx]
    coefficients (unit N s) N ≐ GaussianRationalProperSpanWitness.unit N s := by
  apply sequence_equal coefficientBody GaussianRationalProperSpanWitness.unitBody N (unit N s) s
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have hr : Δ ⊢[PRAAx] lt (var 0) (Syn.shift N) := Prf.hyp0
  have h : Δ ⊢[PRAAx] embed (inst2 unitBody (var 0) (Syn.shift s)) ≐
      inst2 GaussianRationalProperSpanWitness.unitBody (var 0) (Syn.shift s) := embed_delta _ _
  have entry := sequence_decode unitBody (x := Syn.shift s) hr
  simpa only [Δ,unit,Foundations.MasterCertificate.subst_sequence,Syn.shift,coefficientBody,inst2,
    RationalGaussianEmbedding.subst_embed,Foundations.MasterCertificate.subst_entry,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one] using (embed_congr entry).eqTrans h

private theorem span_value_congr (A R N v w : PTm n) (hw : Γ ⊢[PRAAx] v ≐ w)
    (h : Γ ⊢[PRAAx] GaussianSuperellipticSubspaceFromSpan.hasCoefficients A R N v) :
    Γ ⊢[PRAAx] GaussianSuperellipticSubspaceFromSpan.hasCoefficients A R N w := by
  let φ := GaussianSuperellipticSubspaceFromSpan.hasCoefficients (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0)
  have start : Γ ⊢[PRAAx] φ.subst (Syn.inst v) := by
    simpa only [φ,GaussianSuperellipticSubspaceFromSpan.subst_hasCoefficients,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h
  simpa only [φ,GaussianSuperellipticSubspaceFromSpan.subst_hasCoefficients,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqSubst1 φ hw start

theorem proper_of_deficit (A R N : PTm n) (h : Γ ⊢[PRAAx] lt (rank (matrix A R N) R N) N) :
    Γ ⊢[PRAAx] properSpan A R N := by
  let M := matrix A R N
  let s := GaussianRationalAnnihilatorVector.freeColumn M R N
  let v := unit N s
  have eq := unit_embedding (Γ := Γ) N s
  have noGaussian := GaussianRationalOriginalSpanRank.free_witness_missing M R N (matrix_shape A R N) h
  have absent : Γ ⊢[PRAAx] neg (hasCoefficients A R N v) := by
    refine .impI (.impE noGaussian.wk ?_)
    exact span_value_congr M R N _ _ eq.wk (RationalRowSpanGaussianEmbedding.span_embedding A R N v Prf.hyp0)
  have hv : Γ ⊢[PRAAx] length v ≐ N := sequence_length unitBody N s
  refine .exI v ?_
  simpa only [properSpan,Fm.subst_and,Fm.subst_eq,subst_neg,
    Foundations.SequenceComposition.subst_length,RationalRowSpanGaussianEmbedding.subst_hasCoefficients,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.andI hv absent

theorem proper_iff_deficit (A R N : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (properSpan A R N) (lt (rank (matrix A R N) R N) N) :=
  .andI (.impI (rank_deficit _ _ _ Prf.hyp0)) (.impI (proper_of_deficit _ _ _ Prf.hyp0))

def curveInput (f m c : PTm n) : Fm PTm n := le (succ one) m ⋏ (le one (d f c) ⋏
  (gcd m (d f c) ≐ one ⋏ ((length f ≐ succ c) ⋏ RationalPolynomialNonvanishing.nonzeroCoefficients f c)))

theorem curve_input_embedding (f m c : PTm n) (h : Γ ⊢[PRAAx] curveInput f m c) :
    Γ ⊢[PRAAx] GaussianSuperellipticSubspaceWitness.curveInput (coefficients f (succ c)) m c := by
  have hd := f_degree_embedding (Γ := Γ) f c
  have fnz := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  have flag := (RationalPolynomialDegreeGaussianEmbedding.flag_conjugacy f (coefficients f (succ c)) c
    (RationalPolynomialLeadingGaussianEmbedding.coefficient_list_embedding f (succ c))).eqSymm.eqTrans
      (RationalPolynomialNonvanishing.flag_of_nonzero f c fnz)
  exact .andI (.andE₁ h) (.andI (le_congr (.eqRefl _) hd (.andE₁ (.andE₂ h)))
    (.andI ((Foundations.PrimitiveScaling.gcd_congr' (.eqRefl m) hd).eqSymm.eqTrans (.andE₁ (.andE₂ (.andE₂ h))))
      (.andI (coefficients_length f (succ c)) (GaussianRationalPolynomialDegree.nonzero_of_flag_one _ _ flag))))

theorem mapped_power_at (f m c P i : PTm n) (hf : Γ ⊢[PRAAx] length f ≐ succ c)
    (hp : Γ ⊢[PRAAx] RationalSuperellipticNormDegree.pointPowers f m P) (hi : Γ ⊢[PRAAx] lt i (length P)) :
    Γ ⊢[PRAAx] GaussianRationalReciprocal.power (ordinate (points P) i) m ≐
      GaussianRationalHorner.evaluate (coefficients f (succ c)) (abscissa (points P) i) := by
  let f' := coefficients f (succ c)
  let x := abscissa P i
  let y := ordinate P i
  have power := (RationalScalarPowerGaussianEmbedding.power_equality (Γ := Γ) y m
    (RationalPolynomialGaussianEmbedding.evaluate f x)).iffMp
      (RationalSuperellipticNormDegree.point_power_at f m P i hp hi)
  have evaluate := RationalPolynomialBuffersGaussianEmbedding.evaluation_transport f f' (succ c) x hf
    (coefficients_length f (succ c)) (RationalPolynomialLeadingGaussianEmbedding.coefficient_list_embedding f (succ c))
  exact (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl m) (ordinate_at P i hi)).eqTrans
    (power.eqTrans (evaluate.eqTrans (GaussianRationalMonicReduction.evaluate_congr (.eqRefl f') (abscissa_at P i hi).eqSymm)))

theorem mapped_point_powers (f m c P : PTm n) (hf : Γ ⊢[PRAAx] length f ≐ succ c)
    (hp : Γ ⊢[PRAAx] RationalSuperellipticNormDegree.pointPowers f m P) :
    Γ ⊢[PRAAx] GaussianSuperellipticNormDegree.pointPowers (coefficients f (succ c)) m (points P) := by
  refine .allI (.impI ?_)
  have hf' : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift f) ≐ succ (Syn.shift c) := by
    simpa [Fm.shift,Syn.shift] using hf.shift
  have hp' : Γ.map Fm.shift ⊢[PRAAx]
      RationalSuperellipticNormDegree.pointPowers (Syn.shift f) (Syn.shift m) (Syn.shift P) := by
    simpa [Fm.shift,Syn.shift] using hp.shift
  have hmoved : lt (var 0) (length (Syn.shift (points P))) :: Γ.map Fm.shift ⊢[PRAAx]
      lt (var 0) (length (points (Syn.shift P))) := by
    simpa only [Syn.shift,RationalCurvePointsGaussianEmbedding.subst_points] using Prf.hyp0
  have hi := lt_congr (.eqRefl (var 0)) (points_length (Syn.shift P)) hmoved
  simpa [Syn.shift] using mapped_power_at (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift P) (var 0) hf'.wk hp'.wk hi

def pointMembership (m e L P A R : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift P)) ⟶
    hasCoefficients (Syn.shift A) (Syn.shift R) (count (Syn.shift m) (Syn.shift e) (Syn.shift L))
      (vector (Syn.shift m) (Syn.shift e) (Syn.shift L) (abscissa (Syn.shift P) (var 0)) (ordinate (Syn.shift P) (var 0))))

ipra_subst pointMembership [Syn.subst_shift, Syn.shift_subst]

theorem membership_at (m e L P A R i : PTm n) (h : Γ ⊢[PRAAx] pointMembership m e L P A R)
    (hi : Γ ⊢[PRAAx] lt i (length P)) : Γ ⊢[PRAAx] hasCoefficients A R (count m e L)
      (vector m e L (abscissa P i) (ordinate P i)) := by
  have rule : Γ ⊢[PRAAx] lt i (length P) ⟶ hasCoefficients A R (count m e L)
      (vector m e L (abscissa P i) (ordinate P i)) := by simpa [pointMembership] using h.allE i
  exact .impE rule hi

private theorem degree_membership_congr (m L P A R e e' : PTm n) (hd : Γ ⊢[PRAAx] e ≐ e')
    (h : Γ ⊢[PRAAx] pointMembership m e L P A R) : Γ ⊢[PRAAx] pointMembership m e' L P A R := by
  let φ := pointMembership (Syn.shift m) (var 0) (Syn.shift L) (Syn.shift P) (Syn.shift A) (Syn.shift R)
  have start : Γ ⊢[PRAAx] φ.subst (Syn.inst e) := by
    simpa only [φ,subst_pointMembership,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h
  simpa only [φ,subst_pointMembership,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.eqSubst1 φ hd start

private theorem proper_columns_congr (m L A R e e' : PTm n) (hd : Γ ⊢[PRAAx] e ≐ e')
    (h : Γ ⊢[PRAAx] properSpan A R (count m e L)) : Γ ⊢[PRAAx] properSpan A R (count m e' L) := by
  let φ := properSpan (Syn.shift A) (Syn.shift R) (count (Syn.shift m) (var 0) (Syn.shift L))
  have start : Γ ⊢[PRAAx] φ.subst (Syn.inst e) := by
    simpa only [φ,subst_properSpan,GaussianWeightedMonomialBasis.subst_count,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h
  simpa only [φ,subst_properSpan,GaussianWeightedMonomialBasis.subst_count,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqSubst1 φ hd start

private theorem evaluation_congr (m e L x y x' y' : PTm n) (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y') :
    Γ ⊢[PRAAx] GaussianWeightedMonomialBasis.evaluationVector m e L x y ≐
      GaussianWeightedMonomialBasis.evaluationVector m e L x' y' := by
  ipra_congr (GaussianWeightedMonomialBasis.evaluationVector (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with
    [.eqRefl m, .eqRefl e, .eqRefl L, hx, hy]

theorem mapped_membership_at (m e L P A R i : PTm n) (h : Γ ⊢[PRAAx] pointMembership m e L P A R)
    (hi : Γ ⊢[PRAAx] lt i (length P)) : Γ ⊢[PRAAx]
    GaussianSuperellipticSubspaceFromSpan.hasCoefficients (matrix A R (count m e L)) R (count m e L)
      (GaussianSuperellipticSubspaceFromSpan.pointVector m e L (points P) i) := by
  let N := count m e L
  let x := abscissa P i
  let y := ordinate P i
  have hSpan := RationalRowSpanGaussianEmbedding.span_embedding A R N (vector m e L x y) (membership_at _ _ _ _ _ _ _ h hi)
  have eq := (RationalWeightedMonomialEvaluation.vector_embedding (Γ := Γ) m e L x y).eqTrans
    (evaluation_congr m e L (embed x) (embed y) (abscissa (points P) i) (ordinate (points P) i)
      (abscissa_at P i hi).eqSymm (ordinate_at P i hi).eqSymm)
  exact span_value_congr _ _ _ _ _ eq hSpan

theorem mapped_membership (f m c L P A R : PTm n)
    (h : Γ ⊢[PRAAx] pointMembership m (GaussianRationalPolynomialDegree.degree f c) L P A R) : Γ ⊢[PRAAx]
    GaussianSuperellipticSubspaceFromSpan.pointMembership f m c L (points P)
      (matrix A R (GaussianSuperellipticSubspaceWitness.basisCount f m c L)) R := by
  let e := GaussianRationalPolynomialDegree.degree f c
  refine .allI (.impI ?_)
  have h' : Γ.map Fm.shift ⊢[PRAAx]
      pointMembership (Syn.shift m) (Syn.shift e) (Syn.shift L) (Syn.shift P) (Syn.shift A) (Syn.shift R) := by
    simpa [e,Fm.shift,Syn.shift] using h.shift
  have hmoved : lt (var 0) (length (Syn.shift (points P))) :: Γ.map Fm.shift ⊢[PRAAx]
      lt (var 0) (length (points (Syn.shift P))) := by
    simpa only [Syn.shift,RationalCurvePointsGaussianEmbedding.subst_points] using Prf.hyp0
  have hi := lt_congr (.eqRefl (var 0)) (points_length (Syn.shift P)) hmoved
  simpa [e,GaussianSuperellipticSubspaceWitness.basisCount,Syn.shift] using
    mapped_membership_at (Syn.shift m) (Syn.shift e) (Syn.shift L) (Syn.shift P) (Syn.shift A) (Syn.shift R) (var 0) h'.wk hi

def curvePoints (f m P : PTm n) : Fm PTm n := RationalCurvePointsGaussianEmbedding.distinct P ⋏
  RationalSuperellipticNormDegree.pointPowers f m P

theorem point_bound (f m c L P A R : PTm n) (hf : Γ ⊢[PRAAx] curveInput f m c)
    (hProper : Γ ⊢[PRAAx] properSpan A R (count m (d f c) L))
    (hPts : Γ ⊢[PRAAx] curvePoints f m P) (hSpan : Γ ⊢[PRAAx] pointMembership m (d f c) L P A R) :
    Γ ⊢[PRAAx] le (length P) L := by
  let f' := coefficients f (succ c)
  let N := GaussianSuperellipticSubspaceWitness.basisCount f' m c L
  have hd := f_degree_embedding (Γ := Γ) f c
  have hfLength := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hf)))
  have proper := proper_columns_congr m L A R _ _ hd hProper
  have members := degree_membership_congr m L P A R _ _ hd hSpan
  have points' : Γ ⊢[PRAAx] GaussianSuperellipticSubspaceWitness.points f' m (points P) :=
    .andI (RationalCurvePointsGaussianEmbedding.mapped_distinct P (.andE₁ hPts))
      (mapped_point_powers f m c P hfLength (.andE₂ hPts))
  have bound := GaussianRationalOriginalSpanRank.proper_subspace_bound f' m c L (points P) (matrix A R N) R
    (curve_input_embedding _ _ _ hf) (matrix_shape A R N) (proper_embedding A R N proper) points'
    (mapped_membership f' m c L P A R members)
  exact le_congr (points_length P) (.eqRefl L) bound

theorem actual_rational_proper_span_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (properSpan (var 0) (var 1) (var 2) ⟶
      GaussianRationalOriginalSpanRank.properSpan (matrix (var 0) (var 1) (var 2)) (var 1) (var 2)) :=
  closeUniv 3 (.impI (proper_embedding _ _ _ Prf.hyp0))

theorem actual_rational_proper_span_rank_deficit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (Fm.iff (properSpan (var 0) (var 1) (var 2)) (lt (rank (matrix (var 0) (var 1) (var 2)) (var 1) (var 2)) (var 2))) :=
  closeUniv 3 (proper_iff_deficit _ _ _)

theorem actual_rational_proper_subspace_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (curveInput (var 0) (var 1) (var 2) ⟶
      properSpan (var 5) (var 6) (count (var 1) (d (var 0) (var 2)) (var 3)) ⟶
      curvePoints (var 0) (var 1) (var 4) ⟶
      pointMembership (var 1) (d (var 0) (var 2)) (var 3) (var 4) (var 5) (var 6) ⟶
      le (length (var 4)) (var 3)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (point_bound _ _ _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

theorem actual_rational_rank_deficit_point_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (curveInput (var 0) (var 1) (var 2) ⟶
      lt (rank (matrix (var 5) (var 6) (count (var 1) (d (var 0) (var 2)) (var 3))) (var 6)
        (count (var 1) (d (var 0) (var 2)) (var 3))) (count (var 1) (d (var 0) (var 2)) (var 3)) ⟶
      curvePoints (var 0) (var 1) (var 4) ⟶
      pointMembership (var 1) (d (var 0) (var 2)) (var 3) (var 4) (var 5) (var 6) ⟶
      le (length (var 4)) (var 3)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI
    (point_bound _ _ _ _ _ _ _ Prf.hyp1.wk.wk (proper_of_deficit _ _ _ Prf.hyp1.wk) Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.RationalSuperellipticSubspace
