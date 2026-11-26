import IPRADerivations.Analysis.RationalArithmetic.GoldenRatio.RationalPhiFeatures
import IPRADerivations.Analysis.RationalArithmetic.Fibers.RationalCurvePointsGaussianEmbedding
import IPRADerivations.Foundations.FiniteCoverAssignment

/-!
# The zero-ordinate-coefficient branch of the original Phi_s section

The original nonzero annihilator with zero last coefficient produces a
nonzero degree-at-most-s polynomial in x. Distinct abscissa groups are
roots of that actual polynomial, while each ordinate fiber consists of
roots of the actual monic polynomial Y^r-f(x). Their genuine cardinal
partition yields at most r*s original points. No coprimality is needed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPhiSectionZero

open_ipra
open RationalPhiFeatures (dimension polynomial polynomial_length equation features)
open RationalGaussianEmbedding (embed scalarZero)
open RationalPolynomialGaussianEmbedding (coefficients coefficient_lookup embed_congr)
open GaussianRationalHorner (qzero qmul qadd)
open GaussianRationalFiberGrouping (abscissa ordinate groupCount representative fiberCount partitionTotal xKeyF)
open GaussianRationalCurveFibers (pointDistinct curveZeros)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def nonzero (a s : PTm n) : Fm PTm n := .ex (lt (var 0) (dimension (Syn.shift s)) ⋏
  neg (RationalArgmin.rationalEq (entry (Syn.shift a) (var 0)) scalarZero))
def equations (a s P : PTm n) : Fm PTm n := .all (lt (var 0) (length (Syn.shift P)) ⟶
  equation (Syn.shift a) (Syn.shift s) (abscissa (Syn.shift P) (var 0)) (ordinate (Syn.shift P) (var 0)) ≐ scalarZero)
def embeddedPolynomial (a s : PTm n) : PTm n := coefficients (polynomial a s) (succ s)
ipra_subst nonzero [Syn.subst_shift, Syn.shift_subst]
ipra_subst equations [Syn.subst_shift, Syn.shift_subst]
ipra_subst embeddedPolynomial

theorem equation_at (a s P i : PTm n) (h : Γ ⊢[PRAAx] equations a s P) (hi : Γ ⊢[PRAAx] lt i (length P)) : Γ ⊢[PRAAx]
    equation a s (abscissa P i) (ordinate P i) ≐ scalarZero := by
  have rule : Γ ⊢[PRAAx] lt i (length P) ⟶ equation a s (abscissa P i) (ordinate P i) ≐ scalarZero := by simpa [equations] using h.allE i
  exact .impE rule hi

theorem zero_equation_root (a s x y : PTm n) (ha : Γ ⊢[PRAAx] RationalArgmin.rationalEq (entry a (succ s)) scalarZero)
    (he : Γ ⊢[PRAAx] equation a s x y ≐ scalarZero) : Γ ⊢[PRAAx]
    GaussianRationalHorner.evaluate (embeddedPolynomial a s) (embed x) ≐ qzero := by
  have zeroA := (RationalGaussianEmbedding.zero_iff _).iffMpr ha
  have tail := (GaussianRationalSyntheticDivision.qmul_congr zeroA (.eqRefl (embed y))).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_left _)
  have expanded : Γ ⊢[PRAAx] embed (equation a s x y) ≐ embed (RationalPolynomialGaussianEmbedding.evaluate (polynomial a s) x) :=
    (RationalGaussianEmbedding.embed_add _ _).eqTrans
      ((GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) ((RationalGaussianEmbedding.embed_multiply _ _).eqTrans tail)).eqTrans
        (GaussianReciprocalHorner.qadd_zero_right _ (RationalGaussianEmbedding.embed_canonical _)))
  exact (RationalPolynomialBuffersGaussianEmbedding.evaluation_at_width (polynomial a s) (succ s) x (polynomial_length a s)).eqSymm.eqTrans
    (expanded.eqSymm.eqTrans ((embed_congr he).eqTrans RationalGaussianEmbedding.embed_zero))

theorem polynomial_nonzero (a s : PTm n) (hn : Γ ⊢[PRAAx] nonzero a s)
    (ha : Γ ⊢[PRAAx] RationalArgmin.rationalEq (entry a (succ s)) scalarZero) : Γ ⊢[PRAAx]
    GaussianRationalPolynomialDegree.nonzeroCoefficients (embeddedPolynomial a s) s := by
  have has : Γ.map Fm.shift ⊢[PRAAx] RationalArgmin.rationalEq (entry (Syn.shift a) (succ (Syn.shift s))) scalarZero := by
    simpa [Fm.shift,Syn.shift] using ha.shift
  refine .exE hn ?_
  let Δ := (lt (var 0) (dimension (Syn.shift s)) ⋏ neg (RationalArgmin.rationalEq (entry (Syn.shift a) (var 0)) scalarZero)) :: Γ.map Fm.shift
  suffices result : Δ ⊢[PRAAx] GaussianRationalPolynomialDegree.nonzeroCoefficients (embeddedPolynomial (Syn.shift a) (Syn.shift s)) (Syn.shift s) by
    simpa [Δ,Fm.shift,Syn.shift] using result
  have hi : Δ ⊢[PRAAx] le (var 0) (succ (Syn.shift s)) := (succ_monus_succ _ _).eqSymm.eqTrans (.andE₁ Prf.hyp0)
  refine .orE (lt_or_eq_of_le hi) ?_ ?_
  · let Ξ := lt (var 0) (succ (Syn.shift s)) :: Δ
    have hle : Ξ ⊢[PRAAx] le (var 0) (Syn.shift s) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    have hk : Ξ ⊢[PRAAx] lt (monus (Syn.shift s) (var 0)) (succ (Syn.shift s)) :=
      (succ_monus_succ _ _).eqTrans (GaussianRationalMonicReconstruction.monus_le_left _ _)
    have hit := (coefficient_lookup (Γ := Ξ) (polynomial (Syn.shift a) (Syn.shift s)) (succ (Syn.shift s)) _ hk).eqTrans
      ((embed_congr (RationalPhiFeatures.polynomial_ascending _ _ _ hle)).eqTrans (RationalGaussianEmbedding.embed_recode _))
    have recoded := (GaussianTranslatedNonconstant.recode_congr hit).eqTrans
      (GaussianTranslatedNonconstant.recode_eq _ (RationalGaussianEmbedding.embed_canonical _))
    have nz : Ξ ⊢[PRAAx] neg (GaussianTranslatedNonconstant.recode (entry (embeddedPolynomial (Syn.shift a) (Syn.shift s)) (monus (Syn.shift s) (var 0))) ≐ qzero) := by
      refine .impI (.impE (.andE₂ (Prf.hyp1.wk : _ ⊢[PRAAx] _)) ?_)
      exact (RationalGaussianEmbedding.zero_iff _).iffMp (recoded.wk.eqSymm.eqTrans Prf.hyp0)
    refine .exI (monus (Syn.shift s) (var 0)) ?_
    simpa [GaussianRationalPolynomialDegree.nonzeroCoefficients] using Prf.andI hk nz
  · have eq : (var 0 ≐ succ (Syn.shift s)) :: Δ ⊢[PRAAx] RationalArgmin.rationalEq (entry (Syn.shift a) (var 0)) scalarZero :=
      RationalArgmin.rationalEq_congr (entry_congr (.eqRefl _) Prf.hyp0).eqSymm (.eqRefl _) has.wk.wk
    exact .botE _ (.impE (.andE₂ Prf.hyp1) eq)

/-- Actual distinct abscissae of the original first-occurrence groups. -/
def xBody : PTm 2 := abscissa (var 1) (representative (var 1) zero (var 0))
def xList (L : PTm n) : PTm n := sequence xBody (groupCount L zero) L
def xRoots (C L : PTm n) : Fm PTm n := .all (lt (var 0) (length (Syn.shift L)) ⟶
  GaussianRationalHorner.evaluate (Syn.shift C) (abscissa (Syn.shift L) (var 0)) ≐ qzero)
ipra_subst xList
ipra_subst xRoots [Syn.subst_shift, Syn.shift_subst]
theorem x_body_at (L g : PTm n) : inst2 xBody g L = abscissa L (representative L zero g) := by simp [xBody,inst2]
theorem x_list_length (L : PTm n) : Γ ⊢[PRAAx] length (xList L) ≐ groupCount L zero := sequence_length _ _ _
theorem x_list_lookup (L g : PTm n) (hg : Γ ⊢[PRAAx] lt g (groupCount L zero)) : Γ ⊢[PRAAx]
    entry (xList L) g ≐ abscissa L (representative L zero g) := by
  simpa only [xList,x_body_at] using sequence_decode (Γ := Γ) xBody (x := L) hg

theorem x_root_at (C L i : PTm n) (h : Γ ⊢[PRAAx] xRoots C L) (hi : Γ ⊢[PRAAx] lt i (length L)) : Γ ⊢[PRAAx]
    GaussianRationalHorner.evaluate C (abscissa L i) ≐ qzero := by
  have rule : Γ ⊢[PRAAx] lt i (length L) ⟶ GaussianRationalHorner.evaluate C (abscissa L i) ≐ qzero := by simpa [xRoots] using h.allE i
  exact .impE rule hi

theorem x_list_roots (C L : PTm n) (h : Γ ⊢[PRAAx] xRoots C L) : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.roots C (xList L) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] xRoots (Syn.shift C) (Syn.shift L) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (xList (Syn.shift L))) :: Γ.map Fm.shift
  have hg : Δ ⊢[PRAAx] lt (var 0) (groupCount (Syn.shift L) zero) := lt_congr (.eqRefl _) (x_list_length _) Prf.hyp0
  have hi := Foundations.FiniteFiberGrouping.representative_bound xKeyF (Syn.shift L) zero (var 0) hg
  simpa only [Δ,Syn.shift,subst_xList] using
    (GaussianRationalMonicReduction.evaluate_congr (.eqRefl (Syn.shift C)) (x_list_lookup _ _ hg)).eqTrans
      (x_root_at _ _ _ hs.wk hi)

theorem x_list_distinct_at (L i j : PTm n) (hi : Γ ⊢[PRAAx] lt i (groupCount L zero))
    (hj : Γ ⊢[PRAAx] lt j (groupCount L zero)) (hij : Γ ⊢[PRAAx] lt i j) : Γ ⊢[PRAAx]
    neg (GaussianRationalMetric.qsub (entry (xList L) j) (entry (xList L) i) ≐ qzero) := by
  have ne : Γ ⊢[PRAAx] neg (j ≐ i) := .impI (lt_irrefl _ _ (lt_congr (.eqRefl i) Prf.hyp0 hij.wk))
  have distinct := GaussianRationalFiberGrouping.distinct_group_abscissae L zero j i hj hi ne
  refine .impI (.impE distinct.wk ?_)
  exact GaussianRationalValueEquality.equal_values_of_difference_zero _ _
    ((GaussianRationalSyntheticDivision.qsub_congr (x_list_lookup L j hj).eqSymm (x_list_lookup L i hi).eqSymm).wk.eqTrans Prf.hyp0)

theorem x_list_distinct (L : PTm n) : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct (xList L) := by
  unfold GaussianRationalFiniteRoots.distinct
  refine .allI (.impI ?_)
  unfold GaussianRationalFiniteRoots.distinctFrom
  refine .allI (.impI (.impI ?_))
  let Δ : List (Fm PTm (n+2)) := lt (var 1) (var 0) :: lt (var 0) (length (Syn.shift (Syn.shift (xList L)))) ::
    Fm.shift (lt (var 0) (length (Syn.shift (xList L)))) :: (Γ.map Fm.shift).map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 1) (groupCount (Syn.shift (Syn.shift L)) zero) := by
    apply lt_congr (.eqRefl _) (x_list_length _)
    simpa only [Δ,Fm.shift,subst_lt,Foundations.SequenceComposition.subst_length,subst_xList,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one] using
      (Prf.hyp (by simp [Δ]) : Δ ⊢[PRAAx] Fm.shift (lt (var 0) (length (Syn.shift (xList L)))))
  have hj : Δ ⊢[PRAAx] lt (var 0) (groupCount (Syn.shift (Syn.shift L)) zero) := by
    apply lt_congr (.eqRefl _) (x_list_length _)
    simpa only [Δ,Syn.shift,subst_xList] using (Prf.hyp1 : Δ ⊢[PRAAx] _)
  simpa only [Δ,Syn.shift,subst_xList,Syn.subst_var,Fin.succ_zero_eq_one,List.map_cons] using
    x_list_distinct_at (Syn.shift (Syn.shift L)) (var 1) (var 0) hi hj (Prf.hyp0 : Δ ⊢[PRAAx] _)

theorem group_root_bound (C s L : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ s)
    (hNZ : Γ ⊢[PRAAx] GaussianRationalPolynomialDegree.nonzeroCoefficients C s) (hx : Γ ⊢[PRAAx] xRoots C L) : Γ ⊢[PRAAx]
    le (groupCount L zero) s := by
  have count := GaussianRationalPolynomialDegree.computed_root_bound C s (xList L) hC hNZ (x_list_roots C L hx) (x_list_distinct L)
  exact le_congr (x_list_length L) (.eqRefl s) (le_trans (.andE₁ count) (.andE₂ count))

theorem vertical_count (F r C s L : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ s)
    (hNZ : Γ ⊢[PRAAx] GaussianRationalPolynomialDegree.nonzeroCoefficients C s) (hx : Γ ⊢[PRAAx] xRoots C L)
    (hf : Γ ⊢[PRAAx] curveZeros F r L) (hd : Γ ⊢[PRAAx] pointDistinct L) : Γ ⊢[PRAAx] le (length L) (r*s) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] curveZeros (Syn.shift F) (Syn.shift r) (Syn.shift L) := by simpa [Fm.shift,Syn.shift] using hf.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] pointDistinct (Syn.shift L) := by simpa [Fm.shift,Syn.shift] using hd.shift
  have sums : Γ ⊢[PRAAx] le (partitionTotal L zero)
      (ap2 (sumF (var 1 : PTm 2)) (groupCount L zero) r) := by
    refine sum_le_params (Foundations.FiniteFiberGrouping.sizeBody xKeyF) (var 1 : PTm 2)
      (Foundations.FiniteFiberGrouping.data L zero) r (groupCount L zero) (.allI (.impI ?_))
    let Δ := lt (var 0) (groupCount (Syn.shift L) zero) :: Γ.map Fm.shift
    have bound := GaussianRationalCurveFibers.fiber_size_bound (Γ := Δ) (Syn.shift F) (Syn.shift r) (Syn.shift L) zero (var 0) hs.wk ds.wk
    simpa only [Δ,Syn.shift,Foundations.FiniteFiberGrouping.subst_data,Foundations.FiniteFiberGrouping.subst_groupCount,
      ConciseIPRA.PTm.subst_zero,inst2,Syn.subst_var,Matrix.cons_val_one,Matrix.cons_val_zero] using
      le_congr (Foundations.FiniteFiberGrouping.size_at xKeyF (Syn.shift L) zero (var 0)).eqSymm (.eqRefl (Syn.shift r)) bound
  have total : Γ ⊢[PRAAx] le (length L) (groupCount L zero*r) :=
    le_congr (GaussianRationalFiberGrouping.cardinal_partition L zero) (Foundations.FiniteCoverAssignment.constant_sum _ _) sums
  exact le_trans total (le_congr (.eqRefl _) (mul_comm s r) (mul_le_mul_right r (group_root_bound C s L hC hNZ hx)))

def sourceCurve (f r c : PTm n) : PTm n := GaussianSuperellipticTail.tailRows (coefficients f (succ c)) r c
ipra_subst sourceCurve

theorem mapped_x_roots (a s P : PTm n) (ha : Γ ⊢[PRAAx] RationalArgmin.rationalEq (entry a (succ s)) scalarZero)
    (he : Γ ⊢[PRAAx] equations a s P) : Γ ⊢[PRAAx]
    xRoots (embeddedPolynomial a s) (RationalCurvePointsGaussianEmbedding.points P) := by
  have has : Γ.map Fm.shift ⊢[PRAAx] RationalArgmin.rationalEq (entry (Syn.shift a) (succ (Syn.shift s))) scalarZero := by
    simpa [Fm.shift,Syn.shift] using ha.shift
  have hes : Γ.map Fm.shift ⊢[PRAAx] equations (Syn.shift a) (Syn.shift s) (Syn.shift P) := by simpa [Fm.shift,Syn.shift] using he.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (RationalCurvePointsGaussianEmbedding.points (Syn.shift P))) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift P)) :=
    lt_congr (.eqRefl _) (RationalCurvePointsGaussianEmbedding.points_length _) Prf.hyp0
  have root := zero_equation_root (Syn.shift a) (Syn.shift s) (abscissa (Syn.shift P) (var 0)) (ordinate (Syn.shift P) (var 0)) has.wk
    (equation_at _ _ _ _ hes.wk hi)
  simpa only [Δ,Syn.shift,subst_embeddedPolynomial,RationalCurvePointsGaussianEmbedding.subst_points] using
    (GaussianRationalMonicReduction.evaluate_congr (.eqRefl (embeddedPolynomial (Syn.shift a) (Syn.shift s)))
      (RationalCurvePointsGaussianEmbedding.abscissa_at (Syn.shift P) (var 0) hi)).eqTrans root

/-- Original source branch: no degree, coprimality or nonzero-f condition is needed here. -/
theorem zero_section_bound (f a r c s P : PTm n) (hr : Γ ⊢[PRAAx] le one r)
    (hf : Γ ⊢[PRAAx] length f ≐ succ c) (hn : Γ ⊢[PRAAx] nonzero a s)
    (ha : Γ ⊢[PRAAx] RationalArgmin.rationalEq (entry a (succ s)) scalarZero)
    (hd : Γ ⊢[PRAAx] RationalCurvePointsGaussianEmbedding.distinct P)
    (hp : Γ ⊢[PRAAx] RationalSuperellipticNormDegree.pointPowers f r P)
    (he : Γ ⊢[PRAAx] equations a s P) : Γ ⊢[PRAAx] le (length P) (r*s) := by
  have powers := RationalSuperellipticSubspace.mapped_point_powers f r c P hf hp
  have curve := GaussianSuperellipticNormDegree.monic_curve_zeros (coefficients f (succ c)) r c
    (RationalCurvePointsGaussianEmbedding.points P) hr powers
  exact le_congr (RationalCurvePointsGaussianEmbedding.points_length P) (.eqRefl (r*s))
    (vertical_count (sourceCurve f r c) r (embeddedPolynomial a s) s (RationalCurvePointsGaussianEmbedding.points P)
      (RationalPolynomialGaussianEmbedding.coefficients_length _ _) (polynomial_nonzero a s hn ha) (mapped_x_roots a s P ha he)
      curve (RationalCurvePointsGaussianEmbedding.mapped_distinct P hd))

def input (f a r c s P : PTm n) : Fm PTm n := le one r ⋏ (length f ≐ succ c ⋏ (nonzero a s ⋏
  (RationalArgmin.rationalEq (entry a (succ s)) scalarZero ⋏ (RationalCurvePointsGaussianEmbedding.distinct P ⋏
    (RationalSuperellipticNormDegree.pointPowers f r P ⋏ equations a s P)))))
ipra_subst input
theorem source_bound (f a r c s P : PTm n) (h : Γ ⊢[PRAAx] input f a r c s P) : Γ ⊢[PRAAx] le (length P) (r*s) := by
  have tail := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))
  exact zero_section_bound f a r c s P (.andE₁ h) (.andE₁ (.andE₂ h)) (.andE₁ (.andE₂ (.andE₂ h)))
    (.andE₁ tail) (.andE₁ (.andE₂ tail)) (.andE₁ (.andE₂ (.andE₂ tail))) (.andE₂ (.andE₂ (.andE₂ tail)))

/-- Literal fiber polynomial is the existing monic Y^r-f at the actual representative. -/
def fiberPolynomial (f r c P g : PTm n) : PTm n := GaussianRationalCurveFibers.specializedCurve (sourceCurve f r c) r
  (RationalCurvePointsGaussianEmbedding.points P) zero g
theorem fiber_polynomial_length (f r c P g : PTm n) : Γ ⊢[PRAAx] length (fiberPolynomial f r c P g) ≐ succ r :=
  GaussianPolynomialMonicCompanion.monic_length _ _ _
theorem fiber_polynomial_evaluation (f r c P g z : PTm n) (hr : Γ ⊢[PRAAx] le one r) : Γ ⊢[PRAAx]
    GaussianRationalHorner.evaluate (fiberPolynomial f r c P g) z ≐ GaussianRationalMetric.qsub (GaussianRationalReciprocal.power z r)
      (GaussianRationalHorner.evaluate (coefficients f (succ c)) (abscissa (RationalCurvePointsGaussianEmbedding.points P)
        (representative (RationalCurvePointsGaussianEmbedding.points P) zero g))) :=
  GaussianSuperellipticTail.curve_evaluation _ _ _ _ _ hr

def output (f a r c s P : PTm n) : PTm n := pairT (embeddedPolynomial a s) (pairT (sourceCurve f r c)
  (pairT (xList (RationalCurvePointsGaussianEmbedding.points P))
    (pairT (groupCount (RationalCurvePointsGaussianEmbedding.points P) zero)
      (pairT (partitionTotal (RationalCurvePointsGaussianEmbedding.points P) zero) (r*s)))))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (f a r c s P : PTm n) : PTm n := app outputF ![f,a,r,c,s,P]
ipra_subst output
ipra_subst run

theorem program_at (f a r c s P : PTm n) : Γ ⊢[PRAAx] run f a r c s P ≐ output f a r c s P := by
  simpa [run,outputF,output,Matrix.cons_val_succ',Matrix.cons_val_zero'] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![f,a,r,c,s,P]
theorem returned_polynomial (f a r c s P : PTm n) : Γ ⊢[PRAAx] fstT (run f a r c s P) ≐ embeddedPolynomial a s :=
  (program_at f a r c s P).fstE
theorem returned_curve (f a r c s P : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run f a r c s P)) ≐ sourceCurve f r c :=
  (program_at f a r c s P).sndE.fstE
theorem returned_xlist (f a r c s P : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run f a r c s P))) ≐ xList (RationalCurvePointsGaussianEmbedding.points P) :=
  (program_at f a r c s P).sndE.sndE.fstE

private theorem returned_tail (f a r c s P : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run f a r c s P))) ≐
    pairT (groupCount (RationalCurvePointsGaussianEmbedding.points P) zero)
      (pairT (partitionTotal (RationalCurvePointsGaussianEmbedding.points P) zero) (r*s)) := by
  have e := (program_at (Γ := Γ) f a r c s P).sndE
  have e' := e.sndE
  exact e'.sndE
theorem returned_group_count (f a r c s P : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (run f a r c s P)))) ≐ groupCount (RationalCurvePointsGaussianEmbedding.points P) zero :=
  (returned_tail f a r c s P).fstE
theorem returned_total (f a r c s P : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (sndT (run f a r c s P))))) ≐ partitionTotal (RationalCurvePointsGaussianEmbedding.points P) zero :=
  (returned_tail f a r c s P).sndE.fstE
theorem returned_bound (f a r c s P : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (sndT (run f a r c s P))))) ≐ r*s :=
  (returned_tail f a r c s P).sndE.sndE
theorem returned_partition (f a r c s P : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (sndT (run f a r c s P))))) ≐ length P :=
  (returned_total f a r c s P).eqTrans ((GaussianRationalFiberGrouping.cardinal_partition _ zero).eqTrans
    (RationalCurvePointsGaussianEmbedding.points_length P))
theorem returned_source_bound (f a r c s P : PTm n) (h : Γ ⊢[PRAAx] input f a r c s P) : Γ ⊢[PRAAx]
    le (fstT (sndT (sndT (sndT (sndT (run f a r c s P)))))) (sndT (sndT (sndT (sndT (sndT (run f a r c s P)))))) :=
  le_congr (returned_partition f a r c s P).eqSymm (returned_bound f a r c s P).eqSymm (source_bound f a r c s P h)

theorem actual_zero_equation_polynomial_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (RationalArgmin.rationalEq (entry (var 0) (succ (var 1))) scalarZero ⟶ equation (var 0) (var 1) (var 2) (var 3) ≐ scalarZero ⟶
      GaussianRationalHorner.evaluate (embeddedPolynomial (var 0) (var 1)) (embed (var 2)) ≐ qzero) :=
  closeUniv 4 (.impI (.impI (zero_equation_root _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_zero_branch_polynomial_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (nonzero (var 0) (var 1) ⟶ RationalArgmin.rationalEq (entry (var 0) (succ (var 1))) scalarZero ⟶
      GaussianRationalPolynomialDegree.nonzeroCoefficients (embeddedPolynomial (var 0) (var 1)) (var 1)) :=
  closeUniv 2 (.impI (.impI (polynomial_nonzero _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_group_abscissae_distinct_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (GaussianRationalFiniteRoots.distinct (xList (var 0))) := closeUniv 1 (x_list_distinct _)
theorem actual_vertical_section_product_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 2) ≐ succ (var 3) ⟶ GaussianRationalPolynomialDegree.nonzeroCoefficients (var 2) (var 3) ⟶ xRoots (var 2) (var 4) ⟶
      curveZeros (var 0) (var 1) (var 4) ⟶ pointDistinct (var 4) ⟶ le (length (var 4)) (var 1*var 3)) := by
  apply closeUniv 5
  refine .impI (.impI (.impI (.impI (.impI ?_))))
  exact vertical_count _ _ _ _ _ Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0
theorem actual_original_zero_section_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ le (length (var 5)) (var 2*var 4)) :=
  closeUniv 6 (.impI (source_bound _ _ _ _ _ _ Prf.hyp0))
theorem actual_zero_section_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)

theorem actual_zero_fiber_polynomial_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 1) ⟶ GaussianRationalHorner.evaluate (fiberPolynomial (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5) ≐
      GaussianRationalMetric.qsub (GaussianRationalReciprocal.power (var 5) (var 1))
        (GaussianRationalHorner.evaluate (coefficients (var 0) (succ (var 2)))
          (abscissa (RationalCurvePointsGaussianEmbedding.points (var 3))
            (representative (RationalCurvePointsGaussianEmbedding.points (var 3)) zero (var 4))))) :=
  closeUniv 6 (.impI (fiber_polynomial_evaluation _ _ _ _ _ _ Prf.hyp0))
theorem actual_returned_zero_section_partition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (fstT (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))))) ≐ length (var 5)) :=
  closeUniv 6 (returned_partition _ _ _ _ _ _)
theorem actual_returned_zero_section_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      le (fstT (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))))))
        (sndT (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))))))) :=
  closeUniv 6 (.impI (returned_source_bound _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalPhiSectionZero
