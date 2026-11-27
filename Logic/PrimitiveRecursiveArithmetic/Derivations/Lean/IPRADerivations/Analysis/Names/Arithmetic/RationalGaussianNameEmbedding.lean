import IPRADerivations.Analysis.RationalArithmetic.Embeddings.RationalGaussianEmbedding
import IPRADerivations.Analysis.Optimization.CubeInfimum.RationalCubeInfimumName
import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianRadiusExponentialName
import IPRADerivations.Analysis.Names.GaussianNameBounds

/-!
# Original regular rational names embedded in the Gaussian real axis

The original independent-denominator scalar radius is carried to the
actual Euclidean Gaussian distance with the SAME tolerance. No name or
metric law is supplied as an output premise. Actual PR2 scalar samples
are embedded pointwise, yielding a Gaussian pointCN from the original
rational regularity predicate. A uniform disk is then computed from the
real zeroth sample, so the checked larger-disk exponential applies.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalGaussianNameEmbedding

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalGaussianEmbedding (embed native embed_represents)
open GaussianRationalHorner (represents positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_sq)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def crossNumerator (a b : PTm n) : PTm n := GaussianRootAlgebra.sub
  (ComplexLogarithmRemainder.scale (denominatorOf b) (native (numeratorOf a)))
  (ComplexLogarithmRemainder.scale (denominatorOf a) (native (numeratorOf b)))
ipra_subst crossNumerator

theorem cross_norm (a b : PTm n) : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq (crossNumerator a b) ≐
    zabs (RationalValueBounds.cross a b)*zabs (RationalValueBounds.cross a b) := by
  apply deriveNat
  rw [ComplexLogarithmRemainder.normSq_eval,zabs_sq]
  simp only [crossNumerator,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
    RationalGaussianEmbedding.native,ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,
    ComplexLogarithmRemainder.scale,ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_sub,RationalValueBounds.cross]
  simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
    ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_mul,ZT.toZ_ofNat,
    ZT.toZ_sub,Q.mk_zero,map_zero]
  ring

theorem difference_represents (a b : PTm n) : Γ ⊢[PRAAx]
    represents (qsub (embed a) (embed b)) (crossNumerator a b) (denominatorOf a*denominatorOf b) := by
  have da := RationalArgmin.denominator_positive (Γ := Γ) a
  have db := RationalArgmin.denominator_positive (Γ := Γ) b
  have left := GaussianRationalSyntheticDivision.rescale_to (Γ := Γ) (embed a) (native (numeratorOf a)) (denominatorOf a)
    (denominatorOf b) (denominatorOf a*denominatorOf b) (embed_represents a) (.eqRefl _)
  have right := GaussianRationalSyntheticDivision.rescale_to (Γ := Γ) (embed b) (native (numeratorOf b)) (denominatorOf b)
    (denominatorOf a) (denominatorOf a*denominatorOf b) (embed_represents b) (mul_comm _ _)
  exact GaussianRationalMetric.qsub_represents _ _ _ _ _ (positive_product _ _ da db) left right

/-- Exact scalar-to-Euclidean error transport for arbitrary raw codes. -/
theorem distance_from_radius (a b A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] RationalValueBounds.radius a b A B) : Γ ⊢[PRAAx]
    distanceBounded (embed a) (embed b) A B := by
  have square := le_mul_mono h h
  have clear : Γ ⊢[PRAAx] le ((B*B)*ComplexLogarithmRemainder.normSq (crossNumerator a b))
      ((A*A)*((denominatorOf a*denominatorOf b)*(denominatorOf a*denominatorOf b))) :=
    le_congr (by
      have e := natEq (cross_norm (Γ := Γ) a b)
      apply deriveNat; ipra_simps; rw [e]; ring) (by ipra_ring) square
  exact GaussianRationalMetric.bounded_of_cleared _ _ _ _ _
    (positive_product _ _ (RationalArgmin.denominator_positive a) (RationalArgmin.denominator_positive b))
    hB (difference_represents a b) clear

def body (f : PR 2) (p x : PTm n) : PTm n := embed (ap2 f p x)
def nameF (f : PR 2) : PR 2 := PTm.toPR (body f (var 0) (var 1))
def sample (f : PR 2) (p x : PTm n) : PTm n := ap2 (nameF f) p x
ipra_subst body
ipra_subst sample
theorem sample_at (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] sample f p x ≐ embed (ap2 f p x) := by
  change Γ ⊢[PRAAx] PTm.app (PTm.toPR (body f (var 0) (var 1))) ![p,x] ≐ embed (ap2 f p x)
  have h := toPR_eq (Γ := Γ) (body f (var 0) (var 1) : PTm 2) ![p,x]
  have e : Syn.subst ![p,x] (body f (var 0) (var 1) : PTm 2) = embed (ap2 f p x) := by
    rw [subst_body]
    rfl
  rw [e] at h
  exact h

theorem sample_canonical (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (sample f p x) :=
  GaussianRationalHorner.canonical_congr (sample_at f p x) (RationalGaussianEmbedding.embed_canonical _)
theorem sample_axis (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] RationalGaussianEmbedding.axis (sample f p x) :=
  RationalGaussianEmbedding.axis_congr (sample_at f p x).eqSymm (RationalGaussianEmbedding.embed_axis _)

theorem original_radius_at (f : PR 2) (x s t : PTm n) (h : Γ ⊢[PRAAx] RationalCubeInfimumName.regular f x) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (ap2 f s x) (ap2 f t x) (unit s+unit t) (unit s*unit t) := by
  have pair : Γ ⊢[PRAAx] .all
      (RationalValueBounds.radius (ap2 f (Syn.shift s) (Syn.shift x)) (ap2 f (var 0) (Syn.shift x))
        (unit (Syn.shift s)+unit (var 0)) (unit (Syn.shift s)*unit (var 0))) := by
    simpa only [RationalCubeInfimumName.regular,Fm.subst_all,RationalValueBounds.subst_radius,subst_ap2,
      RationalCubeGrid.subst_scale,RationalCubeGrid.scale,unit,PTm.subst_add,PTm.subst_mul,
      Syn.subst_var,Syn.up_zero,Syn.up_one,Syn.up_succ,Foundations.BoundedFormulas.subst_up_shift',
      Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift,Syn.shift_var,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using h.allE s
  simpa only [RationalValueBounds.subst_radius,subst_ap2,GaussianCoefficientNameBounds.subst_unit,
    PTm.subst_add,PTm.subst_mul,Syn.subst_var,Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift] using pair.allE t

theorem sample_regularity (f : PR 2) (x s t : PTm n) (h : Γ ⊢[PRAAx] RationalCubeInfimumName.regular f x) : Γ ⊢[PRAAx]
    distanceBounded (sample f s x) (sample f t x) (unit s+unit t) (unit s*unit t) :=
  GaussianRationalDistanceOrder.distance_congr (sample_at f s x).eqSymm (sample_at f t x).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_from_radius _ _ _ _ (positive_product _ _ (unit_positive s) (unit_positive t)) (original_radius_at f x s t h))
theorem name_regular (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] RationalCubeInfimumName.regular f x) : Γ ⊢[PRAAx]
    pointCN (nameF f) x := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] RationalCubeInfimumName.regular f (Syn.shift (Syn.shift x)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,unit,sample,Syn.shift] using
    sample_regularity f (Syn.shift (Syn.shift x)) (var 1) (var 0) hs

/-- A genuine integer sample disk is computed from the actual zeroth
embedded observation; no uniform bound is supplied as a premise. -/
theorem exponential_input (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] RationalCubeInfimumName.regular f x) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input (nameF f) (GaussianNameBounds.U (nameF f) x) x := by
  have cn := name_regular f x h
  refine .andI cn ?_
  simpa only [GaussianRadiusExponentialName.boundedSamples,GaussianRootApproximationWitness.pointBounds] using
    GaussianNameBounds.all_samples_bounded (nameF f) x cn
theorem exponential_name_regular (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] RationalCubeInfimumName.regular f x) : Γ ⊢[PRAAx]
    pointCN (GaussianRadiusExponentialName.nameF (nameF f))
      (GaussianRadiusExponentialName.data (GaussianNameBounds.U (nameF f) x) x) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input f x h)

theorem original_rational_radius_euclidean_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ RationalValueBounds.radius (var 0) (var 1) (var 2) (var 3) ⟶
      distanceBounded (embed (var 0)) (embed (var 1)) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (distance_from_radius _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_embedded_rational_sample_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (sample f (var 0) (var 1) ≐ embed (ap2 f (var 0) (var 1))) := closeUniv 2 (sample_at f _ _)
theorem actual_embedded_rational_sample_axis_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRationalHorner.canonical (sample f (var 0) (var 1)) ⋏ RationalGaussianEmbedding.axis (sample f (var 0) (var 1))) :=
  closeUniv 2 (.andI (sample_canonical f _ _) (sample_axis f _ _))
theorem original_rational_name_independent_precisions_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (RationalCubeInfimumName.regular f (var 0) ⟶
      distanceBounded (sample f (var 1) (var 0)) (sample f (var 2) (var 0))
        (unit (var 1)+unit (var 2)) (unit (var 1)*unit (var 2))) :=
  closeUniv 3 (.impI (sample_regularity f _ _ _ Prf.hyp0))
theorem original_regular_rational_name_gaussian_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (RationalCubeInfimumName.regular f (var 0) ⟶ pointCN (nameF f) (var 0)) :=
  closeUniv 1 (.impI (name_regular f _ Prf.hyp0))
theorem original_rational_name_computed_exponential_input_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (RationalCubeInfimumName.regular f (var 0) ⟶
      GaussianRadiusExponentialName.input (nameF f) (GaussianNameBounds.U (nameF f) (var 0)) (var 0)) :=
  closeUniv 1 (.impI (exponential_input f _ Prf.hyp0))
theorem original_rational_name_regular_exponential_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (RationalCubeInfimumName.regular f (var 0) ⟶ pointCN (GaussianRadiusExponentialName.nameF (nameF f))
      (GaussianRadiusExponentialName.data (GaussianNameBounds.U (nameF f) (var 0)) (var 0))) :=
  closeUniv 1 (.impI (exponential_name_regular f _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalGaussianNameEmbedding
