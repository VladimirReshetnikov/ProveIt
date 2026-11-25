import IPRADerivations.Analysis.GaussianGammaInverseConjugation
import IPRADerivations.Analysis.RationalGaussianRealPart
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.CertificateTactics

/-!
# Actual rational real values of the original Gamma names

The real-coordinate sampler is an original rational regular name.
Its Gaussian embedding contracts Euclidean distance. A name fixed by
conjugation is cross-equivalent to that actual real-axis projection.
The original C26 conclusions therefore yield real values at original
native inputs fixed by conjugation, including every constructed real
rational input without a raw-code eta assumption.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaRealValues

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalConjugation (point)
open GaussianRationalReciprocal (conjugate)
open RationalGaussianEmbedding (embed native)
open GaussianRationalHorner (represents positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianNameEquivalence (crossEquivalent)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit unit_positive)
open ComplexLogarithmRemainder (re im normSq scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def projection (q : PTm n) : PTm n := embed (fstT q)
@[simp] theorem subst_projection {l : ℕ} (σ : Fin n → PTm l) (q : PTm n) :
    Syn.subst σ (projection q) = projection (Syn.subst σ q) := by simp [projection]

theorem projection_represents (q a E : PTm n) (h : Γ ⊢[PRAAx] represents q a E) : Γ ⊢[PRAAx]
    represents (projection q) (native (re a)) E :=
  RationalGaussianEmbedding.embed_from_representation _ _ _ h.andE₁

theorem real_difference_norm_le (a b : PTm n) : Γ ⊢[PRAAx]
    le (normSq (GaussianRootAlgebra.sub (native (re a)) (native (re b)))) (normSq (GaussianRootAlgebra.sub a b)) := by
  refine le_of_eq_add (d := normSq (ComplexLogarithmRemainder.code (ZT.ofNat zero) (im (GaussianRootAlgebra.sub a b)))) ?_
  ipra_lc [GaussianRootAlgebra.re_sub, GaussianRootAlgebra.im_sub, native, ComplexLogarithmRemainder.eval_re_code, ComplexLogarithmRemainder.eval_im_code, ComplexLogarithmRemainder.normSq_eval]

theorem projection_distance_same_rep (q r a b E A B : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] represents q a E) (hr : Γ ⊢[PRAAx] represents r b E)
    (h : Γ ⊢[PRAAx] distanceBounded q r A B) : Γ ⊢[PRAAx]
    distanceBounded (projection q) (projection r) A B := by
  have old := (GaussianRationalMetric.bounded_difference_iff q r a b E A B hE hB hq hr).iffMp h
  apply (GaussianRationalMetric.bounded_difference_iff _ _ _ _ E A B hE hB
    (projection_represents q a E hq) (projection_represents r b E hr)).iffMpr
  exact le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl _) (real_difference_norm_le a b)) old

theorem projection_distance (q r A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded q r A B) : Γ ⊢[PRAAx] distanceBounded (projection q) (projection r) A B :=
  projection_distance_same_rep q r (scale (rawDen r) (rawGaussian q)) (scale (rawDen q) (rawGaussian r))
    (rawDen q*rawDen r) A B (positive_product _ _ (raw_den_positive q) (raw_den_positive r)) hB
    (GaussianRationalSyntheticDivision.rescale_to _ _ _ _ _ (raw_represents q) (.eqRefl _))
    (GaussianRationalSyntheticDivision.rescale_to _ _ _ _ _ (raw_represents r) (mul_comm _ _)) h

theorem conjugate_difference_norm (a : PTm n) : Γ ⊢[PRAAx]
    normSq (GaussianRootAlgebra.sub a (conjugate a)) ≐
      (two*two)*normSq (GaussianRootAlgebra.sub a (native (re a))) := by
  ipra_lc [GaussianRootAlgebra.re_sub, GaussianRootAlgebra.im_sub, native, ComplexLogarithmRemainder.eval_re_code, ComplexLogarithmRemainder.eval_im_code, GaussianRationalReciprocal.re_conjugate, GaussianRationalReciprocal.im_conjugate, ComplexLogarithmRemainder.normSq_eval]

theorem projection_gap (q A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded q (point q) A B) : Γ ⊢[PRAAx] distanceBounded q (projection q) A B := by
  let a := rawGaussian q
  let E := rawDen q
  have hE := raw_den_positive (Γ := Γ) q
  have hq := raw_represents (Γ := Γ) q
  have hc := GaussianRationalConjugation.point_represents q a E hE hq
  have old := (GaussianRationalMetric.bounded_difference_iff q (point q) a (conjugate a) E A B hE hB hq hc).iffMp h
  have normle : Γ ⊢[PRAAx] le (normSq (GaussianRootAlgebra.sub a (native (re a))))
      (normSq (GaussianRootAlgebra.sub a (conjugate a))) :=
    le_of_eq_add (d := (one+two)*normSq (GaussianRootAlgebra.sub a (native (re a))))
      ((conjugate_difference_norm a).eqTrans (by ipra_ring))
  exact (GaussianRationalMetric.bounded_difference_iff _ _ _ _ E A B hE hB hq (projection_represents q a E hq)).iffMpr
    (le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl _) normle) old)

theorem scalar_radius_of_embedded_distance (a b A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded (embed a) (embed b) A B) : Γ ⊢[PRAAx] RationalValueBounds.radius a b A B := by
  let E := RationalSupMetric.denominatorOf a*RationalSupMetric.denominatorOf b
  have hE := positive_product (Γ := Γ) _ _ (RationalArgmin.denominator_positive a) (RationalArgmin.denominator_positive b)
  have clear := GaussianRationalMetric.bounded_to_cleared _ _ E A B hE hB
    (RationalGaussianNameEmbedding.difference_represents a b) h
  have square : Γ ⊢[PRAAx] le
      ((B*Foundations.GapDecision.zabs (RationalValueBounds.cross a b))*(B*Foundations.GapDecision.zabs (RationalValueBounds.cross a b)))
      ((A*E)*(A*E)) :=
    le_congr ((congrMul (.eqRefl _) (RationalGaussianNameEmbedding.cross_norm a b)).eqTrans (by ipra_ring))
      (by ipra_ring) clear
  have small := nat_sqrt_mono square
  exact le_congr (.eqRefl _) (by dsimp only [E]; ipra_ring) small

def realBody (f : PR 2) : PTm 2 := fstT (ap2 f (var 0) (var 1))
def realF (f : PR 2) : PR 2 := PTm.toPR (realBody f)
def axisF (f : PR 2) : PR 2 := RationalGaussianNameEmbedding.nameF (realF f)

theorem real_sample_at (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] ap2 (realF f) p x ≐ fstT (ap2 f p x) := by
  have args : (fun i : Fin 2 => Syn.subst (![p,x] : Fin 2 → PTm n) ((![var 0,var 1] : Fin 2 → PTm 2) i)) = ![p,x] := by
    funext i
    fin_cases i <;> rfl
  simpa only [realF,realBody,ap2,subst_fstT,ConciseIPRA.PTm.subst_app,args] using
    toPR_eq (Γ := Γ) (realBody f) ![p,x]

theorem axis_sample_at (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] ap2 (axisF f) p x ≐ projection (ap2 f p x) :=
  (RationalGaussianNameEmbedding.sample_at _ p x).eqTrans (RationalGaussianRealPart.embed_congr (real_sample_at f p x))

theorem real_sample_regular (f : PR 2) (x p q : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (ap2 (realF f) p x) (ap2 (realF f) q x) (unit p+unit q) (unit p*unit q) :=
  RationalValueBounds.radius_congr (real_sample_at f p x).eqSymm (real_sample_at f q x).eqSymm (.eqRefl _) (.eqRefl _)
    (scalar_radius_of_embedded_distance _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q))
      (projection_distance _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q))
        (GaussianNameEquivalence.point_at f x p q h)))

theorem real_regular (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    RationalCubeInfimumName.regular (realF f) x := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift (Syn.shift x)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  simpa only [RationalCubeInfimumName.regular,RationalCubeGrid.scale,unit,Syn.shift] using
    real_sample_regular f (Syn.shift (Syn.shift x)) (var 1) (var 0) hs

theorem axis_regular (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx] pointCN (axisF f) x :=
  RationalGaussianNameEmbedding.name_regular _ _ (real_regular f x h)

theorem axis_sample_axis (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    RationalGaussianEmbedding.axis (ap2 (axisF f) p x) :=
  RationalGaussianEmbedding.axis_congr (axis_sample_at f p x).eqSymm (RationalGaussianEmbedding.embed_axis _)

theorem axis_gap_at (f : PR 2) (x p : PTm n)
    (he : Γ ⊢[PRAAx] crossEquivalent (GaussianNameConjugation.nameF f) f x x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 f p x) (ap2 (axisF f) p x) two (unit p) := by
  have raw := GaussianNameEquivalence.cross_at _ _ _ _ p p he
  have small : Γ ⊢[PRAAx] distanceBounded (point (ap2 f p x)) (ap2 f p x) two (unit p) :=
    GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
      (positive_product _ _ (unit_positive p) (unit_positive p)) (unit_positive p)
      (le_of_eq_add (d := zero) (by ipra_ring))
      (GaussianRationalDistanceOrder.distance_congr (GaussianNameConjugation.sample_at f p x) (.eqRefl _) (.eqRefl _) (.eqRefl _) raw)
  have gap := projection_gap _ two (unit p) (unit_positive p)
    (GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ (unit_positive p) small)
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (axis_sample_at f p x).eqSymm (.eqRefl _) (.eqRefl _) gap

theorem axis_cross (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (he : Γ ⊢[PRAAx] crossEquivalent (GaussianNameConjugation.nameF f) f x x) : Γ ⊢[PRAAx]
    crossEquivalent f (axisF f) x x := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ two hf (axis_regular f x hf)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] crossEquivalent (GaussianNameConjugation.nameF f) f (Syn.shift x) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using he.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,two,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using axis_gap_at f (Syn.shift x) (var 0) hs

/-- This is equality of an explicitly constructed native real code;
it does not assume eta for an arbitrary raw pair. -/
theorem native_real_fixed (a : ZT n) : Γ ⊢[PRAAx] conjugate (native a) ≐ native a := by
  let u := pairT a.pos a.neg
  let v : PTm n := pairT zero zero
  let z := native a
  have hp : Γ ⊢[PRAAx] fstT z ≐ u := fst_pair _ _
  have hq : Γ ⊢[PRAAx] sndT z ≐ v := snd_pair _ _
  change Γ ⊢[PRAAx] pairT (pairT (fstT (fstT z)) (sndT (fstT z)))
    (pairT (sndT (sndT z)) (fstT (sndT z))) ≐ pairT u v
  exact congrPairT
    (congrPairT ((congrFst hp).eqTrans (fst_pair _ _)) ((congrSnd hp).eqTrans (snd_pair _ _)))
    (congrPairT ((congrSnd hq).eqTrans (snd_pair _ _)) ((congrFst hq).eqTrans (fst_pair _ _)))

theorem cross_right_data {f g : PR 2} {x y y' : PTm n} (e : Γ ⊢[PRAAx] y ≐ y')
    (h : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx] crossEquivalent f g x y' := by
  simpa using Prf.eqSubst (Γ := Γ) (Ax := PRAAx) (crossEquivalent f g (var 0) (var 1) : Fm PTm 2)
    ![x,y] ![x,y'] (fun i => by fin_cases i; exact .eqRefl _; exact e) (by simpa using h)

theorem c7_data_congr {z a : PTm n} (R B : PTm n) (e : Γ ⊢[PRAAx] z ≐ a) : Γ ⊢[PRAAx]
    GaussianGammaC7Name.data z R B ≐ GaussianGammaC7Name.data a R B := by
  ipra_congr (GaussianGammaC7Name.data (var 0) (var 1) (var 2) : PTm 3) with [e, .eqRefl R, .eqRefl B]

theorem gamma_data_congr {z a : PTm n} (R B d : PTm n) (e : Γ ⊢[PRAAx] z ≐ a) : Γ ⊢[PRAAx]
    GaussianGammaReciprocalInverse.gammaData z R B d ≐ GaussianGammaReciprocalInverse.gammaData a R B d := by
  ipra_congr (GaussianGammaReciprocalInverse.gammaData (var 0) (var 1) (var 2) (var 3) : PTm 4) with
    [e, .eqRefl R, .eqRefl B, .eqRefl d]

theorem original_reciprocal_real (z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B)
    (hr : Γ ⊢[PRAAx] conjugate z ≐ z) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaC7Name.nameF (axisF GaussianGammaC7Name.nameF)
      (GaussianGammaC7Name.data z R B) (GaussianGammaC7Name.data z R B) :=
  axis_cross _ _ (GaussianGammaC7Name.name_regular z R B h)
    (cross_right_data (c7_data_congr R B hr) (GaussianGammaNameConjugation.original_reciprocal_conjugate z R B h))

theorem original_gamma_real (z R B a d : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z R B a d)
    (hr : Γ ⊢[PRAAx] conjugate z ≐ z) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaReciprocalInverse.gammaF (axisF GaussianGammaReciprocalInverse.gammaF)
      (GaussianGammaReciprocalInverse.gammaData z R B d) (GaussianGammaReciprocalInverse.gammaData z R B d) :=
  axis_cross _ _ (GaussianGammaReciprocalInverse.gamma_regular z R B a d h)
    (cross_right_data (gamma_data_congr R B d hr) (GaussianGammaInverseConjugation.original_gamma_conjugate z R B a d h))

theorem original_real_rational_reciprocal (q R : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source (native (RationalSupMetric.numeratorOf q)) R (RationalSupMetric.denominatorOf q)) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaC7Name.nameF (axisF GaussianGammaC7Name.nameF)
      (GaussianGammaC7Name.data (native (RationalSupMetric.numeratorOf q)) R (RationalSupMetric.denominatorOf q))
      (GaussianGammaC7Name.data (native (RationalSupMetric.numeratorOf q)) R (RationalSupMetric.denominatorOf q)) :=
  original_reciprocal_real _ _ _ h (native_real_fixed _)

theorem original_real_rational_gamma (q R a d : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (native (RationalSupMetric.numeratorOf q)) R (RationalSupMetric.denominatorOf q) a d) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaReciprocalInverse.gammaF (axisF GaussianGammaReciprocalInverse.gammaF)
      (GaussianGammaReciprocalInverse.gammaData (native (RationalSupMetric.numeratorOf q)) R (RationalSupMetric.denominatorOf q) d)
      (GaussianGammaReciprocalInverse.gammaData (native (RationalSupMetric.numeratorOf q)) R (RationalSupMetric.denominatorOf q) d) :=
  original_gamma_real _ _ _ _ _ h (native_real_fixed _)

/-- The same PR2 returns original, rational projection and embedded
real-axis observations, without changing the original query precision. -/
def output (f : PR 2) (p x : PTm n) : PTm n :=
  pairT (ap2 f p x) (pairT (ap2 (realF f) p x) (ap2 (axisF f) p x))
def outputF (f : PR 2) : PR 2 := PTm.toPR (output f (var 0) (var 1))
def run (f : PR 2) (p x : PTm n) : PTm n := ap2 (outputF f) p x
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (p x : PTm n) :
    Syn.subst σ (output f p x) = output f (Syn.subst σ p) (Syn.subst σ x) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (p x : PTm n) :
    Syn.subst σ (run f p x) = run f (Syn.subst σ p) (Syn.subst σ x) := by simp [run]

theorem program_at (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] run f p x ≐ output f p x := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output f (var 0) (var 1) : PTm 2) ![p,x]
theorem returned_original (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] fstT (run f p x) ≐ ap2 f p x :=
  (congrFst (program_at f p x)).eqTrans (fst_pair _ _)
theorem returned_scalar (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run f p x)) ≐ ap2 (realF f) p x :=
  ((congrFst (congrSnd (program_at f p x))).eqTrans (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_axis (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run f p x)) ≐ ap2 (axisF f) p x :=
  ((congrSnd (congrSnd (program_at f p x))).eqTrans (congrSnd (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_real_coordinate (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run f p x)) ≐ fstT (fstT (run f p x)) :=
  (returned_scalar f p x).eqTrans ((real_sample_at f p x).eqTrans (congrFst (returned_original f p x)).eqSymm)
theorem returned_axis_is_embedding (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run f p x)) ≐ embed (fstT (sndT (run f p x))) :=
  (returned_axis f p x).eqTrans
    ((RationalGaussianNameEmbedding.sample_at _ p x).eqTrans (RationalGaussianRealPart.embed_congr (returned_scalar f p x)).eqSymm)
theorem returned_axis_value (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    RationalGaussianEmbedding.axis (sndT (sndT (run f p x))) :=
  RationalGaussianEmbedding.axis_congr (returned_axis f p x).eqSymm (axis_sample_axis f p x)

theorem actual_real_projection_contracts_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ distanceBounded (var 0) (var 1) (var 2) (var 3) ⟶
      distanceBounded (projection (var 0)) (projection (var 1)) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (projection_distance _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_original_rational_projection_sampler_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 (realF f) (var 0) (var 1) ≐ fstT (ap2 f (var 0) (var 1))) := closeUniv 2 (real_sample_at f _ _)

theorem actual_original_rational_projection_regular_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN f (var 0) ⟶ RationalCubeInfimumName.regular (realF f) (var 0)) :=
  closeUniv 1 (.impI (real_regular f _ Prf.hyp0))

theorem actual_conjugation_fixed_name_real_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN f (var 0) ⋏ crossEquivalent (GaussianNameConjugation.nameF f) f (var 0) (var 0) ⟶
      crossEquivalent f (axisF f) (var 0) (var 0)) :=
  closeUniv 1 (.impI (axis_cross f _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_constructed_real_input_fixed_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (conjugate (native (⟨var 0,var 1⟩ : ZT 2)) ≐ native (⟨var 0,var 1⟩ : ZT 2)) :=
  closeUniv 2 (native_real_fixed _)

theorem original_real_rational_P_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianGammaCanonicalExponent.source (native (RationalSupMetric.numeratorOf (var 0))) (var 1) (RationalSupMetric.denominatorOf (var 0)) ⟶
      RationalCubeInfimumName.regular (realF GaussianGammaC7Name.nameF)
        (GaussianGammaC7Name.data (native (RationalSupMetric.numeratorOf (var 0))) (var 1) (RationalSupMetric.denominatorOf (var 0))) ⋏
      crossEquivalent GaussianGammaC7Name.nameF (axisF GaussianGammaC7Name.nameF)
        (GaussianGammaC7Name.data (native (RationalSupMetric.numeratorOf (var 0))) (var 1) (RationalSupMetric.denominatorOf (var 0)))
        (GaussianGammaC7Name.data (native (RationalSupMetric.numeratorOf (var 0))) (var 1) (RationalSupMetric.denominatorOf (var 0)))) :=
  closeUniv 2 (.impI (.andI (real_regular _ _ (GaussianGammaC7Name.name_regular _ _ _ Prf.hyp0))
    (original_real_rational_reciprocal _ _ Prf.hyp0)))

theorem original_real_rational_Gamma_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianGammaReciprocalInverse.source (native (RationalSupMetric.numeratorOf (var 0))) (var 1) (RationalSupMetric.denominatorOf (var 0)) (var 2) (var 3) ⟶
      RationalCubeInfimumName.regular (realF GaussianGammaReciprocalInverse.gammaF)
        (GaussianGammaReciprocalInverse.gammaData (native (RationalSupMetric.numeratorOf (var 0))) (var 1) (RationalSupMetric.denominatorOf (var 0)) (var 3)) ⋏
      crossEquivalent GaussianGammaReciprocalInverse.gammaF (axisF GaussianGammaReciprocalInverse.gammaF)
        (GaussianGammaReciprocalInverse.gammaData (native (RationalSupMetric.numeratorOf (var 0))) (var 1) (RationalSupMetric.denominatorOf (var 0)) (var 3))
        (GaussianGammaReciprocalInverse.gammaData (native (RationalSupMetric.numeratorOf (var 0))) (var 1) (RationalSupMetric.denominatorOf (var 0)) (var 3))) :=
  closeUniv 4 (.impI (.andI (real_regular _ _ (GaussianGammaReciprocalInverse.gamma_regular _ _ _ _ _ Prf.hyp0))
    (original_real_rational_gamma _ _ _ _ Prf.hyp0)))

theorem actual_returned_real_projection_fields_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (fstT (run f (var 0) (var 1)) ≐ ap2 f (var 0) (var 1) ⋏
      (fstT (sndT (run f (var 0) (var 1))) ≐ fstT (fstT (run f (var 0) (var 1))) ⋏
        (sndT (sndT (run f (var 0) (var 1))) ≐ embed (fstT (sndT (run f (var 0) (var 1)))) ⋏
          RationalGaussianEmbedding.axis (sndT (sndT (run f (var 0) (var 1))))))) :=
  closeUniv 2 (.andI (returned_original f _ _) (.andI (returned_real_coordinate f _ _)
    (.andI (returned_axis_is_embedding f _ _) (returned_axis_value f _ _))))

end LeanProofs.IPRA.Analysis.GaussianGammaRealValues
