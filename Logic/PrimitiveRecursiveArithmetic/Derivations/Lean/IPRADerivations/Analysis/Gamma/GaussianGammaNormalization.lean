import IPRADerivations.Analysis.Gamma.GaussianGammaFunctionalEquation
import IPRADerivations.Analysis.Gamma.GaussianGammaReciprocalInverse

/-!
# Normalization of the original Gamma reciprocal at one

The same original Euler head at one telescopes to N+1 by a genuine
quantifier-free induction. The original negative-log inverse provider
then gives Q_N(1)=(N+1)/N. The actual C10 error and a computed finite
cutoff identify the original C7 name at one with the actual constant one.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNormalization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (ofGaussian canonical_unique represents_congr positive_product)
open ComplexLogarithmRemainder (oneCode scale)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (qF qData q_regular)
open GaussianGammaEulerShift (expF negativeLogExpData negative_log_exp_regular)
open GaussianGammaEulerShiftLimit (reciprocalPoint)
open GaussianGammaFunctionalEquation (allLogInverse log_inverse_at)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_refl)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def integerPoint (k : PTm n) : PTm n := ofGaussian (scale k oneCode) one
def ratio (N : PTm n) : PTm n := ofGaussian (scale (succ N) oneCode) N
def headLaw (N : PTm n) : Fm PTm n := GaussianGammaEulerHead.head oneCode one N ≐ integerPoint (succ N)
@[simp] theorem subst_integerPoint {l : ℕ} (σ : Fin n → PTm l) (k : PTm n) :
    Syn.subst σ (integerPoint k) = integerPoint (Syn.subst σ k) := by simp [integerPoint]
@[simp] theorem subst_ratio {l : ℕ} (σ : Fin n → PTm l) (N : PTm n) :
    Syn.subst σ (ratio N) = ratio (Syn.subst σ N) := by simp [ratio]
@[simp] theorem subst_headLaw {l : ℕ} (σ : Fin n → PTm l) (N : PTm n) :
    (headLaw N).subst σ = headLaw (Syn.subst σ N) := by simp [headLaw]

theorem head_zero : Γ ⊢[PRAAx] headLaw (zero : PTm n) := by
  refine (GaussianGammaEulerHead.head_zero oneCode one (le_refl _)).eqTrans ?_
  apply canonical_unique _ _ _ one (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _))
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _)) (le_refl _)
    (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _))
  apply represents_congr (.eqRefl _) _ (.eqRefl _) (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _))
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
  all_goals ipra_simps; ring

theorem head_multiply_step (N : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.qmul (integerPoint (succ N)) (GaussianGammaEulerHead.factor N oneCode one) ≐ integerPoint (succ (succ N)) := by
  let E : PTm n := one*(one*succ N)
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (le_refl one)
    (positive_product _ _ (le_refl one) (zero_lt_succ N))
  have left := GaussianRationalHorner.qmul_represents (Γ := Γ) _ _ _ _ _ _ (le_refl one)
    (positive_product _ _ (le_refl one) (zero_lt_succ N))
    (GaussianRationalHorner.ofGaussian_represents (scale (succ N) oneCode) one (le_refl _))
    (GaussianGammaEulerHeadLower.factor_represents N oneCode one (le_refl _))
  have right := GaussianRationalSyntheticDivision.rescale_to (Γ := Γ) (integerPoint (succ (succ N)))
    (scale (succ (succ N)) oneCode) one E E (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _)) (one_mul E)
  apply canonical_unique _ _ _ E (GaussianRationalHorner.qmul_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _)) hE _ right
  apply represents_congr (.eqRefl _) _ (.eqRefl _) left
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,GaussianGammaEulerHeadLower.translated,
      GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add]
  all_goals dsimp only [E]; ipra_simps; ring

theorem head_step (N : PTm n) (ih : Γ ⊢[PRAAx] headLaw N) : Γ ⊢[PRAAx] headLaw (succ N) :=
  (GaussianGammaEulerHead.head_succ oneCode one N).eqTrans
    ((GaussianRationalSyntheticDivision.qmul_congr ih (.eqRefl _)).eqTrans (head_multiply_step N))

theorem head_at_one (N : PTm n) : Γ ⊢[PRAAx] headLaw N := by
  have all : Γ ⊢[PRAAx] .all (headLaw (var 0)) := by
    refine PRA.qfInd _ (by trivial) ?_ ?_
    · simpa only [subst_headLaw,Syn.subst_var,Syn.inst_zero] using (head_zero (Γ := Γ))
    · simpa only [subst_headLaw,Syn.subst_var,Syn.repl_zero] using head_step (var 0) Prf.hyp0
  simpa only [subst_headLaw,Syn.subst_var,Syn.inst_zero] using all.allE N

theorem returned_head_at_one (N : PTm n) : Γ ⊢[PRAAx]
    GaussianGammaEulerHead.run oneCode one N ≐ integerPoint (succ N) :=
  (GaussianGammaEulerHead.program_at oneCode one N).eqTrans (head_at_one N)

theorem integer_reciprocal_ratio (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianRationalHorner.qmul (integerPoint (succ N)) (reciprocalPoint N) ≐ ratio N := by
  have left := GaussianRationalHorner.qmul_represents (Γ := Γ) _ _ _ _ _ _ (le_refl one) hN
    (GaussianRationalHorner.ofGaussian_represents (scale (succ N) oneCode) one (le_refl _))
    (GaussianRationalHorner.ofGaussian_represents oneCode N hN)
  apply canonical_unique _ _ _ N (GaussianRationalHorner.qmul_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hN) hN _ (GaussianRationalHorner.ofGaussian_represents _ _ hN)
  apply represents_congr (.eqRefl _) _ (one_mul N) left
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
  all_goals ring

theorem finite_Q_at_one (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] allLogInverse) : Γ ⊢[PRAAx]
    crossEquivalent qF constantF (qData oneCode one N) (ratio N) := by
  have expn := negative_log_exp_regular (Γ := Γ) N hN
  have first := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF expF constantF
    (GaussianGammaEulerHead.run oneCode one N) (integerPoint (succ N)) (negativeLogExpData N) (reciprocalPoint N)
    (constant_regular _) (constant_regular _) expn (constant_regular _)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (returned_head_at_one N)) (log_inverse_at N hi hN)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _
    (GaussianGammaWeierstrassApproximant.constant_product_cross (integerPoint (succ N)) (reciprocalPoint N))
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (integer_reciprocal_ratio N hN)))


theorem ratio_difference_represents (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianRationalHorner.represents (GaussianRationalMetric.qsub (ratio N) GaussianRationalSyntheticDivision.qone) oneCode N := by
  have rep := GaussianRationalMetric.qsub_represents (Γ := Γ) (ratio N) GaussianRationalSyntheticDivision.qone
    (scale (succ N) oneCode) (scale N oneCode) N hN
    (GaussianRationalHorner.ofGaussian_represents (scale (succ N) oneCode) N hN) (GaussianRationalReciprocal.qone_represents_scaled N)
  apply represents_congr (.eqRefl _) _ (.eqRefl _) rep
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
  all_goals ipra_simps; ring

theorem ratio_distance (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (ratio N) GaussianRationalSyntheticDivision.qone one N := by
  apply GaussianRationalMetric.bounded_of_cleared _ oneCode N one N hN hN (ratio_difference_represents N hN)
  exact le_congr (by have e := natEq (ComplexLogarithmRemainder.normSq_one (Γ := Γ)); apply deriveNat; ipra_simps; rw [e]; ring)
    (by ipra_ring) (le_refl (N*N))

theorem unit_source : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source (oneCode : PTm n) one one :=
  .andI (le_refl _) (.andI (le_refl _)
    (le_congr ComplexLogarithmRemainder.normSq_one.eqSymm (by ipra_ring) (le_refl one)))

def cutoff (t : PTm n) : PTm n := one+t+two+GaussianGammaPerturbationExponent.numerator one+
  (GaussianGammaFunctionalEquation.eulerRate one+one)*unit t
@[simp] theorem subst_cutoff {l : ℕ} (σ : Fin n → PTm l) (t : PTm n) :
    Syn.subst σ (cutoff t) = cutoff (Syn.subst σ t) := by simp [cutoff]

theorem cutoff_positive (t : PTm n) : Γ ⊢[PRAAx] le one (cutoff t) := by
  unfold cutoff
  ipra_le 𝔞 t+2+𝔞(GaussianGammaPerturbationExponent.numerator one)+
    (𝔞(GaussianGammaFunctionalEquation.eulerRate one)+1)*𝔞(unit t)

theorem cutoff_threshold (t : PTm n) : Γ ⊢[PRAAx]
    le ((GaussianGammaFunctionalEquation.eulerRate one+one)*unit t) (cutoff t) := by
  unfold cutoff
  ipra_le 1+𝔞 t+2+𝔞(GaussianGammaPerturbationExponent.numerator one)

theorem cutoff_source (t : PTm n) : Γ ⊢[PRAAx] GaussianGammaEulerConvergence.source oneCode one one (cutoff t) := by
  refine .andI unit_source (.andI ?_ ?_)
  · unfold cutoff
    ipra_le 1+𝔞 t+𝔞(GaussianGammaPerturbationExponent.numerator one)+
      (𝔞(GaussianGammaFunctionalEquation.eulerRate one)+1)*𝔞(unit t)
  · unfold cutoff
    ipra_le 1+𝔞 t+2+(𝔞(GaussianGammaFunctionalEquation.eulerRate one)+1)*𝔞(unit t)

/-- The only analytic premise here is the original negative mesh-log
inverse provider. The Euler head, finite ratio and finite cutoff are derived. -/
theorem normalization_at (t : PTm n) (hi : Γ ⊢[PRAAx] allLogInverse) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaC7Name.sample t oneCode one one) GaussianRationalSyntheticDivision.qone
      (one+two+two) (unit t) := by
  let N := cutoff t
  let E := N*unit t
  have hn := cutoff_positive (Γ := Γ) t
  have hp := positive_product (Γ := Γ) _ _ hn (unit_positive t)
  have first : Γ ⊢[PRAAx] distanceBounded (GaussianGammaC7Name.sample t oneCode one one)
      (ap2 qF t (qData oneCode one N)) (GaussianGammaFunctionalEquation.eulerRate one*unit t+two*N) E :=
    GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ hp
      (GaussianGammaFunctionalEquation.earlier_euler_error t t oneCode one one N (cutoff_source t) (le_refl _))
  have second : Γ ⊢[PRAAx] distanceBounded (ap2 qF t (qData oneCode one N)) (ratio N) (two*N) E := by
    have raw := GaussianNameEquivalence.cross_at (Γ := Γ) _ _ _ _ t t (finite_Q_at_one N hn hi)
    have aligned : Γ ⊢[PRAAx] distanceBounded (ap2 qF t (qData oneCode one N)) (ratio N)
        (unit t+unit t) (unit t*unit t) :=
      GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (GaussianGammaCanonicalExponent.constant_at t (ratio N))
        (.eqRefl _) (.eqRefl _) raw
    exact GaussianRationalDistanceOrder.distance_radius_mono _ _ (unit t+unit t) (unit t*unit t) (two*N) E
      (positive_product _ _ (unit_positive t) (unit_positive t)) hp
      (le_of_eq_add (d := zero) (by dsimp only [E]; ipra_ring)) aligned
  have third : Γ ⊢[PRAAx] distanceBounded (ratio N) GaussianRationalSyntheticDivision.qone (unit t) E :=
    GaussianRationalDistanceOrder.distance_radius_mono _ _ one N (unit t) E hn hp
      (le_of_eq_add (d := zero) (by (try dsimp only [E]); ipra_ring)) (ratio_distance N hn)
  have joined := GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ hp
    (GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ hp first second) third
  apply GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ hp (unit_positive t) _ joined
  have threshold := cutoff_threshold (Γ := Γ) t
  ipra_le 𝔞(unit t)*sl threshold using
    try dsimp only [E]
    ring

theorem original_P_one (hi : Γ ⊢[PRAAx] allLogInverse) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaC7Name.nameF GaussianNameRingLaws.oneF
      (GaussianGammaC7Name.data (oneCode : PTm n) one one) zero := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (one+two+two)
    (GaussianGammaC7Name.name_regular oneCode one one unit_source) (GaussianNameRingLaws.one_fast zero)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] allLogInverse := by simpa [allLogInverse,Fm.shift,Syn.shift] using hi.shift
  have same := GaussianRationalDistanceOrder.distance_congr (.eqRefl _)
    (GaussianNameRingLaws.one_at (var 0) zero).eqSymm (.eqRefl _) (.eqRefl _) (normalization_at (var 0) hs)
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianGammaC7Name.sample,Syn.shift,
    GaussianGammaC7Name.subst_data,ComplexLogarithmRemainder.subst_oneCode,PTm.subst_add,
    one,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using same


theorem translated_one_norm (k : PTm n) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.normSq (GaussianGammaEulerHeadLower.translated oneCode one k) ≐ succ k*succ k := by
  apply deriveNat
  ipra_simps
  rw [ComplexLogarithmRemainder.normSq_eval]
  simp only [GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
    GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
  ipra_simps
  ring

theorem unit_pole_at (k : PTm n) : Γ ⊢[PRAAx] GaussianGammaEulerHeadLower.poleAt oneCode one one one k :=
  le_congr (by ipra_ring) ((congrMul (.eqRefl _) (translated_one_norm k)).eqTrans (by ipra_ring)).eqSymm
    (sq_le_sq (zero_lt_succ k))

theorem unit_pole_guard (N : PTm n) : Γ ⊢[PRAAx] GaussianGammaEulerHeadLower.poleGuard oneCode one one one N := by
  refine .allI (.impI ?_)
  simpa only [GaussianGammaEulerHeadLower.poleGuard,Syn.shift,ComplexLogarithmRemainder.subst_oneCode,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    unit_pole_at (Γ := le (var 0) (Syn.shift N) :: Γ.map Fm.shift) (var 0)

theorem unit_gamma_source : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (oneCode : PTm n) one one one one :=
  .andI unit_source (.andI (le_refl _) (.andI (le_refl _) (unit_pole_guard _)))

/-- C21 normalization for the SAME original reciprocal algorithm and its
actual anchor. The original pole guard at one is derived, not supplied. -/
theorem original_Gamma_one (hi : Γ ⊢[PRAAx] allLogInverse) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaReciprocalInverse.gammaF GaussianNameRingLaws.oneF
      (GaussianGammaReciprocalInverse.gammaData (oneCode : PTm n) one one one) zero := by
  let P := GaussianGammaC7Name.nameF
  let x := GaussianGammaC7Name.data (oneCode : PTm n) one one
  have hp : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN P x := GaussianGammaC7Name.name_regular oneCode one one unit_source
  have ho := GaussianNameRingLaws.one_fast (Γ := Γ) (zero : PTm n)
  have first := GaussianGammaAdjacentCutoff.multiply_cross P GaussianNameRingLaws.oneF GaussianNameRingLaws.oneF GaussianNameRingLaws.oneF
    x zero zero zero hp ho ho ho (original_P_one hi) (cross_refl _ _ ho)
  have product := cross_trans _ _ _ _ _ _ first
    (cross_trans _ _ _ _ _ _ (GaussianNameRingLaws.multiply_one GaussianNameRingLaws.oneF zero ho)
      (GaussianBoundedInverseApartness.ones_equivalent zero x))
  have original := (GaussianGammaReciprocalInverse.original_gamma_inverse (Γ := Γ) oneCode one one one one unit_gamma_source).andE₁
  exact GaussianBoundedInverseApartness.reciprocal_matches_inverse P GaussianNameRingLaws.oneF
    (GaussianGammaReciprocalInverse.gammaHeight oneCode one one one) x zero hp ho original.andE₂ product


/-- Actual original P/Gamma observations at one and an independently
queried constant one. The analytic provider is only a proof input. -/
def output (p q : PTm n) : PTm n := pairT (GaussianGammaC7Name.sample p oneCode one one)
  (pairT (ap2 GaussianGammaReciprocalInverse.gammaF p (GaussianGammaReciprocalInverse.gammaData oneCode one one one))
    (ap2 GaussianNameRingLaws.oneF q zero))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (p q : PTm n) : PTm n := ap2 outputF p q
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (p q : PTm n) :
    Syn.subst σ (output p q) = output (Syn.subst σ p) (Syn.subst σ q) := by
  simp [output,GaussianGammaReciprocalInverse.gammaData,GaussianGammaReciprocalInverse.gammaHeight]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (p q : PTm n) :
    Syn.subst σ (run p q) = run (Syn.subst σ p) (Syn.subst σ q) := by simp [run]

theorem program_at (p q : PTm n) : Γ ⊢[PRAAx] run p q ≐ output p q := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![p,q]
theorem returned_P (p q : PTm n) : Γ ⊢[PRAAx] fstT (run p q) ≐ GaussianGammaC7Name.sample p oneCode one one :=
  (congrFst (program_at p q)).eqTrans (fst_pair _ _)
theorem returned_Gamma (p q : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run p q)) ≐ ap2 GaussianGammaReciprocalInverse.gammaF p (GaussianGammaReciprocalInverse.gammaData oneCode one one one) :=
  ((congrFst (congrSnd (program_at p q))).eqTrans (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_one (p q : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run p q)) ≐ ap2 GaussianNameRingLaws.oneF q zero :=
  ((congrSnd (congrSnd (program_at p q))).eqTrans (congrSnd (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_P_distance (p q : PTm n) (hi : Γ ⊢[PRAAx] allLogInverse) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run p q)) (sndT (sndT (run p q))) (unit p+unit q) (unit p*unit q) :=
  GaussianRationalDistanceOrder.distance_congr (returned_P p q).eqSymm (returned_one p q).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianNameEquivalence.cross_at _ _ _ _ p q (original_P_one hi))
theorem returned_Gamma_distance (p q : PTm n) (hi : Γ ⊢[PRAAx] allLogInverse) : Γ ⊢[PRAAx]
    distanceBounded (fstT (sndT (run p q))) (sndT (sndT (run p q))) (unit p+unit q) (unit p*unit q) :=
  GaussianRationalDistanceOrder.distance_congr (returned_Gamma p q).eqSymm (returned_one p q).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianNameEquivalence.cross_at _ _ _ _ p q (original_Gamma_one hi))

theorem actual_original_unit_head_telescoping_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (GaussianGammaEulerHead.run oneCode one (var 0) ≐ integerPoint (succ (var 0))) :=
  closeUniv 1 (returned_head_at_one _)

theorem original_finite_Q_one_normalization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ allLogInverse ⟶ crossEquivalent qF constantF (qData oneCode one (var 0)) (ratio (var 0))) :=
  closeUniv 1 (.impI (.impI (finite_Q_at_one _ Prf.hyp1 Prf.hyp0)))

theorem actual_original_unit_ratio_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ distanceBounded (ratio (var 0)) GaussianRationalSyntheticDivision.qone one (var 0)) :=
  closeUniv 1 (.impI (ratio_distance _ Prf.hyp0))

theorem actual_unit_normalization_cutoff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (cutoff (var 0)) ⋏
      (GaussianGammaEulerConvergence.source oneCode one one (cutoff (var 0)) ⋏
        le ((GaussianGammaFunctionalEquation.eulerRate one+one)*unit (var 0)) (cutoff (var 0)))) :=
  closeUniv 1 (.andI (cutoff_positive _) (.andI (cutoff_source _) (cutoff_threshold _)))

theorem original_C20_P_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    (allLogInverse ⟶ crossEquivalent GaussianGammaC7Name.nameF GaussianNameRingLaws.oneF
      (GaussianGammaC7Name.data oneCode one one) zero) := .impI (original_P_one Prf.hyp0)

theorem original_unit_gamma_domain_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    GaussianGammaReciprocalInverse.source oneCode one one one one := unit_gamma_source

theorem original_C21_Gamma_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    (allLogInverse ⟶ crossEquivalent GaussianGammaReciprocalInverse.gammaF GaussianNameRingLaws.oneF
      (GaussianGammaReciprocalInverse.gammaData oneCode one one one) zero) := .impI (original_Gamma_one Prf.hyp0)

theorem actual_returned_original_unit_normalizations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (allLogInverse ⟶
      distanceBounded (fstT (run (var 0) (var 1))) (sndT (sndT (run (var 0) (var 1)))) (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1)) ⋏
      distanceBounded (fstT (sndT (run (var 0) (var 1)))) (sndT (sndT (run (var 0) (var 1)))) (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 2 (.impI (.andI (returned_P_distance _ _ Prf.hyp0) (returned_Gamma_distance _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNormalization
