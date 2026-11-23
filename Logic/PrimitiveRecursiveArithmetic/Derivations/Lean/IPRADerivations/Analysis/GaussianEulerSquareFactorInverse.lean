import IPRADerivations.Analysis.GaussianEulerSquareIntegrand

/-!
# The actual reciprocal of the quadratic Euler factor

The inverse is the original normalized product of the constant one half
and the unchanged positive-scaling inverse exponential. Its true product
clock, source-derived bound, inverse identity and cancellation are retained.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSquareFactorInverse

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositiveScalingConstant (source scaleF scaleData inverseF inverseData exponentData)
open GaussianEulerSquareIntegrand (factorF factorData)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast multiplyModulus)
open GaussianNameRingLaws (oneF one_fast multiply_associative multiply_commutative)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_at)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul qmul_canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def half : PTm n := fraction one two
abbrev inverseFactorF : PR 2 := multiplyF constantF inverseF
def inverseFactorData (z B c d : PTm n) : PTm n := multiplyData constantF inverseF half (inverseData z B c d)
def inverseClock (p z B c d : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (multiplyModulus constantF inverseF half (inverseData z B c d)) p
def inverseBound (z B c d : PTm n) : PTm n := GaussianEulerPositiveScalingConstant.inverseBound z B c d

@[simp] theorem subst_half {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (half : PTm n) = half := by simp [half]
@[simp] theorem subst_inverseFactorData {m : ℕ} (σ : Fin n → PTm m) (z B c d : PTm n) :
    Syn.subst σ (inverseFactorData z B c d) = inverseFactorData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ c) (Syn.subst σ d) := by simp [inverseFactorData]
@[simp] theorem subst_inverseClock {m : ℕ} (σ : Fin n → PTm m) (p z B c d : PTm n) :
    Syn.subst σ (inverseClock p z B c d) = inverseClock (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ c) (Syn.subst σ d) := by simp [inverseClock]
@[simp] theorem subst_inverseBound {m : ℕ} (σ : Fin n → PTm m) (z B c d : PTm n) :
    Syn.subst σ (inverseBound z B c d) = inverseBound (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ c) (Syn.subst σ d) := by simp [inverseBound]

theorem factor_regular (z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx] pointCN factorF (factorData z B c d) :=
  multiply_fast constantF scaleF _ _ (constant_regular _) (GaussianEulerPositiveScalingCancellation.scale_regular z B c d h)

theorem inverse_regular (z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx] pointCN inverseFactorF (inverseFactorData z B c d) :=
  multiply_fast constantF inverseF _ _ (constant_regular _) (GaussianEulerPositiveScalingConstant.inverse_regular z B c d h)

theorem inverse_sample_at (p z B c d : PTm n) : Γ ⊢[PRAAx]
    ap2 inverseFactorF p (inverseFactorData z B c d) ≐
      qmul half (ap2 inverseF (inverseClock p z B c d) (inverseData z B c d)) :=
  (GaussianNameArithmetic.multiply_at constantF inverseF half (inverseData z B c d) p).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qmul_congr (constant_at _ _) (.eqRefl _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _)))

theorem inverse_sample_bound (p z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx]
    bounded (ap2 inverseFactorF p (inverseFactorData z B c d)) (inverseBound z B c d) one := by
  have hb : Γ ⊢[PRAAx] bounded (half : PTm n) one one :=
    GaussianEulerExponentCompactBounds.fraction_bound one two one (zero_lt_succ one)
      (le_of_eq_add (d := one) (by ipra_ring))
  have hi := GaussianEulerPositiveScalingConstant.inverse_sample_bound (inverseClock p z B c d) z B c d h
  exact GaussianRationalReciprocal.bound_congr (inverse_sample_at p z B c d).eqSymm (by unfold inverseBound; ipra_ring) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) hb hi)

theorem inverse_bound_positive (z B c d : PTm n) : Γ ⊢[PRAAx] le one (inverseBound z B c d) :=
  GaussianNameBounds.U_positive inverseF (inverseData z B c d)

theorem all_inverse_samples_bounded (z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx]
    GaussianNamedMultiplyRate.sampleBound inverseFactorF (inverseFactorData z B c d) (inverseBound z B c d) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift B) (Syn.shift c) (Syn.shift d) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [GaussianNamedMultiplyRate.sampleBound,subst_inverseFactorData,subst_inverseBound,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    inverse_sample_bound (var 0) (Syn.shift z) (Syn.shift B) (Syn.shift c) (Syn.shift d) hs

private theorem commute_left (f g h : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hh : Γ ⊢[PRAAx] pointCN h z) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF f (multiplyF g h)) (multiplyF g (multiplyF f h))
      (multiplyData f (multiplyF g h) x (multiplyData g h y z))
      (multiplyData g (multiplyF f h) y (multiplyData f h x z)) := by
  have permute := multiply_cross (multiplyF f g) (multiplyF g f) h h
    (multiplyData f g x y) (multiplyData g f y x) z z (multiply_fast _ _ _ _ hf hg)
    (multiply_fast _ _ _ _ hg hf) hh hh (multiply_commutative f g x y hf hg) (cross_refl _ _ hh)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative f g h x y z hf hg hh))
    (cross_trans _ _ _ _ _ _ permute (multiply_associative g f h y x z hg hf hh))

private theorem half_times_two : Γ ⊢[PRAAx] qmul (half : PTm n) (fraction two one) ≐ GaussianRationalSyntheticDivision.qone := by
  have htwo := zero_lt_succ (Γ := Γ) (one : PTm n)
  have prod := GaussianEulerDampedTimeRate.fraction_product one two two one htwo (le_refl one)
  have cancelled : Γ ⊢[PRAAx] fraction (one*two) (two*one) ≐ fraction one one :=
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (.eqRefl _)).eqTrans
      (GaussianCompactRiemannSplit.fraction_cancel two one one htwo (le_refl one))
  have single : Γ ⊢[PRAAx] fraction (one : PTm n) one ≐ GaussianRationalSyntheticDivision.qone :=
    GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one))
      GaussianRationalSyntheticDivision.qone_canonical (le_refl one) (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl one))
      (GaussianRationalReciprocal.qone_represents_scaled one)
  exact prod.eqTrans (cancelled.eqTrans single)

private theorem constant_one (x : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent constantF oneF (GaussianRationalSyntheticDivision.qone : PTm n) x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular _) (one_fast _)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,GaussianRationalSyntheticDivision.subst_qone,Syn.shift] using
    (constant_at (var 0) (GaussianRationalSyntheticDivision.qone : PTm (n+1))).eqTrans (GaussianNameRingLaws.one_at (var 0) (Syn.shift x)).eqSymm

private theorem half_double_product (x : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF constantF constantF) oneF (multiplyData constantF constantF half (fraction two one)) x :=
  cross_trans _ _ _ _ _ _ (GaussianGammaWeierstrassApproximant.constant_product_cross half (fraction two one))
    (cross_trans _ _ _ _ _ _ (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ half_times_two) (constant_one x))

theorem inverse_factor_product (z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF inverseFactorF factorF) oneF
      (multiplyData inverseFactorF factorF (inverseFactorData z B c d) (factorData z B c d)) (exponentData z B c d) := by
  let a : PTm n := half
  let b := inverseData z B c d
  let t : PTm n := fraction two one
  let s := scaleData z B c d
  let x := exponentData z B c d
  let ts := multiplyData constantF scaleF t s
  let is := multiplyData inverseF scaleF b s
  let doubles := multiplyData constantF constantF a t
  have ha := constant_regular (Γ := Γ) a
  have ht := constant_regular (Γ := Γ) t
  have hi := GaussianEulerPositiveScalingConstant.inverse_regular z B c d h
  have hs := GaussianEulerPositiveScalingCancellation.scale_regular z B c d h
  have hts := multiply_fast constantF scaleF t s ht hs
  have his := multiply_fast inverseF scaleF b s hi hs
  have hat := multiply_fast constantF constantF a t ha ht
  have first := multiply_associative constantF inverseF factorF a b ts ha hi hts
  have second := multiply_cross constantF constantF (multiplyF inverseF factorF) (multiplyF constantF (multiplyF inverseF scaleF))
    a a (multiplyData inverseF factorF b ts) (multiplyData constantF (multiplyF inverseF scaleF) t is) ha ha
    (multiply_fast inverseF factorF b ts hi hts) (multiply_fast constantF (multiplyF inverseF scaleF) t is ht his)
    (cross_refl _ _ ha) (commute_left inverseF constantF scaleF b t s hi ht hs)
  have third := cross_symm _ _ _ _ (multiply_associative constantF constantF (multiplyF inverseF scaleF) a t is ha ht his)
  have fourth := multiply_cross (multiplyF constantF constantF) oneF (multiplyF inverseF scaleF) oneF doubles x is x
    hat (one_fast x) his (one_fast x) (half_double_product x) (GaussianEulerPositiveScalingCancellation.inverse_scale_product z B c d h)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ second
    (cross_trans _ _ _ _ _ _ third (cross_trans _ _ _ _ _ _ fourth (GaussianNameRingLaws.multiply_one_left oneF x (one_fast x)))))

theorem factor_inverse_product (z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF factorF inverseFactorF) oneF
      (multiplyData factorF inverseFactorF (factorData z B c d) (inverseFactorData z B c d)) (exponentData z B c d) :=
  cross_trans _ _ _ _ _ _ (multiply_commutative factorF inverseFactorF _ _ (factor_regular z B c d h) (inverse_regular z B c d h))
    (inverse_factor_product z B c d h)

theorem cancel (U V : PR 2) (u v z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d)
    (hu : Γ ⊢[PRAAx] pointCN U u) (hv : Γ ⊢[PRAAx] pointCN V v)
    (he : Γ ⊢[PRAAx] crossEquivalent U (multiplyF factorF V) u (multiplyData factorF V (factorData z B c d) v)) : Γ ⊢[PRAAx]
    crossEquivalent V (multiplyF inverseFactorF U) v (multiplyData inverseFactorF U (inverseFactorData z B c d) u) := by
  let x := inverseFactorData z B c d
  let y := factorData z B c d
  have hi := inverse_regular z B c d h
  have hs := factor_regular z B c d h
  have hsv := multiply_fast factorF V y v hs hv
  have hproduct := multiply_fast inverseFactorF factorF x y hi hs
  have first := multiply_cross inverseFactorF inverseFactorF U (multiplyF factorF V)
    x x u (multiplyData factorF V y v) hi hi hu hsv (cross_refl _ _ hi) he
  have regroup := multiply_associative inverseFactorF factorF V x y v hi hs hv
  have inverse := cross_trans _ _ _ _ _ _ (inverse_factor_product z B c d h)
    (GaussianBoundedInverseApartness.ones_equivalent (exponentData z B c d) v)
  have reduce := multiply_cross (multiplyF inverseFactorF factorF) oneF V V
    (multiplyData inverseFactorF factorF x y) v v v hproduct (one_fast v) hv hv inverse (cross_refl _ _ hv)
  exact cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ first
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ regroup)
      (cross_trans _ _ _ _ _ _ reduce (GaussianNameRingLaws.multiply_one_left V v hv))))

theorem cancel_observations (U V : PR 2) (p q u v z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d)
    (hu : Γ ⊢[PRAAx] pointCN U u) (hv : Γ ⊢[PRAAx] pointCN V v)
    (he : Γ ⊢[PRAAx] crossEquivalent U (multiplyF factorF V) u (multiplyData factorF V (factorData z B c d) v)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 V p v) (ap2 (multiplyF inverseFactorF U) q (multiplyData inverseFactorF U (inverseFactorData z B c d) u))
      (GaussianCoefficientNameBounds.unit p+GaussianCoefficientNameBounds.unit q) (GaussianCoefficientNameBounds.unit p*GaussianCoefficientNameBounds.unit q) :=
  cross_at _ _ _ _ p q (cancel U V u v z B c d h hu hv he)

theorem actual_original_quadratic_factor_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶ crossEquivalent (multiplyF inverseFactorF factorF) oneF
      (multiplyData inverseFactorF factorF (inverseFactorData (var 0) (var 1) (var 2) (var 3)) (factorData (var 0) (var 1) (var 2) (var 3)))
      (exponentData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (inverse_factor_product _ _ _ _ Prf.hyp0))

theorem actual_original_quadratic_factor_cancellation_closed (U V : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 3) (var 4) (var 5) ⟶ pointCN U (var 0) ⟶ pointCN V (var 1) ⟶
      crossEquivalent U (multiplyF factorF V) (var 0)
        (multiplyData factorF V (factorData (var 2) (var 3) (var 4) (var 5)) (var 1)) ⟶
      crossEquivalent V (multiplyF inverseFactorF U) (var 1)
        (multiplyData inverseFactorF U (inverseFactorData (var 2) (var 3) (var 4) (var 5)) (var 0))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (cancel U V _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianEulerSquareFactorInverse
