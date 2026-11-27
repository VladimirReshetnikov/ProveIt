import IPRADerivations.Analysis.Trigonometry.Cyclic.ExponentialRoots.GaussianCyclicExponentialSamples
import IPRADerivations.Analysis.Trigonometry.Cyclic.SineProducts.GaussianCyclicHalfSineMargin

/-!
# A sampled chord from a positive half-angle sine

The exact half-angle exponential square and the inverse product give
a finite comparison of the cyclic root minus one with
(e^{i\theta}(2i\sin\theta)). All observations are the original names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCyclicRootChord

open_ipra
open GaussianCyclicExponentialRoots (rootF rootData sample)
open GaussianCyclicRootHalfAngle (positiveData exponential_square)
open GaussianCyclicHalfSineMargin (sineSample sine_lower_at)
open GaussianCyclicExponentialSamples (sampleBound product_error exponential_bound
  inverse_error inverseBudget exponential_lower lower_under_half_error)
open GaussianArctangentExponentialPeriod (twiceImaginary)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianArctangentDivisionAngles (source)
open GaussianNamedSineFromExponential (sineF sineData differenceF differenceData multiplier)
open GaussianNamedSincSamples (common_late_distance)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianNameEquivalence (cross_diagonal_at)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNamedSmallPerturbationTransport (product_at productClock)
open GaussianRationalHorner (qmul qmul_canonical positive_product qmul_represents ofGaussian_represents
  represents_congr canonical_unique)
open GaussianRationalMetric (bounded distanceBounded qsub bounded_of_cleared)
open GaussianRationalReciprocal (qone qone_represents_scaled bound_congr)
open GaussianRationalSyntheticDivision (qmul_congr qone_canonical)
open GaussianRationalLowerBounds (lower lower_from_representation product_lower name_lower)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianReciprocalHorner (qmul_associative)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRootAlgebra (equal_of_values re_mul im_mul re_scale im_scale re_neg im_neg re_one im_one)
open ComplexLogarithmRemainder (scale oneCode normSq normSq_eval eval_re_code eval_im_code)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "D" => GaussianArctangentDivisionAngles.nameF
local notation "E" => GaussianRadiusExponentialName.nameF

def budget : PTm n := num 4+num 24*sampleBound two
def phaseDenominator (m : PTm n) : PTm n := (two*sampleBound two)*m
def denominator (m : PTm n) : PTm n := two*phaseDenominator m
def reserve (m : PTm n) : PTm n :=
  two*m+two*inverseBudget two+denominator m*budget

ipra_subst reserve [denominator, phaseDenominator, budget]

private theorem multiplier_bound : Γ ⊢[PRAAx] bounded (multiplier : PTm n) one one := by
  let a := ComplexLogarithmRemainder.neg (imaginaryCode : PTm n)
  have e : Γ ⊢[PRAAx] normSq a ≐ one := by
    dsimp only [a]
    apply deriveNat
    rw [normSq_eval]
    simp only [re_neg,im_neg,imaginaryCode,eval_re_code,eval_im_code,ZT.toZ_ofNat]
    ipra_simps
    ring
  have h2 : Γ ⊢[PRAAx] le one two := le_succ_self _
  apply bounded_of_cleared multiplier a two one one h2 (le_refl _) (ofGaussian_represents _ _ h2)
  exact le_congr ((congrMul (.eqRefl _) e).eqTrans (by ipra_ring)).eqSymm (by ipra_ring)
    (by ipra_le 3 : Γ ⊢[PRAAx] le one (two*two))

private theorem twice_norm : Γ ⊢[PRAAx] normSq (scale two (imaginaryCode : PTm n)) ≐ two*two := by
  apply deriveNat
  rw [normSq_eval]
  simp only [re_scale,im_scale,imaginaryCode,eval_re_code,eval_im_code,ZT.toZ_ofNat]
  ipra_simps
  ring
private theorem twice_bound : Γ ⊢[PRAAx] bounded (twiceImaginary : PTm n) two one :=
  bounded_of_cleared _ _ _ _ _ (le_refl _) (le_refl _) (ofGaussian_represents _ _ (le_refl _))
    (le_congr ((congrMul (.eqRefl _) twice_norm).eqTrans (by ipra_ring)).eqSymm (by ipra_ring) (le_refl (two*two)))
private theorem twice_lower : Γ ⊢[PRAAx] lower (twiceImaginary : PTm n) two one :=
  lower_from_representation _ _ _ _ _ (le_refl _) (le_refl _) (ofGaussian_represents _ _ (le_refl _))
    (le_congr (by ipra_ring) ((congrMul (.eqRefl _) twice_norm).eqTrans (by ipra_ring)).eqSymm (le_refl (two*two)))

private theorem scale_inverse : Γ ⊢[PRAAx] qmul (twiceImaginary : PTm n) multiplier ≐ qone := by
  let a := scale two (imaginaryCode : PTm n)
  let b := ComplexLogarithmRemainder.neg (imaginaryCode : PTm n)
  have h2 : Γ ⊢[PRAAx] le one two := le_succ_self _
  have h := qmul_represents (twiceImaginary : PTm n) multiplier a b one two (le_refl _) h2
    (ofGaussian_represents _ _ (le_refl _)) (ofGaussian_represents _ _ h2)
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (ComplexLogarithmRemainder.mul a b) (scale two oneCode) := by
    dsimp only [a,b]
    apply equal_of_values <;> simp only [re_mul,im_mul,re_scale,im_scale,re_neg,im_neg,re_one,im_one,
      imaginaryCode,eval_re_code,eval_im_code,ZT.toZ_ofNat] <;> ipra_simps <;> ring
  exact canonical_unique _ _ _ two (qmul_canonical _ _) qone_canonical h2
    (represents_congr (.eqRefl _) e (one_mul _) h) (qone_represents_scaled two)

private theorem sine_sample_difference (p d m x : PTm n) (h : Γ ⊢[PRAAx] source d m) :
    Γ ⊢[PRAAx] distanceBounded (sineSample p d m x)
      (qmul multiplier (qsub (ap2 (E D) p (positiveData d m x))
        (ap2 (E (negativeF D)) p (GaussianRadiusExponentialName.data two
          (negativeData (GaussianArctangentDivisionAngles.data d m x)))))) (num 8) (unit p) := by
  let a := GaussianArctangentDivisionAngles.data d m x
  let F := E D
  let G := E (negativeF D)
  let b := positiveData d m x
  let c := GaussianRadiusExponentialName.data two (negativeData a)
  let S := differenceF D
  let y := differenceData two a
  let t := productClock constantF S multiplier y p
  have hi := GaussianArctangentDivisionAngles.exponential_input d m x h
  have nf := GaussianRadiusExponentialName.name_regular D two a hi
  have ng := GaussianRadiusExponentialName.name_regular _ _ _ (GaussianExponentialInverse.negative_input _ _ _ hi)
  have sr := GaussianNamedDifference.name_regular _ _ _ _ nf ng
  have hp := unit_positive (Γ := Γ) p
  have near := common_late_distance S y p t p sr (le_add_right _ _) (le_refl _)
  have exactSample : Γ ⊢[PRAAx] sineSample p d m x ≐ qmul multiplier (ap2 S t y) :=
    (product_at constantF S multiplier y p).eqTrans (qmul_congr (constant_at t _) (.eqRefl _))
  have first := distance_congr exactSample.eqSymm (.eqRefl _) (one_mul two) (.eqRefl _)
    (multiply_distance multiplier _ _ one two (unit p) hp multiplier_bound near)
  have last := distance_congr (.eqRefl _) (.eqRefl _) (one_mul (num 6)) (.eqRefl _)
    (multiply_distance multiplier _ _ one (num 6) (unit p) hp multiplier_bound
      (GaussianNamedDifference.sample_error F G b c p nf ng))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp first last)

theorem chord_error (p d m x : PTm n) (h : Γ ⊢[PRAAx] source d m) :
    Γ ⊢[PRAAx] distanceBounded (qsub (sample p d m x) qone)
      (qmul (ap2 (E D) p (positiveData d m x)) (qmul twiceImaginary (sineSample p d m x))) budget (unit p) := by
  let a := GaussianArctangentDivisionAngles.data d m x
  let b := positiveData d m x
  let F := E D
  let H := sampleBound (two : PTm n)
  let u := ap2 F p b
  let v := ap2 (E (negativeF D)) p (GaussianRadiusExponentialName.data two (negativeData a))
  let s := sineSample p d m x
  let w := qsub u v
  have hp := unit_positive (Γ := Γ) p
  have hi := GaussianArctangentDivisionAngles.exponential_input d m x h
  have hr := GaussianRadiusExponentialName.name_regular _ _ _ hi
  have product := product_error F F b b p H H hr hr (fun t => exponential_bound _ _ _ t hi) (fun t => exponential_bound _ _ _ t hi)
  have eq := exponential_square d m x h
  have head := distance_triangle_same _ _ _ _ _ _ hp
    (distance_symmetric _ _ _ _ hp (cross_diagonal_at p eq)) product
  have tail := distance_symmetric _ _ _ _ hp (inverse_error D two a p hi)
  have delta := distance_congr (.eqRefl _) (GaussianRationalRoundedPower.multiplication_difference u u v)
    (.eqRefl _) (.eqRefl _) (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hp head tail)
  have cancel : Γ ⊢[PRAAx] qmul twiceImaginary (qmul multiplier w) ≐ w :=
    (qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr scale_inverse (.eqRefl _)).eqTrans
        (GaussianPolynomialDeterminantTerms.one_mul_canonical _ (GaussianRationalMetric.qsub_canonical _ _)))
  have middle := distance_symmetric _ _ _ _ hp
    (distance_congr (.eqRefl _) cancel (.eqRefl _) (.eqRefl _)
      (multiply_distance twiceImaginary s _ two (num 8) (unit p) hp twice_bound (sine_sample_difference p d m x h)))
  have last := multiply_distance u w _ H _ (unit p) hp (exponential_bound _ _ _ p hi) middle
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold budget inverseBudget; dsimp only [H]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp delta last)

theorem root_minus_one_margin (p d m x : PTm n) (h : Γ ⊢[PRAAx] source d m)
    (hd : Γ ⊢[PRAAx] le one d) (hp : Γ ⊢[PRAAx] le (reserve m) (unit p)) :
    Γ ⊢[PRAAx] lower (qsub (sample p d m x) qone) one (denominator m) := by
  let a := GaussianArctangentDivisionAngles.data d m x
  let u := ap2 (E D) p (positiveData d m x)
  let s := sineSample p d m x
  let b := two*sampleBound (two : PTm n)
  let t := qmul u (qmul twiceImaginary s)
  let U := unit p
  have boundPositive : Γ ⊢[PRAAx] le one (sampleBound (two : PTm n)) :=
    RationalNonnegativePowers.denominator_positive _ _ (by ipra_le 2)
  have hb : Γ ⊢[PRAAx] le one b := positive_product _ _ (le_succ_self _) boundPositive
  have hm := h.andE₁
  have sinGuard : Γ ⊢[PRAAx] le (two*m) U :=
    le_trans (le_of_eq_add (d := two*inverseBudget two+denominator m*budget) (by unfold reserve; ipra_ring)) hp
  have uGuard : Γ ⊢[PRAAx] le (two*inverseBudget two) U :=
    le_trans (le_of_eq_add (d := two*m+denominator m*budget) (by unfold reserve; ipra_ring)) hp
  have ls := sine_lower_at p d m x h hd sinGuard
  have lu : Γ ⊢[PRAAx] lower u one b :=
    exponential_lower D two a p (GaussianArctangentDivisionAngles.exponential_input d m x h) uGuard
  have tw : Γ ⊢[PRAAx] lower (qmul twiceImaginary s) (two*d) m :=
    GaussianRationalLowerBounds.lower_congr (.eqRefl _) (.eqRefl _) (one_mul m)
      (product_lower _ _ _ _ _ _ (le_refl one) hm twice_lower ls)
  have low : Γ ⊢[PRAAx] lower t (two*d) (phaseDenominator m) :=
    GaussianRationalLowerBounds.lower_congr (.eqRefl _) (one_mul _) (.eqRefl _)
      (product_lower _ _ _ _ _ _ hb hm lu tw)
  have margin : Γ ⊢[PRAAx] le (denominator m*budget) ((two*d)*U) :=
    le_trans (le_trans (le_add_left _ _) hp)
      (le_congr (one_mul U) (.eqRefl _) (le_mul_mono (le_trans hd (le_of_eq_add (d := d) (by ipra_ring))) (le_refl U)))
  have hD : Γ ⊢[PRAAx] le one (phaseDenominator m) := positive_product _ _ hb hm
  exact name_lower _ _ _ (le_trans hd (le_of_eq_add (d := d) (by ipra_ring)))
    (positive_product _ _ (le_succ_self _) hD)
    (lower_under_half_error _ _ _ _ _ _ hD (unit_positive p) low (chord_error p d m x h) margin)

theorem denominator_positive (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx] le one (denominator m) :=
  positive_product _ _ (le_succ_self _) (positive_product _ _ (positive_product _ _ (le_succ_self _)
    (RationalNonnegativePowers.denominator_positive _ _ (by ipra_le 2))) hm)

end LeanProofs.IPRA.Analysis.GaussianCyclicRootChord
