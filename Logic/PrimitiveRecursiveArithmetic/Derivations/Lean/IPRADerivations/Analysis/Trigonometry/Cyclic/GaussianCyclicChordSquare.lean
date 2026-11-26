import IPRADerivations.Analysis.Trigonometry.Cyclic.GaussianCyclicAngleAxis
import IPRADerivations.Analysis.Trigonometry.Cyclic.GaussianCyclicFullHalfAngle
import IPRADerivations.Analysis.Trigonometry.Cyclic.GaussianCyclicExponentialSamples
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalImaginaryChord

/-!
# The original cyclic chord and the corresponding squared sine

The actual half-angle exponential observation has real embedded
imaginary part. It approximates the original named sine uniformly.
The squared norm of the same-precision cyclic chord approximates the
square of twice this real embedded observation.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianCyclicChordSquare

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCyclicExponentialRoots (sample sampleRadius source rootF rootData root_regular sample_bound angleF angleData angle_input)
open GaussianCyclicExponentialGroup (productF productData)
open GaussianCyclicFullHalfAngle (half_source sineSample exponential_square)
open GaussianCyclicAngleAxis (imaginary_samples)
open GaussianCyclicExponentialSamples (product_error inverse_error inverseBudget sampleBound exponential_bound)
open GaussianArctangentExponentialPeriod (fullTurnRadius)
open GaussianNamedSineFromExponential (differenceF differenceData multiplier)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianNamedSmallPerturbationTransport (productClock product_at)
open GaussianNamedSincSamples (common_late_distance)
open GaussianNameEquivalence (diagonal_at cross_to_diagonal)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianRationalHorner (qmul qmul_canonical ofGaussian_represents)
open GaussianRationalMetric (bounded distanceBounded qsub qsub_canonical bounded_of_cleared)
open GaussianRationalConjugation (point point_bound)
open GaussianRationalImaginaryChord (sine twiceSine sine_bound sine_recode conjugate_chord_square reverse_chord_square)
open GaussianRationalNormSquareTransport (value product_value)
open GaussianRationalReciprocal (qone qone_bounded bound_congr bounded_product bounded_difference bounded_sum)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianApproximateInverseDistance (multiply_distance)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def realSine (p r m x : PTm n) : PTm n := sine (sample p r (two*m) x)
def doubledSine (p r m x : PTm n) : PTm n := twiceSine (sample p r (two*m) x)
def chord (p r m x : PTm n) : PTm n := qsub qone (sample p r m x)

def chordRadius : PTm n := one+sampleRadius
def twiceSineRadius : PTm n := two*sampleRadius
def sineSquareRadius : PTm n := twiceSineRadius*twiceSineRadius
def compareRadius : PTm n := sampleRadius*(sampleRadius+sampleRadius)
def chordError : PTm n := num 4+num 10*sampleRadius
def unitError : PTm n := two+num 6*sampleRadius
def squareError : PTm n :=
  (chordRadius+compareRadius)*chordError+sineSquareRadius*unitError

@[simp] theorem subst_realSine {L : ℕ} (σ : Fin n → PTm L) (p r m x : PTm n) :
    Syn.subst σ (realSine p r m x) = realSine (Syn.subst σ p) (Syn.subst σ r) (Syn.subst σ m) (Syn.subst σ x) := by
  simp [realSine]

@[simp] theorem subst_doubledSine {L : ℕ} (σ : Fin n → PTm L) (p r m x : PTm n) :
    Syn.subst σ (doubledSine p r m x) = doubledSine (Syn.subst σ p) (Syn.subst σ r) (Syn.subst σ m) (Syn.subst σ x) := by
  simp [doubledSine]

@[simp] theorem subst_chord {L : ℕ} (σ : Fin n → PTm L) (p r m x : PTm n) :
    Syn.subst σ (chord p r m x) = chord (Syn.subst σ p) (Syn.subst σ r) (Syn.subst σ m) (Syn.subst σ x) := by
  simp [chord]

private theorem multiplier_bound : Γ ⊢[PRAAx] bounded (multiplier : PTm n) one one := by
  let a := ComplexLogarithmRemainder.neg (GaussianArctangentCayleyValues.imaginaryCode : PTm n)
  have e : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq a ≐ one := by
    dsimp only [a]
    apply deriveNat
    rw [ComplexLogarithmRemainder.normSq_eval]
    simp only [GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg,GaussianArctangentCayleyValues.imaginaryCode,
      ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
    ipra_simps
    ring
  have h2 : Γ ⊢[PRAAx] le one two := le_succ_self _
  apply bounded_of_cleared multiplier a two one one h2 (le_refl _) (ofGaussian_represents _ _ h2)
  exact le_congr ((congrMul (.eqRefl _) e).eqTrans (by ipra_ring)).eqSymm (by ipra_ring)
    (by ipra_le 3 : Γ ⊢[PRAAx] le one (two*two))

theorem real_sine_bound (p r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] bounded (realSine p r m x) sampleRadius one :=
  sine_bound _ _ (sample_bound _ _ _ _ (half_source r m h))

theorem doubled_sine_bound (p r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] bounded (doubledSine p r m x) twiceSineRadius one := by
  have hs := real_sine_bound p r m x h
  exact bound_congr (.eqRefl _) (by unfold twiceSineRadius; ipra_ring) (by ipra_ring)
    (bounded_sum _ _ _ _ _ _ (le_refl one) (le_refl one) hs hs)

theorem chord_bound (p r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] bounded (chord p r m x) chordRadius one :=
  bound_congr (.eqRefl _) (by unfold chordRadius; ipra_ring) (by ipra_ring)
    (bounded_difference _ _ _ _ _ _ (le_refl one) (le_refl one) qone_bounded (sample_bound p r m x h))

private theorem conjugate_error (p r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (GaussianRadiusExponentialName.nameF (negativeF angleF)) p
        (GaussianRadiusExponentialName.data fullTurnRadius (negativeData (angleData r m x))))
      (point (sample p r m x)) two (unit p) := by
  let a := angleData r m x
  have hi := angle_input r m x h
  have hc := GaussianImaginaryNameConjugation.negative_exponential_conjugate_cross angleF fullTurnRadius a hi
    (imaginary_samples r m x h.andE₁)
  exact distance_congr (.eqRefl _) (GaussianNameConjugation.sample_at rootF p (rootData r m x))
    (.eqRefl _) (.eqRefl _) (diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ hc))

theorem sine_error (p r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] distanceBounded (sineSample p r m x) (realSine p r m x) (num 10) (unit p) := by
  let M := two*m
  let a := angleData r M x
  let S := differenceF angleF
  let y := differenceData fullTurnRadius a
  let b := rootData r M x
  let G := GaussianRadiusExponentialName.nameF (negativeF angleF)
  let c := GaussianRadiusExponentialName.data fullTurnRadius (negativeData a)
  let u := sample p r M x
  let v := ap2 G p c
  let t := productClock constantF S multiplier y p
  have hM := half_source r m h
  have hi := angle_input r M x hM
  have hf := root_regular r M x hM
  have hg := GaussianRadiusExponentialName.name_regular _ _ _
    (GaussianExponentialInverse.negative_input _ _ _ hi)
  have hs := GaussianNamedDifference.name_regular _ _ _ _ hf hg
  have hp := unit_positive (Γ := Γ) p
  have s' : Γ ⊢[PRAAx] sineSample p r m x ≐ qmul multiplier (ap2 S t y) :=
    (product_at constantF S multiplier y p).eqTrans (qmul_congr (constant_at t _) (.eqRefl _))
  have late := common_late_distance S y p t p hs (le_add_right _ _) (le_refl _)
  have first := distance_congr s'.eqSymm (.eqRefl _) (one_mul two) (.eqRefl _)
    (multiply_distance multiplier _ _ one two (unit p) hp multiplier_bound late)
  have step := GaussianNamedDifference.sample_error rootF G b c p hf hg
  have diff := distance_congr (.eqRefl _) (.eqRefl _) (zero_add two) (.eqRefl _)
    (GaussianNamedDifference.difference_distance u u v (point u) _ _ _ hp
      (distance_refl_zero u (unit p) hp) (conjugate_error p r M x hM))
  have mid := distance_triangle_same _ _ _ _ _ _ hp step diff
  have last := distance_congr (.eqRefl _) (sine_recode u) (one_mul _) (.eqRefl _)
    (multiply_distance multiplier _ _ one _ (unit p) hp multiplier_bound mid)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp first last)

private theorem raw_unit_error (p r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] distanceBounded (value (sample p r m x)) qone unitError (unit p) := by
  let u := sample p r m x
  let a := angleData r m x
  let v := ap2 (GaussianRadiusExponentialName.nameF (negativeF angleF)) p
    (GaussianRadiusExponentialName.data fullTurnRadius (negativeData a))
  have hp := unit_positive (Γ := Γ) p
  have d := GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ hp
    (conjugate_error p r m x h)
  have first := multiply_distance u (point u) v sampleRadius two (unit p) hp (sample_bound p r m x h) d
  have inv := inverse_error angleF fullTurnRadius a p (angle_input r m x h)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold unitError inverseBudget sampleRadius sampleBound; ipra_ring)
    (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ hp first inv)

private theorem raw_chord_error (p r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] distanceBounded (qsub (sample p r m x) qone)
      (qmul (sample p r (two*m) x) (qsub (sample p r (two*m) x) (point (sample p r (two*m) x))))
      chordError (unit p) := by
  let M := two*m
  let b := rootData r M x
  let u := sample p r M x
  have hM := half_source r m h
  have hr := root_regular r M x hM
  have hp := unit_positive (Γ := Γ) p
  have sq := diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ (exponential_square r m x h))
  have approx := product_error rootF rootF b b p sampleRadius sampleRadius hr hr
    (fun t => sample_bound t r M x hM) (fun t => sample_bound t r M x hM)
  have near := distance_triangle_same _ _ _ _ _ _ hp (distance_symmetric _ _ _ _ hp sq) approx
  have inv := distance_symmetric _ _ _ _ hp (raw_unit_error p r M x hM)
  exact distance_congr (.eqRefl _) (GaussianRationalRoundedPower.multiplication_difference u u (point u))
    (by unfold chordError unitError; ipra_ring) (.eqRefl _)
    (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hp near inv)

theorem square_error (p r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] distanceBounded (value (chord p r m x))
      (qmul (doubledSine p r m x) (doubledSine p r m x)) squareError (unit p) := by
  let M := two*m
  let u := sample p r M x
  let v := qsub u (point u)
  let d := qsub (sample p r m x) qone
  let H := sampleRadius (n := n)
  let Q := qmul (doubledSine p r m x) (doubledSine p r m x)
  have hp := unit_positive (Γ := Γ) p
  have hu := sample_bound p r M x (half_source r m h)
  have hd : Γ ⊢[PRAAx] bounded d chordRadius one :=
    bound_congr (.eqRefl _) (by unfold chordRadius; ipra_ring) (by ipra_ring)
      (bounded_difference _ _ _ _ _ _ (le_refl one) (le_refl one) (sample_bound p r m x h) qone_bounded)
  have hv : Γ ⊢[PRAAx] bounded v (H+H) one :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (bounded_difference _ _ _ _ _ _ (le_refl one) (le_refl one) hu (point_bound _ _ _ (le_refl one) hu))
  have hcomp : Γ ⊢[PRAAx] bounded (qmul u v) compareRadius one :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) hu hv)
  have twice := doubled_sine_bound p r m x h
  have hQ : Γ ⊢[PRAAx] bounded Q sineSquareRadius one :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) twice twice)
  have norm_eq : Γ ⊢[PRAAx] value (qmul u v) ≐ qmul Q (value u) :=
    (product_value u v).eqTrans ((qmul_congr (.eqRefl _) (conjugate_chord_square u)).eqTrans
      (GaussianRationalPowerAlgebra.qmul_commutative _ _))
  have first := distance_congr (reverse_chord_square (sample p r m x) qone) norm_eq (.eqRefl _) (.eqRefl _)
    (GaussianRationalNormSquareTransport.distance _ _ _ _ _ _ hp hd hcomp (raw_chord_error p r m x h))
  have last := distance_congr (.eqRefl _) (GaussianReciprocalHorner.qmul_one_right Q (qmul_canonical _ _))
    (.eqRefl _) (.eqRefl _)
    (multiply_distance Q _ _ sineSquareRadius unitError (unit p) hp hQ (raw_unit_error p r M x (half_source r m h)))
  exact distance_triangle_same _ _ _ _ _ _ hp first last

theorem actual_cyclic_chord_square_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 2) (var 1) ⟶ distanceBounded (value (chord (var 3) (var 2) (var 1) (var 0)))
        (qmul (doubledSine (var 3) (var 2) (var 1) (var 0)) (doubledSine (var 3) (var 2) (var 1) (var 0)))
        squareError (unit (var 3))) :=
  closeUniv 4 (.impI (square_error _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCyclicChordSquare
