import IPRADerivations.Analysis.Trigonometry.Cyclic.GaussianCyclicHalfAngleAgreement
import IPRADerivations.Analysis.Trigonometry.Cyclic.GaussianCyclicChordSquare
import IPRADerivations.Analysis.Trigonometry.Cyclic.GaussianCyclicExponentialSeparation

/-!
# Supplementary cyclic sine observations

At modulus `2m`, the half-angle exponentials for complementary
indices multiply to the original negative unit. The imaginary
components therefore agree with a uniform cofinal error.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianCyclicSineSupplement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCyclicExponentialRoots (source sample sample_bound sampleRadius rootF rootData root_regular angleF angleData angle_input)
open GaussianCyclicExponentialGroup (productF productData product_index_cross)
open GaussianCyclicExponentialSamples (product_error inverse_error inverseBudget sampleBound)
open GaussianCyclicFullHalfAngle (half_source)
open GaussianCyclicHalfAngleAgreement (endpoint_exp_cross)
open GaussianCyclicAngleAxis (imaginary_samples)
open GaussianCyclicChordSquare (realSine)
open GaussianArctangentExponentialPeriod (fullTurnRadius minusOne minusOneCode)
open GaussianNamedPositiveExponentialOrder (real_order_at)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianNameEquivalence (diagonal_at cross_to_diagonal)
open GaussianGammaCanonicalExponent (constant_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianRationalNormSquareTransport (value)
open GaussianRationalImaginaryChord (sine)
open GaussianRationalConjugation (point point_represents point_bound)
open GaussianRationalHorner (qmul qmul_canonical canonical_unique ofGaussian_represents ofGaussian_canonical represents_congr
  scalar_congr)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalValueEquality (commonDen leftValue rightValue common_den_positive common_left_represents common_right_represents)
open GaussianRationalMetric (bounded distanceBounded bounded_difference_iff qnegative qnegative_represents qnegative_canonical)
open GaussianRationalReciprocal (qone conjugate re_conjugate im_conjugate)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRootAlgebra (equal equal_of_values re_neg im_neg re_one im_one re_sub im_sub)
open ComplexLogarithmRemainder (neg normSq oneCode re im eval_re_code eval_im_code normSq_eval)
open RationalGaussianEmbedding (native embed_from_representation embed_canonical)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def productError : PTm n := num 4+num 4*sampleRadius
def unitError : PTm n := two*sampleRadius+inverseBudget fullTurnRadius
def supplementError : PTm n := sampleRadius*(unitError+productError)

private theorem minus_one_recode : Γ ⊢[PRAAx] (minusOne : PTm n) ≐ qnegative qone := by
  have e : Γ ⊢[PRAAx] equal minusOneCode (ComplexLogarithmRemainder.neg oneCode) := by
    apply equal_of_values <;> simp only [minusOneCode,eval_re_code,eval_im_code,ZT.toZ_sub,ZT.toZ_ofNat,re_neg,im_neg,
      re_one,im_one] <;> ipra_simps <;> ring
  exact canonical_unique _ _ _ one (ofGaussian_canonical _ _ (le_refl one)) (qnegative_canonical _)
    (le_refl one) (represents_congr (.eqRefl _) e (.eqRefl _) (ofGaussian_represents _ _ (le_refl one)))
    (qnegative_represents _ _ _ (ofGaussian_represents _ _ (le_refl one)))

private theorem sine_conjugate_negative (q : PTm n) :
    Γ ⊢[PRAAx] sine (qnegative (point q)) ≐ sine q := by
  let a := rawGaussian q
  let E := rawDen q
  have hE := raw_den_positive (Γ := Γ) q
  have h := raw_represents (Γ := Γ) q
  have r := qnegative_represents _ _ _ (point_represents _ _ _ hE h)
  have e : Γ ⊢[PRAAx] ZT.eq (im (ComplexLogarithmRemainder.neg (conjugate a))) (im a) := by
    apply ZT.derive
    simp [im_neg,im_conjugate]
  exact canonical_unique _ _ _ E (embed_canonical _) (embed_canonical _) hE
    (embed_from_representation _ _ _ (scalar_congr (.eqRefl _) e (.eqRefl _) r.andE₂))
    (embed_from_representation _ _ _ h.andE₂)

private theorem imaginary_difference_norm_le (a b : PTm n) : Γ ⊢[PRAAx]
    le (normSq (GaussianRootAlgebra.sub (native (im a)) (native (im b)))) (normSq (GaussianRootAlgebra.sub a b)) := by
  refine le_of_eq_add (d := normSq (ComplexLogarithmRemainder.code (ZT.ofNat zero) (re (GaussianRootAlgebra.sub a b)))) ?_
  apply deriveNat
  ipra_simps
  simp only [normSq_eval,re_sub,im_sub,native,eval_re_code,eval_im_code,ZT.toZ_ofNat]
  ipra_simps
  ring

private theorem imaginary_projection_distance (a b A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded a b A B) : Γ ⊢[PRAAx] distanceBounded (sine a) (sine b) A B := by
  let E := commonDen a b
  let g := leftValue a b
  let k := rightValue a b
  have hE := common_den_positive (Γ := Γ) a b
  have hg := common_left_represents (Γ := Γ) a b
  have hk := common_right_represents (Γ := Γ) a b
  have old := (bounded_difference_iff a b g k E A B hE hB hg hk).iffMp h
  apply (bounded_difference_iff _ _ _ _ E A B hE hB
    (embed_from_representation _ _ _ hg.andE₂) (embed_from_representation _ _ _ hk.andE₂)).iffMpr
  exact le_trans (le_mul_mono (le_refl _) (imaginary_difference_norm_le g k)) old

private theorem conjugate_unit_error (p r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] distanceBounded (value (sample p r m x)) qone unitError (unit p) := by
  let a := angleData r m x
  let u := sample p r m x
  let v := ap2 (GaussianRadiusExponentialName.nameF (negativeF angleF)) p
    (GaussianRadiusExponentialName.data fullTurnRadius (negativeData a))
  have hp := unit_positive (Γ := Γ) p
  have hi := angle_input r m x h
  have c := GaussianImaginaryNameConjugation.negative_exponential_conjugate_cross angleF fullTurnRadius a hi
    (imaginary_samples r m x h.andE₁)
  have d : Γ ⊢[PRAAx] distanceBounded v (point u) two (unit p) :=
    distance_congr (.eqRefl _) (GaussianNameConjugation.sample_at rootF p (rootData r m x)) (.eqRefl _) (.eqRefl _)
      (diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ c))
  exact distance_triangle_same _ _ _ _ _ _ hp
    (distance_congr (.eqRefl _) (.eqRefl _) (mul_comm _ _) (.eqRefl _)
      (multiply_distance u (point u) v sampleRadius two (unit p) hp (sample_bound p r m x h)
        (distance_symmetric _ _ _ _ hp d)))
    (inverse_error angleF fullTurnRadius a p hi)

private theorem complement_product (p r s m x : PTm n)
    (hr : Γ ⊢[PRAAx] source r m) (hs : Γ ⊢[PRAAx] source s m) (h : Γ ⊢[PRAAx] r+s ≐ m) :
    Γ ⊢[PRAAx] distanceBounded (qmul (sample p r (two*m) x) (sample p s (two*m) x)) minusOne productError (unit p) := by
  let M := two*m
  let a := rootData r M x
  let b := rootData s M x
  let hs' := half_source s m hs
  let hr' := half_source r m hr
  have ht := half_source m m (Γ := Γ) (.andI hr.andE₁ (le_refl _))
  have hu : Γ ⊢[PRAAx] source (r+s) M := .andI ht.andE₁ (le_congr h.eqSymm (.eqRefl _) ht.andE₂)
  have hp := unit_positive (Γ := Γ) p
  have near := product_error rootF rootF a b p sampleRadius sampleRadius (root_regular r M x hr') (root_regular s M x hs')
    (fun t => sample_bound t r M x hr') (fun t => sample_bound t s M x hs')
  have prod := product_index_cross r s M x hr' hs' hu
  have rate := distance_congr (.eqRefl _) (GaussianCyclicExponentialSeparation.sample_index_congr p M x h)
    (.eqRefl _) (.eqRefl _) (diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ prod))
  have last := distance_congr (.eqRefl _) (constant_at p minusOne) (.eqRefl _) (.eqRefl _)
    (diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ (endpoint_exp_cross m x hr.andE₁)))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold productError; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp (distance_symmetric _ _ _ _ hp near)
      (distance_triangle_same _ _ _ _ _ _ hp rate last))

theorem supplementary_sine_distance (p r s m x : PTm n)
    (hr : Γ ⊢[PRAAx] source r m) (hs : Γ ⊢[PRAAx] source s m) (h : Γ ⊢[PRAAx] r+s ≐ m) :
    Γ ⊢[PRAAx] distanceBounded (realSine p r m x) (realSine p s m x) supplementError (unit p) := by
  let M := two*m
  let u := sample p r M x
  let v := sample p s M x
  let w := point v
  let U := unit p
  have hp := unit_positive (Γ := Γ) p
  have hu := sample_bound p r M x (half_source r m hr)
  have hv := sample_bound p s M x (half_source s m hs)
  have canon := GaussianRadiusExponentialName.sample_canonical (Γ := Γ) angleF fullTurnRadius p (angleData r M x)
  have first := distance_congr (qmul_one_right u canon) (qmul_associative u v w).eqSymm
    (.eqRefl _) (.eqRefl _) (multiply_distance u qone (qmul v w) sampleRadius unitError U hp hu
      (distance_symmetric _ _ _ _ hp (conjugate_unit_error p s M x (half_source s m hs))))
  have terminal : Γ ⊢[PRAAx] qmul w minusOne ≐ qnegative w :=
    (qmul_commutative _ _).eqTrans ((qmul_congr minus_one_recode (.eqRefl _)).eqTrans
      (GaussianRationalMatrixFiniteSums.negative_as_minusOne w).eqSymm)
  have last := distance_congr (qmul_commutative w (qmul u v)) terminal (.eqRefl _) (.eqRefl _)
    (multiply_distance w (qmul u v) minusOne sampleRadius productError U hp
      (point_bound _ _ _ (le_refl _) hv) (complement_product p r s m x hr hs h))
  have joined := distance_triangle_same _ _ _ _ _ _ hp first last
  exact distance_congr (.eqRefl _) (sine_conjugate_negative v) (by unfold supplementError; ipra_ring) (.eqRefl _)
    (imaginary_projection_distance _ _ _ _ hp joined)

end LeanProofs.IPRA.Analysis.GaussianCyclicSineSupplement
