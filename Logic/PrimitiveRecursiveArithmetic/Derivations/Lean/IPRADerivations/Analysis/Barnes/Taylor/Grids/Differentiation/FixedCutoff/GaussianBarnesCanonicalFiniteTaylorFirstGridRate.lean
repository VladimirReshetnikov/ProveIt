import IPRADerivations.Analysis.Barnes.Taylor.Grids.Differentiation.FixedCutoff.GaussianBarnesCanonicalFiniteTaylorFirstPolynomial
import IPRADerivations.Analysis.Barnes.Taylor.Grids.Finite.GaussianBarnesCanonicalFiniteTaylorDiskGridLimit

/-!
# Linear error in the first quotient of the original fixed Barnes grid

The first two rows of the degree-two grid have the same original finite
cutoff. Normalizing their errors leaves two powers of the displacement.
The quadratic coefficient of the polynomial adds the linear term.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorFirstGridRate

open_ipra
open ComplexLogarithmRemainder (bounded_mono normSq)
open GaussianBarnesCanonicalFiniteTaylorDiskGridLimit (analyticGain clockGain)
open GaussianBarnesCanonicalFiniteTaylorFirstPolynomial (quadraticCap)
open GaussianBarnesCanonicalFiniteTaylorGridObservations (literalGrid observationCap polynomialGrid scaledPolynomial)
open GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget (rowDenominator rowNumeratorWithGains row_denominator_positive)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor stepDivisor_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianL1 (norm1 norm1_square_le_two_normSq normSq_le_norm1_square)
open GaussianNamedDifferenceQuotient (inverse)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product qmul)
open GaussianRationalMetric (distanceBounded qsub)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def rowCost (q z h R B r : PTm n) : PTm n :=
  two+observationCap q z h R B (norm1 h) r zero two

def gain (R : PTm n) : PTm n := num 4*analyticGain R zero+two+quadraticCap R

def quotient (t z h R B r : PTm n) : PTm n :=
  qmul (inverse h B) (qsub (entry (literalGrid t z h R B r two) one) (entry (literalGrid t z h R B r two) zero))

theorem step_size (h R B : PTm n) (hs : Γ ⊢[PRAAx] le ((two*stepDivisor R)*norm1 h) B) :
    Γ ⊢[PRAAx] le (two*norm1 h) B := by
  have g := stepDivisor_positive (Γ := Γ) R
  exact le_trans (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (norm1 h) (mul_le_mul_right two g))) hs

private theorem row_error (t q z h R B r j : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hs : Γ ⊢[PRAAx] le ((two*stepDivisor R)*norm1 h) B) (hj : Γ ⊢[PRAAx] lt j (succ two)) :
    Γ ⊢[PRAAx] distanceBounded (entry (literalGrid t z h R B r two) j) (entry (polynomialGrid t q z h R B (norm1 h) r zero two) j)
      (rowNumeratorWithGains q t B (norm1 h) zero (rowCost q z h R B r) (analyticGain R zero) (clockGain R))
      (rowDenominator q t B zero) := by
  let U := unit t
  let S := R+one
  let H := norm1 h
  let C := observationCap q z h R B H r zero two
  let P := GaussianBarnesCanonicalHeadUniformMass.headCap S
  let F := GaussianBarnesCanonicalFiniteCentralDiskBound.cap S
  let A := GaussianBarnesCanonicalFiniteWeightedTaylorUniformValue.numerator q S B (two*H) zero
  let D := GaussianBarnesCanonicalFiniteWeightedTaylorValue.denominator q S B zero
  let A' := GaussianBarnesCanonicalFiniteTaylorGridBudget.numeratorWithCaps q S B H zero P F
  let D' := GaussianBarnesCanonicalFiniteTaylorGridBudget.denominator q B zero
  have cmp : Γ ⊢[PRAAx] le (A*D') (A'*D) :=
    GaussianBarnesCanonicalFiniteTaylorGridBudget.radius_comparison_with_caps q S B H zero P F
  have fit : Γ ⊢[PRAAx] le ((A*U*U+D*(U+(one+C)*U))*(D'*U)) ((A'*U+D'*(two+C))*(D*U*U)) := by
    ipra_le 𝔞(U)*𝔞(U)*𝔞(U)*sl cmp
  exact distance_radius_mono _ _ _ _ _ _
    (GaussianBarnesCanonicalFiniteTaylorGridObservations.denominator_positive t t q R B zero hz.andE₁)
    (row_denominator_positive q t B zero hz.andE₁) fit
    (GaussianBarnesCanonicalFiniteTaylorGridUniformObservations.row_error t t q z h R B H r zero two j hz
      (normSq_le_norm1_square h) hs hj)

private theorem cube (N : PTm n) : Γ ⊢[PRAAx] pw N (succ two) ≐ N*N*N :=
  (pw_succ N two).eqTrans (congrMul
    ((pw_succ N one).eqTrans (congrMul ((pw_succ N zero).eqTrans
      ((congrMul (pw_zero N) (.eqRefl N)).eqTrans (one_mul N))) (.eqRefl N))) (.eqRefl N))

private theorem grid_budget (q t B H K A C : PTm n) (hH : Γ ⊢[PRAAx] le one H) (hHB : Γ ⊢[PRAAx] le H B)
    (hq : Γ ⊢[PRAAx] le (num 4*(B*B)*C) (unit q)) (ht : Γ ⊢[PRAAx] le (num 4*(B*B)*K) (unit t)) :
    let X := rowNumeratorWithGains q t B H zero K A C
    let Y := rowDenominator q t B zero
    Γ ⊢[PRAAx] le (((two*B)*(X+X))*B) (((num 4*A+two)*H)*(H*Y)) := by
  let U := unit q
  let T := unit t
  have hHH : Γ ⊢[PRAAx] le one (H*H) := positive_product _ _ hH hH
  have eqH := natEq (cube (Γ := Γ) H)
  have eqB := natEq (cube (Γ := Γ) B)
  dsimp only
  change Γ ⊢[PRAAx] le
    (((two*B)*(((A*pw H (succ two)*U+C*pw B (succ two))*T+(pw B (succ two)*U)*K)+
      ((A*pw H (succ two)*U+C*pw B (succ two))*T+(pw B (succ two)*U)*K)))*B)
    (((num 4*A+two)*H)*(H*((pw B (succ two)*U)*T)))
  ipra_le
    (4*𝔞(A)*𝔞(H)*𝔞(H)*𝔞(B)*𝔞(B)*𝔞(U)*𝔞(T))*sl hHB+
    (𝔞(B)*𝔞(B)*𝔞(B)*𝔞(T))*sl hq+
    (𝔞(B)*𝔞(B)*𝔞(B)*𝔞(U))*sl ht+
    (2*𝔞(B)*𝔞(B)*𝔞(B)*𝔞(U)*𝔞(T))*sl hHH using
    rw [eqH,eqB]
    ring

theorem to_linear (t q z h R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hs : Γ ⊢[PRAAx] le ((two*stepDivisor R)*norm1 h) B)
    (hq : Γ ⊢[PRAAx] le (num 4*(B*B)*clockGain R) (unit q))
    (ht : Γ ⊢[PRAAx] le (num 4*(B*B)*rowCost q z h R B r) (unit t)) :
    Γ ⊢[PRAAx] distanceBounded (quotient t z h R B r)
      (entry (scaledPolynomial t q z R B (norm1 h) r zero two) one) (gain R*norm1 h) B := by
  let H := norm1 h
  let X := rowNumeratorWithGains q t B H zero (rowCost q z h R B r) (analyticGain R zero) (clockGain R)
  let Y := rowDenominator q t B zero
  let p := polynomialGrid t q z h R B H r zero two
  let v := literalGrid t z h R B r two
  let x := quotient t z h R B r
  let y := qmul (inverse h B) (qsub (entry p one) (entry p zero))
  let z' := entry (scaledPolynomial t q z R B H r zero two) one
  have hb := hz.andE₁
  have hp := positive_product two B (le_succ_self one) hb
  have hH := GaussianNativeDerivativeQuotientRate.norm1_positive h hn
  have hY := row_denominator_positive q t B zero hb
  have hHB : Γ ⊢[PRAAx] le H B := le_trans (le_congr (one_mul H) (.eqRefl _) (mul_le_mul_right H (le_succ_self one)))
    (step_size h R B hs)
  have hl : Γ ⊢[PRAAx] GaussianRationalLowerBounds.lower (ofGaussian h B) H (two*B) := by
    apply GaussianRationalLowerBounds.lower_from_representation _ h B _ _ hb hp (ofGaussian_represents h B hb)
    have hsq := norm1_square_le_two_normSq (Γ := Γ) h
    ipra_le 𝔞(B)*𝔞(B)*(sl hsq+2*𝔞(normSq h))
  have inv := GaussianRationalLowerBounds.inverse_bound _ _ _ hH hp hl
  have d := GaussianNamedDifference.difference_distance (entry v one) (entry p one) (entry v zero) (entry p zero) X X Y hY
    (row_error t q z h R B r one hz hs (le_succ_self two)) (row_error t q z h R B r zero hz hs (zero_lt_succ two))
  have prod := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hH hY inv d
  have raw : Γ ⊢[PRAAx] distanceBounded x y ((two*B)*(X+X)) (H*Y) :=
    GaussianRationalReciprocal.bound_congr
      (GaussianRationalRoundedPower.multiplication_difference (inverse h B) _ _).eqSymm (.eqRefl _) (.eqRefl _) prod
  have first : Γ ⊢[PRAAx] distanceBounded x y ((num 4*analyticGain R zero+two)*H) B :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hH hY) hb (grid_budget q t B H _ _ _ hH hHB hq ht) raw
  have wide : Γ ⊢[PRAAx] source z (R+one) B :=
    .andI hb (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by ipra_ring)))
  have last : Γ ⊢[PRAAx] distanceBounded y z' (quadraticCap R*H) B :=
    GaussianBarnesCanonicalFiniteTaylorFirstPolynomial.to_linear t q z h R B H r wide (.andI hb hn) (normSq_le_norm1_square h)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold gain; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hb first last)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorFirstGridRate
