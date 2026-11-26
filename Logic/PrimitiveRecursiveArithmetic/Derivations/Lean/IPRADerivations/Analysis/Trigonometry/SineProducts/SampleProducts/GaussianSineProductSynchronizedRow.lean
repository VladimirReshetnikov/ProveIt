import IPRADerivations.Analysis.Trigonometry.SineProducts.Scaling.GaussianSineProductRelativeArgument
import IPRADerivations.Analysis.Trigonometry.SineProducts.Roots.GaussianSineRawRootBinding
import IPRADerivations.Analysis.Trigonometry.SineProducts.Scaling.GaussianSineProductQuotientTransport
import IPRADerivations.Analysis.Trigonometry.Sinc.GaussianSincRatioProductRow
import IPRADerivations.Analysis.Trigonometry.SineProducts.Roots.GaussianSineSampleRootGuards
import IPRADerivations.Analysis.Trigonometry.Sinc.GaussianNamedSineSincFactorization

/-!
# Transport from the actual sampled sine row to the sinc ratio row

The original numerator sine keeps its exact name. The denominator is
the same positive finite Cayley sine used by the normalized root
product. On the first (K) rows, the reconstructed factor is within
an explicit dyadic error of the independently normalized sinc ratio.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineProductSynchronizedRow

open_ipra
open GaussianSineProductScaledArguments (nameF data observation_bound unit_disk_input natural_code_bound)
open GaussianSineProductScaledArgumentIdentity (realRootData root_sine_cross)
open GaussianSineProductRelativeArgument (relative relative_bound relative_sample_error)
open GaussianSineProductT4Budget (halfIndex multiple cutoff_le_half_index)
open GaussianArctangentDivisionAngles (modulus odd_source)
open GaussianArctangentDivisionAngleResidual (sineSample)
open GaussianArctangentDivisionSinePositive (exactSineData)
open GaussianSineRawRootBinding (raw_root_error_later)
open GaussianNamedSineTaylor (imaginaryF imaginary_input)
open GaussianNamedSineFromExponential (sineF sineData sine_regular)
open GaussianNamedSincQuadraticBounds (observationBound unit_disk_bound)
open GaussianNamedSincRatio (square_lower)
open GaussianSineProductQuotientTransport (correctedFactor corrected_factor_error)
open GaussianSineRootNormalization (normalizedFactor)
open GaussianRadiusExponentialName (input)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus)
open GaussianNameRingLaws (multiply_sample_error)
open GaussianNameEquivalence (diagonal_at cross_to_diagonal)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalLowerBounds (lower)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalPowerAlgebra (qmul_commutative qmul_shuffle)
open GaussianReciprocalHorner (qmul_associative)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same distance_symmetric)
open GaussianApproximateInverseDistance (multiply_distance)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def angleData (z R B K x : PTm n) : PTm n := data z R B (modulus (halfIndex R K)) x
def rootData (R K i x : PTm n) : PTm n := realRootData (succ i) (modulus (halfIndex R K)) x

def angleSineF : PR 2 := sineF (imaginaryF nameF)
def angleSineData (z R B K x : PTm n) : PTm n := sineData (imaginaryF nameF) one (angleData z R B K x)

def sincValue (p d : PTm n) : PTm n := ap2 (GaussianNamedSinc.nameF nameF) p (GaussianNamedSinc.data nameF one d)
def FactorBudget (d : PTm n) : PTm n :=
  multiplyModulus nameF (GaussianNamedSinc.nameF nameF) d (GaussianNamedSinc.data nameF one d)+num 3

def sampledRoot (R K i x p : PTm n) : PTm n :=
  sineSample (GaussianSineSampleRootGuards.clock p (halfIndex R K)) (succ i) (halfIndex R K) x

def actualFactor (z R B K i x p : PTm n) : PTm n :=
  normalizedFactor (ap2 angleSineF p (angleSineData z R B K x)) (sampledRoot R K i x p)
def sincFactor (z R B K i x p : PTm n) : PTm n :=
  correctedFactor (relative z B (succ i)) (sincValue p (angleData z R B K x)) (sincValue p (rootData R K i x))

def productRadius (z R B K x : PTm n) : PTm n :=
  two*(GaussianNameBounds.U angleSineF (angleSineData z R B K x)+R)
def crossCost (z R B K i x : PTm n) : PTm n :=
  two*FactorBudget (angleData z R B K x)+two*(two*((two*R)*two))+
    (two*R)*(FactorBudget (rootData R K i x)+num 11)
def budget (z R B K i x : PTm n) : PTm n :=
  ((GaussianSineSampleRootGuards.sineDenominator (halfIndex R K)*
    GaussianSineSampleRootGuards.sineDenominator (halfIndex R K))*num 4)*
    (two*productRadius z R B K x*crossCost z R B K i x)

ipra_subst angleData
ipra_subst angleSineData
ipra_subst sampledRoot
ipra_subst actualFactor
ipra_subst budget [productRadius, crossCost, FactorBudget, rootData]

theorem modulus_eq (R K : PTm n) : Γ ⊢[PRAAx] modulus (halfIndex R K) ≐ multiple R K :=
  (succ_eq_add_one _).eqTrans (GaussianSineProductT4Budget.odd_multiple R K).eqSymm

theorem argument_input (z R B K x : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] input nameF one (angleData z R B K x) ⋏
      observationBound nameF (angleData z R B K x) (num 4*R) (modulus (halfIndex R K)) := by
  let m := modulus (halfIndex R K)
  have hm : Γ ⊢[PRAAx] le one m := zero_lt_succ _
  exact .andI (unit_disk_input z R B m x hB hm hz
    (le_congr (.eqRefl _) (modulus_eq R K).eqSymm (GaussianSineProductT4Budget.argument_disk R K hR hK)))
    (observation_bound z R B m x hB hm hz)

theorem root_input (R K i x : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K) (hi : Γ ⊢[PRAAx] lt i K) :
    Γ ⊢[PRAAx] input nameF one (rootData R K i x) ⋏
      observationBound nameF (rootData R K i x) (num 4*succ i) (modulus (halfIndex R K)) := by
  let m := modulus (halfIndex R K)
  let k := succ i
  let a := ComplexLogarithmRemainder.scale k ComplexLogarithmRemainder.oneCode
  have hm : Γ ⊢[PRAAx] le one m := zero_lt_succ _
  exact .andI (unit_disk_input a k one m x (le_refl one) hm (natural_code_bound k)
    (le_congr (.eqRefl _) (modulus_eq R K).eqSymm (GaussianSineProductT4Budget.root_disk R K k hR hK hi)))
    (observation_bound a k one m x (le_refl one) hm (natural_code_bound k))

theorem sine_factor_error (d p : PTm n) (h : Γ ⊢[PRAAx] input nameF one d) :
    Γ ⊢[PRAAx] distanceBounded (ap2 angleSineF p (sineData (imaginaryF nameF) one d))
      (qmul (ap2 nameF p d) (sincValue p d)) (FactorBudget d) (unit p) := by
  let g := GaussianNamedSinc.nameF nameF
  let y := GaussianNamedSinc.data nameF one d
  let f := angleSineF
  let x := sineData (imaginaryF nameF) one d
  have c := GaussianNamedSineSincFactorization.original_sine_factors nameF one d h
  have first := diagonal_at f (multiplyF nameF g) x (multiplyData nameF g d y) p (cross_to_diagonal _ _ _ _ c)
  have next := multiply_sample_error nameF g d y p h.andE₁ (GaussianNamedSinc.name_regular nameF one d h)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold FactorBudget; dsimp only [g,y]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) first next)

private theorem root_factor_error (R K i x p : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K) (hi : Γ ⊢[PRAAx] lt i K)
    (h : Γ ⊢[PRAAx] input nameF one (rootData R K i x)) :
    Γ ⊢[PRAAx] distanceBounded (qmul (ap2 nameF p (rootData R K i x)) (sincValue p (rootData R K i x)))
      (sampledRoot R K i x p) (FactorBudget (rootData R K i x)+num 11) (unit p) := by
  let k := succ i
  let J := halfIndex R K
  let m := modulus J
  let d := rootData R K i x
  have hk := le_trans hi (cutoff_le_half_index R K hR hK)
  have hp := unit_positive (Γ := Γ) p
  have first := distance_symmetric _ _ _ _ hp (sine_factor_error d p h)
  have sinEq := root_sine_cross k m x one (odd_source k J hk) h
  have middle := diagonal_at angleSineF (sineF GaussianArctangentDivisionAngles.nameF)
    (sineData (imaginaryF nameF) one d) (exactSineData k m x) p (cross_to_diagonal _ _ _ _ sinEq)
  have last := raw_root_error_later p (GaussianSineSampleRootGuards.clock p J) k J x hk
    (GaussianSineSampleRootGuards.clock_later p J)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp first middle) last)

theorem transport (z R B K i x p : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K) (hB : Γ ⊢[PRAAx] le one B)
    (hi : Γ ⊢[PRAAx] lt i K) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] distanceBounded (actualFactor z R B K i x p) (sincFactor z R B K i x p) (budget z R B K i x) (unit p) := by
  let J := halfIndex R K
  let m := modulus J
  let k := succ i
  let D := GaussianSineSampleRootGuards.sineDenominator J
  let U := unit p
  let a := angleData z R B K x
  let d := rootData R K i x
  let x₁ := ap2 nameF p a
  let x₂ := ap2 nameF p d
  let s := sincValue p a
  let t := sincValue p d
  let u := ap2 angleSineF p (angleSineData z R B K x)
  let v := sampledRoot R K i x p
  let b := relative z B k
  let P := qmul b s
  let W := productRadius z R B K x
  let N := GaussianNameBounds.U angleSineF (angleSineData z R B K x)
  have hp := unit_positive (Γ := Γ) p
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have hm : Γ ⊢[PRAAx] le one m := zero_lt_succ _
  have hiJ : Γ ⊢[PRAAx] lt i J := le_trans hi (cutoff_le_half_index R K hR hK)
  have hu := argument_input z R B K x hR hK hB hz
  have hv := root_input R K i x hR hK hi
  have bu : Γ ⊢[PRAAx] le (num 4*R) m := le_congr (.eqRefl _) (modulus_eq R K).eqSymm
    (GaussianSineProductT4Budget.argument_disk R K hR hK)
  have bv : Γ ⊢[PRAAx] le (num 4*k) m := le_congr (.eqRefl _) (modulus_eq R K).eqSymm
    (GaussianSineProductT4Budget.root_disk R K k hR hK hi)
  have hs : Γ ⊢[PRAAx] bounded s two one := unit_disk_bound nameF one a _ m p hm bu hu.andE₂
  have ht : Γ ⊢[PRAAx] bounded t two one := unit_disk_bound nameF one d _ m p hm bv hv.andE₂
  have hb : Γ ⊢[PRAAx] bounded b R one := bounded_radius_mono _ _ _ _ _ hk (le_refl one)
    (le_mul_mono (le_refl R) hk) (relative_bound z R B k hB hk hz)
  have hP : Γ ⊢[PRAAx] bounded P (two*R) one :=
    bound_congr (.eqRefl _) (mul_comm _ _) (one_mul one) (bounded_product _ _ _ _ _ _ (le_refl _) (le_refl _) hb hs)
  have uBound : Γ ⊢[PRAAx] bounded u N one :=
    GaussianNameBounds.sample_bound _ _ p (sine_regular _ _ _ (imaginary_input _ _ _ hu.andE₁))
  have vBound : Γ ⊢[PRAAx] bounded v one one :=
    GaussianSineSampleRootList.sine_bound (GaussianSineSampleRootGuards.clock p J) k J x
  have leftBound : Γ ⊢[PRAAx] bounded (qmul u t) W one :=
    bounded_radius_mono _ _ _ _ _ (le_refl _) (le_refl _)
      (by unfold W productRadius; dsimp only [N]; ipra_le 2*𝔞 R)
      (bound_congr (.eqRefl _) (.eqRefl _) (one_mul one)
        (bounded_product _ _ _ _ _ _ (le_refl _) (le_refl _) uBound ht))
  have rightBound : Γ ⊢[PRAAx] bounded (qmul v P) W one :=
    bounded_radius_mono _ _ _ _ _ (le_refl _) (le_refl _)
      (by unfold W productRadius; ipra_le 2*𝔞 (GaussianNameBounds.U angleSineF (angleSineData z R B K x)))
      (bound_congr (.eqRefl _) (one_mul _) (one_mul one)
        (bounded_product _ _ _ _ _ _ (le_refl _) (le_refl _) vBound hP))
  have left : Γ ⊢[PRAAx] distanceBounded (qmul u t) (qmul (qmul x₁ s) t) (two*FactorBudget a) U :=
    distance_congr (qmul_commutative t u) (qmul_commutative t (qmul x₁ s)) (.eqRefl _) (.eqRefl _)
      (multiply_distance t u _ two _ U hp ht (sine_factor_error a p hu.andE₁))
  have link : Γ ⊢[PRAAx] distanceBounded x₁ (qmul b x₂) ((two*R)*two) U :=
    relative_sample_error z R B m k x p hB hm hk hz
  have midRaw : Γ ⊢[PRAAx] distanceBounded (qmul x₁ s) (qmul (qmul b x₂) s) (two*((two*R)*two)) U :=
    distance_congr (qmul_commutative _ _) (qmul_commutative _ _) (.eqRefl _) (.eqRefl _)
      (multiply_distance s _ _ two _ U hp hs link)
  have midEq : Γ ⊢[PRAAx] qmul t (qmul (qmul b x₂) s) ≐ qmul (qmul x₂ t) P :=
    (qmul_commutative _ _).eqTrans ((qmul_associative _ _ _).eqTrans
      ((qmul_shuffle b x₂ s t).eqTrans (qmul_commutative _ _)))
  have middle := distance_congr (qmul_commutative _ _) midEq (.eqRefl _) (.eqRefl _)
      (multiply_distance t _ _ two _ U hp ht midRaw)
  have right := distance_congr (qmul_commutative _ _) (qmul_commutative _ _) (.eqRefl _) (.eqRefl _)
    (multiply_distance P _ _ (two*R) _ U hp hP (root_factor_error R K i x p hR hK hi hv.andE₁))
  have e : Γ ⊢[PRAAx] distanceBounded (qmul u t) (qmul v P) (crossCost z R B K i x) U :=
    distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp left middle) right
  have vLower : Γ ⊢[PRAAx] lower v one D :=
    GaussianSineSampleRootList.sine_margin_at (GaussianSineSampleRootGuards.clock p J) J x D i
      (GaussianSineSampleRootGuards.sine_margins _ J x (GaussianSineSampleRootGuards.clock_fine p J)) hiJ
  exact corrected_factor_error u v b s t _ U W D hp (GaussianSineSampleRootGuards.sine_denominator_positive J) vLower
    (square_lower nameF one d _ m p hm bv hv.andE₂) leftBound rightBound e

private theorem observation_denominator_congr (f : PR 2) (x A B C : PTm n)
    (h : Γ ⊢[PRAAx] observationBound f x A B) (e : Γ ⊢[PRAAx] B ≐ C) :
    Γ ⊢[PRAAx] observationBound f x A C := by
  simpa only [GaussianNamedSincQuadraticBounds.subst_observationBound,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    (Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (observationBound f (var 0) (var 1) (var 2) : Fm PTm 3)
      ![x,A,B] ![x,A,C] (fun j => by fin_cases j; exact .eqRefl x; exact .eqRefl A; exact e)
      (by simpa only [GaussianNamedSincQuadraticBounds.subst_observationBound,Syn.subst_var,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using h))

theorem corrected_row_error (z R B K i x p : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K) (hB : Γ ⊢[PRAAx] le one B)
    (hi : Γ ⊢[PRAAx] lt i K) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] distanceBounded (sincFactor z R B K i x p) (GaussianGammaEulerReflectionHead.squareFactor i z B)
      (GaussianInverseSquareProductComparison.rowErrorNumerator (num 96*(R*R)) (R*R) i)
      (GaussianInverseSquareProductComparison.rowErrorDenominator (GaussianSineProductT4Budget.squareDenominator R K) i) :=
  GaussianSincRatioProductRow.row_error nameF nameF one (angleData z R B K x) one (rootData R K i x) p p z R B K i
    hR hB hK hi hz (observation_denominator_congr _ _ _ _ _ (argument_input _ _ _ _ _ hR hK hB hz).andE₂ (modulus_eq R K))
    (observation_denominator_congr _ _ _ _ _ (root_input _ _ _ _ hR hK hi).andE₂ (modulus_eq R K))

theorem row_error (z R B K i x p : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K) (hB : Γ ⊢[PRAAx] le one B)
    (hi : Γ ⊢[PRAAx] lt i K) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    let E := GaussianInverseSquareProductComparison.rowErrorNumerator (num 96*(R*R)) (R*R) i
    let D := GaussianInverseSquareProductComparison.rowErrorDenominator (GaussianSineProductT4Budget.squareDenominator R K) i
    Γ ⊢[PRAAx] distanceBounded (actualFactor z R B K i x p) (GaussianGammaEulerReflectionHead.squareFactor i z B)
      (budget z R B K i x*D+E*unit p) (unit p*D) := by
  dsimp only
  exact GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ (unit_positive p)
    (positive_product _ _ (GaussianSineProductT4Budget.denominator_positive R K)
      (positive_product _ _ (zero_lt_succ _) (zero_lt_succ _)))
    (transport z R B K i x p hR hK hB hi hz) (corrected_row_error z R B K i x p hR hK hB hi hz)

end LeanProofs.IPRA.Analysis.GaussianSineProductSynchronizedRow
