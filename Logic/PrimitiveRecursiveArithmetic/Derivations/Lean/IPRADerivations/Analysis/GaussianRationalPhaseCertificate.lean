import IPRADerivations.Analysis.GaussianRationalHalfAngle
import IPRADerivations.Foundations.RealizerComposition
import IPRADerivations.Core.LinearCombination

/-!
# Finite rational transfer to the direction certificate

The actual Euclidean comparison with the rational normalized target supplies
the cross inequality. Unit norm and completion of a square then yield the
source's signed-dot certificate, without a phase or square-root premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPhaseCertificate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (re im code normSq normSq_eval scale)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product represents)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (positivePart)
open LeanProofs.IPRA.Foundations.RealizerComposition (ap4)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def four : PTm n := two*two
def cross (h g V a S : PTm n) : PTm n := GaussianRootAlgebra.sub (scale S h) (scale (V*a) g)
def dot (h g : PTm n) : ZT n := ZT.ofNat two*(re h*re g+im h*im g)
def dotNatural (h g : PTm n) : PTm n := positivePart (dot h g)
def multiplier (q : PTm n) : PTm n := four*q*q
def slack (p q : PTm n) : PTm n := monus (multiplier q) (p*p)
def coefficientNumerator (p q : PTm n) : PTm n := monus (two*q*q) (p*p)
def middle (g a S p q : PTm n) : PTm n := slack p q*S*S+multiplier q*a*a*normSq g

@[simp] theorem subst_four {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (four : PTm n) = (four : PTm m) := by simp [four]
@[simp] theorem subst_cross {m : ℕ} (σ : Fin n → PTm m) (h g V a S : PTm n) :
    Syn.subst σ (cross h g V a S) = cross (Syn.subst σ h) (Syn.subst σ g) (Syn.subst σ V) (Syn.subst σ a) (Syn.subst σ S) := by simp [cross]
@[simp] theorem subst_dot {m : ℕ} (σ : Fin n → PTm m) (h g : PTm n) :
    (dot h g).subst σ = dot (Syn.subst σ h) (Syn.subst σ g) := by simp [dot]
@[simp] theorem subst_dotNatural {m : ℕ} (σ : Fin n → PTm m) (h g : PTm n) :
    Syn.subst σ (dotNatural h g) = dotNatural (Syn.subst σ h) (Syn.subst σ g) := by simp [dotNatural]
@[simp] theorem subst_multiplier {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (multiplier q) = multiplier (Syn.subst σ q) := by simp [multiplier]
@[simp] theorem subst_slack {m : ℕ} (σ : Fin n → PTm m) (p q : PTm n) :
    Syn.subst σ (slack p q) = slack (Syn.subst σ p) (Syn.subst σ q) := by simp [slack]
@[simp] theorem subst_coefficientNumerator {m : ℕ} (σ : Fin n → PTm m) (p q : PTm n) :
    Syn.subst σ (coefficientNumerator p q) = coefficientNumerator (Syn.subst σ p) (Syn.subst σ q) := by simp [coefficientNumerator]
@[simp] theorem subst_middle {m : ℕ} (σ : Fin n → PTm m) (g a S p q : PTm n) :
    Syn.subst σ (middle g a S p q) = middle (Syn.subst σ g) (Syn.subst σ a) (Syn.subst σ S) (Syn.subst σ p) (Syn.subst σ q) := by simp [middle]

theorem multiplier_positive (q : PTm n) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx] le one (multiplier q) :=
  positive_product _ _ (positive_product _ _
    (positive_product two two (le_succ_self one) (le_succ_self one)) hq) hq

theorem square_le_multiplier (p q : PTm n) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx] le (p*p) (multiplier q) :=
  le_trans (sq_le_sq hpq) (le_of_eq_add (d := (num 3)*q*q) (by unfold multiplier four; ipra_ring))

theorem slack_identity (p q : PTm n) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    multiplier q ≐ p*p+slack p q := eq_add_of_le (square_le_multiplier p q hpq)

theorem coefficient_identity (p q : PTm n) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    two*q*q ≐ p*p+coefficientNumerator p q :=
  eq_add_of_le (le_trans (sq_le_sq hpq) (le_of_eq_add (d := q*q) (by ipra_ring)))

theorem cross_expansion (h g V a S : PTm n) (hNorm : Γ ⊢[PRAAx] normSq h ≐ V*V) :
    𝔞(normSq (cross h g V a S)) = 𝔞(V*V*S*S)+𝔞(V*V*a*a*normSq g)-𝔞(S*V*a)*ZT.toZ Γ (dot h g) := by
  have hn := natEq hNorm
  rw [normSq_eval] at hn
  rw [normSq_eval]
  unfold cross
  simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
    GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale]
  unfold dot
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  ipra_simps
  rw [normSq_eval]
  linear_combination 𝔞(S)^2*hn

theorem cross_balance (h g V a S p q : PTm n) (hpq : Γ ⊢[PRAAx] le p q)
    (hNorm : Γ ⊢[PRAAx] normSq h ≐ V*V)
    (hError : Γ ⊢[PRAAx] le (multiplier q*normSq (cross h g V a S)) (p*p*V*V*S*S)) : Γ ⊢[PRAAx]
    multiplier q*S*V*a*(dot h g).pos ≐ multiplier q*S*V*a*(dot h g).neg+
      V*V*middle g a S p q+monus (p*p*V*V*S*S) (multiplier q*normSq (cross h g V a S)) := by
  have error := natEq (eq_add_of_le hError)
  have expansion := cross_expansion h g V a S hNorm
  have sl := natEq (slack_identity p q hpq)
  apply deriveNat
  unfold middle
  simp only [ZT.toZ] at expansion
  ipra_simps
  linear_combination 𝔞(multiplier q)*expansion+error+𝔞(V)^2*𝔞(S)^2*sl

theorem dot_nonnegative (h g V a S p q : PTm n)
    (hV : Γ ⊢[PRAAx] le one V) (ha : Γ ⊢[PRAAx] le one a) (hS : Γ ⊢[PRAAx] le one S)
    (hq : Γ ⊢[PRAAx] le one q) (hpq : Γ ⊢[PRAAx] le p q)
    (hNorm : Γ ⊢[PRAAx] normSq h ≐ V*V)
    (hError : Γ ⊢[PRAAx] le (multiplier q*normSq (cross h g V a S)) (p*p*V*V*S*S)) : Γ ⊢[PRAAx]
    le (dot h g).neg (dot h g).pos := by
  apply RationalValueBounds.positive_cancel
    (positive_product _ _ (positive_product _ _ (positive_product _ _ (multiplier_positive q hq) hS) hV) ha)
  exact le_of_eq_add (d := V*V*middle g a S p q+monus (p*p*V*V*S*S) (multiplier q*normSq (cross h g V a S)))
    ((cross_balance h g V a S p q hpq hNorm hError).eqTrans (by ipra_ring))

theorem natural_dot_balance (h g V a S p q : PTm n)
    (hV : Γ ⊢[PRAAx] le one V) (ha : Γ ⊢[PRAAx] le one a) (hS : Γ ⊢[PRAAx] le one S)
    (hq : Γ ⊢[PRAAx] le one q) (hpq : Γ ⊢[PRAAx] le p q)
    (hNorm : Γ ⊢[PRAAx] normSq h ≐ V*V)
    (hError : Γ ⊢[PRAAx] le (multiplier q*normSq (cross h g V a S)) (p*p*V*V*S*S)) : Γ ⊢[PRAAx]
    multiplier q*S*V*a*dotNatural h g ≐ V*V*middle g a S p q+
      monus (p*p*V*V*S*S) (multiplier q*normSq (cross h g V a S)) := by
  have nonneg := dot_nonnegative h g V a S p q hV ha hS hq hpq hNorm hError
  have value := GaussianRationalHalfAngle.positive_part_value (Γ := Γ) (dot h g) nonneg
  have balance := natEq (cross_balance h g V a S p q hpq hNorm hError)
  apply deriveNat
  rw [ZT.toZ_ofNat] at value
  simp only [ZT.toZ] at value
  change 𝔞(dotNatural h g) = _ at value
  ipra_simps
  linear_combination balance+𝔞(multiplier q)*𝔞(S)*𝔞(V)*𝔞(a)*value

theorem dot_lower_bound (h g V a S p q : PTm n)
    (hV : Γ ⊢[PRAAx] le one V) (ha : Γ ⊢[PRAAx] le one a) (hS : Γ ⊢[PRAAx] le one S)
    (hq : Γ ⊢[PRAAx] le one q) (hpq : Γ ⊢[PRAAx] le p q)
    (hNorm : Γ ⊢[PRAAx] normSq h ≐ V*V)
    (hError : Γ ⊢[PRAAx] le (multiplier q*normSq (cross h g V a S)) (p*p*V*V*S*S)) : Γ ⊢[PRAAx]
    le (V*middle g a S p q) (multiplier q*S*a*dotNatural h g) := by
  have positive := natural_dot_balance h g V a S p q hV ha hS hq hpq hNorm hError
  apply RationalValueBounds.positive_cancel hV
  exact le_congr (by ipra_ring) (by ipra_ring)
    (le_congr (.eqRefl _) positive.eqSymm (le_add_right _ _))

theorem completed_square (g a S p q : PTm n) : Γ ⊢[PRAAx]
    le (four*slack p q*multiplier q*S*S*a*a*normSq g) (middle g a S p q*middle g a S p q) := by
  let x := slack p q*S*S
  let y := multiplier q*a*a*normSq g
  have ad := natEq (Probability.Variance.ad_sq (Γ := Γ) x y)
  refine le_of_eq_add (d := Probability.Variance.ad x y*Probability.Variance.ad x y) ?_
  apply deriveNat
  unfold middle four
  ipra_simps
  dsimp [x,y] at ad
  ipra_simps
  linear_combination -ad

theorem squared_dot_lower (h g V a S p q : PTm n)
    (hV : Γ ⊢[PRAAx] le one V) (ha : Γ ⊢[PRAAx] le one a) (hS : Γ ⊢[PRAAx] le one S)
    (hq : Γ ⊢[PRAAx] le one q) (hpq : Γ ⊢[PRAAx] le p q)
    (hNorm : Γ ⊢[PRAAx] normSq h ≐ V*V)
    (hError : Γ ⊢[PRAAx] le (multiplier q*normSq (cross h g V a S)) (p*p*V*V*S*S)) : Γ ⊢[PRAAx]
    le (slack p q*normSq g*V*V) (q*q*dotNatural h g*dotNatural h g) := by
  have square := sq_le_sq (dot_lower_bound h g V a S p q hV ha hS hq hpq hNorm hError)
  have low := mul_le_mul_right (V*V) (completed_square (Γ := Γ) g a S p q)
  have both := le_trans (le_congr (.eqRefl _) (by ipra_ring) low) square
  have factor : Γ ⊢[PRAAx] le one (multiplier q*S*S*a*a) :=
    positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _ (multiplier_positive q hq) hS) hS) ha) ha
  have cancelled : Γ ⊢[PRAAx] le (four*slack p q*normSq g*V*V)
      (multiplier q*dotNatural h g*dotNatural h g) :=
    RationalValueBounds.positive_cancel factor (le_congr (by ipra_ring) (by ipra_ring) both)
  apply RationalValueBounds.positive_cancel
    (positive_product two two (le_succ_self one) (le_succ_self one))
  exact le_congr (by unfold four; ipra_ring) (by unfold multiplier four; ipra_ring) cancelled

theorem coefficient_square_bound (p q : PTm n) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    le (coefficientNumerator p q*coefficientNumerator p q) (q*q*slack p q) := by
  have sr := natEq (slack_identity p q hpq)
  have cr := natEq (coefficient_identity p q hpq)
  have gap := natEq (eq_add_of_le (sq_le_sq hpq))
  refine le_of_eq_add (d := p*p*(two*q*q+monus (q*q) (p*p))) ?_
  apply deriveNat
  unfold multiplier four at sr
  ipra_simps
  linear_combination -𝔞(q)^2*sr+(2*𝔞(q)^2-𝔞(p)^2+𝔞(coefficientNumerator p q))*cr+𝔞(p)^2*gap

theorem kernel_certificate (h g V a S p q : PTm n)
    (hV : Γ ⊢[PRAAx] le one V) (ha : Γ ⊢[PRAAx] le one a) (hS : Γ ⊢[PRAAx] le one S)
    (hq : Γ ⊢[PRAAx] le one q) (hpq : Γ ⊢[PRAAx] le p q)
    (hNorm : Γ ⊢[PRAAx] normSq h ≐ V*V)
    (hError : Γ ⊢[PRAAx] le (multiplier q*normSq (cross h g V a S)) (p*p*V*V*S*S)) : Γ ⊢[PRAAx]
    le (dot h g).neg (dot h g).pos ⋏
      le (normSq g*V*V*coefficientNumerator p q*coefficientNumerator p q)
        (q*q*q*q*dotNatural h g*dotNatural h g) := by
  refine .andI (dot_nonnegative h g V a S p q hV ha hS hq hpq hNorm hError) ?_
  have first : Γ ⊢[PRAAx] le (normSq g*V*V*coefficientNumerator p q*coefficientNumerator p q)
      (q*q*slack p q*normSq g*V*V) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (mul_le_mul_right (normSq g*V*V) (coefficient_square_bound p q hpq))
  exact le_trans first (le_congr (by ipra_ring) (by ipra_ring)
    (mul_le_mul_right (q*q) (squared_dot_lower h g V a S p q hV ha hS hq hpq hNorm hError)))

/-! Literal scalar operations in the source certificate. The Gaussian
conjugate retains the original real code and normalizes the negated imaginary
component. Its product, real part and all scalar squares are actual programs. -/
def conjugatePoint (c : PTm n) : PTm n := pairT (fstT c) (RationalArithmetic.negative (sndT c))
def directionDot (c v : PTm n) : PTm n := RationalArithmetic.multiply (fraction two one)
  (fstT (GaussianRationalHorner.qmul v (conjugatePoint c)))
def directionCoefficient (v p q : PTm n) : PTm n := RationalArithmetic.add
  (RationalArithmetic.add (GaussianRationalMetric.qnormSq v) (fraction one one))
  (RationalArithmetic.negative (GaussianRationalMetric.squaredTolerance p q))
def square (c : PTm n) : PTm n := RationalArithmetic.multiply c c
def certificate (c v p q : PTm n) : Fm PTm n :=
  RationalArgmin.rationalLE (fraction zero one) (directionDot c v) ⋏
    RationalArgmin.rationalLE
      (RationalArithmetic.multiply (GaussianRationalMetric.qnormSq c) (square (directionCoefficient v p q)))
      (square (directionDot c v))
def target (c a S : PTm n) : PTm n := GaussianRationalHorner.ofGaussian
  (scale a (GaussianRationalL1.rawGaussian c)) S

@[simp] theorem subst_conjugatePoint {m : ℕ} (σ : Fin n → PTm m) (c : PTm n) :
    Syn.subst σ (conjugatePoint c) = conjugatePoint (Syn.subst σ c) := by simp [conjugatePoint]
@[simp] theorem subst_directionDot {m : ℕ} (σ : Fin n → PTm m) (c v : PTm n) :
    Syn.subst σ (directionDot c v) = directionDot (Syn.subst σ c) (Syn.subst σ v) := by simp [directionDot]
@[simp] theorem subst_directionCoefficient {m : ℕ} (σ : Fin n → PTm m) (v p q : PTm n) :
    Syn.subst σ (directionCoefficient v p q) = directionCoefficient (Syn.subst σ v) (Syn.subst σ p) (Syn.subst σ q) := by simp [directionCoefficient]
@[simp] theorem subst_square {m : ℕ} (σ : Fin n → PTm m) (c : PTm n) :
    Syn.subst σ (square c) = square (Syn.subst σ c) := by simp [square]
@[simp] theorem subst_certificate {m : ℕ} (σ : Fin n → PTm m) (c v p q : PTm n) :
    (certificate c v p q).subst σ = certificate (Syn.subst σ c) (Syn.subst σ v) (Syn.subst σ p) (Syn.subst σ q) := by simp [certificate]
@[simp] theorem subst_target {m : ℕ} (σ : Fin n → PTm m) (c a S : PTm n) :
    Syn.subst σ (target c a S) = target (Syn.subst σ c) (Syn.subst σ a) (Syn.subst σ S) := by simp [target]

theorem conjugate_represents (c g E : PTm n) (hc : Γ ⊢[PRAAx] represents c g E) : Γ ⊢[PRAAx]
    represents (conjugatePoint c) (GaussianRationalReciprocal.conjugate g) E := by
  refine .andI
    (GaussianRationalHorner.scalar_congr (fst_pair _ _).eqSymm ?_ (.eqRefl _) (Prf.andE₁ hc))
    (GaussianRationalHorner.scalar_congr (snd_pair _ _).eqSymm ?_ (.eqRefl _)
      (RationalRepresentations.represents_negative _ _ _ (Prf.andE₂ hc)))
  all_goals apply ZT.derive
  · rw [GaussianRationalReciprocal.re_conjugate]
  · rw [ZT.toZ_neg,GaussianRationalReciprocal.im_conjugate]

theorem direction_dot_represents (c v g h E V : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hV : Γ ⊢[PRAAx] le one V)
    (hc : Γ ⊢[PRAAx] represents c g E) (hv : Γ ⊢[PRAAx] represents v h V) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (directionDot c v) (dot h g) (V*E) := by
  have product := GaussianRationalHorner.qmul_represents (Γ := Γ) v (conjugatePoint c)
    h (GaussianRationalReciprocal.conjugate g) V E hV hE hv (conjugate_represents c g E hc)
  have scaled := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _
    (fraction_represents two one (le_refl one)) (Prf.andE₁ product)
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := one_mul _) (h := scaled)
  ipra_lc [dot, GaussianRootAlgebra.re_mul, GaussianRationalReciprocal.re_conjugate, GaussianRationalReciprocal.im_conjugate]

theorem coefficient_represents (v p q : PTm n) (hq : Γ ⊢[PRAAx] le one q)
    (hpq : Γ ⊢[PRAAx] le p q) (hUnit : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit v) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (directionCoefficient v p q) (ZT.ofNat (coefficientNumerator p q)) (q*q) := by
  have oneRep := GaussianRationalHorner.scalar_congr hUnit.eqSymm (ZT.derive rfl) (.eqRefl _)
    (fraction_represents (Γ := Γ) one one (le_refl one))
  have sumRep := RationalRepresentations.represents_add (Γ := Γ) _ _ _ _ _ _ oneRep
    (fraction_represents one one (le_refl one))
  have negative := RationalRepresentations.represents_negative _ _ _
    (GaussianRationalMetric.squared_tolerance_represents (Γ := Γ) p q hq)
  have combined := RationalRepresentations.represents_add (Γ := Γ) _ _ _ _ _ _ sumRep negative
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := by ipra_ring) (h := combined)
  ipra_lc natEq (coefficient_identity p q hpq)

theorem square_represents (c A B : PTm n) (hc : Γ ⊢[PRAAx] RationalArithmetic.represents c (ZT.ofNat A) B) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (square c) (ZT.ofNat (A*A)) (B*B) := by
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := .eqRefl _)
    (h := RationalRepresentations.represents_multiply c c _ _ B B hc hc)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps

theorem target_difference_represents (c v a S : PTm n)
    (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx]
    represents (GaussianRationalMetric.qsub v (target c a S))
      (cross (GaussianRationalL1.rawGaussian v) (GaussianRationalL1.rawGaussian c) (GaussianRationalL1.rawDen v) a S)
      (GaussianRationalL1.rawDen v*S) := by
  have hV := GaussianRationalL1.raw_den_positive (Γ := Γ) v
  have left := GaussianRationalHorner.represents_rescale _ _ _ S (GaussianRationalL1.raw_represents (Γ := Γ) v)
  have right := GaussianRationalHorner.represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (mul_comm _ _)
    (GaussianRationalHorner.represents_rescale _ _ _ (GaussianRationalL1.rawDen v)
      (GaussianRationalHorner.ofGaussian_represents (Γ := Γ) (scale a (GaussianRationalL1.rawGaussian c)) S hS))
  have difference := GaussianRationalMetric.qsub_represents _ _ _ _ _ (positive_product _ _ hV hS) left right
  apply GaussianRationalHorner.represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := difference)
  apply GaussianRootAlgebra.equal_of_values
  all_goals simp only [cross,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
    GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale] <;> ipra_simps <;> ring

theorem target_error_cleared (c v a S p q : PTm n)
    (hS : Γ ⊢[PRAAx] le one S) (hq : Γ ⊢[PRAAx] le one q)
    (hError : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded v (target c a S) p (two*q)) : Γ ⊢[PRAAx]
    le (multiplier q*normSq (cross (GaussianRationalL1.rawGaussian v) (GaussianRationalL1.rawGaussian c)
      (GaussianRationalL1.rawDen v) a S)) (p*p*GaussianRationalL1.rawDen v*GaussianRationalL1.rawDen v*S*S) :=
  le_congr (by unfold multiplier four; ipra_ring) (by ipra_ring)
    (GaussianRationalMetric.bounded_to_cleared _ _ _ _ _
      (positive_product _ _ (GaussianRationalL1.raw_den_positive v) hS)
      (positive_product _ _ (le_succ_self one) hq) (target_difference_represents c v a S hS) hError)

theorem from_target (c v a S p q : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hS : Γ ⊢[PRAAx] le one S)
    (hq : Γ ⊢[PRAAx] le one q) (hpq : Γ ⊢[PRAAx] le p q)
    (hUnit : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit v)
    (hError : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded v (target c a S) p (two*q)) : Γ ⊢[PRAAx]
    certificate c v p q := by
  have hV := GaussianRationalL1.raw_den_positive (Γ := Γ) v
  have hE := GaussianRationalL1.raw_den_positive (Γ := Γ) c
  have hVE := positive_product _ _ hV hE
  have kernel := kernel_certificate (GaussianRationalL1.rawGaussian v) (GaussianRationalL1.rawGaussian c)
    (GaussianRationalL1.rawDen v) a S p q hV ha hS hq hpq
    (GaussianRationalHalfAngle.raw_unit v hUnit) (target_error_cleared c v a S p q hS hq hError)
  have dotRep := direction_dot_represents (Γ := Γ) c v (GaussianRationalL1.rawGaussian c) (GaussianRationalL1.rawGaussian v)
    (GaussianRationalL1.rawDen c) (GaussianRationalL1.rawDen v) hE hV
    (GaussianRationalL1.raw_represents c) (GaussianRationalL1.raw_represents v)
  have dotValue := GaussianRationalHalfAngle.positive_part_value (Γ := Γ)
    (dot (GaussianRationalL1.rawGaussian v) (GaussianRationalL1.rawGaussian c)) (Prf.andE₁ kernel)
  have dotNaturalRep : Γ ⊢[PRAAx] RationalArithmetic.represents (directionDot c v)
      (ZT.ofNat (dotNatural (GaussianRationalL1.rawGaussian v) (GaussianRationalL1.rawGaussian c)))
      (GaussianRationalL1.rawDen v*GaussianRationalL1.rawDen c) :=
    GaussianRationalHorner.scalar_congr (.eqRefl _) (ZT.derive dotValue.symm) (.eqRefl _) dotRep
  have dotSquare := square_represents _ _ _ dotNaturalRep
  have coefficientSquare := square_represents _ _ _ (coefficient_represents v p q hq hpq hUnit)
  have hQQ := positive_product q q hq hq
  have hQQQQ := positive_product _ _ hQQ hQQ
  have hEE := positive_product _ _ hE hE
  have lhs := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _
    (GaussianRationalMetric.qnormSq_represents c (GaussianRationalL1.rawGaussian c) (GaussianRationalL1.rawDen c)
      hE (GaussianRationalL1.raw_represents c)) coefficientSquare
  have lhsRep : Γ ⊢[PRAAx] RationalArithmetic.represents
      (RationalArithmetic.multiply (GaussianRationalMetric.qnormSq c) (square (directionCoefficient v p q)))
      (ZT.ofNat (normSq (GaussianRationalL1.rawGaussian c)*(coefficientNumerator p q*coefficientNumerator p q)))
      ((GaussianRationalL1.rawDen c*GaussianRationalL1.rawDen c)*((q*q)*(q*q))) := by
    apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    ipra_simps
  refine .andI ?_ ?_
  · apply RationalArithmetic.order_of_representations _ _ _ _ _ _
      (fraction_represents zero one (le_refl one)) dotNaturalRep (le_refl one) hVE
    apply zle_of_toZ (dotNatural (GaussianRationalL1.rawGaussian v) (GaussianRationalL1.rawGaussian c))
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    ipra_simps
    ring
  · apply GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
      (positive_product _ _ hEE hQQQQ) (positive_product _ _ hVE hVE) lhsRep dotSquare
    exact le_congr (by ipra_ring) (by ipra_ring)
      (mul_le_mul_right (GaussianRationalL1.rawDen c*GaussianRationalL1.rawDen c) (Prf.andE₂ kernel))

/-- The source's epsilon guard supplies both denominator positivity and
the weaker p<=q comparison used by the finite algebraic kernel. -/
theorem direction_phase_certificate (c v a S p q : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hS : Γ ⊢[PRAAx] le one S)
    (hp : Γ ⊢[PRAAx] le one p) (hSmall : Γ ⊢[PRAAx] le ((num 16)*p) q)
    (hUnit : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit v)
    (hError : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded v (target c a S) p (two*q)) : Γ ⊢[PRAAx]
    certificate c v p q := by
  have hpq := le_trans (le_of_eq_add (d := (num 15)*p) (by ipra_ring)) hSmall
  exact from_target c v a S p q ha hS (le_trans hp hpq) hpq hUnit hError

theorem coefficient_at_least_one (v p q : PTm n) (hq : Γ ⊢[PRAAx] le one q)
    (hpq : Γ ⊢[PRAAx] le p q) (hUnit : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit v) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fraction one one) (directionCoefficient v p q) := by
  have positive : Γ ⊢[PRAAx] le (q*q) (coefficientNumerator p q) := by
    refine le_of_eq_add (d := monus (q*q) (p*p)) ?_
    ipra_lc natEq (eq_add_of_le (sq_le_sq hpq))-natEq (coefficient_identity p q hpq)
  apply GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ (le_refl one)
    (positive_product q q hq hq) (fraction_represents one one (le_refl one))
    (coefficient_represents v p q hq hpq hUnit)
  exact le_congr (by ipra_ring) (by ipra_ring) positive

theorem coefficient_positive (v p q : PTm n) (hq : Γ ⊢[PRAAx] le one q)
    (hpq : Γ ⊢[PRAAx] le p q) (hUnit : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit v) : Γ ⊢[PRAAx]
    neg (RationalArgmin.rationalLE (directionCoefficient v p q) (fraction zero one)) := by
  refine .impI ?_
  have cmp : (RationalArgmin.rationalLE (directionCoefficient v p q) (fraction zero one))::Γ ⊢[PRAAx]
      RationalArgmin.rationalLE (fraction one one) (fraction zero one) :=
    RationalArgmin.transitive (coefficient_at_least_one (Γ := Γ) v p q hq hpq hUnit).wk Prf.hyp0
  have bad := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (fraction_represents (Γ := Γ) one one (le_refl one)).wk
    (fraction_represents (Γ := Γ) zero one (le_refl one)).wk cmp
  exact not_succ_le_self zero _ (le_congr (one_mul _) (zero_mul _) bad)

/-! An actual PR4 program prints precisely the signed dot, source
coefficient and the two sides of the certified square comparison. -/
def leftSide (c v p q : PTm n) : PTm n :=
  RationalArithmetic.multiply (GaussianRationalMetric.qnormSq c) (square (directionCoefficient v p q))
def rightSide (c v : PTm n) : PTm n := square (directionDot c v)
def output (c v p q : PTm n) : PTm n := pairT (directionDot c v)
  (pairT (directionCoefficient v p q) (pairT (leftSide c v p q) (rightSide c v)))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (c v p q : PTm n) : PTm n := ap4 outputF c v p q

def returnedCertificate (c v p q : PTm n) : Fm PTm n :=
  RationalArgmin.rationalLE (fraction zero one) (fstT (run c v p q)) ⋏
    RationalArgmin.rationalLE (fstT (sndT (sndT (run c v p q)))) (sndT (sndT (sndT (run c v p q))))

@[simp] theorem subst_leftSide {m : ℕ} (σ : Fin n → PTm m) (c v p q : PTm n) :
    Syn.subst σ (leftSide c v p q) = leftSide (Syn.subst σ c) (Syn.subst σ v) (Syn.subst σ p) (Syn.subst σ q) := by simp [leftSide]
@[simp] theorem subst_rightSide {m : ℕ} (σ : Fin n → PTm m) (c v : PTm n) :
    Syn.subst σ (rightSide c v) = rightSide (Syn.subst σ c) (Syn.subst σ v) := by simp [rightSide]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (c v p q : PTm n) :
    Syn.subst σ (output c v p q) = output (Syn.subst σ c) (Syn.subst σ v) (Syn.subst σ p) (Syn.subst σ q) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (c v p q : PTm n) :
    Syn.subst σ (run c v p q) = run (Syn.subst σ c) (Syn.subst σ v) (Syn.subst σ p) (Syn.subst σ q) := by simp [run]
@[simp] theorem subst_returnedCertificate {m : ℕ} (σ : Fin n → PTm m) (c v p q : PTm n) :
    (returnedCertificate c v p q).subst σ = returnedCertificate (Syn.subst σ c) (Syn.subst σ v) (Syn.subst σ p) (Syn.subst σ q) := by simp [returnedCertificate]

theorem program_at (c v p q : PTm n) : Γ ⊢[PRAAx] run c v p q ≐ output c v p q := by
  simpa [run,outputF,ap4] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![c,v,p,q]

theorem returned_dot (c v p q : PTm n) : Γ ⊢[PRAAx] fstT (run c v p q) ≐ directionDot c v :=
  (congrFst (program_at c v p q)).eqTrans (fst_pair _ _)
theorem returned_coefficient (c v p q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run c v p q)) ≐ directionCoefficient v p q :=
  (congrFst ((congrSnd (program_at c v p q)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_left (c v p q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run c v p q))) ≐ leftSide c v p q :=
  (congrFst ((congrSnd ((congrSnd (program_at c v p q)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_right (c v p q : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run c v p q))) ≐ rightSide c v :=
  (congrSnd ((congrSnd ((congrSnd (program_at c v p q)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem returned_certificate (c v a S p q : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hS : Γ ⊢[PRAAx] le one S)
    (hq : Γ ⊢[PRAAx] le one q) (hpq : Γ ⊢[PRAAx] le p q)
    (hUnit : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit v)
    (hError : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded v (target c a S) p (two*q)) : Γ ⊢[PRAAx]
    returnedCertificate c v p q := by
  have proof := from_target c v a S p q ha hS hq hpq hUnit hError
  exact .andI
    (RationalArgmin.rationalLE_congr (.eqRefl _) (returned_dot c v p q).eqSymm (Prf.andE₁ proof))
    (RationalArgmin.rationalLE_congr (returned_left c v p q).eqSymm (returned_right c v p q).eqSymm (Prf.andE₂ proof))

theorem phase_from_target_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 2) ⟶ le one (var 3) ⟶ le one (var 5) ⟶ le (var 4) (var 5) ⟶
      GaussianRationalHalfAngle.unit (var 1) ⟶
      GaussianRationalMetric.distanceBounded (var 1) (target (var 0) (var 2) (var 3)) (var 4) (two*var 5) ⟶
      certificate (var 0) (var 1) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI (.impI
    (from_target _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk
      Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))))

theorem source_direction_phase_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 2) ⟶ le one (var 3) ⟶ le one (var 4) ⟶ le ((num 16)*var 4) (var 5) ⟶
      GaussianRationalHalfAngle.unit (var 1) ⟶
      GaussianRationalMetric.distanceBounded (var 1) (target (var 0) (var 2) (var 3)) (var 4) (two*var 5) ⟶
      certificate (var 0) (var 1) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI (.impI
    (direction_phase_certificate _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk
      Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))))

theorem source_coefficient_positive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ le (var 1) (var 2) ⟶ GaussianRationalHalfAngle.unit (var 0) ⟶
      RationalArgmin.rationalLE (fraction one one) (directionCoefficient (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (coefficient_at_least_one _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem phase_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)

theorem returned_phase_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 2) ⟶ le one (var 3) ⟶ le one (var 5) ⟶ le (var 4) (var 5) ⟶
      GaussianRationalHalfAngle.unit (var 1) ⟶
      GaussianRationalMetric.distanceBounded (var 1) (target (var 0) (var 2) (var 3)) (var 4) (two*var 5) ⟶
      returnedCertificate (var 0) (var 1) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI (.impI
    (returned_certificate _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk
      Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))))

theorem source_coefficient_strict_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ le (var 1) (var 2) ⟶ GaussianRationalHalfAngle.unit (var 0) ⟶
      neg (RationalArgmin.rationalLE (directionCoefficient (var 0) (var 1) (var 2)) (fraction zero one))) :=
  closeUniv 3 (.impI (.impI (.impI (coefficient_positive _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRationalPhaseCertificate
