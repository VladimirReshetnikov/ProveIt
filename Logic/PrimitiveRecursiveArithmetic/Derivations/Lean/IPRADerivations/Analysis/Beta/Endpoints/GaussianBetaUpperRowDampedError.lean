import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelDecayDampedError
import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelGridComparison
import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperPowerBound
import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelUnitBound

/-!
# The unchanged high-time beta row has the sharp damped degree factor

The literal beta replacement keeps the original power clock. Its genuine
regularity is proved using the unit bound of the same finite kernel.
At an auxiliary original query, the exact power bound multiplies the
retained damped kernel error. One finite Euclidean gap removes only this
auxiliary query, leaving the original two observation allowances and the
literal t^(R+2)/N times the actual positive decay reference.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaUpperRowDampedError

open_ipra
open GaussianEulerCompactProductComparison (clock clock_later original_product)
open GaussianBetaKernelGridComparison (row)
open GaussianBetaKernelExponential (kernel)
open GaussianBetaKernelDecayDampedError (referenceBudget referenceDenominator)
open GaussianEulerIntegrandName (powerF powerData decayF decayData productF productData nameF data)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def source (z R B a b N : PTm n) : Fm PTm n :=
  GaussianEulerUpperPowerOrder.source z R B a b ⋏ GaussianBetaKernelLogarithm.source a b N

def leadingNumerator (q R a b : PTm n) : PTm n := pw a R*(a*a*referenceBudget q a b)
def leadingDenominator (q R a b N : PTm n) : PTm n := pw b R*(b*b*N*referenceDenominator q a b*unit q)
def cost (q R a b : PTm n) : PTm n := pw a R+a*a*referenceBudget q a b+num 3
def errorNumerator (p v q R a b N : PTm n) : PTm n :=
  leadingNumerator q R a b*unit p*unit v+leadingDenominator q R a b N*(unit p+unit v)
def errorDenominator (p v q R a b N : PTm n) : PTm n :=
  leadingDenominator q R a b N*unit p*unit v

theorem leading_denominator_positive (q z R B a b N : PTm n) (h : Γ ⊢[PRAAx] source z R B a b N) : Γ ⊢[PRAAx]
    le one (leadingDenominator q R a b N) :=
  positive_product _ _ (RationalNonnegativePowers.denominator_positive b R h.andE₂.andE₁)
    (positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _ h.andE₂.andE₁ h.andE₂.andE₁)
      h.andE₂.andE₂.andE₁) (GaussianBetaKernelDecayDampedError.reference_positive q a b)) (unit_positive q))

theorem row_regularity (p r z R B a b N : PTm n) (h : Γ ⊢[PRAAx] source z R B a b N) : Γ ⊢[PRAAx]
    distanceBounded (row p z B a b N) (row r z B a b N)
      (unit p+unit r) (unit p*unit r) := by
  let kp := clock p z B a b
  let kr := clock r z B a b
  let x := ap2 powerF kp (powerData z B a b)
  let y := ap2 powerF kr (powerData z B a b)
  let w := kernel a b N
  have hp := GaussianExponentialReference.unit_monotone (Γ := Γ) (clock_later p z B a b)
  have hr := GaussianExponentialReference.unit_monotone (Γ := Γ) (clock_later r z B a b)
  have old := GaussianNameEquivalence.point_at powerF (powerData z B a b) kp kr
    (GaussianEulerIntegrandName.power_regular z B a b (GaussianEulerUpperPowerCompatibility.old_source z R B a b h.andE₁))
  have compare : Γ ⊢[PRAAx]
      le ((unit kp+unit kr)*(unit p*unit r)) ((unit p+unit r)*(unit kp*unit kr)) := by
    ipra_le (𝔞 (unit p*unit kp))*sl hr+(𝔞 (unit r*unit kr))*sl hp
  have powerError := distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive kp) (unit_positive kr))
    (positive_product _ _ (unit_positive p) (unit_positive r)) compare old
  have factor := GaussianBetaKernelUnitBound.kernel_bound a b N (GaussianBetaKernelDecayDampedError.full_source a b N h.andE₂)
  have product := GaussianRationalReciprocal.bounded_product w (qsub x y) one one (unit p+unit r) (unit p*unit r)
    (le_refl one) (positive_product _ _ (unit_positive p) (unit_positive r)) factor powerError
  have exactDifference : Γ ⊢[PRAAx] qsub (qmul x w) (qmul y w) ≐ qmul w (qsub x y) :=
    (GaussianRationalSyntheticDivision.qsub_congr (GaussianRationalPowerAlgebra.qmul_commutative x w)
      (GaussianRationalPowerAlgebra.qmul_commutative y w)).eqTrans (GaussianRationalRoundedPower.multiplication_difference w x y)
  exact GaussianRationalReciprocal.bound_congr exactDifference.eqSymm (one_mul _) (one_mul _) product

/-- Explicit multiplication allowance; every denominator is positive.
The leading factor is m*u/(B*V), while all evaluation effects are O(1/P). -/
theorem product_budget (m B u V U P : PTm n)
    (hb : Γ ⊢[PRAAx] le one B) (hv : Γ ⊢[PRAAx] le one V)
    (hu : Γ ⊢[PRAAx] le one U) (hp : Γ ⊢[PRAAx] le P U) : Γ ⊢[PRAAx]
    le (((m*U+B)*(u*U+V))*((B*V)*P))
      ((m*u*P+(m+u+one)*(B*V))*((B*U)*(V*U))) := by
  ipra_le (𝔞 (B*V*P*m*V*U))*sl hb+(𝔞 (B*V*P*u*B*U))*sl hv+
    (𝔞 (B*V*P*B*V))*sl hu+(𝔞 ((m+u+one)*B*V*B*V*U))*sl hp

theorem auxiliary_product_error (r q z R B a b N : PTm n) (h : Γ ⊢[PRAAx] source z R B a b N) : Γ ⊢[PRAAx]
    distanceBounded (row r z B a b N) (ap2 productF r (productData z B a b))
      (leadingNumerator q R a b*unit r+(pw a R+a*a*referenceBudget q a b+one)*leadingDenominator q R a b N)
      (leadingDenominator q R a b N*unit r) := by
  let k := clock r z B a b
  let U := unit k
  let P := unit r
  let m := pw a R
  let d := pw b R
  let u := a*a*referenceBudget q a b
  let v := b*b*N*referenceDenominator q a b*unit q
  let x := ap2 powerF k (powerData z B a b)
  let y := ap2 decayF k (decayData a b)
  let w := kernel a b N
  have hd := RationalNonnegativePowers.denominator_positive (Γ := Γ) b R h.andE₂.andE₁
  have hv := positive_product (Γ := Γ) _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _ h.andE₂.andE₁ h.andE₂.andE₁)
    h.andE₂.andE₂.andE₁) (GaussianBetaKernelDecayDampedError.reference_positive q a b)) (unit_positive q)
  have rawKernel := GaussianBetaKernelDecayDampedError.original_decay_damped_error k q a b N h.andE₂
  have kernelError : Γ ⊢[PRAAx] distanceBounded w y (u*U+v) (v*U) := rawKernel
  have power := GaussianEulerUpperPowerBound.original_power_bound k z R B a b h.andE₁
  have raw := GaussianRationalReciprocal.bounded_product x (qsub w y) (m*U+d) (d*U) (u*U+v) (v*U)
    (positive_product _ _ hd (unit_positive k)) (positive_product _ _ hv (unit_positive k)) power kernelError
  have productError := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference x w y).eqSymm (.eqRefl _) (.eqRefl _) raw
  have compare := product_budget m d u v U P hd hv (unit_positive k)
    (GaussianExponentialReference.unit_monotone (clock_later r z B a b))
  have scaled := distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ hd (unit_positive k)) (positive_product _ _ hv (unit_positive k)))
    (positive_product _ _ (positive_product _ _ hd hv) (unit_positive r)) compare productError
  exact distance_congr (.eqRefl _) (original_product r z B a b).eqSymm (.eqRefl _) (.eqRefl _) scaled

theorem cofinal_slack (p v q r z R B a b N : PTm n) (h : Γ ⊢[PRAAx] source z R B a b N) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (row p z B a b N) (ap2 nameF v (data z B a b)))
      (errorNumerator p v q R a b N) (errorDenominator p v q R a b N) (cost q R a b) r := by
  have dp := positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive r)
  have ds := positive_product (Γ := Γ) _ _ (leading_denominator_positive q z R B a b N h) (unit_positive r)
  have dt := positive_product (Γ := Γ) _ _ (unit_positive r) (unit_positive v)
  have first := row_regularity p r z R B a b N h
  have second := auxiliary_product_error r q z R B a b N h
  have third := GaussianNameEquivalence.cross_at productF nameF (productData z B a b) (data z B a b) r v
    (GaussianEulerIntegrandName.original_power_times_decay z B a b (GaussianEulerUpperPowerCompatibility.old_source z R B a b h.andE₁))
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ (positive_product _ _ dp ds) dt
    (GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ dp ds first second) third
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ dp ds) dt)
    (positive_product _ _ (positive_product _ _ (positive_product _ _ (leading_denominator_positive q z R B a b N h)
      (unit_positive p)) (unit_positive v)) (unit_positive r)) _ joined
  exact le_of_eq_add (d := zero) (by dsimp only [errorNumerator,errorDenominator,cost,unit]; ipra_ring)

theorem original_high_row_damped_error (p v q z R B a b N : PTm n) (h : Γ ⊢[PRAAx] source z R B a b N) : Γ ⊢[PRAAx]
    distanceBounded (row p z B a b N) (ap2 nameF v (data z B a b))
      (errorNumerator p v q R a b N) (errorDenominator p v q R a b N) := by
  have hd := positive_product (Γ := Γ) _ _
    (positive_product _ _ (leading_denominator_positive q z R B a b N h) (unit_positive p)) (unit_positive v)
  exact GaussianRationalSlackRemoval.slack_removal_at _ _ _ (cost q R a b) hd
    (cofinal_slack p v q (GaussianRationalSlackRemoval.precision
      (qsub (row p z B a b N) (ap2 nameF v (data z B a b)))
      (errorNumerator p v q R a b N) (errorDenominator p v q R a b N) (cost q R a b)) z R B a b N h)

theorem power_add_two (a R : PTm n) : Γ ⊢[PRAAx] pw a (R+two) ≐ pw a R*a*a :=
  (pw_add a R two).eqTrans ((congrMul (.eqRefl _)
    ((pw_succ a one).eqTrans (congrMul (pw_one a) (.eqRefl a)))).eqTrans (by ipra_ring))

def monomialNumerator (p v q R a b N : PTm n) : PTm n :=
  pw a (R+two)*referenceBudget q a b*unit p*unit v+
    pw b (R+two)*N*referenceDenominator q a b*unit q*(unit p+unit v)
def monomialDenominator (p v q R a b N : PTm n) : PTm n :=
  pw b (R+two)*N*referenceDenominator q a b*unit q*unit p*unit v

/-- Literal paper factor t^(R+2)/N, at independent unchanged beta p,
Euler v and nonnegative decay-reference q observations. -/
theorem original_high_row_exact_power_error (p v q z R B a b N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a b N) : Γ ⊢[PRAAx]
    distanceBounded (row p z B a b N) (GaussianEulerIntegrandName.sample v z B a b)
      (monomialNumerator p v q R a b N) (monomialDenominator p v q R a b N) := by
  have aPower := natEq (power_add_two (Γ := Γ) a R)
  have bPower := natEq (power_add_two (Γ := Γ) b R)
  exact distance_congr (.eqRefl _) (GaussianEulerIntegrandName.sample_at v z B a b).eqSymm
    (by
      apply deriveNat
      dsimp only [errorNumerator,leadingNumerator,leadingDenominator,monomialNumerator]
      ipra_simps
      rw [aPower,bPower]; ring)
    (by
      apply deriveNat
      dsimp only [errorDenominator,leadingDenominator,monomialDenominator]
      ipra_simps
      rw [bPower]; ring)
    (original_high_row_damped_error p v q z R B a b N h)

theorem original_same_query_high_row_exact_power_error (p q z R B a b N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a b N) : Γ ⊢[PRAAx]
    distanceBounded (row p z B a b N) (GaussianEulerIntegrandName.sample p z B a b)
      (monomialNumerator p p q R a b N) (monomialDenominator p p q R a b N) :=
  original_high_row_exact_power_error p p q z R B a b N h

theorem original_high_side_beta_row_regular_at_original_clock_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
        distanceBounded (row (var 0) (var 2) (var 4) (var 5) (var 6) (var 7))
          (row (var 1) (var 2) (var 4) (var 5) (var 6) (var 7))
          (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (row_regularity _ _ _ _ _ _ _ _ Prf.hyp0))

theorem original_high_side_beta_row_exact_damped_monomial_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        distanceBounded (row (var 0) (var 3) (var 5) (var 6) (var 7) (var 8))
          (GaussianEulerIntegrandName.sample (var 1) (var 3) (var 5) (var 6) (var 7))
          (monomialNumerator (var 0) (var 1) (var 2) (var 4) (var 6) (var 7) (var 8))
          (monomialDenominator (var 0) (var 1) (var 2) (var 4) (var 6) (var 7) (var 8))) :=
  closeUniv 9 (.impI (original_high_row_exact_power_error _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaUpperRowDampedError
