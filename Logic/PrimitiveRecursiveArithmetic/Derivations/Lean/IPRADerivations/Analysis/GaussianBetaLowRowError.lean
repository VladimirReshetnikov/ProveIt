import IPRADerivations.Analysis.GaussianEulerLowTimePowerBound
import IPRADerivations.Analysis.GaussianBetaKernelUnitError
import IPRADerivations.Analysis.GaussianBetaUpperRowDampedError

/-!
# The unchanged low-time beta row has error at most 1/N

The original power observation is bounded by 1/t. The literal finite
beta kernel has quadratic time error, and its unit norm gives genuine
row regularity at the original replacement clock. Their leading product
is t/N<=1/N below time one. One finite Euclidean gap removes only the
auxiliary original product query, retaining the requested beta and Euler
observation precisions and the exact coefficient one.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaLowRowError

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerCompactProductComparison (clock clock_later original_product)
open GaussianBetaKernelGridComparison (row)
open GaussianBetaKernelExponential (kernel)
open GaussianEulerIntegrandName (powerF powerData decayF decayData productF productData nameF data)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def source (z R B A a b N : PTm n) : Fm PTm n :=
  GaussianEulerLowerPowerOrder.source z R B A a b ⋏ GaussianBetaKernelLogarithm.source a b N

def cost (a b : PTm n) : PTm n := b+a*a+num 3
def errorNumerator (p v N : PTm n) : PTm n := unit p*unit v+N*(unit p+unit v)
def errorDenominator (p v N : PTm n) : PTm n := N*unit p*unit v

theorem old_source (z R B A a b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b N) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.source z B a b := GaussianEulerLowerPowerComparison.old_source z R B A a b h.andE₁

theorem row_regularity (p r z R B A a b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b N) : Γ ⊢[PRAAx]
    distanceBounded (row p z B a b N) (row r z B a b N) (unit p+unit r) (unit p*unit r) := by
  let kp := clock p z B a b
  let kr := clock r z B a b
  let x := ap2 powerF kp (powerData z B a b)
  let y := ap2 powerF kr (powerData z B a b)
  let w := kernel a b N
  have hp := GaussianExponentialReference.unit_monotone (Γ := Γ) (clock_later p z B a b)
  have hr := GaussianExponentialReference.unit_monotone (Γ := Γ) (clock_later r z B a b)
  have old := GaussianNameEquivalence.point_at powerF (powerData z B a b) kp kr
    (GaussianEulerIntegrandName.power_regular z B a b (old_source z R B A a b N h))
  have compare : Γ ⊢[PRAAx] le ((unit kp+unit kr)*(unit p*unit r)) ((unit p+unit r)*(unit kp*unit kr)) := by
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

theorem auxiliary_product_error (r z R B A a b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b N) : Γ ⊢[PRAAx]
    distanceBounded (row r z B a b N) (ap2 productF r (productData z B a b))
      (unit r+(b+a*a+one)*N) (N*unit r) := by
  let k := clock r z B a b
  let U := unit k
  let P := unit r
  let V := b*b*N
  let x := ap2 powerF k (powerData z B a b)
  let y := ap2 decayF k (decayData a b)
  let w := kernel a b N
  have ha := h.andE₁.andE₂.andE₁.andE₁
  have hv : Γ ⊢[PRAAx] le one V := positive_product _ _ (positive_product _ _ h.andE₂.andE₁ h.andE₂.andE₁) h.andE₂.andE₂.andE₁
  have hU := unit_positive (Γ := Γ) k
  have hP := unit_positive (Γ := Γ) r
  have power := GaussianEulerLowTimePowerBound.original_power_bound k z R B A a b h.andE₁
  have kernelError := GaussianBetaKernelUnitError.original_kernel_error k a b N h.andE₂
  have raw := GaussianRationalReciprocal.bounded_product x (qsub w y) (b*U+a) (a*U) (a*a*U+V) (V*U)
    (positive_product _ _ ha hU) (positive_product _ _ hv hU) power kernelError
  have exactError := GaussianRationalReciprocal.bound_congr (GaussianRationalRoundedPower.multiplication_difference x w y).eqSymm
    (.eqRefl _) (.eqRefl _) raw
  have first := GaussianBetaUpperRowDampedError.product_budget b a (a*a) V U P ha hv hU
    (GaussianExponentialReference.unit_monotone (clock_later r z B a b))
  have scaled := distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ ha hU) (positive_product _ _ hv hU))
    (positive_product _ _ (positive_product _ _ ha hv) hP) first exactError
  have second : Γ ⊢[PRAAx] le ((b*(a*a)*P+(b+a*a+one)*(a*V))*(N*P))
      ((P+(b+a*a+one)*N)*((a*V)*P)) :=
    le_congr (by dsimp only [V]; ipra_ring) (by dsimp only [V]; ipra_ring)
      (add_le_add_right ((b+a*a+one)*a*V*N*P)
        (mul_le_mul_right (a*b*N*P*P) h.andE₁.andE₂.andE₂))
  have final := distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ ha hv) hP)
    (positive_product _ _ h.andE₂.andE₂.andE₁ hP) second scaled
  exact distance_congr (.eqRefl _) (original_product r z B a b).eqSymm (.eqRefl _) (.eqRefl _) final

theorem cofinal_slack (p v r z R B A a b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b N) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (row p z B a b N) (ap2 nameF v (data z B a b)))
      (errorNumerator p v N) (errorDenominator p v N) (cost a b) r := by
  have dp := positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive r)
  have ds := positive_product (Γ := Γ) _ _ h.andE₂.andE₂.andE₁ (unit_positive r)
  have dt := positive_product (Γ := Γ) _ _ (unit_positive r) (unit_positive v)
  have first := row_regularity p r z R B A a b N h
  have second := auxiliary_product_error r z R B A a b N h
  have third := GaussianNameEquivalence.cross_at productF nameF (productData z B a b) (data z B a b) r v
    (GaussianEulerIntegrandName.original_power_times_decay z B a b (old_source z R B A a b N h))
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ (positive_product _ _ dp ds) dt
    (GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ dp ds first second) third
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ dp ds) dt)
    (positive_product _ _ (positive_product _ _ (positive_product _ _ h.andE₂.andE₂.andE₁ (unit_positive p)) (unit_positive v)) (unit_positive r)) _ joined
  exact le_of_eq_add (d := zero) (by dsimp only [errorNumerator,errorDenominator,cost,unit]; ipra_ring)

/-- At every original low time, the exact leading beta/Euler row error
is 1/N, retaining both requested ordinary observation errors. -/
theorem original_low_row_error (p v z R B A a b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b N) : Γ ⊢[PRAAx]
    distanceBounded (row p z B a b N) (GaussianEulerIntegrandName.sample v z B a b)
      (unit p*unit v+N*(unit p+unit v)) (N*unit p*unit v) := by
  have hd := positive_product (Γ := Γ) _ _ (positive_product _ _ h.andE₂.andE₂.andE₁ (unit_positive p)) (unit_positive v)
  have raw := GaussianRationalSlackRemoval.slack_removal_at _ _ _ (cost a b) hd
    (cofinal_slack p v (GaussianRationalSlackRemoval.precision
      (qsub (row p z B a b N) (ap2 nameF v (data z B a b)))
      (errorNumerator p v N) (errorDenominator p v N) (cost a b)) z R B A a b N h)
  exact distance_congr (.eqRefl _) (GaussianEulerIntegrandName.sample_at v z B a b).eqSymm (.eqRefl _) (.eqRefl _) raw

theorem original_low_time_beta_row_unit_degree_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      distanceBounded (row (var 0) (var 2) (var 4) (var 6) (var 7) (var 8))
        (GaussianEulerIntegrandName.sample (var 1) (var 2) (var 4) (var 6) (var 7))
        (unit (var 0)*unit (var 1)+(var 8)*(unit (var 0)+unit (var 1))) ((var 8)*unit (var 0)*unit (var 1))) :=
  closeUniv 9 (.impI (original_low_row_error _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaLowRowError
