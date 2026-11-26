import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.LowTime.GaussianEulerLowTimePowerBound
import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelUnitError
import IPRADerivations.Analysis.Beta.Endpoints.Upper.GaussianBetaUpperRowDampedError

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

open_ipra
open GaussianEulerCompactProductComparison (clock)
open GaussianBetaKernelGridComparison (row)
open GaussianEulerIntegrandName (powerF powerData decayF decayData productF productData nameF data)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_through_auxiliary)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B A a b N : PTm n) : Fm PTm n :=
  GaussianEulerLowerPowerOrder.source z R B A a b ⋏ GaussianBetaKernelLogarithm.source a b N

def cost (a b : PTm n) : PTm n := b+a*a+num 3
def errorNumerator (p v N : PTm n) : PTm n := unit p*unit v+N*(unit p+unit v)
def errorDenominator (p v N : PTm n) : PTm n := N*unit p*unit v

theorem old_source (z R B A a b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b N) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.source z B a b := GaussianEulerLowerPowerComparison.old_source z R B A a b h.andE₁

theorem row_regularity (p r z R B A a b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b N) : Γ ⊢[PRAAx]
    distanceBounded (row p z B a b N) (row r z B a b N) (unit p+unit r) (unit p*unit r) := by
  exact GaussianBetaUpperRowDampedError.row_regularity_of_source p r z B a b N
    (old_source z R B A a b N h) h.andE₂

theorem auxiliary_product_error (r z R B A a b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b N) : Γ ⊢[PRAAx]
    distanceBounded (row r z B a b N) (ap2 productF r (productData z B a b))
      (unit r+(b+a*a+one)*N) (N*unit r) := by
  let k := clock r z B a b
  let P := unit r
  let V := b*b*N
  have ha := h.andE₁.andE₂.andE₁.andE₁
  have hv : Γ ⊢[PRAAx] le one V := positive_product _ _ (positive_product _ _ h.andE₂.andE₁ h.andE₂.andE₁) h.andE₂.andE₂.andE₁
  have hP := unit_positive (Γ := Γ) r
  have scaled := GaussianBetaUpperRowDampedError.row_product_error_of_bounds r z B a b N b a (a*a) V ha hv
    (GaussianEulerLowTimePowerBound.original_power_bound k z R B A a b h.andE₁)
    (GaussianBetaKernelUnitError.original_kernel_error k a b N h.andE₂)
  have second : Γ ⊢[PRAAx] le ((b*(a*a)*P+(b+a*a+one)*(a*V))*(N*P))
      ((P+(b+a*a+one)*N)*((a*V)*P)) :=
    le_congr (by dsimp only [V]; ipra_ring) (by dsimp only [V]; ipra_ring)
      (add_le_add_right ((b+a*a+one)*a*V*N*P)
        (mul_le_mul_right (a*b*N*P*P) h.andE₁.andE₂.andE₂))
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ ha hv) hP)
    (positive_product _ _ h.andE₂.andE₂.andE₁ hP) second scaled

theorem cofinal_slack (p v r z R B A a b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b N) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (row p z B a b N) (ap2 nameF v (data z B a b)))
      (errorNumerator p v N) (errorDenominator p v N) (cost a b) r := by
  have first := row_regularity p r z R B A a b N h
  have second : Γ ⊢[PRAAx] distanceBounded (row r z B a b N) (ap2 productF r (productData z B a b))
      (one*unit r+(b+a*a+one)*N) (N*unit r) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) (auxiliary_product_error r z R B A a b N h)
  have third := GaussianNameEquivalence.cross_at productF nameF (productData z B a b) (data z B a b) r v
    (GaussianEulerIntegrandName.original_power_times_decay z B a b (old_source z R B A a b N h))
  have joined := distance_through_auxiliary p v r one N (b+a*a+one) h.andE₂.andE₂.andE₁ first second third
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [errorNumerator,errorDenominator,cost,unit]; ipra_ring) (.eqRefl _)
    joined

/-- At every original low time, the exact leading beta/Euler row error
is 1/N, retaining both requested ordinary observation errors. -/
theorem original_low_row_error (p v z R B A a b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b N) : Γ ⊢[PRAAx]
    distanceBounded (row p z B a b N) (GaussianEulerIntegrandName.sample v z B a b)
      (unit p*unit v+N*(unit p+unit v)) (N*unit p*unit v) := by
  have hd := positive_product (Γ := Γ) _ _ (positive_product _ _ h.andE₂.andE₂.andE₁ (unit_positive p)) (unit_positive v)
  have raw := GaussianRationalSlackRemoval.slack_removal_at _ _ _ (cost a b) hd
    (cofinal_slack p v _ z R B A a b N h)
  exact distance_congr (.eqRefl _) (GaussianEulerIntegrandName.sample_at v z B a b).eqSymm (.eqRefl _) (.eqRefl _) raw

theorem original_low_time_beta_row_unit_degree_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      distanceBounded (row (var 0) (var 2) (var 4) (var 6) (var 7) (var 8))
        (GaussianEulerIntegrandName.sample (var 1) (var 2) (var 4) (var 6) (var 7))
        (unit (var 0)*unit (var 1)+(var 8)*(unit (var 0)+unit (var 1))) ((var 8)*unit (var 0)*unit (var 1))) :=
  closeUniv 9 (.impI (original_low_row_error _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaLowRowError
