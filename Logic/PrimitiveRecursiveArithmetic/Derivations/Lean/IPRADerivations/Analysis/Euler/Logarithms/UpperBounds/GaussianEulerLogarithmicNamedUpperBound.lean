import IPRADerivations.Analysis.Euler.Logarithms.UpperBounds.GaussianEulerLogarithmicUpperQuadrature
import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicIntervalName
import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperTailNameBudget

/-!
# Actual logarithmic compact upper bound with an independent decay query

The actual arbitrary-interval logarithmic compact name is bounded by
2^(R+j+1)*(R+j)! times the unchanged nonnegative half-decay reference
at its left endpoint. The reference query q stays fixed. Actual compact
mesh and evaluator precisions remove all finite-grid errors, then true
pointCN and a finite rational gap retain only the requested observation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicNamedUpperBound

open_ipra
open GaussianEulerLogarithmicIntervalName (nameF data name_at name_regular)
open GaussianEulerLogarithmicCompactName (evaluatorF fixedData)
open GaussianEulerLogarithmicMultiplier (lipschitz)
open GaussianEulerLogarithmicUpperPointwise (half_reference_bound)
open GaussianEulerUpperTailPointwise (referenceTop referenceBottom reference_bottom_positive)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianEulerUpperTailScalar (budget)
open GaussianEulerUpperTailNameBudget (enlarged_mesh_lower enlarged_precision_lower mesh_unit_lower precision_unit_lower)
open GaussianCompactRiemannName (mesh precision)
open GaussianRationalMetric (bounded qsub)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (z R B a C E T : PTm n) : Fm PTm n :=
  GaussianEulerLogarithmicUpperQuadrature.source z R B a C E T ⋏ le one C
def point (p j z R B a C E T : PTm n) : PTm n := ap2 nameF p (data j z R B a C E T)
def cost (d C : PTm n) : PTm n := num 18*majorant d+num 3*majorant d*C*C+C*(majorant d+budget d)
def finiteNumerator (p s N C E d A B : PTm n) : PTm n :=
  (C*budget d)*GaussianEulerHalfDecayLeftNorm.denominator p s N E B+
    (majorant d*GaussianEulerHalfDecayLeftNorm.numerator p s N C E A B)*(E*unit p)
def finiteDenominator (p s N E B : PTm n) : PTm n :=
  (E*unit p)*GaussianEulerHalfDecayLeftNorm.denominator p s N E B
def cofinalNumerator (s q d a C E : PTm n) : PTm n :=
  two*majorant d*referenceTop q a E*unit s+cost d C*referenceBottom q a E
def cofinalDenominator (s q a E : PTm n) : PTm n := referenceBottom q a E*unit s
def numerator (p q d a E : PTm n) : PTm n := two*majorant d*referenceTop q a E*unit p+referenceBottom q a E
def denominator (p q a E : PTm n) : PTm n := referenceBottom q a E*unit p

theorem interval_source (z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T) :
    Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource z R B a C E T :=
  .andI h.andE₁.andE₁ (.andI (le_trans h.andE₁.andE₁.andE₂.andE₁ h.andE₁.andE₂.andE₁) h.andE₁.andE₂.andE₂)

theorem lipschitz_positive (j R E T : PTm n) : Γ ⊢[PRAAx] le one (lipschitz j R E T) := by
  have radius : Γ ⊢[PRAAx] le one (GaussianEulerLogarithmicMultiplier.logRadius E T) :=
    le_of_eq_add (d := E*(T+one)+num 24) (by unfold GaussianEulerLogarithmicMultiplier.logRadius GaussianCompactLogarithmBounds.radius; ipra_ring)
  have power := GaussianPolynomialPerturbation.power_positive _ j radius
  exact le_trans (positive_product _ _ (GaussianEulerUpperTailNameBudget.lipschitz_positive R E T) power) (le_add_right _ _)

/-- The exact original finite expression is coarsened using only the
actual mesh/precision lower bounds. The leading reference is unchanged. -/
theorem finite_budget (p s N C E d A B : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hN : Γ ⊢[PRAAx] le (unit s) N) (hp : Γ ⊢[PRAAx] le (unit s) (unit p)) : Γ ⊢[PRAAx]
    le (finiteNumerator p s N C E d (A*unit s+B) (B*unit s)*(B*unit s))
      ((two*majorant d*A*unit s+cost d C*B)*finiteDenominator p s N E (B*unit s)) := by
  have hn := enlarged_mesh_lower s N E hE hN
  have hu := enlarged_precision_lower p s E hE hp
  unfold finiteNumerator finiteDenominator cost GaussianEulerHalfDecayLeftNorm.numerator
    GaussianEulerHalfDecayLeftNorm.denominator GaussianEulerHalfDecayLeftNorm.errorNumerator
    GaussianEulerHalfDecayLeftNorm.errorDenominator
  ipra_le (𝔞 B*𝔞 B*𝔞 E*𝔞(unit p)*𝔞(unit s)*𝔞(unit s)*3*𝔞(majorant d)*𝔞 C*𝔞 C*𝔞(unit p))*sl hn+
    (𝔞 B*𝔞 B*𝔞 E*𝔞(unit p)*𝔞(unit s)*𝔞(unit s)*2*𝔞 C*𝔞 E*𝔞 N*(𝔞(majorant d)+𝔞(budget d)))*sl hu

theorem denominator_positive (p q a E : PTm n) : Γ ⊢[PRAAx] le one (denominator p q a E) :=
  positive_product _ _ (reference_bottom_positive q a E) (unit_positive p)

theorem cofinal_bound (s q j z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C E T) : Γ ⊢[PRAAx]
    bounded (point s j z R B a C E T) (cofinalNumerator s q (R+j) a C E) (cofinalDenominator s q a E) := by
  let P := precision s T
  let L := lipschitz j R E T
  let N := mesh s L T
  let D := referenceBottom q a E
  let A := referenceTop q a E
  let U := GaussianEulerHalfDecayLeftNorm.numerator P s N C E (A*unit s+D) (D*unit s)
  let V := GaussianEulerHalfDecayLeftNorm.denominator P s N E (D*unit s)
  have he := h.andE₁.andE₁.andE₂.andE₁
  have hn := GaussianCompactRiemannName.mesh_positive (Γ := Γ) s L T
  have hd : Γ ⊢[PRAAx] le one (D*unit s) := positive_product _ _ (reference_bottom_positive q a E) (unit_positive s)
  have width : Γ ⊢[PRAAx] le C (E*T) := le_trans (le_add_left C a) h.andE₁.andE₂.andE₂
  have step : Γ ⊢[PRAAx] le C ((two*E)*N) :=
    le_trans (GaussianEulerDecayCompactAntiderivative.mesh_covers_step s C E L T width (lipschitz_positive j R E T))
      (le_of_eq_add (d := E*N) (by ipra_ring))
  have half : Γ ⊢[PRAAx] bounded (GaussianCompactRiemannName.quadrature GaussianEulerCompactUpperTail.halfEvaluator P N a C E zero) U V :=
    GaussianEulerHalfDecayLeftNorm.original_half_decay_left_norm P s N a C E zero _ _
      (.andI (le_trans he h.andE₁.andE₂.andE₁) (.andI hn (.andI he (.andI h.andE₂ (.andI hd step)))))
      (half_reference_bound q s a E he)
  have hv : Γ ⊢[PRAAx] le one V := positive_product _ _ hd
    (GaussianEulerHalfDecayLeftNorm.error_denominator_positive P s N E hn he)
  have actual := GaussianEulerLogarithmicUpperQuadrature.original_grid_bound_from_half P N a C E j z R B T U V h.andE₁ hn hv half
  have estimate := bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ he (unit_positive P)) hv)
    (denominator_positive s q a E)
    (finite_budget P s N C E (R+j) A D he (mesh_unit_lower s L T) (precision_unit_lower s T)) actual
  exact bound_congr (name_at s j z R B a C E T).eqSymm (.eqRefl _) (.eqRefl _) estimate

theorem observation_slack (p q s j z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C E T) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (point p j z R B a C E T) (numerator p q (R+j) a E)
      (denominator p q a E) (cost (R+j) C+one) s := by
  have up := unit_positive (Γ := Γ) p
  have us := unit_positive (Γ := Γ) s
  have dm := positive_product _ _ up us
  have ds := denominator_positive (Γ := Γ) s q a E
  have near := GaussianNameEquivalence.point_at nameF (data j z R B a C E T) p s
    (name_regular j z R B a C E T (interval_source z R B a C E T h))
  have joined := GaussianRationalReciprocal.bounded_sum (point s j z R B a C E T)
    (qsub (point p j z R B a C E T) (point s j z R B a C E T)) _ _ _ _ ds dm
    (cofinal_bound s q j z R B a C E T h) near
  have same := GaussianRationalLinearProduct.add_sub_right (Γ := Γ) (point s j z R B a C E T) (point p j z R B a C E T)
    (GaussianCompactRiemannName.name_canonical evaluatorF p _ _ _ _ _ _)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ ds dm)
    (positive_product _ _ (denominator_positive p q a E) us)
    (le_of_eq_add (d := zero) (by dsimp only [cofinalNumerator,cofinalDenominator,numerator,denominator,unit]; ipra_ring))
    (bound_congr same (.eqRefl _) (.eqRefl _) joined)

/-- The actual compact upper interval retains exactly the independent
positive half-decay observation and the single requested name error. -/
theorem original_named_bound (p q j z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C E T) : Γ ⊢[PRAAx]
    bounded (point p j z R B a C E T) (numerator p q (R+j) a E) (denominator p q a E) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (cost (R+j) C+one) (denominator_positive p q a E)
    (observation_slack p q _ j z R B a C E T h)

theorem actual_logarithmic_compact_upper_independent_half_reference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      bounded (point (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))
        (numerator (var 0) (var 1) (var 4+var 2) (var 6) (var 8)) (denominator (var 0) (var 1) (var 6) (var 8))) :=
  closeUniv 10 (.impI (original_named_bound _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicNamedUpperBound
