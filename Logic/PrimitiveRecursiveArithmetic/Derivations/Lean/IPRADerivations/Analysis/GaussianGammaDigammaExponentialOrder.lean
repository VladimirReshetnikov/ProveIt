import IPRADerivations.Analysis.GaussianStirlingMultiplicativeBoundsOrder
import IPRADerivations.Analysis.RationalConvexEndpointBudget

/-!
# Signed exponentiation of the real order of Gamma logarithm names

An independent name order allows approximation slack at each query.
A rational shift of 2/2^j makes the two inputs to the constant signed
exponential exactly ordered at the frozen query j. The exponential
Lipschitz bound removes this shift at independent output queries.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaExponentialOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameBounds (U sample_bound)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at scalar_coordinate_distance)
open GaussianNamedRealOrderTransport (upperSlack precision remove_upper_slack)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRadiusExponentialName (nameF data)
open GaussianRadiusExponentialLipschitzRate (factor)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (qadd canonical positive_product ofGaussian_canonical)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at constant_input constant_real_order exponential_own_sample_rate)
open RationalGaussianEmbedding (axis)
open RationalValueBounds (upper upper_mono upper_triangle)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "E" => GaussianRadiusExponentialName.input

def radius (f g : PR 2) (x y : PTm n) : PTm n := U f x+(U g y+two)
def bias (r j : PTm n) : PTm n := qadd r (fraction two (unit j))
def cost (R : PTm n) : PTm n := num 4*factor R+num 4

@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (f g : PR 2) (x y : PTm n) :
    Syn.subst σ (radius f g x y) = radius f g (Syn.subst σ x) (Syn.subst σ y) := by simp [radius]

theorem bias_positive_fraction_bound (j : PTm n) : Γ ⊢[PRAAx] bounded (fraction two (unit j)) two (unit j) :=
  GaussianRationalReciprocal.bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point _ _ (unit_positive j)).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded _ _ (unit_positive j))

theorem bias_bound (g : PR 2) (y j : PTm n) (hg : Γ ⊢[PRAAx] pointCN g y) :
    Γ ⊢[PRAAx] bounded (bias (ap2 g j y) j) (U g y+two) one := by
  have small : Γ ⊢[PRAAx] bounded (fraction two (unit j)) two one :=
    GaussianCoefficientNameBounds.bounded_radius_mono _ two (unit j) two one (unit_positive j) (le_refl one)
      (by ipra_le 2*sl (unit_positive (Γ := Γ) j)) (bias_positive_fraction_bound j)
  exact GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ (le_refl one) (sample_bound g y j hg) small

theorem bias_gap (r j : PTm n) : Γ ⊢[PRAAx] distanceBounded (bias r j) r two (unit j) :=
  GaussianRationalReciprocal.bound_congr
    (GaussianRationalSyntheticDivision.qadd_sub_cancel r (fraction two (unit j)) (ofGaussian_canonical _ _ (unit_positive j))).eqSymm
    (.eqRefl _) (.eqRefl _) (bias_positive_fraction_bound j)

theorem bias_real (r j : PTm n) (hr : Γ ⊢[PRAAx] axis r) :
    Γ ⊢[PRAAx] canonical (bias r j) ⋏ axis (bias r j) :=
  .andI (GaussianRationalHorner.qadd_canonical _ _)
    (RationalGaussianEmbedding.axis_add _ _ hr (GaussianStirlingNames.fraction_axis _ _ (unit_positive j)))

theorem biased_order_at (f g : PR 2) (x y j : PTm n) (h : Γ ⊢[PRAAx] realOrder f g x y) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT (ap2 f j x)) (fstT (bias (ap2 g j y) j)) := by
  have hp := unit_positive (Γ := Γ) j
  have h0 := upper_mono _ _ _ _ two (unit j) (positive_product _ _ hp hp)
    (real_order_at f g x y j j h) (le_of_eq_add (d := zero) (by ipra_ring))
  let u := fstT (ap2 g j y)
  let v := fstT (fraction two (unit j))
  let w := GaussianEuclideanDistanceName.fraction two (unit j)
  have e := (RationalGaussianRealPart.real_add (Γ := Γ) (ap2 g j y) (fraction two (unit j))).eqTrans
    ((RationalArithmetic.add_at u v).eqSymm.eqTrans
      ((congrAp2 RationalArithmetic.addF (.eqRefl u) (GaussianStirlingMultiplicativeBoundsOrder.fraction_real_part _ _ hp)).eqTrans
        (RationalArithmetic.add_at u w)))
  exact RationalArgmin.rationalLE_congr (.eqRefl _) e.eqSymm (RationalConvexEndpointBudget.order_of_upper _ _ _ _ hp h0)

theorem bias_rate_at (g : PR 2) (y j p q : PTm n) (hg : Γ ⊢[PRAAx] pointCN g y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 g p y) (ap2 constantF q (bias (ap2 g j y) j))
      (rateNumerator (num 3) (unit j) p q) (rateDenominator (unit j) p q) := by
  have hp := unit_positive (Γ := Γ) p
  have hj := unit_positive (Γ := Γ) j
  have raw := GaussianNameEquivalence.point_at g y p j hg
  have join := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ (positive_product _ _ hp hj) hj raw
    (distance_symmetric _ _ _ _ hj (bias_gap (ap2 g j y) j))
  apply distance_congr (.eqRefl _) (constant_at q (bias (ap2 g j y) j)).eqSymm (.eqRefl _) (.eqRefl _)
  refine distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hp hj) hj)
    (GaussianNamedInverseRate.denominator_positive _ p q hj) ?_ join
  apply le_of_eq_add (d := unit p*unit p*unit j*unit j*unit j)
  unfold rateNumerator rateDenominator
  ipra_ring

@[simp] theorem subst_bias {m : ℕ} (σ : Fin n → PTm m) (r j : PTm n) :
    Syn.subst σ (bias r j) = bias (Syn.subst σ r) (Syn.subst σ j) := by simp [bias]

theorem bias_rate (g : PR 2) (y j : PTm n) (hg : Γ ⊢[PRAAx] pointCN g y) :
    Γ ⊢[PRAAx] independentRate g constantF y (bias (ap2 g j y) j) (num 3) (unit j) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN g (sh y) := by
    simpa [Fm.shift,Syn.shift,sh] using hg.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,Syn.shift,sh,subst_ap2,subst_bias,GaussianCoefficientNameBounds.subst_unit,PTm.subst_num] using
    bias_rate_at g (sh y) (sh j) (var 1) (var 0) hs

set_option maxHeartbeats 800000 in
theorem exp_order_at (f g : PR 2) (x y p q : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (fr : Γ ⊢[PRAAx] realSamples f x) (gr : Γ ⊢[PRAAx] realSamples g y)
    (h : Γ ⊢[PRAAx] realOrder f g x y) :
    Γ ⊢[PRAAx] upper (fstT (ap2 (nameF f) p (data (radius f g x y) x)))
      (fstT (ap2 (nameF g) q (data (radius f g x y) y))) (unit p+unit q) (unit p*unit q) := by
  let R := radius f g x y
  let a := fstT (ap2 (nameF f) p (data R x))
  let b := fstT (ap2 (nameF g) q (data R y))
  let j := precision a b (unit p*unit q) (cost R)
  let u := ap2 f j x
  let v := bias (ap2 g j y) j
  have hj := unit_positive (Γ := Γ) j
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have fi : Γ ⊢[PRAAx] E f R x := GaussianExponentialRadiusIndependence.input_widen f _ _ x
    (GaussianGammaFiniteApproximantName.exponential_input f x hf) (le_add_right _ _)
  have gi : Γ ⊢[PRAAx] E g R y := GaussianExponentialRadiusIndependence.input_widen g _ _ y
    (GaussianGammaFiniteApproximantName.exponential_input g y hg) (le_trans (le_add_right _ _) (le_add_left _ _))
  have vb : Γ ⊢[PRAAx] bounded v R one :=
    GaussianCoefficientNameBounds.bounded_radius_mono v (U g y+two) one R one (le_refl one) (le_refl one)
      (le_congr (by ipra_ring) (by dsimp only [R,radius]; ipra_ring) (le_add_left (U g y+two) (U f x))) (bias_bound g y j hg)
  have ir : Γ ⊢[PRAAx] independentRate (nameF g) (nameF constantF) (data R y) (data R v) (factor R*num 3) (unit j) :=
    GaussianRadiusExponentialLipschitzRate.independent_rate g constantF R y v (num 3) (unit j)
      (.andI hj (.andI gi (.andI (constant_input _ _ vb) (bias_rate g y j hg))))
  have dl := rate_at _ _ _ _ _ _ p j (exponential_own_sample_rate f R x j fi)
  have dr := rate_at _ _ _ _ _ _ q j ir
  have ld := GaussianNamedInverseRate.denominator_positive _ p j hj
  have rd := GaussianNamedInverseRate.denominator_positive _ q j hj
  have first := RationalValueBounds.upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ ld dl)
  have last := RationalValueBounds.upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ rd (distance_symmetric _ _ _ _ rd dr))
  have middle := real_order_at _ _ _ _ j j
    (constant_real_order u v R (real_sample_at f x j fr) (bias_real _ _ (real_sample_at g y j gr).andE₂)
      (GaussianRadiusExponentialName.bounded_samples_at f R x j fi.andE₂) vb (biased_order_at f g x y j h))
  have all := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ first middle) last
  apply remove_upper_slack _ _ _ _ (cost R)
  apply upper_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ ld (positive_product _ _ hj hj)) rd) all
  have clear (P Q J K : PTm n) : Γ ⊢[PRAAx]
      ((((K*one*P*J+J*(P+J))*(J*J)+((J+J)*(J*P*J)))*(J*Q*J)+
        (K*num 3*Q*J+J*(Q+J))*((J*P*J)*(J*J)))*(P*Q*J)) ≐
      ((P+Q)*J+(num 4*K+num 4)*(P*Q))*(((J*P*J)*(J*J))*(J*Q*J)) := by ipra_ring
  exact le_of_eq_add (d := zero) ((clear (unit p) (unit q) (unit j) (factor R)).eqSymm.eqTrans (LeanProofs.IPRA.add_zero _).eqSymm)

theorem exp_order (f g : PR 2) (x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (fr : Γ ⊢[PRAAx] realSamples f x) (gr : Γ ⊢[PRAAx] realSamples g y)
    (h : Γ ⊢[PRAAx] realOrder f g x y) :
    Γ ⊢[PRAAx] realOrder (nameF f) (nameF g) (data (radius f g x y) x) (data (radius f g x y) y) := by
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hx : Δ ⊢[PRAAx] pointCN f (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift.shift
  have hy : Δ ⊢[PRAAx] pointCN g (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hg.shift.shift
  have fx : Δ ⊢[PRAAx] realSamples f (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using fr.shift.shift
  have fy : Δ ⊢[PRAAx] realSamples g (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using gr.shift.shift
  have ho : Δ ⊢[PRAAx] realOrder f g (sh x) (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [realOrder,GaussianRadiusExponentialName.subst_data,subst_radius,Syn.shift,sh] using
    exp_order_at f g (sh x) (sh y) (var 1) (var 0) hx hy fx fy ho

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaExponentialOrder
