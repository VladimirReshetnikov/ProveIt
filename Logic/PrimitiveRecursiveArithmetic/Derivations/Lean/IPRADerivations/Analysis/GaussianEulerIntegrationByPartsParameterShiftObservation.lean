import IPRADerivations.Analysis.GaussianEulerIntegrationByPartsParameterShift
import IPRADerivations.Analysis.GaussianEulerIntegrationByPartsObservation

/-!
# Actual parameter-shift observations with independent original clocks

The original shifted sample at p differs from time times the original
unshifted sample at q by at most 2^-p+T*2^-q whenever time<=T.
The normalized multiplication query is retained; only one auxiliary
precision is removed. On a compact interval the original raw power-decay
boundary observation is obtained with an explicit uniform dyadic cost.
No Gamma recurrence or integral identity is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsParameterShiftObservation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrationByPartsParameterShift (productF productData original_integrand_parameter_shift)
open GaussianEulerIntegrandName (nameF data sample source)
open GaussianGammaEulerHeadShift (shifted)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def query (p z B a b : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus constantF nameF (fraction a b) (data z B a b)) p
def numerator (p q T : PTm n) : PTm n := unit q+T*unit p
def denominator (p q : PTm n) : PTm n := unit p*unit q
def primitiveCost (R E T : PTm n) : PTm n := T*(GaussianEulerCompactPowerMajorant.majorant R E T+LeanProofs.IPRA.PTm.num 5)+one
@[simp] theorem subst_query {m : ℕ} (σ : Fin n → PTm m) (p z B a b : PTm n) :
    Syn.subst σ (query p z B a b) = query (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [query]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (p q T : PTm n) :
    Syn.subst σ (numerator p q T) = numerator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ T) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (p q : PTm n) :
    Syn.subst σ (denominator p q) = denominator (Syn.subst σ p) (Syn.subst σ q) := by simp [denominator]
@[simp] theorem subst_primitiveCost {m : ℕ} (σ : Fin n → PTm m) (R E T : PTm n) :
    Syn.subst σ (primitiveCost R E T) = primitiveCost (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) :=
  by simp [primitiveCost,GaussianEulerCompactPowerMajorant.majorant,GaussianEulerCompactPowerMajorant.exponentRadius]

theorem original_product_query (p z B a b : PTm n) : Γ ⊢[PRAAx]
    ap2 productF p (productData z B a b) ≐ qmul (fraction a b) (ap2 nameF (query p z B a b) (data z B a b)) :=
  (GaussianNameArithmetic.multiply_at constantF nameF _ _ p).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qmul_congr (constant_at _ _) (.eqRefl _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem product_observations (s q z B a b T : PTm n) (h : Γ ⊢[PRAAx] source z B a b)
    (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 productF s (productData z B a b)) (qmul (fraction a b) (sample q z B a b))
      (T*(unit s+unit q)) (unit s*unit q) := by
  let u := query s z B a b
  let U := unit u
  let S := unit s
  let Q := unit q
  have hU : Γ ⊢[PRAAx] le one U := unit_positive u
  have hS : Γ ⊢[PRAAx] le one S := unit_positive s
  have hQ : Γ ⊢[PRAAx] le one Q := unit_positive q
  have old := positive_product _ _ hU hQ
  have next := positive_product _ _ hS hQ
  have times := GaussianEulerExponentCompactBounds.fraction_bound a b T h.andE₂.andE₂ ht
  have near := GaussianNameEquivalence.point_at nameF (data z B a b) u q (GaussianEulerIntegrandName.name_regular z B a b h)
  have product := bounded_product _ _ T one (U+Q) (U*Q) (le_refl one) old times near
  have scaled : Γ ⊢[PRAAx] distanceBounded (qmul (fraction a b) (ap2 nameF u (data z B a b)))
      (qmul (fraction a b) (ap2 nameF q (data z B a b))) (T*(U+Q)) (U*Q) :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference _ _ _).eqSymm (.eqRefl _) (by ipra_ring) product
  have grow : Γ ⊢[PRAAx] le S U := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have reduced := distance_radius_mono _ _ _ _ (T*(S+Q)) (S*Q) old next
    (by ipra_le (𝔞 T*𝔞 Q*𝔞 Q)*sl grow) scaled
  exact distance_congr (original_product_query s z B a b).eqSymm
    (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (GaussianEulerIntegrandName.sample_at q z B a b).eqSymm)
    (.eqRefl _) (.eqRefl _) reduced

theorem original_shift_slack (p q s z B a b T : PTm n) (h : Γ ⊢[PRAAx] source z B a b)
    (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (sample p (shifted z B) B a b) (qmul (fraction a b) (sample q z B a b)))
      (numerator p q T) (denominator p q) (T+one) s := by
  let P := unit p
  let Q := unit q
  let S := unit s
  let D := P*Q*S
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have hs := unit_positive (Γ := Γ) s
  have d1 := positive_product _ _ hp hs
  have d2 := positive_product _ _ hs hq
  have dd := positive_product _ _ (positive_product _ _ hp hq) hs
  have first := GaussianNameEquivalence.cross_at _ _ _ _ p s (original_integrand_parameter_shift z B a b h)
  have left := distance_radius_mono _ _ _ _ (Q*(P+S)) D d1 dd
    (le_of_eq_add (d := zero) (by dsimp only [D,P,Q,S]; ipra_ring)) first
  have right := distance_radius_mono _ _ _ _ (P*T*(S+Q)) D d2 dd
    (le_of_eq_add (d := zero) (by dsimp only [D,P,Q,S]; ipra_ring)) (product_observations s q z B a b T h ht)
  have sum := distance_triangle_same _ _ _ _ _ _ dd left right
  exact bound_congr (GaussianRationalSyntheticDivision.qsub_congr (GaussianEulerIntegrandName.sample_at p (shifted z B) B a b).eqSymm (.eqRefl _))
    (by dsimp only [numerator,denominator,P,Q,S]; unfold unit; ipra_ring) (.eqRefl _) sum

theorem original_observations (p q z B a b T : PTm n) (h : Γ ⊢[PRAAx] source z B a b)
    (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    distanceBounded (sample p (shifted z B) B a b) (qmul (fraction a b) (sample q z B a b)) (numerator p q T) (denominator p q) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (T+one)
    (positive_product _ _ (unit_positive p) (unit_positive q)) (original_shift_slack p q _ z B a b T h ht)

theorem original_diagonal (p z B a b T : PTm n) (h : Γ ⊢[PRAAx] source z B a b)
    (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    distanceBounded (sample p (shifted z B) B a b) (qmul (fraction a b) (sample p z B a b)) (T+one) (unit p) :=
  distance_radius_mono _ _ _ _ (T+one) (unit p)
    (positive_product _ _ (unit_positive p) (unit_positive p)) (unit_positive p)
    (le_of_eq_add (d := zero) (by unfold numerator; ipra_ring)) (original_observations p p z B a b T h ht)

theorem original_primitive_observation (p z R B E T a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerIntegrationByPartsObservation.source z R B E T a b) : Γ ⊢[PRAAx]
    distanceBounded (sample p (shifted z B) B a b) (GaussianEulerIntegrationByPartsLinear.primitive p z B a b)
      (primitiveCost R E T) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have old := GaussianEulerIntegrationByPartsObservation.original_diagonal p z R B E T a b h
  have times := GaussianEulerExponentCompactBounds.fraction_bound a b T h.andE₂.andE₁.andE₂ h.andE₂.andE₂.andE₂
  have product := bounded_product _ _ T one (GaussianEulerIntegrationByPartsObservation.factor R E T+one) (unit p)
    (le_refl one) hp times old
  have scaled : Γ ⊢[PRAAx] distanceBounded (qmul (fraction a b) (sample p z B a b))
      (GaussianEulerIntegrationByPartsLinear.primitive p z B a b) (T*(GaussianEulerIntegrationByPartsObservation.factor R E T+one)) (unit p) :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference _ _ _).eqSymm (.eqRefl _) (by ipra_ring) product
  have shift := original_diagonal p z B a b T (.andI h.andE₁.andE₁ h.andE₂.andE₁) h.andE₂.andE₂.andE₂
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold primitiveCost GaussianEulerIntegrationByPartsObservation.factor; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp shift scaled)

theorem actual_original_Euler_parameter_shift_independent_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source (var 2) (var 3) (var 4) (var 5) ⋏ le (var 4) (var 6*var 5)) ⟶
      distanceBounded (sample (var 0) (shifted (var 2) (var 3)) (var 3) (var 4) (var 5))
        (qmul (fraction (var 4) (var 5)) (sample (var 1) (var 2) (var 3) (var 4) (var 5)))
        (numerator (var 0) (var 1) (var 6)) (denominator (var 0) (var 1))) :=
  closeUniv 7 (.impI (original_observations _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_original_shifted_Euler_boundary_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (GaussianEulerIntegrationByPartsObservation.source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      distanceBounded (sample (var 0) (shifted (var 1) (var 3)) (var 3) (var 6) (var 7))
        (GaussianEulerIntegrationByPartsLinear.primitive (var 0) (var 1) (var 3) (var 6) (var 7))
        (primitiveCost (var 2) (var 4) (var 5)) (unit (var 0))) :=
  closeUniv 8 (.impI (original_primitive_observation _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsParameterShiftObservation
