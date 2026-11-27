import IPRADerivations.Analysis.Euler.Integration.Decay.Damping.GaussianEulerWeightedHalfDecay
import IPRADerivations.Analysis.Euler.PositiveAxis.HalfDecay.GaussianEulerHalfDecayReference

/-!
# Pointwise factorial majorant for the original Euler integrand

At time `t=a/b≥1`, the original complex integrand observation at
precision `p` is bounded by `2^R R! (H_q+2^-q)+2^-p`, where `H_q`
is the actual nonnegative representative of the half-decay at an
independent requested precision. An explicit finite rational gap
eliminates all auxiliary clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUpperTailPointwise

open_ipra
open GaussianEulerUpperPowerOrder (source)
open GaussianEulerUpperPowerCompatibility (old_source)
open GaussianEulerIntegrandName (decayF decayData nameF data sample sample_at)
open GaussianEulerHalfDecayProduct
  (halfWeightedF halfWeightedData original_integrand_half_decay_factors)
open GaussianEulerWeightedHalfDecay (majorant productSlack halfSample original_weighted_half_decay_sample)
open GaussianEulerHalfDecayReference (scalar numerator denominator denominator_positive
  decay_reference_error reference_norm)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianReconstructionRoots (norm_from_distance)
open GaussianNamedSmallPerturbationTransport (productClock product_at)
open GaussianRationalSlackRemoval (slack precision slack_removal_at)
open RationalGaussianEmbedding (embed)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def referenceTop (q a b : PTm n) : PTm n := numerator q a b*unit q+denominator q a b
def referenceBottom (q a b : PTm n) : PTm n := denominator q a b*unit q
def majorantTop (p q R a b : PTm n) : PTm n :=
  majorant R*referenceTop q a b*unit p+referenceBottom q a b
def majorantBottom (p q a b : PTm n) : PTm n := referenceBottom q a b*unit p

ipra_subst referenceTop
ipra_subst referenceBottom
ipra_subst majorantTop
ipra_subst majorantBottom

theorem reference_bottom_positive (q a b : PTm n) : Γ ⊢[PRAAx] le one (referenceBottom q a b) :=
  positive_product _ _ (denominator_positive q a b) (unit_positive q)

theorem majorant_bottom_positive (p q a b : PTm n) : Γ ⊢[PRAAx] le one (majorantBottom p q a b) :=
  positive_product _ _ (reference_bottom_positive q a b) (unit_positive p)

theorem half_reference_bound (q s a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (halfSample s a b)
      (referenceTop q a b*unit s+referenceBottom q a b) (referenceBottom q a b*unit s) := by
  let x := halfSample s a b
  let y := embed (scalar q a b)
  let U := unit q
  let V := unit s
  let E := denominator q a b
  let N := numerator q a b
  have hE : Γ ⊢[PRAAx] le one E := denominator_positive q a b
  have ht : Γ ⊢[PRAAx] le one (U*V) := positive_product _ _ (unit_positive q) (unit_positive s)
  have err : Γ ⊢[PRAAx] distanceBounded y x (U+V) (U*V) := decay_reference_error q s a b hb
  have sym := distance_symmetric _ _ _ _ ht err
  have h := norm_from_distance x y (U+V) (U*V) N E ht hE sym (reference_norm q a b)
  exact bound_congr (.eqRefl _) (by unfold referenceTop referenceBottom; ipra_ring)
    (by unfold referenceBottom; ipra_ring) h

private def cost (M K N : PTm n) : PTm n := M+K*(N+one)

theorem approximate_reference_product (x y M K N D U : PTm n)
    (hd : Γ ⊢[PRAAx] le one D) (hu : Γ ⊢[PRAAx] le one U)
    (hx : Γ ⊢[PRAAx] bounded x (M*U+K) U)
    (hy : Γ ⊢[PRAAx] bounded y (N*U+D) (D*U)) : Γ ⊢[PRAAx]
    bounded (qmul x y) (M*N*U+(M+K*(N+one))*D) (D*U) := by
  have hDU := positive_product D U hd hu
  have h1 : Γ ⊢[PRAAx] le (K*N*U) (K*N*U*D) :=
    le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (K*N*U) hd)
  have h2 : Γ ⊢[PRAAx] le (K*D) (K*D*U) :=
    le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (K*D) hu)
  have cmp : Γ ⊢[PRAAx] le ((M*U+K)*(N*U+D)) ((M*N*U+(M+K*(N+one))*D)*U) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (le_refl (M*N*U*U+M*D*U)) (add_le_add₂ h1 h2))
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ hu hDU) hDU _
    (bounded_product x y _ _ _ _ hu hDU hx hy)
  exact le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right (D*U) cmp)

private theorem integrand_product_envelope (F : PR 2) (x p q a b M K : PTm n)
    (hb : Γ ⊢[PRAAx] le one b)
    (weighted : ∀ s : PTm n, Γ ⊢[PRAAx] bounded (ap2 F s x) (M*unit s+K) (unit s)) :
    Γ ⊢[PRAAx] bounded (ap2 (multiplyF F decayF) p (multiplyData F decayF x (decayData a (two*b))))
      (M*referenceTop q a b*unit p+cost M K (referenceTop q a b)*referenceBottom q a b)
      (referenceBottom q a b*unit p) := by
  let y := decayData a (two*b)
  let s := productClock F decayF x y p
  let N := referenceTop q a b
  let D := referenceBottom q a b
  let C := cost M K N
  have hd : Γ ⊢[PRAAx] le one D := reference_bottom_positive q a b
  have e := product_at (Γ := Γ) F decayF x y p
  have est : Γ ⊢[PRAAx] bounded (qmul (ap2 F s x) (ap2 decayF s y))
      (M*N*unit s+C*D) (D*unit s) :=
    approximate_reference_product _ _ M K N D (unit s) hd (unit_positive s) (weighted s)
      (half_reference_bound q s a b hb)
  have order : Γ ⊢[PRAAx] le (unit p) (unit s) :=
    GaussianExponentialReference.unit_monotone (le_add_right p _)
  have cmp : Γ ⊢[PRAAx] le ((M*N*unit s+C*D)*(D*unit p)) ((M*N*unit p+C*D)*(D*unit s)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (le_refl (M*N*unit p*unit s*D)) (mul_le_mul_right (C*D*D) order))
  exact bound_congr e.eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ (positive_product _ _ hd (unit_positive s))
      (positive_product _ _ hd (unit_positive p)) cmp est)

/-- Transfer a leading reference radius between observations, collecting both
late allowances in the same removable slack. -/
theorem reference_observation_slack (x y A D H K p t : PTm n)
    (hD : Γ ⊢[PRAAx] le one D)
    (near : Γ ⊢[PRAAx] distanceBounded x y (unit t+H*unit p) (unit p*unit t))
    (reference : Γ ⊢[PRAAx] bounded y (A*unit t+K*D) (D*unit t)) :
    Γ ⊢[PRAAx] slack x (A*unit p+D) (D*unit p) (H+K) t := by
  let U := unit p
  let V := unit t
  have up := unit_positive (Γ := Γ) p
  have ut := unit_positive (Γ := Γ) t
  have uv := positive_product _ _ up ut
  have dv := positive_product _ _ hD ut
  have du := positive_product _ _ hD up
  have bound := norm_from_distance x y (V+H*U) (U*V) (A*V+K*D) (D*V) uv dv near reference
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ uv dv) (positive_product _ _ du ut)
    (le_of_eq_add (d := zero) (by
      change Γ ⊢[PRAAx] ((A*U+D)*V+(H+K)*(D*U))*((U*V)*(D*V)) ≐
        ((V+H*U)*(D*V)+(A*V+K*D)*(U*V))*(D*U*V)+zero
      ipra_ring)) bound

/-- The exact named product with the half-decay factor has the leading
reference bound at the requested observation precision. -/
theorem half_decay_product_bound (F G : PR 2) (x y p q a b M K : PTm n)
    (hb : Γ ⊢[PRAAx] le one b)
    (same : Γ ⊢[PRAAx] crossEquivalent (multiplyF F decayF) G (multiplyData F decayF x (decayData a (two*b))) y)
    (weighted : ∀ s : PTm n, Γ ⊢[PRAAx] bounded (ap2 F s x) (M*unit s+K) (unit s)) :
    Γ ⊢[PRAAx] bounded (ap2 G p y) (M*referenceTop q a b*unit p+referenceBottom q a b)
      (majorantBottom p q a b) := by
  let A := M*referenceTop q a b
  let D := referenceBottom q a b
  let C := cost M K (referenceTop q a b)
  let t := precision (ap2 G p y) (A*unit p+D) (D*unit p) (one+C)
  let w := multiplyData F decayF x (decayData a (two*b))
  have raw := cross_at _ _ _ _ t p same
  have near : Γ ⊢[PRAAx] distanceBounded (ap2 G p y) (ap2 (multiplyF F decayF) t w)
      (unit t+one*unit p) (unit p*unit t) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive t) (unit_positive p)) raw)
  exact slack_removal_at _ _ _ (one+C) (majorant_bottom_positive p q a b)
    (reference_observation_slack _ _ A D one C p t (reference_bottom_positive q a b) near
      (integrand_product_envelope F x t q a b M K hb weighted))

theorem original_upper_tail_pointwise (p q z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) :
    Γ ⊢[PRAAx] bounded (sample p z B a b) (majorantTop p q R a b) (majorantBottom p q a b) :=
  bound_congr (sample_at p z B a b).eqSymm (.eqRefl _) (.eqRefl _)
    (half_decay_product_bound halfWeightedF nameF (halfWeightedData z B a b) (data z B a b)
      p q a b (majorant R) (productSlack a R) h.andE₂.andE₁.andE₂
      (original_integrand_half_decay_factors z B a b (old_source z R B a b h))
      (fun t => original_weighted_half_decay_sample t z R B a b h))

theorem original_Euler_integrand_upper_tail_pointwise_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      bounded (sample (var 0) (var 2) (var 4) (var 5) (var 6))
        (majorantTop (var 0) (var 1) (var 3) (var 5) (var 6)) (majorantBottom (var 0) (var 1) (var 5) (var 6))) :=
  closeUniv 7 (.impI (original_upper_tail_pointwise _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUpperTailPointwise
