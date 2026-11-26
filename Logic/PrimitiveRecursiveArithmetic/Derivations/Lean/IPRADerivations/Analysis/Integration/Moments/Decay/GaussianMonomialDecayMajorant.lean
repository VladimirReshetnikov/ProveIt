import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperTailScalar

/-!
# The actual monomial-decay name has the exact factorial half-decay majorant

The monomial is the literal canonical rational (a/b)^d, with numerical d.
Only existing constant/product/decay programs are used. The actual named
half-decay factorization and one finite-gap removal retain the exact
2^d*d! majorant, without replacing d by d+1 or assuming a power law.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianMonomialDecayMajorant

open_ipra
open GaussianEulerIntegrandName (decayF decayData)
open GaussianEulerUpperTailPointwise (referenceTop referenceBottom reference_bottom_positive majorantTop majorantBottom majorant_bottom_positive)
open GaussianEulerWeightedHalfDecay (majorant halfSample)
open GaussianEulerHalfDecayReference (scalar numerator denominator denominator_positive decay_reference_error reference_norm)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans cross_refl)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product power)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianReconstructionRoots (norm_from_distance)
open GaussianDominantPairAlgebra (radiusPoint radius_power)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianNamedSmallPerturbationTransport (productClock product_at)
open GaussianRationalSlackRemoval (slack precision slack_removal_at)
open RationalGaussianEmbedding (embed)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (a b : PTm n) : Fm PTm n := le one b ⋏ le b a
def monomial (d a b : PTm n) : PTm n := radiusPoint (pw a d) (pw b d)
def nameF : PR 2 := multiplyF constantF decayF
def data (d a b : PTm n) : PTm n := multiplyData constantF decayF (monomial d a b) (decayData a b)
def sample (p d a b : PTm n) : PTm n := ap2 nameF p (data d a b)
def halfWeightedF : PR 2 := multiplyF constantF decayF
def halfWeightedData (d a b : PTm n) : PTm n := multiplyData constantF decayF (monomial d a b) (decayData a (two*b))
def halfIntegrandF : PR 2 := multiplyF halfWeightedF decayF
def halfIntegrandData (d a b : PTm n) : PTm n := multiplyData halfWeightedF decayF (halfWeightedData d a b) (decayData a (two*b))
ipra_subst source
ipra_subst monomial
ipra_subst data [decayData, GaussianGammaFiniteApproximantName.exponentialInputData]
ipra_subst sample

theorem half_factorization (d a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    crossEquivalent halfIntegrandF nameF (halfIntegrandData d a b) (data d a b) := by
  let P := monomial d a b
  let D := decayData a (two*b)
  let E := decayData a b
  let D2 := GaussianEulerHalfDecayProduct.halfProductData a b
  have hp := constant_regular (Γ := Γ) P
  have hd := GaussianEulerHalfDecayProduct.decay_regular (Γ := Γ) a (two*b)
  have he := GaussianEulerHalfDecayProduct.decay_regular (Γ := Γ) a b
  have hs := GaussianNameArithmetic.multiply_fast decayF decayF D D hd hd
  exact cross_trans _ _ _ _ _ _
    (GaussianNameRingLaws.multiply_associative constantF decayF decayF P D D hp hd hd)
    (GaussianGammaAdjacentCutoff.multiply_cross constantF constantF (multiplyF decayF decayF) decayF
      P P D2 E hp hp hs he (cross_refl constantF P hp) (GaussianEulerHalfDecayProduct.original_decay_as_half_product a b hb))

theorem half_weighted_bound (p d a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    bounded (ap2 halfWeightedF p (halfWeightedData d a b))
      (majorant d*unit p+GaussianEulerWeightedHalfDecay.slack a d) (unit p) := by
  let P := monomial d a b
  let D := decayData a (two*b)
  let s := productClock constantF decayF P D p
  have hb := h.andE₁
  have ha := le_trans hb h.andE₂
  have h2 := (le_succ_self (Γ := Γ) one)
  have fraction := (GaussianDominantPairAlgebra.radius_congr (mul_comm two a) (mul_comm two b)).eqTrans
    (GaussianEulerWeightedHalfDecay.radius_rescale a b two hb h2)
  have weight : Γ ⊢[PRAAx] power (radiusPoint (two*a) (two*b)) d ≐ P :=
    (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl d) fraction).eqTrans (radius_power a b d hb)
  have raw := bound_congr (qmul_congr weight (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (GaussianEulerDecayFactorBounds.original_half_decay_factor_bound a (two*b) d s ha (positive_product _ _ h2 hb))
  have e := (product_at (Γ := Γ) constantF decayF P D p).eqTrans
    (qmul_congr (constant_at s P) (.eqRefl _))
  have grow : Γ ⊢[PRAAx] le (unit p) (unit s) := GaussianExponentialReference.unit_monotone (le_add_right p _)
  have compare : Γ ⊢[PRAAx] le ((majorant d*unit s+GaussianEulerWeightedHalfDecay.slack a d)*unit p)
      ((majorant d*unit p+GaussianEulerWeightedHalfDecay.slack a d)*unit s) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (le_refl (majorant d*unit p*unit s))
        (mul_le_mul_right (GaussianEulerWeightedHalfDecay.slack a d) grow))
  exact bound_congr e.eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ (unit_positive s) (unit_positive p) compare raw)

private theorem half_decay_from_reference (q s a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
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

private theorem multiply_approximate_bounds (x y M K N D U : PTm n)
    (hd : Γ ⊢[PRAAx] le one D) (hu : Γ ⊢[PRAAx] le one U)
    (hx : Γ ⊢[PRAAx] bounded x (M*U+K) U)
    (hy : Γ ⊢[PRAAx] bounded y (N*U+D) (D*U)) : Γ ⊢[PRAAx]
    bounded (qmul x y) (M*N*U+cost M K N*D) (D*U) := by
  have hDU := positive_product D U hd hu
  have h1 : Γ ⊢[PRAAx] le (K*N*U) (K*N*U*D) :=
    le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (K*N*U) hd)
  have h2 : Γ ⊢[PRAAx] le (K*D) (K*D*U) :=
    le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (K*D) hu)
  have cmp : Γ ⊢[PRAAx] le ((M*U+K)*(N*U+D)) ((M*N*U+cost M K N*D)*U) :=
    le_congr (by ipra_ring) (by unfold cost; ipra_ring)
      (add_le_add₂ (le_refl (M*N*U*U+M*D*U)) (add_le_add₂ h1 h2))
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ hu hDU) hDU _
    (bounded_product x y _ _ _ _ hu hDU hx hy)
  exact le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right (D*U) cmp)

private theorem integrand_product_envelope (p q d a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] bounded (ap2 halfIntegrandF p (halfIntegrandData d a b))
      (majorant d*referenceTop q a b*unit p+cost (majorant d) (GaussianEulerWeightedHalfDecay.slack a d) (referenceTop q a b)*referenceBottom q a b)
      (referenceBottom q a b*unit p) := by
  let x := halfWeightedData d a b
  let y := decayData a (two*b)
  let s := productClock halfWeightedF decayF x y p
  let M := majorant d
  let K := cost M (GaussianEulerWeightedHalfDecay.slack a d) (referenceTop q a b)
  let N := referenceTop q a b
  let D := referenceBottom q a b
  have hd : Γ ⊢[PRAAx] le one D := reference_bottom_positive q a b
  have e := product_at (Γ := Γ) halfWeightedF decayF x y p
  have est : Γ ⊢[PRAAx] bounded (qmul (ap2 halfWeightedF s x) (ap2 decayF s y))
      (M*N*unit s+K*D) (D*unit s) :=
    multiply_approximate_bounds _ _ M (GaussianEulerWeightedHalfDecay.slack a d) N D (unit s) hd (unit_positive s)
      (half_weighted_bound s d a b h)
      (half_decay_from_reference q s a b h.andE₁)
  have order : Γ ⊢[PRAAx] le (unit p) (unit s) :=
    GaussianExponentialReference.unit_monotone (le_add_right p _)
  have cmp : Γ ⊢[PRAAx] le ((M*N*unit s+K*D)*(D*unit p)) ((M*N*unit p+K*D)*(D*unit s)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (le_refl (M*N*unit p*unit s*D)) (mul_le_mul_right (K*D*D) order))
  exact bound_congr e.eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ (positive_product _ _ hd (unit_positive s))
      (positive_product _ _ hd (unit_positive p)) cmp est)

private theorem observation_slack (p q t d a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] slack (sample p d a b) (majorantTop p q d a b) (majorantBottom p q a b)
      (succ (cost (majorant d) (GaussianEulerWeightedHalfDecay.slack a d) (referenceTop q a b))) t := by
  let x := sample p d a b
  let y := ap2 halfIntegrandF t (halfIntegrandData d a b)
  let U := unit p
  let V := unit t
  let D := referenceBottom q a b
  let K := cost (majorant d) (GaussianEulerWeightedHalfDecay.slack a d) (referenceTop q a b)
  let A := majorant d*referenceTop q a b
  have hx := half_factorization d a b h.andE₁
  have den : Γ ⊢[PRAAx] le one (U*V) := positive_product _ _ (unit_positive p) (unit_positive t)
  have raw := GaussianNameEquivalence.cross_at _ _ _ _ t p hx
  have e : Γ ⊢[PRAAx] distanceBounded x y (U+V) (U*V) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive t) (unit_positive p)) raw)
  have bound := norm_from_distance x y (U+V) (U*V) (A*V+K*D) (D*V)
    den (positive_product _ _ (reference_bottom_positive q a b) (unit_positive t))
    e (integrand_product_envelope t q d a b h)
  apply bounded_radius_mono _ _ _ _ _
    (positive_product _ _ den (positive_product _ _ (reference_bottom_positive q a b) (unit_positive t)))
    (positive_product _ _ (majorant_bottom_positive p q a b) (unit_positive t)) _ bound
  exact le_of_eq_add (d := zero) (by
    change Γ ⊢[PRAAx] ((A*U+D)*V+succ K*(D*U))*((U*V)*(D*V)) ≐
      ((U+V)*(D*V)+(A*V+K*D)*(U*V))*(D*U*V)+zero
    ipra_ring)

theorem original_upper_tail_pointwise (p q d a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] bounded (sample p d a b) (majorantTop p q d a b) (majorantBottom p q a b) := by
  let K := succ (cost (majorant d) (GaussianEulerWeightedHalfDecay.slack a d) (referenceTop q a b))
  let t := precision (sample p d a b) (majorantTop p q d a b) (majorantBottom p q a b) K
  exact slack_removal_at _ _ _ K (majorant_bottom_positive p q a b)
    (observation_slack p q t d a b h)

theorem actual_literal_monomial_decay_factorial_majorant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 3) (var 4) ⟶ bounded (sample (var 0) (var 2) (var 3) (var 4))
      (majorantTop (var 0) (var 1) (var 2) (var 3) (var 4)) (majorantBottom (var 0) (var 1) (var 3) (var 4))) :=
  closeUniv 5 (.impI (original_upper_tail_pointwise _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianMonomialDecayMajorant
