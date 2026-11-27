import IPRADerivations.Analysis.Euler.Integration.Incomplete.Endpoints.GaussianEulerIncompleteSmallRationalEndpoint
import IPRADerivations.Analysis.Gamma.Integrals.CompactQuadrature.GaussianGammaCompactCutoffGeometry
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport

/-!
# Original Euler tails at quadratically mapped cutoff endpoints

At every n >= k+c+d, the map (c/d)u^2 sends the original lower
endpoint below eta_k and the original upper endpoint above top_k.
The checked arbitrary-small-rational incomplete integral estimate then
controls the actual lower omitted tail at the mapped rational endpoint.
Its actual upper incomplete name approaches the unchanged Euler
improper name with the original root-rate coefficient A. A finite upper
truncation at the other mapped endpoint is a separate obligation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerQuadraticLowerEndpoint

open_ipra
open GaussianGammaIntegralCutoffs (height etaDen top)
open GaussianEulerIncompleteName (lowerF upperF)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianNameEquivalence (cross_refl)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {ℓ : ℕ} {Γ : List (Fm PTm ℓ)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def source (z R B A c d : PTm ℓ) : Fm PTm ℓ :=
  GaussianEulerIntegralGammaIdentification.source z R B A ⋏ (le one c ⋏ le one d)
def minimumIndex (k c d : PTm ℓ) : PTm ℓ := k+c+d
def denominator (n A R d : PTm ℓ) : PTm ℓ := d*etaDen n A R*etaDen n A R
def data (n z R B A c d : PTm ℓ) : PTm ℓ :=
  GaussianEulerIncompleteName.data z R B A c (denominator n A R d)
def gridDenominator (n A R d M : PTm ℓ) : PTm ℓ := d*(etaDen n A R*M)*(etaDen n A R*M)
def gridData (n M z R B A c d : PTm ℓ) : PTm ℓ :=
  GaussianEulerIncompleteName.data z R B A (c*M*M) (gridDenominator n A R d M)

ipra_subst source
ipra_subst minimumIndex
ipra_subst denominator [etaDen, height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst data
ipra_subst gridDenominator [etaDen, height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst gridData

theorem index_after (k c d : PTm ℓ) : Γ ⊢[PRAAx] le k (minimumIndex k c d) :=
  le_of_eq_add (d := c+d) (by unfold minimumIndex; ipra_ring)
theorem index_c (k c d : PTm ℓ) : Γ ⊢[PRAAx] le c (minimumIndex k c d) :=
  le_of_eq_add (d := k+d) (by unfold minimumIndex; ipra_ring)
theorem index_d (k c d : PTm ℓ) : Γ ⊢[PRAAx] le d (minimumIndex k c d) := le_add_left _ _

theorem height_after (n A R : PTm ℓ) : Γ ⊢[PRAAx] le n (height n A R) :=
  le_of_eq_add (d := A+GaussianGammaIntegralCutoffs.tailCoefficient R+num 10) (by unfold height; ipra_ring)

theorem eta_dominates_index (n A R : PTm ℓ) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx] le n (etaDen n A R) := by
  have exponent : Γ ⊢[PRAAx] le n (A*height n A R) :=
    le_trans (height_after n A R) (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right (height n A R) hA))
  exact le_trans (AnalyticNumberTheory.ZetaFiniteContract.le_pow_self n) (GaussianExponentialReference.unit_monotone exponent)

theorem eta_monotone (k n A R : PTm ℓ) (h : Γ ⊢[PRAAx] le k n) : Γ ⊢[PRAAx] le (etaDen k A R) (etaDen n A R) :=
  le_congr (by ipra_ring) (GaussianGammaCompactCutoffGeometry.eta_den_refinement k n A R h).eqSymm
    (mul_le_mul_right (etaDen k A R) (GaussianGammaCompactCutoffGeometry.ratio_positive k n A))

theorem denominator_positive (n A R d : PTm ℓ) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx] le one (denominator n A R d) :=
  positive_product _ _ (positive_product _ _ hd (GaussianGammaIntegralCutoffs.eta_den_positive n A R))
    (GaussianGammaIntegralCutoffs.eta_den_positive n A R)

/-- The mapped lower endpoint c/(d*eta_n^2) is no larger than eta_k. -/
theorem lower_containment (k n A R c d : PTm ℓ) (hA : Γ ⊢[PRAAx] le one A) (hd : Γ ⊢[PRAAx] le one d)
    (hn : Γ ⊢[PRAAx] le (minimumIndex k c d) n) : Γ ⊢[PRAAx]
    le (c*etaDen k A R) (denominator n A R d) := by
  have cap := le_trans (index_c k c d) hn
  have old := le_trans (index_after k c d) hn
  have first := AnalyticNumberTheory.PhiLower.le_mul_mono (le_trans cap (eta_dominates_index n A R hA)) (eta_monotone k n A R old)
  have second := mul_le_mul_right (etaDen n A R*etaDen n A R) hd
  exact le_trans first (le_congr (by ipra_ring) (by unfold denominator; ipra_ring) second)

/-- The mapped upper endpoint c*top_n^2/d is no smaller than top_k. -/
theorem upper_containment (k n A R c d : PTm ℓ) (hc : Γ ⊢[PRAAx] le one c)
    (hn : Γ ⊢[PRAAx] le (minimumIndex k c d) n) : Γ ⊢[PRAAx]
    le (d*top k A R) (c*top n A R*top n A R) := by
  have cap := le_trans (index_d k c d) hn
  have ht : Γ ⊢[PRAAx] le (height n A R) (top n A R) :=
    le_of_eq_add (d := height n A R) (by unfold top; ipra_ring)
  have first := AnalyticNumberTheory.PhiLower.le_mul_mono (le_trans cap (le_trans (height_after n A R) ht))
    (GaussianGammaCompactCutoffGeometry.top_monotone k n A R (le_trans (index_after k c d) hn))
  have second := mul_le_mul_right (top n A R*top n A R) hc
  exact le_trans first (le_congr (by ipra_ring) (by ipra_ring) second)

theorem endpoint_source (k n z R B A c d : PTm ℓ) (hs : Γ ⊢[PRAAx] source z R B A c d)
    (hn : Γ ⊢[PRAAx] le (minimumIndex k c d) n) : Γ ⊢[PRAAx]
    GaussianEulerIncompleteSmallRationalEndpoint.source z R B A k c (denominator n A R d) :=
  .andI (.andI hs.andE₁ (.andI hs.andE₂.andE₁ (denominator_positive n A R d hs.andE₂.andE₂)))
    (lower_containment k n A R c d hs.andE₁.andE₁.andE₁ hs.andE₂.andE₂ hn)

theorem original_lower_bound (p k n z R B A c d : PTm ℓ) (hs : Γ ⊢[PRAAx] source z R B A c d)
    (hn : Γ ⊢[PRAAx] le (minimumIndex k c d) n) : Γ ⊢[PRAAx]
    bounded (ap2 lowerF p (data n z R B A c d))
      (A*unit p+unit (height k A R)) (unit (height k A R)*unit p) :=
  GaussianEulerIncompleteSmallRationalEndpoint.original_lower_small_rational_bound p z R B A k c (denominator n A R d)
    (endpoint_source k n z R B A c d hs hn)

theorem original_dyadic_lower_bound (p k n z R B A c d : PTm ℓ) (hs : Γ ⊢[PRAAx] source z R B A c d)
    (hn : Γ ⊢[PRAAx] le (minimumIndex k c d) n) : Γ ⊢[PRAAx]
    bounded (ap2 lowerF p (data n z R B A c d)) (unit p+unit (k+num 6)) (unit p*unit (k+num 6)) := by
  have budget : Γ ⊢[PRAAx] le (A*unit (k+num 6)) (unit (height k A R)) :=
    le_trans (mul_le_mul_right (unit (k+num 6)) (le_add_right A (GaussianGammaIntegralCutoffs.tailCoefficient R)))
      (le_of_lt (GaussianGammaIntegralCutoffs.omitted_tail_budget k A R))
  apply GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (unit_positive _) (unit_positive _)) (positive_product _ _ (unit_positive _) (unit_positive _))
    ?_ (original_lower_bound p k n z R B A c d hs hn)
  ipra_le (𝔞(unit p))^2*sl budget

/-- The unchanged actual upper incomplete program at the mapped lower
endpoint approaches the original whole Euler name with the same root rate. -/
theorem original_upper_to_Euler_rate (k n z R B A c d : PTm ℓ) (hs : Γ ⊢[PRAAx] source z R B A c d)
    (hn : Γ ⊢[PRAAx] le (minimumIndex k c d) n) : Γ ⊢[PRAAx]
    independentRate upperF GaussianEulerImproperName.nameF (data n z R B A c d) (GaussianEulerImproperName.data z R B A)
      A (unit (height k A R)) := by
  have s := endpoint_source k n z R B A c d hs hn
  have hu := (GaussianEulerIncompleteName.original_regular_names z R B A c (denominator n A R d) s.andE₁).andE₂
  exact GaussianNamedRateTransport.transport upperF gammaF upperF GaussianEulerImproperName.nameF
    (data n z R B A c d) (gammaData z R B A) (data n z R B A c d) (GaussianEulerImproperName.data z R B A)
    A (unit (height k A R)) (unit_positive _)
    (GaussianEulerIncompleteSmallRationalEndpoint.original_upper_small_rational_rate z R B A k c (denominator n A R d) s)
    (cross_refl _ _ hu) (GaussianEulerIntegralGammaIdentification.original_Euler_integral_is_Gamma z R B A hs.andE₁)

/-- Retain the literal M-squared encoding of the image of the first
original affine-grid point. No endpoint-encoding equality is assumed. -/
theorem grid_endpoint_source (k n M z R B A c d : PTm ℓ) (hs : Γ ⊢[PRAAx] source z R B A c d)
    (hn : Γ ⊢[PRAAx] le (minimumIndex k c d) n) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    GaussianEulerIncompleteSmallRationalEndpoint.source z R B A k (c*M*M) (gridDenominator n A R d M) := by
  have ee := positive_product _ _ (GaussianGammaIntegralCutoffs.eta_den_positive n A R) hM
  have cp := positive_product _ _ (positive_product _ _ hs.andE₂.andE₁ hM) hM
  have dp := positive_product _ _ (positive_product _ _ hs.andE₂.andE₂ ee) ee
  have raw := mul_le_mul_right (M*M) (lower_containment k n A R c d hs.andE₁.andE₁.andE₁ hs.andE₂.andE₂ hn)
  have bound : Γ ⊢[PRAAx] le ((c*M*M)*etaDen k A R) (gridDenominator n A R d M) :=
    le_congr (by ipra_ring) (by unfold denominator gridDenominator; ipra_ring) raw
  exact .andI (.andI hs.andE₁ (.andI cp dp)) bound

theorem original_grid_lower_bound (p k n M z R B A c d : PTm ℓ) (hs : Γ ⊢[PRAAx] source z R B A c d)
    (hn : Γ ⊢[PRAAx] le (minimumIndex k c d) n) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    bounded (ap2 lowerF p (gridData n M z R B A c d))
      (A*unit p+unit (height k A R)) (unit (height k A R)*unit p) :=
  GaussianEulerIncompleteSmallRationalEndpoint.original_lower_small_rational_bound p z R B A k (c*M*M)
    (gridDenominator n A R d M) (grid_endpoint_source k n M z R B A c d hs hn hM)

theorem original_grid_upper_to_Euler_rate (k n M z R B A c d : PTm ℓ) (hs : Γ ⊢[PRAAx] source z R B A c d)
    (hn : Γ ⊢[PRAAx] le (minimumIndex k c d) n) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    independentRate upperF GaussianEulerImproperName.nameF (gridData n M z R B A c d) (GaussianEulerImproperName.data z R B A)
      A (unit (height k A R)) := by
  have s := grid_endpoint_source k n M z R B A c d hs hn hM
  have hu := (GaussianEulerIncompleteName.original_regular_names z R B A (c*M*M) (gridDenominator n A R d M) s.andE₁).andE₂
  exact GaussianNamedRateTransport.transport upperF gammaF upperF GaussianEulerImproperName.nameF
    (gridData n M z R B A c d) (gammaData z R B A) (gridData n M z R B A c d) (GaussianEulerImproperName.data z R B A)
    A (unit (height k A R)) (unit_positive _)
    (GaussianEulerIncompleteSmallRationalEndpoint.original_upper_small_rational_rate z R B A k (c*M*M) (gridDenominator n A R d M) s)
    (cross_refl _ _ hu) (GaussianEulerIntegralGammaIdentification.original_Euler_integral_is_Gamma z R B A hs.andE₁)

theorem actual_quadratically_mapped_original_lower_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏ le (minimumIndex (var 1) (var 7) (var 8)) (var 2)) ⟶
      bounded (ap2 lowerF (var 0) (data (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (unit (var 0)+unit (var 1+num 6)) (unit (var 0)*unit (var 1+num 6))) :=
  closeUniv 9 (.impI (original_dyadic_lower_bound _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_mapped_lower_endpoint_upper_integral_Euler_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⋏ le (minimumIndex (var 0) (var 6) (var 7)) (var 1)) ⟶
      independentRate upperF GaussianEulerImproperName.nameF (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (GaussianEulerImproperName.data (var 2) (var 3) (var 4) (var 5)) (var 5) (unit (height (var 0) (var 5) (var 3)))) :=
  closeUniv 8 (.impI (original_upper_to_Euler_rate _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerQuadraticLowerEndpoint
