import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.GaussianEulerUnitSubstitutionArbitraryPanels
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.GaussianEulerUnitKernelNestedObservations

/-!
# The real companion gap for an arbitrary unit panel

The original real-parameter quadrature on the arbitrary panel lies
above the original inner reference quadrature up to the observed
one-sided error. Both the inner reference and the later containing
ordinary quadrature have known rates to the original projected Gamma
name. Combining these statements bounds the signed gap used to
control the two omitted strips.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionProjectedGap

open_ipra
open GaussianEulerUnitSubstitutionOrdinaryImproper (source)
open GaussianEulerUnitSubstitutionOrdinaryContainment (containmentIndex containment_index_later)
open GaussianEulerUnitSubstitutionArbitraryPanels (exhaustionSource innerIndex surrounding_sources)
open GaussianEulerUnitSubstitutionCofinalPanelRate
  (panelData original_safe_observations projected_gamma_source)
open GaussianEulerUnitKernelCompactName (nameF data)
open GaussianEulerVerticalNativeProjection (argument)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalValueBounds (upper upper_triangle upper_of_radius upper_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem late_cofinal_observations (p q u t z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (ht : Γ ⊢[PRAAx] le u t) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (panelData t z R B A)) (ap2 gammaF q (gammaData z R B A))
      (rateNumerator two (unit u) p q) (rateDenominator (unit u) p q) := by
  have grow := GaussianExponentialReference.unit_monotone ht
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ (unit_positive t))
    (denominator_positive _ _ _ (unit_positive u))
    (by unfold rateNumerator rateDenominator
        ipra_le (𝔞 (unit p))^2*(𝔞 (unit q))^2*2*sl grow)
    (original_safe_observations p q t z R B A h)

def gapNumerator (s u : PTm n) : PTm n := two*unit u+num 12*unit (innerIndex s)
def gapDenominator (s u : PTm n) : PTm n := unit (innerIndex s)*unit u

theorem original_projected_gap (s u z R B A a C E G : PTm n)
    (h : Γ ⊢[PRAAx] exhaustionSource s z R B A a C E G) : Γ ⊢[PRAAx]
    upper (fstT (ap2 nameF u (panelData (containmentIndex u E) (argument z) R B A)))
      (fstT (ap2 nameF u (data (argument z) R B a C E G))) (gapNumerator s u) (gapDenominator s u) := by
  let b := innerIndex s
  let t := containmentIndex u E
  let Z := argument z
  let I := unit b
  let U := unit u
  let m := ap2 nameF u (panelData b Z R B A)
  let w := ap2 nameF u (panelData t Z R B A)
  let g := ap2 gammaF u (gammaData Z R B A)
  let D := I*U
  have hI := unit_positive (Γ := Γ) b
  have hU := unit_positive (Γ := Γ) u
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hI hU
  have hz : Γ ⊢[PRAAx] source Z R B A := projected_gamma_source z R B A h.andE₁
  have outer : Γ ⊢[PRAAx] distanceBounded w g (rateNumerator two U u u) (rateDenominator U u u) :=
    late_cofinal_observations u u u t Z R B A hz (containment_index_later u E)
  have inner : Γ ⊢[PRAAx] distanceBounded m g (rateNumerator two I u u) (rateDenominator I u u) :=
    original_safe_observations u u b Z R B A hz
  have outerBound : Γ ⊢[PRAAx] distanceBounded w g (num 4*I) D :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ hU) hD
      (by unfold rateNumerator rateDenominator; dsimp only [D,U]; ipra_le 0) outer
  have innerBound : Γ ⊢[PRAAx] distanceBounded g m (two*U+two*I) D :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ hI) hD
      (by unfold rateNumerator rateDenominator; dsimp only [D,U]; ipra_le 0)
      (distance_symmetric _ _ _ _ (denominator_positive _ _ _ hI) inner)
  have combined := distance_triangle_same _ _ _ _ _ _ hD outerBound innerBound
  have coordinate := upper_of_radius _ _ _ _
    (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ hD combined)
  have middle := GaussianEulerUnitKernelNestedObservations.real_middle_upper u u z R B a C E G _ _ _ _
    (surrounding_sources s u z R B A a C E G h).andE₁
  have tail : Γ ⊢[PRAAx] upper (fstT m) (fstT (ap2 nameF u (data Z R B a C E G))) (num 6*I) D :=
    upper_mono _ _ _ _ _ _ (positive_product _ _ hU hU) middle (by dsimp only [D,U]; ipra_le 0)
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ hD hD)
    (upper_triangle _ _ _ _ _ _ _ coordinate tail) (by dsimp only [D,I,U,gapNumerator,gapDenominator,b]; ipra_le 0)

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionProjectedGap
