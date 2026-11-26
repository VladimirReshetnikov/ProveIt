import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.Lattices.GaussianEulerUnitSubstitutionLatticeComparison

/-!
# A separated numerical rate for the actual original unit lattice

The true decay mesh is the only term requiring the time-grid count first.
After that choice, the original chart query, independent rational lattice
and kernel observation can be refined separately. Exact multiplication
by their positive denominators retains all four error contributions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionLatticeRate

open_ipra
open GaussianEulerUnitSubstitutionLatticeGeometry (source disk start count denominator_positive)
open GaussianEulerUnitDecayInput (clock compactDenominator)
open GaussianEulerUnitKernelCompactRate (lipschitz)
open GaussianEulerCompactPowerMajorant (majorant)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def meshCoefficient (R C E T : PTm n) : PTm n := num 6*lipschitz R (disk E T)*C
def queryMinor (N R E T : PTm n) : PTm n :=
  lipschitz R (disk E T)*(num 20+two*N)+one+two*N*majorant R E T
def queryCoefficient (N R E T : PTm n) : PTm n := lipschitz R (compactDenominator E T)+queryMinor N R E T
def latticeCoefficient (N R E T : PTm n) : PTm n := lipschitz R (disk E T)+two*N*majorant R E T
def numerator (k q N R C E T M : PTm n) : PTm n :=
  meshCoefficient R C E T*unit k*M*unit q+
    queryCoefficient N R E T*(E*N)*M*unit q+
    latticeCoefficient N R E T*(E*N)*unit k*unit q+(E*N)*unit k*M
def denominator (k q N E M : PTm n) : PTm n := E*N*unit k*M*unit q

ipra_subst meshCoefficient
ipra_subst queryCoefficient [queryMinor]
ipra_subst latticeCoefficient
ipra_subst numerator
ipra_subst denominator

theorem numerical_coarsening (k q N R C E T M : PTm n) : Γ ⊢[PRAAx]
    le (GaussianEulerUnitSubstitutionLatticeComparison.numerator k q N R C E T M*denominator k q N E M)
      (numerator k q N R C E T M*GaussianEulerUnitSubstitutionLatticeComparison.denominator k q N E T M) := by
  have grow := GaussianExponentialReference.unit_monotone (Γ := Γ) (GaussianEulerUnitDecayInput.clock_later k E T)
  unfold numerator denominator meshCoefficient queryCoefficient queryMinor latticeCoefficient
    GaussianEulerUnitSubstitutionLatticeComparison.numerator GaussianEulerUnitSubstitutionLatticeComparison.denominator
    GaussianEulerUnitSubstitutionLatticeComparison.widthNumerator GaussianEulerUnitSubstitutionLatticeComparison.widthDenominator
    GaussianEulerUnitSubstitutionLatticeRows.anchorNumerator GaussianEulerUnitSubstitutionLatticeRows.anchorDenominator
    GaussianEulerUnitSubstitutionLatticeRows.pointNumerator GaussianEulerUnitSubstitutionLatticeRows.pointDenominator
    GaussianEulerUnitSubstitutionLatticeRows.displacementNumerator GaussianEulerUnitSubstitutionLatticeRows.displacementDenominator
    GaussianEulerUnitSubstitutionNearbyKernel.leadingNumerator GaussianEulerUnitSubstitutionNearbyKernel.leadingDenominator
    GaussianEulerUnitSubstitutionImageGrid.meshNumerator GaussianEulerUnitSubstitutionImageGrid.meshDenominator
    GaussianNamedInverseRate.rateNumerator GaussianNamedInverseRate.rateDenominator
  ipra_le (𝔞 (E*N)^2*𝔞 M^3*𝔞 (unit k)*𝔞 (unit (clock k E T))^3*𝔞 (unit q)^2*
    (𝔞 (lipschitz R (disk E T))*(20+2*𝔞 N)+1+2*𝔞 N*𝔞 (majorant R E T)))*sl grow

theorem rate_denominator_positive (k q N z R B a C E T M : PTm n) (h : Γ ⊢[PRAAx] source k N z R B a C E T M) :
    Γ ⊢[PRAAx] le one (denominator k q N E M) :=
  positive_product _ _ (positive_product _ _ (positive_product _ _
    (positive_product _ _ h.andE₁.andE₁.andE₁.andE₂.andE₁ h.andE₁.andE₂.andE₁) (unit_positive k))
    (denominator_positive _ _ _ _ _ _ _ _ _ _ h)) (unit_positive q)

theorem original_finite_bound (k q N z R B a C E T M : PTm n) (h : Γ ⊢[PRAAx] source k N z R B a C E T M) :
    Γ ⊢[PRAAx] distanceBounded
      (GaussianEulerUnitKernelLatticeSum.lattice q (count k N a C E T M) z B (start k N a C E T M) M)
      (GaussianEulerUnitSubstitutionDensity.density (clock k E T) N z B a C E)
      (numerator k q N R C E T M) (denominator k q N E M) :=
  distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (GaussianEulerUnitSubstitutionLatticeRows.anchor_denominator_positive k q N z R B a C E T M h)
      (GaussianEulerUnitSubstitutionLatticeComparison.width_denominator_positive k N z R B a C E T M h))
    (rate_denominator_positive k q N z R B a C E T M h) (numerical_coarsening k q N R C E T M)
    (GaussianEulerUnitSubstitutionLatticeComparison.original_finite_bound k q N z R B a C E T M h)


theorem actual_original_unit_lattice_separated_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (source (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
      distanceBounded (GaussianEulerUnitKernelLatticeSum.lattice (var 1)
        (count (var 0) (var 2) (var 6) (var 7) (var 8) (var 9) (var 10))
        (var 3) (var 5) (start (var 0) (var 2) (var 6) (var 7) (var 8) (var 9) (var 10)) (var 10))
      (GaussianEulerUnitSubstitutionDensity.density (clock (var 0) (var 8) (var 9)) (var 2) (var 3) (var 5) (var 6) (var 7) (var 8))
      (numerator (var 0) (var 1) (var 2) (var 4) (var 7) (var 8) (var 9) (var 10))
      (denominator (var 0) (var 1) (var 2) (var 8) (var 10))) :=
  closeUniv 11 (.impI (original_finite_bound _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionLatticeRate
