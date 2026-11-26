import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBoseLiteralUniform
import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.GaussianBinetSecondDecayPiBridge

/-!
# Move actual literal Bose cells to a common frozen Pi clock

The literal exponential clock depends on the time tag. Since it is
later than the angular observation, the exponential can first be
compared at that observation and then against the frozen Pi row.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseLiteralFrozen

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetBoseExponential (expF expData exp_regular)
open GaussianBinetBoseLiteralPrefix (term)
open GaussianBinetBoseLiteralUniform (clock row_clock_later)
open GaussianBinetBoseSeriesRows (rowClock)
open GaussianBinetSecondDecayPiBridge (budget angular_row_error)
open GaussianBinetSecondDecayPointwise (angle row frozenPiNumerator)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRightHalfPlaneLogarithm (source)
open GaussianStirlingConstant (piDenominator)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

theorem cell_error (p k j N a b T K X Y D sign : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hb : Γ ⊢[PRAAx] le one b) (ht : Γ ⊢[PRAAx] le a (T*b))
    (hK : Γ ⊢[PRAAx] le D (K*X)) (hk : Γ ⊢[PRAAx] le (budget (succ j) T*unit p) (unit k)) :
    Γ ⊢[PRAAx] distanceBounded
      (qmul (angle p X Y D sign a b) (term j (clock p N a b) a b))
      (row p X Y D sign a b (frozenPiNumerator (succ j) k) (piDenominator k)) (num 5*K*T) (unit p) := by
  let m := succ j
  let q := clock p N a b
  let r := rowClock q b
  let x := expData true (m*a) b
  let v := angle p X Y D sign a b
  let left := qmul v (term j q a b)
  let middle := qmul v (ap2 expF p x)
  let right := row p X Y D sign a b (frozenPiNumerator m k) (piDenominator k)
  have hr : Γ ⊢[PRAAx] le p r := le_trans (le_add_right p _) (row_clock_later q b)
  have near := GaussianNamedProductObservationBound.late_observation expF x p r (exp_regular true (m*a) b hb) hr
  have hv : Γ ⊢[PRAAx] bounded v (K*T) one :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hb hz.andE₁.andE₁) (le_refl one)
      (by ipra_le 𝔞(D)*sl ht+𝔞(T)*𝔞(b)*sl hK)
      (GaussianBinetArctangentQuadratureBound.name_bound p X Y D sign a b hz hb)
  have hp := unit_positive (Γ := Γ) p
  have first : Γ ⊢[PRAAx] distanceBounded left middle ((K*T)*two) (unit p) :=
    GaussianApproximateInverseDistance.multiply_distance v (term j q a b) (ap2 expF p x) (K*T) two (unit p) hp hv near
  have later := angular_row_error p k m a b T K X Y D sign hz hb ht hK hk
  exact distance_congr (.eqRefl left) (.eqRefl right) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same left middle right ((K*T)*two) (num 3*K*T) (unit p) hp first later)

end LeanProofs.IPRA.Analysis.GaussianBinetBoseLiteralFrozen
