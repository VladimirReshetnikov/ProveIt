import IPRADerivations.Analysis.Euler.Integration.Parts.CompactNames.GaussianEulerIntegrationByPartsCompactNamedIdentity

/-!
# The original compact integration-by-parts residual at a later query

The normalization costs of the compact product and endpoint difference
depend on the interval. Pay those costs by computing a later query,
so the residual has a bound independent of the interval data.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsRawResidual

open_ipra
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianEulerIntegrationByPartsCompactNames (leftF leftData boundaryF boundaryData productModulus)
open GaussianEulerIntegrationByPartsCompactNameObservations (rawLeft left_readback boundary_readback)
open GaussianEulerIntegrationByPartsCompact (boundary)
open GaussianGammaEulerHeadShift (shifted)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def clock (t z R B a C E T : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (productModulus z R B a C E T+num 7+num 6) t

theorem clock_later (t z R B a C E T : PTm n) : Γ ⊢[PRAAx] le t (clock t z R B a C E T) :=
  le_add_right _ _

theorem original_raw_residual (t q z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T)
    (hq : Γ ⊢[PRAAx] le (clock t z R B a C E T) q) : Γ ⊢[PRAAx]
    distanceBounded (rawLeft q z R B a C E T) (boundary q z B a C E) (num 4) (unit t) := by
  let K := productModulus z R B a C E T+num 7
  let L := ap2 leftF q (leftData z R B a C E T)
  let P := ap2 boundaryF q (boundaryData z B a C E)
  have hT := unit_positive (Γ := Γ) t
  have hQ := unit_positive (Γ := Γ) q
  have tq := unit_monotone (le_trans (clock_later t z R B a C E T) hq)
  have budget := le_trans (GaussianFastValueCut.query_budget (K+num 6) t) (unit_monotone hq)
  have small (J : PTm n) (hJ : Γ ⊢[PRAAx] le J (K+num 6)) : Γ ⊢[PRAAx] le (J*unit t) (one*unit q) :=
    le_congr (.eqRefl _) (one_mul _).eqSymm (le_trans (mul_le_mul_right (unit t) hJ) budget)
  have first : Γ ⊢[PRAAx] distanceBounded (rawLeft q z R B a C E T) L one (unit t) :=
    distance_symmetric _ _ _ _ hT (distance_radius_mono _ _ _ _ _ _ hQ hT (small K (le_add_right _ _))
      (left_readback q z R B a C E T h))
  have middle : Γ ⊢[PRAAx] distanceBounded L P two (unit t) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hQ hQ) hT
      (by ipra_le (𝔞(two*unit q))*sl tq)
      (GaussianNameEquivalence.cross_at _ _ _ _ q q
        (GaussianEulerIntegrationByPartsCompactNamedIdentity.original_compact_IBP_names z R B a C E T h))
  have last : Γ ⊢[PRAAx] distanceBounded P (boundary q z B a C E) one (unit t) :=
    distance_radius_mono _ _ _ _ _ _ hQ hT (small (num 6) (le_add_left _ _)) (boundary_readback q z R B a C E T h)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ L _ _ _ _ hT first (distance_triangle_same L P _ _ _ _ hT middle last))

theorem actual_original_compact_Euler_raw_residual_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      ((intervalSource (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏
         le (clock (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) (var 1)) ⟶
        distanceBounded (rawLeft (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
          (boundary (var 1) (var 2) (var 4) (var 5) (var 6) (var 7)) (num 4) (unit (var 0))) :=
  closeUniv 9 (.impI (original_raw_residual _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsRawResidual
