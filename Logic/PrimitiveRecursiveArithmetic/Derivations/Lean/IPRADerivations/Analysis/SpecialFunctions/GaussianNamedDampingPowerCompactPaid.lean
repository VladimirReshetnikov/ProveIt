import IPRADerivations.Analysis.SpecialFunctions.GaussianNamedDampingPowerCompactFrozen
import IPRADerivations.Analysis.Integration.GaussianCompactMeshIndependence

/-!
# Returned compact observations at a paid parameter clock

Both ordinary compact names keep their original clocks and meshes. An
affine common refinement transports the frozen-parameter bound back to
the returned observations. The parameter clock uses only the compact
interval and uniform source bounds and is independent of the rational
sample denominators.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerCompactPaid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedDampingPowerCompact (source evaluatorF fixedData lipschitz nameF data kernel_source_at compact_input)
open GaussianNamedDampingPowerCompactFrozen (rationalFixedData quadrature_distance)
open GaussianNamedDampingPowerFrozen (budget actual_rational_source)
open GaussianNamedPositiveLogarithm (numerator denominator)
open GaussianCompactRiemannName (grid grid_inside mesh precision sample quadrature)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "rationalEvaluator" => GaussianEulerPowerScalingCompactName.evaluatorF
local notation "rationalLipschitz" => GaussianEulerPowerScalingCompactRate.lipschitz

def parameterClock (p Rz C R E T : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (budget Rz C R E T*T) (p+num 6)
def rationalNameData (F G : PR 2) (k z Rz B x y C R a W E T : PTm n) : PTm n :=
  GaussianEulerPowerScalingCompactName.data z Rz B (numerator G k y) (denominator G k y)
    (numerator F k x) (denominator F k x) R C a W E T

theorem rational_source (F G : PR 2) (k z Rz B x y C₀ C R₀ R a W E T : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z Rz B x y C₀ C R₀ R a W E T) : Γ ⊢[PRAAx]
    GaussianEulerPowerScalingCompactName.source z Rz B (numerator G k y) (denominator G k y)
      (numerator F k x) (denominator F k x) R C a W E T := by
  let t := grid zero one a W E
  have ht := grid_inside (Γ := Γ) zero one a W E hs.andE₁.andE₂.andE₁ hs.andE₁.andE₁.andE₂.andE₁
    (le_refl one) (zero_le one)
  have hs' := kernel_source_at F G z Rz B x y C₀ C R₀ R a W E T t hs ht
  exact .andI hs.andE₁ (actual_rational_source F G k z Rz B x y C₀ C R₀ R E T (fstT t) (sndT t) hs').andE₁

private theorem budget_compare (W E T A K U V : PTm n)
    (hw : Γ ⊢[PRAAx] le W (E*T)) (ha : Γ ⊢[PRAAx] le (A*T*K) U) (ht : Γ ⊢[PRAAx] le (T*K) V) :
    Γ ⊢[PRAAx] le ((W*(A*V*V+U*(V+V)))*K) (num 3*(E*(U*V*V))) := by
  ipra_le 𝔞((A*V*V+U*(V+V))*K)*sl hw + 𝔞(E*V*V)*sl ha + 𝔞(two*E*U*V)*sl ht

theorem original_paid_observations (F G : PR 2) (p k z Rz B x y C₀ C R₀ R a W E T : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z Rz B x y C₀ C R₀ R a W E T)
    (hk : Γ ⊢[PRAAx] le (parameterClock p Rz C R E T) k) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF F G) p (data z Rz B x y C R a W E T))
      (ap2 GaussianEulerPowerScalingCompactName.nameF p (rationalNameData F G k z Rz B x y C R a W E T))
      (num 9) (unit (p+num 6)) := by
  let X := evaluatorF F G
  let Y := rationalEvaluator
  let x₀ := fixedData z B x y
  let y₀ := rationalFixedData F G k z B x y C
  let L := lipschitz Rz C R E T
  let M := rationalLipschitz Rz R C E T
  let J := precision p T
  let N := mesh p L T*mesh p M T
  let K := unit (p+num 6)
  let A := budget Rz C R E T
  have hx := compact_input F G z Rz B x y C₀ C R₀ R a W E T hs
  have hy := GaussianEulerPowerScalingCompactName.compact_input z Rz B (numerator G k y) (denominator G k y)
    (numerator F k x) (denominator F k x) R C a W E T (rational_source F G k z Rz B x y C₀ C R₀ R a W E T hs)
  have nL := GaussianCompactRiemannName.mesh_positive (Γ := Γ) p L T
  have nR := GaussianCompactRiemannName.mesh_positive (Γ := Γ) p M T
  have hK := unit_positive (Γ := Γ) (p+num 6)
  have hE := hx.andE₂.andE₁
  have later := GaussianCompactRiemannName.dyadic_monotone (Γ := Γ) (parameterClock p Rz C R E T) k hk
  have paid : Γ ⊢[PRAAx] le (A*T*K) (unit k) :=
    le_trans (GaussianFastValueCut.query_budget (A*T) (p+num 6)) later
  have left := distance_congr (GaussianCompactRiemannName.quadrature_index_congr X J (mesh p M T*mesh p L T) N
      a W E x₀ (mul_comm _ _)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianCompactMeshIndependence.arbitrary_refinement X p J (mesh p M T) a W E L T x₀ hx nR (le_refl J))
  have right := GaussianCompactMeshIndependence.arbitrary_refinement Y p J (mesh p L T) a W E M T y₀ hy nL (le_refl J)
  have raw := quadrature_distance F G J J k N z Rz B x y C₀ C R₀ R a W E T hs (positive_product _ _ nL nR)
  have middle : Γ ⊢[PRAAx] distanceBounded (quadrature X J N a W E x₀) (quadrature Y J N a W E y₀) (num 3) K :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hE (denominator_positive (unit k) J J (unit_positive k))) hK
      (budget_compare W E T A K (unit k) (unit J) hx.andE₂.andE₂.andE₁ paid (le_congr (mul_comm K T) (.eqRefl _) (GaussianCompactRiemannName.precision_lower p T))) raw
  exact distance_congr (GaussianCompactRiemannName.name_at X p a W E L T x₀).eqSymm
    (GaussianCompactRiemannName.name_at Y p a W E M T y₀).eqSymm (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ (quadrature X J N a W E x₀) _ _ _ K hK (distance_symmetric _ _ _ _ hK left)
      (distance_triangle_same _ (quadrature Y J N a W E y₀) _ _ _ K hK middle right))

theorem actual_named_power_damped_compact_paid_observations_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 15
      (source F G (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) (var 14) ⟶
        le (parameterClock (var 0) (var 3) (var 8) (var 10) (var 13) (var 14)) (var 1) ⟶
        distanceBounded (ap2 (nameF F G) (var 0) (data (var 2) (var 3) (var 4) (var 5) (var 6) (var 8) (var 10) (var 11) (var 12) (var 13) (var 14)))
          (ap2 GaussianEulerPowerScalingCompactName.nameF (var 0)
            (rationalNameData F G (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 8) (var 10) (var 11) (var 12) (var 13) (var 14)))
          (num 9) (unit (var 0+num 6))) :=
  closeUniv 15 (.impI (.impI (original_paid_observations F G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerCompactPaid
