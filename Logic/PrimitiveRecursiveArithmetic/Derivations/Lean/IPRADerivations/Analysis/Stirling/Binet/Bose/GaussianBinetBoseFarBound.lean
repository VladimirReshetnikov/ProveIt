import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBoseCubicGap
import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBoseIntegrandBound

/-!
# Inverse-square decay of the original second Binet integrand

The cubic bound is used at the actual inner clock of the reciprocal.
The original arctangent has linear growth. Their original normalized
product therefore has inverse-square decay, uniformly at all clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseFarBound

open_ipra
open GaussianBinetBoseCubicGap (cube cube_positive denominator_lower)
open GaussianBinetBoseDenominator (reciprocalF reciprocalData)
open GaussianBinetBoseIntegrandBound (nameF data)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianFastValueCut (exponent)
open GaussianNameArithmetic (multiplyModulus multiplyRaw multiply_at)
open GaussianRationalHorner (positive_product qmul qmul_canonical)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bounded_product bound_congr reciprocal_canonical)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Atan" => GaussianBinetArctangentQuadrature.nameF
local notation "atanData" => GaussianBinetArctangentQuadrature.data
local notation "Bose" => GaussianBinetBoseDenominator.nameF
local notation "boseData" => GaussianBinetBoseDenominator.data

theorem reciprocal_bound (p A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (ap2 reciprocalF p (reciprocalData A B)) (cube B) (cube A) := by
  let r := exponent (GaussianNameReciprocal.modulus B) p+GaussianNameReciprocal.anchor B
  let x := ap2 Bose r (boseData A B)
  let v := GaussianRationalReciprocal.reciprocal x
  have read : Γ ⊢[PRAAx] ap2 reciprocalF p (reciprocalData A B) ≐ v :=
    (GaussianNameReciprocal.name_at Bose B (boseData A B) p).eqTrans
      (GaussianExponentialReference.recode_fixed v (reciprocal_canonical x))
  exact bound_congr read.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalLowerBounds.inverse_bound x (cube A) (cube B) (cube_positive A hA) (cube_positive B hB)
      (denominator_lower r A B hB))

theorem rational_time_bound (p X Y D sign A B K : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le D (K*X)) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data X Y D sign A B)) (K*B*B) (A*A) := by
  let x := atanData X Y D sign A B
  let y := reciprocalData A B
  let q := exponent (multiplyModulus Atan reciprocalF x y) p
  let u := ap2 Atan q x
  let v := ap2 reciprocalF q y
  have ht := GaussianBinetArctangentQuadratureBound.name_bound q X Y D sign A B hz hB
  have hi := reciprocal_bound q A B hA hB
  have bx := positive_product _ _ hB hz.andE₁.andE₁
  have cb := cube_positive A hA
  have den := positive_product _ _ bx cb
  have both := bounded_product u v (A*D) (B*X) (cube B) (cube A) bx cb ht hi
  have read : Γ ⊢[PRAAx] ap2 nameF p (data X Y D sign A B) ≐ qmul u v :=
    (multiply_at Atan reciprocalF x y p).eqTrans
      (GaussianExponentialReference.recode_fixed (multiplyRaw Atan reciprocalF q x y) (qmul_canonical u v))
  have radius : Γ ⊢[PRAAx] le (((A*D)*cube B)*(A*A)) ((K*B*B)*((B*X)*cube A)) :=
    le_congr (by unfold cube; ipra_ring) (by unfold cube; ipra_ring)
      (mul_le_mul_right (cube A*cube B) hk)
  exact bound_congr read.eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ den (positive_product _ _ hA hA) radius both)

theorem integrand_bound (p X Y D sign A B U K : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B) (hU : Γ ⊢[PRAAx] le one U)
    (ha : Γ ⊢[PRAAx] le (U*B) A) (hk : Γ ⊢[PRAAx] le D (K*X)) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data X Y D sign A B)) K (U*U) :=
  bounded_radius_mono _ _ _ _ _ (positive_product _ _ hA hA) (positive_product _ _ hU hU)
    (le_congr (by ipra_ring) (mul_comm _ _) (mul_le_mul_right K (sq_le_sq ha)))
    (rational_time_bound p X Y D sign A B K hz hA hB hk)

theorem actual_second_Binet_integrand_inverse_square_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((source (var 1) (var 3) (var 4) ⋏ (le one (var 5) ⋏ le one (var 6))) ⋏
      (le one (var 7) ⋏ (le (var 7*var 6) (var 5) ⋏ le (var 3) (var 8*var 1))) ⟶
      bounded (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))) (var 8) (var 7*var 7)) :=
  closeUniv 9 (.impI (integrand_bound _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂.andE₁
    Prf.hyp0.andE₁.andE₂.andE₂ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetBoseFarBound
