import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetArctangentQuadratureBound
import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetBoseDenominator

/-!
# Bound the actual second Binet integrand at the lower endpoint

Both original factor observations retain their sampling clocks. The
arctangent has norm at most t / Re(z), and the actual Bose reciprocal
has norm at most 1 / (4t), so the product remains bounded independently
of positive rational t.
-/

set_option autoImplicit false
set_option maxHeartbeats 480000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseIntegrandBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetBoseDenominator (reciprocalF reciprocalData reciprocal_regular observation_lower)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiplyRaw multiply_fast)
open GaussianRationalHorner (positive_product qmul_canonical)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bounded_product bound_congr reciprocal_canonical)
open GaussianRightHalfPlaneLogarithm (source)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Atan" => GaussianBinetArctangentQuadrature.nameF
local notation "atanData" => GaussianBinetArctangentQuadrature.data
local notation "Bose" => GaussianBinetBoseDenominator.nameF
local notation "boseData" => GaussianBinetBoseDenominator.data

theorem reciprocal_bound (p A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (ap2 reciprocalF p (reciprocalData A B)) B (num 4*A) := by
  let q := exponent (GaussianNameReciprocal.modulus B) p
  let r := q+GaussianNameReciprocal.anchor B
  let x := ap2 Bose r (boseData A B)
  let v := GaussianRationalReciprocal.reciprocal x
  have same : Γ ⊢[PRAAx] ap2 reciprocalF p (reciprocalData A B) ≐ v :=
    (GaussianNameReciprocal.name_at Bose B (boseData A B) p).eqTrans
      (GaussianExponentialReference.recode_fixed v (reciprocal_canonical x))
  have positive : Γ ⊢[PRAAx] le one (num 4*A) := positive_product _ _ (by ipra_le 3) hA
  exact bound_congr same.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalLowerBounds.inverse_bound x (num 4*A) B positive hB (observation_lower r A B hB))

def nameF : PR 2 := multiplyF Atan reciprocalF
def data (X Y D sign A B : PTm n) : PTm n :=
  multiplyData Atan reciprocalF (atanData X Y D sign A B) (reciprocalData A B)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (X Y D sign A B : PTm n) :
    Syn.subst σ (data X Y D sign A B) =
      data (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign)
        (Syn.subst σ A) (Syn.subst σ B) := by simp [data]

theorem regular (X Y D sign A B : PTm n) (h : Γ ⊢[PRAAx] source X D sign)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN nameF (data X Y D sign A B) :=
  multiply_fast _ _ _ _ (GaussianBinetArctangentQuadrature.regular X Y D sign A B h hB)
    (reciprocal_regular A B hA hB)

theorem observation_bound (p X Y D sign A B : PTm n) (h : Γ ⊢[PRAAx] source X D sign)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data X Y D sign A B)) D (num 4*X) := by
  let x := atanData X Y D sign A B
  let y := reciprocalData A B
  let q := exponent (multiplyModulus Atan reciprocalF x y) p
  let u := ap2 Atan q x
  let v := ap2 reciprocalF q y
  have ha := GaussianBinetArctangentQuadratureBound.name_bound q X Y D sign A B h hB
  have hb := reciprocal_bound q A B hA hB
  have bx := positive_product B X hB h.andE₁.andE₁
  have four : Γ ⊢[PRAAx] le one (num 4 : PTm n) := by ipra_le 3
  have dy := positive_product (num 4) A four hA
  have ex := positive_product (num 4) X four h.andE₁.andE₁
  have product := bounded_product u v (A*D) (B*X) B (num 4*A) bx dy ha hb
  have same : Γ ⊢[PRAAx] ap2 nameF p (data X Y D sign A B) ≐ GaussianRationalHorner.qmul u v :=
    (GaussianNameArithmetic.multiply_at Atan reciprocalF x y p).eqTrans
      (GaussianExponentialReference.recode_fixed (multiplyRaw Atan reciprocalF q x y) (qmul_canonical _ _))
  exact bound_congr same.eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ D (num 4*X) (positive_product _ _ bx dy) ex
      (le_congr (.eqRefl _) (by ipra_ring) (le_refl _)) product)

theorem actual_second_Binet_integrand_uniform_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source (var 1) (var 3) (var 4) ⋏ (le one (var 5) ⋏ le one (var 6))) ⟶
      pointCN nameF (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) ⋏
        bounded (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))) (var 3) (num 4*var 1)) :=
  closeUniv 7 (.impI (.andI (regular _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)
    (observation_bound _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBinetBoseIntegrandBound
