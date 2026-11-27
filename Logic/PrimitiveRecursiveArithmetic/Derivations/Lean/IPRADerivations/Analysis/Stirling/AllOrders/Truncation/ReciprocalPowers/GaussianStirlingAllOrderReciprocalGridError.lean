import IPRADerivations.Analysis.Stirling.AllOrders.Truncation.ReciprocalPowers.GaussianStirlingAllOrderReciprocalWeightError

/-!
# Uniform reciprocal-power curvature errors on the original panel

The denominator on both adjacent rows is at least the mesh count.
The centered denominator is at most (U+B) times this count. These
internal bounds give a single M^(-2) precision estimate over the panel.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderReciprocalGridError

open_ipra
open GaussianStirlingAllOrderKernel (rowWeight offset)
open GaussianStirlingAllOrderReciprocalWeightError
  (power weight coefficient scaledSecond derivative commonDen errorNumerator common_positive curvature_error)
open GaussianStirlingAllOrderReciprocalTaylorBound (width size integerBound)
open GaussianStirlingAllOrderDiscreteParts (secondDifference)
open GaussianEuclideanDistanceName (fraction)
open GaussianRationalHorner (positive_product)
open RationalValueBounds (radius radius_mono)
open RationalArithmetic (multiply)
open RationalNonnegativePowers (fraction_congr fraction_multiply)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def gridDen (U B M r : PTm n) : PTm n := U*M+B*r

def gridCoefficient (e : ℕ) (U B : PTm n) : PTm n :=
  power e B*num (size e)*power 4 B*power (width e) (U+B)

theorem row_bounds (U B M r : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hr : Γ ⊢[PRAAx] le one r) (hM : Γ ⊢[PRAAx] le r M) :
    Γ ⊢[PRAAx] le B (gridDen U B M r) ⋏
      (le M (monus (gridDen U B M r) B) ⋏
      (le M (gridDen U B M r) ⋏ le (gridDen U B M r) ((U+B)*M))) := by
  let D := gridDen U B M r
  have hD : Γ ⊢[PRAAx] le (M+B) D := by
    unfold D gridDen
    ipra_le 𝔞 M*sl hU+𝔞 B*sl hr
  have hB : Γ ⊢[PRAAx] le B D := le_trans (le_add_left B M) hD
  have hm : Γ ⊢[PRAAx] le M D := le_trans (le_add_right M B) hD
  have hf : Γ ⊢[PRAAx] le M (monus D B) := by
    have e₂ := natEq (eq_add_of_le hB)
    ipra_le sl hD using linear_combination -e₂
  have hu : Γ ⊢[PRAAx] le D ((U+B)*M) := by
    unfold D gridDen
    ipra_le 𝔞 B*sl hM
  exact .andI hB (.andI hf (.andI hm hu))

private theorem add_power (e f : ℕ) (x : PTm n) : Γ ⊢[PRAAx] power (e+f) x ≐ power e x*power f x := by
  apply deriveNat
  simp only [power,AnalyticNumberTheory.RobinThreePos.pw_lit,IPRA.Q.mk_mul,map_mul,pow_add]

private theorem two_power (x : PTm n) : Γ ⊢[PRAAx] power 2 x ≐ x*x := by
  apply deriveNat
  simp only [power,AnalyticNumberTheory.RobinThreePos.pw_lit,IPRA.Q.mk_mul,map_mul,pow_two]

private theorem power_product (e : ℕ) (x y : PTm n) : Γ ⊢[PRAAx] power e (x*y) ≐ power e x*power e y :=
  AnalyticNumberTheory.LocalFactor.pw_mul_base _ _ _

private theorem denominator_lower (e : ℕ) (x B M : PTm n)
    (hx : Γ ⊢[PRAAx] le M x) (hxlo : Γ ⊢[PRAAx] le M (monus x B)) :
    Γ ⊢[PRAAx] le (power (3*e+2) M) (commonDen e x B) := by
  have hu := pw_le_pw (num (e+2)) hx
  have hv := pw_le_pw (num e) (le_trans hx (le_add_right x B))
  have hw := pw_le_pw (num e) hxlo
  have proof := le_mul_mono hu (le_mul_mono hv hw)
  have eq : Γ ⊢[PRAAx] power (3*e+2) M ≐ power (e+2) M*(power e M*power e M) := by
    have ed : 3*e+2=(e+2)+(e+e) := by omega
    rw [ed]
    exact (add_power (e+2) (e+e) M).eqTrans (congrMul (.eqRefl _) (add_power e e M))
  exact le_congr eq.eqSymm (.eqRefl _) proof

private theorem numerator_upper (e : ℕ) (he : 2≤e) (x U B M : PTm n) (hx : Γ ⊢[PRAAx] le x ((U+B)*M)) :
    Γ ⊢[PRAAx] le (errorNumerator e x B M) (gridCoefficient e U B*power (3*e) M) := by
  have ho := pw_le_pw (num (width e)) hx
  have cells : Γ ⊢[PRAAx] le (errorNumerator e x B M)
      ((power e (B*M)*(M*M))*(num (size e)*power 4 B*power (width e) ((U+B)*M))) :=
    le_mul_mono (le_refl _) (le_mul_mono (le_refl _) ho)
  have eq : Γ ⊢[PRAAx] (power e (B*M)*(M*M))*(num (size e)*power 4 B*power (width e) ((U+B)*M)) ≐
      gridCoefficient e U B*power (3*e) M := by
    apply deriveNat
    have ee := natEq (power_product (Γ := Γ) e B M)
    have ew := natEq (power_product (Γ := Γ) (width e) (U+B) M)
    have en : Γ ⊢[PRAAx] power (3*e) M ≐ (power e M*power 2 M)*power (width e) M := by
      have ed : 3*e=(e+2)+width e := by unfold width; omega
      rw [ed]
      exact (add_power (e+2) (width e) M).eqTrans (congrMul (add_power e 2 M) (.eqRefl _))
    have em := natEq en
    have e₂ := natEq (two_power (Γ := Γ) M)
    unfold gridCoefficient
    ipra_simps
    rw [ee,ew,em,e₂]
    ring
  exact le_congr (.eqRefl _) eq cells

theorem grid_error (e : ℕ) (he : 2≤e) (U B M r : PTm n)
    (hU : Γ ⊢[PRAAx] le one U) (hM : Γ ⊢[PRAAx] le one M)
    (hr : Γ ⊢[PRAAx] le one r) (hrm : Γ ⊢[PRAAx] le r M) :
    Γ ⊢[PRAAx] radius (scaledSecond e (gridDen U B M r) B M) (derivative e (gridDen U B M r) B M)
      (gridCoefficient e U B) (M*M) := by
  let D := gridDen U B M r
  have rows := row_bounds U B M r hU hr hrm
  have hX := le_trans hM rows.andE₂.andE₁
  have pos := common_positive e D B rows.andE₁ hX
  have num := numerator_upper e he D U B M rows.andE₂.andE₂.andE₂
  have den := denominator_lower e D B M rows.andE₂.andE₂.andE₁ rows.andE₂.andE₁
  have eq : Γ ⊢[PRAAx] (gridCoefficient e U B*power (3*e) M)*(M*M) ≐ gridCoefficient e U B*power (3*e+2) M := by
    have e₁ := natEq (add_power (Γ := Γ) (3*e) 2 M)
    have e₂ := natEq (two_power (Γ := Γ) M)
    apply deriveNat
    ipra_simps
    rw [e₁,e₂]
    ring
  have error := curvature_error e he D B M rows.andE₁ hX
  exact radius_mono _ _ _ _ _ _ pos error (le_trans (le_congr (.eqRefl _) eq (mul_le_mul_right (M*M) num))
    (le_mul_mono (le_refl _) den))

private theorem step_exponent (e : ℕ) (he : 0<e) : Γ ⊢[PRAAx] succ (num (e-1) : PTm n) ≐ num e := by
  apply deriveNat
  ipra_simps
  have eq : e-1+1=e := by omega
  simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun j : ℕ => (j : Groth (IPRA.Q Γ))) eq

theorem original_weight (e : ℕ) (he : 0<e) (A B M k r : PTm n) :
    Γ ⊢[PRAAx] rowWeight (num (e-1)) A B M k r ≐ weight e B M (gridDen (A+B*k) B M r) :=
  fraction_congr (congrAp2 powF (step_exponent e he) (.eqRefl _))
    (congrAp2 powF (step_exponent e he) (.eqRefl _))

theorem derivative_weight (e : ℕ) (A B M k r : PTm n) (h : Γ ⊢[PRAAx] le one (gridDen (A+B*k) B M r)) :
    Γ ⊢[PRAAx] derivative e (gridDen (A+B*k) B M r) B M ≐
      multiply (fraction (coefficient e) one) (rowWeight (num (e+1)) A B M k r) := by
  let D := gridDen (A+B*k) B M r
  have hd : Γ ⊢[PRAAx] le one (power (e+2) D) := GaussianFactorBudget.power_positive _ _ h
  have ew := original_weight (Γ := Γ) (e+2) (by omega) A B M k r
  have ef := fraction_multiply (Γ := Γ) (coefficient e) one (power (e+2) (B*M)) (power (e+2) D) (le_refl one) hd
  exact (fraction_congr (.eqRefl _) (one_mul _).eqSymm).eqTrans
    (ef.eqSymm.eqTrans (RationalAlgebra.multiply_congr (.eqRefl _) ew.eqSymm))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderReciprocalGridError
