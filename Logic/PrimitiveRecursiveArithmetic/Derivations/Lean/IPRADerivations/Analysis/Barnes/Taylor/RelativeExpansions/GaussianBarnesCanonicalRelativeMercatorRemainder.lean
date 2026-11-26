import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalRelativeStep
import IPRADerivations.Analysis.Logarithm.Local.GaussianLocalLogarithmTaylorRemainder
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius
import IPRADerivations.AnalyticNumberTheory.LocalFactor

/-!
# Arbitrary-order ordinary Mercator increments in the Barnes relative chart

The exact relative chart expresses the difference of the two original
local logarithms as an ordinary logarithm at the relative step. Its
remainder has the actual geometric ratio and a simpler bound whose
powers of the step and factor denominators separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalRelativeMercatorRemainder

open_ipra
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalRelativeStep (source local_admission relative_bound logarithm_increment)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianLocalLogarithmName (pointF data)
open GaussianLocalLogarithmTaylorRemainder (half_disk_radius_strict)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "L" => pointF
local notation "RNum" => GaussianBarnesCanonicalRelativeStep.numerator
local notation "RDen" => GaussianBarnesCanonicalRelativeStep.denominator
local notation "RRadius" => GaussianBarnesCanonicalRelativeStep.radius
local notation "Num" => GaussianFiniteLogarithmTaylorRemainder.numerator
local notation "Den" => GaussianFiniteLogarithmTaylorRemainder.denominator

abbrev incrementF : PR 2 := GaussianNamedDifference.nameF L L

def incrementData (z h R B k : PTm n) : PTm n :=
  GaussianNamedDifference.data (data (add z h) (R*B) (B*k)) (data z (R*B) (B*k))

def polynomial (m z h B k : PTm n) : PTm n :=
  GaussianLocalLogarithmTaylorRemainder.polynomial m (RNum z h B k) (RDen z B k)

def powerDenominator (m B k : PTm n) : PTm n := succ m*pw B (succ m)*pw k (succ m)

@[simp] theorem subst_incrementData {l : ℕ} (σ : Fin n → PTm l) (z h R B k : PTm n) :
    Syn.subst σ (incrementData z h R B k) = incrementData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ k) := by simp [incrementData]

@[simp] theorem subst_polynomial {l : ℕ} (σ : Fin n → PTm l) (m z h B k : PTm n) :
    Syn.subst σ (polynomial m z h B k) = polynomial (Syn.subst σ m) (Syn.subst σ z) (Syn.subst σ h)
      (Syn.subst σ B) (Syn.subst σ k) := by simp [polynomial]

@[simp] theorem subst_powerDenominator {l : ℕ} (σ : Fin n → PTm l) (m B k : PTm n) :
    Syn.subst σ (powerDenominator m B k) = powerDenominator (Syn.subst σ m) (Syn.subst σ B) (Syn.subst σ k) :=
  by simp [powerDenominator]

private theorem half_disk (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] le (two*(two*H)) (B*k) :=
  le_trans (le_of_eq_add (d := num 12*H) (by ipra_ring)) hs.andE₂.andE₂.andE₂

theorem rate (m z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] independentRate incrementF constantF (incrementData z h R B k) (polynomial m z h B k)
      (Num (two*H) m) (Den (two*H) (B*k) m) := by
  let D := Den (two*H) (B*k) m
  let x := data (RNum z h B k) (RRadius H B k) (RDen z B k)
  let w := polynomial m z h B k
  have hd := positive_product B k hs.andE₁.andE₁ hs.andE₁.andE₂.andE₁
  have strict := half_disk_radius_strict (two*H) (B*k) hd (half_disk z h R B k H hs)
  have raw := GaussianLocalLogarithmTaylorRemainder.rate_at_radius m (RNum z h B k) (RRadius H B k) (RDen z B k) (two*H) (B*k)
    (local_admission z h R B k H hs) hd strict (relative_bound z h R B k H hs)
  exact GaussianNamedRateTransport.transport L constantF incrementF constantF x w (incrementData z h R B k) w
    (Num (two*H) m) D (GaussianFiniteLogarithmTaylorRemainder.denominator_positive _ _ _ hd strict) raw
    (logarithm_increment z h R B k H hs) (cross_refl _ _ (constant_regular _))

private theorem half_disk_power_budget (A D m : PTm n) (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] le (two*A) D) :
    Γ ⊢[PRAAx] le (Num A m*(succ m*pw D (succ m))) ((two*Num A m)*Den A D m) := by
  let G := monus D A
  let E := pw D m
  let N := Num A m
  have strict := half_disk_radius_strict A D hD h
  have e := eq_add_of_le (le_of_lt strict)
  have small : Γ ⊢[PRAAx] le A G :=
    le_of_add_le_add_right (le_congr (by ipra_ring) (e.eqTrans (add_comm _ _)) h)
  have gap : Γ ⊢[PRAAx] le D (two*G) :=
    le_congr e.eqSymm (by ipra_ring) (add_le_add_right G small)
  have grow := mul_le_mul_right (N*(succ m*E)) gap
  have left : Γ ⊢[PRAAx] Num A m*(succ m*pw D (succ m)) ≐ D*(N*(succ m*E)) :=
    (congrMul (.eqRefl _) (congrMul (.eqRefl _) (pw_succ D m))).eqTrans (by ipra_ring)
  exact le_congr left.eqSymm (by unfold GaussianFiniteLogarithmTaylorRemainder.denominator G E N; ipra_ring) grow

theorem power_rate (m z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] independentRate incrementF constantF (incrementData z h R B k) (polynomial m z h B k)
      (two*Num (two*H) m) (powerDenominator m B k) := by
  let A := two*H
  let D := B*k
  have hB := hs.andE₁.andE₁
  have hk := hs.andE₁.andE₂.andE₁
  have hd := positive_product B k hB hk
  have hh := half_disk z h R B k H hs
  have strict := half_disk_radius_strict A D hd hh
  have hOld := GaussianFiniteLogarithmTaylorRemainder.denominator_positive A D m hd strict
  have hNew : Γ ⊢[PRAAx] le one (powerDenominator m B k) :=
    positive_product _ _ (positive_product _ _ (zero_lt_succ m) (GaussianFactorBudget.power_positive _ _ hB))
      (GaussianFactorBudget.power_positive _ _ hk)
  have e : Γ ⊢[PRAAx] succ m*pw D (succ m) ≐ powerDenominator m B k :=
    (congrMul (.eqRefl _) (pw_mul_base B k (succ m))).eqTrans (by unfold powerDenominator; ipra_ring)
  have fit := le_congr (congrMul (.eqRefl _) e) (.eqRefl _) (half_disk_power_budget A D m hd hh)
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hOld hNew fit (rate m z h R B k H hs)

theorem actual_Barnes_relative_ordinary_Mercator_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let m := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let k := var 5
     let H := var 6
     source z h R B k H ⟶
       independentRate incrementF constantF (incrementData z h R B k) (polynomial m z h B k)
         (two*Num (two*H) m) (powerDenominator m B k)) :=
  closeUniv 7 (.impI (power_rate _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalRelativeMercatorRemainder
