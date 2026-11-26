import IPRADerivations.Analysis.SpecialFunctions.DampingPower.GaussianNamedDampingPowerCompact
import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerPowerScalingCompactName
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianCompactScalarMajorant

/-!
# Ordinary compact quadrature under frozen rational parameters

Use one original affine grid for the named parameters and their literal
positive rational observations. The time-independent kernel bound
passes through the actual weighted finite sum, retaining independently
chosen sample clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerCompactFrozen

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedDampingPowerCompact (source evaluatorF fixedData kernel_source_at)
open GaussianNamedDampingPowerFrozen (budget original_frozen_rate)
open GaussianNamedPositiveLogarithm (numerator denominator)
open GaussianNamedInverseRate (rateNumerator rateDenominator rate_at denominator_positive)
open GaussianCompactRiemannName (inside grid grid_inside sampleBody sampleData sample_body_at quadrature)
open GaussianRationalRiemannRefinement (termsDistance)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rationalFixedData (F G : PR 2) (k z B x y C : PTm n) : PTm n :=
  GaussianEulerPowerScalingCompactName.fixedData z B (numerator G k y) (denominator G k y)
    (numerator F k x) (denominator F k x) C

@[simp] theorem subst_rationalFixedData {m : ℕ} (σ : Fin n → PTm m) (F G : PR 2) (k z B x y C : PTm n) :
    Syn.subst σ (rationalFixedData F G k z B x y C) =
      rationalFixedData F G (Syn.subst σ k) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ C) := by
  simp [rationalFixedData,GaussianNamedPositiveLogarithm.numerator,GaussianNamedPositiveLogarithm.denominator]

@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (Rz C R E T : PTm n) :
    Syn.subst σ (budget Rz C R E T) = budget (Syn.subst σ Rz) (Syn.subst σ C) (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by
  simp [budget,GaussianNamedDampingPowerIntegrand.gain,GaussianNamedDampingPowerIntegrand.decayBound,
    GaussianNamedDampingPowerChart.gain,GaussianNamedDampingPowerChart.majorant,GaussianCompactLogarithmBounds.radius,one]

private theorem row (F G : PR 2) (i p q k N z Rz B x y C₀ C R₀ R a W E T : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z Rz B x y C₀ C R₀ R a W E T)
    (hn : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded (inst2 (sampleBody (evaluatorF F G)) i (sampleData p N a W E (fixedData z B x y)))
      (inst2 (sampleBody GaussianEulerPowerScalingCompactName.evaluatorF) i
        (sampleData q N a W E (rationalFixedData F G k z B x y C)))
      (rateNumerator (budget Rz C R E T) (unit k) p q) (rateDenominator (unit k) p q) := by
  let t := grid i N a W E
  have ht : Γ ⊢[PRAAx] inside a W E t := grid_inside i N a W E hs.andE₁.andE₂.andE₁ hs.andE₁.andE₁.andE₂.andE₁ hn (le_of_lt hi)
  have kernel := kernel_source_at F G z Rz B x y C₀ C R₀ R a W E T t hs ht
  have point := rate_at _ _ _ _ _ _ p q (original_frozen_rate F G k z Rz B x y C₀ C R₀ R E T (fstT t) (sndT t) kernel)
  have lhs := (sample_body_at (Γ := Γ) (evaluatorF F G) i p N a W E (fixedData z B x y)).eqTrans
    (GaussianNamedDampingPowerCompact.evaluator_at F G p t z B x y)
  have rhs := (sample_body_at (Γ := Γ) GaussianEulerPowerScalingCompactName.evaluatorF i q N a W E (rationalFixedData F G k z B x y C)).eqTrans
    (GaussianEulerPowerScalingCompactName.evaluator_at q t z B (numerator G k y) (denominator G k y)
      (numerator F k x) (denominator F k x) C)
  exact distance_congr lhs.eqSymm rhs.eqSymm (.eqRefl _) (.eqRefl _) point

theorem quadrature_distance (F G : PR 2) (p q k N z Rz B x y C₀ C R₀ R a W E T : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z Rz B x y C₀ C R₀ R a W E T) (hn : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (quadrature (evaluatorF F G) p N a W E (fixedData z B x y))
      (quadrature GaussianEulerPowerScalingCompactName.evaluatorF q N a W E (rationalFixedData F G k z B x y C))
      (W*rateNumerator (budget Rz C R E T) (unit k) p q) (E*rateDenominator (unit k) p q) := by
  let sh (v : PTm n) := Syn.shift v
  have ss : Γ.map Fm.shift ⊢[PRAAx] source F G (sh z) (sh Rz) (sh B) (sh x) (sh y) (sh C₀) (sh C)
      (sh R₀) (sh R) (sh a) (sh W) (sh E) (sh T) := by
    simpa only [Fm.shift,Syn.shift,GaussianNamedDampingPowerCompact.subst_source,sh] using hs.shift
  have sn : Γ.map Fm.shift ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,sh] using hn.shift
  have cells : Γ ⊢[PRAAx] termsDistance (sampleBody (evaluatorF F G)) (sampleBody GaussianEulerPowerScalingCompactName.evaluatorF) N
      (sampleData p N a W E (fixedData z B x y)) (sampleData q N a W E (rationalFixedData F G k z B x y C))
      (rateNumerator (budget Rz C R E T) (unit k) p q) (rateDenominator (unit k) p q) := by
    refine .allI (.impI ?_)
    simpa only [termsDistance,GaussianCompactRiemannName.subst_sampleData,GaussianNamedDampingPowerCompact.subst_fixedData,
      subst_rationalFixedData,GaussianNamedInverseRate.subst_rateNumerator,GaussianNamedInverseRate.subst_rateDenominator,
      GaussianCoefficientNameBounds.subst_unit,subst_budget,Syn.shift,sh] using
      row F G (var 0) (sh p) (sh q) (sh k) (sh N) (sh z) (sh Rz) (sh B) (sh x) (sh y) (sh C₀) (sh C) (sh R₀)
        (sh R) (sh a) (sh W) (sh E) (sh T) ss.wk sn.wk Prf.hyp0
  exact GaussianCompactScalarMajorant.common_mesh_distance _ _ N _ _ W E _ _ hn hs.andE₁.andE₁.andE₂.andE₁
    (denominator_positive (unit k) p q (unit_positive k)) cells

theorem actual_named_power_damped_compact_frozen_quadratures_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 17
      (source F G (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12)
          (var 13) (var 14) (var 15) (var 16) ⟶ le one (var 3) ⟶
        distanceBounded (quadrature (evaluatorF F G) (var 0) (var 3) (var 13) (var 14) (var 15)
          (fixedData (var 4) (var 6) (var 7) (var 8)))
          (quadrature GaussianEulerPowerScalingCompactName.evaluatorF (var 1) (var 3) (var 13) (var 14) (var 15)
            (rationalFixedData F G (var 2) (var 4) (var 6) (var 7) (var 8) (var 10)))
          (var 14*rateNumerator (budget (var 5) (var 10) (var 12) (var 15) (var 16)) (unit (var 2)) (var 0) (var 1))
          (var 15*rateDenominator (unit (var 2)) (var 0) (var 1))) :=
  closeUniv 17 (.impI (.impI (quadrature_distance F G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerCompactFrozen
