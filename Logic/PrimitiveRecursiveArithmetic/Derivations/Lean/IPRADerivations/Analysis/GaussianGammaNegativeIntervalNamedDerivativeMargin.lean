import IPRADerivations.Analysis.GaussianGammaNegativeIntervalNamedDerivative
import IPRADerivations.Analysis.GaussianNamedEulerUnitTimeMargin

/-!
# Independence of the certified margin for the named Gamma derivative

The two derivative names agree with one rational derivative at a
common late observation of the original offset. Applying this
comparison at each precision proves equality of the names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedDerivativeMargin

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialRadiusIndependence (independent_radii_proper)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input)
open GaussianGammaNegativeIntervalNamedDerivative (nameF data name_regular freezeClock productCost frozen_product_rate)
open GaussianGammaNegativeIntervalNamedGamma (actualF actualData actual_regular signedF signedData signed_regular)
open GaussianGammaNegativeIntervalNamedInput (sampleNumerator sampleDenominator)
open GaussianGammaNegativeIntervalProductSign (signUnit)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianNameRingLaws (equivalent_of_envelope three)
open GaussianNamedEulerUnitTime (source)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open GaussianNamedRateComposition (same_denominator_at symmetric)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private def comparisonCost (f : PR 2) (x E D N : PTm n) : PTm n :=
  productCost f x E N+productCost f x D N+two

private theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x E N : PTm n) :
    Syn.subst σ (data f x E N) = data f (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ N) := by
  simp [data, actualData, signedData, GaussianGammaFiniteApproximantName.exponentialInputData]

private theorem subst_comparisonCost {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x E D N : PTm n) :
    Syn.subst σ (comparisonCost f x E D N) =
      comparisonCost f (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ D) (Syn.subst σ N) := by
  simp [comparisonCost, productCost, actualData, signedData, GaussianGammaFiniteApproximantName.exponentialInputData, three, two]

private theorem comparison_at (f : PR 2) (p x E D N : PTm n)
    (hE : Γ ⊢[PRAAx] source f x E) (hD : Γ ⊢[PRAAx] source f x D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) p (data f x E N)) (ap2 (nameF f) p (data f x D N))
      (comparisonCost f x E D N) (unit p) := by
  let k := freezeClock f p x E N+freezeClock f p x D N
  let F := nameF f
  let G := GaussianGammaNegativeIntervalDerivativeTarget.nameF
  let u := data f x E N
  let v := data f x D N
  let z := GaussianGammaNegativeIntervalDerivativeTarget.data (sampleNumerator f k x) (sampleDenominator f k x) N
  let A := productCost f x E N
  let B := productCost f x D N
  have hp := unit_positive (Γ := Γ) p
  have l := frozen_product_rate f p k x E N hE (le_add_right _ _)
  have r := frozen_product_rate f p k x D N hD (le_add_left _ _)
  have joined := same_denominator_at F G F u z v A (unit p) B p p hp l (symmetric F G v z B (unit p) hp r)
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ hp) hp
    (le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator comparisonCost A B; ipra_ring)) joined

theorem same_input_cross (f : PR 2) (x E D N : PTm n) (hE : Γ ⊢[PRAAx] source f x E) (hD : Γ ⊢[PRAAx] source f x D) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF f) (data f x E N) (data f x D N) := by
  refine equivalent_of_envelope _ _ _ _ (comparisonCost f x E D N) (name_regular f x E N hE) (name_regular f x D N hD) (.allI ?_)
  let Δ := Γ.map Fm.shift
  let sh (v : PTm n) := Syn.shift v
  have hs : Δ ⊢[PRAAx] source f (sh x) (sh E) := by simpa [Δ,sh,Syn.shift,Fm.shift] using hE.shift
  have ht : Δ ⊢[PRAAx] source f (sh x) (sh D) := by simpa [Δ,sh,Syn.shift,Fm.shift] using hD.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal, Syn.shift, sh, subst_data, subst_comparisonCost] using
    comparison_at f (var 0) (sh x) (sh E) (sh D) (sh N) hs ht

theorem actual_named_negative_Gamma_derivative_margin_independence_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((source f (var 0) (var 1) ⋏ source f (var 0) (var 2)) ⟶
        crossEquivalent (nameF f) (nameF f) (data f (var 0) (var 1) (var 3)) (data f (var 0) (var 2) (var 3))) :=
  closeUniv 4 (.impI (same_input_cross f _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem same_margin_cross (f g : PR 2) (x y E N : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E) (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data f x E N) (data g y E N) := by
  let F := GaussianGammaNegativeIntervalNamedLog.nameF f
  let G := GaussianGammaNegativeIntervalNamedLog.nameF g
  let u := GaussianGammaNegativeIntervalNamedLog.data x E N
  let v := GaussianGammaNegativeIntervalNamedLog.data y E N
  let S := signUnit (succ N)
  let df := GaussianGammaNegativeIntervalNamedDigamma.nameF f
  let dg := GaussianGammaNegativeIntervalNamedDigamma.nameF g
  let dx := GaussianGammaNegativeIntervalNamedDigamma.data x E N
  let dy := GaussianGammaNegativeIntervalNamedDigamma.data y E N
  have log := GaussianGammaNegativeIntervalNamedLog.proper f g x y E N hf hg he
  have left := GaussianGammaNegativeIntervalNamedLog.name_regular f x E N hf
  have right := GaussianGammaNegativeIntervalNamedLog.name_regular g y E N hg
  have magnitude : Γ ⊢[PRAAx] crossEquivalent (signedF f) (signedF g) (signedData f x E N) (signedData g y E N) :=
    independent_radii_proper F G (U F u) (U G v) u v (exponential_input F u left) (exponential_input G v right) log
  have gamma : Γ ⊢[PRAAx] crossEquivalent (actualF f) (actualF g) (actualData f x E N) (actualData g y E N) :=
    multiply_cross constantF constantF (signedF f) (signedF g) S S (signedData f x E N) (signedData g y E N)
      (constant_regular S) (constant_regular S) (signed_regular f x E N hf) (signed_regular g y E N hg)
      (cross_refl _ _ (constant_regular S)) magnitude
  exact multiply_cross (actualF f) (actualF g) df dg (actualData f x E N) (actualData g y E N) dx dy
    (actual_regular f x E N hf) (actual_regular g y E N hg)
    (GaussianGammaNegativeIntervalNamedDigamma.name_regular f x E N hf)
    (GaussianGammaNegativeIntervalNamedDigamma.name_regular g y E N hg) gamma
    (GaussianGammaNegativeIntervalNamedDigamma.proper f g x y E N hf hg he)

theorem proper (f g : PR 2) (x y E D N : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y D) (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data f x E N) (data g y D N) := by
  let S := E+D
  have left := GaussianNamedEulerUnitTimeMargin.widen f x E S hf (le_add_right E D)
  have right := GaussianNamedEulerUnitTimeMargin.widen g y D S hg (le_add_left D E)
  exact cross_trans _ _ _ _ _ _ (same_input_cross f x E S N hf left)
    (cross_trans _ _ _ _ _ _ (same_margin_cross f g x y S N left right he) (same_input_cross g y S D N right hg))

theorem actual_named_negative_Gamma_derivative_properness_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((source f (var 0) (var 2) ⋏ (source g (var 1) (var 3) ⋏ crossEquivalent f g (var 0) (var 1))) ⟶
        crossEquivalent (nameF f) (nameF g) (data f (var 0) (var 2) (var 4)) (data g (var 1) (var 3) (var 4))) :=
  closeUniv 5 (.impI (proper f g _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedDerivativeMargin
