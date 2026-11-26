import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaTwoShiftNamedBinding
import IPRADerivations.Analysis.Exponential.GaussianExponentialRadiusIndependence

/-!
# Uniform freeze of the original named normalized Gamma ratio

The common exponential radius depends only on the original input
names and their source data. Independent comparison of the actual
normalized quotient with each frozen rational quotient uses the same
radius at every precision.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftNamedExponential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaDigammaTwoShiftNamedFreeze (source clock chartDenominator baseNumerator leftNumerator rightNumerator)
open GaussianGammaDigammaTwoShiftNamedBinding (quotientF quotientData quotientLogF quotientLogData budget)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRightHalfPlane (threshold)
open GaussianRadiusExponentialLipschitzRate (factor)
open GaussianRadiusExponentialName (data)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "U" => GaussianNameBounds.U
local notation "RF" => GaussianGammaDigammaTwoShiftBinding.quotientLogF
local notation "RD" => GaussianGammaDigammaTwoShiftBinding.quotientLogData
local notation "QF" => GaussianGammaDigammaTwoShiftBinding.quotientF
local notation "QD" => GaussianGammaDigammaTwoShiftBinding.quotientData

def commonRadius (f g h : PR 2) (x y z M : PTm n) : PTm n :=
  U (quotientLogF f g h) (quotientLogData f g h x y z M)+budget f g h x y z M+two

def quotientBudget (f g h : PR 2) (x y z M : PTm n) : PTm n :=
  factor (commonRadius f g h x y z M)*budget f g h x y z M

@[simp] theorem subst_commonRadius {m : ℕ} (σ : Fin n → PTm m) (f g h : PR 2) (x y z M : PTm n) :
    Syn.subst σ (commonRadius f g h x y z M) = commonRadius f g h (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ M) := by
  simp [commonRadius,two]

@[simp] theorem subst_quotientBudget {m : ℕ} (σ : Fin n → PTm m) (f g h : PR 2) (x y z M : PTm n) :
    Syn.subst σ (quotientBudget f g h x y z M) = quotientBudget f g h (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ M) := by
  simp [quotientBudget]

def frozenQuotientRate (f g h : PR 2) (s x y z M : PTm n) : Fm PTm n :=
  let k := clock g h s y z M
  let a := baseNumerator f g h k x y z
  let b := chartDenominator f g h k x y z
  let c := leftNumerator f g h k x y z
  let d := rightNumerator f g h k x y z
  independentRate (quotientF f g h) QF (quotientData f g h x y z M) (QD a b c d) (quotientBudget f g h x y z M) (unit s)

theorem frozen_quotient_rate (f g h : PR 2) (s x y z M : PTm n) (hs : Γ ⊢[PRAAx] source f g h x y z M) :
    Γ ⊢[PRAAx] frozenQuotientRate f g h s x y z M := by
  let k := clock g h s y z M
  let a := baseNumerator f g h k x y z
  let b := chartDenominator f g h k x y z
  let c := leftNumerator f g h k x y z
  let d := rightNumerator f g h k x y z
  let A := budget f g h x y z M
  let F := quotientLogF f g h
  let X := quotientLogData f g h x y z M
  let Y := RD a b c d
  let D := unit s
  let R := commonRadius f g h x y z M
  have hd := unit_positive (Γ := Γ) s
  have chart := GaussianGammaDigammaTwoShiftNamedFreeze.charts f g h k x y z M hs (le_add_left _ _)
  have hX := GaussianGammaDigammaTwoShiftNamedBinding.quotient_log_regular f g h x y z M hs
  have hY := GaussianGammaDigammaTwoShiftBinding.quotient_log_regular a b c d chart.andE₁ chart.andE₂.andE₁ chart.andE₂.andE₂
  have hX0 := GaussianGammaFiniteApproximantName.exponential_input F X hX
  have hY0 := GaussianGammaFiniteApproximantName.exponential_input RF Y hY
  have hX' : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input F R X :=
    GaussianExponentialRadiusIndependence.input_widen F (U F X) R X hX0
      (le_trans (le_add_right _ _) (le_add_right _ _))
  have rate : Γ ⊢[PRAAx] independentRate F RF X Y A D :=
    GaussianGammaDigammaTwoShiftNamedBinding.frozen_log_rate f g h s x y z M hs
  have hY' : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input RF R Y :=
    .andI hY (GaussianNamedUniformRateClosure.sample_bound_of_rate RF F Y X (U F X) A D hd
      (GaussianNameBounds.all_samples_bounded _ _ hX)
      (GaussianNamedRateComposition.symmetric _ _ _ _ _ _ hd rate))
  have exponent := GaussianRadiusExponentialLipschitzRate.independent_rate F RF R X Y A D
    (.andI hd (.andI hX' (.andI hY' rate)))
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ (factor R*A) D hd exponent
    (GaussianExponentialRadiusIndependence.same_input_cross F (U F X) R X hX0 hX')
    (GaussianExponentialRadiusIndependence.same_input_cross RF (U RF Y) R Y hY0 hY')

theorem actual_named_two_shift_quotient_frozen_closed (f g h : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source f g h (var 1) (var 2) (var 3) (var 4) ⟶ frozenQuotientRate f g h (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (frozen_quotient_rate f g h _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftNamedExponential
