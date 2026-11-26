import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianNonmonicTravelCoefficientBound
import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianNonmonicDisplacementRadius
import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianTravelResidualClearing
import IPRADerivations.Analysis.RationalArithmetic.Powers.RationalShrinkingStepPowerBound

/-!
# The actual nonmonic shrinking-step bound

An arbitrary original positive-degree coefficient has a positive rational
lower bound. Actual translation, maximum selection, balanced radius and
residual clearing derive the power comparison; positive-exponent order
reflection then proves the source travel estimate. The existing fixed
displacement program stays within that actual starting radius, including
the zero-residual branch. No nonconstancy certificate, selected coefficient,
power comparison or travel/output law is an incoming source premise.

All degrees, lists, points, coefficient indices, positive denominators,
decay ratios and iteration counters are internal numerical inputs. The
source point disk U-1 is relaxed to U; the decay ratio may equal zero or
one. The general coefficient-name Cauchy iteration remains separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNonmonicStepBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.Analysis.GaussianNonmonicTravelCoefficientBound (weight lowerBound selectedIndex)
open LeanProofs.IPRA.Analysis.GaussianNonmonicDisplacementRadius
  (startingNumerator startingDenominator startingRadius deltaF)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (N A M E R j : PTm n) : PTm n := A*(E*weight N*M)*pw R j
def denominator (B L F S j : PTm n) : PTm n := B*(F*L)*pw S j
def bound (N A B L M E F R S j : PTm n) : PTm n :=
  fraction (numerator N A M E R j) (denominator B L F S j)
def coefficientInput (C N z A B k L M : PTm n) : Fm PTm n :=
  GaussianTranslationCoefficientBound.input C N z A B ⋏
    (le one k ⋏ (le k N ⋏ (le one L ⋏ (le one M ⋏ lowerBound C N k L M))))
def rateInput (N L M E F q s R S : PTm n) : Fm PTm n :=
  le one F ⋏ (le one s ⋏ (le one S ⋏ (le R S ⋏
    (rationalLE (fraction q s) (RationalNonnegativePowers.power R S N) ⋏ le (F*L) (E*weight N*M)))))
def input (C N z A B k L M E F q s R S j : PTm n) : Fm PTm n :=
  coefficientInput C N z A B k L M ⋏
    (rateInput N L M E F q s R S ⋏ bounded (evaluate C z) (E*pw q j) (F*pw s j))

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (N A M E R j : PTm n) :
    Syn.subst σ (numerator N A M E R j) = numerator (Syn.subst σ N) (Syn.subst σ A)
      (Syn.subst σ M) (Syn.subst σ E) (Syn.subst σ R) (Syn.subst σ j) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (B L F S j : PTm n) :
    Syn.subst σ (denominator B L F S j) = denominator (Syn.subst σ B) (Syn.subst σ L)
      (Syn.subst σ F) (Syn.subst σ S) (Syn.subst σ j) := by simp [denominator]
@[simp] theorem subst_bound {m : ℕ} (σ : Fin n → PTm m) (N A B L M E F R S j : PTm n) :
    Syn.subst σ (bound N A B L M E F R S j) = bound (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ B)
      (Syn.subst σ L) (Syn.subst σ M) (Syn.subst σ E) (Syn.subst σ F)
      (Syn.subst σ R) (Syn.subst σ S) (Syn.subst σ j) := by simp [bound]
@[simp] theorem subst_coefficientInput {m : ℕ} (σ : Fin n → PTm m) (C N z A B k L M : PTm n) :
    (coefficientInput C N z A B k L M).subst σ = coefficientInput (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ L) (Syn.subst σ M) := by simp [coefficientInput]
@[simp] theorem subst_rateInput {m : ℕ} (σ : Fin n → PTm m) (N L M E F q s R S : PTm n) :
    (rateInput N L M E F q s R S).subst σ = rateInput (Syn.subst σ N) (Syn.subst σ L) (Syn.subst σ M)
      (Syn.subst σ E) (Syn.subst σ F) (Syn.subst σ q) (Syn.subst σ s) (Syn.subst σ R) (Syn.subst σ S) := by simp [rateInput]
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (C N z A B k L M E F q s R S j : PTm n) :
    (input C N z A B k L M E F q s R S j).subst σ = input (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ L) (Syn.subst σ M)
      (Syn.subst σ E) (Syn.subst σ F) (Syn.subst σ q) (Syn.subst σ s) (Syn.subst σ R) (Syn.subst σ S) (Syn.subst σ j) := by simp [input]

theorem denominator_positive (B L F S j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hL : Γ ⊢[PRAAx] le one L) (hF : Γ ⊢[PRAAx] le one F) (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx]
    le one (denominator B L F S j) := GaussianRationalHorner.positive_product _ _
      (GaussianRationalHorner.positive_product _ _ hB (GaussianRationalHorner.positive_product _ _ hF hL))
      (RationalNonnegativePowers.denominator_positive S j hS)

/-- All local power and coefficient premises are discharged by actual
producers before the source radius comparison is exported. -/
theorem starting_radius_bound (C N z A B k L M E F q s R S j : PTm n)
    (h : Γ ⊢[PRAAx] input C N z A B k L M E F q s R S j) : Γ ⊢[PRAAx]
    rationalLE (startingRadius C N z) (bound N A B L M E F R S j) := by
  have hc := Prf.andE₁ h
  have shape := Prf.andE₁ hc
  have c1 := Prf.andE₂ hc
  have hk := Prf.andE₁ c1
  have c2 := Prf.andE₂ c1
  have hkN := Prf.andE₁ c2
  have c3 := Prf.andE₂ c2
  have hL := Prf.andE₁ c3
  have c4 := Prf.andE₂ c3
  have hM := Prf.andE₁ c4
  have lower := Prf.andE₂ c4
  have hr := Prf.andE₁ (Prf.andE₂ h)
  have hF := Prf.andE₁ hr
  have r1 := Prf.andE₂ hr
  have hs := Prf.andE₁ r1
  have r2 := Prf.andE₂ r1
  have hS := Prf.andE₁ r2
  have r3 := Prf.andE₂ r2
  have hRS := Prf.andE₁ r3
  have r4 := Prf.andE₂ r3
  have hQ := Prf.andE₁ r4
  have hC := Prf.andE₂ r4
  have hResidual := Prf.andE₂ (Prf.andE₂ h)
  have coefficient := GaussianNonmonicTravelCoefficientBound.coefficient_radius_bound C N z A B k L M shape hk hkN hL hM lower
  have combined := GaussianTravelResidualClearing.combined_point_budget (evaluate C z)
    (startingNumerator C N z) (startingDenominator C N z) A B L M (weight N) E F q s (selectedIndex C N z A B) j
    hF hs coefficient hResidual
  have indices := GaussianNonmonicTravelCoefficientBound.selected_bounds C N z A B (Prf.andE₁ (Prf.andE₂ shape))
  exact RationalShrinkingStepPowerBound.source_bound (startingNumerator C N z) (startingDenominator C N z)
    A B L M E F q s R S j N (selectedIndex C N z A B) (weight N)
    (GaussianNonmonicDisplacementRadius.starting_denominator_positive C N z)
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ shape))) hL hF hs hS hC hRS
    (Prf.andE₁ indices) (Prf.andE₂ indices) hQ combined

theorem input_denominator_positive (C N z A B k L M E F q s R S j : PTm n)
    (h : Γ ⊢[PRAAx] input C N z A B k L M E F q s R S j) : Γ ⊢[PRAAx]
    le one (denominator B L F S j) := by
  have hc := Prf.andE₁ h
  have shape := Prf.andE₁ hc
  have hL := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hc)))
  have hr := Prf.andE₁ (Prf.andE₂ h)
  have hS := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ hr))
  exact denominator_positive B L F S j (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ shape))) hL (Prf.andE₁ hr) hS

theorem delta_bound (C N z A B k L M E F q s R S j : PTm n)
    (h : Γ ⊢[PRAAx] input C N z A B k L M E F q s R S j) : Γ ⊢[PRAAx]
    bounded (GaussianNonmonicRD.delta N C z) (numerator N A M E R j) (denominator B L F S j) := by
  have hb := GaussianNonmonicDisplacementRadius.starting_denominator_positive (Γ := Γ) C N z
  have hd := input_denominator_positive C N z A B k L M E F q s R S j h
  have order := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (fraction_represents (startingNumerator C N z) (startingDenominator C N z) hb)
    (fraction_represents (numerator N A M E R j) (denominator B L F S j) hd)
    (starting_radius_bound C N z A B k L M E F q s R S j h)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hb hd
    (le_congr (mul_comm _ _) (.eqRefl _) order) (GaussianNonmonicDisplacementRadius.delta_radius C N z)

theorem delta_program_bound (C N z A B k L M E F q s R S j : PTm n)
    (h : Γ ⊢[PRAAx] input C N z A B k L M E F q s R S j) : Γ ⊢[PRAAx]
    bounded (ap3 deltaF N C z) (numerator N A M E R j) (denominator B L F S j) :=
  GaussianRationalReciprocal.bound_congr (GaussianNonmonicDisplacementRadius.delta_program_at N C z).eqSymm
    (.eqRefl _) (.eqRefl _) (delta_bound C N z A B k L M E F q s R S j h)

theorem source_step_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 15
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
      (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) (var 14) ⟶
      rationalLE (startingRadius (var 0) (var 1) (var 2))
        (bound (var 1) (var 3) (var 4) (var 6) (var 7) (var 8) (var 9) (var 12) (var 13) (var 14))) :=
  closeUniv 15 (.impI (starting_radius_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem source_displacement_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 15
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
      (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) (var 14) ⟶
      bounded (GaussianNonmonicRD.delta (var 1) (var 0) (var 2))
        (numerator (var 1) (var 3) (var 7) (var 8) (var 12) (var 14))
        (denominator (var 4) (var 6) (var 9) (var 13) (var 14))) :=
  closeUniv 15 (.impI (delta_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem source_displacement_program_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 15
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
      (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) (var 14) ⟶
      bounded (ap3 deltaF (var 1) (var 0) (var 2))
        (numerator (var 1) (var 3) (var 7) (var 8) (var 12) (var 14))
        (denominator (var 4) (var 6) (var 9) (var 13) (var 14))) :=
  closeUniv 15 (.impI (delta_program_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNonmonicStepBound
