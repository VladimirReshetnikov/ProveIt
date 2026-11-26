import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalNamedTerminalInput
import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalNamedTerminalProperness
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianNamedGammaEulerFirstDerivative

/-!
# The terminal positive Gamma derivative for an arbitrary named increment

The exact terminal arguments are (1+t) and (1+(t+h)).
The increment bound supplies both the pole window for (t+h) and the
original Euler derivative hypothesis. Named addition and original Gamma
properness identify the latter theorem's endpoint ((1+t)+h) with the
desired terminal evaluation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedTerminalDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialSmallPerturbation (smallSamples small_samples_at)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_refl cross_trans)
open GaussianNameRingLaws (add_associative add_commutative)
open GaussianNamedGammaSmallIncrementInput (sumData)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)
open GaussianRationalSyntheticDivision (qone)
open GaussianRealNameExponentialInjectivity (axisSamples)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "offsetSource" => GaussianNamedEulerUnitTime.source
local notation "halfPlane" => GaussianNamedRightHalfPlane.source
local notation "sumF" => GaussianNamedGammaSmallIncrementInput.sumF
local notation "G" => GaussianNamedGamma.nameF
local notation "gd" => GaussianNamedGamma.data
local notation "I" => GaussianNamedEulerLogarithmicImproper.nameF
local notation "id" => GaussianNamedEulerLogarithmicImproper.data
local notation "Q" => GaussianNamedIncrementDifferenceQuotient.nameF
local notation "qd" => GaussianNamedIncrementDifferenceQuotient.data

def derivativeModulus (f : PR 2) (p x : PTm n) : PTm n :=
  GaussianNamedEulerLogarithmicNamedDerivative.incrementModulus (terminalF f) p zero (terminalData x) one

def modulus (f : PR 2) (p x E : PTm n) : PTm n := two*E+derivativeModulus f p x

def source (f K : PR 2) (p x y E a : PTm n) : Fm PTm n :=
  offsetSource f x E ⋏ (axisSamples K y ⋏ (GaussianNameReciprocal.input K a y ⋏ smallSamples K y one (modulus f p x E)))

def quotientF (f K : PR 2) : PR 2 := Q (G (terminalF (sumF f K))) (G (terminalF f)) K
def quotientData (f K : PR 2) (x y a : PTm n) : PTm n :=
  qd (G (terminalF (sumF f K))) (G (terminalF f)) K
    (gd (terminalData (sumData x y)) one) (gd (terminalData x) one) y a
abbrev derivativeF (f : PR 2) : PR 2 := I (terminalF f)
def derivativeData (x : PTm n) : PTm n := id one (terminalData x) one

@[simp] theorem subst_derivativeModulus {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x : PTm n) :
    Syn.subst σ (derivativeModulus f p x) = derivativeModulus f (Syn.subst σ p) (Syn.subst σ x) := by
  simp [derivativeModulus]
@[simp] theorem subst_modulus {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x E : PTm n) :
    Syn.subst σ (modulus f p x E) = modulus f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ E) := by simp [modulus]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (f K : PR 2) (p x y E a : PTm n) :
    (source f K p x y E a).subst σ = source f K (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ E) (Syn.subst σ a) :=
  by simp [source]
@[simp] theorem subst_quotientData {m : ℕ} (σ : Fin n → PTm m) (f K : PR 2) (x y a : PTm n) :
    Syn.subst σ (quotientData f K x y a) = quotientData f K (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ a) :=
  by simp [quotientData]
@[simp] theorem subst_derivativeData {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (derivativeData x) = derivativeData (Syn.subst σ x) := by simp [derivativeData]

private theorem small_weaken (K : PR 2) (y D M : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hDM : Γ ⊢[PRAAx] le D M) (h : Γ ⊢[PRAAx] smallSamples K y one M) :
    Γ ⊢[PRAAx] smallSamples K y one D := by
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] smallSamples K (sh y) one (sh M) := by simpa [Δ,Fm.shift,Syn.shift,sh,one] using h.shift
  have hd : Δ ⊢[PRAAx] le one (sh D) := by simpa [Δ,Fm.shift,Syn.shift,sh,one] using hD.shift
  have hdm : Δ ⊢[PRAAx] le (sh D) (sh M) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hDM.shift
  have out := bounded_radius_mono (ap2 K (var 0) (sh y)) one (sh M) one (sh D) (le_trans hd hdm) hd
    (le_congr (by ipra_ring) (by ipra_ring) hdm) (small_samples_at K (sh y) one (sh M) (var 0) hs)
  simpa only [smallSamples,Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,sh] using out

theorem euler_source (f K : PR 2) (p x y E a : PTm n) (h : Γ ⊢[PRAAx] source f K p x y E a) :
    Γ ⊢[PRAAx] GaussianNamedGammaEulerFirstDerivative.source (terminalF f) K p (terminalData x) y one a := by
  have hd : Γ ⊢[PRAAx] le one (derivativeModulus f p x) := GaussianEulerLogarithmicContinuity.modulus_positive _ _ _ _
  exact .andI (terminal_source f x E h.andE₁) (.andI h.andE₂.andE₂.andE₁
    (small_weaken K y _ _ hd (le_add_left _ _) h.andE₂.andE₂.andE₂))

theorem endpoint_source (f K : PR 2) (p x y E a : PTm n) (h : Γ ⊢[PRAAx] source f K p x y E a) :
    Γ ⊢[PRAAx] offsetSource (sumF f K) (sumData x y) (two*E) := by
  have Epos := (GaussianNamedEulerUnitTime.source_at f zero x E h.andE₁).andE₂.andE₁
  have hD := positive_product _ _ RationalAlgebra.two_positive Epos
  exact shifted_offset_source f K x y E h.andE₁ h.andE₂.andE₂.andE₁.andE₁ h.andE₂.andE₁
    (small_weaken K y _ _ hD (le_add_right _ _) h.andE₂.andE₂.andE₂)

theorem terminal_add_cross (f K : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hk : Γ ⊢[PRAAx] pointCN K y) :
    Γ ⊢[PRAAx] crossEquivalent (sumF (terminalF f) K) (terminalF (sumF f K))
      (sumData (terminalData x) y) (terminalData (sumData x y)) := by
  have hc := constant_regular (Γ := Γ) (qone : PTm n)
  have first := add_associative f constantF K x qone y hf hc hk
  have move := add_cross f f (addF constantF K) (addF K constantF) x x (addData qone y) (addData y qone)
    hf hf (add_fast _ _ _ _ hc hk) (add_fast _ _ _ _ hk hc) (cross_refl _ _ hf) (add_commutative _ _ _ _ hc hk)
  have last := cross_symm _ _ _ _ (add_associative f K constantF x y qone hf hk hc)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ move last)

theorem exact_upper_gamma_cross (f K : PR 2) (p x y E a : PTm n) (h : Γ ⊢[PRAAx] source f K p x y E a) :
    Γ ⊢[PRAAx] crossEquivalent (G (sumF (terminalF f) K)) (G (terminalF (sumF f K)))
      (gd (sumData (terminalData x) y) (two*one)) (gd (terminalData (sumData x y)) one) := by
  have e := euler_source f K p x y E a h
  have left := GaussianNamedEulerLogarithmicNamedDerivative.shifted_name_source (terminalF f) K p zero (terminalData x) y one a e
  have right := terminal_source (sumF f K) (sumData x y) (two*E) (endpoint_source f K p x y E a h)
  exact original_gamma_proper _ _ _ _ _ _ left right (terminal_add_cross f K x y h.andE₁.andE₁ h.andE₂.andE₂.andE₁.andE₁)

theorem quotient_cross (f K : PR 2) (p x y E a : PTm n) (h : Γ ⊢[PRAAx] source f K p x y E a) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedGammaEulerFirstDerivative.quotientF (terminalF f) K) (quotientF f K)
      (GaussianNamedGammaEulerFirstDerivative.quotientData (terminalF f) K (terminalData x) y one a) (quotientData f K x y a) := by
  let F := terminalF f
  let L := sumF F K
  let R := terminalF (sumF f K)
  let Y := terminalData x
  let Z := gd Y one
  let V := gd (sumData Y y) (two*one)
  let W := gd (terminalData (sumData x y)) one
  have hf := euler_source f K p x y E a h
  have hl := GaussianNamedEulerLogarithmicNamedDerivative.shifted_name_source F K p zero Y y one a hf
  have hr := terminal_source (sumF f K) (sumData x y) (two*E) (endpoint_source f K p x y E a h)
  have base := GaussianNamedGamma.name_regular F Y one hf.andE₁
  exact GaussianNamedIncrementDifferenceQuotientProperness.proper (G L) (G R) (G F) (G F) K V W Z Z y a
    (GaussianNamedGamma.name_regular L (sumData Y y) (two*one) hl)
    (GaussianNamedGamma.name_regular R (terminalData (sumData x y)) one hr) base base h.andE₂.andE₂.andE₁
    (exact_upper_gamma_cross f K p x y E a h) (cross_refl (G F) Z base)

theorem derivative_regular (f : PR 2) (x E : PTm n) (h : Γ ⊢[PRAAx] offsetSource f x E) :
    Γ ⊢[PRAAx] pointCN (derivativeF f) (derivativeData x) :=
  GaussianNamedEulerLogarithmicImproper.name_regular (terminalF f) one (terminalData x) one (terminal_source f x E h)

theorem quotient_regular (f K : PR 2) (p x y E a : PTm n) (h : Γ ⊢[PRAAx] source f K p x y E a) :
    Γ ⊢[PRAAx] pointCN (quotientF f K) (quotientData f K x y a) := by
  have he := quotient_cross f K p x y E a h
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ he) he

theorem original_rate (f K : PR 2) (p x y E a : PTm n) (h : Γ ⊢[PRAAx] source f K p x y E a) :
    Γ ⊢[PRAAx] independentRate (quotientF f K) (derivativeF f) (quotientData f K x y a) (derivativeData x) one (unit p) := by
  have hc := quotient_cross f K p x y E a h
  have e := euler_source f K p x y E a h
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ (unit_positive p)
    (GaussianNamedGammaEulerFirstDerivative.original_first_derivative_rate (terminalF f) K p (terminalData x) y one a e)
    (cross_symm _ _ _ _ hc) (cross_refl _ _ (derivative_regular f x E h.andE₁))

theorem actual_original_negative_interval_named_terminal_derivative_closed (f K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source f K (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        offsetSource (sumF f K) (sumData (var 1) (var 2)) (two*var 3) ⋏
        independentRate (quotientF f K) (derivativeF f) (quotientData f K (var 1) (var 2) (var 4))
          (derivativeData (var 1)) one (unit (var 0))) :=
  closeUniv 5 (.impI (.andI (endpoint_source f K _ _ _ _ _ Prf.hyp0) (original_rate f K _ _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedTerminalDerivative
