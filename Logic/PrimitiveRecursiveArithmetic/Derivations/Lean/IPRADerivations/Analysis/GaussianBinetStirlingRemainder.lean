import IPRADerivations.Analysis.GaussianLogGammaEulerPositiveAxis
import IPRADerivations.Analysis.GaussianLogGammaEulerRepresentation
import IPRADerivations.Analysis.GaussianStirlingGlobalBounds

/-!
# The actual complex Stirling remainder and its positive-axis restriction

Use the canonical cofinal Euler log-Gamma, the canonical right-half-plane
logarithm, and the existing named Stirling constant. On the positive
axis, this normalized expression recovers the original real Stirling
remainder, so its checked real estimates can be reused.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000

namespace LeanProofs.IPRA.Analysis.GaussianBinetStirlingRemainder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaInputProperness (code_data_cross)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerCofinal (canonicalData canonical_regular)
open GaussianNameArithmetic (addF addData add_fast add_equivalent multiplyF multiplyData multiply_fast multiply_equivalent)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_to_diagonal)
open GaussianNamedDifferenceQuotientProperness (difference_proper)
open GaussianPositiveRationalLogarithm (fraction logF)
open GaussianRationalHorner (canonical_unique ofGaussian_canonical ofGaussian_represents represents_congr)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianRightHalfPlaneLogarithm (source)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianRightHalfPlaneLogarithm.nameF
local notation "ld" => GaussianRightHalfPlaneLogarithm.data
local notation "G" => GaussianLogGammaEulerCofinal.nameF
local notation "C" => GaussianStirlingConstant.nameF
local notation "cd" => GaussianStirlingConstant.nameData
local notation "F" => GaussianNamedDifference.nameF
local notation "fd" => GaussianNamedDifference.data

def offset (A B D neg : PTm n) : PTm n := qsub (argument A B D neg) (fraction one two)

def weightedF : PR 2 := multiplyF constantF L
def weightedData (A B D neg : PTm n) : PTm n := multiplyData constantF L (offset A B D neg) (ld A B D neg)

def coreF : PR 2 := addF (F G weightedF) constantF
def coreData (A B D neg : PTm n) : PTm n :=
  addData (fd (canonicalData A B D neg) (weightedData A B D neg)) (argument A B D neg)

def nameF : PR 2 := F coreF C
def data (A B D neg x : PTm n) : PTm n := fd (coreData A B D neg) (cd x)

@[simp] theorem subst_offset {m : ℕ} (σ : Fin n → PTm m) (A B D neg : PTm n) :
    Syn.subst σ (offset A B D neg) = offset (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) := by
  simp [offset, one, two, GaussianLogGammaEulerRepresentation.subst_argument]

@[simp] theorem subst_weightedData {m : ℕ} (σ : Fin n → PTm m) (A B D neg : PTm n) :
    Syn.subst σ (weightedData A B D neg) =
      weightedData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) := by simp [weightedData]

@[simp] theorem subst_coreData {m : ℕ} (σ : Fin n → PTm m) (A B D neg : PTm n) :
    Syn.subst σ (coreData A B D neg) =
      coreData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) := by
  simp [coreData, canonicalData, GaussianLogGammaEulerRepresentation.subst_argument]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (A B D neg x : PTm n) :
    Syn.subst σ (data A B D neg x) =
      data (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) (Syn.subst σ x) := by simp [data]

theorem weighted_regular (A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] pointCN weightedF (weightedData A B D neg) :=
  multiply_fast constantF L _ _ (constant_regular _) (GaussianRightHalfPlaneLogarithm.regular A B D neg h)

theorem core_regular (A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] pointCN coreF (coreData A B D neg) :=
  add_fast _ _ _ _ (GaussianNamedDifference.name_regular _ _ _ _ (canonical_regular A B D neg h)
    (weighted_regular A B D neg h)) (constant_regular _)

theorem regular (A B D neg x : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] pointCN nameF (data A B D neg x) :=
  GaussianNamedDifference.name_regular _ _ _ _ (core_regular A B D neg h) (GaussianStirlingConstant.name_regular x)

private theorem axis_argument (A D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) : Γ ⊢[PRAAx]
    argument A zero D neg ≐ fraction A D := by
  let a := GaussianLogGammaEulerResidualDomain.native A zero neg
  let b := GaussianStirlingGammaLogarithm.arg A
  have hD := h.andE₂
  change Γ ⊢[PRAAx] GaussianRationalHorner.ofGaussian a D ≐ GaussianRationalHorner.ofGaussian b D
  exact canonical_unique _ _ b D (ofGaussian_canonical _ _ hD) (ofGaussian_canonical _ _ hD) hD
    (represents_congr (.eqRefl _) (GaussianLogGammaEulerPositiveAxis.native_axis_equal A neg h.andE₁.andE₂)
      (.eqRefl _) (ofGaussian_represents a D hD)) (ofGaussian_represents b D hD)

theorem core_axis_equivalent (A D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) : Γ ⊢[PRAAx]
    crossEquivalent coreF GaussianStirlingNames.nameF (coreData A zero D neg) (GaussianStirlingNames.nameData A D) := by
  let H := GaussianStirlingNames.logXF
  let J := GaussianStirlingNames.logGammaF
  let W := GaussianStirlingNames.productF
  let a := argument A zero D neg
  let a' := GaussianStirlingNames.point A D
  let b := offset A zero D neg
  let b' := GaussianStirlingNames.offset A D
  let x := ld A zero D neg
  let x' := GaussianStirlingNames.logXData A D
  let g := canonicalData A zero D neg
  let g' := GaussianStirlingNames.logGammaData A D
  let w := weightedData A zero D neg
  let w' := GaussianStirlingNames.productData A D
  have hs : Γ ⊢[PRAAx] GaussianStirlingNames.source A D := .andI h.andE₁.andE₁ h.andE₂
  have ea := axis_argument A D neg h
  have ca := code_data_cross constantF a a' (constant_regular a) (constant_regular a') ea
  have cb := code_data_cross constantF b b' (constant_regular b) (constant_regular b') (qsub_congr ea (.eqRefl _))
  have lx : Γ ⊢[PRAAx] crossEquivalent L H x x' :=
    cross_trans L logF H x (GaussianPositiveRationalLogarithm.data A D) x'
      (GaussianRightHalfPlaneLogarithm.positive_axis A D neg h)
      (GaussianHarmonicLogarithmName.cross_original A D hs)
  have pw : Γ ⊢[PRAAx] crossEquivalent weightedF W w w' :=
    multiply_equivalent constantF constantF L H b b' x x'
      (constant_regular b) (constant_regular b') (GaussianRightHalfPlaneLogarithm.regular A zero D neg h)
      (GaussianStirlingNames.log_x_regular A D hs) (cross_to_diagonal _ _ _ _ cb) (cross_to_diagonal _ _ _ _ lx)
  have gg := canonical_regular A zero D neg h
  have gj := GaussianStirlingNames.log_gamma_regular A D hs
  have rw := weighted_regular A zero D neg h
  have rw' := GaussianStirlingNames.product_regular A D hs
  have diff := difference_proper G J weightedF W g g' w w' gg gj rw rw'
    (GaussianLogGammaEulerPositiveAxis.equivalent A D neg h) pw
  exact add_equivalent (F G weightedF) (F J W) constantF constantF (fd g w) (fd g' w') a a'
    (GaussianNamedDifference.name_regular G weightedF g w gg rw)
    (GaussianNamedDifference.name_regular J W g' w' gj rw') (constant_regular a) (constant_regular a')
    (cross_to_diagonal _ _ _ _ diff) (cross_to_diagonal _ _ _ _ ca)

theorem axis_equivalent (A D neg x : PTm n) (h : Γ ⊢[PRAAx] source A D neg) : Γ ⊢[PRAAx]
    crossEquivalent nameF GaussianStirlingGlobalBounds.remainderF (data A zero D neg x)
      (GaussianStirlingGlobalBounds.remainderData A D x) :=
  difference_proper coreF GaussianStirlingNames.nameF C C _ _ (cd x) (cd x)
    (core_regular A zero D neg h) (GaussianStirlingNames.name_regular A D (.andI h.andE₁.andE₁ h.andE₂))
    (GaussianStirlingConstant.name_regular x) (GaussianStirlingConstant.name_regular x)
    (core_axis_equivalent A D neg h) (cross_refl C _ (GaussianStirlingConstant.name_regular x))

theorem actual_complex_Stirling_remainder_positive_axis_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ crossEquivalent nameF GaussianStirlingGlobalBounds.remainderF
      (data (var 0) zero (var 1) (var 2) (var 3)) (GaussianStirlingGlobalBounds.remainderData (var 0) (var 1) (var 3))) :=
  closeUniv 4 (.impI (axis_equivalent _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetStirlingRemainder
