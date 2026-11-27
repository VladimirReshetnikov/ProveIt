import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.FirstDerivative.Cofinal.GaussianBarnesCanonicalPositiveFirstLogarithm
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.SecondDerivative.GaussianBarnesCanonicalPositiveSecondLogarithm

/-! The positive logarithmic derivatives agree across certified radii by comparing
the actual series samplers with a shared finite prefix. -/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveLogarithmDerivativeRadius

open_ipra
open Common
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "disk" => GaussianBarnesCanonicalLogCofinal.source
local notation "L₁" => GaussianBarnesCanonicalPositiveFirstLogarithm.nameF
local notation "d₁" => GaussianBarnesCanonicalPositiveFirstLogarithm.data
local notation "S₁" => GaussianBarnesCanonicalPositiveFirstLogarithm.seriesF
local notation "s₁" => GaussianBarnesCanonicalPositiveFirstLogarithm.seriesData
local notation "len₁" => GaussianBarnesCanonicalDerivativeCofinal.length
local notation "v₁" => GaussianBarnesCanonicalDerivativeTail.value
local notation "L₂" => GaussianBarnesCanonicalPositiveSecondLogarithm.nameF
local notation "d₂" => GaussianBarnesCanonicalPositiveSecondLogarithm.data
local notation "S₂" => GaussianBarnesCanonicalPositiveSecondLogarithm.seriesF
local notation "s₂" => GaussianBarnesCanonicalPositiveSecondLogarithm.seriesData
local notation "len₂" => GaussianBarnesCanonicalSecondDerivativeCofinal.length
local notation "v₂" => GaussianBarnesCanonicalSecondDerivativeTail.value

private theorem paired_prefix_errors (p x y u v : PTm n) (h₀ : Γ ⊢[PRAAx] u ≐ v)
    (h₁ : Γ ⊢[PRAAx] distanceBounded x u (num 4) (unit p))
    (h₂ : Γ ⊢[PRAAx] distanceBounded y v (num 4) (unit p)) :
    Γ ⊢[PRAAx] distanceBounded x y (num 8) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have e := distance_congr (.eqRefl _) h₀ (.eqRefl _) (.eqRefl _) h₁
  have f := distance_symmetric _ _ _ _ hp h₂
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp e f)

private theorem first_series_at (p A B R S : PTm n)
    (hR : Γ ⊢[PRAAx] disk (center A B) R B) (hS : Γ ⊢[PRAAx] disk (center A B) S B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 S₁ p (s₁ A B R)) (ap2 S₁ p (s₁ A B S)) (num 8) (unit p) := by
  let r := len₁ p R
  let s := len₁ p S
  let K := initial S+(r+s)
  let M := initial R+(r+s)
  have h₁ : Γ ⊢[PRAAx] le r K := le_trans (le_add_right r s) (le_add_left (r+s) (initial S))
  have h₂ : Γ ⊢[PRAAx] le s M := le_trans (le_add_left s r) (le_add_left (r+s) (initial R))
  have e : Γ ⊢[PRAAx] GaussianBarnesCanonicalPositiveFirstLogarithm.prefixValue A B R K ≐
      GaussianBarnesCanonicalPositiveFirstLogarithm.prefixValue A B S M := by
    ipra_congr (v₁ (var 0) (var 1) (var 2) (var 3) : PTm 4)
      with [.eqRefl _,.eqRefl _, .eqRefl _, (by dsimp only [K,M]; ipra_ring)]
      using [GaussianBarnesCanonicalPositiveFirstLogarithm.prefixValue]
  exact paired_prefix_errors p _ _ _ _ e
    (GaussianBarnesCanonicalPositiveFirstLogarithm.series_prefix_error p A B R K hR h₁)
    (GaussianBarnesCanonicalPositiveFirstLogarithm.series_prefix_error p A B S M hS h₂)

private theorem second_series_at (p A B R S : PTm n)
    (hR : Γ ⊢[PRAAx] disk (center A B) R B) (hS : Γ ⊢[PRAAx] disk (center A B) S B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 S₂ p (s₂ A B R)) (ap2 S₂ p (s₂ A B S)) (num 8) (unit p) := by
  let r := len₂ p R
  let s := len₂ p S
  let K := initial S+(r+s)
  let M := initial R+(r+s)
  have h₁ : Γ ⊢[PRAAx] le r K := le_trans (le_add_right r s) (le_add_left (r+s) (initial S))
  have h₂ : Γ ⊢[PRAAx] le s M := le_trans (le_add_left s r) (le_add_left (r+s) (initial R))
  have e : Γ ⊢[PRAAx] GaussianBarnesCanonicalPositiveSecondLogarithm.prefixValue A B R K ≐
      GaussianBarnesCanonicalPositiveSecondLogarithm.prefixValue A B S M := by
    ipra_congr (v₂ (var 0) (var 1) (var 2) (var 3) : PTm 4)
      with [.eqRefl _,.eqRefl _, .eqRefl _, (by dsimp only [K,M]; ipra_ring)]
      using [GaussianBarnesCanonicalPositiveSecondLogarithm.prefixValue]
  exact paired_prefix_errors p _ _ _ _ e
    (GaussianBarnesCanonicalPositiveSecondLogarithm.series_prefix_error p A B R K hR h₁)
    (GaussianBarnesCanonicalPositiveSecondLogarithm.series_prefix_error p A B S M hS h₂)

theorem first (A B R S : PTm n) (hR : Γ ⊢[PRAAx] disk (center A B) R B)
    (hS : Γ ⊢[PRAAx] disk (center A B) S B) :
    Γ ⊢[PRAAx] crossEquivalent L₁ L₁ (d₁ A B R) (d₁ A B S) := by
  let G := GaussianBarnesCanonicalPrefactorInverse.exponentF
  let x := GaussianBarnesCanonicalPositiveFirstLogarithm.prefactorData A B
  have hx := GaussianBarnesCanonicalPositiveFirstLogarithm.prefactor_regular (Γ := Γ) A B
  have hr := GaussianBarnesCanonicalPositiveFirstLogarithm.series_regular A B R hR
  have hs := GaussianBarnesCanonicalPositiveFirstLogarithm.series_regular A B S hS
  have e : Γ ⊢[PRAAx] crossEquivalent S₁ S₁ (s₁ A B R) (s₁ A B S) := by
    refine GaussianNameRingLaws.equivalent_of_envelope S₁ S₁ _ _ (num 8) hr hs (.allI ?_)
    let sh (a : PTm n) := Syn.shift a
    have ar : Γ.map Fm.shift ⊢[PRAAx] disk (center (sh A) (sh B)) (sh R) (sh B) := by
      simpa [Syn.shift,Fm.shift,sh] using hR.shift
    have as : Γ.map Fm.shift ⊢[PRAAx] disk (center (sh A) (sh B)) (sh S) (sh B) := by
      simpa [Syn.shift,Fm.shift,sh] using hS.shift
    simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianBarnesCanonicalPositiveFirstLogarithm.subst_seriesData,
      PTm.subst_num,Syn.shift,sh] using first_series_at (var 0) (sh A) (sh B) (sh R) (sh S) ar as
  exact add_cross G G S₁ S₁ x x (s₁ A B R) (s₁ A B S) hx hx hr hs (cross_refl _ _ hx) e

theorem second (A B R S : PTm n) (hR : Γ ⊢[PRAAx] disk (center A B) R B)
    (hS : Γ ⊢[PRAAx] disk (center A B) S B) :
    Γ ⊢[PRAAx] crossEquivalent L₂ L₂ (d₂ A B R) (d₂ A B S) := by
  let G := GaussianBarnesCanonicalPositiveSecondLogarithm.coefficientF
  let x : PTm n := GaussianBarnesCanonicalPositiveSecondLogarithm.coefficientData
  have hx := GaussianBarnesCanonicalPositiveSecondLogarithm.coefficient_regular (Γ := Γ)
  have hr := GaussianBarnesCanonicalPositiveSecondLogarithm.series_regular A B R hR
  have hs := GaussianBarnesCanonicalPositiveSecondLogarithm.series_regular A B S hS
  have e : Γ ⊢[PRAAx] crossEquivalent S₂ S₂ (s₂ A B R) (s₂ A B S) := by
    refine GaussianNameRingLaws.equivalent_of_envelope S₂ S₂ _ _ (num 8) hr hs (.allI ?_)
    let sh (a : PTm n) := Syn.shift a
    have ar : Γ.map Fm.shift ⊢[PRAAx] disk (center (sh A) (sh B)) (sh R) (sh B) := by
      simpa [Syn.shift,Fm.shift,sh] using hR.shift
    have as : Γ.map Fm.shift ⊢[PRAAx] disk (center (sh A) (sh B)) (sh S) (sh B) := by
      simpa [Syn.shift,Fm.shift,sh] using hS.shift
    simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianBarnesCanonicalPositiveSecondLogarithm.subst_seriesData,
      PTm.subst_num,Syn.shift,sh] using second_series_at (var 0) (sh A) (sh B) (sh R) (sh S) ar as
  exact add_cross G G S₂ S₂ x x (s₂ A B R) (s₂ A B S) hx hx hr hs (cross_refl _ _ hx) e

theorem actual_Barnes_logarithmic_derivative_radii_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let A := var 0
       let B := var 1
       let R := var 2
       let S := var 3
       (disk (center A B) R B ⋏ disk (center A B) S B) ⟶
         (crossEquivalent L₁ L₁ (d₁ A B R) (d₁ A B S) ⋏ crossEquivalent L₂ L₂ (d₂ A B R) (d₂ A B S))) :=
  closeUniv 4 (.impI (.andI (first _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)
    (second _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveLogarithmDerivativeRadius
