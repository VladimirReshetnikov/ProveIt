import IPRADerivations.Analysis.Stirling.Binet.Laplace.Rectangles.GaussianBinetLaplaceRectangleJoin

/-!
# Binet's first formula on the original encoded right half-plane

The checked rectangle comparison supplies the unit difference of
the actual improper Laplace sampler. The original Stirling
remainder has the same unit difference and both sides tend to
zero under right translation.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBinetFirstFormula

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetFirstFormulaDecay (laplaceData laplace_regular)
open GaussianBinetFirstFormulaPinning (laplaceStepData stepLaw first_formula_of_unit_difference)
open GaussianBinetLaplaceRectangleJoin (comparisonCost original_observation)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianRightHalfPlaneLogarithm (source)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "J" => GaussianBinetLaplaceImproperName.nameF
local notation "U" => GaussianBinetStirlingUnitDifference.nameF
local notation "ud" => GaussianBinetStirlingUnitDifference.data
local notation "W" => GaussianBinetWeightedResolvent.nameF
local notation "wd" => GaussianBinetWeightedResolvent.data
local notation "S" => GaussianBinetStirlingRemainder.nameF
local notation "sd" => GaussianBinetStirlingRemainder.data
local notation "Diff" => GaussianNamedDifference.nameF

theorem unit_difference (A B D sign : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] crossEquivalent (Diff J J) W (laplaceStepData A B D sign) (wd A B D sign) := by
  have hs := GaussianBinetLaplaceDifferencePrefix.shifted_source A D sign h
  have regular := GaussianNamedDifference.name_regular J J (laplaceData A B D sign) (laplaceData (A+D) B D sign)
    (laplace_regular A B D sign h) (laplace_regular (A+D) B D sign hs)
  have actual : Γ ⊢[PRAAx] crossEquivalent (Diff J J) U (laplaceStepData A B D sign) (ud A B D sign) := by
    refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (comparisonCost A B D sign) regular
      (GaussianBinetStirlingUnitDifference.regular A B D sign h) (.allI ?_)
    let s (t : PTm n) := Syn.shift t
    have hh : Γ.map Fm.shift ⊢[PRAAx] source (s A) (s D) (s sign) := by
      simpa [s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using h.shift
    simpa only [GaussianValueNormalizerExtensionality.rawDiagonal, Syn.shift, s,
      GaussianBinetFirstFormulaPinning.subst_laplaceStepData, GaussianBinetStirlingUnitDifference.subst_data,
      GaussianBinetLaplaceRectangleJoin.subst_comparisonCost] using
      original_observation (var 0) (s A) (s B) (s D) (s sign) hh
  exact cross_trans _ U _ _ _ _ actual
    (cross_symm _ _ _ _ (GaussianBinetWeightedResolvent.equivalent A B D sign h))

theorem translated_unit_difference (A B D sign : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] stepLaw A B D sign := by
  refine .allI ?_
  let s (t : PTm n) := Syn.shift t
  have hh : Γ.map Fm.shift ⊢[PRAAx] source (s A) (s D) (s sign) := by
    simpa [s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using h.shift
  exact unit_difference (s A+var 0*s D) (s B) (s D) (s sign)
    (GaussianLogGammaEulerHead.shifted_source (var 0) (s A) (s D) (s sign) hh)

theorem equivalent (A B D sign x : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] crossEquivalent S J (sd A B D sign x) (laplaceData A B D sign) :=
  first_formula_of_unit_difference A B D sign x h (translated_unit_difference A B D sign h)

theorem actual_first_Binet_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 2) (var 3) ⟶
      crossEquivalent S J (sd (var 0) (var 1) (var 2) (var 3) (var 4))
        (laplaceData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (equivalent _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetFirstFormula
