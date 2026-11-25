import IPRADerivations.Analysis.GaussianBinetFirstFormulaPinning

/-!
# Truncation of the actual Binet Laplace unit difference

Both observations of the shifted difference retain the original
improper names. The two original compact prefixes use the same physical
cutoff, with the error from each original strip kept explicitly.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceDifferencePrefix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetFirstFormulaDecay (laplaceData laplace_regular)
open GaussianBinetFirstFormulaPinning (laplaceStepData)
open GaussianBinetLaplaceOrderedPrefixes (prefixData prefix_regular)
open GaussianLogGammaEulerResidualRadius (radius source_of_right_half_plane)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedDifference (nameF name_regular data)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)
open GaussianRightHalfPlaneLogarithm (source)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "J" => GaussianBinetLaplaceImproperName.nameF
local notation "C" => GaussianBinetLaplaceStrip.nameF GaussianBinetLaplaceStrip.Kernel.cofinal

def prefixStepData (A B D sign L : PTm n) : PTm n :=
  data (prefixData A B D sign (radius A B) L)
    (prefixData (A+D) B D sign (radius (A+D) B) L)

@[simp] theorem subst_prefixStepData {m : ℕ} (σ : Fin n → PTm m) (A B D sign L : PTm n) :
    Syn.subst σ (prefixStepData A B D sign L) =
      prefixStepData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ L) := by
  simp [prefixStepData]

theorem shifted_source (A D sign : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] source (A+D) D sign :=
  .andI (.andI (le_trans h.andE₁.andE₁ (le_add_right A D)) h.andE₁.andE₂) h.andE₂

theorem prefix_step_regular (A B D sign L : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] pointCN (nameF C C) (prefixStepData A B D sign L) :=
  name_regular _ _ _ _
    (prefix_regular A B D sign _ L (source_of_right_half_plane A B D sign h))
    (prefix_regular (A+D) B D sign _ L (source_of_right_half_plane (A+D) B D sign (shifted_source A D sign h)))

abbrev tailDen (A L : PTm n) : PTm n := num 12*A*unit L

theorem tail_den_positive (A L : PTm n) (h : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] le one (tailDen A L) :=
  positive_product _ _ (positive_product _ _ (by ipra_le 11) h) (unit_positive L)

theorem prefix_step_rate (A B D sign L : PTm n)
    (h : Γ ⊢[PRAAx] source A D sign) (hL : Γ ⊢[PRAAx] le one L) :
    Γ ⊢[PRAAx] independentRate (nameF J J) (nameF C C)
      (laplaceStepData A B D sign) (prefixStepData A B D sign L)
      (D*tailDen (A+D) L+D*tailDen A L) (tailDen A L*tailDen (A+D) L) := by
  let x := laplaceData A B D sign
  let y := laplaceData (A+D) B D sign
  let u := prefixData A B D sign (radius A B) L
  let v := prefixData (A+D) B D sign (radius (A+D) B) L
  have hs := shifted_source A D sign h
  have hx := source_of_right_half_plane A B D sign h
  have hy := source_of_right_half_plane (A+D) B D sign hs
  exact GaussianNamedDifferenceRate.original_rate J J C C x y u v D (tailDen A L) D (tailDen (A+D) L)
    (.andI (.andI (tail_den_positive A L h.andE₁.andE₁) (tail_den_positive (A+D) L hs.andE₁.andE₁))
      (.andI (.andI (laplace_regular A B D sign h) (laplace_regular (A+D) B D sign hs))
        (.andI (.andI (prefix_regular A B D sign _ L hx) (prefix_regular (A+D) B D sign _ L hy))
          (.andI (GaussianBinetLaplaceImproperName.prefix_rate A B D sign _ L hx hL)
            (GaussianBinetLaplaceImproperName.prefix_rate (A+D) B D sign _ L hy hL)))))

theorem actual_Binet_unit_difference_prefix_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 2) (var 3) ⟶ le one (var 4) ⟶ independentRate (nameF J J) (nameF C C)
      (laplaceStepData (var 0) (var 1) (var 2) (var 3))
      (prefixStepData (var 0) (var 1) (var 2) (var 3) (var 4))
      (var 2*tailDen (var 0+var 2) (var 4)+var 2*tailDen (var 0) (var 4))
      (tailDen (var 0) (var 4)*tailDen (var 0+var 2) (var 4))) :=
  closeUniv 5 (.impI (.impI (prefix_step_rate _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceDifferencePrefix
