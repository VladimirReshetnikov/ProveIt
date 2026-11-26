import IPRADerivations.Analysis.Gamma.Digamma.ElementaryBounds.GaussianGammaDigammaElementaryBounds
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotientProperness

/-!
# Elementary digamma bounds with the original logarithm name

Transport both exact bounds from the harmonic mesh logarithm to the
original positive rational logarithm used for the Gamma identities.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaElementaryOriginalLog

open_ipra
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaDigammaHarmonicCells (halfReciprocal)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderTransport (transport)
open GaussianPositiveRationalLogarithm (fraction logF)
open GaussianStirlingGammaLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data
local notation "HF" => GaussianGammaDigammaElementaryBounds.nameF
local notation "hL" => GaussianGammaDigammaElementaryBounds.lowerData
local notation "hU" => GaussianGammaDigammaElementaryBounds.upperData

def nameF : PR 2 := GaussianNamedDifference.nameF logF constantF

def data (a b c : PTm n) : PTm n :=
  GaussianNamedDifference.data (GaussianPositiveRationalLogarithm.data a b) c

def lowerData (a b : PTm n) : PTm n := data a b (fraction b a)
def upperData (a b : PTm n) : PTm n := data a b (halfReciprocal a b)

ipra_subst data
ipra_subst lowerData
ipra_subst upperData

theorem endpoint_cross (a b c : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent nameF HF (data a b c)
      (GaussianNamedDifference.data (GaussianHarmonicLogarithmName.data a b) c) :=
  GaussianNamedDifferenceQuotientProperness.difference_proper _ _ constantF constantF _ _ c c
    (GaussianPositiveRationalLogarithm.name_regular a b hs) (GaussianHarmonicLogarithmName.name_regular a b hs)
    (constant_regular c) (constant_regular c) (GaussianHarmonicLogarithmName.cross_original a b hs)
    (cross_refl constantF c (constant_regular c))

theorem elementary_bounds (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] (realOrder nameF DF (lowerData a b) (dd a b) ⋏ realOrder DF nameF (dd a b) (upperData a b)) := by
  have h := GaussianGammaDigammaElementaryBounds.elementary_bounds a b hs
  have id := cross_refl DF _ (GaussianGammaDigammaNative.name_regular a b hs)
  have eL : Γ ⊢[PRAAx] crossEquivalent nameF HF (lowerData a b) (hL a b) := endpoint_cross a b _ hs
  have eU : Γ ⊢[PRAAx] crossEquivalent nameF HF (upperData a b) (hU a b) := endpoint_cross a b _ hs
  exact .andI
    (transport nameF HF DF DF _ _ _ _ eL id h.andE₁)
    (transport DF DF HF nameF _ _ _ _ id (cross_symm _ _ _ _ eU) h.andE₂)

theorem actual_original_log_digamma_elementary_bounds_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source (var 0) (var 1) ⟶
        (realOrder nameF DF (lowerData (var 0) (var 1)) (dd (var 0) (var 1)) ⋏
         realOrder DF nameF (dd (var 0) (var 1)) (upperData (var 0) (var 1)))) :=
  closeUniv 2 (.impI (elementary_bounds _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaElementaryOriginalLog
