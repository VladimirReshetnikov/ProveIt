import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalTerminalRemainder
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalBaseProductShift
import IPRADerivations.Analysis.Exponential.IntegerPowers.GaussianBoundedIntegerExponential
import IPRADerivations.Analysis.Logarithm.Local.GaussianLocalLogarithmMultiplicativeIncrement

/-!
# Exact power of the original terminal logarithm

Exponentiating the actual scaled local logarithm gives the rational
power of `1+w/K`. Multiplying by the exact power of `K` recovers the
terminal factor of the original cleared Barnes shift.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTerminalPower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalTerminalRemainder (source local_source scaledF scaledData scaled_regular)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianRationalHorner (ofGaussian ofGaussian_represents ofGaussian_canonical canonical_unique represents_rescale
  represents_congr positive_product qmul)
open GaussianRationalNaturalScale (natScale_represents natScale_as_product natScale_canonical naturalPoint)
open GaussianRationalPowerAlgebra (power_product)
open GaussianRationalReciprocal (power powerF qone qone_bounded bound_congr bounded_sum)
open GaussianRootAlgebra (equal_of_values re_add im_add re_scale im_scale)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "L" => GaussianLocalLogarithmName.pointF
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ld" => GaussianLocalLogarithmName.data
local notation "ed" => GaussianRadiusExponentialName.data

def normalizedPower (w B K : PTm n) : PTm n := power (GaussianBarnesCanonicalFactor.base w B K) K
def data (w R B K : PTm n) : PTm n := exponentialInputData scaledF (scaledData w R B K)

theorem exponentiated_scaled (w R B K : PTm n) (h : Γ ⊢[PRAAx] source w R B K) : Γ ⊢[PRAAx]
    crossEquivalent (E scaledF) constantF (data w R B K) (normalizedPower w B K) := by
  let a := ofGaussian w (B*K)
  let c := GaussianBarnesCanonicalFactor.base w B K
  let x := ld w (R*B) (B*K)
  let d := scaledData w R B K
  let A := GaussianNamedNaturalScale.radius K one
  have hs := local_source w R B K h
  have ix := GaussianExponentialRadiusIndependence.radius_one_input L x
    (GaussianLocalLogarithmName.original_exponential_input _ _ _ hs)
  have e : Γ ⊢[PRAAx] crossEquivalent (E L) constantF (ed one x) c :=
    GaussianLocalLogarithmMultiplicativeIncrement.exponential_base_cross w (R*B) (B*K) hs
  have hc : Γ ⊢[PRAAx] GaussianRationalMetric.bounded c two one :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (bounded_sum qone a one one one one (le_refl _) (le_refl _) qone_bounded
        (GaussianLocalLogarithmLinearRemainder.linear_unit_bound _ _ _ hs))
  have scaled : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input scaledF A d :=
    GaussianNamedNaturalScale.exponential_input L K K one x ix (le_refl K)
  have original := exponential_input scaledF d (scaled_regular w R B K h)
  exact cross_trans _ _ _ _ _ _ (GaussianExponentialRadiusIndependence.same_input_cross scaledF (U scaledF d) A d original scaled)
    (GaussianBoundedIntegerExponential.integer_power_cross L K one x c two (.andI ix (.andI e hc)))

theorem terminal_factorization (z B K : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    GaussianBarnesCanonicalBaseProductShift.terminal z B K ≐
      qmul (power (naturalPoint K) K) (normalizedPower (translated z B one) B K) := by
  let w := translated z B one
  let x := GaussianBarnesCanonicalDeflatedFactor.translatedValue w B K
  let y := GaussianBarnesCanonicalDeflatedFactor.translatedValue z B (succ K)
  let a := GaussianBarnesCanonicalFactor.base w B K
  have hD := positive_product B K hB hK
  have left := natScale_represents K a (translated w B K) (B*K) hD (GaussianBarnesCanonicalBase.base_represents w B K hB hK)
  have right := represents_rescale x (translated w B K) B K (ofGaussian_represents _ _ hB)
  have scale : Γ ⊢[PRAAx] x ≐ qmul (naturalPoint K) a :=
    (canonical_unique _ _ _ _ (ofGaussian_canonical _ _ hB) (natScale_canonical _ _) hD right left).eqTrans
      (natScale_as_product K a)
  have e : Γ ⊢[PRAAx] y ≐ x := by
    apply canonical_unique _ _ _ B (ofGaussian_canonical _ _ hB) (ofGaussian_canonical _ _ hB) hB
      (hrv := ofGaussian_represents (translated w B K) B hB)
    apply represents_congr (.eqRefl _) _ (.eqRefl _) (ofGaussian_represents (translated z B (succ K)) B hB)
    apply equal_of_values <;> simp only [w,translated,re_add,im_add,re_scale,im_scale] <;> ipra_simps <;> ring
  exact (congrAp2 powerF (.eqRefl K) (e.eqTrans scale)).eqTrans (power_product _ _ K)

theorem actual_Barnes_exponential_terminal_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent (E scaledF) constantF (data (var 0) (var 1) (var 2) (var 3))
      (normalizedPower (var 0) (var 2) (var 3))) :=
  closeUniv 4 (.impI (exponentiated_scaled _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTerminalPower
