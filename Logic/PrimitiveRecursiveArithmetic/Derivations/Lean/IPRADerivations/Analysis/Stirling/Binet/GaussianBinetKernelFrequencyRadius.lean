import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetKernelFrequencyGrid
import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceStripHorizon

/-!
# Independent radii for the Binet frequency grid

The sine rectangle can use a larger bound for its damping exponential
without changing the actual compact sampler's parameters. The two
cofinal product names represent the same integrand at each shared tag.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelFrequencyRadius

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetKernelFrequencyGrid (cofinalBody originalData physical_row_at)
open GaussianBinetKernelFrozenIndependent (dampedNumerator errorDenominator error_denominator_positive)
open GaussianBinetLaplaceIntegrand (cofinalF cofinalData)
open GaussianBinetOscillatoryColumns (damping)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalFiniteProduct (offset_at)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def errorNumerator (p q I : PTm n) : PTm n := dampedNumerator p q I+two*I*unit p

@[simp] theorem subst_errorNumerator {m : ℕ} (σ : Fin n → PTm m) (p q I : PTm n) :
    Syn.subst σ (errorNumerator p q I) = errorNumerator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ I) := by
  simp [errorNumerator,two,one]

theorem damping_suffix_error (j J s p q k I N X Y D sign S R T C W : PTm n)
    (hS : Γ ⊢[PRAAx] source X Y D sign S) (hR : Γ ⊢[PRAAx] source X Y D sign R)
    (hN : Γ ⊢[PRAAx] le one N) (hj : Γ ⊢[PRAAx] le (J+j) N) (hI : Γ ⊢[PRAAx] le one I)
    (hk : Γ ⊢[PRAAx] le (I*unit p) (unit k))
    (hw : Γ ⊢[PRAAx] C ≐ W) (ht : Γ ⊢[PRAAx] T ≐ W) (hs : Γ ⊢[PRAAx] le p (s+N)) :
    Γ ⊢[PRAAx] distanceBounded
      (qmul (damping s X Y D sign W (J+j) N S) (GaussianBinetKernelFrozenPrefix.value k I (W*(J+j)) N))
      (inst2 (offB cofinalBody) j (pairT J (originalData q N X Y D sign R T C)))
      (errorNumerator p q I) (errorDenominator p q I) := by
  let A := W*(J+j)
  let U := unit p
  let V := unit q
  let K := errorDenominator p q I
  have hK := error_denominator_positive p q I hI
  have hV := unit_positive (Γ := Γ) q
  have upper : Γ ⊢[PRAAx] le A (W*N) :=
    le_congr (mul_comm (J+j) W) (mul_comm N W) (mul_le_mul_right W hj)
  have guard : Γ ⊢[PRAAx] le A (T*N) := le_congr (.eqRefl _) (congrMul ht.eqSymm (.eqRefl N)) upper
  have first := GaussianBinetKernelFrequencyGrid.damping_suffix_error j J s p q k I N X Y D sign S T C W
    hS hN hj hI hk hw ht hs
  have cross := GaussianBinetLaplaceStripHorizon.integrand_coherence .cofinal X Y D sign S T R T zero A N
    (.andI hS (.andI hN guard)) (.andI hR (.andI hN guard))
  have changeRadius := GaussianNameEquivalence.cross_at cofinalF cofinalF
    (cofinalData X Y D sign S T A N) (cofinalData X Y D sign R T A N) q q cross
  have suffix_at (r : PTm n) :
      Γ ⊢[PRAAx] inst2 (offB cofinalBody) j (pairT J (originalData q N X Y D sign r T C)) ≐
        ap2 cofinalF q (cofinalData X Y D sign r T A N) :=
    (offset_at cofinalBody J j (originalData q N X Y D sign r T C)).eqTrans
      (physical_row_at (J+j) q N X Y D sign r T C W hw)
  have last := distance_radius_mono _ _ _ _ (two*I*U) K (positive_product _ _ hV hV) hK
    (le_of_eq_add (d := zero) (by dsimp only [K,errorDenominator,U,V]; ipra_ring))
    (distance_congr (suffix_at S).eqSymm (suffix_at R).eqSymm (.eqRefl _) (.eqRefl _) changeRadius)
  exact distance_triangle_same _ _ _ _ _ _ hK first last

end LeanProofs.IPRA.Analysis.GaussianBinetKernelFrequencyRadius
