import IPRADerivations.Analysis.Barnes.Growth.GaussianBarnesCanonicalDiskBound
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalProduct

/-!
# A uniform cutoff for Barnes values on a rational disk

The entire leading error budget depends only on the disk radius. The
common cutoff works for every admitted Gaussian rational encoding and
every later literal product, with independent observation clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalUniformCutoff

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBarnesCanonicalDiskBound (prefixBound prefix_U_le)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (endpoint endpoint_monotone)
open GaussianBarnesCanonicalProduct (amplification literalData cutoff_rate_of_le)
open GaussianBarnesCanonicalValue (prefixF nameF data)
open GaussianCoefficientNameBounds (unit)
open GaussianRootSchedule (binaryLength binary_length_correct binary_length_minimal)
open GaussianNamedInverseRate (independentRate)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def gain (R : PTm n) : PTm n :=
  (two*prefixBound R+two)*GaussianRadiusExponentialLipschitzRate.factor (GaussianBarnesCanonicalFiniteLog.radius R)

def cutoff (R p : PTm n) : PTm n := endpoint (GaussianFastValueCut.exponent (gain R) p) R

private theorem binary_length_mono (a b : PTm n) (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (binaryLength a) (binaryLength b) := by
  refine .orE (lt_or_le (binaryLength b) (binaryLength a)) ?_ Prf.hyp0
  exact .botE _ (.impE (binary_length_minimal a (binaryLength b) Prf.hyp0)
    (le_trans h.wk (binary_length_correct b).andE₁))

theorem cutoff_le (z R B p : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] le (GaussianBarnesCanonicalProduct.cutoff p z R B) (cutoff R p) := by
  have g : Γ ⊢[PRAAx] le (amplification z R B) (gain R) :=
    le_mul_mono (prefix_U_le z R B h) (le_refl _)
  exact endpoint_monotone _ _ R
    (add_le_add₂ (le_refl p) (add_le_add_right two (binary_length_mono _ _ g)))

theorem uniform_rate (z R B p N : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hN : Γ ⊢[PRAAx] le (cutoff R p) N) : Γ ⊢[PRAAx]
    independentRate prefixF nameF (literalData z R B N) (data z R B) one (unit p) :=
  cutoff_rate_of_le p z R B N h (le_trans (cutoff_le z R B p h) hN)

theorem actual_Barnes_canonical_product_uniform_disk_cutoff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let R := var 1
     let B := var 2
     let p := var 3
     let N := var 4
     source z R B ⟶ le (cutoff R p) N ⟶
       independentRate prefixF nameF (literalData z R B N) (data z R B) one (unit p)) :=
  closeUniv 5 (.impI (.impI (uniform_rate _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalUniformCutoff
