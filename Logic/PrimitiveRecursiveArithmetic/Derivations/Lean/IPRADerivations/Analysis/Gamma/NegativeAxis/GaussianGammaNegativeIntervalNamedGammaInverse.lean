import IPRADerivations.Analysis.Exponential.GaussianExponentialInverse
import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalNamedGamma
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaNegativeIntervalSignedDigammaQuotient

/-!
# A multiplicative inverse for the original named negative Gamma

Exponentiating the negative log-magnitude and restoring the interval
sign gives a reciprocal of the original named Gamma.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedGammaInverse

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaFiniteApproximantName (exponential_input)
open GaussianGammaNegativeIntervalNamedGamma (signedF signedData signed_regular actualF actualData)
open GaussianGammaNegativeIntervalNamedSign (valueF valueData value_regular)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianNameRingLaws (negativeF negativeData multiply_commutative oneF)
open GaussianNamedEulerUnitTime (source)
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianGammaNegativeIntervalNamedLog.nameF
local notation "ld" => GaussianGammaNegativeIntervalNamedLog.data
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data

def inverseF (f : PR 2) : PR 2 := valueF (E (negativeF (L f)))
def inverseData (f : PR 2) (x W N : PTm n) : PTm n :=
  valueData (E (negativeF (L f))) N (ed (U (L f) (ld x W N)) (negativeData (ld x W N)))

private theorem negative_log_input (f : PR 2) (x W N : PTm n) (hs : Γ ⊢[PRAAx] source f x W) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input (negativeF (L f)) (U (L f) (ld x W N)) (negativeData (ld x W N)) :=
  GaussianExponentialInverse.negative_input _ _ _
    (exponential_input _ _ (GaussianGammaNegativeIntervalNamedLog.name_regular f x W N hs))

theorem inverse_regular (f : PR 2) (x W N : PTm n) (hs : Γ ⊢[PRAAx] source f x W) :
    Γ ⊢[PRAAx] pointCN (inverseF f) (inverseData f x W N) :=
  value_regular _ _ _ (GaussianRadiusExponentialName.name_regular _ _ _ (negative_log_input f x W N hs))

theorem left_inverse (f : PR 2) (x W N : PTm n) (hs : Γ ⊢[PRAAx] source f x W) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (inverseF f) (actualF f)) oneF
      (multiplyData (inverseF f) (actualF f) (inverseData f x W N) (actualData f x W N)) (ld x W N) := by
  let F := E (negativeF (L f))
  let X := ed (U (L f) (ld x W N)) (negativeData (ld x W N))
  let G := signedF f
  let Y := signedData f x W N
  have hn : Γ ⊢[PRAAx] pointCN F X := GaussianRadiusExponentialName.name_regular _ _ _ (negative_log_input f x W N hs)
  have hp := signed_regular f x W N hs
  have hsigned := GaussianGammaNegativeIntervalSignedDigammaQuotient.double_sign_product F G N X Y hn hp
  have hcomm := multiply_commutative F G X Y hn hp
  have hinv := GaussianExponentialInverse.exponential_inverse (L f) (U (L f) (ld x W N)) (ld x W N)
    (exponential_input _ _ (GaussianGammaNegativeIntervalNamedLog.name_regular f x W N hs))
  have hplain : Γ ⊢[PRAAx] crossEquivalent (multiplyF F G) oneF (multiplyData F G X Y) (ld x W N) :=
    cross_trans (multiplyF F G) (multiplyF G F) oneF _ _ _ hcomm hinv
  exact cross_trans (multiplyF (inverseF f) (actualF f)) (multiplyF F G) oneF _ _ _ hsigned hplain

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedGammaInverse
