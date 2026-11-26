import IPRADerivations.Analysis.Names.GaussianNameArithmetic
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalDistanceOrder
import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.GaussianReconstructionRoots

/-!
# Exact radius arithmetic for the Euler comparison

The three panel distances are added in the same order as the literal
shared-grid split. The two sampler bindings contribute their
observation errors. All intermediate radii use positive natural denominators.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSharpResidualAssembly

open_ipra
open GaussianRationalHorner (positive_product qadd)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_sum)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric)
open GaussianReconstructionRoots (distance_triangle)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Adds the low, middle, and tail errors while preserving both leading
numerators, with U the dyadic working denominator. -/
theorem panel_distance (a b c d e f M N A B U : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hB : Γ ⊢[PRAAx] le one B) (hU : Γ ⊢[PRAAx] le one U)
    (hlow : Γ ⊢[PRAAx] distanceBounded a b (U+N) (N*U))
    (hmiddle : Γ ⊢[PRAAx] distanceBounded c d (M*U+two*N) (N*U))
    (htail : Γ ⊢[PRAAx] distanceBounded e f (A*U+B) (B*U)) :
    Γ ⊢[PRAAx] distanceBounded (qadd (qadd a c) e) (qadd (qadd b d) f)
      (((one+M)*B+A*N)*U+num 4*(N*B)) (N*B*U) := by
  have hd1 := positive_product N U hN hU
  have hd2 := positive_product B U hB hU
  have first := GaussianNameArithmetic.sum_distance a b c d _ _ _ hd1 hlow hmiddle
  have sum := bound_congr (GaussianNameArithmetic.sum_difference (qadd a c) (qadd b d) e f).eqSymm
    (.eqRefl _) (.eqRefl _) (bounded_sum _ _ _ _ _ _ hd1 hd2 first htail)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hd1 hd2)
    (positive_product _ _ (positive_product _ _ hN hB) hU)
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl _)) sum

/-- Reinstates the whole grid on both sides, spending each split at the
working dyadic scale. -/
theorem split_distance (a b c d X B U : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hU : Γ ⊢[PRAAx] le one U)
    (hab : Γ ⊢[PRAAx] distanceBounded a b one U)
    (hbc : Γ ⊢[PRAAx] distanceBounded b c (X*U+num 4*B) (B*U))
    (hdc : Γ ⊢[PRAAx] distanceBounded d c one U) : Γ ⊢[PRAAx]
    distanceBounded a d (X*U+num 6*B) (B*U) := by
  have hd := positive_product B U hB hU
  have first := distance_triangle _ _ _ _ _ _ _ hU hd hab hbc
  have sum := distance_triangle _ _ _ _ _ _ _ (positive_product _ _ hU hd) hU first
    (distance_symmetric _ _ _ _ hU hdc)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hU hd) hU) hd
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl _)) sum

def boundNumerator (A B P V : PTm n) : PTm n := A*(P*V)+(P+V)*B
def boundDenominator (B P V : PTm n) : PTm n := B*(P*V)

/-- Adds both sampler bindings at arbitrary independent requested precisions.
The total remaining allowance is twelve units at the working precision. -/
theorem sampler_distance (a b c d A B P V U : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hP : Γ ⊢[PRAAx] le one P) (hV : Γ ⊢[PRAAx] le one V)
    (hU : Γ ⊢[PRAAx] le one U)
    (hba : Γ ⊢[PRAAx] distanceBounded b a (U+two*P) (U*P))
    (hbc : Γ ⊢[PRAAx] distanceBounded b c (A*U+num 6*B) (B*U))
    (hcd : Γ ⊢[PRAAx] distanceBounded c d (U+num 4*V) (U*V)) : Γ ⊢[PRAAx]
    distanceBounded a d (boundNumerator A B P V*U+num 12*boundDenominator B P V)
      (boundDenominator B P V*U) := by
  have hp := positive_product U P hU hP
  have hv := positive_product U V hU hV
  have hd := positive_product B U hB hU
  have first := distance_triangle _ _ _ _ _ _ _ hp hd (distance_symmetric _ _ _ _ hp hba) hbc
  have sum := distance_triangle _ _ _ _ _ _ _ (positive_product _ _ hp hd) hv first hcd
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hp hd) hv)
    (positive_product _ _ (positive_product _ _ hB (positive_product _ _ hP hV)) hU)
    (le_congr (by unfold boundNumerator boundDenominator; ipra_ring) (.eqRefl _) (le_refl _)) sum

end LeanProofs.IPRA.Analysis.GaussianEulerSharpResidualAssembly
