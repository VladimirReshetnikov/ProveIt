import IPRADerivations.Analysis.Barnes.Prefactors.GaussianBarnesCanonicalPrefactor
import IPRADerivations.Analysis.Names.Differences.GaussianNamedStrictOrderDifference
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.Folded.GaussianGammaFoldedApproximantBalance
import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.GaussianGammaEulerHeadLower

/-!
# The exact shift of the original Barnes prefactor

The ratio is represented by exponentiating the named difference of
the two original prefactor exponents. The product identity keeps
the original Stirling and Euler–Mascheroni observations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorShift

open_ipra
open GaussianBarnesCanonicalPrefactor (linearF linearData linear_regular correctionF correctionData correction_regular
  combinedF combinedData combined radius)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_refl)
open GaussianNameRingLaws (add_associative add_commutative negativeF negativeData negative_fast)
open GaussianNamedGammaHalfShift (add_cross)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "P" => GaussianBarnesCanonicalPrefactor.nameF
local notation "pd" => GaussianBarnesCanonicalPrefactor.data
local notation "Exp" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data
local notation "D" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data

abbrev exponentF : PR 2 := addF linearF correctionF
def exponentData (z B : PTm n) : PTm n := addData (linearData z B) (correctionData z B)
abbrev differenceF : PR 2 := D exponentF exponentF
def differenceData (z B : PTm n) : PTm n := dd (exponentData (translated z B one) B) (exponentData z B)
abbrev nameF : PR 2 := Exp differenceF
def data (z B : PTm n) : PTm n := exponentialInputData differenceF (differenceData z B)

theorem exponent_regular (z B : PTm n) : Γ ⊢[PRAAx] pointCN exponentF (exponentData z B) :=
  add_fast _ _ _ _ (linear_regular z B) (correction_regular z B)

theorem difference_regular (z B : PTm n) : Γ ⊢[PRAAx] pointCN differenceF (differenceData z B) :=
  GaussianNamedDifference.name_regular exponentF exponentF _ _ (exponent_regular _ _) (exponent_regular _ _)

theorem regular (z B : PTm n) : Γ ⊢[PRAAx] pointCN nameF (data z B) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input _ _ (difference_regular z B))

private theorem add_difference (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) : Γ ⊢[PRAAx]
    crossEquivalent (addF f (D g f)) g (addData x (dd y x)) y := by
  let F := negativeF f
  let X := negativeData x
  have hx := negative_fast f x hf
  have a := cross_symm _ _ _ _ (add_associative f g F x y X hf hg hx)
  have b := add_cross (addF f g) (addF g f) F F (addData x y) (addData y x) X X
    (add_fast _ _ _ _ hf hg) (add_fast _ _ _ _ hg hf) hx hx (add_commutative f g x y hf hg) (cross_refl _ _ hx)
  exact cross_trans _ _ _ _ _ _ a (cross_trans _ _ _ _ _ _ b (GaussianNamedStrictOrderDifference.sum_sub_right g f y x hg hf))

theorem prefactor_shift (z B : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF P nameF) P (multiplyData P nameF (pd z B) (data z B)) (pd (translated z B one) B) := by
  let w := translated z B one
  let f := exponentF
  let g := differenceF
  let x := exponentData z B
  let y := exponentData w B
  let u := differenceData z B
  let R := radius z B+radius z B
  let S := U g u
  let T := radius w B+radius w B
  have hx := GaussianExponentialReference.add_input linearF correctionF (radius z B) (linearData z B) (correctionData z B)
    (GaussianBarnesCanonicalPrefactor.linear_input (Γ := Γ) z B) (GaussianBarnesCanonicalPrefactor.correction_input (Γ := Γ) z B)
  have hy := GaussianExponentialReference.add_input linearF correctionF (radius w B) (linearData w B) (correctionData w B)
    (GaussianBarnesCanonicalPrefactor.linear_input (Γ := Γ) w B) (GaussianBarnesCanonicalPrefactor.correction_input (Γ := Γ) w B)
  have hu := exponential_input g u (difference_regular (Γ := Γ) z B)
  have h1 := GaussianGammaAdjacentCutoff.multiply_cross P combinedF nameF nameF (pd z B) (combinedData z B) (data z B) (data z B)
    (GaussianBarnesCanonicalPrefactor.regular z B) (GaussianRadiusExponentialName.name_regular _ _ _ hx)
    (regular z B) (regular z B) (combined z B) (cross_refl _ _ (regular z B))
  have h2 := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent f g f R S T x u y hx hu hy
    (add_difference f f x y (exponent_regular z B) (exponent_regular w B))
  exact cross_trans _ _ _ _ _ _ h1 (cross_trans _ _ _ _ _ _ h2 (cross_symm _ _ _ _ (combined w B)))

theorem actual_Barnes_original_prefactor_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (let z := var 0
     let B := var 1
     crossEquivalent (multiplyF P nameF) P (multiplyData P nameF (pd z B) (data z B)) (pd (translated z B one) B)) :=
  closeUniv 2 (prefactor_shift _ _)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorShift
