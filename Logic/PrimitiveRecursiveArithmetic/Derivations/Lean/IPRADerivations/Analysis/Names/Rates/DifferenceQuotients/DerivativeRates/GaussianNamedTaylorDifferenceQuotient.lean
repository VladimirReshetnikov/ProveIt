import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.NamedIncrements.GaussianNamedIncrementDifferenceQuotient
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianNamedMultiplyRate
import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport

/-!
# Divide a named Taylor estimate by an apart increment

Use the actual reciprocal program of the increment. Its certified norm
bound multiplies the leading Taylor error. The same reciprocal cancels
the increment in the first-order term, preserving both observation errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedTaylorDifferenceQuotient

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (multiplyF multiplyData multiply_equivalent multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_to_diagonal cross_trans)
open GaussianNameReciprocal (R nameData name_fast product_one)
open GaussianNameRingLaws (multiply_associative multiply_commutative multiply_one_left oneF one_fast)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound leadingNumerator leadingDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "inverseF" => GaussianNameReciprocal.nameF
local notation "diffF" => GaussianNamedDifference.nameF
local notation "diffData" => GaussianNamedDifference.data
local notation "quotientF" => GaussianNamedIncrementDifferenceQuotient.nameF
local notation "quotientData" => GaussianNamedIncrementDifferenceQuotient.data

def source (F G H S : PR 2) (x y z w a E D : PTm n) : Fm PTm n :=
  GaussianNamedIncrementDifferenceQuotient.input F G H x y z a ⋏
    (pointCN S w ⋏ (le one D ⋏
      independentRate (diffF F G) (multiplyF H S) (diffData x y) (multiplyData H S z w) E D))

private theorem cancel_weight (H S : PR 2) (z w a : PTm n)
    (hh : Γ ⊢[PRAAx] GaussianNameReciprocal.input H a z) (hs : Γ ⊢[PRAAx] pointCN S w) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (inverseF H) (multiplyF H S)) S
      (multiplyData (inverseF H) (multiplyF H S) (nameData a z) (multiplyData H S z w)) w := by
  let J := inverseF H
  let u := nameData a z
  have hj := name_fast H a z hh.andE₁ hh.andE₂
  have grouped := multiply_associative J H S u z w hj hh.andE₁ hs
  have swapped := multiply_commutative J H u z hj hh.andE₁
  have one := cross_trans _ _ _ _ _ _ swapped
    (cross_trans _ _ _ _ _ _ (product_one H a z hh.andE₁ hh.andE₂)
      (GaussianBoundedInverseApartness.ones_equivalent z w))
  have linear := multiply_equivalent (multiplyF J H) oneF S S (multiplyData J H u z) w w w
    (multiply_fast J H u z hj hh.andE₁) (one_fast w) hs hs
    (cross_to_diagonal _ _ _ _ one) (cross_to_diagonal _ _ _ _ (cross_refl _ _ hs))
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ grouped)
    (cross_trans _ _ _ _ _ _ linear (multiply_one_left S w hs))

theorem quotient_rate (F G H S : PR 2) (x y z w a E D : PTm n)
    (h : Γ ⊢[PRAAx] source F G H S x y z w a E D) :
    Γ ⊢[PRAAx] independentRate (quotientF F G H) S (quotientData F G H x y z a) w (R a*E) D := by
  let J := inverseF H
  let P := diffF F G
  let T := multiplyF H S
  let u := nameData a z
  let v := diffData x y
  let t := multiplyData H S z w
  have hh := h.andE₁.andE₂.andE₂
  have hs := h.andE₂.andE₁
  have hD := h.andE₂.andE₂.andE₁
  have hj : Γ ⊢[PRAAx] pointCN J u := name_fast H a z hh.andE₁ hh.andE₂
  have hp : Γ ⊢[PRAAx] pointCN P v := GaussianNamedDifference.name_regular F G x y h.andE₁.andE₁ h.andE₁.andE₂.andE₁
  have ht : Γ ⊢[PRAAx] pointCN T t := multiply_fast H S z w hh.andE₁ hs
  have signed : Γ.map Fm.shift ⊢[PRAAx] GaussianNameReciprocal.input H (Syn.shift a) (Syn.shift z) :=
    by simpa [Fm.shift, Syn.shift] using hh.shift
  have bound : Γ ⊢[PRAAx] sampleBound J u (R a) := by
    refine .allI ?_
    simpa [sampleBound, Syn.shift, u, J] using
      GaussianNamedIncrementDifferenceQuotient.inverse_sample_bound H (Syn.shift a) (Syn.shift z) (var 0) signed
  have rate := GaussianNamedMultiplyRate.independent_rate J P J T u v u t zero one E D
    (GaussianNameBounds.U P v) (R a) (le_refl one) hD hj hp hj ht
    (GaussianNameBounds.all_samples_bounded P v hp) bound (GaussianNamedDifferenceRate.self_rate J u hj)
    h.andE₂.andE₂.andE₂
  have scaled := GaussianNamedDifferenceRate.rate_parameters_congr (multiplyF J P) (multiplyF J T)
    (multiplyData J P u v) (multiplyData J T u t) _ _ (R a*E) D
    (by unfold leadingNumerator; ipra_ring) (by unfold leadingDenominator; ipra_ring) rate
  have replace := cancel_weight H S z w a hh hs
  have hq := GaussianNamedIncrementDifferenceQuotient.name_regular F G H x y z a h.andE₁
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hD scaled (cross_refl _ _ hq)
    (cross_symm _ _ _ _ replace)

theorem actual_named_Taylor_difference_quotient_rate_closed (F G H S : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (source F G H S (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
        independentRate (quotientF F G H) S (quotientData F G H (var 0) (var 1) (var 2) (var 4))
          (var 3) (R (var 4) * var 5) (var 6)) :=
  closeUniv 7 (.impI (quotient_rate F G H S _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedTaylorDifferenceQuotient
