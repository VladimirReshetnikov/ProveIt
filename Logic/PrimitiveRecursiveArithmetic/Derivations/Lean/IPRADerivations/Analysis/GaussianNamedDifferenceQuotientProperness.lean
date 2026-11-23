import IPRADerivations.Analysis.GaussianNamedDifferenceQuotient

/-!
# Endpoint replacement in the original divided-difference program

Actual negative, addition and multiplication properness transport both
original endpoints. The reciprocal is the same literal fixed program
value on both sides; the replacement law needs only regular endpoints.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDifferenceQuotientProperness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal cross_refl)
open GaussianNameRingLaws (negativeF negativeData negative_fast negative_equivalent)
open GaussianNameArithmetic (add_equivalent multiply_equivalent)
open GaussianBoundedConstantProductName (constantF constant_regular)
open GaussianNamedDifferenceQuotient (nameF data inverse)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (f f' g g' : PR 2) (x x' y y' : PTm n) : Fm PTm n :=
  pointCN f x ⋏ (pointCN f' x' ⋏ (pointCN g y ⋏ (pointCN g' y' ⋏
    (crossEquivalent f f' x x' ⋏ crossEquivalent g g' y y'))))

@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (f f' g g' : PR 2) (x x' y y' : PTm n) :
    (input f f' g g' x x' y y').subst σ = input f f' g g' (Syn.subst σ x) (Syn.subst σ x')
      (Syn.subst σ y) (Syn.subst σ y') := by simp [input]

theorem difference_proper (f f' g g' : PR 2) (x x' y y' : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hfp : Γ ⊢[PRAAx] pointCN f' x')
    (hg : Γ ⊢[PRAAx] pointCN g y) (hgp : Γ ⊢[PRAAx] pointCN g' y')
    (hfe : Γ ⊢[PRAAx] crossEquivalent f f' x x') (hge : Γ ⊢[PRAAx] crossEquivalent g g' y y') : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNamedDifference.nameF f g) (GaussianNamedDifference.nameF f' g')
      (GaussianNamedDifference.data x y) (GaussianNamedDifference.data x' y') :=
  add_equivalent f f' (negativeF g) (negativeF g') x x' (negativeData y) (negativeData y')
    hf hfp (negative_fast g y hg) (negative_fast g' y' hgp) (cross_to_diagonal _ _ _ _ hfe)
    (cross_to_diagonal _ _ _ _ (negative_equivalent g g' y y' hg hgp (cross_to_diagonal _ _ _ _ hge)))

theorem proper (f f' g g' : PR 2) (x x' y y' h D : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hfp : Γ ⊢[PRAAx] pointCN f' x')
    (hg : Γ ⊢[PRAAx] pointCN g y) (hgp : Γ ⊢[PRAAx] pointCN g' y')
    (hfe : Γ ⊢[PRAAx] crossEquivalent f f' x x') (hge : Γ ⊢[PRAAx] crossEquivalent g g' y y') : Γ ⊢[PRAAx]
    crossEquivalent (nameF f g) (nameF f' g') (data f g x y h D) (data f' g' x' y' h D) := by
  have hc : Γ ⊢[PRAAx] pointCN constantF (inverse h D) := constant_regular _
  exact multiply_equivalent constantF constantF (GaussianNamedDifference.nameF f g) (GaussianNamedDifference.nameF f' g')
    (inverse h D) (inverse h D) (GaussianNamedDifference.data x y) (GaussianNamedDifference.data x' y') hc hc
    (GaussianNamedDifference.name_regular f g x y hf hg) (GaussianNamedDifference.name_regular f' g' x' y' hfp hgp)
    (cross_to_diagonal _ _ _ _ (cross_refl _ _ hc))
    (cross_to_diagonal _ _ _ _ (difference_proper f f' g g' x x' y y' hf hfp hg hgp hfe hge))

theorem actual_original_divided_difference_endpoint_replacement_closed (f f' g g' : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input f f' g g' (var 0) (var 1) (var 2) (var 3) ⟶
      crossEquivalent (nameF f g) (nameF f' g')
        (data f g (var 0) (var 2) (var 4) (var 5)) (data f' g' (var 1) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (proper f f' g g' _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedDifferenceQuotientProperness
