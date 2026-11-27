import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.NamedIncrements.GaussianNamedIncrementDifferenceQuotient
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.EndpointRates.GaussianNamedDifferenceQuotientProperness

/-!
# Endpoint replacement with the same actual named reciprocal

Both original endpoint programs may be replaced by cross-equivalent
regular programs. The increment, apartness anchor and actual reciprocal
program/data are kept fixed. Existing difference and multiplication
properness preserve the original independently observed quotient names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedIncrementDifferenceQuotientProperness

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal cross_refl)
open GaussianNameArithmetic (multiply_equivalent)
open GaussianNamedIncrementDifferenceQuotient (nameF data)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (F F' G G' K : PR 2) (x x' y y' z a : PTm n) : Fm PTm n :=
  (pointCN F x ⋏ pointCN F' x') ⋏ ((pointCN G y ⋏ pointCN G' y') ⋏
    (GaussianNameReciprocal.input K a z ⋏ (crossEquivalent F F' x x' ⋏ crossEquivalent G G' y y')))

ipra_subst input

theorem proper (F F' G G' K : PR 2) (x x' y y' z a : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hfp : Γ ⊢[PRAAx] pointCN F' x')
    (hg : Γ ⊢[PRAAx] pointCN G y) (hgp : Γ ⊢[PRAAx] pointCN G' y')
    (hk : Γ ⊢[PRAAx] GaussianNameReciprocal.input K a z)
    (hfe : Γ ⊢[PRAAx] crossEquivalent F F' x x') (hge : Γ ⊢[PRAAx] crossEquivalent G G' y y') : Γ ⊢[PRAAx]
    crossEquivalent (nameF F G K) (nameF F' G' K) (data F G K x y z a) (data F' G' K x' y' z a) := by
  let J := GaussianNameReciprocal.nameF K
  let u := GaussianNameReciprocal.nameData a z
  have hj : Γ ⊢[PRAAx] pointCN J u := GaussianNameReciprocal.name_fast K a z hk.andE₁ hk.andE₂
  exact multiply_equivalent J J (GaussianNamedDifference.nameF F G) (GaussianNamedDifference.nameF F' G')
    u u (GaussianNamedDifference.data x y) (GaussianNamedDifference.data x' y') hj hj
    (GaussianNamedDifference.name_regular F G x y hf hg) (GaussianNamedDifference.name_regular F' G' x' y' hfp hgp)
    (cross_to_diagonal _ _ _ _ (cross_refl J u hj))
    (cross_to_diagonal _ _ _ _ (GaussianNamedDifferenceQuotientProperness.difference_proper F F' G G' x x' y y' hf hfp hg hgp hfe hge))

theorem actual_named_increment_quotient_endpoint_replacement_closed (F F' G G' K : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input F F' G G' K (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      crossEquivalent (nameF F G K) (nameF F' G' K)
        (data F G K (var 0) (var 2) (var 4) (var 5)) (data F' G' K (var 1) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (proper F F' G G' K _ _ _ _ _ _ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂
    Prf.hyp0.andE₂.andE₁.andE₁ Prf.hyp0.andE₂.andE₁.andE₂ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedIncrementDifferenceQuotientProperness
