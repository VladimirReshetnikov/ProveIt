import OAI.Combinatorics.Progressions.Linear.RankQuotientHeightBudget

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module
open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)
  {κ : SquarefreeIndex ι → Type*} [∀ a, Fintype (κ a)]
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer π a))

noncomputable def squarefreeSupportedFinBasis (P : SquarefreeIndex ι → Prop) :
    Basis (Fin (finrank ℚ
      ((squarefreeSupportModule P).comap (F.squarefreeAdaptedSubalgebra π).incl.toLinearMap))) ℚ
      ((squarefreeSupportModule P).comap (F.squarefreeAdaptedSubalgebra π).incl.toLinearMap) := by
  classical
  exact (F.squarefreeSupportedBasis π b P).reindex
    (Fintype.equivFinOfCardEq (finrank_eq_card_basis (F.squarefreeSupportedBasis π b P)).symm)

theorem squarefreeSupportedFinBasis_height (P : SquarefreeIndex ι → Prop) (j k) :
    RationalHeightLE ((F.squarefreeBasis π b).repr (F.squarefreeSupportedFinBasis π b P j).val k) 1 := by
  classical
  unfold squarefreeSupportedFinBasis
  rw [Basis.reindex_apply, F.squarefreeSupportedBasis_coe]
  exact basis_repr_height_one _ _ _

noncomputable def squarefreeMultidegreeBasis (c : ι → ℕ) :
    Basis (Fin (finrank ℚ (F.squarefreeMultidegreeLayer π c))) ℚ (F.squarefreeMultidegreeLayer π c) :=
  F.squarefreeSupportedFinBasis π b (fun a => c ≤ fun i => a.val i)

theorem squarefreeMultidegreeBasis_height (c : ι → ℕ) (j k) :
    RationalHeightLE ((F.squarefreeBasis π b).repr (F.squarefreeMultidegreeBasis π b c j).val k) 1 :=
  F.squarefreeSupportedFinBasis_height π b _ j k

noncomputable def squarefreeDegreeBasis (n : ℕ) :
    Basis (Fin (finrank ℚ (F.squarefreeDegreeLayer π n))) ℚ (F.squarefreeDegreeLayer π n) :=
  F.squarefreeSupportedFinBasis π b (fun a => n ≤ ∑ i, a.val i)

theorem squarefreeDegreeBasis_height (n : ℕ) (j k) :
    RationalHeightLE ((F.squarefreeBasis π b).repr (F.squarefreeDegreeBasis π b n j).val k) 1 :=
  F.squarefreeSupportedFinBasis_height π b _ j k

end Erdos3.MultidegreeLieFiltration

end

end OAI
