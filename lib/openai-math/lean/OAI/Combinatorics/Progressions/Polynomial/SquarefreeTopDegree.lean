import OAI.Combinatorics.Progressions.Estimates.SquarefreePermutationFiltration

namespace OAI

section

namespace Erdos3

noncomputable def SquarefreeIndex.full (ι : Type*) [Fintype ι] : SquarefreeIndex ι :=
  ⟨Finsupp.equivFunOnFinite.symm (fun _ => 1), fun _ => le_rfl⟩

theorem SquarefreeIndex.full_apply {ι : Type*} [Fintype ι] (i : ι) :
    (full ι).val i = 1 := rfl

theorem SquarefreeIndex.one_le_iff {ι : Type*} [Fintype ι] (a : SquarefreeIndex ι) :
    (fun _ => 1) ≤ (fun i => a.val i) ↔ a = full ι := by
  constructor
  · intro h
    apply Subtype.ext
    ext i
    exact le_antisymm (a.property i) (h i)
  · rintro rfl
    intro i
    exact le_rfl

theorem SquarefreeIndex.permute_full {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    permute e (full ι) = full κ := by
  apply Subtype.ext
  ext j
  rfl

theorem squarefree_top_monomial {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (x : SquarefreePolynomial ι L)
    (hx : x ∈ squarefreeSupportModule (fun a : SquarefreeIndex ι => (fun _ => 1) ≤ fun i => a.val i)) :
    x = squarefreeMonomial (SquarefreeIndex.full ι)
      (squarefreePolynomialEquiv x (SquarefreeIndex.full ι)) := by
  apply squarefreePolynomialEquiv.injective
  ext a
  by_cases ha : SquarefreeIndex.full ι = a
  · subst a
    rw [squarefreePolynomialEquiv_monomial_self]
  · rw [squarefreePolynomialEquiv_monomial_ne _ _ ha]
    exact hx a (fun h => ha ((SquarefreeIndex.one_le_iff a).mp h).symm)

namespace MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeBlockPermute_eq_self_top (e : ι ≃ ι) (he : ∀ i, π (e i) = π i)
    (x : F.SquarefreeAlgebra π) (hx : x ∈ F.squarefreeMultidegreeLayer π (fun _ => 1)) :
    F.squarefreeBlockPermute π e he x = x := by
  apply Subtype.ext
  change squarefreePermute e x.val = x.val
  rw [squarefree_top_monomial x.val hx, squarefreePermute_monomial, SquarefreeIndex.permute_full]

end MultidegreeLieFiltration

end Erdos3

end

end OAI
