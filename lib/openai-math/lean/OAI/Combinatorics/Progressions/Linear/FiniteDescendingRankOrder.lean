import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

namespace OAI

section

namespace Erdos3

theorem exists_finite_descending_rank_equiv {I : Type*} [Fintype I]
    (rank : I → ℕ) :
    ∃ e : Fin (Fintype.card I) ≃ I, ∀ i j, i ≤ j → rank (e j) ≤ rank (e i) := by
  classical
  let key : I → OrderDual ℕ ×ₗ Fin (Fintype.card I) :=
    fun i => toLex (rank i, Fintype.equivFin I i)
  have hkey : Function.Injective key := by
    intro i j hij
    apply (Fintype.equivFin I).injective
    exact congrArg (fun z => (ofLex z).2) hij
  let _ : LinearOrder I := LinearOrder.lift' key hkey
  let e : Fin (Fintype.card I) ≃o I := Fintype.orderIsoFinOfCardEq I rfl
  refine ⟨e.toEquiv, ?_⟩
  intro i j hij
  have hle : key (e i) ≤ key (e j) := e.monotone hij
  exact Prod.Lex.monotone_fst _ _ hle

end Erdos3

end

end OAI
