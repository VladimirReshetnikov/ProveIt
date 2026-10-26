import Mathlib.Data.Finset.Sort

/-! Standalone proof kernel for the pinned ProveIt physical-order theorem. -/
namespace ProveItReview

theorem strictMono_fin_eq_self {n : ℕ} (f : Fin n → Fin n)
    (hf : StrictMono f) (i : Fin n) : f i = i := by
  exact DFunLike.congr_fun
    (OrderHom.eq_id_of_injective (⟨f, hf.monotone⟩ : Fin n →o Fin n) hf.injective) i

-- The same argument works for every finite linearly ordered type.
theorem strictMono_finite_eq_self {α : Type*} [LinearOrder α] [Finite α]
    (f : α → α) (hf : StrictMono f) (x : α) : f x = x := by
  exact DFunLike.congr_fun
    (OrderHom.eq_id_of_injective (⟨f, hf.monotone⟩ : α →o α) hf.injective) x

example (f : Fin 0 → Fin 0) (hf : StrictMono f) : ∀ i, f i = i :=
  strictMono_fin_eq_self f hf

example (f : Fin 1 → Fin 1) (hf : StrictMono f) : f 0 = 0 :=
  strictMono_fin_eq_self f hf 0

#print axioms strictMono_fin_eq_self
#print axioms strictMono_finite_eq_self

end ProveItReview
