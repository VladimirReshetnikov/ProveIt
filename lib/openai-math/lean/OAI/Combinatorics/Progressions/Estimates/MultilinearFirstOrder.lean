import Mathlib.LinearAlgebra.Multilinear.Basic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {R I L E : Type*} [CommRing R] [Fintype I] [DecidableEq I]
  [AddCommGroup L] [Module R L] [AddCommGroup E] [Module R E]

theorem multilinear_eq_first_order_of_two_vanish
    (f : MultilinearMap R (fun _ : I => L) E) (C D : I → Submodule R L)
    (hDC : ∀ i, D i ≤ C i)
    (hvanish : ∀ v : I → L, (∀ i, v i ∈ C i) → ∀ i j, i ≠ j →
      v i ∈ D i → v j ∈ D j → f v = 0)
    (x y : I → L) (hx : ∀ i, x i ∈ C i) (hy : ∀ i, y i ∈ D i) :
    f (x + y) = f x + f.linearDeriv x y := by
  classical
  rw [f.map_add_eq_map_add_linearDeriv_add]
  have hsum : (∑ s : Finset I with 2 ≤ s.card, f (s.piecewise y x)) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    have hs' : 1 < s.card := (Finset.mem_filter.mp hs).2
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hs'
    refine hvanish _ ?_ i j hij ?_ ?_
    · intro k
      by_cases hk : k ∈ s
      · simpa only [s.piecewise_eq_of_mem _ _ hk] using hDC k (hy k)
      · simpa only [s.piecewise_eq_of_notMem _ _ hk] using hx k
    · simpa only [s.piecewise_eq_of_mem _ _ hi] using hy i
    · simpa only [s.piecewise_eq_of_mem _ _ hj] using hy j
  rw [hsum, add_zero]

theorem exists_linear_expansion_of_two_vanish
    (f : MultilinearMap R (fun _ : I => L) E) (C D : I → Submodule R L)
    (hDC : ∀ i, D i ≤ C i)
    (hvanish : ∀ v : I → L, (∀ i, v i ∈ C i) → ∀ i j, i ≠ j →
      v i ∈ D i → v j ∈ D j → f v = 0)
    (x : I → L) (hx : ∀ i, x i ∈ C i) :
    ∃ A : (∀ i, D i) →ₗ[R] E, ∀ y : ∀ i, D i,
      f (fun i => x i + (y i : L)) = f x + A y := by
  classical
  let inclusion : (∀ i, D i) →ₗ[R] (I → L) :=
    LinearMap.pi (fun i => (D i).subtype.comp (LinearMap.proj i))
  refine ⟨(f.linearDeriv x).comp inclusion, ?_⟩
  intro y
  exact multilinear_eq_first_order_of_two_vanish f C D hDC hvanish x
    (fun i => y i) hx (fun i => (y i).property)

end Erdos3

end

end OAI
