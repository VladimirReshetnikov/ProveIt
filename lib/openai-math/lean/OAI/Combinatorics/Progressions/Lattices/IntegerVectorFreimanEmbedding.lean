import Mathlib

namespace OAI

section

namespace Erdos3.FreimanModel

open scoped BigOperators Pointwise

noncomputable def coordinatePolynomial (n : ℕ) : (Fin n → ℤ) →+ Polynomial ℤ where
  toFun x := ∑ i : Fin n, Polynomial.monomial (i : ℕ) (x i)
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

theorem coordinatePolynomial_coeff {n : ℕ} (x : Fin n → ℤ) (i : Fin n) :
    (coordinatePolynomial n x).coeff (i : ℕ) = x i := by
  change (∑ j : Fin n, Polynomial.monomial (j : ℕ) (x j)).coeff (i : ℕ) = x i
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Polynomial.coeff_monomial, Fin.val_inj.ne.mpr hji]
  · simp

theorem coordinatePolynomial_injective (n : ℕ) :
    Function.Injective (coordinatePolynomial n) := by
  intro x y h
  funext i
  simpa only [coordinatePolynomial_coeff] using
    congrArg (fun p : Polynomial ℤ => p.coeff (i : ℕ)) h

theorem exists_fin_integer_embedding {n : ℕ} (A : Finset (Fin n → ℤ)) :
    ∃ f : (Fin n → ℤ) →+ ℤ, Set.InjOn f (A : Set _) := by
  classical
  let P := coordinatePolynomial n
  let R := (A ×ˢ A).biUnion fun xy => (P xy.1 - P xy.2).roots.toFinset
  obtain ⟨t, ht⟩ := R.exists_notMem
  let f := (Polynomial.evalRingHom t).toAddMonoidHom.comp P
  refine ⟨f, ?_⟩
  intro x hx y hy hxy
  by_contra hne
  have hP : P x - P y ≠ 0 :=
    sub_ne_zero.mpr (fun h => hne (coordinatePolynomial_injective n h))
  apply ht
  apply Finset.mem_biUnion.mpr
  refine ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
  change (P x - P y).eval t = 0
  rw [Polynomial.eval_sub, sub_eq_zero]
  exact hxy

theorem exists_integer_vector_embedding {I : Type*} [Fintype I]
    (A : Finset (I → ℤ)) : ∃ f : (I → ℤ) →+ ℤ, Set.InjOn f (A : Set _) := by
  classical
  let e := Fintype.equivFin I
  let r : (I → ℤ) →+ (Fin (Fintype.card I) → ℤ) :=
    { toFun := fun x j => x (e.symm j)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hr : Function.Injective r := by
    intro x y h
    funext i
    simpa only [r, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Equiv.symm_apply_apply] using
      congrFun h (e i)
  obtain ⟨f, hf⟩ := exists_fin_integer_embedding (A.image r)
  refine ⟨f.comp r, ?_⟩
  intro x hx y hy hxy
  exact hr (hf (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    (Finset.mem_image.mpr ⟨y, hy, rfl⟩) hxy)

theorem multiset_sum_mem_iterated_sumset {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (A : Finset G) {T : Multiset G} (hT : ∀ x ∈ T, x ∈ A) :
    T.sum ∈ T.card • A := by
  induction T using Multiset.induction_on with
  | empty => simp
  | @cons a T ih =>
      rw [Multiset.card_cons, succ_nsmul, Finset.mem_add]
      refine ⟨T.sum, ih ?_, a, hT a (by simp), ?_⟩
      · intro x hx
        exact hT x (by simp [hx])
      · simp [add_comm]

theorem isAddFreimanIso_of_injOn_iterated_sums
    {G H : Type*} [AddCommMonoid G] [AddCommMonoid H] [DecidableEq G] [DecidableEq H]
    (f : G →+ H) (A : Finset G) (s : ℕ) (hinj : Set.InjOn f (A : Set G))
    (hsinj : Set.InjOn f (s • A : Finset G)) :
    IsAddFreimanIso s (A : Set G) (A.image f : Set H) f := by
  refine ⟨⟨?_, hinj, ?_⟩, ?_⟩
  · intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · intro y hy
    exact Finset.mem_image.mp hy
  · intro T U hT hU hTc hUc
    rw [← map_multiset_sum, ← map_multiset_sum]
    have hTs : T.sum ∈ s • A := by
      simpa only [hTc] using multiset_sum_mem_iterated_sumset A (fun x hx => hT hx)
    have hUs : U.sum ∈ s • A := by
      simpa only [hUc] using multiset_sum_mem_iterated_sumset A (fun x hx => hU hx)
    exact ⟨fun h => hsinj hTs hUs h, congrArg f⟩

theorem exists_integer_freiman_embedding {I : Type*} [Fintype I]
    (A : Finset (I → ℤ)) (s : ℕ) :
    ∃ f : (I → ℤ) →+ ℤ, IsAddFreimanIso s (A : Set _)
      (A.image f : Set ℤ) f := by
  classical
  obtain ⟨f, hf⟩ := exists_integer_vector_embedding (A ∪ s • A)
  refine ⟨f, isAddFreimanIso_of_injOn_iterated_sums f A s ?_ ?_⟩
  · exact hf.mono (fun _ hx => Finset.mem_union_left _ hx)
  · exact hf.mono (fun _ hx => Finset.mem_union_right _ hx)

end Erdos3.FreimanModel

end

end OAI
