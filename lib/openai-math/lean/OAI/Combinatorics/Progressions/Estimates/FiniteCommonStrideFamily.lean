import OAI.Combinatorics.Progressions.Geometry.CommonStrideCoordinates

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def finiteCommonStrideFamily {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) (C : I → Finset (Finset ℤ)) : Finset (Finset (I → ℤ)) :=
  (Finset.univ : Finset (Fin M × (I → Fin M))).biUnion (fun q =>
    (Fintype.piFinset C).image (fun S => Fintype.piFinset (fun i =>
      (S i).image (fun x => ((q.2 i).val : ℤ) + (q.1.val + 1 : ℕ) * x))))

theorem finiteCommonStrideFamily_card {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) (C : I → Finset (Finset ℤ)) :
    (finiteCommonStrideFamily M C).card ≤ M ^ (Fintype.card I + 1) * ∏ i, (C i).card := by
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _q : Fin M × (I → Fin M), (Fintype.piFinset C).card :=
      Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
    _ = _ := by simp [Fintype.card_piFinset, pow_succ, mul_assoc, mul_comm]

theorem mem_finiteCommonStrideFamily {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) (C : I → Finset (Finset ℤ)) {m : ℕ} (hm : 0 < m) (hmM : m ≤ M)
    (r : I → ℕ) (hr : ∀ i, r i < M) (S : I → Finset ℤ) (hS : ∀ i, S i ∈ C i) :
    Fintype.piFinset (fun i => (S i).image (fun x => (r i : ℤ) + m * x)) ∈
      finiteCommonStrideFamily M C := by
  apply Finset.mem_biUnion.mpr
  refine ⟨(⟨m - 1, by omega⟩, fun i => ⟨r i, hr i⟩), Finset.mem_univ _, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨S, Fintype.mem_piFinset.mpr hS, by simp only [Nat.sub_add_cancel hm]⟩

theorem finiteCommonStrideFamily_shape {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) (C : I → Finset (Finset ℤ))
    (hshape : ∀ i S, S ∈ C i → ∃ a b : ℕ, S = Finset.Ico (a : ℤ) (b : ℤ))
    {A : Finset (I → ℤ)} (hA : A ∈ finiteCommonStrideFamily M C) :
    ∃ (c : I → ℤ) (m : ℕ) (H : I → ℕ), 0 < m ∧ m ≤ M ∧ A = commonStrideBox c m H := by
  obtain ⟨q, _, hq⟩ := Finset.mem_biUnion.mp hA
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hq
  choose a b hab using fun i => hshape i (S i) (Fintype.mem_piFinset.mp hS i)
  refine ⟨(fun i => ((q.2 i).val : ℤ) + (q.1.val + 1 : ℕ) * a i), q.1.val + 1,
    (fun i => b i - a i), by omega, by omega, ?_⟩
  congr 1
  funext i
  rw [hab i, affine_interval_eq_progression]

end Erdos3

end

end OAI
