import OAI.Combinatorics.Progressions.Results.Basic

namespace OAI

section

namespace Erdos3

variable {N : ℕ}

noncomputable def finitePatternRepresentative (r : Setoid (Fin N)) (i : Fin N) : Fin N := by
  classical
  exact (Finset.univ.filter (fun j => r i j)).min'
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, r.refl' i⟩⟩

theorem finitePatternRepresentative_related (r : Setoid (Fin N)) (i : Fin N) :
    r i (finitePatternRepresentative r i) := by
  classical
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).2

theorem finitePatternRepresentative_le (r : Setoid (Fin N)) (i j : Fin N) (h : r i j) :
    finitePatternRepresentative r i ≤ j := by
  classical
  exact Finset.min'_le _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)

theorem finitePatternRepresentative_eq_iff (r : Setoid (Fin N)) (i j : Fin N) :
    finitePatternRepresentative r i = finitePatternRepresentative r j ↔ r i j := by
  constructor
  · intro h
    have hi := finitePatternRepresentative_related r i
    have hj := finitePatternRepresentative_related r j
    rw [h] at hi
    exact r.trans' hi (r.symm' hj)
  · intro h
    apply le_antisymm
    · exact finitePatternRepresentative_le r i _ (r.trans' h (finitePatternRepresentative_related r j))
    · exact finitePatternRepresentative_le r j _ (r.trans' (r.symm' h) (finitePatternRepresentative_related r i))

theorem finitePatternRepresentative_injective :
    Function.Injective (finitePatternRepresentative (N := N)) := by
  intro r s h
  apply Setoid.ext
  intro i j
  rw [← finitePatternRepresentative_eq_iff r i j, ← finitePatternRepresentative_eq_iff s i j]
  rw [congrFun h i, congrFun h j]

theorem finiteEqualityPatterns_card_le (P : Finset (Setoid (Fin N))) : P.card ≤ N ^ N := by
  classical
  calc
    P.card = (P.image finitePatternRepresentative).card :=
      (Finset.card_image_of_injective P finitePatternRepresentative_injective).symm
    _ ≤ Fintype.card (Fin N → Fin N) := Finset.card_le_univ _
    _ = N ^ N := by simp only [Fintype.card_fun, Fintype.card_fin]

end Erdos3

end

section

namespace Erdos3

variable {S : Type*} [Fintype S]

theorem finiteEqualityPatterns_card_le_card (P : Finset (Setoid S)) :
    P.card ≤ Fintype.card S ^ Fintype.card S := by
  classical
  let e := (Fintype.equivFin S).symm
  calc
    P.card = (P.image (Setoid.comap e)).card :=
      (Finset.card_image_of_injective P (Setoid.comap_injective e e.surjective)).symm
    _ ≤ Fintype.card S ^ Fintype.card S := finiteEqualityPatterns_card_le _

end Erdos3

end

end OAI
