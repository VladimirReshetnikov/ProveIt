import OAI.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder

namespace OAI

section

namespace Erdos3

variable {X : Type*} [Fintype X]

theorem freeWordSet_card_le (t : Finset (FreeMonoid X)) (s : ℕ)
    (ht : ∀ w ∈ t, w.length ≤ s) :
    t.card ≤ (s + 1) * (Fintype.card X + 1) ^ s := by
  classical
  let code : t → (Σ n : Fin (s + 1), Fin n.val → X) := fun w =>
    ⟨⟨w.val.toList.length, Nat.lt_succ_of_le (ht w w.property)⟩, w.val.toList.get⟩
  have hinj : Function.Injective code := by
    intro u v huv
    have hl := congrArg (fun z : Σ n : Fin (s + 1), Fin n.val → X => List.ofFn z.2) huv
    change List.ofFn u.val.toList.get = List.ofFn v.val.toList.get at hl
    rw [List.ofFn_get, List.ofFn_get] at hl
    exact Subtype.ext (congrArg FreeMonoid.ofList hl)
  have hcard := Fintype.card_le_of_injective code hinj
  simp only [Fintype.card_coe, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin] at hcard
  calc
    t.card ≤ ∑ n : Fin (s + 1), Fintype.card X ^ n.val := hcard
    _ ≤ ∑ _n : Fin (s + 1), (Fintype.card X + 1) ^ s := by
      apply Finset.sum_le_sum
      intro n _
      exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ n.isLt))
    _ = _ := by simp

theorem bchProductBracketSupport_card_le (s : ℕ) (xs : List X) :
    (bchProductBracketSupport s xs).card ≤ (s + 1) * (Fintype.card X + 1) ^ s := by
  classical
  let t := (bchProductBracketSupport s xs).image FreeSemigroup.toFreeMonoid
  have h := freeWordSet_card_le t s (by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    simpa only [freeSemigroup_toFreeMonoid_length] using bchProductBracketSupport_length s xs hv)
  simpa only [t, Finset.card_image_of_injective _ FreeSemigroup.toFreeMonoid_injective] using h

end Erdos3

end

section

namespace Erdos3

def BoundedFreeWord (X : Type*) (s : ℕ) := {w : FreeSemigroup X // w.length ≤ s}

variable {X : Type*} {s : ℕ}

def boundedFreeWordCode (w : BoundedFreeWord X s) : Σ n : Fin (s + 1), Fin n.val → X :=
  ⟨⟨w.val.toFreeMonoid.toList.length, by
      exact Nat.lt_succ_of_le ((freeSemigroup_toFreeMonoid_length w.val).le.trans w.property)⟩,
    w.val.toFreeMonoid.toList.get⟩

theorem boundedFreeWordCode_injective : Function.Injective (boundedFreeWordCode (X := X) (s := s)) := by
  intro u v huv
  have he := congrArg (fun z : Σ n : Fin (s + 1), Fin n.val → X => List.ofFn z.2) huv
  change List.ofFn u.val.toFreeMonoid.toList.get = List.ofFn v.val.toFreeMonoid.toList.get at he
  rw [List.ofFn_get, List.ofFn_get] at he
  apply Subtype.ext
  apply FreeSemigroup.toFreeMonoid_injective
  exact congrArg FreeMonoid.ofList he

noncomputable instance boundedFreeWordFintype [Fintype X] : Fintype (BoundedFreeWord X s) :=
  Fintype.ofInjective boundedFreeWordCode boundedFreeWordCode_injective

theorem boundedFreeWord_card_le [Fintype X] :
    Fintype.card (BoundedFreeWord X s) ≤ (s + 1) * (Fintype.card X + 1) ^ s := by
  have hc := Fintype.card_le_of_injective (boundedFreeWordCode (X := X) (s := s))
    boundedFreeWordCode_injective
  simp only [Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin] at hc
  calc
    _ ≤ ∑ n : Fin (s + 1), Fintype.card X ^ n.val := hc
    _ ≤ ∑ _n : Fin (s + 1), (Fintype.card X + 1) ^ s := by
      apply Finset.sum_le_sum
      intro n _
      exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ n.isLt))
    _ = _ := by simp

end Erdos3

end

end OAI
