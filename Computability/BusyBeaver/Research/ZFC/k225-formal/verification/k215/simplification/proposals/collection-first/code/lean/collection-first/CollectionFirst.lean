import Std

/-!
Standalone semantic core for the proposed collection-first quotient refactor.

`ImageCollection` and `CollectionInstance` have exactly the shape used by
BusyBeaver.ZFC.ProfileCollection at commit
6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95.  This file needs only Lean's Std.
It proves consequences of one explicitly supplied collection instance;
it does not postulate collection for every semantic predicate.
-/

namespace CollectionFirst

universe u
variable {V : Type u}

def ImageCollection (mem : V → V → Prop) (r : V → V → Prop)
    (a b : V) : Prop :=
  (∀ y, mem y b → ∃ x, r x y) ∧
  (∀ x, mem x a → (∃ y, r x y) → ∃ y, mem y b ∧ r x y)

def CollectionInstance (mem : V → V → Prop) (r : V → V → Prop) : Prop :=
  ∀ a, ∃ b, ImageCollection mem r a b

/-- A domain guard converts global support into support over `a`.
Partial functionality is required only on the domain. -/
theorem exact_image_of_collection (mem : V → V → Prop)
    (r : V → V → Prop) (a : V)
    (functional : ∀ x y z, mem x a → r x y → r x z → y = z)
    (collect : CollectionInstance mem (fun x y => mem x a ∧ r x y)) :
    ∃ b, ∀ y, mem y b ↔ ∃ x, mem x a ∧ r x y := by
  obtain ⟨b, support, cover⟩ := collect a
  refine ⟨b, fun y => ⟨?_, ?_⟩⟩
  · intro hy
    exact support y hy
  · rintro ⟨x, hxa, hxy⟩
    obtain ⟨z, hzb, _, hxz⟩ := cover x hxa ⟨y, hxa, hxy⟩
    exact (functional x z y hxa hxz hxy) ▸ hzb

/-- Separation is the exact image of the partial identity on `p`.
Again, only the displayed relation instance is assumed. -/
theorem separation_of_collection (mem : V → V → Prop)
    (p : V → Prop) (a : V)
    (collect : CollectionInstance mem
      (fun x y => mem x a ∧ (x = y ∧ p x))) :
    ∃ b, ∀ y, mem y b ↔ mem y a ∧ p y := by
  have functional : ∀ x y z, mem x a →
      (x = y ∧ p x) → (x = z ∧ p x) → y = z :=
    fun _ _ _ _ hxy hxz => hxy.1.symm.trans hxz.1
  obtain ⟨b, hb⟩ := exact_image_of_collection mem
    (fun x y => x = y ∧ p x) a functional collect
  refine ⟨b, fun y => (hb y).trans ⟨?_, ?_⟩⟩
  · rintro ⟨x, hxa, hxy, hp⟩
    exact hxy ▸ ⟨hxa, hp⟩
  · intro hy
    exact ⟨y, hy.1, rfl, hy.2⟩

#print axioms exact_image_of_collection
#print axioms separation_of_collection

end CollectionFirst
