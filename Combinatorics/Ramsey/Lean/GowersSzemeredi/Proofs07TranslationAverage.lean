import GowersSzemeredi.Sections06_07

/-! Averaging translated finite sets retains their exact cardinality ratio;
no coordinate-grid rounding loss is needed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def translationFiber {G H : Type*} [Fintype G] [DecidableEq G]
    [AddCommGroup H] [DecidableEq H] (f : G → H) (A : Finset H) (z : H) : Finset G :=
  Finset.univ.filter fun x ↦ f x - z ∈ A

theorem translation_fiber_sum {G H : Type*}
    [Fintype G] [DecidableEq G] [AddCommGroup H] [Fintype H] [DecidableEq H]
    (f : G → H) (A : Finset H) :
    (∑ z : H, (translationFiber f A z).card) = Fintype.card G * A.card := by
  classical
  have hx (x : G) : (Finset.univ.filter fun z : H ↦ f x - z ∈ A).card = A.card := by
    apply Finset.card_bij (fun z _ ↦ f x - z)
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · intro z _ w _ hzw
      simpa using congrArg (fun v ↦ f x - v) hzw
    · intro y hy
      refine ⟨f x - y, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hy⟩
      · simp
  simp only [translationFiber, Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    _ = ∑ _x : G, A.card := by
      apply Finset.sum_congr rfl
      intro x _
      simpa only [Finset.card_filter] using hx x
    _ = _ := by simp

/-- There is a translate with at least the exact average number of preimages,
expressed without division so all small finite cases are retained. -/
theorem exists_translation_fiber_cross_bound {G H : Type*}
    [Fintype G] [DecidableEq G] [AddCommGroup H] [Fintype H] [DecidableEq H]
    (f : G → H) (A : Finset H) :
    ∃ z : H, Fintype.card G * A.card ≤ Fintype.card H * (translationFiber f A z).card := by
  classical
  have hs : (∑ _z : H, Fintype.card G * A.card) ≤
      ∑ z : H, Fintype.card H * (translationFiber f A z).card := by
    calc
      _ = Fintype.card H * (Fintype.card G * A.card) := by simp
      _ = Fintype.card H * (∑ z : H, (translationFiber f A z).card) := by
        rw [translation_fiber_sum]
      _ ≤ _ := by rw [Finset.mul_sum]
  obtain ⟨z, _, hz⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hs
  exact ⟨z, hz⟩

theorem finite_product_subset_card {X I : Type*} [Fintype X] [DecidableEq X]
    [Fintype I] [DecidableEq I] (A : Finset X) :
    (Finset.univ.filter fun z : I → X ↦ ∀ i, z i ∈ A).card = A.card ^ Fintype.card I := by
  classical
  let Q := Finset.univ.filter fun z : I → X ↦ ∀ i, z i ∈ A
  let e : {z : I → X // z ∈ Q} ≃ (I → {x : X // x ∈ A}) :=
    { toFun := fun z i ↦ ⟨z.val i, (Finset.mem_filter.mp z.property).2 i⟩
      invFun := fun z ↦ ⟨fun i ↦ (z i).val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i ↦ (z i).property⟩⟩
      left_inv := by intro z; apply Subtype.ext; rfl
      right_inv := by intro z; rfl }
  change Q.card = _
  rw [← Fintype.card_coe]
  exact (Fintype.card_congr e).trans (by simp)

end LeanProofs.GowersSzemeredi
