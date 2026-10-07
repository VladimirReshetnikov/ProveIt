import OAI.Combinatorics.Progressions.Linear.RankedCoordinateDecisionTree

namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

def outsideAssignment (K : Finset ι) (base : ∀ i, Value i)
    (x : ∀ i : {i // i ∉ K}, Value i.val) : ∀ i, Value i :=
  fun i => if h : i ∈ K then base i else x ⟨i, h⟩

theorem outsideAssignment_update (K : Finset ι) (base : ∀ i, Value i)
    (x : ∀ i : {i // i ∉ K}, Value i.val) (i : {i // i ∉ K}) (v : Value i.val) :
    outsideAssignment K base (Function.update x i v) =
      Function.update (outsideAssignment K base x) i.val v := by
  funext j
  by_cases h : j = i.val
  · subst j
    simp only [outsideAssignment, i.property, dite_false, Function.update_self]
  · by_cases hj : j ∈ K
    · simp only [outsideAssignment, hj, dite_true, Function.update_of_ne h]
    · have hji : (⟨j, hj⟩ : {i // i ∉ K}) ≠ i := fun heq => h (congrArg Subtype.val heq)
      simp only [outsideAssignment, hj, dite_false, Function.update_of_ne h, Function.update_of_ne hji]

def liftOutside (K : Finset ι) :
    CoordinateDecisionTree {i // i ∉ K} (fun i => Value i.val) → CoordinateDecisionTree ι Value
  | .leaf => .leaf
  | .split i children => .split i.val (fun v => liftOutside K (children v))

theorem Valid.liftOutside (K : Finset ι) (base : ∀ i, Value i)
    {Good : Finset {i // i ∉ K} → (∀ i : {i // i ∉ K}, Value i.val) → Prop}
    {Better : Finset ι → (∀ i, Value i) → Prop}
    (transfer : ∀ J y, Good J y → Better (K ∪ J.image Subtype.val) (outsideAssignment K base y))
    {I : Finset {i // i ∉ K}} {x : ∀ i : {i // i ∉ K}, Value i.val}
    {tree : CoordinateDecisionTree {i // i ∉ K} (fun i => Value i.val)} {d : ℕ}
    (h : Valid Good I x tree d) :
    Valid Better (K ∪ I.image Subtype.val) (outsideAssignment K base x) (tree.liftOutside K) d := by
  classical
  induction h with
  | leaf good => exact .leaf (transfer _ _ good)
  | @split I x i children d fresh branches ih =>
    have hfresh : i.val ∉ K ∪ I.image Subtype.val := by
      simp only [Finset.mem_union, Finset.mem_image]
      rintro (hK | ⟨j, hj, heq⟩)
      · exact i.property hK
      · exact fresh ((Subtype.ext heq : j = i) ▸ hj)
    apply Valid.split hfresh
    intro v
    have hsets : K ∪ (insert i I).image Subtype.val = insert i.val (K ∪ I.image Subtype.val) := by
      ext j
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert]
      aesop
    simpa only [hsets, outsideAssignment_update] using ih v

end Erdos3.CoordinateDecisionTree

end

end OAI
