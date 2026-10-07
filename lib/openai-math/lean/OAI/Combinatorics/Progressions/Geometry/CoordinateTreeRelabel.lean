import OAI.Combinatorics.Progressions.Linear.RankedCoordinateDecisionTree

namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v w

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v} {Other : ι → Type w}

def relabelAssignment (e : ∀ i, Value i ≃ Other i) (x : ∀ i, Value i) : ∀ i, Other i :=
  fun i => e i (x i)

theorem relabelAssignment_update (e : ∀ i, Value i ≃ Other i)
    (x : ∀ i, Value i) (i : ι) (v : Value i) :
    relabelAssignment e (Function.update x i v) =
      Function.update (relabelAssignment e x) i (e i v) := by
  funext j
  by_cases h : j = i
  · subst j; simp only [relabelAssignment, Function.update_self]
  · simp only [relabelAssignment, Function.update_of_ne h]

omit [DecidableEq ι] in
theorem relabelAssignment_inverse (e : ∀ i, Value i ≃ Other i) (x : ∀ i, Value i) :
    relabelAssignment (fun i => (e i).symm) (relabelAssignment e x) = x := by
  funext i
  exact (e i).symm_apply_apply (x i)

def relabel (e : ∀ i, Value i ≃ Other i) :
    CoordinateDecisionTree ι Value → CoordinateDecisionTree ι Other
  | .leaf => .leaf
  | .split i children => .split i (fun v => relabel e (children ((e i).symm v)))

theorem Valid.relabel {Good : Finset ι → (∀ i, Value i) → Prop}
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d : ℕ}
    (h : Valid Good I x tree d) (e : ∀ i, Value i ≃ Other i) :
    Valid (fun J y => Good J (relabelAssignment (fun i => (e i).symm) y))
      I (relabelAssignment e x) (tree.relabel e) d := by
  induction h with
  | leaf good =>
    exact .leaf (by simpa only [relabelAssignment_inverse] using good)
  | @split I x i children d fresh branches ih =>
    apply Valid.split fresh
    intro v
    simpa only [relabelAssignment_update, Equiv.apply_symm_apply] using ih ((e i).symm v)

end Erdos3.CoordinateDecisionTree

end

end OAI
