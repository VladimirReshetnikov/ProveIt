import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Defs

namespace OAI

section

namespace Erdos3

universe u v

inductive CoordinateDecisionTree (ι : Type u) (Value : ι → Type v) : Type (max u v)
  | leaf : CoordinateDecisionTree ι Value
  | split (i : ι) (children : Value i → CoordinateDecisionTree ι Value) : CoordinateDecisionTree ι Value

namespace CoordinateDecisionTree

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

inductive Valid (Good : Finset ι → (∀ i, Value i) → Prop) :
    Finset ι → (∀ i, Value i) → CoordinateDecisionTree ι Value → ℕ → Prop
  | leaf {I : Finset ι} {x : ∀ i, Value i} {d : ℕ} (good : Good I x) : Valid Good I x .leaf d
  | split {I : Finset ι} {x : ∀ i, Value i} {i : ι}
      {children : Value i → CoordinateDecisionTree ι Value} {d : ℕ}
      (fresh : i ∉ I)
      (branches : ∀ value, Valid Good (insert i I) (Function.update x i value) (children value) d) :
      Valid Good I x (.split i children) (d + 1)

theorem Valid.weaken {Good : Finset ι → (∀ i, Value i) → Prop}
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d : ℕ}
    (h : Valid Good I x tree d) (extra : ℕ) : Valid Good I x tree (d + extra) := by
  induction h with
  | leaf good => exact .leaf good
  | @split I x i children d fresh branches ih =>
    have hsum : d + 1 + extra = d + extra + 1 := by omega
    rw [hsum]
    exact .split fresh ih

theorem Valid.mono {Good : Finset ι → (∀ i, Value i) → Prop}
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d e : ℕ}
    (h : Valid Good I x tree d) (hde : d ≤ e) : Valid Good I x tree e := by
  have he : d + (e - d) = e := Nat.add_sub_of_le hde
  simpa only [he] using h.weaken (e - d)

end CoordinateDecisionTree

end Erdos3

end

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem Valid.congr_assignment {Good : Finset ι → (∀ i, Value i) → Prop}
    (hlocal : ∀ I x y, (∀ i ∈ I, x i = y i) → Good I x → Good I y)
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d : ℕ}
    (h : Valid Good I x tree d) (y : ∀ i, Value i) (hxy : ∀ i ∈ I, x i = y i) :
    Valid Good I y tree d := by
  induction h generalizing y with
  | leaf good => exact .leaf (hlocal _ _ _ hxy good)
  | @split I x i children d fresh branches ih =>
    apply Valid.split fresh
    intro value
    apply ih value (Function.update y i value)
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · simp only [Function.update_self]
    · have hji : j ≠ i := by intro heq; subst j; exact fresh hj
      simpa only [Function.update_of_ne hji] using hxy j hj

end Erdos3.CoordinateDecisionTree

end

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem Valid.preserve_subset {Good : Finset ι → (∀ i, Value i) → Prop}
    {I M : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d : ℕ}
    (h : Valid Good I x tree d) (hMI : M ⊆ I) :
    Valid (fun J y => M ⊆ J ∧ Good J y) I x tree d := by
  revert hMI
  induction h with
  | leaf good => intro hMI; exact .leaf ⟨hMI, good⟩
  | @split I x i children d fresh branches ih =>
    intro hMI
    exact .split fresh (fun value => ih value (hMI.trans (Finset.subset_insert i I)))

end Erdos3.CoordinateDecisionTree

end

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

def trace : CoordinateDecisionTree ι Value → Finset ι → (∀ i, Value i) → (∀ i, Value i) →
    Finset ι × (∀ i, Value i)
  | .leaf, I, x, _ => (I, x)
  | .split i children, I, x, input =>
    trace (children (input i)) (insert i I) (Function.update x i (input i)) input

theorem trace_contains (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (x input : ∀ i, Value i) : I ⊆ (trace tree I x input).1 := by
  induction tree generalizing I x with
  | leaf => exact Finset.Subset.refl I
  | split i children ih =>
    exact (Finset.subset_insert i I).trans (ih (input i) (insert i I) (Function.update x i (input i)))

theorem trace_agrees (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (x input : ∀ i, Value i) (hagree : ∀ i ∈ I, x i = input i) :
    ∀ i ∈ (trace tree I x input).1, (trace tree I x input).2 i = input i := by
  induction tree generalizing I x with
  | leaf => exact hagree
  | split i children ih =>
    apply ih (input i) (insert i I) (Function.update x i (input i))
    intro j hj
    by_cases hji : j = i
    · subst j
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne hji]
      exact hagree j (Finset.mem_of_mem_insert_of_ne hj hji)

theorem Valid.trace_good {Good : Finset ι → (∀ i, Value i) → Prop}
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d : ℕ}
    (h : Valid Good I x tree d) (input : ∀ i, Value i) :
    Good (trace tree I x input).1 (trace tree I x input).2 := by
  induction h generalizing input with
  | leaf good => exact good
  | @split I x i children d fresh branches ih => exact ih (input i) input

theorem Valid.trace_card_le {Good : Finset ι → (∀ i, Value i) → Prop}
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d : ℕ}
    (h : Valid Good I x tree d) (input : ∀ i, Value i) :
    (trace tree I x input).1.card ≤ I.card + d := by
  induction h generalizing input with
  | leaf good => simp only [trace]; omega
  | @split I x i children d fresh branches ih =>
    have hchild := ih (input i) input
    have hcard := Finset.card_insert_of_notMem fresh
    change (trace (children (input i)) (insert i I) (Function.update x i (input i)) input).1.card ≤ _
    omega

end Erdos3.CoordinateDecisionTree

end

end OAI
