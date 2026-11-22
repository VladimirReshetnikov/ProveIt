import Graph

/-! Exact three-colour triangle Ramsey number. The lower colouring encodes
`F₂⁵ / ⟨11111⟩` by giving its representatives with last coordinate zero.
For the upper bound we choose six neighbours having the same colour from a
pivot, then use the constructive two-colour theorem in `Graph.lean`. -/

namespace Ramsey.ThreeColors

private def decideExistsFin : (n : Nat) → (p : Fin n → Prop) →
    [DecidablePred p] → Decidable (∃ i, p i)
  | 0, _, _ => .isFalse (fun ⟨i, _⟩ => Fin.elim0 i)
  | n+1, p, _ =>
    letI : Decidable (∃ i : Fin n, p i.succ) := decideExistsFin n (fun i => p i.succ)
    decidable_of_iff _ Fin.exists_fin_succ.symm

local instance {n : Nat} (p : Fin n → Prop) [DecidablePred p] : Decidable (∃ i, p i) :=
  decideExistsFin n p

/-- Coloured unordered pairs are read at their increasing representatives. -/
def HasTriangle {n : Nat} (c : Fin n → Fin n → Fin 3) : Prop :=
  ∃ x y z, x < y ∧ y < z ∧ c x y = c x z ∧ c x z = c y z

private theorem boolWitnessOfClique {c : Fin 6 → Fin 6 → Bool} {d : Bool}
    (h : Graph.Clique c (List.finRange 6) d 3) :
    ∃ x y z, x < y ∧ y < z ∧ c x y = c x z ∧ c x z = c y z := by
  have sorted : h.vertices.Pairwise (· < ·) :=
    (by decide : (List.finRange 6).Pairwise (· < ·)).sublist h.inside
  have size := h.size_eq
  have mono := h.mono
  generalize h.vertices = vs at sorted size mono
  cases vs with
  | nil => simp_all
  | cons x xs =>
    cases xs with
    | nil => simp_all
    | cons y ys =>
      cases ys with
      | nil => simp_all
      | cons z zs =>
        simp only [List.pairwise_cons, List.mem_cons] at sorted mono
        have cxy := mono.1 y (.inl rfl)
        have cxz := mono.1 z (.inr (.inl rfl))
        have cyz := mono.2.1 z (.inl rfl)
        exact ⟨x, y, z, sorted.1 y (.inl rfl), sorted.2.1 z (.inl rfl),
          cxy.trans cxz.symm, cxz.trans cyz.symm⟩

private theorem boolWitness (c : Fin 6 → Fin 6 → Bool) :
    ∃ x y z, x < y ∧ y < z ∧ c x y = c x z ∧ c x z = c y z := by
  cases Graph.triangleOnSix c with
  | inl h => exact boolWitnessOfClique h
  | inr h => exact boolWitnessOfClique h

private def fiber {α : Type} (f : α → Fin 3) (d : Fin 3) (xs : List α) :=
  xs.filter (fun x => f x == d)

private theorem partitionLength {α : Type} (f : α → Fin 3) (xs : List α) :
    (fiber f 0 xs).length + (fiber f 1 xs).length + (fiber f 2 xs).length = xs.length := by
  have three : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases three (f x) with hx | hx | hx <;>
      simp [fiber, hx, List.filter] at * <;> omega

private theorem largeFiber {α : Type} (f : α → Fin 3) (xs : List α) (h : xs.length = 16) :
    ∃ d, 6 ≤ (fiber f d xs).length := by
  have partition := partitionLength f xs
  by_cases h0 : 6 ≤ (fiber f 0 xs).length
  · exact ⟨0, h0⟩
  by_cases h1 : 6 ≤ (fiber f 1 xs).length
  · exact ⟨1, h1⟩
  exact ⟨2, by omega⟩

private def binary (omitted t : Fin 3) : Bool := t.val == (omitted.val + 1) % 3

private theorem binary_injective : ∀ d u v : Fin 3,
    u ≠ d → v ≠ d → binary d u = binary d v → u = v := by decide

/-- The upper bound in R(3,3,3)=17. Every search here has a finite decidable domain. -/
theorem triangleOnSeventeen (c : Fin 17 → Fin 17 → Fin 3) : HasTriangle c := by
  let others := (List.finRange 17).tail
  have sorted : others.Pairwise (· < ·) := by decide
  have pos : ∀ x : Fin 17, x ∈ others → 0 < x := by decide
  obtain ⟨d, enough⟩ := largeFiber (c 0) others (by decide)
  let xs := fiber (c 0) d others
  have hi (i : Fin 6) : i.val < xs.length := by have := i.isLt; change 6 ≤ xs.length at enough; omega
  let f (i : Fin 6) := xs[i.val]'(hi i)
  have sortedXs : xs.Pairwise (· < ·) := sorted.sublist List.filter_sublist
  have f_lt (i j : Fin 6) (hij : i < j) : f i < f j :=
    List.pairwise_iff_getElem.mp sortedXs i.val j.val (hi i) (hi j) hij
  have f_mem (i : Fin 6) : f i ∈ xs := List.getElem_mem (hi i)
  have f_color (i : Fin 6) : c 0 (f i) = d := by simpa using (List.mem_filter.mp (f_mem i)).2
  have f_pos (i : Fin 6) : 0 < f i := pos (f i) (List.mem_filter.mp (f_mem i)).1
  by_cases found : ∃ i j : Fin 6, i < j ∧ c (f i) (f j) = d
  · obtain ⟨i, j, hij, h⟩ := found
    exact ⟨0, f i, f j, f_pos i, f_lt i j hij, (f_color i).trans (f_color j).symm,
      (f_color j).trans h.symm⟩
  · have avoid (i j : Fin 6) (hij : i < j) : c (f i) (f j) ≠ d :=
      fun h => found ⟨i, j, hij, h⟩
    obtain ⟨i, j, k, hij, hjk, h1, h2⟩ := boolWitness (fun u v => binary d (c (f u) (f v)))
    have hik : i < k := Nat.lt_trans hij hjk
    exact ⟨f i, f j, f k, f_lt i j hij, f_lt j k hjk,
      binary_injective d _ _ (avoid i j hij) (avoid i k hik) h1,
      binary_injective d _ _ (avoid i k hik) (avoid j k hjk) h2⟩

/-- The five singleton and five side classes in the quotient. All remaining
nonzero differences are diagonal classes; the diagonal of the table is unused. -/
def sixteenColor (x y : Fin 16) : Fin 3 :=
  match Nat.xor x.val y.val with
  | 1 | 2 | 4 | 8 | 15 => 0
  | 3 | 6 | 7 | 12 | 14 => 1
  | _ => 2

set_option maxHeartbeats 2000000 in
/-- The lower bound, checked by ordinary Lean-kernel computation. -/
theorem sixteen_obstruction : ¬ HasTriangle sixteenColor := by
  unfold HasTriangle
  decide

end Ramsey.ThreeColors
