import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Generated Boolean algebras by membership atoms

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/05_algebraic.tex`, Theorem A17
(`thm:boolean-atoms`), for coded subsets `E₀, …, E_{s−1}` of `Fin n`: "define `x ≡ y` when their `s` membership
bits agree. The nonempty equivalence classes are the atoms of the generated Boolean algebra. The generated
algebra is exactly the collection of unions of these atoms; if there are `a` atoms, it has `2^a` members, with
`a ≤ min(n, 2^s)`."

* `word`, `atom`: the membership word of a point and its class; `mem_atom_self`, `atom_eq_iff`;
* `gen_union`: every generator is the union of the atoms of its points; `compl_union`: the complement of a union
  of atoms is a union of atoms (so unions of atoms form a Boolean algebra, with finite unions trivially);
* `atom_mem`: every Boolean family containing `univ` and the generators and closed under `∩` and complement
  contains every atom (an atom is `⋂_i (E_i or its complement)`), so the unions of atoms are the least
  algebra;
* `atoms_le_n`, `atoms_le_pow`: `a ≤ n` and `a ≤ 2^s`;
* `card_unions`: distinct sets of atoms have distinct unions, so the algebra has `2^a` members;
* A18 ("bounded and stabilization-certified unions"): `union_unions` (finite unions of members are members) and
  `stabilized_union` (with a supplied stabilization property the finite union represents the unbounded union).
-/

namespace LeanProofs.IPRA.Topology.BooleanAtoms

variable {n s : ℕ} (E : Fin s → Finset (Fin n))

/-- The membership word of `x`. -/
def word (x : Fin n) : Fin s → Bool := fun i => decide (x ∈ E i)

/-- The class of `x`. -/
def atom (x : Fin n) : Finset (Fin n) := Finset.univ.filter fun y => word E y = word E x

/-- The set of atoms. -/
def atoms : Finset (Finset (Fin n)) := Finset.univ.image (atom E)

theorem mem_atom_self (x : Fin n) : x ∈ atom E x := by simp [atom]

theorem mem_atom {x y : Fin n} : y ∈ atom E x ↔ word E y = word E x := by simp [atom]

theorem atom_eq_iff {x y : Fin n} : atom E x = atom E y ↔ word E x = word E y := by
  constructor
  · intro h
    have : x ∈ atom E y := h ▸ mem_atom_self E x
    exact (mem_atom E).mp this
  · intro h
    ext z
    simp only [mem_atom, h]

/-- Every generator is the union of the atoms of its points. -/
theorem gen_union (i : Fin s) : E i = (E i).biUnion (atom E) := by
  ext y
  simp only [Finset.mem_biUnion]
  constructor
  · intro hy
    exact ⟨y, hy, mem_atom_self E y⟩
  · rintro ⟨x, hx, hyx⟩
    have hw := congrFun ((mem_atom E).mp hyx) i
    simp only [word, decide_eq_decide] at hw
    exact hw.mpr hx

/-- The complement of a union of atoms is a union of atoms. -/
theorem compl_union (S : Finset (Fin n)) :
    Finset.univ \ S.biUnion (atom E) = (Finset.univ \ S.biUnion (atom E)).biUnion (atom E) := by
  ext y
  simp only [Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · intro hy
    exact ⟨y, hy, mem_atom_self E y⟩
  · rintro ⟨x, hx, hyx⟩ ⟨z, hz, hyz⟩
    apply hx
    refine ⟨z, hz, ?_⟩
    rw [mem_atom] at hyx hyz ⊢
    exact hyx.symm.trans hyz

/-- The atom of `x` as a finite intersection of generators and complements. -/
theorem atom_eq_inter (x : Fin n) :
    atom E x = Finset.univ.filter fun y => ∀ i, (y ∈ E i ↔ x ∈ E i) := by
  ext y
  simp only [mem_atom, Finset.mem_filter, Finset.mem_univ, true_and, word, funext_iff, decide_eq_decide]

/-- Every Boolean family containing `univ` and the generators contains every atom. -/
theorem atom_mem (B : Finset (Finset (Fin n))) (huniv : Finset.univ ∈ B) (hgen : ∀ i, E i ∈ B)
    (hinter : ∀ U ∈ B, ∀ V ∈ B, U ∩ V ∈ B) (hcompl : ∀ U ∈ B, Finset.univ \ U ∈ B) (x : Fin n) :
    atom E x ∈ B := by
  classical
  -- `⋂_{i ∈ I} (E_i or its complement)` lies in `B` for every finite index set `I`
  have key : ∀ I : Finset (Fin s),
      (Finset.univ.filter fun y => ∀ i ∈ I, (y ∈ E i ↔ x ∈ E i)) ∈ B := by
    intro I
    induction I using Finset.induction_on with
    | empty => simpa using huniv
    | insert j I hj ih =>
      have hside : (Finset.univ.filter fun y => (y ∈ E j ↔ x ∈ E j)) ∈ B := by
        by_cases hx : x ∈ E j
        · have : (Finset.univ.filter fun y => (y ∈ E j ↔ x ∈ E j)) = E j := by
            ext y; simp [hx]
          rw [this]; exact hgen j
        · have : (Finset.univ.filter fun y => (y ∈ E j ↔ x ∈ E j)) = Finset.univ \ E j := by
            ext y; simp [hx]
          rw [this]; exact hcompl _ (hgen j)
      have e : (Finset.univ.filter fun y => ∀ i ∈ insert j I, (y ∈ E i ↔ x ∈ E i)) =
          (Finset.univ.filter fun y => (y ∈ E j ↔ x ∈ E j)) ∩
            Finset.univ.filter fun y => ∀ i ∈ I, (y ∈ E i ↔ x ∈ E i) := by
        ext y; simp [Finset.mem_insert]
      rw [e]
      exact hinter _ hside _ ih
  have := key Finset.univ
  rw [atom_eq_inter]
  simpa using this

/-- `a ≤ n`. -/
theorem atoms_le_n : (atoms E).card ≤ n := by
  calc (atoms E).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
    _ = n := Finset.card_fin n

/-- `a ≤ 2^s`: an atom depends only on the membership word. -/
theorem atoms_le_pow : (atoms E).card ≤ 2 ^ s := by
  classical
  have hsub : atoms E ⊆ (Finset.univ : Finset (Fin s → Bool)).image
      (fun w => Finset.univ.filter fun y => word E y = w) := by
    intro A hA
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hA
    exact Finset.mem_image.mpr ⟨word E x, Finset.mem_univ _, rfl⟩
  calc (atoms E).card
      ≤ ((Finset.univ : Finset (Fin s → Bool)).image fun w => Finset.univ.filter fun y => word E y = w).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin s → Bool)).card := Finset.card_image_le
    _ = 2 ^ s := by simp [Finset.card_univ, Fintype.card_pi]

theorem atom_of_mem {S : Finset (Finset (Fin n))} (hS : S ⊆ atoms E) {A : Finset (Fin n)} (hA : A ∈ S) :
    ∃ x, atom E x = A := by
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp (hS hA)
  exact ⟨x, hx⟩

/-- If a point lies in the union of a set of atoms, its own atom belongs to that set. -/
theorem atom_mem_of_mem_sup {S : Finset (Finset (Fin n))} (hS : S ⊆ atoms E) {x : Fin n}
    (hx : x ∈ S.sup id) : atom E x ∈ S := by
  obtain ⟨B, hB, hxB⟩ := Finset.mem_sup.mp hx
  obtain ⟨y, rfl⟩ := atom_of_mem E hS hB
  have : atom E x = atom E y := (atom_eq_iff E).mpr ((mem_atom E).mp hxB)
  rw [this]; exact hB

/-- Distinct sets of atoms have distinct unions, so the algebra has `2^a` members. -/
theorem card_unions :
    ((atoms E).powerset.image fun S => S.sup id).card = 2 ^ (atoms E).card := by
  classical
  rw [Finset.card_image_of_injOn, Finset.card_powerset]
  intro S hS S' hS' h
  rw [Finset.mem_coe, Finset.mem_powerset] at hS hS'
  simp only at h
  ext A
  constructor
  · intro hA
    obtain ⟨x, rfl⟩ := atom_of_mem E hS hA
    have hx : x ∈ S.sup id := Finset.mem_sup.mpr ⟨atom E x, hA, mem_atom_self E x⟩
    rw [h] at hx
    exact atom_mem_of_mem_sup E hS' hx
  · intro hA
    obtain ⟨x, rfl⟩ := atom_of_mem E hS' hA
    have hx : x ∈ S'.sup id := Finset.mem_sup.mpr ⟨atom E x, hA, mem_atom_self E x⟩
    rw [← h] at hx
    exact atom_mem_of_mem_sup E hS hx

/-! ## A18: bounded and stabilization-certified unions -/

/-- Unions of atoms are closed under finite unions (bitwise disjunction of masks). -/
theorem union_unions (S S' : Finset (Finset (Fin n))) : (S ∪ S').sup id = S.sup id ∪ S'.sup id :=
  Finset.sup_union

/-- A18: under the supplied stabilization property `E(t) ⊆ ⋃_{i<T} E(i)` for all `t`, the finite union
represents the unbounded union predicate `x ↦ ∃ t, x ∈ E(t)`. -/
theorem stabilized_union (F : ℕ → Finset (Fin n)) (T : ℕ) (h : ∀ t, F t ⊆ (Finset.range T).biUnion F)
    (x : Fin n) : (∃ t, x ∈ F t) ↔ x ∈ (Finset.range T).biUnion F := by
  constructor
  · rintro ⟨t, ht⟩
    exact h t ht
  · intro hx
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hx
    exact ⟨i, hi⟩

end LeanProofs.IPRA.Topology.BooleanAtoms
