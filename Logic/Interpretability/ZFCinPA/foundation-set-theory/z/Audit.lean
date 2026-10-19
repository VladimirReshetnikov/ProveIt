import Foundation.FirstOrder.SetTheory.Z

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭]

#print axioms LO.FirstOrder.SetTheory.mem_ext_iff
#print axioms LO.FirstOrder.SetTheory.empty_exists
#print axioms LO.FirstOrder.SetTheory.not_mem_empty
#print axioms LO.FirstOrder.SetTheory.pairing_exists
#print axioms LO.FirstOrder.SetTheory.union_exists
#print axioms LO.FirstOrder.SetTheory.power_exists
#print axioms LO.FirstOrder.SetTheory.separation_exists_eval
#print axioms LO.FirstOrder.SetTheory.empty_mem_ω
#print axioms LO.FirstOrder.SetTheory.ω_succ_closed
#print axioms LO.FirstOrder.SetTheory.mem_succ_iff
#print axioms LO.FirstOrder.SetTheory.naturalNumber_induction
#print axioms LO.FirstOrder.SetTheory.foundation

example {x y : V} : x = y ↔ ∀ z, z ∈ x ↔ z ∈ y := mem_ext_iff

example : ∃ e : V, IsEmpty e := empty_exists

example {x : V} : x ∉ (∅ : V) := not_mem_empty

example (x y : V) : ∃ z : V, ∀ w, w ∈ z ↔ w = x ∨ w = y :=
  pairing_exists x y

example (x : V) : ∃ y : V, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w := union_exists x

example (x : V) : ∃ y : V, ∀ z, z ∈ y ↔ z ⊆ x := power_exists x

example (x : V) (φ : SetTheorySemiformula V 1) :
    ∃ y : V, ∀ z : V, z ∈ y ↔ z ∈ x ∧ φ.Eval ![z] id :=
  separation_exists_eval x φ

example : ∅ ∈ (ω : V) := empty_mem_ω

example {x : V} (hx : x ∈ (ω : V)) : succ x ∈ (ω : V) := ω_succ_closed hx

example {x y : V} : y ∈ succ x ↔ y = x ∨ y ∈ x := mem_succ_iff

example (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (hzero : P 0) (hsucc : ∀ x ∈ (ω : V), P x → P (succ x)) :
    ∀ x ∈ (ω : V), P x := naturalNumber_induction P hP hzero hsucc

example (x : V) [IsNonempty x] : ∃ y ∈ x, ∀ z ∈ x, z ∉ y := foundation x

end LO.FirstOrder.SetTheory
