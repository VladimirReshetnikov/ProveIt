import Foundation.FirstOrder.SetTheory.Basic.Model

namespace LO.FirstOrder.SetTheory

#print axioms LO.FirstOrder.SetTheory.subset_refl
#print axioms LO.FirstOrder.SetTheory.subset_trans
#print axioms LO.FirstOrder.SetTheory.not_isEmpty_iff_isNonempty
#print axioms LO.FirstOrder.SetTheory.val_isSucc_iff
#print axioms LO.FirstOrder.SetTheory.mk_mem_mk_iff_mem

example {V : Type*} [SetStructure V] (x : V) : x ⊆ x := subset_refl x

example {V : Type*} [SetStructure V] {x y z : V}
    (hxy : x ⊆ y) (hyz : y ⊆ z) : x ⊆ z := subset_trans hxy hyz

example {V : Type*} [SetStructure V] {x : V} :
    ¬IsEmpty x ↔ IsNonempty x := not_isEmpty_iff_isNonempty

example {V : Type*} [SetStructure V] {v : Fin 2 → V} :
    V ⊧/v isSucc ↔ ∀ z, z ∈ v 0 ↔ z = v 1 ∨ z ∈ v 1 := val_isSucc_iff

example {V : Type*} [SetStructure V] {U : Set V} {x y : V}
    {hx : x ∈ U} {hy : y ∈ U} :
    (⟨x, hx⟩ : U) ∈ (⟨y, hy⟩ : U) ↔ x ∈ y := mk_mem_mk_iff_mem

end LO.FirstOrder.SetTheory
