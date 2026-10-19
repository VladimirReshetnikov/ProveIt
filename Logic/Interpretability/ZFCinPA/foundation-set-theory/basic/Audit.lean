import Foundation.FirstOrder.SetTheory.Basic

namespace LO.FirstOrder.SetTheory

#print axioms LO.FirstOrder.SetTheory.z_subset_zf
#print axioms LO.FirstOrder.SetTheory.subset_refl

example : 𝗭 ⊆ 𝗭𝗙 := z_subset_zf

example {V : Type*} [SetStructure V] (x : V) : x ⊆ x := subset_refl x

end LO.FirstOrder.SetTheory
