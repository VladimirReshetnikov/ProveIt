import ZFCinPA.NativeTheory

set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.NativeSet

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA
open SetTheory.BusyBeaver.ZFC

#print axioms LeanProofs.ZFCinPA.NativeSet.nativeFixed_delta1
#print axioms LeanProofs.ZFCinPA.NativeSet.nativeTheory_delta1
#print axioms LeanProofs.ZFCinPA.NativeSet.models_containerAx
#print axioms LeanProofs.ZFCinPA.NativeSet.models_irAx
#print axioms LeanProofs.ZFCinPA.NativeSet.models_gic
#print axioms LeanProofs.ZFCinPA.NativeSet.sat_of_models_toSet
#print axioms LeanProofs.ZFCinPA.NativeSet.containers
#print axioms LeanProofs.ZFCinPA.NativeSet.irreflexive
#print axioms LeanProofs.ZFCinPA.NativeSet.collection
#print axioms LeanProofs.ZFCinPA.NativeSet.models_cpgic

example : nativeFixed.Δ₁ := nativeFixed_delta1

example : nativeTheory.Δ₁ := nativeTheory_delta1

example : 𝗘𝗤 ℒₛₑₜ ⪯ nativeTheory := inferInstance

section Semantics
variable {M : Type} [Nonempty M] [SetStructure M] [M↓[ℒₛₑₜ] ⊧* nativeTheory]

example : M↓[ℒₛₑₜ] ⊧ containerAx := models_containerAx

example : M↓[ℒₛₑₜ] ⊧ irAx := models_irAx

example (ψ : SetTheorySemiproposition 2) :
    M↓[ℒₛₑₜ] ⊧ (gicBodyMeta ψ).univCl := models_gic ψ

example (φ : SetTheory.Form) (h : M↓[ℒₛₑₜ] ⊧ (toSet 0 φ).univCl)
    (e : ℕ → M) : SetTheory.Sat (memRel M) e φ :=
  sat_of_models_toSet φ h e

example : ProfileCollection.Containers (memRel M) := containers

example (x : M) : ¬ x ∈ x := irreflexive x

example (phi : SetTheory.Form) (env : ℕ → M) :
    ProfileCollection.CollectionInstance (memRel M)
      (DeepPositiveClosure.MatrixRelation (memRel M) phi env) :=
  collection phi env

example : ProfileModel.ModelsCPGIC (memRel M) ∧ ∀ x : M, ¬ x ∈ x :=
  models_cpgic
end Semantics

end LeanProofs.ZFCinPA.NativeSet
