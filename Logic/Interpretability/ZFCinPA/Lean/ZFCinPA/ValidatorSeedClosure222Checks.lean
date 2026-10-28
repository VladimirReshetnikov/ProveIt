import ZFCinPA.ValidatorSeedClosure222

set_option autoImplicit false
set_option Elab.async false

namespace LeanProofs.ZFCinPA.ValidatorSeedClosure222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorEind222
open ValidatorSeedWitness222 ValidatorSeedClosure222
open ArithmeticSeedTemplates222 (req clos)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem legal_zero_supported_seed :
    CProv (ex (0 : V) (conj (wal 1 (wim (wel 1 0) 0)) (req 1 0 0))) :=
  seed_supported_request 1 1 0 zero_ne_one zero_ne_one (vac_truth 1)

theorem zero_member_singleton_witness :
    ∃ code : V, ArithmeticHistory222.value code =
      ex (containerLabel 0) (singletonBody 0) + 1 := singleton_object_witness 0

/-- Literal numeric witnesses use the actual new checker, including p=0. -/
theorem concrete_empty_witness :
    ∃ code : Nat, ArithmeticHistory222.value code = ex 1 (wal 0 (neg (wel 0 1))) + 1 :=
  empty_object_witness

theorem concrete_singleton_witness :
    ∃ code : Nat, ArithmeticHistory222.value code =
      ex (containerLabel 0) (singletonBody 0) + 1 := singleton_object_witness 0

theorem concrete_c222_singleton :
    KCode222.C222 (ex (containerLabel 0) (singletonBody 0)) :=
  (cProv_nat_iff _).mp (singleton_object (0 : Nat))

#print axioms closure_support
#print axioms seed_supported_request
#print axioms empty_object
#print axioms Eind_symm
#print axioms seed_singleton
#print axioms singleton_object
#print axioms closed_singleton_object
#print axioms empty_object_witness
#print axioms singleton_object_witness
#print axioms legal_zero_supported_seed
#print axioms zero_member_singleton_witness
#print axioms concrete_empty_witness
#print axioms concrete_singleton_witness
#print axioms concrete_c222_singleton

end LeanProofs.ZFCinPA.ValidatorSeedClosure222Checks
