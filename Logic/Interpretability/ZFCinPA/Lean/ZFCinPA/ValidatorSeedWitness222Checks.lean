import ZFCinPA.ValidatorSeedWitness222

set_option autoImplicit false
set_option Elab.async false

namespace LeanProofs.ZFCinPA.ValidatorSeedWitness222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorEind222
open ValidatorSeedWitness222
open ArithmeticSeedTemplates222 (req clos)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem legal_zero_diagonal_seed :
    CProv (ex (0 : V) (conj (clos 1 1 0 0) (req 1 0 0))) :=
  seed_pair 1 1 0 zero_ne_one zero_ne_one

theorem legal_zero_diagonal_seed_witness :
    ∃ code : V, ArithmeticHistory222.value code =
      ex 0 (conj (clos 1 1 0 0) (req 1 0 0)) + 1 := legal_zero_diagonal_seed

theorem zero_member_container_witness :
    ∃ code : V, ArithmeticHistory222.value code =
      ex (containerLabel 0) (wel 0 (containerLabel 0)) + 1 :=
  membership_container_witness 0

/-- This uses the actual new Nat checker, not the old C254 calculus. -/
theorem concrete_nat_container_witness :
    ∃ code : Nat, ArithmeticHistory222.value code =
      ex (containerLabel 0) (wel 0 (containerLabel 0)) + 1 :=
  membership_container_witness 0

theorem zero_label_fresh : (1 : V) < containerLabel 0 ∧ (0 : V) < containerLabel 0 := by
  simpa only [zero_add] using (containerLabel_bounds (0 : V))

#print axioms not_all_imp_ex_conj
#print axioms seed_pair
#print axioms seed_request
#print axioms request_eind_member
#print axioms eind_gt_arguments
#print axioms membership_container
#print axioms closed_membership_container
#print axioms membership_container_witness
#print axioms legal_zero_diagonal_seed_witness
#print axioms zero_member_container_witness
#print axioms concrete_nat_container_witness

end LeanProofs.ZFCinPA.ValidatorSeedWitness222Checks
