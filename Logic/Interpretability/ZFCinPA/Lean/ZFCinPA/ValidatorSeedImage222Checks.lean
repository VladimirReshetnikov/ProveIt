import ZFCinPA.ValidatorSeedImage222

set_option autoImplicit false
set_option Elab.async false

namespace LeanProofs.ZFCinPA.ValidatorSeedImage222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorSeedImage222
open ArithmeticSeedTemplates222 (req clos)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem legal_diagonal_zero_seed : CProv (ex (0 : V) (imageBody 1 1 0 0)) :=
  seed_image 1 1 0 zero_ne_one zero_ne_one

theorem arbitrary_matrix_with_coincident_binders (p : V) :
    CProv (wim (clos p p p p)
      (wal p (wim (wel p p) (ex p p)))) := closure_support_exists p p p p

theorem coverage_has_free_input (a b k p : V) :
    coverage a b k p = wal b (wim (wel b k)
      (wim (wal k (wim (wel k a) (wel k b))) (req b k p))) := rfl

theorem zero_matrix_internal_witness :
    ∃ code : V, ArithmeticHistory222.value code =
      ex (pad 0) (imageBody 1 3 (pad 0) 0) + 1 := matrix_image_witness 0

theorem concrete_zero_matrix_witness :
    ∃ code : Nat, ArithmeticHistory222.value code =
      ex (pad 0) (imageBody 1 3 (pad 0) 0) + 1 := matrix_image_witness 0

theorem concrete_actual_c222 (p : Nat) :
    KCode222.C222 (ex (pad p) (imageBody 1 3 (pad p) p)) :=
  (cProv_nat_iff _).mp (matrix_image p)

#print axioms closure_support_exists
#print axioms closure_coverage
#print axioms pair_image
#print axioms seed_image
#print axioms request_congr
#print axioms closure_congr
#print axioms pad_gt_three
#print axioms matrix_image
#print axioms matrix_image_witness
#print axioms legal_diagonal_zero_seed
#print axioms arbitrary_matrix_with_coincident_binders
#print axioms zero_matrix_internal_witness
#print axioms concrete_zero_matrix_witness
#print axioms concrete_actual_c222

end LeanProofs.ZFCinPA.ValidatorSeedImage222Checks
