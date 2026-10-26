import ZFCinPA.ValidatorEind222

set_option autoImplicit false
set_option Elab.async false

namespace LeanProofs.ZFCinPA.ValidatorEind222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorEind222

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem legal_zero_binder : Vac (0 : V) (Eind 1 1) :=
  Eind_vac 1 1 0 zero_ne_one zero_ne_one

/-- This is the auxiliary-binder collision branch, not the direct vacuity
branch: aux(0,0)=1. Equal input labels remain legal. -/
theorem legal_auxiliary_collision : Vac (1 : V) (Eind 0 0) :=
  Eind_vac 0 0 1 _root_.one_ne_zero _root_.one_ne_zero

theorem alpha_same_binder (v a b : V) (ha : v ≠ a) (hb : v ≠ b) :
    CProv (wim (Ev v a b) (Ev v a b)) := ev_alpha v v a b ha hb ha hb

theorem literal_auxiliary_collision : aux (0 : V) 0 = 1 := by simp [aux]

theorem actual_vacuity_witness (a b c : V) (ha : c ≠ a) (hb : c ≠ b) :
    ∃ code : V, ArithmeticHistory222.value code = wim (Eind a b) (wal c (Eind a b)) + 1 :=
  Eind_vac a b c ha hb

theorem actual_existence_witness (a b : V) :
    ∃ code : V, ArithmeticHistory222.value code = ex a (Eind a b) + 1 := Eind_ex a b

#print axioms eq_symm
#print axioms bin_spec
#print axioms bout_spec
#print axioms ev_alpha
#print axioms Eq_Eind
#print axioms Eind_ex
#print axioms Eind_el_l
#print axioms Eind_el_r
#print axioms Eind_euclid
#print axioms Eind_vac
#print axioms legal_zero_binder
#print axioms legal_auxiliary_collision
#print axioms actual_vacuity_witness
#print axioms actual_existence_witness

end LeanProofs.ZFCinPA.ValidatorEind222Checks
