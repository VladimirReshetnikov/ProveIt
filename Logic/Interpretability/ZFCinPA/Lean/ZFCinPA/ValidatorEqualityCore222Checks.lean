import ZFCinPA.ValidatorEqualityCore222

set_option autoImplicit false
set_option Elab.async false

namespace LeanProofs.ZFCinPA.ValidatorEqualityCore222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorEqualityCore222

section Internal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example : CProv (weq (0 : V) 0) := cProv_refl 0
example (a b : V) : CProv (wim (weq a b) (wal (wel a b) (weq a b))) :=
  cProv_helper a b
example (a b : V) : CProv (wim (wal (wel a b) (weq a b)) (weq a b)) :=
  cProv_eq_specialize a b
example (a b c : V) : CProv (wim (weq c a) (wim (weq c b) (weq a b))) := by
  change CProv (ArithmeticTemplates254.rho7 a b c)
  exact cProv_rho7 a b c
example (a : V) : CProv (ArithmeticTemplates254.rho7 a a 0) := cProv_rho7 a a 0

example (a b c : V) (ha : c ≠ a) (hb : c ≠ b) :
    CProv (wim (wel a b) (wal c (wel a b))) := by
  simpa only [ArithmeticSeedTemplates222.vrel_eq] using cProv_vrel a b c ha hb
example (a c : V) (h : c ≠ a) : CProv (ArithmeticSeedTemplates222.vrel a a c) :=
  cProv_vrel a a c h h
example (a b : V) (ha : (0 : V) ≠ a) (hb : (0 : V) ≠ b) :
    CProv (ArithmeticSeedTemplates222.vrel a b 0) := cProv_vrel a b 0 ha hb
end Internal

/-- Only the already checked Nat binding is used here, not the old Nat proof. -/
example (a b c : Nat) : KCode222.C222 (Code254.rho7 a b c) := by
  have h := (cProv_nat_iff (ArithmeticTemplates254.rho7 a b c)).mp (cProv_rho7 a b c)
  simpa only [ArithmeticTemplates254.rho7_nat] using h

#print axioms contrapose
#print axioms all_ex
#print axioms ex_mono
#print axioms cProv_refl
#print axioms cProv_helper
#print axioms cProv_eq_specialize
#print axioms cProv_rho7
#print axioms cProv_vrel

end LeanProofs.ZFCinPA.ValidatorEqualityCore222Checks
