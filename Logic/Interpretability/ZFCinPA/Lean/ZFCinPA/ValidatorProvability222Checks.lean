import ZFCinPA.ValidatorProvability222

set_option autoImplicit false
set_option Elab.async false

namespace LeanProofs.ZFCinPA.ValidatorProvability222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222

section Internal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (p : V) : cProvDef.val.Evalb ![p] ↔
    ∃ code : V, ArithmeticHistory222.value code = p + 1 := by
  simp [cProvDef]

example (a b : V) (hi : CProv (wim a b)) (ha : CProv a) : CProv b := cProv_mp hi ha
example (a p : V) (h : CProv p) : CProv (wal a p) := cProv_gen a h

example (a b c : V) :
    CProv (wim (weq c a) (wim (weq c b) (wal (wel a b) (weq a b)))) := by
  simpa only [ArithmeticTemplates222.growG_eq] using cProv_growG a b c

example (a c : V) (h : c ≠ a) : CProv (ArithmeticSeedTemplates222.bundle222 a a c) :=
  cProv_bundle a a c h h
example (a b : V) (ha : (0 : V) ≠ a) (hb : (0 : V) ≠ b) :
    CProv (ArithmeticSeedTemplates222.bundle222 a b 0) := cProv_bundle a b 0 ha hb

example (p : V) : CProv (wim 1 p) := cProv_ex_falso p
example : Kalmar.Classical (wim : V → V → V) 1 CProv := cProv_classical
end Internal

example (n : Nat) : CProv n ↔ KCode222.C222 n := cProv_nat_iff n

#print axioms cProv_defined
#print axioms cProv_mp
#print axioms cProv_gen
#print axioms cProv_growG
#print axioms cProv_bundle
#print axioms cProv_implicational
#print axioms cProv_composition
#print axioms cProv_ex_falso
#print axioms cProv_classical
#print axioms cProv_nat_iff

end LeanProofs.ZFCinPA.ValidatorProvability222Checks
