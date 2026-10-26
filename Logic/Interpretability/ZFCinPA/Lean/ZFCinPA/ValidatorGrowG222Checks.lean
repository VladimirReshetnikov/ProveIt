import ZFCinPA.ValidatorGrowG222

set_option autoImplicit false
set_option Elab.async false

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCode254 ArithmeticTemplates222
open LeanProofs.ZFCinPA.ValidatorProvability254
open LeanProofs.ZFCinPA.ValidatorGrowG222

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (a b c : V) : CProv (growG a b c) := cProv_growG a b c

-- Equal variable labels are legal, including equality with c.
example (a : V) : CProv (growG a a a) := cProv_growG a a a

-- The chosen binder need not be fresh for c.
example (a b : V) : CProv (growG a b (wel a b)) := cProv_growG a b (wel a b)

example : CProv (growG (0 : V) 0 0) := cProv_growG 0 0 0

example (a b c : V) : ∃ d : V, ArithmeticHistory254.value d =
    wim (weq c a) (wim (weq c b) (wal (wel a b) (weq a b))) + 1 :=
  exists_growG_code a b c
end

example (a b c : Nat) : growG a b c = KCode222.growG a b c := growG_nat a b c
example (a b c : Nat) : Code254.C254 (KCode222.growG a b c) := c254_growG a b c

example : HierarchySymbol.DefinedFunction₃ (V := Nat) 𝚺₀
    KCode222.growG growGDef := codeGrowG_defined

#print axioms growG_eq
#print axioms growG_defined
#print axioms growG_nat
#print axioms codeGrowG_defined
#print axioms wel_gt_left
#print axioms wel_gt_right
#print axioms cProv_growG_literal
#print axioms cProv_growG
#print axioms exists_growG_code
#print axioms c254_growG
