import BusyBeaver.ZFC.ArithmeticSeedTemplates222

set_option autoImplicit false
set_option Elab.async false

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCode254 ArithmeticSeedTemplates222

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

example (a b c : V) : bundle222 a b c =
    wim (wim (wim (wel a b) (wal c (wel a b)))
      (wal c (wim (clos a b c c) (wim (req b c c) 1)))) 1 := rfl

-- No a!=b gate is introduced; c is both matrix and private binder.
example (a c : V) : nks a a c =
    wal c (wim (clos a a c c) (wim (req a c c) 1)) := nks_eq a a c

example (a b : V) : nks a b 0 =
    wal 0 (wim (clos a b 0 0) (wim (req b 0 0) 1)) := nks_eq a b 0
end

example (a b c : Nat) : bundle222 a b c = KCode222.bundle222 a b c := bundle222_nat a b c

-- These are genuinely permitted inputs of the actual seed axiom's gate.
example : (0 : Nat) ≠ 1 ∧ (0 : Nat) ≠ 1 := by decide
example : KCode222.C222 (KCode222.bundle222 1 1 0) :=
  .bundle 1 1 0 (by decide) (by decide)

example : HierarchySymbol.DefinedFunction₃ (V := Nat) 𝚺₀
    KCode222.bundle222 bundleDef := codeBundle_defined

#print axioms req_eq
#print axioms clos_eq
#print axioms nks_eq
#print axioms vrel_eq
#print axioms bundle222_eq
#print axioms req_defined
#print axioms clos_defined
#print axioms nks_defined
#print axioms vrel_defined
#print axioms bundle_defined
#print axioms req_nat
#print axioms clos_nat
#print axioms nks_nat
#print axioms vrel_nat
#print axioms bundle222_nat
#print axioms codeBundle_defined
