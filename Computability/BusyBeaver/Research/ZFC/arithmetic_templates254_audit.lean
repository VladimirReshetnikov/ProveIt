import BusyBeaver.ZFC.ArithmeticTemplates254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticTemplates254

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.bounded_tagged_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.Circuit.defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.Circuit.eval_im
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.Circuit.eval_el
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.Circuit.eval_al
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.Circuit.eval_eq
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.Circuit.eval_input0
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.Circuit.eval_input1
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.Circuit.eval_input2
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.Circuit.eval_input3
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.Circuit.eval_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.rho2_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.rho2_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.codeRho2_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.rho3_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.rho3_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.codeRho3_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.rho4_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.rho4_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.codeRho4_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.rho5_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.rho5_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.codeRho5_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.rho6_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.rho6_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.codeRho6_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.rho7_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.rho7_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.codeRho7_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.rho8_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.rho8_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.codeRho8_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.bundleC_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.bundleC_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.codeBundleC_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.bundleG_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.bundleG_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.codeBundleG_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.bundle_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.bundle_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.codeBundle_defined

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
example (e : Circuit) : 𝚺₀-Function₄[V] e.eval via e.graph := inferInstance
example (k a b r : V) :
    (a ≤ r ∧ b ≤ r ∧ r = ArithmeticCode254.tagged k a b) ↔
      r = ArithmeticCode254.tagged k a b := bounded_tagged_iff k a b r
example : 𝚺₀-Function₃[V] rho2 via rho2Def := inferInstance
example : 𝚺₀-Function₃[V] rho3 via rho3Def := inferInstance
example : 𝚺₀-Function₃[V] rho4 via rho4Def := inferInstance
example : 𝚺₀-Function₃[V] rho5 via rho5Def := inferInstance
example : 𝚺₀-Function₂[V] rho6 via rho6Def := inferInstance
example : 𝚺₀-Function₃[V] rho7 via rho7Def := inferInstance
example : 𝚺₀-Function₄[V] rho8 via rho8Def := inferInstance
example : 𝚺₀-Function₃[V] bundleC via bundleCDef := inferInstance
example : 𝚺₀-Function₃[V] bundleG via bundleGDef := inferInstance
example : 𝚺₀-Function₃[V] bundle via bundleDef := inferInstance
end

example (a b c : Nat) : rho2 a b c = Code254.rho2 a b c := rho2_nat a b c
example : HierarchySymbol.DefinedFunction₃ (V := Nat) 𝚺₀ Code254.rho2 rho2Def := inferInstance
example (a b c : Nat) : rho3 a b c = Code254.rho3 a b c := rho3_nat a b c
example : HierarchySymbol.DefinedFunction₃ (V := Nat) 𝚺₀ Code254.rho3 rho3Def := inferInstance
example (a b c : Nat) : rho4 a b c = Code254.rho4 a b c := rho4_nat a b c
example : HierarchySymbol.DefinedFunction₃ (V := Nat) 𝚺₀ Code254.rho4 rho4Def := inferInstance
example (a b c : Nat) : rho5 a b c = Code254.rho5 a b c := rho5_nat a b c
example : HierarchySymbol.DefinedFunction₃ (V := Nat) 𝚺₀ Code254.rho5 rho5Def := inferInstance
example (a b : Nat) : rho6 a b = Code254.rho6 a b := rho6_nat a b
example : HierarchySymbol.DefinedFunction₂ (V := Nat) 𝚺₀ Code254.rho6 rho6Def := inferInstance
example (a b c : Nat) : rho7 a b c = Code254.rho7 a b c := rho7_nat a b c
example : HierarchySymbol.DefinedFunction₃ (V := Nat) 𝚺₀ Code254.rho7 rho7Def := inferInstance
example (a b c u : Nat) : rho8 a b c u = Code254.rho8 a b c u := rho8_nat a b c u
example : HierarchySymbol.DefinedFunction₄ (V := Nat) 𝚺₀ Code254.rho8 rho8Def := inferInstance
example (a b c : Nat) : bundleC a b c = Code254.bundleC a b c := bundleC_nat a b c
example : HierarchySymbol.DefinedFunction₃ (V := Nat) 𝚺₀ Code254.bundleC bundleCDef := inferInstance
example (a b c : Nat) : bundleG a b c = Code254.bundleG a b c := bundleG_nat a b c
example : HierarchySymbol.DefinedFunction₃ (V := Nat) 𝚺₀ Code254.bundleG bundleGDef := inferInstance
example (a b c : Nat) : bundle a b c = Code254.bundle a b c := bundle_nat a b c
example : HierarchySymbol.DefinedFunction₃ (V := Nat) 𝚺₀ Code254.bundle bundleDef := inferInstance

-- The cyclic truth alias and coincident labels remain legal numeric inputs.
example : (Circuit.im Circuit.input0 Circuit.input0).eval (0 : Nat) 0 0 0 = 0 := by
  simp [ArithmeticCode254.wim_nat, Code254.wim, Code254.P,
    SetTheory.Cantor.toNat, SetTheory.Cantor.tri]
example : rho6 (0 : Nat) 0 = Code254.rho6 0 0 := rho6_nat 0 0
example : bundle (0 : Nat) 0 0 = Code254.bundle 0 0 0 := bundle_nat 0 0 0
example : bundle (1 : Nat) 1 1 = Code254.bundle 1 1 1 := bundle_nat 1 1 1
