module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateBinaryReverse
public import M6PA.Calibration.NumericPAeqTermBinaryTemplates
public import M6PA.Calibration.RelationalClosedCertificateSupply
@[expose] public section
namespace M6.PA.RelationalPredicateBinary
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
noncomputable def domain : SF (V:=V) 1 := ⌜NumericPAeqTerm.domainTemplate⌝
noncomputable def addition : SF (V:=V) 3 := ⌜NumericPAeqTerm.additionTemplate⌝
noncomputable def multiplication : SF (V:=V) 3 := ⌜NumericPAeqTerm.multiplicationTemplate⌝

@[simp] theorem domain_quote {n : Nat} (x : FFL.FirstOrder.Semiterm L Nat n) :
    unary (domain (V:=V)) (⌜x⌝ : ST (V:=V) n)=⌜RelationalSource.Ordinal.domain x⌝ := by
  apply Bootstrapping.Semiformula.ext
  exact NumericPAeqTerm.domainCode_quote x
@[simp] theorem addition_quote {n : Nat} (x y z : FFL.FirstOrder.Semiterm L Nat n) :
    ternary (addition (V:=V)) (⌜x⌝ : ST (V:=V) n) ⌜y⌝ ⌜z⌝=⌜RelationalSource.PairGraph.addResult x y z⌝ := by
  apply Bootstrapping.Semiformula.ext
  exact NumericPAeqTerm.additionCode_quote x y z
@[simp] theorem multiplication_quote {n : Nat} (x y z : FFL.FirstOrder.Semiterm L Nat n) :
    ternary (multiplication (V:=V)) (⌜x⌝ : ST (V:=V) n) ⌜y⌝ ⌜z⌝=⌜RelationalSource.PairGraph.mulResult x y z⌝ := by
  apply Bootstrapping.Semiformula.ext
  exact NumericPAeqTerm.multiplicationCode_quote x y z

#print axioms domain_quote
#print axioms addition_quote
#print axioms multiplication_quote
end M6.PA.RelationalPredicateBinary

