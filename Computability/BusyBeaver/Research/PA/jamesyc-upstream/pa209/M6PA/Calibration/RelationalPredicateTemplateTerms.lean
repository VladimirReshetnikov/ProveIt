module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateSyntax
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def termValue {n : Nat} : Term n → V → V → V
  | .bvar i,b,_ => nth b (i:Nat)
  | .fvar i,_,f => nth f i
  | .func fn _,_,_ => nomatch fn
end M6.PA.RelationalPredicateTemplate
