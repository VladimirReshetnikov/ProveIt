import DiophantineConsistency.ArithmeticCommandCircuitPerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandCircuitPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254 ArithmeticTemplates254
open ArithmeticCommandCircuitPerm222 ArithmeticCommandBlockPerm222 ArithmeticCommandLeafPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (e : Circuit) : 𝚺₁-Function₄[V] e.eval via e.graph := Circuit.defined e
example (e : Circuit) (a b c u : V) : e.graph.val.Evalb ![e.eval a b c u,a,b,c,u] := by simp
example (a b c u : V) : (Circuit.sub .input0 .input3).eval a b c u=a-u := rfl
example (a b c u : V) : (Circuit.imp .input0 .input1).eval a b c u=wim a b := rfl
example (a b c u : V) : (Circuit.load .zero).eval a b c u=0 := by
  simp only [Circuit.eval,Jword_zero]
example (a b c u : V) : (Circuit.load .input3).eval a b c u=Jword u := rfl
example (a b c u : V) (hu : u≤a) :
    Contract ((Circuit.leaf 8 .input0 .input1 .input2 .input3).eval a b c u) (rho8 a b c u) := by
  rw [Circuit.eval_leaf]
  exact leaf8 a b c u hu
example (a b c u : V) :
    (Circuit.consAx .input2 .input0 .input1 .zero).eval a b c u=axWord c a b 0 :=
  Circuit.eval_consAx _ _ _ _ a b c u

#print axioms Circuit.defined
#print axioms Circuit.eval_consNip
#print axioms Circuit.eval_consDrop
#print axioms Circuit.eval_consMp
#print axioms Circuit.eval_consAx
#print axioms Circuit.eval_nips
#print axioms Circuit.eval_discard
#print axioms Circuit.eval_terminator
#print axioms Circuit.eval_leaf
end DiophantineConsistency.ArithmeticCommandCircuitPerm222Checks
