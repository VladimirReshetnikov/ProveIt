import Foundation.FirstOrder.Arithmetic.HFS.PRF

/-! The graph of a primitive recursion with one fixed parameter. -/
set_option autoImplicit false
namespace DiophantineConsistency.ArithmeticUnaryRecursion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Specialize the general recursion graph to a single initial parameter. -/
theorem result_defined (b : PR.Blueprint 1) (c : PR.Construction V b) :
    𝚺₁-Function₂[V] (fun time initial => c.result ![initial] time) via b.resultDef :=
  .mk fun e => by
    have he : (fun i : Fin 1 => e i.succ.succ) = ![e 2] :=
      funext <| Fin.forall_fin_one.mpr rfl
    have h := c.result_defined.df e
    change b.resultDef.val.Evalb e ↔ e 0 = c.result (fun i : Fin 1 => e i.succ.succ) (e 1) at h
    rw [he] at h
    exact h

end DiophantineConsistency.ArithmeticUnaryRecursion
