import Natural79ConcreteUnits
import DiophantineConsistency.ModelDifferenceRing

/-! Source-only: under w=0 derive J>0 from the literal 79 guard unit.
This module, its imports, model argument and tactics are unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.Natural79ZeroWJPosDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open ArithmeticAdaptiveFactorMagnitude2011 Natural79ConcreteUnitsDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The positive signed unit gives ring value one. -/
theorem eval_one_of_pair_unit {σ : Type*} (e : Expr σ) (v : σ → V)
    (hu : (pairEval e v).1=(pairEval e v).2+1) :
    e.evalRing (fun j => ι (v j))=1 := by
  have hu' := congrArg (ι : V →+* DiffRing V) hu
  simp only [map_add,map_one] at hu'
  have he := split_evalRing e (fun j => ι (v j))
  rw [← evalSemiring_map ι, ← evalSemiring_map ι] at he
  change ι (pairEval e v).1-ι (pairEval e v).2 = e.evalRing (fun j => ι (v j)) at he
  linarith

/-- At J=w=0 the guard uses only a represented nonnegative K0 port.
The integer beta, MC and MF ports are arbitrary in this algebraic cut. -/
theorem guard_zero_cut (p : Fin 4 → ℤ) (K : V) (v : Fin 14 → V)
    (hK : (p 1 : DiffRing V)=ι K) (hJ : v 0=0) (hw : v 6=0) :
    (P79NaturalForcedW.graph p).guardFactor.evalRing (fun j => ι (v j)) =
      -(ι (v 1)+ι (v 2)+1)*ι K-ι (v 1) := by
  simp [P79NaturalForcedW.graph, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant,
    Expr.evalRing_ofNat, hK, hJ, hw, map_zero] <;> ring

/-- At a 79 zero with w=0, the unshifted J coordinate is positive.
No strict K0, beta, gamma, or w-positivity hypothesis is assumed. -/
theorem J_pos_of_zero_w_zero (p : Fin 4 → ℤ) (K : V) (v : Fin 14 → V)
    (hK : (p 1 : DiffRing V)=ι K)
    (hz : InternalZero (P79NaturalForcedW.graph p).output v) (hw : v 6=0) :
    0 < v 0 := by
  apply pos_iff_ne_zero.mpr
  intro hJ
  have units := Natural79ConcreteUnitsDraft.units_of_zero_w_zero p v hz hw
  have hone : (P79NaturalForcedW.graph p).guardFactor.evalRing (fun j => ι (v j))=1 :=
    eval_one_of_pair_unit _ v units.2.2.2.1
  rw [guard_zero_cut p K v hK hJ hw] at hone
  have hF := ι_nonneg (v 1)
  have ha := ι_nonneg (v 2)
  have hK0 := ι_nonneg K
  have hm : 0 ≤ (ι (v 1)+ι (v 2)+1)*ι K :=
    mul_nonneg (by linarith) hK0
  linarith

end DiophantineConsistency.Natural79ZeroWJPosDraft

#print axioms DiophantineConsistency.Natural79ZeroWJPosDraft.guard_zero_cut
#print axioms DiophantineConsistency.Natural79ZeroWJPosDraft.J_pos_of_zero_w_zero
