import P88FourSquareGraph
import DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011
import DiophantineConsistency.Compact44.FreeJ13

/-! Source-only same-valuation binding from the 13-parent four-square zero
to existing Fin13 adaptive scaled norms. No adaptive expression zero,
Lean elaboration, quotient or endpoint is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.ParentScaledNormsDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs ArithmeticSignedPairExpressions
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveScaledNorms2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The two first factors differ from the parent residuals only by the unit
and the distributive form of the folded first root. -/
theorem first_factor_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    ((factors p).1).evalRing v=1+(P88FourSquare.graph p).A0.evalRing v := by
  simp [factors,P88FourSquare.graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat] <;> ring

theorem main_factor_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    ((factors p).2.1).evalRing v=1+(P88FourSquare.graph p).A1.evalRing v := by
  simp [factors,P88FourSquare.graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat] <;> ring

/-- The parent own zero supplies both natural adaptive scaled norms at the
same valuation and natural port tuple. -/
theorem scaled_norms (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hz : InternalZero (P88FourSquare.graph (fun j => (p j : ℤ))).output v) : ScaledNorms p v := by
  let pi : Fin 4 → ℤ := fun j => (p j : ℤ)
  let w : Fin 13 → DiffRing V := fun j => ι (v j)
  have hz' := (internalZero_iff _ _).mp hz
  rw [P88FourSquare.output_shape] at hz'
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one] at hz'
  change ((P88FourSquare.graph pi).A0.evalRing w*(P88FourSquare.graph pi).A0.evalRing w+
    (P88FourSquare.graph pi).A1.evalRing w*(P88FourSquare.graph pi).A1.evalRing w)+
    (((P88FourSquare.graph pi).aux.evalRing w-1)*((P88FourSquare.graph pi).aux.evalRing w-1)+
      (P88FourSquare.graph pi).gap.evalRing w*(P88FourSquare.graph pi).gap.evalRing w)=0 at hz'
  have h0 : (P88FourSquare.graph pi).A0.evalRing w=0 := mul_self_eq_zero.mp (by
    have ha := mul_self_nonneg ((P88FourSquare.graph pi).A0.evalRing w)
    have hb := mul_self_nonneg ((P88FourSquare.graph pi).A1.evalRing w)
    have hc := mul_self_nonneg ((P88FourSquare.graph pi).aux.evalRing w-1)
    have hd := mul_self_nonneg ((P88FourSquare.graph pi).gap.evalRing w)
    linarith)
  have h1 : (P88FourSquare.graph pi).A1.evalRing w=0 := mul_self_eq_zero.mp (by
    have ha := mul_self_nonneg ((P88FourSquare.graph pi).A0.evalRing w)
    have hb := mul_self_nonneg ((P88FourSquare.graph pi).A1.evalRing w)
    have hc := mul_self_nonneg ((P88FourSquare.graph pi).aux.evalRing w-1)
    have hd := mul_self_nonneg ((P88FourSquare.graph pi).gap.evalRing w)
    linarith)
  have hu0 : (pairEval (factors pi).1 v).1=(pairEval (factors pi).1 v).2+1 := by
    apply (FreeJ13.unit_iff_one _ _).mpr
    rw [first_factor_eval pi w,h0,add_zero]
  have hu1 : (pairEval (factors pi).2.1 v).1=(pairEval (factors pi).2.1 v).2+1 := by
    apply (FreeJ13.unit_iff_one _ _).mpr
    rw [main_factor_eval pi w,h1,add_zero]
  rw [first_shape pi] at hu0
  rw [main_shape pi] at hu1
  have hn0 := unit_square_norm _ _ v hu0
  have hn1 := unit_square_norm _ _ v hu1
  rw [first_rhs_pair p v] at hn0
  rw [main_rhs_pair p v] at hn1
  simpa only [ScaledNorms,pi,Prod.fst,Prod.snd,add_zero] using And.intro hn0 hn1

end DiophantineConsistency.ParentScaledNormsDraft

#print axioms DiophantineConsistency.ParentScaledNormsDraft.scaled_norms
