import Ring78To75
import FirstRootBridge

/-! Source-only same-coordinate forward zero transfer. Literal graph and
five-square dependencies remain unelaborated; no converse is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.Model78To75Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing DirectFirstRootModelDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Any 78 zero yields a 75 zero at exactly the same model valuation and
integer ports. This direction needs no positivity or fixed-port hypotheses. -/
theorem zero_of_78_zero (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hz : InternalZero (P78AuxRoot.graph p).output v) :
    InternalZero (P75NegativePell.graph p).output v := by
  rw [internalZero_iff,P78AuxRoot.output_shape] at hz
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one] at hz
  let w : Fin 14 → DiffRing V := fun j => ι (v j)
  have hfive : fiveSquares ((P78AuxRoot.graph p).A0.evalRing w)
      ((P78AuxRoot.graph p).A1.evalRing w) ((P78AuxRoot.graph p).aux.evalRing w-1)
      ((P78AuxRoot.graph p).gap.evalRing w) ((P78AuxRoot.graph p).guardResidual.evalRing w)=0 := by
    simpa only [fiveSquares,w] using hz
  rcases (fiveSquares_eq_zero_iff _ _ _ _ _).mp hfive with ⟨h0,h1,ha,hs,hg⟩
  have haux : (P78AuxRoot.graph p).aux.evalRing w=1 := sub_eq_zero.mp ha
  have hfactors := Ring78To75Draft.factor_evals p w
  rw [internalZero_iff,P75NegativePell.output_shape]
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one]
  change (P75NegativePell.graph p).first.evalRing w *
    (P75NegativePell.graph p).main.evalRing w *
    (P75NegativePell.graph p).aux.evalRing w *
    (P75NegativePell.graph p).strong.evalRing w *
    (P75NegativePell.graph p).guardFactor.evalRing w - 1 = 0
  rw [hfactors.1,hfactors.2.1,hfactors.2.2.1,hfactors.2.2.2.1,hfactors.2.2.2.2]
  simp [h0,h1,haux,hs,hg]

end DiophantineConsistency.Model78To75Draft

#print axioms DiophantineConsistency.Model78To75Draft.zero_of_78_zero
