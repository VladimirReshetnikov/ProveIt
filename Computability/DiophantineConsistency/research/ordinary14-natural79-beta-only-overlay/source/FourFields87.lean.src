import FirstQuotient87

/-! Source-only extraction of the four non-guard 87 residuals. No 86
zero, guard equality, power calibration or Lean elaboration is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FourFields87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing DirectFirstRootModelDraft FirstFields86Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The two literal graphs have identical non-guard expressions. -/
theorem shared_fields (p : Fin 4 → ℤ) :
    (P87ShiftedGuard.graph p).A0=(P86ResidueGraph.graph p).A0 ∧
    (P87ShiftedGuard.graph p).A1=(P86ResidueGraph.graph p).A1 ∧
    (P87ShiftedGuard.graph p).aux=(P86ResidueGraph.graph p).aux ∧
    (P87ShiftedGuard.graph p).gap=(P86ResidueGraph.graph p).gap := by
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- The four shared residuals vanish at an 87 own-zero. This is not an
86 zero, whose distinct guard remains unconstrained by these four facts. -/
theorem fields_of_zero (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    eval (P86ResidueGraph.graph p).A0 v=0 ∧
    eval (P86ResidueGraph.graph p).A1 v=0 ∧
    eval (P86ResidueGraph.graph p).aux v-1=0 ∧
    eval (P86ResidueGraph.graph p).gap v=0 := by
  rw [internalZero_iff,P87ShiftedGuard.output_shape] at hz
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one] at hz
  have hfive : fiveSquares (eval (P87ShiftedGuard.graph p).A0 v)
      (eval (P87ShiftedGuard.graph p).A1 v) (eval (P87ShiftedGuard.graph p).aux v-1)
      (eval (P87ShiftedGuard.graph p).gap v) (eval (P87ShiftedGuard.graph p).guardResidual v)=0 := by
    simpa only [fiveSquares,eval] using hz
  have hf := (fiveSquares_eq_zero_iff _ _ _ _ _).mp hfive
  have hs := shared_fields p
  rw [hs.1,hs.2.1,hs.2.2.1,hs.2.2.2] at hf
  exact ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1⟩

end DiophantineConsistency.FourFields87Draft

#print axioms DiophantineConsistency.FourFields87Draft.fields_of_zero
