import P79NaturalForcedW
import FactorResidues74
import DiophantineConsistency.ModelDifferenceRing

/-! Source-only proposal: extracting factor units from a 79 zero when w=0.
All source drafts, imported providers and proofs are unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.Natural79ZeroWUnitsDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveFactorUnits2011
open FactorResidues74Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem pairEval_mul {σ : Type*} (e f : Expr σ) (v : σ → V) :
    pairEval (e*f) v=multiply (pairEval e v) (pairEval f v) := rfl

private theorem one_of_zero {σ : Type*} (e : Expr σ) (v : σ → V)
    (hz : InternalZero (e-1) v) : Equivalent (pairEval e v) (natural (1:V)) := by
  apply equivalent_one.mpr
  change (Expr.sub e (Expr.constant 1)).splitNatural.1.evalSemiring v =
    (Expr.sub e (Expr.constant 1)).splitNatural.2.evalSemiring v at hz
  simpa [Expr.splitNatural,NatExpr.evalSemiring,pairEval] using hz

private theorem swap_last (p q r s t : Pair V) :
    product5 p q r s t=product5 p q r t s := by
  apply Prod.ext <;> simp only [product5,multiply] <;> ring

/-- A literal 79 zero gives its five signed factors' product equal to one. -/
theorem product_of_zero (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hz : InternalZero (P79NaturalForcedW.graph p).output v) :
    Equivalent (product5 (pairEval (P79NaturalForcedW.graph p).first v)
      (pairEval (P79NaturalForcedW.graph p).main v)
      (pairEval (P79NaturalForcedW.graph p).aux v)
      (pairEval (P79NaturalForcedW.graph p).guardFactor v)
      (pairEval (P79NaturalForcedW.graph p).strong v)) (natural (1:V)) := by
  rw [P79NaturalForcedW.output_shape] at hz
  have h := one_of_zero _ v hz
  rw [pairEval_mul,pairEval_mul,pairEval_mul,pairEval_mul] at h
  change Equivalent (product5 (pairEval (P79NaturalForcedW.graph p).first v)
    (pairEval (P79NaturalForcedW.graph p).main v)
    (pairEval (P79NaturalForcedW.graph p).aux v)
    (pairEval (P79NaturalForcedW.graph p).strong v)
    (pairEval (P79NaturalForcedW.graph p).guardFactor v)) (natural (1:V)) at h
  rw [swap_last] at h
  exact h

/-- At w=0 the first ring factor is the square of r, for arbitrary ports. -/
theorem first_eval_at_w_zero (p : Fin 4 → ℤ) (v : Fin 14 → V) (hw : v 6=0) :
    (P79NaturalForcedW.graph p).first.evalRing (fun j => ι (v j)) =
      ι (v 8)*ι (v 8) := by
  simp [P79NaturalForcedW.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    hw,map_zero]

/-- A nonnegative ring evaluation cannot be the negative signed unit. -/
theorem nonnegative_not_negative_unit {σ : Type*} (e : Expr σ) (v : σ → V)
    (he : 0 ≤ e.evalRing (fun j => ι (v j))) :
    (pairEval e v).1+1 ≠ (pairEval e v).2 := by
  intro hneg
  have hmap := congrArg (ι : V →+* DiffRing V) hneg
  simp only [map_add,map_one] at hmap
  have hs := split_evalRing e (fun j => ι (v j))
  rw [← evalSemiring_map ι,← evalSemiring_map ι] at hs
  change ι (pairEval e v).1-ι (pairEval e v).2 = e.evalRing (fun j => ι (v j)) at hs
  linarith

/-- Literal 79 unit extraction at w=0. The three modulo-four exclusion
premises are explicit; no positive w, beta, J, gamma or port assumption. -/
theorem units_of_zero_w_zero (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hz : InternalZero (P79NaturalForcedW.graph p).output v) (hw : v 6=0)
    (hmain : pairResidue (pairEval (P79NaturalForcedW.graph p).main v) ≠ -1)
    (haux : pairResidue (pairEval (P79NaturalForcedW.graph p).aux v) ≠ -1)
    (hstrong : pairResidue (pairEval (P79NaturalForcedW.graph p).strong v) ≠ -1) :
    (pairEval (P79NaturalForcedW.graph p).first v).1=(pairEval (P79NaturalForcedW.graph p).first v).2+1 ∧
    (pairEval (P79NaturalForcedW.graph p).main v).1=(pairEval (P79NaturalForcedW.graph p).main v).2+1 ∧
    (pairEval (P79NaturalForcedW.graph p).aux v).1=(pairEval (P79NaturalForcedW.graph p).aux v).2+1 ∧
    (pairEval (P79NaturalForcedW.graph p).guardFactor v).1=(pairEval (P79NaturalForcedW.graph p).guardFactor v).2+1 ∧
    (pairEval (P79NaturalForcedW.graph p).strong v).1=(pairEval (P79NaturalForcedW.graph p).strong v).2+1 := by
  have hn : 0 ≤ (P79NaturalForcedW.graph p).first.evalRing (fun j => ι (v j)) := by
    rw [first_eval_at_w_zero p v hw]
    exact mul_self_nonneg _
  exact product5_positive (product_of_zero p v hz)
    (nonnegative_not_negative_unit _ v hn)
    (fun h => hmain (negative_residue h))
    (fun h => haux (negative_residue h))
    (fun h => hstrong (negative_residue h))

/-- Explicit expression-pattern bindings allow reuse of the three existing
residue lemmas; establishing these bindings for graph 79 remains separate. -/
theorem restricted_residues_of_shapes (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (u a c d y z f i : Expr (Fin 14))
    (hm : (P79NaturalForcedW.graph p).main=mainPattern u a c d)
    (ha : (P79NaturalForcedW.graph p).aux=auxPattern y z a f)
    (hs : (P79NaturalForcedW.graph p).strong=strongPattern i a f) :
    pairResidue (pairEval (P79NaturalForcedW.graph p).main v) ≠ -1 ∧
    pairResidue (pairEval (P79NaturalForcedW.graph p).aux v) ≠ -1 ∧
    pairResidue (pairEval (P79NaturalForcedW.graph p).strong v) ≠ -1 := by
  rw [hm,ha,hs]
  exact ⟨main_ne _ _ _ _ v,aux_ne _ _ _ _ v,strong_ne _ _ _ v⟩

end DiophantineConsistency.Natural79ZeroWUnitsDraft

#print axioms DiophantineConsistency.Natural79ZeroWUnitsDraft.first_eval_at_w_zero
#print axioms DiophantineConsistency.Natural79ZeroWUnitsDraft.units_of_zero_w_zero
#print axioms DiophantineConsistency.Natural79ZeroWUnitsDraft.restricted_residues_of_shapes
