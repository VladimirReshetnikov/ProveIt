import DiophantineConsistency.GraphSizeBounds

/-! # Depth metadata for the fixed native enumerator

The formula blocks below are folded into natural-number depths. Their large
polynomial syntax trees are not evaluated in order to obtain these bounds.
-/

namespace DiophantineConsistency

namespace NativeFormulaSyntax

variable {σ : Type*}

@[simp] theorem implication_depth (a b : NatExpr σ) :
    (implication a b).depth = 4 + max a.depth b.depth := by
  change 1 + max (1 + max (1 + max 0 (1 + max a.depth b.depth))
    (1 + max (1 + max a.depth b.depth) 0)) (1 + max 0 b.depth) = _
  omega
@[simp] theorem membership_depth (a b : NatExpr σ) :
    (membership a b).depth = 5 + max a.depth b.depth := by
  change 1 + max (implication a b).depth 0 = _
  rw [implication_depth]; omega
@[simp] theorem universal_depth (a b : NatExpr σ) :
    (universal a b).depth = 5 + max a.depth b.depth := by
  change 1 + max (implication a b).depth 0 = _
  rw [implication_depth]; omega
@[simp] theorem equality_depth (a b : NatExpr σ) :
    (equality a b).depth = 5 + max a.depth b.depth := by
  change 1 + max (implication a b).depth 0 = _
  rw [implication_depth]; omega
@[simp] theorem negation_depth (a : NatExpr σ) :
    (negation a).depth = 4 + a.depth := by
  change (implication a 1).depth = _
  rw [implication_depth]
  change 4 + max a.depth 0 = _
  omega
@[simp] theorem existential_depth (a b : NatExpr σ) :
    (existential a b).depth = 9 + max a.depth (4 + b.depth) := by
  rw [existential, negation_depth, universal_depth, negation_depth]
  omega

end NativeFormulaSyntax

namespace NativeEnumerationSize

open Rep (Thin)

/-- One fixed allowance covers the formula rows and denominator-cleared stack. -/
abbrev allowance : ℕ := 512

theorem implicationCoordinates_depth : NativeFormulaGraphs.implicationCoordinates.depth ≤ allowance := by
  change (NativeFormulaSyntax.implication (.var (0 : Fin 2)) (.var 1)).directGraphRep.depth ≤ _
  rw [NatExpr.depth_directGraphRep, NativeFormulaSyntax.implication_depth]
  decide

private theorem bundle_expression : NativeFormulaGraphs.bundleCoordinates.expression =
    (NativeFormulaSyntax.bundle (.var (0 : Fin 3)) (.var 1) (.var 2)).directGraphRep.expression := rfl

theorem bundleCoordinates_depth : NativeFormulaGraphs.bundleCoordinates.depth ≤ 128 := by
  change NativeFormulaGraphs.bundleCoordinates.expression.depth ≤ 128
  rw [bundle_expression]
  change (NativeFormulaSyntax.bundle (.var (0 : Fin 3)) (.var 1) (.var 2)).directGraphRep.depth ≤ _
  rw [NatExpr.depth_directGraphRep]
  simp only [NativeFormulaSyntax.bundle, NativeFormulaSyntax.closure, NativeFormulaSyntax.request,
    NativeFormulaSyntax.implication_depth, NativeFormulaSyntax.universal_depth,
    NativeFormulaSyntax.negation_depth, NativeFormulaSyntax.membership_depth, NatExpr.depth]
  decide

theorem stackCoordinates_depth : NativeFormulaGraphs.stackCoordinates.depth ≤ allowance := by
  rw [NativeFormulaGraphs.stackCoordinates, ScaledNatural.depth_graphRep]
  simp only [NativeFormulaGraphs.stackScaled, ScaledNatural.depth_cantorPair,
    ScaledNatural.depth_ofNatExpr, NativeFormulaSyntax.row1, NativeFormulaSyntax.row2,
    NativeFormulaSyntax.row3, NativeFormulaSyntax.row4, NativeFormulaSyntax.row5,
    NativeFormulaSyntax.row6, NativeFormulaSyntax.growth, NativeFormulaSyntax.row8,
    NativeFormulaSyntax.implication_depth, NativeFormulaSyntax.universal_depth,
    NativeFormulaSyntax.equality_depth, NativeFormulaSyntax.membership_depth,
    NativeFormulaSyntax.existential_depth, NatExpr.depth]
  decide

theorem gateCoordinates_depth : NativeFormulaGraphs.gateCoordinates.depth ≤ allowance := by
  have hb := bundleCoordinates_depth
  simp only [NativeFormulaGraphs.gateCoordinates, Rep.depth_ofIff,
    Rep.depth_disjunction, Rep.depth_conjunction, Rep.depth_equality]
  have he : (Rep.nonzero ((Expr.var (some (2 : Fin 3)) - Expr.var (some 0)) *
      (Expr.var (some 2) - Expr.var (some 1)))).depth = 5 := rfl
  rw [he]
  simp only [Expr.depth_sub, Expr.depth_mul, Expr.depth_var, Expr.depth_constant]
  dsimp only [allowance] at *
  omega

theorem subCoordinates_thin : Thin allowance GraphRep.subCoordinates := by unfold Thin; decide

theorem naturalPairCoordinates_thin : Thin allowance GraphRep.pairCoordinates := by unfold Thin; decide

theorem naturalLeftCoordinate_thin : Thin allowance GraphRep.unpairLeftCoordinate := by unfold Thin; decide

theorem naturalRightCoordinate_thin : Thin allowance GraphRep.unpairRightCoordinate := by unfold Thin; decide

theorem cantorPairCoordinates_thin : Thin allowance CantorRepresentation.pairCoordinates := by unfold Thin; decide

theorem cantorLeftCoordinate_thin : Thin allowance CantorRepresentation.leftCoordinate := by unfold Thin; decide

theorem cantorRightCoordinate_thin : Thin allowance CantorRepresentation.rightCoordinate := by unfold Thin; decide

theorem ifEqCoordinates_thin : Thin allowance GraphRep.ifEqDirectCoordinates := by unfold Thin; decide

theorem implicationCoordinates_thin : Thin allowance NativeFormulaGraphs.implicationCoordinates := by
  have h := implicationCoordinates_depth
  change NativeFormulaGraphs.implicationCoordinates.depth ≤ allowance
  exact h

theorem gateCoordinates_thin : Thin allowance NativeFormulaGraphs.gateCoordinates := by
  have h := gateCoordinates_depth
  unfold Thin
  rw [NativeFormulaGraphs.gateCoordinates_witnessCount]
  omega

theorem stackCoordinates_thin : Thin allowance NativeFormulaGraphs.stackCoordinates := by
  have h := stackCoordinates_depth
  change NativeFormulaGraphs.stackCoordinates.depth ≤ allowance
  exact h

end NativeEnumerationSize

end DiophantineConsistency
