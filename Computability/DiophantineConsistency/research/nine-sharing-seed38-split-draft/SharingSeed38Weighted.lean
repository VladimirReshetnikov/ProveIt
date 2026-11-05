import DiophantineConsistency.SharingSeed38Syntax

/-! UNCOMPILED split draft; no new checked claim. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed38

/-- Candidate syntax-degree calculation; not yet checked by Lean. -/
theorem seed_weightedDegree (p : Fin 4 → ℤ) :
    (seed p).weightedDegree (fun _ => 1) ≤ 4 := by
  simp [seed, firstResidual, remainingResiduals, QuarticSyntax.sumExpressions,
    Expr.weightedDegree]


end DiophantineConsistency.SharingSeed38
