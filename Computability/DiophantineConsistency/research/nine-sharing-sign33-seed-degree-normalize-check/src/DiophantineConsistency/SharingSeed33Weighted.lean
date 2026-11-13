import DiophantineConsistency.SharingSeed33Syntax

/-! UNCOMPILED split draft; no new checked claim. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed33

/-- Constructor-oriented rewrites for the overloaded syntax operations. -/
private theorem degree_add (w : Fin 34 → ℕ) (a b : Expr (Fin 34)) :
    (a + b).weightedDegree w = max (a.weightedDegree w) (b.weightedDegree w) := rfl
private theorem degree_sub (w : Fin 34 → ℕ) (a b : Expr (Fin 34)) :
    (a - b).weightedDegree w = max (a.weightedDegree w) (b.weightedDegree w) := rfl
private theorem degree_mul (w : Fin 34 → ℕ) (a b : Expr (Fin 34)) :
    (a * b).weightedDegree w = a.weightedDegree w + b.weightedDegree w := rfl

/-- Candidate syntax-degree calculation; not yet checked by Lean. -/
theorem seed_weightedDegree (p : Fin 4 → ℤ) :
    (seed p).weightedDegree (fun _ => 1) ≤ 4 := by
  simp [seed, firstResidual, remainingResiduals, QuarticSyntax.sumExpressions,
    degree_add, degree_sub, degree_mul, Expr.weightedDegree]


end DiophantineConsistency.SharingSeed33

#print axioms DiophantineConsistency.SharingSeed33.seed_weightedDegree
