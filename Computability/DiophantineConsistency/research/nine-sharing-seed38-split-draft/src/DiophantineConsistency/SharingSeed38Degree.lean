import DiophantineConsistency.SharingSeed38Weighted

/-! UNCOMPILED split draft; no new checked claim. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed38

/-- Candidate polynomial-degree bound; not yet checked by Lean. -/
theorem seed_degree (p : Fin 4 → ℤ) : (seed p).toPolynomial.totalDegree ≤ 4 := by
  have h := Expr.degree_evalRing_le (seed p) (fun _ => 1)
    (MvPolynomial.X : Fin 39 → MvPolynomial (Fin 39) ℤ) (by intro i; simp)
  rw [Expr.evalRing_X] at h
  exact h.trans (seed_weightedDegree p)


end DiophantineConsistency.SharingSeed38
