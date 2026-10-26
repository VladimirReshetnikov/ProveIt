import DiophantineConsistency.GatesSemiring

/-! Prototype showing that the natural gate proofs are instances of the
already proved semiring results.  Integrating it requires splitting gate data
out of QuarticCompiler to avoid an import cycle; this file is an independent
validation of the semantic bridge, not that module reorganization. -/
namespace DiophantineConsistency.ProofSimplification.SemiringSpecialization
open QuarticCompiler.Gates

variable {σ τ : Type*}

theorem zero_iff_semiringZero (e : Expr (σ ⊕ τ)) (v : σ → ℕ) (w : τ → ℕ) :
    e.eval (natAssignment v w) = 0 ↔ e.SemiringZero (semiringAssignment v w) := by
  have ha : natAssignment v w = fun i => (semiringAssignment v w i : ℤ) := by
    funext i
    cases i <;> rfl
  rw [ha, Expr.eval_eq_zero_iff_splitNatural]
  simp only [Expr.SemiringZero, NatExpr.evalSemiring_nat]

theorem values_nat (e : NatExpr σ) (v : σ → ℕ) :
    semiringValues e v = values e v := by
  induction e with
  | constant n => rfl
  | var i => rfl
  | add p q hp hq | mul p q hp hq =>
    funext k
    rcases k with k | (k | k)
    · simp only [semiringValues, values, NatExpr.evalSemiring_nat]
    · exact congrFun hp k
    · exact congrFun hq k

theorem complete_from_semiring (e : NatExpr σ) (v : σ → ℕ) (k : Wire e) :
    (residualSyntax e k).eval (natAssignment v (values e v)) = 0 := by
  apply (zero_iff_semiringZero _ _ _).mpr
  simpa only [values_nat] using semiring_complete e v k

theorem sound_from_semiring (e : NatExpr σ) (v : σ → ℕ) (w : Wire e → ℕ)
    (h : ∀ k, (residualSyntax e k).eval (natAssignment v w) = 0) :
    w (root e) = e.eval v := by
  simpa only [NatExpr.evalSemiring_nat] using
    semiring_sound e v w (fun k => (zero_iff_semiringZero _ _ _).mp (h k))

#print axioms complete_from_semiring
#print axioms sound_from_semiring
end DiophantineConsistency.ProofSimplification.SemiringSpecialization
