import DiophantineConsistency.Representation

/-!
# Translate natural unknowns to strictly positive integer unknowns

Replace each coordinate by its predecessor in the polynomial. This
preserves the number of variables and gives an exact domain equivalence.
-/

namespace DiophantineConsistency.Expr

variable {σ : Type*}

/-- Integer polynomial syntax on positive inputs, obtained by `u = v - 1`. -/
def positiveShift (e : Expr σ) : Expr σ := e.subst (fun i => .var i - .constant 1)

theorem hasPositiveZero_positiveShift_iff (e : Expr σ) :
    (∃ v : σ → ℤ, (∀ i, 0 < v i) ∧ e.positiveShift.eval v = 0) ↔
      ∃ u : σ → ℕ, e.eval (fun i => (u i : ℤ)) = 0 := by
  constructor
  · rintro ⟨v, hp, hz⟩
    refine ⟨fun i => (v i - 1).toNat, ?_⟩
    have he : (fun i => ((v i - 1).toNat : ℤ)) = fun i => v i - 1 := by
      funext i
      exact Int.toNat_of_nonneg (by have := hp i; omega)
    simpa only [positiveShift, eval_subst, eval_sub, eval_var, eval_constant, he] using hz
  · rintro ⟨u, hu⟩
    refine ⟨fun i => (u i : ℤ) + 1, ?_, ?_⟩
    · intro i
      exact Int.add_pos_of_nonneg_of_pos (Int.natCast_nonneg _) (by decide)
    · simpa only [positiveShift, eval_subst, eval_sub, eval_var, eval_constant,
        add_sub_cancel_right] using hu

end DiophantineConsistency.Expr
