import DiophantineConsistency.Sign17SyntaxDegree

/-! SOURCE-ONLY: compositional syntax-degree bounds. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17SyntaxDegree

theorem degree_subst_le {σ τ : Type*} (e : Expr σ) (f : σ → Expr τ)
    (hf : ∀ i, degree (f i) ≤ 1) : degree (e.subst f) ≤ degree e := by
  induction e with
  | constant z => simp [Expr.subst, degree]
  | var i => simpa [Expr.subst, degree] using hf i
  | add a b ha hb => exact max_le_max ha hb
  | sub a b ha hb => exact max_le_max ha hb
  | mul a b ha hb => exact Nat.add_le_add ha hb

theorem sum_squares_degree_le {σ : Type*} (rs : List (Expr σ))
    (h : ∀ e ∈ rs, degree e ≤ 48) :
    degree (QuarticSyntax.sumExpressions (rs.map fun e => e * e)) ≤ 96 := by
  induction rs with
  | nil => simp [QuarticSyntax.sumExpressions, degree]
  | cons e es ih =>
    simp only [List.map_cons, QuarticSyntax.sumExpressions, degree]
    apply max_le
    · have he := h e (by simp)
      omega
    · apply ih
      intro x hx
      exact h x (by simp [hx])

theorem removeInput_degree_le {n : ℕ} (e : Expr (Fin (n + 1))) :
    degree (Sign32GenericRemoveInput.removeInput e) ≤ degree e := by
  unfold Sign32GenericRemoveInput.removeInput
  apply degree_subst_le
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [degree]
  · simp [degree]
end DiophantineConsistency.Sign17SyntaxDegree
#print axioms DiophantineConsistency.Sign17SyntaxDegree.degree_subst_le
#print axioms DiophantineConsistency.Sign17SyntaxDegree.sum_squares_degree_le
#print axioms DiophantineConsistency.Sign17SyntaxDegree.removeInput_degree_le
