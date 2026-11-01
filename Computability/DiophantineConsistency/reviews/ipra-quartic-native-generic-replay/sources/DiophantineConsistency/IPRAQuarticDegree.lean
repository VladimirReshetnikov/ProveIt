import DiophantineConsistency.QuarticSyntax
import DiophantineConsistency.PositiveOffsetSyntaxDegree
import DiophantineConsistency.IPRAQuarticPositiveCore
set_option autoImplicit false
namespace DiophantineConsistency.IPRAQuarticDegree
open QuarticCompiler QuarticSyntax PositiveOffsetArithmetic PositiveOffsetSyntaxDegree

theorem rename_degree {σ τ : Type*} (e : Expr σ) (f : σ → τ) :
    syntaxDegree (e.rename f) = syntaxDegree e := by
  induction e <;> simp_all [Expr.rename, syntaxDegree]

theorem gate_degree {σ : Type*} (e : NatExpr σ) :
    ∀ k : Gates.Wire e, syntaxDegree (Gates.residualSyntax e k) ≤ 2 := by
  induction e with
  | constant n => intro k; change max 1 0 ≤ 2; decide
  | var i => intro k; change max 1 1 ≤ 2; decide
  | add p q hp hq | mul p q hp hq =>
    intro k
    cases k with
    | inl z => first | change max 1 (max 1 1) ≤ 2; decide | change max 1 (1 + 1) ≤ 2; decide
    | inr k =>
      cases k with
      | inl k => simpa only [Gates.residualSyntax, rename_degree] using hp k
      | inr k => simpa only [Gates.residualSyntax, rename_degree] using hq k

theorem residual_degree {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m))
    (i : Equation p q) : syntaxDegree (residualSyntax p q i) ≤ 2 := by
  cases i with
  | inl i => change max 1 0 ≤ 2; decide
  | inr i =>
    cases i with
    | inl i => simpa only [residualSyntax, rename_degree] using gate_degree p i
    | inr i =>
      cases i with
      | inl i => simpa only [residualSyntax, rename_degree] using gate_degree q i
      | inr i => change max 1 1 ≤ 2; decide

theorem list_degree {σ : Type*} (es : List (Expr σ))
    (h : ∀ e ∈ es, syntaxDegree e ≤ 4) : syntaxDegree (sumExpressions es) ≤ 4 := by
  induction es with
  | nil => simp [sumExpressions, syntaxDegree]
  | cons e es ih =>
    simp only [sumExpressions, syntaxDegree, max_le_iff]
    exact ⟨h e (by simp), ih (fun a ha => h a (by simp [ha]))⟩

theorem expression_degree {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    syntaxDegree (QuarticSyntax.expression p q) ≤ 4 := by
  rw [QuarticSyntax.expression, rename_degree]
  apply list_degree
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  dsimp only [syntaxDegree]
  have hh := residual_degree p q ((equationIndex p q).symm i)
  omega

theorem polynomial_degree_le {σ : Type*} (e : Expr σ) :
    e.toPolynomial.totalDegree ≤ syntaxDegree e := by
  induction e with
  | constant z =>
    change (MvPolynomial.C z : MvPolynomial σ ℤ).totalDegree ≤ 0
    rw [MvPolynomial.totalDegree_C]
  | var i => simp [Expr.toPolynomial,syntaxDegree]
  | add a b ha hb => exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max ha hb)
  | sub a b ha hb => exact (MvPolynomial.totalDegree_sub _ _).trans (max_le_max ha hb)
  | mul a b ha hb => exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add ha hb)

theorem positive_quartic_degree {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    (decrement (QuarticSyntax.expression p q)).toPolynomial.totalDegree ≤ 4 := by
  exact (polynomial_degree_le _).trans (by rw [degree_decrement]; exact expression_degree p q)
theorem rawQuartic_degree {m : ℕ} (e : Expr (Fin m)) :
    (IPRAQuarticPositiveBridge.rawQuartic e).toPolynomial.totalDegree ≤ 4 :=
  positive_quartic_degree _ _
#print axioms positive_quartic_degree
#print axioms rawQuartic_degree
end DiophantineConsistency.IPRAQuarticDegree
