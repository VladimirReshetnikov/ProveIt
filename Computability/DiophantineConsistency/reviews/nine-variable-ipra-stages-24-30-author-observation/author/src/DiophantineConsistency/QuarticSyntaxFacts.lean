import DiophantineConsistency.QuarticSyntaxCore
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Degree and normalization of the quartic gate syntax, Matrix-free

`QuarticSyntax.expression p q` is a sum of squared quadratic residuals, so
its polynomial has total degree at most four, and it does not vanish when
every witness is zero (the guard residual `X_guard - 1` is then `-1`). The
same facts are `QuarticCompiler.quartic_degree` and `quartic_normalized`,
whose module imports Jones's Paper1982 and hence Mathlib's matrices; the
proofs here use only the syntax, so model-internal (Foundation) modules can
rely on them. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.QuarticSyntaxFacts
open QuarticCompiler

theorem polynomial_rename {σ τ : Type*} (e : Expr σ) (f : σ → τ) :
    (e.rename f).toPolynomial = MvPolynomial.rename f e.toPolynomial := by
  induction e <;> simp_all [Expr.rename, Expr.toPolynomial]

private theorem degree_sub {α : Type*} {p q : MvPolynomial α ℤ} {d : ℕ}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) : (p - q).totalDegree ≤ d :=
  (MvPolynomial.totalDegree_sub p q).trans (max_le hp hq)

private theorem degree_add {α : Type*} {p q : MvPolynomial α ℤ} {d : ℕ}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) : (p + q).totalDegree ≤ d :=
  (MvPolynomial.totalDegree_add p q).trans (max_le hp hq)

/-- Every gate residual is quadratic (`QuarticCompiler.Gates.residual_degree`). -/
theorem gates_residual_degree {σ : Type*} (e : NatExpr σ) :
    ∀ k, (Gates.residualSyntax e k).toPolynomial.totalDegree ≤ 2 := by
  induction e with
  | constant n =>
      intro k
      change ((MvPolynomial.X (Sum.inr 0) : MvPolynomial (σ ⊕ Fin 1) ℤ) - MvPolynomial.C (n : ℤ)).totalDegree ≤ 2
      exact degree_sub (by simp) (by rw [MvPolynomial.totalDegree_C]; omega)
  | var i =>
      intro k
      change ((MvPolynomial.X (Sum.inr 0) : MvPolynomial (σ ⊕ Fin 1) ℤ) - MvPolynomial.X (Sum.inl i)).totalDegree ≤ 2
      exact degree_sub (by simp) (by simp)
  | add p q hp hq | mul p q hp hq =>
      intro k
      cases k with
      | inl j =>
          first
          | change ((MvPolynomial.X (Sum.inr (Sum.inl 0)) : MvPolynomial (σ ⊕ Gates.Wire (.add p q)) ℤ) -
              (MvPolynomial.X (Sum.inr (Sum.inr (Sum.inl (Gates.root p)))) + MvPolynomial.X (Sum.inr (Sum.inr (Sum.inr (Gates.root q)))))).totalDegree ≤ 2
            exact degree_sub (by simp) (degree_add (by simp) (by simp))
          | change ((MvPolynomial.X (Sum.inr (Sum.inl 0)) : MvPolynomial (σ ⊕ Gates.Wire (.mul p q)) ℤ) -
              MvPolynomial.X (Sum.inr (Sum.inr (Sum.inl (Gates.root p)))) * MvPolynomial.X (Sum.inr (Sum.inr (Sum.inr (Gates.root q))))).totalDegree ≤ 2
            apply degree_sub (by simp)
            exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
      | inr k =>
          cases k with
          | inl k =>
              simpa only [Gates.residualSyntax, polynomial_rename] using
                (MvPolynomial.totalDegree_rename_le _ _).trans (hp k)
          | inr k =>
              simpa only [Gates.residualSyntax, polynomial_rename] using
                (MvPolynomial.totalDegree_rename_le _ _).trans (hq k)

/-- Every residual of the gate system is quadratic (`QuarticCompiler.residual_degree`). -/
theorem residual_degree {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) (i : Equation p q) :
    (residualSyntax p q i).toPolynomial.totalDegree ≤ 2 := by
  cases i with
  | inl i =>
      change ((MvPolynomial.X (some (Sum.inr (Sum.inr (Sum.inr 0)))) : MvPolynomial (Option (Witness p q)) ℤ) - MvPolynomial.C 1).totalDegree ≤ 2
      exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  | inr i =>
      cases i with
      | inl k =>
          simpa only [residualSyntax, polynomial_rename] using
            (MvPolynomial.totalDegree_rename_le _ _).trans (gates_residual_degree p k)
      | inr i =>
          cases i with
          | inl k =>
              simpa only [residualSyntax, polynomial_rename] using
                (MvPolynomial.totalDegree_rename_le _ _).trans (gates_residual_degree q k)
          | inr i =>
              change ((MvPolynomial.X (some (Sum.inr (Sum.inl (Gates.root p)))) : MvPolynomial (Option (Witness p q)) ℤ) -
                MvPolynomial.X (some (Sum.inr (Sum.inr (Sum.inl (Gates.root q)))))).totalDegree ≤ 2
              exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)

theorem polynomial_sumExpressions {σ : Type*} (es : List (Expr σ)) :
    (QuarticSyntax.sumExpressions es).toPolynomial = (es.map Expr.toPolynomial).sum := by
  induction es <;> simp_all [QuarticSyntax.sumExpressions, Expr.toPolynomial]

theorem eval_sumExpressions {σ : Type*} (es : List (Expr σ)) (v : σ → ℤ) :
    (QuarticSyntax.sumExpressions es).eval v = (es.map (Expr.eval v)).sum := by
  induction es <;> simp_all [QuarticSyntax.sumExpressions]

/-- **The quartic gate syntax has total degree at most four.** -/
theorem expression_degree {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    (QuarticSyntax.expression p q).toPolynomial.totalDegree ≤ 4 := by
  rw [QuarticSyntax.expression, polynomial_rename, polynomial_sumExpressions]
  refine (MvPolynomial.totalDegree_rename_le _ _).trans ?_
  rw [List.map_ofFn, Fin.sum_ofFn]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
  change (Expr.toPolynomial _ * Expr.toPolynomial _).totalDegree ≤ 4
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h := residual_degree p q ((QuarticSyntax.equationIndex p q).symm i)
  omega

/-- **The quartic gate syntax never vanishes at zero witnesses.** -/
theorem expression_normalized {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) (x : ℤ) :
    (QuarticSyntax.expression p q).eval (fun j => if j = 0 then x else 0) ≠ 0 := by
  set v : Fin (witnessCount p q + 1) → ℤ := fun j => if j = 0 then x else 0
  have hsome : ∀ w : Witness p q, v (coordinate p q (some w)) = 0 := by
    intro w
    have hne : coordinate p q (some w) ≠ 0 := by
      intro h
      rw [← coordinate_none p q] at h
      exact Option.some_ne_none w ((coordinate p q).injective h)
    simp only [v, if_neg hne]
  rw [QuarticSyntax.expression, Expr.eval_rename, eval_sumExpressions, List.map_ofFn,
    Fin.sum_ofFn]
  set f : Fin (1 + (Gates.count p + (Gates.count q + 1))) → ℤ := fun i =>
    (residualSyntax p q ((QuarticSyntax.equationIndex p q).symm i)).eval (v ∘ coordinate p q)
  show (∑ i, f i * f i) ≠ 0
  let i0 := QuarticSyntax.equationIndex p q (Sum.inl 0)
  have hf0 : f i0 = -1 := by
    simp only [f, i0, Equiv.symm_apply_apply, residualSyntax, Expr.eval_sub, Expr.eval_var,
      Function.comp_apply, hsome]
    rfl
  have hle : f i0 * f i0 ≤ ∑ i, f i * f i :=
    Finset.single_le_sum (f := fun i => f i * f i) (fun i _ => mul_self_nonneg (f i))
      (Finset.mem_univ i0)
  rw [hf0] at hle
  intro h
  linarith

end DiophantineConsistency.QuarticSyntaxFacts
