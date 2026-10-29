import DiophantineConsistency.QuarticCompiler
import DiophantineConsistency.NaturalExpressionSemiring

/-! # The literal tree gates over an arbitrary commutative semiring

The residuals are the existing integer syntax, interpreted through their two
natural parts. The finite syntax induction works for all semiring values.
-/

namespace DiophantineConsistency

namespace Expr
variable {σ τ R : Type*} [CommSemiring R]

def SemiringZero (e : Expr σ) (v : σ → R) : Prop :=
  e.splitNatural.1.evalSemiring v = e.splitNatural.2.evalSemiring v

theorem splitNatural_eval_rename (e : Expr σ) (f : σ → τ) (v : τ → R) :
    ((e.rename f).splitNatural.1.evalSemiring v,
      (e.rename f).splitNatural.2.evalSemiring v) =
    (e.splitNatural.1.evalSemiring (v ∘ f),e.splitNatural.2.evalSemiring (v ∘ f)) := by
  induction e <;> simp_all [rename,splitNatural,NatExpr.evalSemiring]

@[simp] theorem semiringZero_rename (e : Expr σ) (f : σ → τ) (v : τ → R) :
    (e.rename f).SemiringZero v ↔ e.SemiringZero (v ∘ f) := by
  have h := splitNatural_eval_rename e f v
  exact Iff.of_eq (congrArg (fun p : R × R => p.1=p.2) h)

@[simp] theorem semiringZero_var_nat (i : σ) (n : ℕ) (v : σ → R) :
    (.var i - .constant (n : ℤ) : Expr σ).SemiringZero v ↔ v i=n := by
  simp [SemiringZero,splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub]

@[simp] theorem semiringZero_var_var (i j : σ) (v : σ → R) :
    (.var i - .var j : Expr σ).SemiringZero v ↔ v i=v j := by
  simp [SemiringZero,splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub]

@[simp] theorem semiringZero_var_add (i j k : σ) (v : σ → R) :
    (Expr.sub (.var i) (.add (.var j) (.var k))).SemiringZero v ↔ v i=v j+v k := by
  simp [SemiringZero,splitNatural,NatExpr.evalSemiring]

@[simp] theorem semiringZero_var_mul (i j k : σ) (v : σ → R) :
    (Expr.sub (.var i) (.mul (.var j) (.var k))).SemiringZero v ↔ v i=v j*v k := by
  simp [SemiringZero,splitNatural,NatExpr.evalSemiring]

end Expr

namespace QuarticCompiler.Gates
variable {σ R : Type*} [CommSemiring R]

def semiringAssignment {τ : Type*} (v : σ → R) (w : τ → R) : σ ⊕ τ → R := Sum.elim v w

def semiringValues : (e : NatExpr σ) → (σ → R) → Wire e → R
  | .constant n, _, _ => n
  | .var i, v, _ => v i
  | .add p q, v, Sum.inl _ => p.evalSemiring v+q.evalSemiring v
  | .add p _, v, Sum.inr (Sum.inl k) => semiringValues p v k
  | .add _ q, v, Sum.inr (Sum.inr k) => semiringValues q v k
  | .mul p q, v, Sum.inl _ => p.evalSemiring v*q.evalSemiring v
  | .mul p _, v, Sum.inr (Sum.inl k) => semiringValues p v k
  | .mul _ q, v, Sum.inr (Sum.inr k) => semiringValues q v k

@[simp] theorem semiringValues_root (e : NatExpr σ) (v : σ → R) :
    semiringValues e v (root e)=e.evalSemiring v := by
  cases e <;> rfl

omit [CommSemiring R] in
private theorem assignment_comp {τ ι : Type*} (v : σ → R) (w : τ → R) (f : ι → τ) :
    semiringAssignment v w ∘ Sum.map id f = semiringAssignment v (w ∘ f) := by
  funext i
  cases i <;> rfl

theorem semiring_complete (e : NatExpr σ) (v : σ → R) :
    ∀ k : Wire e, (residualSyntax e k).SemiringZero
      (semiringAssignment v (semiringValues e v)) := by
  induction e with
  | constant n =>
    intro k
    exact (Expr.semiringZero_var_nat _ _ _).mpr rfl
  | var i =>
    intro k
    exact (Expr.semiringZero_var_var _ _ _).mpr rfl
  | add p q hp hq | mul p q hp hq =>
    intro k
    cases k with
    | inl j =>
      first
      | exact (Expr.semiringZero_var_add _ _ _ _).mpr (by simp [semiringAssignment,semiringValues])
      | exact (Expr.semiringZero_var_mul _ _ _ _).mpr (by simp [semiringAssignment,semiringValues])
    | inr k =>
      cases k with
      | inl k =>
        rw [residualSyntax,Expr.semiringZero_rename,assignment_comp]
        convert hp k using 1
        congr 1
      | inr k =>
        rw [residualSyntax,Expr.semiringZero_rename,assignment_comp]
        convert hq k using 1
        congr 1

theorem semiring_sound (e : NatExpr σ) (v : σ → R) (w : Wire e → R)
    (h : ∀ k, (residualSyntax e k).SemiringZero (semiringAssignment v w)) :
    w (root e)=e.evalSemiring v := by
  induction e with
  | constant n => exact (Expr.semiringZero_var_nat _ _ _).mp (h 0)
  | var i => exact (Expr.semiringZero_var_var _ _ _).mp (h 0)
  | add p q hp hq | mul p q hp hq =>
    have hl := hp (fun j => w (Sum.inr (Sum.inl j))) (fun k => by
      have hh := h (Sum.inr (Sum.inl k))
      rw [residualSyntax,Expr.semiringZero_rename,assignment_comp] at hh
      simpa only [Function.comp_def] using hh)
    have hr := hq (fun j => w (Sum.inr (Sum.inr j))) (fun k => by
      have hh := h (Sum.inr (Sum.inr k))
      rw [residualSyntax,Expr.semiringZero_rename,assignment_comp] at hh
      simpa only [Function.comp_def] using hh)
    first
    | exact ((Expr.semiringZero_var_add _ _ _ _).mp (h (Sum.inl 0))).trans (congrArg₂ (·+·) hl hr)
    | exact ((Expr.semiringZero_var_mul _ _ _ _).mp (h (Sum.inl 0))).trans (congrArg₂ (·*·) hl hr)

end QuarticCompiler.Gates
end DiophantineConsistency
