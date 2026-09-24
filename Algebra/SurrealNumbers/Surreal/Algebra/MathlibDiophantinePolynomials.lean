import Mathlib.NumberTheory.Dioph
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Data.Finset.Sum

/-!
# Connecting Mathlib's Diophantine polynomials to native multivariate polynomials

A prerequisite for the remaining MRDP direction of `odg:def:thm:ce`.
Mathlib's `IsPoly` and `Poly` describe polynomial functions on natural
assignments. Their native MvPolynomial representatives involve only finitely
many variables, even when the original witness type is infinite.
-/

namespace Surreal.MathlibDiophantine
open MvPolynomial
noncomputable section

/-- Every Mathlib polynomial function has a native integer multivariate polynomial representative. -/
theorem exists_mvPolynomial {α : Type*} {f : (α → ℕ) → ℤ} (hf : IsPoly f) :
    ∃ p : MvPolynomial α ℤ, ∀ x, p.eval (fun i => (x i : ℤ)) = f x := by
  induction hf with
  | proj i => exact ⟨X i, fun _ => by simp⟩
  | const c => exact ⟨C c, fun _ => by simp⟩
  | sub _ _ ihf ihg =>
    obtain ⟨p, hp⟩ := ihf
    obtain ⟨q, hq⟩ := ihg
    exact ⟨p - q, fun x => by simp only [map_sub, hp, hq]⟩
  | mul _ _ ihf ihg =>
    obtain ⟨p, hp⟩ := ihf
    obtain ⟨q, hq⟩ := ihg
    exact ⟨p * q, fun x => by simp only [eval_mul, hp, hq]⟩

/-- Conversely, native integer polynomial evaluation is a Mathlib polynomial function. -/
theorem isPoly_eval {α : Type*} (p : MvPolynomial α ℤ) :
    IsPoly (fun x : α → ℕ => p.eval (fun i => (x i : ℤ))) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using IsPoly.const (α := α) c
  | add p q hp hq =>
    have he : (fun x : α → ℕ => (p + q).eval (fun i => (x i : ℤ))) =
        ((fun x : α → ℕ => p.eval (fun i => (x i : ℤ))) +
          fun x : α → ℕ => q.eval (fun i => (x i : ℤ))) := by
      funext x
      exact map_add _ _ _
    rw [he]
    exact hp.add hq
  | mul_X p i hp => simpa only [eval_mul, eval_X] using hp.mul (IsPoly.proj i)

/-- A native polynomial can be restricted to the finitely many witness variables it actually uses. -/
theorem exists_finite_witness_polynomial {α β : Type*} (p : MvPolynomial (α ⊕ β) ℤ) :
    ∃ s : Finset β, ∃ q : MvPolynomial (α ⊕ s) ℤ,
      rename (Sum.map id Subtype.val) q = p := by
  classical
  let s := p.vars.toRight
  refine ⟨s, ?_⟩
  apply exists_rename_eq_of_vars_subset_range p (Sum.map id Subtype.val)
  · exact Sum.map_injective.mpr ⟨Function.injective_id, Subtype.val_injective⟩
  · intro v hv
    cases v with
    | inl i => exact ⟨Sum.inl i, rfl⟩
    | inr j => exact ⟨Sum.inr ⟨j, Finset.mem_toRight.mpr hv⟩, rfl⟩

/-- Restricting to used witnesses preserves solvability with natural-number witnesses. -/
theorem finite_witness_solvability {α β : Type*} (s : Finset β)
    (q : MvPolynomial (α ⊕ s) ℤ) (x : α → ℕ) :
    (∃ y : β → ℕ, (rename (Sum.map id Subtype.val) q).eval
      (fun v => ((Sum.elim x y v : ℕ) : ℤ)) = 0) ↔
    ∃ y : s → ℕ, q.eval (fun v => ((Sum.elim x y v : ℕ) : ℤ)) = 0 := by
  classical
  have he (y : β → ℕ) :
      (rename (Sum.map id Subtype.val) q).eval (fun v => ((Sum.elim x y v : ℕ) : ℤ)) =
        q.eval (fun v => ((Sum.elim x (fun j : s => y j.val) v : ℕ) : ℤ)) := by
    rw [eval_rename]
    apply congrArg (fun z => q.eval z)
    funext v
    cases v <;> rfl
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨fun j => y j.val, (he y) ▸ hy⟩
  · rintro ⟨y, hy⟩
    let y' : β → ℕ := fun j => if hj : j ∈ s then y ⟨j, hj⟩ else 0
    have hres : (fun j : s => y' j.val) = y := by funext j; simp [y', j.property]
    refine ⟨y', ?_⟩
    rw [he, hres]
    exact hy

end
end Surreal.MathlibDiophantine
