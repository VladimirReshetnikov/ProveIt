import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Polynomial renaming with a distinguished input

Variables indexed by `Option σ` separate one input (`none`) from the witnesses
(`some idx`). A variable equivalence preserves solutions with the input fixed,
as well as evaluation with every witness set to zero. These facts are independent
of the number of witnesses and the polynomial's degree.
-/

namespace Diophantine

/-- Renaming preserves solutions with a fixed input and a prescribed value.
Witnesses may lie in any type `A`; `embed` maps their values into the coefficient
semiring and need not be injective. No finiteness assumption is required. -/
theorem exists_eval_rename_option_iff {σ τ A R : Type*} [CommSemiring R]
    (e : Option σ ≃ τ) (p : MvPolynomial (Option σ) R)
    (embed : A → R) (x : A) (target : R) :
    (∃ a : τ → A, a (e none) = x ∧
      MvPolynomial.eval (embed ∘ a) (MvPolynomial.rename e p) = target) ↔
      ∃ v : σ → A, MvPolynomial.eval
        (fun idx => match idx with
          | none => embed x
          | some k => embed (v k)) p = target := by
  constructor
  · rintro ⟨a, hinput, ha⟩
    refine ⟨fun k => a (e (some k)), ?_⟩
    rw [MvPolynomial.eval_rename] at ha
    refine (congrArg (fun values => MvPolynomial.eval values p) ?_).trans ha
    funext idx
    cases idx with
    | none => exact congrArg embed hinput.symm
    | some k => rfl
  · rintro ⟨v, hv⟩
    refine ⟨fun idx => (e.symm idx).elim x v, ?_, ?_⟩
    · change (e.symm (e none)).elim x v = x
      rw [e.symm_apply_apply]
      rfl
    · rw [MvPolynomial.eval_rename]
      refine (congrArg (fun values => MvPolynomial.eval values p) ?_).trans hv
      funext idx
      change embed ((e.symm (e idx)).elim x v) = _
      rw [e.symm_apply_apply]
      cases idx <;> rfl

/-- Setting every witness to zero commutes with renaming. The distinguished
input has the same value on both sides. -/
theorem eval_rename_zeroWitnesses {σ τ R : Type*} [CommSemiring R] [DecidableEq τ]
    (e : Option σ ≃ τ) (p : MvPolynomial (Option σ) R) (x : R) :
    MvPolynomial.eval (fun idx => if idx = e none then x else 0)
        (MvPolynomial.rename e p) =
      MvPolynomial.eval (fun idx => match idx with
        | none => x
        | some _ => 0) p := by
  classical
  have heq : (fun idx => if idx = e none then x else 0) ∘ e =
      (fun idx => match idx with | none => x | some _ => 0) := by
    funext idx
    change (if e idx = e none then x else 0) = _
    cases idx <;> simp [e.apply_eq_iff_eq]
  rw [MvPolynomial.eval_rename, heq]

end Diophantine
