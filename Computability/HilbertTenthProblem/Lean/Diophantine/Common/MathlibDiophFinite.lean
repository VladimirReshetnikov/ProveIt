import Diophantine.Common.MathlibPolynomial
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite witnesses for Mathlib's Diophantine sets

Mathlib's `Dioph` permits an arbitrary witness index type. A polynomial uses
only finitely many of those coordinates. Enumerating the witness variables
in its finite variable set therefore preserves its existential zero set.
The input index type is retained unchanged, and need not be finite.
-/

namespace Diophantine

/-- An integer polynomial with arbitrarily indexed natural witnesses has
the same existential zero set as one with finitely many witnesses.
Only the witness coordinates are renamed; all input coordinates are kept. -/
theorem exists_fin_witness_polynomial {α β : Type*}
    (p : MvPolynomial (α ⊕ β) ℤ) :
    ∃ (m : ℕ) (q : MvPolynomial (α ⊕ Fin m) ℤ), ∀ v : α → ℕ,
      (∃ t : β → ℕ,
        MvPolynomial.eval (fun i => ((Sum.elim v t i : ℕ) : ℤ)) p = 0) ↔
      ∃ t : Fin m → ℕ,
        MvPolynomial.eval (fun i => ((Sum.elim v t i : ℕ) : ℤ)) q = 0 := by
  classical
  let s : Finset β := p.vars.toRight
  let e : s ≃ Fin s.card := s.equivFin
  let f : Fin s.card → β := fun i => (e.symm i).val
  have hf : Function.Injective f := by
    intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  let k : α ⊕ Fin s.card → α ⊕ β := Sum.map id f
  have hk : Function.Injective k :=
    Sum.map_injective.mpr ⟨Function.injective_id, hf⟩
  have hvars : (p.vars : Set (α ⊕ β)) ⊆ Set.range k := by
    intro i hi
    cases i with
    | inl a => exact ⟨Sum.inl a, rfl⟩
    | inr b =>
        have hb : b ∈ s := Finset.mem_toRight.mpr hi
        refine ⟨Sum.inr (e ⟨b, hb⟩), ?_⟩
        simp [k, f]
  obtain ⟨q, hq⟩ := p.exists_rename_eq_of_vars_subset_range k hk hvars
  have heval (v : α → ℕ) (t : β → ℕ) :
      MvPolynomial.eval (fun i => ((Sum.elim v t i : ℕ) : ℤ)) p =
        MvPolynomial.eval (fun i => ((Sum.elim v (t ∘ f) i : ℕ) : ℤ)) q := by
    rw [← hq, MvPolynomial.eval_rename]
    apply congrArg (fun w : α ⊕ Fin s.card → ℤ => MvPolynomial.eval w q)
    funext i
    cases i <;> rfl
  refine ⟨s.card, q, fun v => ?_⟩
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t ∘ f, (heval v t).symm.trans ht⟩
  · rintro ⟨t, ht⟩
    let t' : β → ℕ := Function.extend f t (fun _ => 0)
    have htf : t' ∘ f = t := Function.extend_comp hf t (fun _ => 0)
    refine ⟨t', ?_⟩
    rw [heval v t', htf]
    exact ht

/-- Mathlib's `Dioph` is equivalent to an ordinary integer multivariate
polynomial with finitely many natural witnesses. The input type may be
infinite; restricting it to `Type` matches `Dioph`'s witness universe with
the universe of `Fin m`. -/
theorem dioph_iff_exists_fin_polynomial {α : Type} {S : Set (α → ℕ)} :
    Dioph S ↔ ∃ (m : ℕ) (p : MvPolynomial (α ⊕ Fin m) ℤ),
      ∀ v : α → ℕ, v ∈ S ↔ ∃ t : Fin m → ℕ,
        MvPolynomial.eval (fun i => ((Sum.elim v t i : ℕ) : ℤ)) p = 0 := by
  constructor
  · rintro ⟨β, P, hP⟩
    obtain ⟨p, hp⟩ := isPoly_iff_exists_mvPolynomial.mp P.isPoly
    obtain ⟨m, q, hq⟩ := exists_fin_witness_polynomial p
    refine ⟨m, q, fun v => (hP v).trans ?_⟩
    have heq : (∃ t : β → ℕ, P (Sum.elim v t) = 0) ↔
        ∃ t : β → ℕ,
          MvPolynomial.eval (fun i => ((Sum.elim v t i : ℕ) : ℤ)) p = 0 := by
      apply exists_congr
      intro t
      rw [hp (Sum.elim v t)]
    exact heq.trans (hq v)
  · rintro ⟨m, p, hp⟩
    let f : ((α ⊕ Fin m) → ℕ) → ℤ :=
      fun w => MvPolynomial.eval (fun i => (w i : ℤ)) p
    have hf : IsPoly f := isPoly_iff_exists_mvPolynomial.mpr ⟨p, fun _ => rfl⟩
    exact ⟨Fin m, ⟨f, hf⟩, hp⟩

end Diophantine
