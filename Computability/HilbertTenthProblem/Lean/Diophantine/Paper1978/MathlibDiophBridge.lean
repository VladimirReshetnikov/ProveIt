import Diophantine.Common.MathlibDiophFinite
import Diophantine.Paper1978.Enumeration

/-!
# Comparing the two definitions of Diophantine sets

Mathlib represents polynomials as integer-valued functions on natural
tuples and permits arbitrary witness index types. The common finite-support
adapter reduces those witnesses to `Fin m`. The two renamings below place
the single input at coordinate zero, as required by the 1978 definition.
The equivalence holds for every natural input, including zero.
-/

namespace Jones1978

open MvPolynomial

/-- The article's finite-polynomial definition agrees with Mathlib's
functional definition, without any finiteness hypothesis on Mathlib's
original witness type. -/
theorem isDiophantine_iff_mathlib_dioph {S : Set ℕ} :
    IsDiophantine S ↔ Dioph {v : Unit → ℕ | v () ∈ S} := by
  rw [Diophantine.dioph_iff_exists_fin_polynomial]
  constructor
  · rintro ⟨m, Q, hQ⟩
    let fromFin : Fin (m + 1) → Unit ⊕ Fin m :=
      Fin.cases (Sum.inl ()) Sum.inr
    refine ⟨m, rename fromFin Q, fun v => ?_⟩
    rw [Set.mem_setOf_eq, hQ]
    apply exists_congr
    intro t
    rw [eval_rename]
    have heval : (fun i => ((Sum.elim v t i : ℕ) : ℤ)) ∘ fromFin =
        Fin.cons (v () : ℤ) (fun i => (t i : ℤ)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [heval]
  · rintro ⟨m, Q, hQ⟩
    let toFin : Unit ⊕ Fin m → Fin (m + 1) :=
      Sum.elim (fun _ => 0) Fin.succ
    refine ⟨m, rename toFin Q, fun x => ?_⟩
    rw [show x ∈ S ↔ (fun _ : Unit => x) ∈ {v : Unit → ℕ | v () ∈ S}
      from Iff.rfl, hQ]
    apply exists_congr
    intro t
    rw [eval_rename]
    have heval : Fin.cons (x : ℤ) (fun i => (t i : ℤ)) ∘ toFin =
        (fun i => ((Sum.elim (fun _ : Unit => x) t i : ℕ) : ℤ)) := by
      funext i
      cases i <;> rfl
    rw [heval]

/-- View an article-style Diophantine set in Mathlib's representation. -/
theorem IsDiophantine.mathlib_dioph {S : Set ℕ} (hS : IsDiophantine S) :
    Dioph {v : Unit → ℕ | v () ∈ S} :=
  isDiophantine_iff_mathlib_dioph.mp hS

/-- Intersection closure transferred from Mathlib's proved construction. -/
theorem IsDiophantine.inter {S T : Set ℕ}
    (hS : IsDiophantine S) (hT : IsDiophantine T) : IsDiophantine (S ∩ T) :=
  isDiophantine_iff_mathlib_dioph.mpr (hS.mathlib_dioph.inter hT.mathlib_dioph)

/-- Union closure transferred from Mathlib's proved construction. -/
theorem IsDiophantine.union {S T : Set ℕ}
    (hS : IsDiophantine S) (hT : IsDiophantine T) : IsDiophantine (S ∪ T) :=
  isDiophantine_iff_mathlib_dioph.mpr (hS.mathlib_dioph.union hT.mathlib_dioph)

/-- An existential exponent can be eliminated by Mathlib's proved
Diophantine representation of exponentiation, including bases zero and one. -/
theorem isDiophantine_powers (a : ℕ) : IsDiophantine {x : ℕ | ∃ n : ℕ, a ^ n = x} := by
  apply isDiophantine_iff_mathlib_dioph.mpr
  have hpow : Dioph {v : Option Unit → ℕ | a ^ v none = v (some ())} :=
    Dioph.eq_dioph (Dioph.pow_dioph (Dioph.const_dioph a) (Dioph.proj_dioph none))
      (Dioph.proj_dioph (some ()))
  exact Dioph.ex1_dioph hpow

end Jones1978
