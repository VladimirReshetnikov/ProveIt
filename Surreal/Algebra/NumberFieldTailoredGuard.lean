import Surreal.Algebra.NumberFieldSquarefreeRadicands
import Surreal.Algebra.TailoredPrimeSelection
import Surreal.Algebra.TailoredArithmeticGuard
import Surreal.Algebra.AlgebraicTypeComputability

/-!
# A root-free intersective sextic and native guard for every number field

Proves `odg:def:lem:tailored` without an unproved prime-selection hypothesis,
and supplies the native five-witness formula for `odg:def:thm:numberfield`.
The prime pair is chosen once for each field. All coefficients of the guard
remain integer numerals; there are no field parameters in its syntax.
-/

namespace Surreal.NumberFieldTailoredGuard
open TailoredIntersectivePolynomial

/-- The required prime pair exists for every number field. -/
theorem exists_admissible_nonsquares (K : Type*) [Field K] [NumberField K] :
    ∃ p q : ℕ, Admissible p q ∧ ¬IsSquare (p : K) ∧ ¬IsSquare (q : K) ∧
      ¬IsSquare ((p * q : ℕ) : K) :=
  exists_admissible_nonsquares_of_finite (SquarefreeRadicands.numberField_finite K)

/-- The full source lemma, with its exact sextic and bounded modular representatives. -/
theorem exists_rootfree_intersective_pair (K : Type*) [Field K] [NumberField K] :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧
      (∀ x : K, (polynomial p q).eval₂ (Int.castRingHom K) x ≠ 0) ∧
      ∀ m : ℕ, 0 < m → ∃ r : ℤ, 0 ≤ r ∧ r < (m : ℤ) ∧
        (m : ℤ) ∣ (polynomial p q).eval r := by
  obtain ⟨p, q, h, hp, hq, hpq⟩ := exists_admissible_nonsquares K
  refine ⟨p, q, h.1, h.2.1, (admissible_distinct_odd h).1, ?_, ?_⟩
  · intro x
    rw [eval₂_polynomial]
    exact value_ne_zero p q hp hq hpq x
  · intro m hm
    obtain ⟨r, hr0, hrm, hr⟩ := exists_integer_root_mod_bounded h m hm
    refine ⟨r, hr0, hrm, ?_⟩
    simpa [polynomial, value] using hr

/-- Prime data sufficient for every coefficient subring of the chosen field. -/
structure PrimePair (K : Type*) [Field K] where
  p : ℕ
  q : ℕ
  admissible : Admissible p q
  p_nonsquare : ¬IsSquare (p : K)
  q_nonsquare : ¬IsSquare (q : K)
  pq_nonsquare : ¬IsSquare ((p * q : ℕ) : K)

/-- Choose a verified prime pair once for each number field. -/
noncomputable def pair (K : Type*) [Field K] [NumberField K] : PrimePair K :=
  Classical.choice (by
    obtain ⟨p, q, h, hp, hq, hpq⟩ := exists_admissible_nonsquares K
    exact ⟨⟨p, q, h, hp, hq, hpq⟩⟩)

/-- The source's native parameter-free guard, with the verified chosen primes as numerals. -/
noncomputable def guard (K : Type*) [Field K] [NumberField K] :
    FirstOrder.Language.ring.Formula (Fin 1) :=
  TailoredArithmeticGuard.guard (pair K).p (pair K).q

local instance : Primcodable (FirstOrder.Language.ring.Formula (Fin 1)) :=
  RingFormulaCode.fixedFormulaPrimcodable 0

/-- For each fixed number field, the chosen native type has primitive-recursive membership.
This does not assert an algorithm selecting primes uniformly from presentations of fields. -/
theorem type_membership_primrec (K : Type*) [Field K] [NumberField K] :
    PrimrecPred (fun φ => φ ∈ AlgebraicOmittedType.formulas (guard K)) :=
  AlgebraicTypeCode.membership_primrec (guard K)

/-- The omitted type is computable under the verified native formula encoding. -/
theorem type_membership_computable (K : Type*) [Field K] [NumberField K] :
    ComputablePred (fun φ => φ ∈ AlgebraicOmittedType.formulas (guard K)) :=
  AlgebraicTypeCode.membership_computable (guard K)

end Surreal.NumberFieldTailoredGuard
