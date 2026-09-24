import Diophantine.Paper1976.TwelveVariablePolynomial
import Diophantine.Paper1976.RefinedWeightBounds
import Diophantine.Common.RefinedRelationCombining

/-!
# The six-square refined prime polynomial in twelve variables

The coordinates remain `k,n,x,w,m,i,j,p,l,r,z,t`. The existing capital,
radicand, and strict-margin polynomials are combined using six separate
polynomial weights and the unsquared positive divisor and dividend.

This constructs another ordinary integer polynomial whose positive values
on natural assignments are exactly the primes. It is the six-square
refinement; no five-square equivalence or polynomial degree bound is
asserted here.
-/

namespace JSWW1976.RefinedTwelveVariable

open MvPolynomial Diophantine
open TwelveVariable (Poly capitals capitalVector radicands marginPolynomial assignment)

noncomputable section

/-- The individual weights, in the same order as the six radicands. -/
def weights : Fin 6 → Poly :=
  let k : Poly := X 0 + 1
  let K : Poly := X 1 + k + 1 + X 7 * (capitals 0 + 1)
  let L : Poly := k + 1 + X 8 * (capitals 0 * X 2 + 1)
  let R : Poly := k + 1 + X 9 * (capitals 0 * X 1 * X 2 + 1)
  let G : Poly := capitals 1 + capitals 6 * (capitals 6 + capitals 1)
  ![(2 * k + 4) * (2 * k + 2) * (X 1 + 1) + 2,
    (2 * X 1 + 4) * (2 * X 1 + 2) * (X 2 + 1) + 2,
    ((capitals 1 + 1) * capitals 3 + 2) *
      ((capitals 1 + 1) * capitals 5 + 2) * ((G + 1) * capitals 8 + 2),
    (capitals 0 + 1) * K + 2,
    (capitals 0 * X 2 + 1) * L + 2,
    (capitals 0 * X 1 * X 2 + 1) * R + 2]

theorem eval_weights (v : Fin 12 → ℤ) (idx : Fin 6) :
    eval v (weights idx) =
      RefinedWeightBounds.weights (v 0 + 1) (v 1) (v 2) (v 3) (v 4) (v 5)
        (v 6) (v 7) (v 8) (v 9) (v 10) idx := by
  fin_cases idx <;>
    simp [weights, TwelveVariable.eval_capitals, capitalVector,
      RefinedWeightBounds.weights, RefinedWeightBounds.uWeight,
      RefinedWeightBounds.kBound, RefinedWeightBounds.lBound,
      RefinedWeightBounds.rBound, RefinedWeightBounds.gBound]

/-- The refined relation-combining polynomial, with no additional variables. -/
def combined : Poly :=
  RefinedRelationCombiningPolynomial.compose 6 radicands weights (X 11)
    (capitals 6) (capitals 8 - capitals 3) marginPolynomial

theorem eval_combined (v : Fin 12 → ℤ) :
    eval v combined =
      let a := elim39Values (v 0 + 1) (v 1) (v 2) (v 3) (v 4) (v 5)
        (v 6) (v 7) (v 8) (v 9) (v 10)
      RefinedRelationCombiningPolynomial.value 6
        (elim39Squares (v 0 + 1) (v 1) (v 2) (v 3) (v 4) (v 5)
          (v 6) (v 7) (v 8) (v 9) (v 10))
        (RefinedWeightBounds.weights (v 0 + 1) (v 1) (v 2) (v 3) (v 4) (v 5)
          (v 6) (v 7) (v 8) (v 9) (v 10))
        (v 11) a.F (a.H - a.C) (elim39Margin a.C a.K a.L a.R a.S (v 3) (v 2)) := by
  rw [combined, RefinedRelationCombiningPolynomial.eval_compose]
  simp only [TwelveVariable.eval_radicands, eval_weights, TwelveVariable.eval_capitals,
    capitalVector, eval_X, eval_sub, TwelveVariable.eval_marginPolynomial]
  rfl

/-- Every natural zero satisfies the same ten-witness reduced criterion. -/
theorem reduced_of_combined_zero (v : Fin 12 → ℕ)
    (hzero : eval (fun a => (v a : ℤ)) combined = 0) :
    ReducedSys39 (v 0 + 1) (v 1) (v 2) (v 3) (v 4) (v 5)
      (v 6) (v 7) (v 8) (v 9) (v 10) := by
  have hpositive := elim39Values_divisibility_positive (v 0 + 1) (v 1) (v 2)
    (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10)
  have hzero' :
      let a := elim39Values ((v 0 + 1 : ℕ) : ℤ) (v 1) (v 2) (v 3) (v 4) (v 5)
        (v 6) (v 7) (v 8) (v 9) (v 10)
      RefinedRelationCombiningPolynomial.value 6
        (elim39Squares ((v 0 + 1 : ℕ) : ℤ) (v 1) (v 2) (v 3) (v 4) (v 5)
          (v 6) (v 7) (v 8) (v 9) (v 10))
        (RefinedWeightBounds.weights ((v 0 + 1 : ℕ) : ℤ) (v 1) (v 2) (v 3) (v 4) (v 5)
          (v 6) (v 7) (v 8) (v 9) (v 10))
        (v 11) a.F (a.H - a.C) (elim39Margin a.C a.K a.L a.R a.S (v 3) (v 2)) = 0 := by
    simpa only [eval_combined, Nat.cast_add, Nat.cast_one] using hzero
  have hc := RefinedRelationCombining.conditions_of_value_zero
    (RefinedWeightBounds.one_le_weights (v 0 + 1) (v 1) (v 2) (v 3) (v 4) (v 5)
      (v 6) (v 7) (v 8) (v 9) (v 10))
    (fun idx _ hz => (RefinedWeightBounds.weights_majorant (v 0 + 1) (v 1) (v 2)
      (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) idx).norm_le hz)
    hpositive.1 hpositive.2.le hzero'
  exact ⟨hc.1, hc.2.1, hc.2.2⟩

/-- Separate weights still need only one new natural witness. -/
theorem exists_combined_zero_of_reduced {k n x w m i j p l r z : ℕ}
    (h : ReducedSys39 (k + 1) n x w m i j p l r z) :
    ∃ t : ℕ, eval (fun a => (assignment k n x w m i j p l r z t a : ℤ)) combined = 0 := by
  have hpositive := elim39Values_divisibility_positive (k + 1) n x w m i j p l r z
  obtain ⟨t, ht⟩ := RefinedRelationCombining.exists_value_zero_of_conditions
    (RefinedWeightBounds.one_le_weights (k + 1) n x w m i j p l r z)
    (fun idx _ hroot =>
      (RefinedWeightBounds.weights_majorant (k + 1) n x w m i j p l r z idx).norm_le hroot)
    hpositive.1 hpositive.2.le h.squares h.dvd h.margin
  refine ⟨t, ?_⟩
  rw [eval_combined]
  simpa [assignment] using ht

/-- The six-square refined prime polynomial on the same twelve coordinates. -/
def primePolynomial : Poly := (X 0 + 2) * (1 - combined ^ 2)

theorem eval_primePolynomial (v : Fin 12 → ℤ) :
    eval v primePolynomial = (v 0 + 2) * (1 - (eval v combined) ^ 2) := by
  simp [primePolynomial]

theorem positive_value_prime (v : Fin 12 → ℕ)
    (hpos : 0 < eval (fun a => (v a : ℤ)) primePolynomial) :
    eval (fun a => (v a : ℤ)) primePolynomial = (v 0 : ℤ) + 2 ∧
      Nat.Prime (v 0 + 2) := by
  let e := eval (fun a => (v a : ℤ)) combined
  have he : e = 0 :=
    Diophantine.eq_zero_of_mul_one_sub_sq_pos (a := (v 0 : ℤ) + 2)
      (by positivity) (by simpa only [eval_primePolynomial, e] using hpos)
  have hred := reduced_of_combined_zero v he
  refine ⟨?_, ?_⟩
  · rw [eval_primePolynomial]
    change ((v 0 : ℤ) + 2) * (1 - e ^ 2) = _
    rw [he]
    ring
  · have hp := (theorem_3_9_reduced (k := v 0 + 1) (by omega)).mpr
      ⟨v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, hred⟩
    simpa only [Nat.add_assoc] using hp

theorem exists_value_of_prime {P : ℕ} (hP : Nat.Prime P) :
    ∃ v : Fin 12 → ℕ, eval (fun a => (v a : ℤ)) primePolynomial = (P : ℤ) := by
  let k := P - 2
  have hk : k + 2 = P := Nat.sub_add_cancel hP.two_le
  have hprime : Nat.Prime ((k + 1) + 1) := by
    simpa only [Nat.add_assoc, hk] using hP
  obtain ⟨n, x, w, m, i, j, p, l, r, z, hred⟩ :=
    (theorem_3_9_reduced (k := k + 1) (by omega)).mp hprime
  obtain ⟨t, ht⟩ := exists_combined_zero_of_reduced hred
  refine ⟨assignment k n x w m i j p l r z t, ?_⟩
  rw [eval_primePolynomial, ht]
  have hkZ : (k : ℤ) + 2 = (P : ℤ) := by exact_mod_cast hk
  simpa [assignment] using hkZ

/-- The positive natural-assignment values of the refined polynomial are
exactly the primes. -/
theorem prime_iff_positive_value (P : ℕ) :
    Nat.Prime P ↔ 0 < P ∧
      ∃ v : Fin 12 → ℕ, eval (fun a => (v a : ℤ)) primePolynomial = (P : ℤ) := by
  constructor
  · intro hP
    exact ⟨hP.pos, exists_value_of_prime hP⟩
  · rintro ⟨hP, v, hv⟩
    have hpos : 0 < eval (fun a => (v a : ℤ)) primePolynomial := by
      rw [hv]
      exact_mod_cast hP
    obtain ⟨he, hp⟩ := positive_value_prime v hpos
    have heq : P = v 0 + 2 := by rw [hv] at he; exact_mod_cast he
    exact heq.symm ▸ hp

theorem exists_refined_twelve_variable_prime_polynomial :
    ∃ f : MvPolynomial (Fin 12) ℤ, ∀ P : ℕ,
      Nat.Prime P ↔ 0 < P ∧
        ∃ v : Fin 12 → ℕ, eval (fun a => (v a : ℤ)) f = (P : ℤ) :=
  ⟨primePolynomial, prime_iff_positive_value⟩

end

end JSWW1976.RefinedTwelveVariable
