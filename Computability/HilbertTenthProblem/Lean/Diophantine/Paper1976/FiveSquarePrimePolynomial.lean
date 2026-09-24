import Diophantine.Paper1976.FiveSquareCriterion
import Diophantine.Paper1976.RefinedTwelveVariablePolynomial

/-!
# The five-square prime polynomial in twelve variables

Equation (24) replaces the original two initial square conditions. The
remaining four square tests, divisor, dividend, and strict margin are
unchanged. Five polynomial weights and the refined relation-combining
construction leave exactly twelve natural coordinates.

The prime-value theorem uses the proved five-square criterion. It does
not identify the replacement test with the old second square condition.
Degree bounds for this particular polynomial are a separate result.
-/

namespace JSWW1976.FiveSquarePrimePolynomial

open MvPolynomial Diophantine
open TwelveVariable (Poly capitals capitalVector marginPolynomial assignment)

noncomputable section

/-- The first original square radicand, with the shifted prime parameter. -/
def firstSquare : Poly := TwelveVariable.uPolynomial (2 * (X 0 + 1)) (X 1)

theorem eval_firstSquare (v : Fin 12 → ℤ) :
    eval v firstSquare = elim39U (2 * (v 0 + 1)) (v 1) := by
  simp [firstSquare, TwelveVariable.eval_uPolynomial]

/-- The polynomial replacement radicand in equation (24). -/
def mergedRadicand : Poly :=
  firstSquare * (16 * firstSquare * (firstSquare - 1) *
    (X 1 + 1) ^ 2 * (X 2 + 1) ^ 2 + 1)

theorem eval_mergedRadicand (v : Fin 12 → ℤ) :
    eval v mergedRadicand = RefinedWeightBounds.mergedRadicand (v 0 + 1) (v 1) (v 2) := by
  simp [mergedRadicand, eval_firstSquare, RefinedWeightBounds.mergedRadicand]

/-- The polynomial weight for the replacement radicand. -/
def mergedWeight : Poly :=
  RefinedTwelveVariable.weights 0 * (4 * firstSquare * (X 1 + 1) * (X 2 + 1) + 2)

theorem eval_mergedWeight (v : Fin 12 → ℤ) :
    eval v mergedWeight = RefinedWeightBounds.mergedWeight (v 0 + 1) (v 1) (v 2) := by
  simp [mergedWeight, eval_firstSquare, RefinedTwelveVariable.eval_weights,
    RefinedWeightBounds.weights, RefinedWeightBounds.mergedWeight]

/-- The five ordinary polynomial radicands. -/
def radicands : Fin 5 → Poly :=
  ![mergedRadicand, TwelveVariable.radicands 2, TwelveVariable.radicands 3,
    TwelveVariable.radicands 4, TwelveVariable.radicands 5]

theorem eval_radicands (v : Fin 12 → ℤ) (idx : Fin 5) :
    eval v (radicands idx) =
      RefinedWeightBounds.fiveRadicands (v 0 + 1) (v 1) (v 2) (v 3) (v 4) (v 5)
        (v 6) (v 7) (v 8) (v 9) (v 10) idx := by
  fin_cases idx <;>
    simp [radicands, eval_mergedRadicand, TwelveVariable.eval_radicands,
      RefinedWeightBounds.fiveRadicands]

/-- The five separate polynomial weights. -/
def weights : Fin 5 → Poly :=
  ![mergedWeight, RefinedTwelveVariable.weights 2, RefinedTwelveVariable.weights 3,
    RefinedTwelveVariable.weights 4, RefinedTwelveVariable.weights 5]

theorem eval_weights (v : Fin 12 → ℤ) (idx : Fin 5) :
    eval v (weights idx) =
      RefinedWeightBounds.fiveWeights (v 0 + 1) (v 1) (v 2) (v 3) (v 4) (v 5)
        (v 6) (v 7) (v 8) (v 9) (v 10) idx := by
  fin_cases idx <;>
    simp [weights, eval_mergedWeight, RefinedTwelveVariable.eval_weights,
      RefinedWeightBounds.fiveWeights]

/-- A single equation replacing all five square tests and the other two conditions. -/
def combined : Poly :=
  RefinedRelationCombiningPolynomial.compose 5 radicands weights (X 11)
    (capitals 6) (capitals 8 - capitals 3) marginPolynomial

theorem eval_combined (v : Fin 12 → ℤ) :
    eval v combined =
      let a := elim39Values (v 0 + 1) (v 1) (v 2) (v 3) (v 4) (v 5)
        (v 6) (v 7) (v 8) (v 9) (v 10)
      RefinedRelationCombiningPolynomial.value 5
        (RefinedWeightBounds.fiveRadicands (v 0 + 1) (v 1) (v 2) (v 3) (v 4) (v 5)
          (v 6) (v 7) (v 8) (v 9) (v 10))
        (RefinedWeightBounds.fiveWeights (v 0 + 1) (v 1) (v 2) (v 3) (v 4) (v 5)
          (v 6) (v 7) (v 8) (v 9) (v 10))
        (v 11) a.F (a.H - a.C) (elim39Margin a.C a.K a.L a.R a.S (v 3) (v 2)) := by
  rw [combined, RefinedRelationCombiningPolynomial.eval_compose]
  simp only [eval_radicands, eval_weights, TwelveVariable.eval_capitals,
    capitalVector, eval_X, eval_sub, TwelveVariable.eval_marginPolynomial]
  rfl

/-- Every natural zero gives the five-square prime criterion. -/
theorem criterion_of_combined_zero (v : Fin 12 → ℕ)
    (hzero : eval (fun a => (v a : ℤ)) combined = 0) :
    FiveSquareSys39 (v 0 + 1) (v 1) (v 2) (v 3) (v 4) (v 5)
      (v 6) (v 7) (v 8) (v 9) (v 10) := by
  have hpositive := elim39Values_divisibility_positive (v 0 + 1) (v 1) (v 2)
    (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10)
  have hzero' :
      let a := elim39Values ((v 0 + 1 : ℕ) : ℤ) (v 1) (v 2) (v 3) (v 4) (v 5)
        (v 6) (v 7) (v 8) (v 9) (v 10)
      RefinedRelationCombiningPolynomial.value 5
        (RefinedWeightBounds.fiveRadicands ((v 0 + 1 : ℕ) : ℤ) (v 1) (v 2) (v 3)
          (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10))
        (RefinedWeightBounds.fiveWeights ((v 0 + 1 : ℕ) : ℤ) (v 1) (v 2) (v 3)
          (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10))
        (v 11) a.F (a.H - a.C) (elim39Margin a.C a.K a.L a.R a.S (v 3) (v 2)) = 0 := by
    simpa only [eval_combined, Nat.cast_add, Nat.cast_one] using hzero
  have hc := RefinedRelationCombining.conditions_of_value_zero
    (RefinedWeightBounds.one_le_fiveWeights (v 0 + 1) (v 1) (v 2) (v 3) (v 4) (v 5)
      (v 6) (v 7) (v 8) (v 9) (v 10))
    (fun idx _ hz => (RefinedWeightBounds.fiveWeights_majorant (v 0 + 1) (v 1) (v 2)
      (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) idx).norm_le hz)
    hpositive.1 hpositive.2.le hzero'
  exact ⟨hc.1, hc.2.1, hc.2.2⟩

/-- A five-square solution needs just one combining witness. -/
theorem exists_combined_zero_of_criterion {k n x w m i j p l r z : ℕ}
    (h : FiveSquareSys39 (k + 1) n x w m i j p l r z) :
    ∃ t : ℕ, eval (fun a => (assignment k n x w m i j p l r z t a : ℤ)) combined = 0 := by
  have hpositive := elim39Values_divisibility_positive (k + 1) n x w m i j p l r z
  obtain ⟨t, ht⟩ := RefinedRelationCombining.exists_value_zero_of_conditions
    (RefinedWeightBounds.one_le_fiveWeights (k + 1) n x w m i j p l r z)
    (fun idx _ hroot =>
      (RefinedWeightBounds.fiveWeights_majorant (k + 1) n x w m i j p l r z idx).norm_le hroot)
    hpositive.1 hpositive.2.le h.squares h.dvd h.margin
  refine ⟨t, ?_⟩
  rw [eval_combined]
  simpa [assignment] using ht

/-- The five-square prime polynomial, still in twelve variables. -/
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
  have hcriterion := criterion_of_combined_zero v he
  refine ⟨?_, ?_⟩
  · rw [eval_primePolynomial]
    change ((v 0 : ℤ) + 2) * (1 - e ^ 2) = _
    rw [he]
    ring
  · have hp := (theorem_3_9_five_square (k := v 0 + 1) (by omega)).mpr
      ⟨v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, hcriterion⟩
    simpa only [Nat.add_assoc] using hp

theorem exists_value_of_prime {P : ℕ} (hP : Nat.Prime P) :
    ∃ v : Fin 12 → ℕ, eval (fun a => (v a : ℤ)) primePolynomial = (P : ℤ) := by
  let k := P - 2
  have hk : k + 2 = P := Nat.sub_add_cancel hP.two_le
  have hprime : Nat.Prime ((k + 1) + 1) := by
    simpa only [Nat.add_assoc, hk] using hP
  obtain ⟨n, x, w, m, i, j, p, l, r, z, hcriterion⟩ :=
    (theorem_3_9_five_square (k := k + 1) (by omega)).mp hprime
  obtain ⟨t, ht⟩ := exists_combined_zero_of_criterion hcriterion
  refine ⟨assignment k n x w m i j p l r z t, ?_⟩
  rw [eval_primePolynomial, ht]
  have hkZ : (k : ℤ) + 2 = (P : ℤ) := by exact_mod_cast hk
  simpa [assignment] using hkZ

/-- Every prime, including two, is attained; every positive value is prime. -/
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

theorem exists_five_square_prime_polynomial :
    ∃ f : MvPolynomial (Fin 12) ℤ, ∀ P : ℕ,
      Nat.Prime P ↔ 0 < P ∧
        ∃ v : Fin 12 → ℕ, eval (fun a => (v a : ℤ)) f = (P : ℤ) :=
  ⟨primePolynomial, prime_iff_positive_value⟩

end

end JSWW1976.FiveSquarePrimePolynomial
