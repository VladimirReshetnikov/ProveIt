import Diophantine.Paper1976.Theorem39Elimination
import Diophantine.Common.RelationCombining
import Diophantine.Common.RelationCombiningComposition
import Diophantine.Common.PositiveSquareTest

/-!
# A prime polynomial in twelve variables

The coordinates are `k, n, x, w, m, i, j, p, l, r, z, t`, in that order.
The first eleven coordinates supply the parameter and the ten witnesses of
the reduced Theorem 3.9, with its parameter replaced by `k + 1`. The last
coordinate is the single natural witness supplied by relation combining.

The resulting ordinary integer polynomial is `(k + 2) * (1 - M²)`, where
`M` combines the six square tests, the divisibility, and the strict margin.
Its positive values on natural assignments are exactly the primes. This
file proves the twelve-variable assertion of Theorem 2 without asserting
the degree bound printed in the article.
-/

namespace JSWW1976.TwelveVariable

open MvPolynomial
open Diophantine

noncomputable section

abbrev Poly := MvPolynomial (Fin 12) ℤ

/-- The fourteen capital expressions, in the order `M,A,B,C,D,E,F,G,H,I,K,L,R,S`. -/
def capitals : Fin 14 → Poly :=
  let k : Poly := X 0 + 1
  let M : Poly := 16 * X 1 * X 2 * (X 3 + 2) + 1
  let A := M * (X 2 + 1)
  let B : Poly := X 1 + 1
  let C : Poly := X 4 + B
  let D := (A ^ 2 - 1) * C ^ 2 + 1
  let E : Poly := 2 * (X 5 + 1) * D * C ^ 2
  let F := (A ^ 2 - 1) * E ^ 2 + 1
  let G := A + F * (F - A)
  let H : Poly := B + 2 * (X 6 + 1) * C
  let I := (G ^ 2 - 1) * H ^ 2 + 1
  let K : Poly := X 1 + 1 + X 7 * (M - 1) - k
  let L : Poly := k + 1 + X 8 * (M * X 2 - 1)
  let R : Poly := k + 1 + X 9 * (M * X 1 * X 2 - 1)
  let S : Poly := (X 10 + 1) * (k + 1) - 2
  ![M, A, B, C, D, E, F, G, H, I, K, L, R, S]

/-- The corresponding vector of integer capital values. -/
def capitalVector (v : Elim39Values) : Fin 14 → ℤ :=
  ![v.M, v.A, v.B, v.C, v.D, v.E, v.F, v.G, v.H, v.I, v.K, v.L, v.R, v.S]

theorem eval_capitals (v : Fin 12 → ℤ) (a : Fin 14) :
    eval v (capitals a) = capitalVector
      (elim39Values (v 0 + 1) (v 1) (v 2) (v 3) (v 4) (v 5)
        (v 6) (v 7) (v 8) (v 9) (v 10)) a := by
  fin_cases a <;> simp [capitals, capitalVector, elim39Values]

/-- The polynomial form of Definition 3.7. -/
def uPolynomial (x y : Poly) : Poly := (x + 2) ^ 3 * (x + 4) * (y + 1) ^ 2 + 1

theorem eval_uPolynomial (v : Fin 12 → ℤ) (x y : Poly) :
    eval v (uPolynomial x y) = elim39U (eval v x) (eval v y) := by
  simp [uPolynomial, elim39U]

/-- The six square radicands, with the capital letters eliminated. -/
def radicands : Fin 6 → Poly :=
  ![uPolynomial (2 * (X 0 + 1)) (X 1), uPolynomial (2 * X 1) (X 2),
    capitals 4 * capitals 6 * capitals 9,
    (capitals 0 ^ 2 - 1) * capitals 10 ^ 2 + 1,
    ((capitals 0 * X 2) ^ 2 - 1) * capitals 11 ^ 2 + 1,
    ((capitals 0 * X 1 * X 2) ^ 2 - 1) * capitals 12 ^ 2 + 1]

theorem eval_radicands (v : Fin 12 → ℤ) (a : Fin 6) :
    eval v (radicands a) =
      elim39Squares (v 0 + 1) (v 1) (v 2) (v 3) (v 4) (v 5)
        (v 6) (v 7) (v 8) (v 9) (v 10) a := by
  fin_cases a <;>
    simp [radicands, eval_uPolynomial, eval_capitals, capitalVector, elim39Squares]

/-- The polynomial replacing the rational strict inequality. -/
def marginPolynomial : Poly :=
  let d := (capitals 3 - (X 3 + 1) * X 2 * capitals 10 * capitals 11) *
    (capitals 3 - capitals 12) ^ 2
  d ^ 2 - 4 * (capitals 12 * capitals 10 * capitals 3 ^ 2 -
    (capitals 13 + 1) * d) ^ 2

theorem eval_marginPolynomial (v : Fin 12 → ℤ) :
    eval v marginPolynomial =
      let a := elim39Values (v 0 + 1) (v 1) (v 2) (v 3) (v 4) (v 5)
        (v 6) (v 7) (v 8) (v 9) (v 10)
      elim39Margin a.C a.K a.L a.R a.S (v 3) (v 2) := by
  simp [marginPolynomial, eval_capitals, capitalVector,
    elim39Margin, elim39Denominator, elim39Numerator]

/-- One ordinary polynomial combines all eight remaining tests. -/
def combined : Poly :=
  RelationCombiningPolynomial.compose 6 radicands (X 11) (capitals 6)
    (capitals 8 - capitals 3) marginPolynomial

theorem eval_combined (v : Fin 12 → ℤ) :
    eval v combined =
      let a := elim39Values (v 0 + 1) (v 1) (v 2) (v 3) (v 4) (v 5)
        (v 6) (v 7) (v 8) (v 9) (v 10)
      RelationCombiningPolynomial.value 6
        (elim39Squares (v 0 + 1) (v 1) (v 2) (v 3) (v 4) (v 5)
          (v 6) (v 7) (v 8) (v 9) (v 10))
        (v 11) a.F (a.H - a.C) (elim39Margin a.C a.K a.L a.R a.S (v 3) (v 2)) := by
  rw [combined, RelationCombiningPolynomial.eval_compose]
  simp only [eval_radicands, eval_capitals, capitalVector, eval_X, eval_sub,
    eval_marginPolynomial]
  rfl

/-- A natural zero of the combined polynomial satisfies the reduced prime criterion. -/
theorem reduced_of_combined_zero (v : Fin 12 → ℕ)
    (hzero : eval (fun a => (v a : ℤ)) combined = 0) :
    ReducedSys39 (v 0 + 1) (v 1) (v 2) (v 3) (v 4) (v 5)
      (v 6) (v 7) (v 8) (v 9) (v 10) := by
  have hF := (elim39Values_divisibility_positive (v 0 + 1) (v 1) (v 2)
    (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10)).1
  have hzero' :
      let a := elim39Values ((v 0 + 1 : ℕ) : ℤ) (v 1) (v 2) (v 3) (v 4) (v 5)
        (v 6) (v 7) (v 8) (v 9) (v 10)
      RelationCombiningPolynomial.value 6
        (elim39Squares ((v 0 + 1 : ℕ) : ℤ) (v 1) (v 2) (v 3) (v 4) (v 5)
          (v 6) (v 7) (v 8) (v 9) (v 10))
        (v 11) a.F (a.H - a.C) (elim39Margin a.C a.K a.L a.R a.S (v 3) (v 2)) = 0 := by
    simpa only [eval_combined, Nat.cast_add, Nat.cast_one] using hzero
  have hc := RelationCombining.conditions_of_value_zero (ne_of_gt hF) hzero'
  exact ⟨hc.1, hc.2.1, hc.2.2⟩

/-- The twelve natural coordinates, with one new combining witness `t`. -/
def assignment (k n x w m i j p l r z t : ℕ) : Fin 12 → ℕ :=
  ![k, n, x, w, m, i, j, p, l, r, z, t]

/-- A reduced solution needs exactly one additional natural coordinate. -/
theorem exists_combined_zero_of_reduced {k n x w m i j p l r z : ℕ}
    (h : ReducedSys39 (k + 1) n x w m i j p l r z) :
    ∃ t : ℕ, eval (fun a => (assignment k n x w m i j p l r z t a : ℤ)) combined = 0 := by
  have hF := (elim39Values_divisibility_positive (k + 1) n x w m i j p l r z).1
  obtain ⟨t, ht⟩ := RelationCombining.exists_value_zero_of_conditions
    (ne_of_gt hF) h.squares h.dvd h.margin
  refine ⟨t, ?_⟩
  rw [eval_combined]
  simpa [assignment] using ht

/-- The twelve-variable prime polynomial. -/
def primePolynomial : Poly := (X 0 + 2) * (1 - combined ^ 2)

theorem eval_primePolynomial (v : Fin 12 → ℤ) :
    eval v primePolynomial = (v 0 + 2) * (1 - (eval v combined) ^ 2) := by
  simp [primePolynomial]

/-- Every positive natural-assignment value equals its parameter plus two and is prime. -/
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

/-- Every prime is attained on a natural assignment. In particular, the prime two is included. -/
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

/-- The positive values of the displayed polynomial are exactly the natural primes. -/
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

/-- Theorem 2: an ordinary integer polynomial in twelve variables has precisely
the primes as its positive values on nonnegative integer assignments. -/
theorem exists_twelve_variable_prime_polynomial :
    ∃ f : MvPolynomial (Fin 12) ℤ, ∀ P : ℕ,
      Nat.Prime P ↔ 0 < P ∧
        ∃ v : Fin 12 → ℕ, eval (fun a => (v a : ℤ)) f = (P : ℤ) :=
  ⟨primePolynomial, prime_iff_positive_value⟩

end

end JSWW1976.TwelveVariable
