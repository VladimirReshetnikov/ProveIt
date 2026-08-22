import Mathlib.Tactic

/-!
# Carry-path algebra from continuation report 26

This module kernel-checks the finite algebraic core of report 26's new carry-language
construction.  A word consists of exponent moves `(a,b)`.  Starting from the sum of all
moves, a carry by `(a,b)` replaces the distinguished monomial by
`U^a V^b` copies at the next suffix vertex, freezes all but one copy, and continues with
the distinguished copy.

The theorems below prove that the resulting list of frozen terms

* sums exactly to the monomial at the endpoint;
* has exactly `1 + ∑ (U^a V^b - 1)` terms; and
* retains enough ordered suffix data to reconstruct the word once its endpoint is fixed.

The analytic entropy estimates and the passage from ordered suffix data to injectivity of
the associated *multisets* are deliberately left at paper level.
-/

namespace LeanProofs.TwoBaseIntegerExponent
namespace Report26CarryPath

/-- An exponent-lattice move. -/
abbrev Move := ℕ × ℕ

/-- Coordinatewise addition of exponent moves. -/
def addMove (v w : Move) : Move := (v.1 + w.1, v.2 + w.2)

/-- The endpoint of a carry word, i.e. the sum of all its exponent moves. -/
def endpoint : List Move → Move
  | [] => (0, 0)
  | v :: word => addMove v (endpoint word)

/-- The monomial `U^a V^b` attached to an exponent pair `(a,b)`. -/
def monomial (U V : ℕ) (v : Move) : ℕ := U ^ v.1 * V ^ v.2

/-- The ordered list of destination vertices visited by a carry word. -/
def suffixVertices : List Move → List Move
  | [] => []
  | _ :: word => endpoint word :: suffixVertices word

/-- The distinguished-descendant representation associated with a carry word.

At a letter `v`, freeze `U^v.1 * V^v.2 - 1` copies of the monomial at the
remaining suffix endpoint, then continue with one distinguished copy.
-/
def carryRepresentation (U V : ℕ) : List Move → List ℕ
  | [] => [1]
  | v :: word =>
      List.replicate (monomial U V v - 1) (monomial U V (endpoint word)) ++
        carryRepresentation U V word

/-- The exact arity predicted by the carry word. -/
def carryArity (U V : ℕ) : List Move → ℕ
  | [] => 1
  | v :: word => monomial U V v - 1 + carryArity U V word

/-- Monomials turn coordinatewise addition of exponent pairs into multiplication. -/
theorem monomial_add (U V : ℕ) (v w : Move) :
    monomial U V (addMove v w) = monomial U V v * monomial U V w := by
  simp only [monomial, addMove, pow_add]
  ring

/-- Positive bases give positive monomial multipliers. -/
theorem monomial_pos {U V : ℕ} (hU : 0 < U) (hV : 0 < V) (v : Move) :
    0 < monomial U V v := by
  exact Nat.mul_pos (Nat.pow_pos hU) (Nat.pow_pos hV)

/-- The frozen frontier plus the final distinguished `1` telescopes to the endpoint
monomial. -/
theorem carryRepresentation_sum
    {U V : ℕ} (hU : 0 < U) (hV : 0 < V) (word : List Move) :
    (carryRepresentation U V word).sum = monomial U V (endpoint word) := by
  induction word with
  | nil => simp [carryRepresentation, endpoint, monomial]
  | cons v word ih =>
      have hD : 1 ≤ monomial U V v := monomial_pos hU hV v
      simp only [carryRepresentation, List.sum_append, List.sum_replicate, ih,
        endpoint, monomial_add]
      calc
        (monomial U V v - 1) * monomial U V (endpoint word) +
            monomial U V (endpoint word) =
            ((monomial U V v - 1) + 1) * monomial U V (endpoint word) := by ring
        _ = monomial U V v * monomial U V (endpoint word) := by
          rw [Nat.sub_add_cancel hD]

/-- Every carry letter contributes exactly `D - 1` frozen terms, in addition to the
single final distinguished term. -/
theorem carryRepresentation_length (U V : ℕ) (word : List Move) :
    (carryRepresentation U V word).length = carryArity U V word := by
  induction word with
  | nil => simp [carryRepresentation, carryArity]
  | cons v word ih =>
      simp [carryRepresentation, carryArity, ih]

/-- Packaged correctness theorem for the distinguished-descendant carry construction. -/
theorem carryConstruction_correct
    {U V : ℕ} (hU : 0 < U) (hV : 0 < V) (word : List Move) :
    (carryRepresentation U V word).sum = monomial U V (endpoint word) ∧
      (carryRepresentation U V word).length = carryArity U V word := by
  exact ⟨carryRepresentation_sum hU hV word, carryRepresentation_length U V word⟩

/-- A nonzero move strictly lowers total exponent degree when it is removed from an
endpoint.  This is the ordering invariant used to recover carry paths from their frozen
vertices. -/
theorem endpoint_tail_degree_lt (v : Move) (word : List Move) (hv : v ≠ (0, 0)) :
    (endpoint word).1 + (endpoint word).2 <
      (endpoint (v :: word)).1 + (endpoint (v :: word)).2 := by
  have hvpos : 0 < v.1 + v.2 := by
    by_cases hfirst : v.1 = 0
    · have hsecond : v.2 ≠ 0 := by
        intro hsecond
        apply hv
        exact Prod.ext hfirst hsecond
      exact Nat.add_pos_right v.1 (Nat.pos_of_ne_zero hsecond)
    · exact Nat.add_pos_left (Nat.pos_of_ne_zero hfirst) v.2
  simp only [endpoint, addMove]
  omega

/-- Once the common endpoint and ordered suffix vertices are known, the carry word is
uniquely determined. -/
theorem word_eq_of_endpoint_eq_of_suffixVertices_eq
    {word word' : List Move}
    (hend : endpoint word = endpoint word')
    (hsuffix : suffixVertices word = suffixVertices word') :
    word = word' := by
  induction word generalizing word' with
  | nil =>
      cases word' with
      | nil => rfl
      | cons v word' => simp [suffixVertices] at hsuffix
  | cons v word ih =>
      cases word' with
      | nil => simp [suffixVertices] at hsuffix
      | cons v' word' =>
          have hsuffix' : endpoint word = endpoint word' ∧
              suffixVertices word = suffixVertices word' := by
            simpa only [suffixVertices, List.cons.injEq] using hsuffix
          have hword : word = word' := ih hsuffix'.1 hsuffix'.2
          subst word'
          have hfst : v.1 + (endpoint word).1 = v'.1 + (endpoint word).1 := by
            simpa only [endpoint, addMove] using congrArg Prod.fst hend
          have hsnd : v.2 + (endpoint word).2 = v'.2 + (endpoint word).2 := by
            simpa only [endpoint, addMove] using congrArg Prod.snd hend
          have hvv' : v = v' := by
            apply Prod.ext
            · exact Nat.add_right_cancel hfst
            · exact Nat.add_right_cancel hsnd
          subst v'
          rfl

end Report26CarryPath
end LeanProofs.TwoBaseIntegerExponent
