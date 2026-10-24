import DiophantineConsistency.PowerRepresentation
import DiophantineConsistency.RemainderRepresentation
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.Indexes
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-!
# Explicit binomial and factorial representations

The arithmetic identities used by the CRT construction are checked separately
from the representation constructors. They use digits of an explicitly chosen
power, and an explicit ceiling quotient for factorials.
-/

namespace DiophantineConsistency.FactorialRepresentation

open Nat List Finset

/-- Every binomial coefficient is an explicit digit of a power, including `k > n`. -/
theorem binomial_formula (n k : ℕ) :
    n.choose k = ((2 ^ n + 2) ^ n / (2 ^ n + 1) ^ k) % (2 ^ n + 1) := by
  let q := 2 ^ n + 1
  change n.choose k = (q.succ ^ n / q ^ k) % q
  have hCoefficient_bound := n.choose_le_two_pow
  erw [show q.succ ^ _ = ofDigits q (ofFn <| n.choose ∘ Fin.val) by
        simpa [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, sum_ofFn,
          sum_range, mul_comm] using add_pow q 1 _,
    ofDigits_div_pow_eq_ofDigits_drop _ (Nat.succ_pos _) _ <| by grind,
    ofDigits_mod_eq_head!]
  simp_all [head!_eq_head?_getD, -ofFn_succ, apply_ite_left,
    choose_eq_zero_iff, Nat.mod_eq_of_lt]

/-- The fixed radius used by the factorial quotient. -/
def radius (n : ℕ) : ℕ := (n + 2) ^ (n + 2)

/-- The explicit ceiling quotient computes factorial, also at zero. -/
theorem factorial_formula (n : ℕ) :
    ((radius n + 1) ^ n + ((radius n + n).choose n - 1)) /
      (radius n + n).choose n = n.factorial := by
  have hFactorial_bound := n.succ.succ.factorial_le_pow
  simp [factorial_succ] at hFactorial_bound
  set r := n.succ.succ ^ n.succ.succ
  change (r.succ ^ n + ((r + n).choose n - 1)) / (r + n).choose n = n.factorial
  have hAscending_bound m : r.succ * r.succ.ascFactorial m ≤
      r.succ ^ m * r.succ + m ^ 2 * r.succ.ascFactorial m := by
    induction m with
    | zero => simp
    | succ m ih =>
        simp_all [ascFactorial_succ, pow_succ]
        nlinarith [zero_le <| m * r.succ.ascFactorial m]
  have hChoose_pred := Nat.sub_add_cancel <| Nat.choose_pos <| n.le_add_left r
  apply Nat.div_eq_of_lt_le
  all_goals
    nlinarith [hAscending_bound n, r.ascFactorial_eq_factorial_mul_choose n,
      r.succ.pow_succ_le_ascFactorial n]

/-- Supplied finite graph data for the two inputs of a binomial coefficient. -/
def binomialCoordinates : GraphRep (fun v : Fin 2 → ℕ => (v 0).choose (v 1)) := by
  let n : GraphRep (fun v : Fin 2 → ℕ => v 0) := GraphRep.coordinate 0
  let k : GraphRep (fun v : Fin 2 → ℕ => v 1) := GraphRep.coordinate 1
  let q := ((GraphRep.constant 2).pow n).add (GraphRep.constant 1)
  let r := (((q.add (GraphRep.constant 1)).pow n).div (q.pow k)).mod q
  refine r.ofIff ?_
  intro v
  change (v none = ((2 ^ v (some 0) + 1 + 1) ^ v (some 0) /
    (2 ^ v (some 0) + 1) ^ v (some 1)) % (2 ^ v (some 0) + 1)) ↔
      v none = (v (some 0)).choose (v (some 1))
  rw [Nat.add_assoc, show 1 + 1 = (2 : ℕ) from rfl, ← binomial_formula]

end DiophantineConsistency.FactorialRepresentation

namespace DiophantineConsistency.GraphRep

/-- Binomial coefficients of represented arguments, including `k > n`. -/
def binomial {σ : Type*} {f g : (σ → ℕ) → ℕ} (r : GraphRep f) (s : GraphRep g) :
    GraphRep (fun v => (f v).choose (g v)) := by
  let arguments : ∀ i : Fin 2, GraphRep (![f, g] i) :=
    Fin.cases r (Fin.cases s (fun i => Fin.elim0 i))
  exact GraphRep.compose FactorialRepresentation.binomialCoordinates arguments

end DiophantineConsistency.GraphRep

namespace DiophantineConsistency.FactorialRepresentation

/-- Supplied finite graph data for factorial, using an explicit ceiling quotient. -/
def factorialCoordinates : GraphRep (fun v : Fin 1 → ℕ => (v 0).factorial) := by
  let n : GraphRep (fun v : Fin 1 → ℕ => v 0) := GraphRep.coordinate 0
  let shift := n.add (GraphRep.constant 2)
  let radius := shift.pow shift
  let c := (radius.add n).binomial n
  let numerator := ((radius.add (GraphRep.constant 1)).pow n).add
    (c.sub (GraphRep.constant 1))
  let r := numerator.div c
  refine r.ofIff ?_
  intro v
  change (v none = ((FactorialRepresentation.radius (v (some 0)) + 1) ^ v (some 0) +
      ((FactorialRepresentation.radius (v (some 0)) + v (some 0)).choose (v (some 0)) - 1)) /
    (FactorialRepresentation.radius (v (some 0)) + v (some 0)).choose (v (some 0))) ↔
      v none = (v (some 0)).factorial
  rw [factorial_formula]

end DiophantineConsistency.FactorialRepresentation

namespace DiophantineConsistency.GraphRep

/-- Factorials of explicitly represented functions, without choosing syntax. -/
def factorial {σ : Type*} {f : (σ → ℕ) → ℕ} (r : GraphRep f) :
    GraphRep (fun v => (f v).factorial) := by
  let arguments : ∀ _ : Fin 1, GraphRep f := fun _ => r
  exact GraphRep.compose FactorialRepresentation.factorialCoordinates arguments

end DiophantineConsistency.GraphRep
