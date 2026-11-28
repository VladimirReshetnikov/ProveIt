import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
The determinant and scalar-budget core of the proposed refactor.
This file does not formalize theta lifts, the local exchange laws, or
the conversion of those laws to the recurrence below.
-/

namespace MatrixChainBudget

open Matrix

variable {K : Type*} [CommRing K]

/-- The scalar accumulated while moving successively to the next row. -/
def scalarChain (a : ℕ → ℕ → K) : ℕ → ℕ → K
  | _, 0 => 1
  | i, n + 1 => a i n * scalarChain a (i + 1) n

/-- Taking determinants at every stage needs no commutativity between
the matrices `S i` and no construction of their global product. -/
theorem determinant_chain {d : Type*} [Fintype d] [DecidableEq d]
    (G : ℕ → ℕ → Matrix d d K) (S : ℕ → Matrix d d K)
    (a : ℕ → ℕ → K)
    (hzero : ∀ i, G i 0 = 1)
    (hstep : ∀ i n, G i (n + 1) = a i n • (S i * G (i + 1) n))
    (i n : ℕ) :
    (G i n).det = scalarChain a i n ^ Fintype.card d *
      ((List.range' i n).map fun k => (S k).det).prod := by
  induction n generalizing i with
  | zero => simp [hzero, scalarChain]
  | succ n ih =>
      rw [hstep, Matrix.det_smul, Matrix.det_mul, ih]
      simp only [scalarChain, List.range'_succ, List.map_cons, List.prod_cons, mul_pow]
      ring

/-- Additive scalar cost along the same triangular recursion. -/
def accumulatedCost (e : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | i, n + 1 => e i n + accumulatedCost e (i + 1) n

def triangular : ℕ → ℕ
  | 0 => 0
  | n + 1 => n + triangular n

theorem twice_triangular (n : ℕ) : 2 * triangular n + n = n * n := by
  induction n with
  | zero => simp [triangular]
  | succ n ih => simp only [triangular]; nlinarith

theorem accumulatedCost_uniform (C : ℝ) (i n : ℕ) :
    accumulatedCost (fun _ n => (n : ℝ) * C) i n = (triangular n : ℝ) * C := by
  induction n generalizing i with
  | zero => simp [accumulatedCost, triangular]
  | succ n ih => simp [accumulatedCost, triangular, ih, Nat.cast_add, add_mul]

/-- Each square `(r,k)` is charged once, allowing a different cost for
every square of the triangular array. -/
theorem accumulatedCost_squares (E : ℕ → ℕ → ℝ) (i n : ℕ) :
    accumulatedCost
      (fun i n => ∑ k ∈ Finset.Ioc (i + 1) (i + 1 + n), E (i + 1) k) i n =
      ∑ r ∈ Finset.Ioc i (i + n), ∑ k ∈ Finset.Ioc r (i + n), E r k := by
  induction n generalizing i with
  | zero => simp [accumulatedCost]
  | succ n ih =>
      rw [accumulatedCost, ih]
      have hsum := Finset.sum_Ioc_consecutive
        (fun r => ∑ k ∈ Finset.Ioc r (i + (n + 1)), E r k)
        (Nat.le_succ i) (show i + 1 ≤ i + (n + 1) by omega)
      simpa [Nat.Ioc_succ_singleton, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsum

section Ratio

variable {T J : Type*} (t₀ : T) (sample : J → T)

/-- This formula is algebraically total in Lean. Its use as a ratio of
nonzero volumes must additionally supply the nonvanishing hypotheses. -/
noncomputable def squaredRatio (c : T → ℂ) : J → ℂ :=
  fun j => (‖c t₀ / c (sample j)‖ : ℂ) ^ 2

theorem squaredRatio_one :
    squaredRatio t₀ sample (fun _ => (1 : ℂ)) = 1 := by
  funext j
  simp [squaredRatio]

theorem squaredRatio_mul (c c' : T → ℂ) :
    squaredRatio t₀ sample (fun t => c t * c' t) =
      squaredRatio t₀ sample c * squaredRatio t₀ sample c' := by
  funext j
  simp only [squaredRatio, mul_div_mul_comm, norm_mul, Complex.ofReal_mul, mul_pow,
    Pi.mul_apply]

/-- The proposed guarded interface. `Good` is instantiated by
`D.HasSmallRatios` and `H` by the existing `New.HeightLe`. -/
def ScalarBudget (Good : (J → T) → Prop) (H : ℝ → (J → ℂ) → Prop)
    (c : T → ℂ) (B : ℝ) : Prop :=
  c t₀ ≠ 0 → ∀ sample, Good sample → H B (squaredRatio t₀ sample c)

theorem scalarBudget_mul (Good : (J → T) → Prop) (H : ℝ → (J → ℂ) → Prop)
    (hmul : ∀ {u v : ℝ} {x y : J → ℂ}, H u x → H v y → H (u + v) (x * y))
    {c c' : T → ℂ} {u v : ℝ}
    (hc : ScalarBudget t₀ Good H c u) (hc' : ScalarBudget t₀ Good H c' v) :
    ScalarBudget t₀ Good H (fun t => c t * c' t) (u + v) := by
  intro hbase sample hgood
  simpa only [squaredRatio_mul] using
    hmul (hc (left_ne_zero_of_mul hbase) sample hgood)
      (hc' (right_ne_zero_of_mul hbase) sample hgood)

/-- Any multiplicative height calculus can propagate the local costs.
Negative costs are allowed; there is no use of monotonicity here. -/
theorem scalarChain_cost
    (H : ℝ → (J → ℂ) → Prop)
    (hone : H 0 1)
    (hmul : ∀ {u v : ℝ} {x y : J → ℂ}, H u x → H v y → H (u + v) (x * y))
    (a : T → ℕ → ℕ → ℂ) (e : ℕ → ℕ → ℝ)
    (ha : ∀ i n, H (e i n) (squaredRatio t₀ sample (fun t => a t i n)))
    (i n : ℕ) :
    H (accumulatedCost e i n)
      (squaredRatio t₀ sample (fun t => scalarChain (a t) i n)) := by
  induction n generalizing i with
  | zero => simpa [accumulatedCost, scalarChain, squaredRatio_one] using hone
  | succ n ih =>
      simpa only [accumulatedCost, scalarChain, squaredRatio_mul] using
        hmul (ha i n) (ih (i + 1))

/-- The guarded local certificates propagate without assuming individual
nonvanishing in advance. The accumulated scalar's base-point guard is
enough to recover each guard during the recursion. -/
theorem scalarChain_budget
    (Good : (J → T) → Prop) (H : ℝ → (J → ℂ) → Prop)
    (hone : H 0 1)
    (hmul : ∀ {u v : ℝ} {x y : J → ℂ}, H u x → H v y → H (u + v) (x * y))
    (a : T → ℕ → ℕ → ℂ) (e : ℕ → ℕ → ℝ)
    (ha : ∀ i n, ScalarBudget t₀ Good H (fun t => a t i n) (e i n))
    (i n : ℕ) :
    ScalarBudget t₀ Good H (fun t => scalarChain (a t) i n) (accumulatedCost e i n) := by
  induction n generalizing i with
  | zero => intro _ sample _; simpa [scalarChain, accumulatedCost, squaredRatio_one] using hone
  | succ n ih =>
      simpa only [scalarChain, accumulatedCost] using
        scalarBudget_mul t₀ Good H hmul (ha i n) (ih (i + 1))

end Ratio

end MatrixChainBudget

#print axioms MatrixChainBudget.determinant_chain
#print axioms MatrixChainBudget.scalarChain_cost
#print axioms MatrixChainBudget.twice_triangular
#print axioms MatrixChainBudget.accumulatedCost_squares
#print axioms MatrixChainBudget.scalarBudget_mul
#print axioms MatrixChainBudget.scalarChain_budget
