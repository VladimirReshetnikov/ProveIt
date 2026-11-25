import IPRADerivations.DiophantineNumberTheory.PellNegDescent
import IPRADerivations.Core.LinearCombination

/-!
# Uniform descent for the generalized Pell equation `x² − Dy² = N`

Packet: `diophantine-number-theory/pell_ipra_2026-11-15`, Lemma `lem:generaldescent`.

Let `A² = 1 + D B²` with `B, D ≥ 1`, let `K = |N| ≥ 1`, and let `(x, y)` solve
`x² = Dy² + K` (`N > 0`) or `x² + K = Dy²` (`N < 0`) with `y > AK`. Then multiplication by
`(A, −B)` gives `r = Ax ∸ DBy`, `t = Ay ∸ Bx` with

* the same norm (`r² = Dt² + K`, resp. `r² + K = Dt²`), `r ≥ 1`, `t ≥ 1`, `t < y`,
* and the reconstruction `x = Ar + DBt`, `y = Br + At`.

The three strict square comparisons of the paper are written with explicit surpluses in terms
of `w = y² − (A²K + 1) ≥ 0` (from `y > AK`, `K ≥ 1`):

* `N > 0`: `(Ay)² − (Bx)² = 1 + w + K(1 + (D−1)B²)`, `(Ax)² − (DBy)² = Dy² + A²K`,
  `(Bx)² − ((A−1)y)² = 2(A−1)y² + B²K`;
* `N < 0`: `(Ay)² − (Bx)² = y² + B²K`, `(Ax)² − (DBy)² = (D−1)y² + 1 + w`,
  `(Bx)² − ((A−1)y)² = 1 + y² + w + K(1 + (D−1)B²) + 2(A−2)y²`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellGenDescent

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.PellDescent (lt_of_sq_lt A_pos rr tt)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `A²K < y²` from `AK < y` and `K ≥ 1`. -/
theorem sq_gap {A K y : PTm n} (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) (hy : Γ ⊢[PRAAx] lt (A * K) y) :
    Γ ⊢[PRAAx] lt (A * A * K) (y * y) := by
  refine le_of_eq_add (d := A * A * K * pred K + two * (A * K * succ (monus y (succ (A * K)))) +
    two * monus y (succ (A * K)) + monus y (succ (A * K)) * monus y (succ (A * K))) ?_
  ipra_lc (Groth.ι (IPRA.Q.mk Γ y) + Groth.ι (IPRA.Q.mk Γ A) * Groth.ι (IPRA.Q.mk Γ K) + 1 + Groth.ι (IPRA.Q.mk Γ (monus y (succ (A * K))))) * natEq (eq_add_of_le hy) +
    Groth.ι (IPRA.Q.mk Γ A) ^ 2 * Groth.ι (IPRA.Q.mk Γ K) * natEq hK

/-- The shared tail of both descents: positivity, `t < y`, reconstruction. -/
theorem assemble {A B D x y : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (lr : Γ ⊢[PRAAx] lt (D * (B * y)) (A * x)) (ht : Γ ⊢[PRAAx] lt (B * x) (A * y))
    (ly : Γ ⊢[PRAAx] lt (pred A * y) (B * x)) :
    Γ ⊢[PRAAx] le one (rr A B D x y) ⋏ le one (tt A B D x y) ⋏ lt (tt A B D x y) y ⋏
      (x ≐ A * rr A B D x y + D * (B * tt A B D x y)) ⋏ (y ≐ B * rr A B D x y + A * tt A B D x y) := by
  have er := ((eq_add_of_le (le_of_lt lr)).eqTrans (add_comm _ _)).eqSymm
  have et := ((eq_add_of_le (le_of_lt ht)).eqTrans (add_comm _ _)).eqSymm
  have h₁ := natEq hA; have h₃ := natEq er; have h₄ := natEq et
  refine .andI ?_ (.andI ?_ (.andI ?_ (.andI ?_ ?_)))
  · refine le_of_eq_add (d := monus (A * x) (succ (D * (B * y)))) ?_
    have h₅ := natEq (eq_add_of_le lr)
    apply deriveNat; ipra_simps
    linear_combination h₃ + h₅
  · refine le_of_eq_add (d := monus (A * y) (succ (B * x))) ?_
    have h₅ := natEq (eq_add_of_le ht)
    apply deriveNat; ipra_simps
    linear_combination h₄ + h₅
  · refine le_of_eq_add (d := monus (B * x) (succ (pred A * y))) ?_
    have h₅ := natEq (eq_add_of_le ly); have h₆ := natEq (A_pos hA)
    apply deriveNat; ipra_simps
    linear_combination -h₄ + h₅ - Groth.ι (IPRA.Q.mk Γ y) * h₆
  · ipra_lc -Groth.ι (IPRA.Q.mk Γ x) * h₁ - Groth.ι (IPRA.Q.mk Γ A) * h₃ -
      Groth.ι (IPRA.Q.mk Γ D) * Groth.ι (IPRA.Q.mk Γ B) * h₄
  · ipra_lc -Groth.ι (IPRA.Q.mk Γ y) * h₁ - Groth.ι (IPRA.Q.mk Γ B) * h₃ - Groth.ι (IPRA.Q.mk Γ A) * h₄

/-! ## Positive `N = K` -/

section Pos
variable {A B D K x y : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
  (hx : Γ ⊢[PRAAx] x * x ≐ D * (y * y) + K)
include hA hx

theorem pos_t (hD : Γ ⊢[PRAAx] D ≐ succ (pred D)) (hK : Γ ⊢[PRAAx] K ≐ succ (pred K))
    (hy : Γ ⊢[PRAAx] lt (A * K) y) : Γ ⊢[PRAAx] lt (B * x) (A * y) := by
  refine lt_of_sq_lt (le_of_eq_add (d := monus (y * y) (succ (A * A * K)) + K * succ (pred D * (B * B))) ?_)
  ipra_lc (Groth.ι (IPRA.Q.mk Γ y) ^ 2 + Groth.ι (IPRA.Q.mk Γ K)) * natEq hA -
    Groth.ι (IPRA.Q.mk Γ B) ^ 2 * natEq hx + natEq (eq_add_of_le (sq_gap hK hy)) +
    Groth.ι (IPRA.Q.mk Γ K) * Groth.ι (IPRA.Q.mk Γ B) ^ 2 * natEq hD

theorem pos_r (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) : Γ ⊢[PRAAx] lt (D * (B * y)) (A * x) := by
  have hp := pos_mul (pos_mul (A_pos hA) (A_pos hA)) hK
  refine lt_of_sq_lt (le_of_eq_add (d := D * (y * y) + pred (A * A * K)) ?_)
  ipra_lc Groth.ι (IPRA.Q.mk Γ A) ^ 2 * natEq hx + Groth.ι (IPRA.Q.mk Γ D) * Groth.ι (IPRA.Q.mk Γ y) ^ 2 * natEq hA +
    natEq hp

theorem pos_y (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) :
    Γ ⊢[PRAAx] lt (pred A * y) (B * x) := by
  have hp := pos_mul (pos_mul hB hB) hK
  refine lt_of_sq_lt (le_of_eq_add (d := two * (pred A * (y * y)) + pred (B * B * K)) ?_)
  ipra_lc Groth.ι (IPRA.Q.mk Γ B) ^ 2 * natEq hx - Groth.ι (IPRA.Q.mk Γ y) ^ 2 * natEq hA + natEq hp +
    (Groth.ι (IPRA.Q.mk Γ (pred A)) + Groth.ι (IPRA.Q.mk Γ A) + 1) * Groth.ι (IPRA.Q.mk Γ y) ^ 2 * natEq (A_pos hA)

end Pos

/-- Lemma `lem:generaldescent`, `N = K > 0`. -/
theorem gen_descent_pos {A B D K x y : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hD : Γ ⊢[PRAAx] D ≐ succ (pred D))
    (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) (hx : Γ ⊢[PRAAx] x * x ≐ D * (y * y) + K)
    (hy : Γ ⊢[PRAAx] lt (A * K) y) :
    Γ ⊢[PRAAx] (rr A B D x y * rr A B D x y ≐ D * (tt A B D x y * tt A B D x y) + K) ⋏
      (le one (rr A B D x y) ⋏ le one (tt A B D x y) ⋏ lt (tt A B D x y) y ⋏
      (x ≐ A * rr A B D x y + D * (B * tt A B D x y)) ⋏ (y ≐ B * rr A B D x y + A * tt A B D x y)) := by
  have lr := pos_r hA hx hK
  have ht := pos_t hA hx hD hK hy
  refine .andI ?_ (assemble hA lr ht (pos_y hA hx hB hK))
  have er := ((eq_add_of_le (le_of_lt lr)).eqTrans (add_comm _ _)).eqSymm
  have et := ((eq_add_of_le (le_of_lt ht)).eqTrans (add_comm _ _)).eqSymm
  ipra_lc (Groth.ι (IPRA.Q.mk Γ (rr A B D x y)) + Groth.ι (IPRA.Q.mk Γ A) * Groth.ι (IPRA.Q.mk Γ x) - Groth.ι (IPRA.Q.mk Γ D) * Groth.ι (IPRA.Q.mk Γ B) * Groth.ι (IPRA.Q.mk Γ y)) * natEq er -
    Groth.ι (IPRA.Q.mk Γ D) * (Groth.ι (IPRA.Q.mk Γ (tt A B D x y)) + Groth.ι (IPRA.Q.mk Γ A) * Groth.ι (IPRA.Q.mk Γ y) - Groth.ι (IPRA.Q.mk Γ B) * Groth.ι (IPRA.Q.mk Γ x)) * natEq et +
    (Groth.ι (IPRA.Q.mk Γ x) ^ 2 - Groth.ι (IPRA.Q.mk Γ D) * Groth.ι (IPRA.Q.mk Γ y) ^ 2) * natEq hA + natEq hx

/-! ## Negative `N = −K` -/

section Neg
variable {A B D K x y : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
  (hx : Γ ⊢[PRAAx] x * x + K ≐ D * (y * y))
include hA hx

theorem neg_t (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) :
    Γ ⊢[PRAAx] lt (B * x) (A * y) := by
  have hp := pos_mul (pos_mul hB hB) hK
  refine lt_of_sq_lt (le_of_eq_add (d := y * y + pred (B * B * K)) ?_)
  ipra_lc Groth.ι (IPRA.Q.mk Γ y) ^ 2 * natEq hA - Groth.ι (IPRA.Q.mk Γ B) ^ 2 * natEq hx + natEq hp

theorem neg_r (hD : Γ ⊢[PRAAx] D ≐ succ (pred D)) (hK : Γ ⊢[PRAAx] K ≐ succ (pred K))
    (hy : Γ ⊢[PRAAx] lt (A * K) y) : Γ ⊢[PRAAx] lt (D * (B * y)) (A * x) := by
  refine lt_of_sq_lt (le_of_eq_add (d := pred D * (y * y) + monus (y * y) (succ (A * A * K))) ?_)
  ipra_lc Groth.ι (IPRA.Q.mk Γ A) ^ 2 * natEq hx + Groth.ι (IPRA.Q.mk Γ D) * Groth.ι (IPRA.Q.mk Γ y) ^ 2 * natEq hA +
    natEq (eq_add_of_le (sq_gap hK hy)) + Groth.ι (IPRA.Q.mk Γ y) ^ 2 * natEq hD

theorem neg_y (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hD : Γ ⊢[PRAAx] D ≐ succ (pred D))
    (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) (hy : Γ ⊢[PRAAx] lt (A * K) y) :
    Γ ⊢[PRAAx] lt (pred A * y) (B * x) := by
  have hA2 : Γ ⊢[PRAAx] lt one A := by
    refine lt_of_sq_lt (le_of_eq_add (d := pred (D * (B * B))) ?_)
    have h₁ := natEq hA; have h₂ := natEq (pos_mul hD (pos_mul hB hB))
    apply deriveNat; ipra_simps
    linear_combination h₁ + h₂
  refine lt_of_sq_lt (le_of_eq_add (d := y * y + monus (y * y) (succ (A * A * K)) +
    K * succ (pred D * (B * B)) + two * (monus A (succ one) * (y * y))) ?_)
  have h₁ := natEq hA; have h₂ := natEq hx; have h₃ := natEq (eq_add_of_le (sq_gap hK hy))
  have h₄ := natEq hD; have h₅ := natEq (A_pos hA); have h₆ := natEq (eq_add_of_le hA2)
  apply deriveNat; ipra_simps
  linear_combination Groth.ι (IPRA.Q.mk Γ B) ^ 2 * h₂ - (Groth.ι (IPRA.Q.mk Γ y) ^ 2 - Groth.ι (IPRA.Q.mk Γ K)) * h₁ +
    h₃ + Groth.ι (IPRA.Q.mk Γ K) * Groth.ι (IPRA.Q.mk Γ B) ^ 2 * h₄ +
    (Groth.ι (IPRA.Q.mk Γ (pred A)) + Groth.ι (IPRA.Q.mk Γ A) - 1) * Groth.ι (IPRA.Q.mk Γ y) ^ 2 * h₅ +
    2 * Groth.ι (IPRA.Q.mk Γ y) ^ 2 * h₆

end Neg

/-- Lemma `lem:generaldescent`, `N = −K < 0`. -/
theorem gen_descent_neg {A B D K x y : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hD : Γ ⊢[PRAAx] D ≐ succ (pred D))
    (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) (hx : Γ ⊢[PRAAx] x * x + K ≐ D * (y * y))
    (hy : Γ ⊢[PRAAx] lt (A * K) y) :
    Γ ⊢[PRAAx] (rr A B D x y * rr A B D x y + K ≐ D * (tt A B D x y * tt A B D x y)) ⋏
      (le one (rr A B D x y) ⋏ le one (tt A B D x y) ⋏ lt (tt A B D x y) y ⋏
      (x ≐ A * rr A B D x y + D * (B * tt A B D x y)) ⋏ (y ≐ B * rr A B D x y + A * tt A B D x y)) := by
  have lr := neg_r hA hx hD hK hy
  have ht := neg_t hA hx hB hK
  refine .andI ?_ (assemble hA lr ht (neg_y hA hx hB hD hK hy))
  have er := ((eq_add_of_le (le_of_lt lr)).eqTrans (add_comm _ _)).eqSymm
  have et := ((eq_add_of_le (le_of_lt ht)).eqTrans (add_comm _ _)).eqSymm
  ipra_lc (Groth.ι (IPRA.Q.mk Γ (rr A B D x y)) + Groth.ι (IPRA.Q.mk Γ A) * Groth.ι (IPRA.Q.mk Γ x) - Groth.ι (IPRA.Q.mk Γ D) * Groth.ι (IPRA.Q.mk Γ B) * Groth.ι (IPRA.Q.mk Γ y)) * natEq er -
    Groth.ι (IPRA.Q.mk Γ D) * (Groth.ι (IPRA.Q.mk Γ (tt A B D x y)) + Groth.ι (IPRA.Q.mk Γ A) * Groth.ι (IPRA.Q.mk Γ y) - Groth.ι (IPRA.Q.mk Γ B) * Groth.ι (IPRA.Q.mk Γ x)) * natEq et +
    (Groth.ι (IPRA.Q.mk Γ x) ^ 2 - Groth.ι (IPRA.Q.mk Γ D) * Groth.ι (IPRA.Q.mk Γ y) ^ 2) * natEq hA + natEq hx

end LeanProofs.IPRA.DiophantineNumberTheory.PellGenDescent
