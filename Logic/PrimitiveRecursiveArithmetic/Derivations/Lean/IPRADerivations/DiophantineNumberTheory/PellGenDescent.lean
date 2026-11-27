import IPRADerivations.DiophantineNumberTheory.PellNegDescent

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

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellGenDescent

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.PellDescent (lt_of_sq_lt A_pos rr tt residual_norm_balance positive_residual)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `A²K < y²` from `AK < y` and `K ≥ 1`. -/
theorem sq_gap {A K y : PTm n} (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) (hy : Γ ⊢[PRAAx] lt (A * K) y) :
    Γ ⊢[PRAAx] lt (A * A * K) (y * y) := by
  refine lt_of_le_of_lt ?_ (Common.sq_lt_sq hy)
  exact le_congr (Common.mul_one_right _) (by ipra_ring)
    (mul_le_mul_left (A * A * K) (Common.one_le_of_pos hK))

/-- The shared tail of both descents: positivity, `t < y`, reconstruction. -/
theorem assemble {A B D x y : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (lr : Γ ⊢[PRAAx] lt (D * (B * y)) (A * x)) (ht : Γ ⊢[PRAAx] lt (B * x) (A * y))
    (ly : Γ ⊢[PRAAx] lt (pred A * y) (B * x)) :
    Γ ⊢[PRAAx] le one (rr A B D x y) ⋏ le one (tt A B D x y) ⋏ lt (tt A B D x y) y ⋏
      (x ≐ A * rr A B D x y + D * (B * tt A B D x y)) ⋏ (y ≐ B * rr A B D x y + A * tt A B D x y) :=
  positive_residual hA lr ht ly

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
  ipra_lc natEq (residual_norm_balance hA (le_of_lt lr) (le_of_lt ht)) + natEq hx

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
    ipra_lc natEq hA + natEq (pos_mul hD (pos_mul hB hB))
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
  ipra_lc natEq (residual_norm_balance hA (le_of_lt lr) (le_of_lt ht)) + natEq hx

end LeanProofs.IPRA.DiophantineNumberTheory.PellGenDescent
