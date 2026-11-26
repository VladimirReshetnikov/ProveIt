import IPRADerivations.DiophantineNumberTheory.PellDescent
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# Negative descent for Pell's equation

Packet: `diophantine-number-theory/pell_ipra_2026-11-15`, Lemma `lem:negdescent`.

Let `A² = 1 + D B²` with `B ≥ 1`, `D ≥ 2`, and let `x² + 1 = D y²` (norm `−1`) with `y > B`. Then
`r = A x ∸ D B y` and `t = A y ∸ B x` are honest differences, and

* `r² + 1 = D t²`, `r ≥ 1`, `t ≥ 1`, `t < y`, `x = A r + D B t`, `y = B r + A t`.

The strict inequalities come from the square identities of the paper:
`(Ax)² − (DBy)² = D(y² − B²) − 1 ≥ 1`, `(Ay)² − (Bx)² = y² + B²` and
`(Bx)² − ((A − 1)y)² = 2(A − 1)y² − B²`, each written with an explicit nonnegative surplus.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellNegDescent

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.PellDescent (lt_of_sq_lt A_pos rr tt)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `A ≥ 2`. -/
theorem one_lt_A {A B D : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hD : Γ ⊢[PRAAx] le two D) : Γ ⊢[PRAAx] lt one A := by
  refine lt_of_sq_lt (le_of_eq_add (d := succ (two * pred (B * B)) + monus D two * succ (pred (B * B))) ?_)
  ipra_lc natEq hA + (1 + Groth.ι (IPRA.Q.mk Γ (pred (B * B)))) * natEq (eq_add_of_le hD) +
    Groth.ι (IPRA.Q.mk Γ D) * natEq (pos_mul hB hB)

/-- `D B y < A x`. -/
theorem lt_r {A B D x y : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (hx : Γ ⊢[PRAAx] x * x + one ≐ D * (y * y)) (hD : Γ ⊢[PRAAx] le two D) (hBy : Γ ⊢[PRAAx] lt B y) :
    Γ ⊢[PRAAx] lt (D * (B * y)) (A * x) := by
  refine lt_of_sq_lt (le_of_eq_add (d := two * (two * B + two * monus y (succ B) +
      two * (B * monus y (succ B)) + monus y (succ B) * monus y (succ B)) +
    monus D two * (succ (monus y (succ B)) * (succ (two * B) + monus y (succ B)))) ?_)
  ipra_lc Groth.ι (IPRA.Q.mk Γ x) ^ 2 * natEq hA +
    (1 + Groth.ι (IPRA.Q.mk Γ D) * Groth.ι (IPRA.Q.mk Γ B) ^ 2) * natEq hx +
    Groth.ι (IPRA.Q.mk Γ D) * (Groth.ι (IPRA.Q.mk Γ y) + Groth.ι (IPRA.Q.mk Γ B) + 1 + Groth.ι (IPRA.Q.mk Γ (monus y (succ B)))) * natEq (eq_add_of_le hBy) +
    (1 + Groth.ι (IPRA.Q.mk Γ (monus y (succ B)))) * (2 * Groth.ι (IPRA.Q.mk Γ B) + 1 + Groth.ι (IPRA.Q.mk Γ (monus y (succ B)))) * natEq (eq_add_of_le hD)

/-- `B x < A y`. -/
theorem lt_t' {A B D x y : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (hx : Γ ⊢[PRAAx] x * x + one ≐ D * (y * y)) (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) :
    Γ ⊢[PRAAx] lt (B * x) (A * y) := by
  refine lt_of_sq_lt (le_of_eq_add (d := y * y + pred (B * B)) ?_)
  ipra_lc Groth.ι (IPRA.Q.mk Γ y) ^ 2 * natEq hA - Groth.ι (IPRA.Q.mk Γ B) ^ 2 * natEq hx + natEq (pos_mul hB hB)

/-- `(A − 1) y < B x`. -/
theorem lt_y {A B D x y : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (hx : Γ ⊢[PRAAx] x * x + one ≐ D * (y * y)) (hB : Γ ⊢[PRAAx] B ≐ succ (pred B))
    (hD : Γ ⊢[PRAAx] le two D) (hBy : Γ ⊢[PRAAx] lt B y) :
    Γ ⊢[PRAAx] lt (pred A * y) (B * x) := by
  have hA2 := eq_add_of_le (one_lt_A hA hB hD)
  refine lt_of_sq_lt (le_of_eq_add (d := B * B + two * two * (B * succ (monus y (succ B))) +
      succ (two * two * monus y (succ B) + two * (monus y (succ B) * monus y (succ B))) +
      two * (monus A (succ one) * (y * y))) ?_)
  ipra_lc -Groth.ι (IPRA.Q.mk Γ y) ^ 2 * natEq hA + Groth.ι (IPRA.Q.mk Γ B) ^ 2 * natEq hx +
    (Groth.ι (IPRA.Q.mk Γ (pred A)) + Groth.ι (IPRA.Q.mk Γ A) - 1) * Groth.ι (IPRA.Q.mk Γ y) ^ 2 * natEq (A_pos hA) +
    2 * Groth.ι (IPRA.Q.mk Γ y) ^ 2 * natEq hA2 +
    2 * (Groth.ι (IPRA.Q.mk Γ y) + Groth.ι (IPRA.Q.mk Γ B) + 1 + Groth.ι (IPRA.Q.mk Γ (monus y (succ B)))) * natEq (eq_add_of_le hBy)

/-- Lemma `lem:negdescent`. -/
theorem neg_descent {A B D x y : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hD : Γ ⊢[PRAAx] le two D)
    (hx : Γ ⊢[PRAAx] x * x + one ≐ D * (y * y)) (hBy : Γ ⊢[PRAAx] lt B y) :
    Γ ⊢[PRAAx] (rr A B D x y * rr A B D x y + one ≐ D * (tt A B D x y * tt A B D x y)) ⋏
      le one (rr A B D x y) ⋏ le one (tt A B D x y) ⋏ lt (tt A B D x y) y ⋏
      (x ≐ A * rr A B D x y + D * (B * tt A B D x y)) ⋏ (y ≐ B * rr A B D x y + A * tt A B D x y) := by
  have lr := lt_r hA hx hD hBy
  have lt := lt_t' hA hx hB
  have er := ((eq_add_of_le (le_of_lt lr)).eqTrans (add_comm _ _)).eqSymm
  have et := ((eq_add_of_le (le_of_lt lt)).eqTrans (add_comm _ _)).eqSymm
  have h₁ := natEq hA; have h₂ := natEq hx; have h₃ := natEq er; have h₄ := natEq et
  refine .andI ?_ (.andI ?_ (.andI ?_ (.andI ?_ (.andI ?_ ?_))))
  · ipra_lc (Groth.ι (IPRA.Q.mk Γ (rr A B D x y)) + Groth.ι (IPRA.Q.mk Γ A) * Groth.ι (IPRA.Q.mk Γ x) - Groth.ι (IPRA.Q.mk Γ D) * Groth.ι (IPRA.Q.mk Γ B) * Groth.ι (IPRA.Q.mk Γ y)) * h₃ -
      Groth.ι (IPRA.Q.mk Γ D) * (Groth.ι (IPRA.Q.mk Γ (tt A B D x y)) + Groth.ι (IPRA.Q.mk Γ A) * Groth.ι (IPRA.Q.mk Γ y) - Groth.ι (IPRA.Q.mk Γ B) * Groth.ι (IPRA.Q.mk Γ x)) * h₄ +
      (Groth.ι (IPRA.Q.mk Γ x) ^ 2 - Groth.ι (IPRA.Q.mk Γ D) * Groth.ι (IPRA.Q.mk Γ y) ^ 2) * h₁ + h₂
  · refine le_of_eq_add (d := monus (A * x) (succ (D * (B * y)))) ?_
    have h₅ := natEq (eq_add_of_le lr)
    apply deriveNat; ipra_simps
    linear_combination h₃ + h₅
  · refine le_of_eq_add (d := monus (A * y) (succ (B * x))) ?_
    have h₅ := natEq (eq_add_of_le lt)
    apply deriveNat; ipra_simps
    linear_combination h₄ + h₅
  · have w := eq_add_of_le (lt_y hA hx hB hD hBy)
    refine le_of_eq_add (d := monus (B * x) (succ (pred A * y))) ?_
    have h₅ := natEq w; have h₆ := natEq (A_pos hA)
    apply deriveNat; ipra_simps
    linear_combination -h₄ + h₅ - Groth.ι (IPRA.Q.mk Γ y) * h₆
  · ipra_lc -Groth.ι (IPRA.Q.mk Γ x) * h₁ - Groth.ι (IPRA.Q.mk Γ A) * h₃ -
      Groth.ι (IPRA.Q.mk Γ D) * Groth.ι (IPRA.Q.mk Γ B) * h₄
  · ipra_lc -Groth.ι (IPRA.Q.mk Γ y) * h₁ - Groth.ι (IPRA.Q.mk Γ B) * h₃ - Groth.ι (IPRA.Q.mk Γ A) * h₄

end LeanProofs.IPRA.DiophantineNumberTheory.PellNegDescent
