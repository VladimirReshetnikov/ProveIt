import IPRADerivations.DiophantineNumberTheory.Coprime
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.Header

/-!
# Positive unit descent for Pell's equation

Packet: `diophantine-number-theory/pell_ipra_2026-11-15`, Lemma `lem:unitdescent`.

Let `A² = 1 + D B²` with `B ≥ 1`, and let `x² = 1 + D y²` with `y ≥ B`. Then
`r = A x ∸ D B y` and `t = A y ∸ B x` are honest differences, and

* `r² = 1 + D t²`, `t < y`, `x = A r + D B t`, `y = B r + A t`.

The inequalities come from exact square identities, as in the paper:
`(Ax)² = (DBy)² + (1 + Dy² + DB²)`, `(Ay)² = (Bx)² + (y - B)(y + B)` and
`(Bx)² = ((A - 1) y)² + B² + 2 (A - 1) y²`, together with `le_of_sq_le`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellDescent

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `a² < b² → a < b`. -/
alias lt_of_sq_lt := Common.lt_of_sq_lt

theorem A_pos {A B D : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B)) : Γ ⊢[PRAAx] A ≐ succ (pred A) := by
  refine .orE (zero_or_succ A) ?_ Prf.hyp0
  refine succ_ne_zero' _ (a := D * (B * B)) ((hA.wk.eqSymm.eqTrans ((congrMul Prf.hyp0 Prf.hyp0).eqTrans
    (mul_zero _))).eqSymm.eqTrans ?_ |>.eqSymm)
  exact (by ipra_ring)

/-- `D B y ≤ A x`. -/
theorem le_r {A B D x y : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (hx : Γ ⊢[PRAAx] x * x ≐ one + D * (y * y)) : Γ ⊢[PRAAx] le (D * (B * y)) (A * x) := by
  refine le_of_sq_le (le_of_eq_add (d := one + D * (y * y) + D * (B * B)) ?_)
  ipra_lc (1 + Groth.ι (IPRA.Q.mk Γ D) * Groth.ι (IPRA.Q.mk Γ y) ^ 2) * natEq hA +
    Groth.ι (IPRA.Q.mk Γ A) ^ 2 * natEq hx

/-- `B x ≤ A y` when `B ≤ y`. -/
theorem le_t {A B D x y : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (hx : Γ ⊢[PRAAx] x * x ≐ one + D * (y * y)) (hBy : Γ ⊢[PRAAx] le B y) :
    Γ ⊢[PRAAx] le (B * x) (A * y) := by
  have e := eq_add_of_le hBy
  refine le_of_sq_le (le_of_eq_add (d := monus y B * (monus y B + two * B)) ?_)
  ipra_lc Groth.ι (IPRA.Q.mk Γ y) ^ 2 * natEq hA - Groth.ι (IPRA.Q.mk Γ B) ^ 2 * natEq hx +
    (Groth.ι (IPRA.Q.mk Γ y) + Groth.ι (IPRA.Q.mk Γ B) + Groth.ι (IPRA.Q.mk Γ (monus y B))) * natEq e

/-- `(A - 1) y < B x` when `B ≥ 1`. -/
theorem lt_t {A B D x y : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (hx : Γ ⊢[PRAAx] x * x ≐ one + D * (y * y)) (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) :
    Γ ⊢[PRAAx] lt (pred A * y) (B * x) := by
  have hAp := A_pos hA
  refine lt_of_sq_lt (le_of_eq_add (d := pred (B * B) + two * (pred A * (y * y))) ?_)
  ipra_lc Groth.ι (IPRA.Q.mk Γ B) ^ 2 * natEq hx - Groth.ι (IPRA.Q.mk Γ y) ^ 2 * natEq hA +
    Groth.ι (IPRA.Q.mk Γ y) ^ 2 * (Groth.ι (IPRA.Q.mk Γ A) + Groth.ι (IPRA.Q.mk Γ (pred A)) + 1) * natEq hAp +
    natEq (pos_mul hB hB)

/-- The residual `(r, t)`. -/
abbrev rr (A B D x y : PTm n) : PTm n := monus (A * x) (D * (B * y))
abbrev tt (A B _D x y : PTm n) : PTm n := monus (A * y) (B * x)

/-- Lemma `lem:unitdescent`. -/
theorem unit_descent {A B D x y : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hx : Γ ⊢[PRAAx] x * x ≐ one + D * (y * y))
    (hBy : Γ ⊢[PRAAx] le B y) :
    Γ ⊢[PRAAx] (rr A B D x y * rr A B D x y ≐ one + D * (tt A B D x y * tt A B D x y)) ⋏
      lt (tt A B D x y) y ⋏ (x ≐ A * rr A B D x y + D * (B * tt A B D x y)) ⋏
      (y ≐ B * rr A B D x y + A * tt A B D x y) := by
  have er := ((eq_add_of_le (le_r hA hx)).eqTrans (add_comm _ _)).eqSymm
  have et := ((eq_add_of_le (le_t hA hx hBy)).eqTrans (add_comm _ _)).eqSymm
  have h₁ := natEq hA; have h₂ := natEq hx; have h₃ := natEq er; have h₄ := natEq et
  refine .andI ?_ (.andI ?_ (.andI ?_ ?_))
  · ipra_lc (Groth.ι (IPRA.Q.mk Γ (rr A B D x y)) + Groth.ι (IPRA.Q.mk Γ A) * Groth.ι (IPRA.Q.mk Γ x) - Groth.ι (IPRA.Q.mk Γ D) * Groth.ι (IPRA.Q.mk Γ B) * Groth.ι (IPRA.Q.mk Γ y)) * h₃ -
      Groth.ι (IPRA.Q.mk Γ D) * (Groth.ι (IPRA.Q.mk Γ (tt A B D x y)) + Groth.ι (IPRA.Q.mk Γ A) * Groth.ι (IPRA.Q.mk Γ y) - Groth.ι (IPRA.Q.mk Γ B) * Groth.ι (IPRA.Q.mk Γ x)) * h₄ +
      (Groth.ι (IPRA.Q.mk Γ x) ^ 2 - Groth.ι (IPRA.Q.mk Γ D) * Groth.ι (IPRA.Q.mk Γ y) ^ 2) * h₁ + h₂
  · -- `t + B x = A y` and `(A - 1) y + 1 ≤ B x`.
    have l := lt_t hA hx hB
    have w := eq_add_of_le l
    refine le_of_eq_add (d := monus (B * x) (succ (pred A * y))) ?_
    ipra_lc -h₄ + natEq w - Groth.ι (IPRA.Q.mk Γ y) * natEq (A_pos hA)
  · ipra_lc -Groth.ι (IPRA.Q.mk Γ x) * h₁ - Groth.ι (IPRA.Q.mk Γ A) * h₃ -
      Groth.ι (IPRA.Q.mk Γ D) * Groth.ι (IPRA.Q.mk Γ B) * h₄
  · ipra_lc -Groth.ι (IPRA.Q.mk Γ y) * h₁ - Groth.ι (IPRA.Q.mk Γ B) * h₃ - Groth.ι (IPRA.Q.mk Γ A) * h₄

end LeanProofs.IPRA.DiophantineNumberTheory.PellDescent
