import IPRADerivations.DiophantineNumberTheory.Coprime

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

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellDescent

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `a² < b² → a < b`. -/
alias lt_of_sq_lt := Common.lt_of_sq_lt

theorem A_pos {A B D : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B)) : Γ ⊢[PRAAx] A ≐ succ (pred A) :=
  Common.pos_of_one_le (le_of_sq_le
    (le_congr (Common.mul_one_right one).eqSymm hA.eqSymm (le_add_right one _)))

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

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

/-- A norm-one unit preserves the cross-sum expression for the residual norm. -/
theorem residual_norm_balance {A B D x y : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (lr : Γ ⊢[PRAAx] le (D * (B * y)) (A * x)) (lt' : Γ ⊢[PRAAx] le (B * x) (A * y)) :
    Γ ⊢[PRAAx] rr A B D x y * rr A B D x y + D * (y * y) ≐
      x * x + D * (tt A B D x y * tt A B D x y) := by
  have er := ((eq_add_of_le lr).eqTrans (add_comm _ _)).eqSymm
  have et := ((eq_add_of_le lt').eqTrans (add_comm _ _)).eqSymm
  ipra_lc (𝔞 (rr A B D x y) + 𝔞 A * 𝔞 x - 𝔞 D * 𝔞 B * 𝔞 y) * natEq er -
    𝔞 D * (𝔞 (tt A B D x y) + 𝔞 A * 𝔞 y - 𝔞 B * 𝔞 x) * natEq et +
    (𝔞 x ^ 2 - 𝔞 D * 𝔞 y ^ 2) * natEq hA

/-- The residual is smaller in its second coordinate and multiplication by the unit recovers the input. -/
theorem residual_reconstruction {A B D x y : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (lr : Γ ⊢[PRAAx] le (D * (B * y)) (A * x)) (lt' : Γ ⊢[PRAAx] le (B * x) (A * y))
    (ly : Γ ⊢[PRAAx] lt (pred A * y) (B * x)) :
    Γ ⊢[PRAAx] lt (tt A B D x y) y ⋏ (x ≐ A * rr A B D x y + D * (B * tt A B D x y)) ⋏
      (y ≐ B * rr A B D x y + A * tt A B D x y) := by
  have er := ((eq_add_of_le lr).eqTrans (add_comm _ _)).eqSymm
  have et := ((eq_add_of_le lt').eqTrans (add_comm _ _)).eqSymm
  refine .andI ?_ (.andI ?_ ?_)
  · refine le_of_eq_add (d := monus (B * x) (succ (pred A * y))) ?_
    ipra_lc -natEq et + natEq (eq_add_of_le ly) - 𝔞 y * natEq (A_pos hA)
  · ipra_lc -𝔞 x * natEq hA - 𝔞 A * natEq er - 𝔞 D * 𝔞 B * natEq et
  · ipra_lc -𝔞 y * natEq hA - 𝔞 B * natEq er - 𝔞 A * natEq et

/-- Strict difference bounds make both residual coordinates positive. -/
theorem positive_residual {A B D x y : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (lr : Γ ⊢[PRAAx] lt (D * (B * y)) (A * x)) (lt' : Γ ⊢[PRAAx] lt (B * x) (A * y))
    (ly : Γ ⊢[PRAAx] lt (pred A * y) (B * x)) :
    Γ ⊢[PRAAx] le one (rr A B D x y) ⋏ le one (tt A B D x y) ⋏ lt (tt A B D x y) y ⋏
      (x ≐ A * rr A B D x y + D * (B * tt A B D x y)) ⋏ (y ≐ B * rr A B D x y + A * tt A B D x y) :=
  .andI (Common.one_le_monus_of_lt _ _ lr) (.andI (Common.one_le_monus_of_lt _ _ lt')
    (residual_reconstruction hA (le_of_lt lr) (le_of_lt lt') ly))

/-- Lemma `lem:unitdescent`. -/
theorem unit_descent {A B D x y : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hx : Γ ⊢[PRAAx] x * x ≐ one + D * (y * y))
    (hBy : Γ ⊢[PRAAx] le B y) :
    Γ ⊢[PRAAx] (rr A B D x y * rr A B D x y ≐ one + D * (tt A B D x y * tt A B D x y)) ⋏
      lt (tt A B D x y) y ⋏ (x ≐ A * rr A B D x y + D * (B * tt A B D x y)) ⋏
      (y ≐ B * rr A B D x y + A * tt A B D x y) := by
  have lr := le_r hA hx
  have lt' := le_t hA hx hBy
  refine .andI ?_ (residual_reconstruction hA lr lt' (lt_t hA hx hB))
  ipra_lc natEq (residual_norm_balance hA lr lt') + natEq hx

end LeanProofs.IPRA.DiophantineNumberTheory.PellDescent

export_ipra DiophantineNumberTheory.PellDescent (lt_of_sq_lt)
