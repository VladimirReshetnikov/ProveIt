import IPRADerivations.DiophantineNumberTheory.SquareArea

/-!
# The rational points of `y² = x³ − x`

Packet: `diophantine-number-theory/mordell_weil_ipra` (`thm:e1`): every affine rational point of
`E₁ : y² = x³ − x` has `y = 0`, so `E₁(ℚ) = {O, (0, 0), (1, 0), (−1, 0)}`.

A point with `y ≠ 0` has `x ≠ 0, ±1`. Write `x = ±a/b` and `y = ±c/e` with `a, b, c, e ≥ 1`, and let
`D ≥ 1` be `|a² − b²|`, so that `a² + D = b²` (for `|x| < 1`) or `b² + D = a²` (for `|x| > 1`). The
curve equation is then `a D e² = c² b³` (the sign of `x` is the sign of `x² − 1`, since
`x³ − x = y² > 0`). The packet's triangle `(6.10)`, cleared of the denominator `b² c / e`, is

  `(D e, 2 a b e, (a² + b²) e)` with area `a b D e² = b (b² c)²`, i.e. `A B = 2 (b² c)²`,

a right triangle with square area (`thm:no-square-area`).

* `no_tri`: `DiophantineNumberTheory/SquareArea` in an arbitrary context;
* `e1_tri`: the triangle above;
* `e1_no_point`: no point with `y ≠ 0`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.EllipticE1

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Pythagoras (two_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.SquareArea (tri mk_tri chiF chi_of_tri hyps)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `thm:no-square-area` in any context. -/
theorem no_tri {A B C S : PTm n} (ht : Γ ⊢[PRAAx] tri A B C S) : Γ ⊢[PRAAx] Fm.bot := by
  have d := inst (Γ := Γ) (.impI (DescentEx.descent hyps)) (![pairT A (pairT B S), C] : Fin 2 → PTm n)
  simp only [Fm.subst_imp, Fm.subst_eq, subst_inst2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
    Fm.subst_bot] at d
  exact .impE d (chi_of_tri ht)

/-- The triangle of a point with `y ≠ 0`. -/
theorem e1_tri {a b c e D : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hc : Γ ⊢[PRAAx] c ≐ succ (pred c)) (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) (hD : Γ ⊢[PRAAx] D ≐ succ (pred D))
    (hab : Γ ⊢[PRAAx] (a * a + D ≐ b * b) ⋎ (b * b + D ≐ a * a))
    (hE : Γ ⊢[PRAAx] a * D * (e * e) ≐ (c * c) * (b * b * b)) :
    Γ ⊢[PRAAx] tri (D * e) (two * a * b * e) ((a * a + b * b) * e) (b * b * c) := by
  refine mk_tri (pos_mul hD he) (pos_mul (pos_mul (pos_mul two_pos ha) hb) he) (pos_mul (pos_mul hb hb) hc) ?_ ?_
  · refine .orE hab ?_ ?_
    · have f := natEq (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := a * a + D ≐ b * b))
      apply deriveNat; ipra_simps
      linear_combination (𝔞 e) ^ 2 * (𝔞 D + 𝔞 b ^ 2 - 𝔞 a ^ 2) * f
    · have f := natEq (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := b * b + D ≐ a * a))
      apply deriveNat; ipra_simps
      linear_combination (𝔞 e) ^ 2 * (𝔞 D + 𝔞 a ^ 2 - 𝔞 b ^ 2) * f
  · have f := natEq hE
    apply deriveNat; ipra_simps
    linear_combination 2 * 𝔞 b * f

/-- `thm:e1`: no rational point of `y² = x³ − x` has `y ≠ 0`. With `x = ±a/b`, `y = ±c/e`,
`D = |a² − b²|`, all at least `1`, the curve equation `a D e² = c² b³` is impossible. -/
theorem e1_no_point {a b c e D : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hc : Γ ⊢[PRAAx] c ≐ succ (pred c)) (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) (hD : Γ ⊢[PRAAx] D ≐ succ (pred D))
    (hab : Γ ⊢[PRAAx] (a * a + D ≐ b * b) ⋎ (b * b + D ≐ a * a))
    (hE : Γ ⊢[PRAAx] a * D * (e * e) ≐ (c * c) * (b * b * b)) : Γ ⊢[PRAAx] Fm.bot :=
  no_tri (e1_tri ha hb hc he hD hab hE)

end LeanProofs.IPRA.DiophantineNumberTheory.EllipticE1
