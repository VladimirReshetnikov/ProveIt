import IPRADerivations.Core.SumLemmas
import IPRADerivations.Core.OrderCertificates

/-!
# The finite identity for `∑ (n + 1) zⁿ`

Packet: `analysis/hypergeometric_ipra_2026-11-16`, `sections/06_special.tex`, Corollary "Geometric
cases": "for `₂F₁(1, 2; 1; z)`, the coefficient is `n + 1`, and the finite identity
`(1 − z)² ∑_{n<N} (n + 1) zⁿ = 1 − (N + 1) z^N + N z^{N+1}` supplies an explicit remainder."

For a natural `z = y + 1` (so `(1 − z)² = y²`) and with the subtracted term moved across:

* `gB`: the term `(n + 1) zⁿ`;
* `geometric_square`: `y² ∑_{n<N} (n + 1) zⁿ + (N + 1) z^N = 1 + N z^{N+1}`, by quantifier-free
  induction on `N`.

The identity is polynomial in `z`, and the natural values `z ≥ 1` are the instance with all terms
nonnegative. The remainder estimate on a disk is not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GeometricSquareSum

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `(n + 1) zⁿ`; variables `0 = n`, `1 = z`. -/
def gB : PTm 2 := succ (var 0) * pw (var 1) (var 0)

theorem inst2_gB (k z : PTm n) : inst2 gB k z = succ k * pw z k := by
  simp [inst2, gB]

theorem gs_base (y : PTm n) :
    Γ ⊢[PRAAx] y * y * ap2 (sumF gB) zero (succ y) + succ zero * pw (succ y) zero ≐
      one + zero * pw (succ y) (succ zero) := by
  ipra_lc 𝔟 y * 𝔟 y * natEq (sum_zero (Γ := Γ) gB (succ y)) + natEq (pw_zero (Γ := Γ) (succ y))

theorem gs_step {N y : PTm n}
    (ih : Γ ⊢[PRAAx] y * y * ap2 (sumF gB) N (succ y) + succ N * pw (succ y) N ≐
      one + N * pw (succ y) (succ N)) :
    Γ ⊢[PRAAx] y * y * ap2 (sumF gB) (succ N) (succ y) + succ (succ N) * pw (succ y) (succ N) ≐
      one + succ N * pw (succ y) (succ (succ N)) := by
  have s := sum_succ' (Γ := Γ) gB N (succ y)
  rw [inst2_gB] at s
  ipra_lc 𝔟 y * 𝔟 y * natEq s + natEq ih + (𝔟 N + 1) * (1 - 𝔟 y) * natEq (pw_succ (Γ := Γ) (succ y) N) -
    (𝔟 N + 1) * natEq (pw_succ (Γ := Γ) (succ y) (succ N))

/-- Variables: `0 = N`, `1 = y`. -/
private abbrev gsF : Fm PTm 2 :=
  var 1 * var 1 * ap2 (sumF gB) (var 0) (succ (var 1)) + succ (var 0) * pw (succ (var 1)) (var 0) ≐
    one + var 0 * pw (succ (var 1)) (succ (var 0))

private theorem gs₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] gsF := by
  refine ind _ trivial ?_ ?_
  · have e : gsF.subst (Syn.inst zero) =
        (var 0 * var 0 * ap2 (sumF gB) zero (succ (var 0)) + succ zero * pw (succ (var 0)) zero ≐
          one + zero * pw (succ (var 0)) (succ zero) : Fm PTm 1) := by
      simp
    rw [e]
    exact gs_base _
  · have e : gsF.subst (repl (succ (var 0))) =
        (var 1 * var 1 * ap2 (sumF gB) (succ (var 0)) (succ (var 1)) +
            succ (succ (var 0)) * pw (succ (var 1)) (succ (var 0)) ≐
          one + succ (var 0) * pw (succ (var 1)) (succ (succ (var 0))) : Fm PTm 2) := by
      simp
    rw [e]
    exact gs_step Prf.hyp0

/-- `y² ∑_{n<N} (n + 1) zⁿ + (N + 1) z^N = 1 + N z^{N+1}` for `z = y + 1`. -/
theorem geometric_square (N y : PTm n) :
    Γ ⊢[PRAAx] y * y * ap2 (sumF gB) N (succ y) + succ N * pw (succ y) N ≐
      one + N * pw (succ y) (succ N) := by
  have h := inst (Γ := Γ) gs₀ (![N, y] : Fin 2 → PTm n)
  simpa using h

end LeanProofs.IPRA.Analysis.GeometricSquareSum
