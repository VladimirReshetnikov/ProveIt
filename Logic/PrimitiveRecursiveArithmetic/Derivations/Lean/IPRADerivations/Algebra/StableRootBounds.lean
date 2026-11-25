import IPRADerivations.Foundations.FormalDerivation
import IPRADerivations.Foundations.ChainViability
import IPRADerivations.Probability.Variance
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.LinearCombination

/-!
# Grid rotations and the scalar square-root inequality

Packet: `algebra/ipra_stable_observables`:

* Proposition `prop:grid` (`paper/sections/04_jacobi.tex`): for the rotation entries
  `c(u) = (1 − u²)/(1 + u²)`, `s(u) = 2u/(1 + u²)`, "the exact rational identities
  `c(u) − c(v) = 2(v² − u²)/((1 + u²)(1 + v²))`, `s(u) − s(v) = 2(u − v)(1 − uv)/((1 + u²)(1 + v²))`
  give `|c(u) − c(v)|, |s(u) − s(v)| ≤ 4|u − v|`" for `|u|, |v| ≤ 1`;
* Theorem `thm:sqrtstable` (`paper/sections/06_square_roots.tex`), the scalar step: "For nonnegative
  rationals `s, t`, `|s − t| ≤ s + t`, so `(s − t)² ≤ |s² − t²|`."

* `cos_diff`, `sin_diff`: the two rational identities, as identities of fractions of integer
  polynomial expressions (`Foundations/FormalDerivation`, cleared of denominators);
* `ad_sq_diff`: for natural `k, j`, `|k² − j²| = |k − j| (k + j)`, with `|a − b| = (a ∸ b) + (b ∸ a)`;
* `cos_lipschitz`: for grid points `u = j/L`, `v = k/L` with `j, k ≤ L` (the case `0 ≤ u, v ≤ 1`),
  `2L² |k² − j²| · L ≤ 4 |j − k| (L² + j²)(L² + k²)`, i.e. `|c(u) − c(v)| ≤ 4 |u − v|` (the signs of
  `u, v` only change `c` by symmetry);
* `sqrt_scalar`: for natural `s, t`, `|s − t|² ≤ |s² − t²|`.

The matrix inequality `F(S − T)² ≤ n F(S² − T²)` in mixed orthogonal bases, the diagonalizer and the
fuel bound are not derived here; `Algebra/JacobiRotation` has the rotation algebra.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.StableRootBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Foundations.ChainViability (monus_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The rational identities of `prop:grid`

Variables `0 = u`, `1 = v`. -/

section Fractions

open ZExp

/-- `c(u) = (1 − u²)/(1 + u²)`. -/
abbrev cR (u : ZExp 2) : Frac 2 := ⟨1 - u ^ 2, 1 + u ^ 2⟩
/-- `s(u) = 2u/(1 + u²)`. -/
abbrev sR (u : ZExp 2) : Frac 2 := ⟨2 * u, 1 + u ^ 2⟩

/-- `c(u) − c(v) = 2(v² − u²)/((1 + u²)(1 + v²))`. -/
theorem cos_diff :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (Frac.eqn (cR (ZExp.var 0) - cR (ZExp.var 1))
        ⟨2 * (ZExp.var 1 ^ 2 - ZExp.var 0 ^ 2), (1 + ZExp.var 0 ^ 2) * (1 + ZExp.var 1 ^ 2)⟩)) :=
  derive_imp _ _ (by frac_poly R ρ h; ring)

/-- `s(u) − s(v) = 2(u − v)(1 − uv)/((1 + u²)(1 + v²))`. -/
theorem sin_diff :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (Frac.eqn (sR (ZExp.var 0) - sR (ZExp.var 1))
        ⟨2 * (ZExp.var 0 - ZExp.var 1) * (1 - ZExp.var 0 * ZExp.var 1), (1 + ZExp.var 0 ^ 2) * (1 + ZExp.var 1 ^ 2)⟩)) :=
  derive_imp _ _ (by frac_poly R ρ h; ring)

end Fractions

/-! ## The bounds -/

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem ad_sq_diff_of_le {j k : PTm n} (h : Γ ⊢[PRAAx] le j k) :
    Γ ⊢[PRAAx] ad (k * k) (j * j) ≐ ad k j * (k + j) := by
  ipra_lc -natEq (eq_add_of_le (sq_le_sq h)) + natEq (sq_le_sq h) + (𝔟 k + 𝔟 j) * natEq (eq_add_of_le h) -
    (𝔟 k + 𝔟 j) * natEq h

/-- `|k² − j²| = |k − j| (k + j)`. -/
theorem ad_sq_diff (j k : PTm n) : Γ ⊢[PRAAx] ad (k * k) (j * j) ≐ ad k j * (k + j) := by
  refine .orE (le_total j k) (ad_sq_diff_of_le Prf.hyp0) ?_
  ipra_lc natEq (ad_sq_diff_of_le (j := k) (k := j) (Γ := le k j :: Γ) Prf.hyp0)

/-- `prop:grid`: `|c(j/L) − c(k/L)| ≤ 4 |j/L − k/L|` for `j, k ≤ L`, cleared of denominators. -/
theorem cos_lipschitz {j k L : PTm n} (hj : Γ ⊢[PRAAx] le j L) (hk : Γ ⊢[PRAAx] le k L) :
    Γ ⊢[PRAAx] le (two * (L * L) * ad (k * k) (j * j) * L)
      (num 4 * ad j k * ((L * L + j * j) * (L * L + k * k))) := by
  have e := natEq (ad_sq_diff (Γ := Γ) j k)
  ipra_le 4 * (𝔟(monus k j) + 𝔟(monus j k)) * (𝔟 L * 𝔟 L * (𝔟 k * 𝔟 k) + 𝔟 j * 𝔟 j * (𝔟 L * 𝔟 L) +
      𝔟 j * 𝔟 j * (𝔟 k * 𝔟 k)) +
    2 * 𝔟 L * 𝔟 L * 𝔟 L * (𝔟(monus k j) + 𝔟(monus j k)) * (sl hk + sl hj) using
    linear_combination (-2 * 𝔟 L * 𝔟 L * 𝔟 L) * e

/-- `thm:sqrtstable`, the scalar step: `|s − t|² ≤ |s² − t²|` for natural `s, t`. -/
theorem sqrt_scalar (s t : PTm n) : Γ ⊢[PRAAx] le (ad s t * ad s t) (ad (s * s) (t * t)) := by
  have e := natEq (ad_sq_diff (Γ := Γ) t s)
  have h₁ := monus_le (Γ := Γ) s t
  have h₂ := monus_le (Γ := Γ) t s
  ipra_le (𝔟(monus s t) + 𝔟(monus t s)) * (sl h₁ + sl h₂) using linear_combination e

end LeanProofs.IPRA.Algebra.StableRootBounds
