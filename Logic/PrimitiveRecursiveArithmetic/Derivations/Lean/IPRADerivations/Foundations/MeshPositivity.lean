import IPRADerivations.Core.Division
import IPRADerivations.Core.Gcd
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Header

/-!
# A finite certificate of positivity on a mesh

Packet: `foundations/ipra_embedding_framework`, `paper/03_analysis.tex`, Proposition
`prop:mesh-positivity` ("A finite certificate of positivity"): if the approximants satisfy
`A(j/M, p) ≥ 3γ` at all grid points, with `|A − f| ≤ e_p ≤ γ` and a continuity modulus giving
`|f(x) − f(y)| ≤ 2^{−k} ≤ γ` at distance `1/M`, then `f(x) ≥ γ` throughout: "choose … the lower grid
point … The sup-norm distance is at most `1/M`. Each tested grid value of `f` is at least
`3γ − e_p ≥ 2γ`. The modulus then gives `f(x) ≥ 2γ − 2^{−k} ≥ γ`."

In one coordinate, for a rational point `x = u/v` (`v = v′ + 1`) and the mesh `M`:

* `gridIx u v′ M = ⌊uM/v⌋`, the lower grid index; `grid_lower`, `grid_upper`:
  `v j ≤ u M < v (j + 1)`, i.e. `j/M ≤ x < (j + 1)/M`, so the distance to the grid point is below `1/M`;
  `grid_le`: `u ≤ v` gives `j ≤ M`, so the grid point lies in the box (the endpoint `x = 1` gets the last
  index);
* `mesh_positive`: from `3γ ≤ A`, `A ≤ f(g) + e`, `e ≤ γ`, `f(g) ≤ f(x) + δ`, `δ ≤ γ` (values as
  numerators over a common denominator) one gets `γ ≤ f(x)`.

For `d` coordinates the grid index is taken in each coordinate. The represented evaluator, its modulus
and the quantification over all rational points are data of the application.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.MeshPositivity

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The lower grid index `⌊uM/v⌋` of `x = u/v`, `v = v′ + 1`. -/
abbrev gridIx (u v' M : PTm n) : PTm n := quo (u * M) (succ v')

/-- `v j ≤ u M`: the grid point is not above `x`. -/
theorem grid_lower (u v' M : PTm n) : Γ ⊢[PRAAx] le (succ v' * gridIx u v' M) (u * M) := by
  have d := natEq (Prf.andE₁ (div_mod (Γ := Γ) (u * M) v'))
  ipra_le 𝔟(rem (u * M) (succ v')) using linear_combination d

/-- `u M < v (j + 1)`: the next grid point is above `x`. -/
theorem grid_upper (u v' M : PTm n) :
    Γ ⊢[PRAAx] lt (u * M) (succ v' * succ (gridIx u v' M)) := by
  have dm := div_mod (Γ := Γ) (u * M) v'
  have d := natEq (Prf.andE₁ dm)
  have hr : Γ ⊢[PRAAx] le (succ (rem (u * M) (succ v'))) (succ v') := Prf.andE₂ dm
  have goal : Γ ⊢[PRAAx] le (succ (u * M)) (succ v' * succ (gridIx u v' M)) := by
    ipra_le sl hr using linear_combination -d
  exact goal

/-- `u ≤ v` gives `j ≤ M`: the grid point lies in `[0, 1]`. -/
theorem grid_le {u v' M : PTm n} (h : Γ ⊢[PRAAx] le u (succ v')) :
    Γ ⊢[PRAAx] le (gridIx u v' M) M := by
  have h₂ : Γ ⊢[PRAAx] le (u * M) (succ v' * M) := by
    ipra_le sl h * 𝔟 M
  exact mul_le_cancel (le_trans (grid_lower u v' M) h₂)

/-- `prop:mesh-positivity`, the estimate at one point. -/
theorem mesh_positive {γ A fg fx e δ : PTm n}
    (hA : Γ ⊢[PRAAx] le (num 3 * γ) A) (he : Γ ⊢[PRAAx] le A (fg + e))
    (heγ : Γ ⊢[PRAAx] le e γ) (hf : Γ ⊢[PRAAx] le fg (fx + δ)) (hδ : Γ ⊢[PRAAx] le δ γ) :
    Γ ⊢[PRAAx] le γ fx := by
  ipra_le sl hA + sl he + sl heγ + sl hf + sl hδ

end LeanProofs.IPRA.Foundations.MeshPositivity
