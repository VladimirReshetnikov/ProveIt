import IPRADerivations.Probability.Variance
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# Dyadic energy identities

Packet: `foundations/ipra_measure_transport_2026-11-20`, `lean/Energy.lean` (host-level Lean over `ℚ` there; "the
object-iPRA translation remains a separate task"): `dyadic_energy_identity`, `dyadic_residual_identity`,
`dyadic_energy_monotone`, `weighted_square_expansion` and `finite_orthogonal_energy`.

Object-level derivations, cleared of the denominators `2` and `4` of the averages:

* `energy_identity`: `2(a² + b²) = (a + b)² + (a − b)²` (`(a² + b²)/2 = mean² + detail`);
* `residual_identity`: `(2a − (a + b))² + (2b − (a + b))² = 2 (a − b)²`;
* `energy_monotone`: `(a + b)² ≤ 2(a² + b²)` for natural `a, b`, with slack `|a − b|²`;
* `square_expansion`: `∑ w (f − g)² = ∑ w f² + ∑ w g² − 2 ∑ w f g` on a finite list of cells (integer terms);
* `orthogonal_energy`: if `∑ w f g = ∑ w g²` (the finite cell-average orthogonality) then
  `∑ w (f − g)² = ∑ w f² − ∑ w g²`, the conditional-expectation energy identity.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.DyadicEnergy

open_ipra
open LeanProofs.IPRA.Probability.Variance (ad ad_sq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem energy_identity (a b : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * (a * a + b * b)) ((a + b) * (a + b) + (a - b) * (a - b)) := by
  ipra_lc

theorem residual_identity (a b : ZT n) :
    Γ ⊢[PRAAx] ZT.eq ((ZT.natLit 2 * a - (a + b)) * (ZT.natLit 2 * a - (a + b)) +
        (ZT.natLit 2 * b - (a + b)) * (ZT.natLit 2 * b - (a + b)))
      (ZT.natLit 2 * ((a - b) * (a - b))) := by
  ipra_lc

theorem energy_monotone (a b : PTm n) : Γ ⊢[PRAAx] le ((a + b) * (a + b)) (two * (a * a + b * b)) := by
  have e := natEq (ad_sq (Γ := Γ) a b)
  ipra_le 𝔟 (ad a b) ^ 2 with e

variable {α : Type}

/-- `∑ f` over a finite list of cells, for integer terms. -/
def zsum (f : α → ZT n) : List α → ZT n
  | [] => ZT.natLit 0
  | r :: rs => f r + zsum f rs

/-- `∑ w (f − g)² = ∑ w f² + ∑ w g² − 2 ∑ w f g`. -/
theorem square_expansion (w f g : α → ZT n) (L : List α) :
    Γ ⊢[PRAAx] ZT.eq (zsum (fun r => w r * ((f r - g r) * (f r - g r))) L)
      (zsum (fun r => w r * (f r * f r)) L + zsum (fun r => w r * (g r * g r)) L -
        ZT.natLit 2 * zsum (fun r => w r * (f r * g r)) L) := by
  apply ZT.derive
  induction L with
  | nil => simp [zsum, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit]
  | cons r rs ih =>
    simp only [zsum, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit] at ih ⊢
    push_cast at ih ⊢
    linear_combination ih

/-- `∑ w f g = ∑ w g²` gives `∑ w (f − g)² = ∑ w f² − ∑ w g²`. -/
theorem orthogonal_energy (w f g : α → ZT n) (L : List α)
    (hcross : Γ ⊢[PRAAx] ZT.eq (zsum (fun r => w r * (f r * g r)) L) (zsum (fun r => w r * (g r * g r)) L)) :
    Γ ⊢[PRAAx] ZT.eq (zsum (fun r => w r * ((f r - g r) * (f r - g r))) L)
      (zsum (fun r => w r * (f r * f r)) L - zsum (fun r => w r * (g r * g r)) L) := by
  ipra_lc ZT.toZ_eq (square_expansion (Γ := Γ) w f g L) - 2 * ZT.toZ_eq hcross

end LeanProofs.IPRA.Foundations.DyadicEnergy
