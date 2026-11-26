import IPRADerivations.Core.Gcd
import IPRADerivations.Core.SumOrder

/-!
# The recursion step of the rational Brunn–Minkowski theorem

Packet: `geometry/isoperimetric_ipra_constructive_2026-11-15`, `report/euclidean.tex`,
`thm:rational-bm` ("Let `X, Y` be nonempty finite unions of rational boxes with disjoint
interiors, in dimension `n ≥ 1`, and let `q ≥ 0` be rational. Then
`q^n V(X) ≤ V(Y) ⟹ V(X + Y) ≥ V(X)(1 + q)^n`."). Its proof is a recursion on the total number
of boxes. The base case is `Geometry/BoxProduct.box_base`, the cut is `Geometry/RationalCut`,
and the numerical content of the step is derived here, with volumes as natural-number terms
(cleared of a common denominator), `q = Q/E`, the powers `Qn = Q^n`, `En = E^n`,
`Sn = (E + Q)^n` as arbitrary terms, and the volume fraction `λ = p/r`, `r ≥ 1`:

* `child_hyp` ("Hence the same hypothesis `q^n V(X^±) ≤ V(Y^±)` holds in both children"): from
  `r V(X⁻) = p V(X)`, `r V(Y⁻) = p V(Y)` and `Qn V(X) ≤ En V(Y)`: `Qn V(X⁻) ≤ En V(Y⁻)`;
* `combine` ("finite additivity of box volume allows their lower bounds to be added"): from
  `V(X) = V(X⁻) + V(X⁺)`, `V(X⁻ + Y⁻) + V(X⁺ + Y⁺) ≤ V(X + Y)` and the two inductive bounds
  `V(X^±) Sn ≤ En V(X^± + Y^±)`: `V(X) Sn ≤ En V(X + Y)`.

Not derived: the geometry of the step (clipping, the half-spaces `x_i ≤ s + t` and
`x_i ≥ s + t` containing the two sums, the count of boxes in the children) and the recursion
itself.
-/

namespace LeanProofs.IPRA.Geometry.RationalBrunnMinkowski

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The hypothesis passes to a child with the same volume fraction `p/r`. -/
theorem child_hyp {VX VY VXm VYm Qn En p r : PTm n} (hr : Γ ⊢[PRAAx] r ≐ succ (pred r))
    (hX : Γ ⊢[PRAAx] r * VXm ≐ p * VX) (hY : Γ ⊢[PRAAx] r * VYm ≐ p * VY)
    (H : Γ ⊢[PRAAx] le (Qn * VX) (En * VY)) : Γ ⊢[PRAAx] le (Qn * VXm) (En * VYm) := by
  refine mul_le_cancel (d' := pred r) (le_of_eq_add (d := p * monus (En * VY) (Qn * VX)) ?_)
  ipra_lc (𝔞 En * 𝔞 VYm - 𝔞 Qn * 𝔞 VXm) * (-natEq hr) + 𝔞 En * natEq hY - 𝔞 Qn * natEq hX +
    𝔞 p * natEq (eq_add_of_le H)

/-- The two lower bounds add. -/
theorem combine {VX VXm VXp Wm Wp W En Sn : PTm n} (hX : Γ ⊢[PRAAx] VX ≐ VXm + VXp)
    (hW : Γ ⊢[PRAAx] le (Wm + Wp) W) (im : Γ ⊢[PRAAx] le (VXm * Sn) (En * Wm))
    (ip : Γ ⊢[PRAAx] le (VXp * Sn) (En * Wp)) : Γ ⊢[PRAAx] le (VX * Sn) (En * W) := by
  refine le_of_eq_add (d := monus (En * Wm) (VXm * Sn) + monus (En * Wp) (VXp * Sn) +
    En * monus W (Wm + Wp)) ?_
  ipra_lc 𝔞 En * natEq (eq_add_of_le hW) + natEq (eq_add_of_le im) + natEq (eq_add_of_le ip) - 𝔞 Sn * natEq hX

end LeanProofs.IPRA.Geometry.RationalBrunnMinkowski
