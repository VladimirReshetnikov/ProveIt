import IPRADerivations.Foundations.RationalRootConstant
import IPRADerivations.Core.ProdLemmas

/-!
# A rational eigenvalue lies on a finite grid (`ipra_presentations_to_witnesses`, `cor:eigenvalue-grid`)

Packet: `foundations/ipra_presentations_to_witnesses`, corollary `cor:eigenvalue-grid`: for a
rational matrix `M` with integer multiple `A = Δ M`, `Δ > 0`, an eigenvalue `x` satisfies
`x = z / Δ` with `z ∈ ℤ`, `|z| ≤ R(A)`; "in particular, if `x = a/q` is reduced with `q > 0`,
then `q ∣ Δ`, `q ≤ Δ`, and `|a| ≤ R(A)`."

The integer `z = Δ x` and its bound are `lem:integer-eigenvalue`
(`Foundations/EigenvalueIntegral`, `Foundations/EigenvalueBound`). This module derives the "in
particular" part from the equation `z q = Δ a` (that is, `z / Δ = a / q`), in natural-number
form with `Z = |z|`, `La = |a|`, `q = q' + 1`, `Δ = Δ' + 1`:

* `grid_den_dvd`: `q ∣ Δ`, by Euclid's lemma for the coprime pair `(q, La)`;
* `grid_den_le`: `q ≤ Δ`;
* `mul_cancel`: cancellation of a positive factor in an equation;
* `grid_num_le`: `La ≤ Z`, hence `La ≤ R` whenever `Z ≤ R`.

So a reduced eigenvalue has denominator dividing `Δ` and numerator bounded by `R(A)`: the
finite grid of the packet. The case `z = 0` needs no separate treatment (`La ≤ Z` is then
`La = 0`).
-/

namespace LeanProofs.IPRA.Foundations.EigenvalueGrid

open_ipra exports
open LeanProofs.IPRA.Foundations.RationalRootConstant (dvd_le)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- The reduced denominator divides `Δ`. -/
theorem grid_den_dvd {q' Δ' La Z u v : PTm k} (hB : Γ ⊢[PRAAx] Bez q' La u v)
    (hE : Γ ⊢[PRAAx] Z * succ q' ≐ succ Δ' * La) : Γ ⊢[PRAAx] dvd (succ q') (succ Δ') :=
  euclid hB (dvd_of_eq (w := Z) (hE.eqSymm.eqTrans (mul_comm _ _)))

/-- The reduced denominator is at most `Δ`. -/
theorem grid_den_le {q' Δ' La Z u v : PTm k} (hB : Γ ⊢[PRAAx] Bez q' La u v)
    (hE : Γ ⊢[PRAAx] Z * succ q' ≐ succ Δ' * La) : Γ ⊢[PRAAx] le (succ q') (succ Δ') :=
  dvd_le (grid_den_dvd hB hE) (pos_of_eq_succ (c := Δ') (.eqRefl _))

/-- Cancellation of a positive factor in an equation. -/
theorem mul_cancel {d' a b : PTm k} (h : Γ ⊢[PRAAx] succ d' * a ≐ succ d' * b) :
    Γ ⊢[PRAAx] a ≐ b :=
  le_antisymm (mul_le_cancel (le_congr (.eqRefl _) h (le_refl _)))
    (mul_le_cancel (le_congr h (.eqRefl _) (le_refl _)))

/-- The reduced numerator is at most `|z|`. -/
theorem grid_num_le {q' Δ' La Z u v : PTm k} (hB : Γ ⊢[PRAAx] Bez q' La u v)
    (hE : Γ ⊢[PRAAx] Z * succ q' ≐ succ Δ' * La) : Γ ⊢[PRAAx] le La Z := by
  have hd := eq_of_dvd (grid_den_dvd hB hE)
  -- `Z = t La` with `t = ⌊Δ / q⌋`
  have hz : Γ ⊢[PRAAx] Z ≐ quo (succ Δ') (succ q') * La := by
    refine mul_cancel (d' := q') ?_
    have e₁ := natEq hE
    ipra_lc e₁ + 𝔞 La * natEq hd
  refine .orE (zero_or_succ (quo (succ Δ') (succ q'))) ?_ ?_
  · -- `t = 0` would make `Δ` zero
    have e₂ := natEq (hd.wk (ψ := quo (succ Δ') (succ q') ≐ zero))
    have c0 : ((quo (succ Δ') (succ q') ≐ zero) :: Γ) ⊢[PRAAx] succ Δ' ≐ zero := by
      ipra_lc e₂ + (𝔞 q' + 1) * natEq (Prf.hyp0 (φ := quo (succ Δ') (succ q') ≐ zero))
    exact succ_ne_zero' _ c0
  · have s := natEq (Prf.hyp0 (Γ := Γ)
      (φ := quo (succ Δ') (succ q') ≐ succ (pred (quo (succ Δ') (succ q')))))
    have e := natEq (hz.wk
      (ψ := quo (succ Δ') (succ q') ≐ succ (pred (quo (succ Δ') (succ q')))))
    refine le_of_eq_add (d := pred (quo (succ Δ') (succ q')) * La) ?_
    ipra_lc e + 𝔞 La * s

/-- `cor:eigenvalue-grid`, the reduced form: `q ∣ Δ`, `q ≤ Δ` and `|a| ≤ R`. -/
theorem grid {q' Δ' La Z R u v : PTm k} (hB : Γ ⊢[PRAAx] Bez q' La u v)
    (hE : Γ ⊢[PRAAx] Z * succ q' ≐ succ Δ' * La) (hR : Γ ⊢[PRAAx] le Z R) :
    Γ ⊢[PRAAx] dvd (succ q') (succ Δ') ⋏ (le (succ q') (succ Δ') ⋏ le La R) :=
  .andI (grid_den_dvd hB hE) (.andI (grid_den_le hB hE) (le_trans (grid_num_le hB hE) hR))

end LeanProofs.IPRA.Foundations.EigenvalueGrid
