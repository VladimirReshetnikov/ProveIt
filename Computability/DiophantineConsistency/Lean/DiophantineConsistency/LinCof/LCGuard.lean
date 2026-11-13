import DiophantineConsistency.LinCof.LCCanonical
import DiophantineConsistency.ZRows.ModelPellExistence

/-! # The guard Pell pair of the linear-cofactor circuit

At the canonical record, for a slot law of exponent `e ≤ 1`:

* `Budget = lcBudget Cn e > 64` (`LCCanonical.lcBudget_gt`), so `D = Budget − 4 > 0`;
* `16 ∣ Budget` (`LCCanonical.lcBudget_mod`), so `D ≡ 12 (mod 16)`, which no square is
  (`P138Guard.not_square_mod_sixteen`);
* hence `D·τ²` is not a square, and `ModelPellExistence.exists_pos` gives `s, g > 0` with
  `g² = 1 + D τ² s²` (`lc_guard`);
* at a matching point with `x 10 = s`: `P = Dt·(1 + D·Dt·s²) = (τ g)²` (`lc_P`).

Differences from `P138Guard.guard`: `Budget ≡ 0 (mod 16)` always (138 had the two classes
`0, 12`), and the guard register is `P` alone: there is no `BP = Dm·P` here, the factor `Dm`
having moved into the linear cofactor `B = r·A·Dm` (see `LCInterp`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.LCGuard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing P138Ports LCValue LCCanonical
open P138Canonical (Canonical)

attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho coneA coneB

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The guard Pell pair: `D = Budget − 4` is the image of a natural `Dn`, and there are
`s, g > 0` with `g² = 1 + Dn·τ²·s²`. -/
theorem lc_guard (Cn : Canonical V) {e : ℕ} (he : e ≤ 1) :
    ∃ Dn s g : V, 0 < s ∧ 0 < g ∧ ι Dn = lcBudget Cn e - 4 ∧
      g * g = 1 + Dn * (Cn.τ * Cn.τ) * (s * s) := by
  have hB := lcBudget_gt Cn he
  obtain ⟨w, hw⟩ := lcBudget_mod Cn e
  obtain ⟨Dn, hDn⟩ := nonneg_iff.mp (show (0 : DiffRing V) ≤ lcBudget Cn e - 4 by linarith)
  have hDpos : 0 < Dn := ι_lt_ι.mp (by rw [map_zero, ← hDn]; linarith)
  have hτpos : 0 < Cn.τ := P138Interp.τ_pos Cn
  have hns : ∀ t : V, t * t ≠ Dn * Cn.τ * Cn.τ := by
    intro t ht
    have hdvd : Cn.τ * Cn.τ ∣ t * t := ⟨Dn, by rw [ht]; ring⟩
    obtain ⟨t', rfl⟩ := ZRowsCoprimeSquares.dvd_of_mul_self_dvd_mul_self hdvd
    have hsq : t' * t' = Dn := by
      apply ArithmeticBinomLegendre.cancel_left (mul_pos hτpos hτpos)
      calc Cn.τ * Cn.τ * (t' * t') = Cn.τ * t' * (Cn.τ * t') := by ring
        _ = Dn * Cn.τ * Cn.τ := ht
        _ = Cn.τ * Cn.τ * Dn := by ring
    have hsqR : (ι t') ^ 2 = lcBudget Cn e - 4 := by
      rw [hDn, ← hsq, map_mul]
      ring
    exact (P138Guard.not_square_mod_sixteen (ι t') (w - 1)).2 (by rw [hsqR, hw]; ring)
  have hd0 : 0 < Dn * Cn.τ * Cn.τ := mul_pos (mul_pos hDpos hτpos) hτpos
  obtain ⟨g, s, hs, hg⟩ := ModelPellExistence.exists_pos (Dn * Cn.τ * Cn.τ) hd0 hns
  have hgpos : 0 < g := by
    rcases (Arithmetic.zero_le g).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_mul] at hg
      exact absurd hg (ne_of_lt (lt_of_lt_of_le _root_.zero_lt_one le_add_self))
  exact ⟨Dn, s, g, hs, hgpos, hDn.symm, hg.trans (by ring)⟩

/-- At a matching point with `x 10 = s`: `P = Dt·(1 + Dguard·Dt·s²) = (τ g)²`. -/
theorem lc_P (Cn : Canonical V) {e : ℕ} {Dn s g : V} (hD : ι Dn = lcBudget Cn e - 4)
    (hg : g * g = 1 + Dn * (Cn.τ * Cn.τ) * (s * s))
    {x : Fin 11 → DiffRing V} (hx : LCMatches Cn x) (κ ω Λ ψ wt : DiffRing V)
    (hlaw : SlotLaw (portsR (V := V)) x κ ω Λ e) (hκ : κ = ι Cn.k) (h10 : x 10 = ι s) :
    (regsK (portsR (V := V)) x κ ω Λ ψ wt).P = (ι Cn.τ * ι g) ^ 2 := by
  have hgR := congrArg (ι (V := V)) hg
  simp only [map_add, map_mul, map_one] at hgR
  rw [P_eq, Dguard_eq, lc_Dt Cn hx κ ω Λ ψ wt hlaw hκ, lc_Budget Cn hx κ ω Λ ψ wt hlaw hκ, h10]
  linear_combination (-(ι Cn.τ * ι Cn.τ)) * hgR - (ι Cn.τ * ι Cn.τ) ^ 2 * ι s ^ 2 * hD

#print axioms lc_guard
#print axioms lc_P

end DiophantineConsistency.LCGuard
