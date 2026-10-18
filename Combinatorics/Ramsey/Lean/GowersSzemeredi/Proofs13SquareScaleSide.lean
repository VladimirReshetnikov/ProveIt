import GowersSzemeredi.Proofs13SquareScale

/-! Declarations of `Proofs13SquareScale` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open Filter

namespace LeanProofs.GowersSzemeredi

/-- The three remaining row, coefficient-width, and affine scale conditions
hold uniformly as the Stage 13.6 length tends to infinity. -/
theorem eventually_square_scales {f g W : Real} (hf : 0 < f) (hg : 0 < g) :
    ∀ᶠ L : Nat in atTop, 8 ≤ (L : Real) ^ f ∧ W ≤ (L : Real) ^ f ∧
      8 ≤ ((Nat.floor ((L : Real) ^ f) / 2 : Nat) : Real) ^ g := by
  filter_upwards [eventually_ge_atTop (Nat.ceil (squareLengthThreshold f g W))] with L hL
  exact square_scales_of_explicit_length hf hg L
    ((Nat.le_ceil _).trans (by exact_mod_cast hL))

/-- A positive power-law lower bound forces all three square scales for
large N, uniformly over every progression length above that lower bound. -/
theorem square_scales_above_power_lower_bound {c e f g W : Real}
    (hc : 0 < c) (he : 0 < e) (hf : 0 < f) (hg : 0 < g) :
    ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → ∀ L : Nat,
      c * (N : Real) ^ e ≤ L →
      8 ≤ (L : Real) ^ f ∧ W ≤ (L : Real) ^ f ∧
        8 ≤ ((Nat.floor ((L : Real) ^ f) / 2 : Nat) : Real) ^ g := by
  refine ⟨Nat.ceil (squareScaleThreshold c e f g W), ?_⟩
  intro N hN L hL
  exact square_scales_above_power_explicit hc he hf hg N L
    ((Nat.le_ceil _).trans (by exact_mod_cast hN)) hL

/-- The nested floors and final subtraction preserve a concrete positive
power of N. The factor four in the exponent absorbs all fixed constants. -/
theorem eventually_square_power_lower {c e f g : Real}
    (hc : 0 < c) (he : 0 < e) (hf : 0 < f) (hg : 0 < g) :
    ∀ᶠ N : Nat in atTop, (N : Real) ^ (e * f * g / 4) ≤
      ((Nat.floor ((c * (N : Real) ^ e) ^ f) / 2 : Nat) : Real) ^ (g / 2) - 1 := by
  filter_upwards [eventually_ge_atTop (Nat.ceil (squarePowerThreshold c e f g))] with N hN
  exact square_power_lower_explicit hc he hf hg N
    ((Nat.le_ceil _).trans (by exact_mod_cast hN))

end LeanProofs.GowersSzemeredi
