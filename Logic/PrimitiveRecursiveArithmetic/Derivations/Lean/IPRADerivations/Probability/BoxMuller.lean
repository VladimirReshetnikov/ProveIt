import IPRADerivations.Foundations.FormalDerivation

/-!
# The Jacobians of the Box–Muller transform

Packet: `probability/normal_distribution_ipra_2026-11-16`, `sections/10_statistics_sampling.tex`,
Theorem `thm:box-muller`: "The transformation `u = e^{−r²/2}` sends the uniform density to
`r e^{−r²/2}` on `r > 0` … The polar Jacobian from `(r, θ)` to `(x, y)` is `r`, so the Cartesian density
is `(2π)^{−1} e^{−(x² + y²)/2} = φ(x) φ(y)`", and "the certificate code checks the symbolic Jacobian".

With the partial derivations of `Foundations/FormalDerivation`: variables `0 = r`, `1 = c = cos θ`,
`2 = s = sin θ`, `3 = u`; `∂_r r = 1`, `∂_r u = −r u` (for `u = e^{−r²/2}`); `∂_θ c = −s`, `∂_θ s = c`;
hypothesis `c² + s² = 1`.

* `polar_jacobian`: for `x = r c`, `y = r s`, `∂_r x ∂_θ y − ∂_θ x ∂_r y = r`;
* `radial_density`: `−∂_r u = r u`, i.e. `|du/dr| = r e^{−r²/2}`, the radial density;
* `cartesian_exponent`: `x² + y² = r²`, so `e^{−r²/2} = e^{−(x² + y²)/2}` splits as `φ(x) φ(y)` up to
  the constant.

The independence of the uniforms, the truncation at `2^{−M}` and the change of variables in the
integrals are not formalized.
-/

namespace LeanProofs.IPRA.Probability.BoxMuller

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-- `∂_r`: `r ↦ 1`, `u ↦ −r u`. -/
def δr : Fin 4 → ZExp 4
  | ⟨0, _⟩ => 1
  | ⟨3, _⟩ => -(var 0 * var 3)
  | _ => 0

/-- `∂_θ`: `c ↦ −s`, `s ↦ c`. -/
def δθ : Fin 4 → ZExp 4
  | ⟨1, _⟩ => -(var 2)
  | ⟨2, _⟩ => var 1
  | _ => 0

theorem δr_0 : δr 0 = 1 := rfl
theorem δr_1 : δr 1 = 0 := rfl
theorem δr_2 : δr 2 = 0 := rfl
theorem δr_3 : δr 3 = -(var 0 * var 3) := rfl
theorem δθ_0 : δθ 0 = 0 := rfl
theorem δθ_1 : δθ 1 = -(var 2) := rfl
theorem δθ_2 : δθ 2 = var 1 := rfl
theorem δθ_3 : δθ 3 = 0 := rfl

/-- `thm:box-muller`: the polar Jacobian is `r`. -/
theorem polar_jacobian :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 4)
      (imp [(var 1 * var 1 + var 2 * var 2, 1)]
        (der δr (var 0 * var 1) * der δθ (var 0 * var 2) - der δθ (var 0 * var 1) * der δr (var 0 * var 2),
          var 0)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [δr_0, δr_1, δr_2, δr_3, δθ_0, δθ_1, δθ_2, δθ_3]
    linear_combination ρ 0 * h)

/-- `thm:box-muller`: `u = e^{−r²/2}` has `−du/dr = r u`, the radial density. -/
theorem radial_density :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 4)
      (imp [] (-(der δr (var 3)), var 0 * var 3)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [δr_0, δr_1, δr_2, δr_3, δθ_0, δθ_1, δθ_2, δθ_3]; ring)

/-- `x² + y² = r²` for `x = r c`, `y = r s`. -/
theorem cartesian_exponent :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 4)
      (imp [(var 1 * var 1 + var 2 * var 2, 1)]
        ((var 0 * var 1) * (var 0 * var 1) + (var 0 * var 2) * (var 0 * var 2), var 0 * var 0)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    linear_combination ρ 0 * ρ 0 * h)

end LeanProofs.IPRA.Probability.BoxMuller
