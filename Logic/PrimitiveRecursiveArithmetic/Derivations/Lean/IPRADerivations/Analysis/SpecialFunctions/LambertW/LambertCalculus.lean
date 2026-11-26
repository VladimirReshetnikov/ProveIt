import IPRADerivations.Foundations.FormalDerivation

/-!
# The calculus of the Lambert function by formal derivations

Packet: `analysis/lambert_w_ipra_2026-11-16`, Sections "Differential calculus" and "Antiderivatives and
definite integrals": with `w = W(x)`, `x = w e^w`, "`dx = e^w (1 + w) dw`" (7.1), Corollary
`cor:curvature` (`W″(z) = −e^{−2w} (w + 2)/(w + 1)³`, (6.6)) and Theorem `thm:antiderivatives`:
`∫ W dx = x W − x + e^W` (7.2), `∫ W/x dx = W²/2 + W` (7.3),
`∫ W/x² dx = Ei(−W) − e^{−W}` (7.5), "a direct derivative shows that `e^w (w² − w + 1) = xW − x + e^W`
is an antiderivative".

The branch value `w` is the independent variable; `E` stands for `e^w` with `δ E = E`
(`Foundations/FormalDerivation`), and `x = w E`. A statement `dF/dx = G` is `δ F = G · δ x`.

* `dx_dw` (7.1): `δ (w E) = E (1 + w)`;
* `anti_W` (7.2): `δ (x w − x + E) = w · δ x`;
* `anti_W_over_x` (7.3), multiplied by `2x`: `x · δ (w² + 2w) = 2w · δ x`;
* `second_derivative` (6.6): with `W′ = 1/(E (1 + w))` as a fraction, `W″ = W′ · d(W′)/dw` equals
  `−(w + 2)/(E² (1 + w)³)` (quotient rule `Frac.d`);
* `anti_Ei` (7.5): with `N` for `e^{−w}` (`N E = 1`, `δ N = −N`), `r` for `1/w` (`r w = 1`,
  `δ r = −r²`) and `I` for `Ei(−w)` (`δ I = N r`, from `Ei′(t) = e^t/t`):
  `δ (I − N) · x² = w · δ x`.

These are closed sentences of iPRA about signed integer variables. The branches, the named function
`Ei` and the definite integrals are not formalized.
-/

namespace LeanProofs.IPRA.Analysis.LambertCalculus

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-! ## Variables `0 = w`, `1 = E = e^w` -/

/-- `δ w = 1`, `δ E = E`. -/
def δL : Fin 2 → ZExp 2
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => var 1

theorem δL_0 : δL 0 = 1 := rfl
theorem δL_1 : δL 1 = var 1 := rfl

/-- (7.1): `dx = e^w (1 + w) dw` for `x = w e^w`. -/
theorem dx_dw :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (der δL (var 0 * var 1), var 1 * (1 + var 0))) :=
  derive_imp _ _ (by frac_poly R ρ h [δL_0, δL_1]; ring)

/-- (7.2): `x W − x + e^W` is an antiderivative of `W`. -/
theorem anti_W :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (der δL (var 0 * var 1 * var 0 - var 0 * var 1 + var 1),
        var 0 * der δL (var 0 * var 1))) :=
  derive_imp _ _ (by frac_poly R ρ h [δL_0, δL_1]; ring)

/-- (7.3): `W²/2 + W` is an antiderivative of `W/x` (multiplied by `2x`). -/
theorem anti_W_over_x :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] ((var 0 * var 1) * der δL (var 0 * var 0 + 2 * var 0),
        2 * var 0 * der δL (var 0 * var 1))) :=
  derive_imp _ _ (by frac_poly R ρ h [δL_0, δL_1]; ring)

/-- `W′ = 1/(e^w (1 + w))` as a fraction in `w`. -/
abbrev dW : Frac 2 := ⟨1, var 1 * (1 + var 0)⟩

/-- (6.6): `W″ = W′ · d(W′)/dw = −(w + 2)/(e^{2w} (1 + w)³)`. -/
theorem second_derivative :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (Frac.eqn (dW * Frac.d δL dW)
        ⟨-(var 0 + 2), var 1 * var 1 * ((1 + var 0) * (1 + var 0) * (1 + var 0))⟩)) :=
  derive_imp _ _ (by frac_poly R ρ h [δL_0, δL_1]; ring)

/-! ## Variables `0 = w`, `1 = E`, `2 = N = e^{−w}`, `3 = r = 1/w`, `4 = I = Ei(−w)` -/

/-- `δ w = 1`, `δ E = E`, `δ N = −N`, `δ r = −r²`, `δ I = N r`. -/
def δI : Fin 5 → ZExp 5
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => var 1
  | ⟨2, _⟩ => -(var 2)
  | ⟨3, _⟩ => -(var 3 * var 3)
  | ⟨4, _⟩ => var 2 * var 3

theorem δI_0 : δI 0 = 1 := rfl
theorem δI_1 : δI 1 = var 1 := rfl
theorem δI_2 : δI 2 = -(var 2) := rfl
theorem δI_3 : δI 3 = -(var 3 * var 3) := rfl
theorem δI_4 : δI 4 = var 2 * var 3 := rfl

/-- (7.5): `Ei(−W) − e^{−W}` is an antiderivative of `W/x²` (multiplied by `x²`). -/
theorem anti_Ei :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(var 2 * var 1, 1), (var 3 * var 0, 1)]
        (der δI (var 4 - var 2) * ((var 0 * var 1) * (var 0 * var 1)),
          var 0 * der δI (var 0 * var 1))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [δI_0, δI_1, δI_2, δI_3, δI_4]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (ρ 0 * ρ 1 * ρ 2 * ρ 1) * h₂ + (ρ 0 * ρ 1 + ρ 0 * ρ 0 * ρ 1) * h₁)

end LeanProofs.IPRA.Analysis.LambertCalculus
