import IPRADerivations.Core.PolynomialImplications

/-!
# Inverse metric and Maxwell identities of the Kerr–Newman family (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, Sections "Metric, inverse, determinant, and
elementary identities" and "The Maxwell field and the Einstein equation". With

`s = 1 − x²`, `Σ = r² + a² x²`, `P = r² + a²`, `Δ = r² − 2 m r + a² + q²`

the rational identities of these sections, cleared of the denominators `Σ`, `Δ`, `s`, are
polynomial identities over the integers in `r, x, a, m, q`; each is a closed sentence of iPRA
(`Core/PolynomialImplications`).

**The coframe change `eq:Q`**, `Q = [[1, −a s], [−a, P]]` with adjugate `[[P, a s], [a, 1]]`:
`coframe_tt`, `coframe_pp` (`Q · adj Q = Σ · 1` on the diagonal; the off-diagonal entries are
`a s − a s` and `−a P + P a`), and `coframe_b`: `a² s + Σ = P`, i.e. `a p − Σ dφ = −b`.

**The inverse `eq:ginv`** of the `(t, φ)` block `eq:gtable`:
`inverse_diag`: `(Δ − a² s)(P² − a² Δ s) + a² s (P − Δ)² = Σ² Δ`, which is both
`(g g⁻¹)_t^t = 1` and `(g g⁻¹)_φ^φ = 1`; `inverse_offdiag`: `(g g⁻¹)_t^φ = 0` over the common
denominator.

**The density table `eq:density`** (raising both indices of `eq:Ftable` with `eq:ginv`):
`density_rt`, `density_rphi`, `density_xt`, `density_xphi`.

**The field `eq:EB`**, with numerators `Ē = q (r² − a² x²)`, `B̄ = 2 q a r x` over `Σ²`:
`sum_squares` (`eq:sumSquares`), `field_norm`: `Ē² + B̄² = q² Σ²` (so
`E² + 𝓑² = q² / Σ²`); `Er_numer`, `Bx_numer` (the quotient-rule numerators of `eq:EBderiv`),
`maxwell_second` (`𝓑_x = −a E_r`), `maxwell_first_step` and `maxwell_first`
(`eq:twoMaxwell`).

The differentiations themselves (that the displayed numerators are the derivatives) and the
curvature computations of the packet are not formalized.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanInverse

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

local notation "vr" => (ZExp.var 0 : ZExp 5)
local notation "vx" => (ZExp.var 1 : ZExp 5)
local notation "va" => (ZExp.var 2 : ZExp 5)
local notation "vm" => (ZExp.var 3 : ZExp 5)
local notation "vq" => (ZExp.var 4 : ZExp 5)

/-- `s = 1 − x²`. -/
abbrev sS : ZExp 5 := 1 - vx ^ 2
/-- `Σ = r² + a² x²`. -/
abbrev Sg : ZExp 5 := vr ^ 2 + va ^ 2 * vx ^ 2
/-- `P = r² + a²`. -/
abbrev Pp : ZExp 5 := vr ^ 2 + va ^ 2
/-- `Δ = r² − 2 m r + a² + q²`. -/
abbrev Dl : ZExp 5 := vr ^ 2 - 2 * vm * vr + va ^ 2 + vq ^ 2
/-- The numerator `Ē = q (r² − a² x²)` of `E`. -/
abbrev En : ZExp 5 := vq * (vr ^ 2 - va ^ 2 * vx ^ 2)
/-- The numerator `B̄ = 2 q a r x` of `𝓑`. -/
abbrev Bn : ZExp 5 := 2 * vq * va * vr * vx
/-- The numerator `2 q r (−r² + 3 a² x²)` of `E_r` over `Σ³`. -/
abbrev Ern : ZExp 5 := 2 * vq * vr * (3 * va ^ 2 * vx ^ 2 - vr ^ 2)
/-- The numerator `2 q a r (r² − 3 a² x²)` of `𝓑_x` over `Σ³`. -/
abbrev Bxn : ZExp 5 := 2 * vq * va * vr * (vr ^ 2 - 3 * va ^ 2 * vx ^ 2)

/-! ## The coframe change -/

/-- `(Q · adj Q)_{tt} = P − a² s = Σ`. -/
theorem coframe_tt : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (1 * Pp + (-(va * sS)) * va, Sg)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- `(Q · adj Q)_{φφ} = −a · a s + P = Σ`. -/
theorem coframe_pp : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] ((-va) * (va * sS) + Pp * 1, Sg)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- `a² s + Σ = P`: the coefficient identity behind `a p − Σ dφ = −b`. -/
theorem coframe_b : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (va ^ 2 * sS + Sg, Pp)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-! ## The inverse of the `(t, φ)` block -/

/-- `(g g⁻¹)_t^t = (g g⁻¹)_φ^φ = 1`, cleared of `Σ² Δ`. -/
theorem inverse_diag : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] ((Dl - va ^ 2 * sS) * (Pp ^ 2 - va ^ 2 * Dl * sS) + va ^ 2 * sS * (Pp - Dl) ^ 2,
      Sg ^ 2 * Dl)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- `(g g⁻¹)_t^φ = 0`, cleared of `Σ² Δ s`: `g_tt g^{tφ} s + g_tφ g^{φφ} = 0` in numerators. -/
theorem inverse_offdiag : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] ((-(Dl - va ^ 2 * sS)) * (-(va * (Pp - Dl))) * sS +
      (-(va * sS * (Pp - Dl))) * (Dl - va ^ 2 * sS), 0)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-! ## The density table -/

/-- `Σ F^{rt} = −P E`: `g^{tt} · 1 + g^{tφ} · (−a s)` in numerators is `−P Σ`. -/
theorem density_rt : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (-(Pp ^ 2 - va ^ 2 * Dl * sS) + (-(va * (Pp - Dl))) * (-(va * sS)), -(Pp * Sg))) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- `Σ F^{rφ} = −a E`: `g^{φt} · s + g^{φφ} · (−a s)` in numerators over `Σ Δ s` is `−a Σ s`. -/
theorem density_rphi : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] ((-(va * (Pp - Dl))) * sS + (Dl - va ^ 2 * sS) * (-(va * sS)), -(va * Sg * sS))) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- `Σ F^{xt} = −a s 𝓑`: `g^{tt} · a + g^{tφ} · (−P)` in numerators is `−a Δ Σ`. -/
theorem density_xt : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] ((-(Pp ^ 2 - va ^ 2 * Dl * sS)) * va + (-(va * (Pp - Dl))) * (-Pp),
      -(va * Dl * Sg))) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- `Σ F^{xφ} = −𝓑`: `g^{φt} · a s + g^{φφ} · (−P)` in numerators over `Σ Δ s` is `−Δ Σ`. -/
theorem density_xphi : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] ((-(va * (Pp - Dl))) * (va * sS) + (Dl - va ^ 2 * sS) * (-Pp), -(Dl * Sg))) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-! ## The Maxwell field -/

/-- `eq:sumSquares`: `(r² − a² x²)² + 4 a² r² x² = (r² + a² x²)²`. -/
theorem sum_squares : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] ((vr ^ 2 - va ^ 2 * vx ^ 2) ^ 2 + 4 * va ^ 2 * vr ^ 2 * vx ^ 2, Sg ^ 2)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- `Ē² + B̄² = q² Σ²`, that is `E² + 𝓑² = q² / Σ²`. -/
theorem field_norm : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (En ^ 2 + Bn ^ 2, vq ^ 2 * Sg ^ 2)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- The quotient-rule numerator of `E_r`: `Ē_r Σ − 2 Ē Σ_r` with `Ē_r = 2 q r`, `Σ_r = 2 r`. -/
theorem Er_numer : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (2 * vq * vr * Sg - 2 * En * (2 * vr), Ern)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- The quotient-rule numerator of `𝓑_x`: `B̄_x Σ − 2 B̄ Σ_x` with `B̄_x = 2 q a r`,
`Σ_x = 2 a² x`. -/
theorem Bx_numer : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (2 * vq * va * vr * Sg - 2 * Bn * (2 * va ^ 2 * vx), Bxn)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- The second equation of `eq:twoMaxwell`: `a E_r + 𝓑_x = 0`. -/
theorem maxwell_second : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (va * Ern + Bxn, 0)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- `P E_r + a s 𝓑_x = Σ E_r` in numerators. -/
theorem maxwell_first_step : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Pp * Ern + va * sS * Bxn, Sg * Ern)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- The first equation of `eq:twoMaxwell`, cleared of `Σ²`: `2 r E + Σ E_r − 2 a x 𝓑 = 0`. -/
theorem maxwell_first : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (2 * vr * En + Ern - 2 * va * vx * Bn, 0)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end LeanProofs.IPRA.Geometry.KerrNewmanInverse
