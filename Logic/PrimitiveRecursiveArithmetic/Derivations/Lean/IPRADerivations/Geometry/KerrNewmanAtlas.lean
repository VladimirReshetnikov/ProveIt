import IPRADerivations.Geometry.KerrNewmanIngoingConnection
import IPRADerivations.Geometry.MonotileSubstitution

/-!
# The rational atlas of the Kerr–Newman metric (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, Section "A rational atlas across radial and
polar coordinate poles": `eq:sphereform`, `eq:stereo` with the chart transition,
`eq:nullcoframe`, `eq:signature`, `eq:cartesian`, `eq:flatpullback` with its Jacobian, and
`eq:KS`.

## The sphere form (indeterminates `r, x, a, m, q`)

With the ingoing metric of `Geometry/KerrNewmanIngoingConnection`, `L = 2mr − q²`, `η = s dψ`,
`dΩ² = dx²/s + s dψ²` and `p₊ = dv − a η`, `eq:sphereform`,
`g₊ = −dv² + 2 dv dr − 2a dr η + Σ dΩ² + a² η² + (L/Σ) p₊²`, in the coordinates `(v, r, x, ψ)`:

* `sphere_vv`, `sphere_vr`, `sphere_vp`, `sphere_rp`, `sphere_pp`, `sphere_xx`: the entries of
  the right-hand side are those of `eq:ingoing` ("Indeed `P − Σ = a² s`"); the other entries are
  `0` on both sides;
* `ks_vv`, `ks_vp`, `ks_pp` (`eq:KS`): with `g₀` the ingoing metric at `m = q = 0` (where
  `Δ = P`), `g₊ − g₀ = (L/Σ) p₊²`; the other entries of the difference vanish;
* `p_null`: `g₊⁻¹(p₊, p₊) = g^vv − 2 a s g^vψ + a² s² g^ψψ = 0` for every `m`, `q`, in
  particular for `g₀` ("The covector `p` is null for `g₀⁻¹`").

## The null coframe and the signature (`eq:nullcoframe`, `eq:signature`)

In the basis `(dv, dr, η)` of the one-forms entering `eq:sphereform` (the term `Σ dΩ²` is the
same on both sides), `p = dv − a η` and `n = dr − a η + c p` with `c = (L − Σ)/(2Σ)`:

* `null_vv`, `null_vr`, `null_ve`, `null_rr`, `null_re`, `null_ee`: the symmetric product
  `2 p n` has the entries of `−dv² + 2 dv dr − 2a dr η + a² η² + (L/Σ) p²`, so
  `g₊ = 2 p n + Σ dΩ²`;
* `signature_split`: `2 (pᵢ nⱼ + pⱼ nᵢ) = (p + n)ᵢ (p + n)ⱼ − (p − n)ᵢ (p − n)ⱼ`, so
  `2 p n = −½ (p − n)² + ½ (p + n)²`.

* `null_block_det` (`eq:stereodet`): for `p = dv + α du + β dz`, `n = c dv + dr + γ du + δ dz`
  (a coframe unitriangular relative to `(dv, dr, du, dz)`) and any `k`, the form
  `2 p n + k (du² + dz²)` has determinant `−k²` (`det4` of `Geometry/MonotileSubstitution`); with
  the coefficients of `eq:nullcoframe` in the stereographic chart and `k = 4Σ/h²` this is
  `det g₊ = −16 Σ²/h⁴`. The substitution of those fractional coefficients is not stated as one
  sentence.

## The stereographic chart (indeterminates `u, z`)

`h = 1 + u² + z²`, `x = (1 − u² − z²)/h`, `η = 4 (u dz − z du)/h²`, `dΩ² = 4 (du² + dz²)/h²`:

* `stereo_s`: `s = 1 − x² = 4 (u² + z²)/h²`;
* `stereo_eta_u`, `stereo_eta_z`: `η = s dψ` for `dψ = (u dz − z du)/(u² + z²)`;
* `stereo_uu`, `stereo_uz`, `stereo_zz`: `s dΩ² = dx² + η²`, that is
  `dΩ² = dx²/s + s dψ²`, the angular metric of the `(x, ψ)` chart, with `dx` the formal
  differential of `x(u, z)`.

## The chart transition

On the second chart `x = (u′² + z′² − 1)/h′`, with `(u′, z′) = (u, z)/(u² + z²)`:

* `transition_x`: `x h′ = u′² + z′² − 1` with the first-chart `x`, so the two charts give the
  same `x` ("The metric and potential use `x` only through `x²`": here even `x` agrees);
* `transition_eta_u`, `transition_eta_z`: the pullback of `η′ = 4 (u′ dz′ − z′ du′)/h′²` is `η`;
* `transition_uu`, `transition_uz`, `transition_zz`: the pullback of
  `dΩ′² = 4 (du′² + dz′²)/h′²` is `dΩ²`.

## The flat background (indeterminates `v, r, u, z, a`)

`T = v − r`, `X = 2 (r u − a z)/h`, `Y = 2 (r z + a u)/h`, `Z = r (1 − u² − z²)/h`
(`eq:cartesian`):

* `der_Xr`, …, `der_Zz`, `der_v`, `der_T`: the first derivatives, each `∂_i F` of `X, Y, Z`
  reduced to a numerator `Fᵢ` over `h²`;
* `flat_vv`, `flat_vr`, `flat_rr`, `flat_ru`, `flat_rz`, `flat_uu`, `flat_uz`, `flat_zz`: the
  entries of `eq:flatpullback`,
  `−dT² + dX² + dY² + dZ² = −dv² + 2 dv dr − 2a dr η + Σ dΩ² + a² η²` with `Σ = r² + a² x²`, in
  the coordinates `(v, r, u, z)`, as `−∂_i T ∂_j T + (Xᵢ Xⱼ + Yᵢ Yⱼ + Zᵢ Zⱼ)/h⁴` (the entries
  `vu`, `vz` are `0` on both sides, since `∂_v X = ∂_v Y = ∂_v Z = 0` and `∂_u T = ∂_z T = 0`);
* `flat_jacobian`, `flat_sigma`: the determinant of the numerators is
  `4 (r² h² + a² (1 − u² − z²)²) h²` and `Σ = (r² h² + a² (1 − u² − z²)²)/h²`, so the Jacobian
  determinant of `(X, Y, Z)` with respect to `(r, u, z)` is `4Σ/h²` ("The spatial Jacobian has
  absolute determinant `4Σ/h²`").

The composition of the derivative statements with the entry statements (substituting the
reduced derivatives into the products) is not stated as one sentence per entry.

The derivatives are the formal derivations of `Foundations/FormalDerivation`. Every statement
is an identity of fractions cleared of denominators, a closed sentence of iPRA certified in
every commutative ring.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanAtlas

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-! ## The sphere form and the Kerr–Schild form -/

section Sphere

open LeanProofs.IPRA.Geometry.KerrNewmanIngoingConnection (Sg sx Pp Dl gvv gvr gvp grp gpp gxx
  ivv ivp ipp)

local notation "r" => (ZExp.var 0 : ZExp 5)
local notation "x" => (ZExp.var 1 : ZExp 5)
local notation "a" => (ZExp.var 2 : ZExp 5)
local notation "m" => (ZExp.var 3 : ZExp 5)
local notation "q" => (ZExp.var 4 : ZExp 5)

/-- `L = 2mr − q²`. -/
def Lm : ZExp 5 := 2 * m * r - q ^ 2

/-- `eq:sphereform`, entry `vv`: `g_vv = −1 + L/Σ`. -/
theorem sphere_vv :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn gvv (Frac.ofZ (-1) + ⟨Lm, Sg⟩))) :=
  derive_imp _ _ (by frac_poly R ρ h [gvv, Lm, Dl, Sg, sx]; ring)

/-- `eq:sphereform`, entry `vr`: `g_vr = 1`. -/
theorem sphere_vr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5) (imp [] (Frac.eqn gvr (Frac.ofZ 1))) :=
  derive_imp _ _ (by frac_poly R ρ h [gvr])

/-- `eq:sphereform`, entry `vψ`: `g_vψ = (L/Σ)(−a s)`. -/
theorem sphere_vp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn gvp (⟨Lm, Sg⟩ * Frac.ofZ (-(a * sx))))) :=
  derive_imp _ _ (by frac_poly R ρ h [gvp, Lm, Dl, Pp, Sg, sx]; ring)

/-- `eq:sphereform`, entry `rψ`: `g_rψ = −a s`, from `−2a dr η`. -/
theorem sphere_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn grp (Frac.ofZ (-(a * sx))))) :=
  derive_imp _ _ (by frac_poly R ρ h [grp])

/-- `eq:sphereform`, entry `ψψ`: `g_ψψ = Σ s + a² s² + (L/Σ) a² s²`. -/
theorem sphere_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn gpp (Frac.ofZ (Sg * sx) + Frac.ofZ (a ^ 2 * sx ^ 2)
        + ⟨Lm, Sg⟩ * Frac.ofZ (a ^ 2 * sx ^ 2)))) :=
  derive_imp _ _ (by frac_poly R ρ h [gpp, Lm, Dl, Pp, Sg, sx]; ring)

/-- `eq:sphereform`, entry `xx`: `g_xx = Σ/s`, from `Σ dΩ²`. -/
theorem sphere_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn gxx (Frac.ofZ Sg * ⟨1, sx⟩))) :=
  derive_imp _ _ (by frac_poly R ρ h [gxx]; ring)

/-- `g₀_vv`: the ingoing metric at `m = q = 0`, where `Δ = P`. -/
def g0vv : Frac 5 := ⟨-Pp + a ^ 2 * sx, Sg⟩
/-- `g₀_vψ = 0`. -/
def g0vp : Frac 5 := ⟨0, Sg⟩
/-- `g₀_ψψ = s (P² − a² P s)/Σ`. -/
def g0pp : Frac 5 := ⟨sx * (Pp ^ 2 - a ^ 2 * Pp * sx), Sg⟩

/-- `eq:KS`, entry `vv`: `g_vv − g₀_vv = L/Σ`. -/
theorem ks_vv :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5) (imp [] (Frac.eqn (gvv - g0vv) ⟨Lm, Sg⟩)) :=
  derive_imp _ _ (by frac_poly R ρ h [gvv, g0vv, Lm, Dl, Pp, Sg, sx]; ring)

/-- `eq:KS`, entry `vψ`: `g_vψ − g₀_vψ = (L/Σ)(−a s)`. -/
theorem ks_vp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gvp - g0vp) (⟨Lm, Sg⟩ * Frac.ofZ (-(a * sx))))) :=
  derive_imp _ _ (by frac_poly R ρ h [gvp, g0vp, Lm, Dl, Pp, Sg, sx]; ring)

/-- `eq:KS`, entry `ψψ`: `g_ψψ − g₀_ψψ = (L/Σ) a² s²`. -/
theorem ks_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gpp - g0pp) (⟨Lm, Sg⟩ * Frac.ofZ (a ^ 2 * sx ^ 2)))) :=
  derive_imp _ _ (by frac_poly R ρ h [gpp, g0pp, Lm, Dl, Pp, Sg, sx]; ring)

/-- `p₊ = dv − a s dψ` is null for the inverse metric, for every `m`, `q`. -/
theorem p_null :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (ivv - Frac.ofZ (2 * a * sx) * ivp + Frac.ofZ (a ^ 2 * sx ^ 2) * ipp)
        (Frac.ofZ 0))) :=
  derive_imp _ _ (by frac_poly R ρ h [ivv, ivp, ipp, Sg, sx]; ring)

/-! ### The null coframe, in the basis `(dv, dr, η)` -/

/-- `c = (L − Σ)/(2Σ)`. -/
def cn : Frac 5 := ⟨Lm - Sg, 2 * Sg⟩

/-- `eq:signature`, entry `vv`: `2 p_v n_v = 2c = −1 + L/Σ`. -/
theorem null_vv :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * cn) (Frac.ofZ (-1) + ⟨Lm, Sg⟩))) :=
  derive_imp _ _ (by frac_poly R ρ h [cn]; ring)

/-- `eq:signature`, entry `vr`: `p_v n_r + p_r n_v = 1`. -/
theorem null_vr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 1 * Frac.ofZ 1 + Frac.ofZ 0 * cn) (Frac.ofZ 1))) :=
  derive_imp _ _ (by frac_poly R ρ h [cn]; ring)

/-- `eq:signature`, entry `vη`: `p_v n_η + p_η n_v = −a − 2ac = −a L/Σ`. -/
theorem null_ve :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ (-a) - Frac.ofZ a * cn + Frac.ofZ (-a) * cn)
        (Frac.ofZ (-a) * ⟨Lm, Sg⟩))) :=
  derive_imp _ _ (by frac_poly R ρ h [cn]; ring)

/-- `eq:signature`, entry `rr`: `2 p_r n_r = 0`. -/
theorem null_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Frac.ofZ 0 * Frac.ofZ 1)) (Frac.ofZ 0))) :=
  derive_imp _ _ (by frac_poly R ρ h; ring)

/-- `eq:signature`, entry `rη`: `p_r n_η + p_η n_r = −a`. -/
theorem null_re :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn
        (Frac.ofZ 0 * (Frac.ofZ (-a) - Frac.ofZ a * cn) + Frac.ofZ (-a) * Frac.ofZ 1)
        (Frac.ofZ (-a)))) :=
  derive_imp _ _ (by frac_poly R ρ h [cn]; ring)

/-- `eq:signature`, entry `ηη`: `2 p_η n_η = 2a² + 2a² c = a² + a² L/Σ`. -/
theorem null_ee :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Frac.ofZ (-a) * (Frac.ofZ (-a) - Frac.ofZ a * cn)))
        (Frac.ofZ (a ^ 2) + Frac.ofZ (a ^ 2) * ⟨Lm, Sg⟩))) :=
  derive_imp _ _ (by frac_poly R ρ h [cn]; ring)

end Sphere

section Split

local notation "pi" => (ZExp.var 0 : ZExp 4)
local notation "pj" => (ZExp.var 1 : ZExp 4)
local notation "ni" => (ZExp.var 2 : ZExp 4)
local notation "nj" => (ZExp.var 3 : ZExp 4)

/-- `2 p n = −½ (p − n)² + ½ (p + n)²`, entrywise. -/
theorem signature_split :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 4)
      (imp [] (2 * (pi * nj + pj * ni), (pi + ni) * (pj + nj) - (pi - ni) * (pj - nj))) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end Split

section NullBlock

open LeanProofs.IPRA.Geometry.MonotileSubstitution (Row4 det4)

local notation "α" => (ZExp.var 0 : ZExp 6)
local notation "β" => (ZExp.var 1 : ZExp 6)
local notation "c" => (ZExp.var 2 : ZExp 6)
local notation "γ" => (ZExp.var 3 : ZExp 6)
local notation "δ" => (ZExp.var 4 : ZExp 6)
local notation "k" => (ZExp.var 5 : ZExp 6)

/-- `eq:stereodet` from `eq:signature`: for one-forms `p = dv + α du + β dz` and
`n = c dv + dr + γ du + δ dz` (the coframe `(p, n, du, dz)` is unitriangular) and any `k`, the
quadratic form `2 p n + k (du² + dz²)` has, in the basis `(dv, dr, du, dz)`, determinant `−k²`.
For `eq:nullcoframe` in the stereographic chart, `α = −a η_u`, `β = −a η_z`,
`c = (L − Σ)/(2Σ)`, `γ = −a (1 + c) η_u`, `δ = −a (1 + c) η_z` and `k = 4Σ/h²`, so
`det g₊ = −16 Σ²/h⁴`. -/
theorem null_block_det :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (det4 ⟨2 * c, 1, γ + α * c, δ + β * c⟩ ⟨1, 0, α, β⟩
        ⟨γ + α * c, α, 2 * α * γ + k, α * δ + β * γ⟩ ⟨δ + β * c, β, α * δ + β * γ, 2 * β * δ + k⟩,
        -(k ^ 2))) :=
  derive_imp _ _ (by ipra_poly R ρ h [det4]; ring)

end NullBlock

/-! ## The stereographic chart and the chart transition -/

section Stereo

local notation "u" => (ZExp.var 0 : ZExp 2)
local notation "z" => (ZExp.var 1 : ZExp 2)

/-- `∂_u`. -/
def δu : Fin 2 → ZExp 2
  | ⟨0, _⟩ => 1
  | _ => 0

/-- `∂_z`. -/
def δz : Fin 2 → ZExp 2
  | ⟨1, _⟩ => 1
  | _ => 0

theorem δu_0 : δu 0 = 1 := rfl
theorem δu_1 : δu 1 = 0 := rfl
theorem δz_0 : δz 0 = 0 := rfl
theorem δz_1 : δz 1 = 1 := rfl

/-- `h = 1 + u² + z²`. -/
def hh : ZExp 2 := 1 + u ^ 2 + z ^ 2
/-- `x = (1 − u² − z²)/h`. -/
def Xs : Frac 2 := ⟨1 - u ^ 2 - z ^ 2, hh⟩
/-- `s = 1 − x²`. -/
def ss : Frac 2 := Frac.ofZ 1 - Xs * Xs
/-- The `du`-coefficient of `η`: `−4z/h²`. -/
def eu : Frac 2 := ⟨-(4 * z), hh ^ 2⟩
/-- The `dz`-coefficient of `η`: `4u/h²`. -/
def ez : Frac 2 := ⟨4 * u, hh ^ 2⟩
/-- The coefficient of `du²` and `dz²` in `dΩ²`: `4/h²`. -/
def om : Frac 2 := ⟨4, hh ^ 2⟩

/-- `s = 4 (u² + z²)/h²`. -/
theorem stereo_s :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (Frac.eqn ss ⟨4 * (u ^ 2 + z ^ 2), hh ^ 2⟩)) :=
  derive_imp _ _ (by frac_poly R ρ h [ss, Xs, hh]; ring)

/-- `η = s dψ`, `du`-coefficient: `s · (−z/(u² + z²)) = −4z/h²`. -/
theorem stereo_eta_u :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (Frac.eqn (ss * ⟨-z, u ^ 2 + z ^ 2⟩) eu)) :=
  derive_imp _ _ (by frac_poly R ρ h [ss, Xs, eu, hh]; ring)

/-- `η = s dψ`, `dz`-coefficient: `s · (u/(u² + z²)) = 4u/h²`. -/
theorem stereo_eta_z :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (Frac.eqn (ss * ⟨u, u ^ 2 + z ^ 2⟩) ez)) :=
  derive_imp _ _ (by frac_poly R ρ h [ss, Xs, ez, hh]; ring)

/-- `s dΩ² = dx² + η²`, entry `uu`. -/
theorem stereo_uu :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (Frac.eqn (Frac.d δu Xs * Frac.d δu Xs + eu * eu) (ss * om))) :=
  derive_imp _ _ (by frac_poly R ρ h [ss, Xs, eu, om, hh, δu_0, δu_1]; ring)

/-- `s dΩ² = dx² + η²`, entry `uz`. -/
theorem stereo_uz :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (Frac.eqn (Frac.d δu Xs * Frac.d δz Xs + eu * ez) (Frac.ofZ 0))) :=
  derive_imp _ _ (by frac_poly R ρ h [Xs, eu, ez, hh, δu_0, δu_1, δz_0, δz_1]; ring)

/-- `s dΩ² = dx² + η²`, entry `zz`. -/
theorem stereo_zz :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (Frac.eqn (Frac.d δz Xs * Frac.d δz Xs + ez * ez) (ss * om))) :=
  derive_imp _ _ (by frac_poly R ρ h [ss, Xs, ez, om, hh, δz_0, δz_1]; ring)

/-- `u′ = u/(u² + z²)`. -/
def u' : Frac 2 := ⟨u, u ^ 2 + z ^ 2⟩
/-- `z′ = z/(u² + z²)`. -/
def z' : Frac 2 := ⟨z, u ^ 2 + z ^ 2⟩
/-- `h′ = 1 + u′² + z′²`. -/
def hh' : Frac 2 := Frac.ofZ 1 + u' * u' + z' * z'

/-- The two charts give the same `x`: `x h′ = u′² + z′² − 1`. -/
theorem transition_x :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (Frac.eqn (Xs * hh') (u' * u' + z' * z' - Frac.ofZ 1))) :=
  derive_imp _ _ (by frac_poly R ρ h [Xs, hh', u', z', hh]; ring)

/-- The pullback of `η′`, `du`-coefficient: `4 (u′ ∂_u z′ − z′ ∂_u u′) = (−4z/h²) h′²`. -/
theorem transition_eta_u :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (Frac.eqn (Frac.ofZ 4 * (u' * Frac.d δu z' - z' * Frac.d δu u'))
        (eu * (hh' * hh')))) :=
  derive_imp _ _ (by frac_poly R ρ h [eu, hh', u', z', hh, δu_0, δu_1]; ring)

/-- The pullback of `η′`, `dz`-coefficient: `4 (u′ ∂_z z′ − z′ ∂_z u′) = (4u/h²) h′²`. -/
theorem transition_eta_z :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (Frac.eqn (Frac.ofZ 4 * (u' * Frac.d δz z' - z' * Frac.d δz u'))
        (ez * (hh' * hh')))) :=
  derive_imp _ _ (by frac_poly R ρ h [ez, hh', u', z', hh, δz_0, δz_1]; ring)

/-- The pullback of `dΩ′²`, entry `uu`: `4 ((∂_u u′)² + (∂_u z′)²) = (4/h²) h′²`. -/
theorem transition_uu :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (Frac.eqn (Frac.ofZ 4 * (Frac.d δu u' * Frac.d δu u' + Frac.d δu z' * Frac.d δu z'))
        (om * (hh' * hh')))) :=
  derive_imp _ _ (by frac_poly R ρ h [om, hh', u', z', hh, δu_0, δu_1]; ring)

/-- The pullback of `dΩ′²`, entry `uz`: `4 (∂_u u′ ∂_z u′ + ∂_u z′ ∂_z z′) = 0`. -/
theorem transition_uz :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (Frac.eqn (Frac.ofZ 4 * (Frac.d δu u' * Frac.d δz u' + Frac.d δu z' * Frac.d δz z'))
        (Frac.ofZ 0))) :=
  derive_imp _ _ (by frac_poly R ρ h [u', z', δu_0, δu_1, δz_0, δz_1]; ring)

/-- The pullback of `dΩ′²`, entry `zz`: `4 ((∂_z u′)² + (∂_z z′)²) = (4/h²) h′²`. -/
theorem transition_zz :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (Frac.eqn (Frac.ofZ 4 * (Frac.d δz u' * Frac.d δz u' + Frac.d δz z' * Frac.d δz z'))
        (om * (hh' * hh')))) :=
  derive_imp _ _ (by frac_poly R ρ h [om, hh', u', z', hh, δz_0, δz_1]; ring)

end Stereo

/-! ## The flat background -/

section Flat

local notation "v" => (ZExp.var 0 : ZExp 5)
local notation "r" => (ZExp.var 1 : ZExp 5)
local notation "u" => (ZExp.var 2 : ZExp 5)
local notation "z" => (ZExp.var 3 : ZExp 5)
local notation "a" => (ZExp.var 4 : ZExp 5)

/-- `∂_v`. -/
def δV : Fin 5 → ZExp 5
  | ⟨0, _⟩ => 1
  | _ => 0
/-- `∂_r`. -/
def δR : Fin 5 → ZExp 5
  | ⟨1, _⟩ => 1
  | _ => 0
/-- `∂_u`. -/
def δU : Fin 5 → ZExp 5
  | ⟨2, _⟩ => 1
  | _ => 0
/-- `∂_z`. -/
def δZ : Fin 5 → ZExp 5
  | ⟨3, _⟩ => 1
  | _ => 0

theorem δV_0 : δV 0 = 1 := rfl
theorem δV_1 : δV 1 = 0 := rfl
theorem δV_2 : δV 2 = 0 := rfl
theorem δV_3 : δV 3 = 0 := rfl
theorem δV_4 : δV 4 = 0 := rfl
theorem δR_0 : δR 0 = 0 := rfl
theorem δR_1 : δR 1 = 1 := rfl
theorem δR_2 : δR 2 = 0 := rfl
theorem δR_3 : δR 3 = 0 := rfl
theorem δR_4 : δR 4 = 0 := rfl
theorem δU_0 : δU 0 = 0 := rfl
theorem δU_1 : δU 1 = 0 := rfl
theorem δU_2 : δU 2 = 1 := rfl
theorem δU_3 : δU 3 = 0 := rfl
theorem δU_4 : δU 4 = 0 := rfl
theorem δZ_0 : δZ 0 = 0 := rfl
theorem δZ_1 : δZ 1 = 0 := rfl
theorem δZ_2 : δZ 2 = 0 := rfl
theorem δZ_3 : δZ 3 = 1 := rfl
theorem δZ_4 : δZ 4 = 0 := rfl

/-- `h = 1 + u² + z²`. -/
def hF : ZExp 5 := 1 + u ^ 2 + z ^ 2
/-- `T = v − r`. -/
def Tc : Frac 5 := Frac.ofZ (v - r)
/-- `X = 2 (r u − a z)/h`. -/
def Xc : Frac 5 := ⟨2 * (r * u - a * z), hF⟩
/-- `Y = 2 (r z + a u)/h`. -/
def Yc : Frac 5 := ⟨2 * (r * z + a * u), hF⟩
/-- `Z = r (1 − u² − z²)/h`. -/
def Zc : Frac 5 := ⟨r * (1 - u ^ 2 - z ^ 2), hF⟩
/-- `x = (1 − u² − z²)/h`. -/
def xF : Frac 5 := ⟨1 - u ^ 2 - z ^ 2, hF⟩
/-- `Σ = r² + a² x²`. -/
def SF : Frac 5 := Frac.ofZ (r ^ 2) + Frac.ofZ (a ^ 2) * (xF * xF)
/-- `η_u = −4z/h²`. -/
def eU : Frac 5 := ⟨-(4 * z), hF ^ 2⟩
/-- `η_z = 4u/h²`. -/
def eZ : Frac 5 := ⟨4 * u, hF ^ 2⟩
/-- `4/h²`. -/
def oF : Frac 5 := ⟨4, hF ^ 2⟩

/-! ### The first derivatives, reduced over `h²` -/

/-- `h² ∂_r X`. -/
def Xr : ZExp 5 := 2 * u * hF
/-- `h² ∂_u X`. -/
def Xu : ZExp 5 := 2 * (2 * a * u * z - r * u ^ 2 + r * z ^ 2 + r)
/-- `h² ∂_z X`. -/
def Xz : ZExp 5 := 2 * (-a * u ^ 2 + a * z ^ 2 - a - 2 * r * u * z)
/-- `h² ∂_r Y`. -/
def Yr : ZExp 5 := 2 * z * hF
/-- `h² ∂_u Y`. -/
def Yu : ZExp 5 := 2 * (-a * u ^ 2 + a * z ^ 2 + a - 2 * r * u * z)
/-- `h² ∂_z Y`. -/
def Yz : ZExp 5 := -2 * (2 * a * u * z - r * u ^ 2 + r * z ^ 2 - r)
/-- `h² ∂_r Z`. -/
def Zr : ZExp 5 := -(u ^ 2 + z ^ 2 - 1) * hF
/-- `h² ∂_u Z`. -/
def Zu : ZExp 5 := -4 * r * u
/-- `h² ∂_z Z`. -/
def Zz : ZExp 5 := -4 * r * z

/-- Start the certificate of a derivative of `eq:cartesian`. -/
local macro "der_poly" : tactic =>
  `(tactic| (
    frac_poly R ρ h [Tc, Xc, Yc, Zc, hF, Xr, Xu, Xz, Yr, Yu, Yz, Zr, Zu, Zz, δV_0, δV_1, δV_2,
      δV_3, δV_4, δR_0, δR_1, δR_2, δR_3, δR_4, δU_0, δU_1, δU_2, δU_3, δU_4, δZ_0, δZ_1, δZ_2,
      δZ_3, δZ_4]
    ring))

/-- `∂_r X = 2u/h`. -/
theorem der_Xr : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Frac.eqn (Frac.d δR Xc) ⟨Xr, hF ^ 2⟩)) := derive_imp _ _ (by der_poly)
/-- `∂_u X`. -/
theorem der_Xu : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Frac.eqn (Frac.d δU Xc) ⟨Xu, hF ^ 2⟩)) := derive_imp _ _ (by der_poly)
/-- `∂_z X`. -/
theorem der_Xz : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Frac.eqn (Frac.d δZ Xc) ⟨Xz, hF ^ 2⟩)) := derive_imp _ _ (by der_poly)
/-- `∂_r Y = 2z/h`. -/
theorem der_Yr : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Frac.eqn (Frac.d δR Yc) ⟨Yr, hF ^ 2⟩)) := derive_imp _ _ (by der_poly)
/-- `∂_u Y`. -/
theorem der_Yu : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Frac.eqn (Frac.d δU Yc) ⟨Yu, hF ^ 2⟩)) := derive_imp _ _ (by der_poly)
/-- `∂_z Y`. -/
theorem der_Yz : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Frac.eqn (Frac.d δZ Yc) ⟨Yz, hF ^ 2⟩)) := derive_imp _ _ (by der_poly)
/-- `∂_r Z = (1 − u² − z²)/h`. -/
theorem der_Zr : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Frac.eqn (Frac.d δR Zc) ⟨Zr, hF ^ 2⟩)) := derive_imp _ _ (by der_poly)
/-- `∂_u Z = −4ru/h²`. -/
theorem der_Zu : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Frac.eqn (Frac.d δU Zc) ⟨Zu, hF ^ 2⟩)) := derive_imp _ _ (by der_poly)
/-- `∂_z Z = −4rz/h²`. -/
theorem der_Zz : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Frac.eqn (Frac.d δZ Zc) ⟨Zz, hF ^ 2⟩)) := derive_imp _ _ (by der_poly)
/-- `∂_v X = ∂_v Y = ∂_v Z = 0`: the Cartesian space coordinates do not depend on `v`. -/
theorem der_v : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Frac.eqn (Frac.d δV Xc + Frac.d δV Yc + Frac.d δV Zc) (Frac.ofZ 0))) :=
  derive_imp _ _ (by der_poly)
/-- `∂_v T = 1`, `∂_r T = −1`, `∂_u T = ∂_z T = 0`. -/
theorem der_T : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Frac.eqn (Frac.d δV Tc - Frac.d δR Tc + Frac.d δU Tc + Frac.d δZ Tc)
      (Frac.ofZ 2))) :=
  derive_imp _ _ (by der_poly)

/-! ### The entries of `eq:flatpullback`

With these derivatives (and `∂_v X = ∂_v Y = ∂_v Z = 0`, `∂_v T = 1`, `∂_r T = −1`), the entry
`(i, j)` of `−dT² + dX² + dY² + dZ²` is `−∂_i T ∂_j T + (Xᵢ Xⱼ + Yᵢ Yⱼ + Zᵢ Zⱼ)/h⁴`. -/

/-- Start the certificate of an entry of `eq:flatpullback`. -/
local macro "flat_poly" : tactic =>
  `(tactic| (
    frac_poly R ρ h [xF, SF, eU, eZ, oF, hF, Xr, Xu, Xz, Yr, Yu, Yz, Zr, Zu, Zz]
    ring))

/-- `eq:flatpullback`, entry `vv`: `−(∂_v T)² = −1`. -/
theorem flat_vv : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Frac.eqn (Frac.ofZ (-(1 * 1))) (Frac.ofZ (-1)))) := derive_imp _ _ (by flat_poly)

/-- `eq:flatpullback`, entry `vr`: `−∂_v T ∂_r T = 1`, from `2 dv dr`. -/
theorem flat_vr : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Frac.eqn (Frac.ofZ (-(1 * (-1)))) (Frac.ofZ 1))) := derive_imp _ _ (by flat_poly)

/-- `eq:flatpullback`, entry `rr`: `−1 + (Xr² + Yr² + Zr²)/h⁴ = 0`. -/
theorem flat_rr : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Frac.eqn (Frac.ofZ (-1) + ⟨Xr * Xr + Yr * Yr + Zr * Zr, hF ^ 4⟩) (Frac.ofZ 0))) :=
  derive_imp _ _ (by flat_poly)

/-- `eq:flatpullback`, entry `ru`: `(Xr Xu + Yr Yu + Zr Zu)/h⁴ = −a η_u`, from `−2a dr η`. -/
theorem flat_ru : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Frac.eqn ⟨Xr * Xu + Yr * Yu + Zr * Zu, hF ^ 4⟩ (Frac.ofZ (-a) * eU))) :=
  derive_imp _ _ (by flat_poly)

/-- `eq:flatpullback`, entry `rz`: `(Xr Xz + Yr Yz + Zr Zz)/h⁴ = −a η_z`. -/
theorem flat_rz : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Frac.eqn ⟨Xr * Xz + Yr * Yz + Zr * Zz, hF ^ 4⟩ (Frac.ofZ (-a) * eZ))) :=
  derive_imp _ _ (by flat_poly)

/-- `eq:flatpullback`, entry `uu`: `(Xu² + Yu² + Zu²)/h⁴ = Σ · 4/h² + a² η_u²`. -/
theorem flat_uu : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Frac.eqn ⟨Xu * Xu + Yu * Yu + Zu * Zu, hF ^ 4⟩
      (SF * oF + Frac.ofZ (a ^ 2) * (eU * eU)))) :=
  derive_imp _ _ (by flat_poly)

/-- `eq:flatpullback`, entry `uz`: `(Xu Xz + Yu Yz + Zu Zz)/h⁴ = a² η_u η_z`. -/
theorem flat_uz : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Frac.eqn ⟨Xu * Xz + Yu * Yz + Zu * Zz, hF ^ 4⟩ (Frac.ofZ (a ^ 2) * (eU * eZ)))) :=
  derive_imp _ _ (by flat_poly)

/-- `eq:flatpullback`, entry `zz`: `(Xz² + Yz² + Zz²)/h⁴ = Σ · 4/h² + a² η_z²`. -/
theorem flat_zz : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Frac.eqn ⟨Xz * Xz + Yz * Yz + Zz * Zz, hF ^ 4⟩
      (SF * oF + Frac.ofZ (a ^ 2) * (eZ * eZ)))) :=
  derive_imp _ _ (by flat_poly)

/-- The Jacobian of `(X, Y, Z)` with respect to `(r, u, z)`: the determinant of the numerators
is `4 (r² h² + a² (1 − u² − z²)²) h²`, so the Jacobian determinant is
`4 (r² h² + a² (1 − u² − z²)²)/h⁴ = 4Σ/h²`. -/
theorem flat_jacobian : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (det3 ⟨Xr, Xu, Xz⟩ ⟨Yr, Yu, Yz⟩ ⟨Zr, Zu, Zz⟩,
      4 * (r ^ 2 * hF ^ 2 + a ^ 2 * (1 - u ^ 2 - z ^ 2) ^ 2) * hF ^ 2)) :=
  derive_imp _ _ (by ipra_poly R ρ h [hF, Xr, Xu, Xz, Yr, Yu, Yz, Zr, Zu, Zz]; ring)

/-- `Σ = r² + a² x² = (r² h² + a² (1 − u² − z²)²)/h²` in the stereographic chart. -/
theorem flat_sigma : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Frac.eqn SF ⟨r ^ 2 * hF ^ 2 + a ^ 2 * (1 - u ^ 2 - z ^ 2) ^ 2, hF ^ 2⟩)) :=
  derive_imp _ _ (by flat_poly)

end Flat

end LeanProofs.IPRA.Geometry.KerrNewmanAtlas
