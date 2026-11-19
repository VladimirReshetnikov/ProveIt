import IPRADerivations.Foundations.FormalDerivation

/-!
# The Maxwell field of the Kerr–Newman family by formal derivations (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, Section "The Maxwell field and the Einstein
equation", and the tests of `thm:arithmetic` ("every component of `eq:EM`–`eq:maxwell`, with
formal rational differentiation"). The metric is `eq:master` with the radial function left as
an indeterminate `d` (the field does not contain it: "these expressions do not contain `d` or
`Δ`: they hold for the general radial-function metric of `lem:offshell` as well"), in the
coordinates `(t, r, x, φ)` (index `p` for `φ`), with `Σ = r² + a² x²`, `s = 1 − x²`,
`P = r² + a²`, and the derivations `∂_r`, `∂_x` of `Foundations/FormalDerivation`
(`∂_t = ∂_φ = 0`).

* The potential `eq:potential`, `A = −(q r/Σ) p`: `A_t = −q r/Σ`, `A_φ = q r a s/Σ`.
* `field_rt`, `field_rp`, `field_xt`, `field_xp` (`eq:Ftable`): `F_{μν} = ∂_μ A_ν − ∂_ν A_μ` gives
  `F_rt = E`, `F_rφ = −a s E`, `F_xt = a 𝓑`, `F_xφ = −P 𝓑`, with `E = q (r² − a² x²)/Σ²`,
  `𝓑 = 2 q a r x/Σ²` (`eq:EB`).
* `closed_t`, `closed_p` (`eq:dF`): `∂_r F_xt − ∂_x F_rt = 0`, `∂_r F_xφ − ∂_x F_rφ = 0`, the two
  components of `dF = 0` that are not identically trivial.
* `raise_rt`, `raise_rp`, `raise_xt`, `raise_xp` (`eq:density`): raising both indices with
  `eq:ginv`, `Σ F^{rt} = −P E`, `Σ F^{rφ} = −a E`, `Σ F^{xt} = −a s 𝓑`, `Σ F^{xφ} = −𝓑`; the
  radial function `d` cancels.
* `maxwell_t`, `maxwell_p` (`eq:maxwell`, `eq:twoMaxwell`): `∂_r(Σ F^{rν}) + ∂_x(Σ F^{xν}) = 0`
  for `ν = t, φ` (for `ν = r, x` every term is a derivative along `t` or `φ`).
* `F2_electric`, `F2_magnetic` (`eq:F2`): `F_rt F^{rt} + F_rφ F^{rφ} = −E²` and
  `F_xt F^{xt} + F_xφ F^{xφ} = 𝓑²`, so `F_{αβ} F^{αβ} = 2 (𝓑² − E²)`.
* `field_norm` (`eq:sumSquares`): `E² + 𝓑² = q²/Σ²`.
* The stress tensor of `eq:EM`,
  `T_{μν} = 2 (Σ_{ρ,σ} F_{μρ} g^{ρσ} F_{νσ} − ¼ g_{μν} F_{αβ} F^{αβ})`, in coordinates: each
  nonvanishing term is reduced over a common denominator (`Tμν_tk`) and
  `stress_tt`, `stress_tp`, `stress_pp`, `stress_rr`, `stress_xx`, `stress_rx` give
  `T_tt = (E² + 𝓑²)(d/Σ + s a²/Σ)`, `T_tφ = −(E² + 𝓑²)(d a s + s a P)/Σ`,
  `T_φφ = (E² + 𝓑²)(d a² s² + s P²)/Σ`, `T_rr = −(E² + 𝓑²) Σ/d`, `T_xx = (E² + 𝓑²) Σ/s`,
  `T_rx = 0`: the components of `eq:stress`,
  `(E² + 𝓑²)((d/Σ) p² − (Σ/d) dr² + (Σ/s) dx² + (s/Σ) b²)`. The entries `T_tr`, `T_tx`, `T_rφ`,
  `T_xφ` have no nonvanishing term.

With `Geometry/KerrNewmanRicci` this is the Einstein–Maxwell equation `eq:EM` for the
Kerr–Newman metric: there `R_{μν} = U (…) + V (…)` with the same four tensors, and
`U = V = q²/Σ²` for `d = Δ` (`kn_N`, `kn_w`), while here `T_{μν} = (E² + 𝓑²)(…)` and
`E² + 𝓑² = q²/Σ²`.

The numerators of the stress terms were proposed by a computer algebra script; every identity
is checked by Lean as an identity of fractions cleared of denominators, a closed sentence of
iPRA certified in every commutative ring.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanMaxwell

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

local notation "r" => (ZExp.var 0 : ZExp 5)
local notation "x" => (ZExp.var 1 : ZExp 5)
local notation "a" => (ZExp.var 2 : ZExp 5)
local notation "d" => (ZExp.var 3 : ZExp 5)
local notation "q" => (ZExp.var 4 : ZExp 5)

/-- `∂_r`: `r ↦ 1`, and `0` on the other variables (no derivative of `d` is taken). -/
def δr : Fin 5 → ZExp 5
  | ⟨0, _⟩ => 1
  | _ => 0

/-- `∂_x`: `x ↦ 1`, and `0` on the other variables. -/
def δx : Fin 5 → ZExp 5
  | ⟨1, _⟩ => 1
  | _ => 0

theorem δr_0 : δr 0 = 1 := rfl
theorem δr_1 : δr 1 = 0 := rfl
theorem δr_2 : δr 2 = 0 := rfl
theorem δr_3 : δr 3 = 0 := rfl
theorem δr_4 : δr 4 = 0 := rfl
theorem δx_0 : δx 0 = 0 := rfl
theorem δx_1 : δx 1 = 1 := rfl
theorem δx_2 : δx 2 = 0 := rfl
theorem δx_3 : δx 3 = 0 := rfl
theorem δx_4 : δx 4 = 0 := rfl

/-- `Σ = r² + a² x²`. -/
def Sg : ZExp 5 := r ^ 2 + a ^ 2 * x ^ 2
/-- `s = 1 − x²`. -/
def sx : ZExp 5 := 1 - x ^ 2
/-- `P = r² + a²`. -/
def Pp : ZExp 5 := r ^ 2 + a ^ 2

/-! ## The metric `eq:master` with `Δ` replaced by `d`, and `eq:ginv` -/

/-- `g_tt = (−d + a² s)/Σ`. -/
def gtt : Frac 5 := ⟨-d + a ^ 2 * sx, Sg⟩
/-- `g_tφ = −a s (P − d)/Σ`. -/
def gtp : Frac 5 := ⟨-(a * sx * (Pp - d)), Sg⟩
/-- `g_φφ = s (P² − a² d s)/Σ`. -/
def gpp : Frac 5 := ⟨sx * (Pp ^ 2 - a ^ 2 * d * sx), Sg⟩
/-- `g_rr = Σ/d`. -/
def grr : Frac 5 := ⟨Sg, d⟩
/-- `g_xx = Σ/s`. -/
def gxx : Frac 5 := ⟨Sg, sx⟩
/-- `g^tt = −(P² − a² d s)/(dΣ)`. -/
def itt : Frac 5 := ⟨-(Pp ^ 2 - a ^ 2 * d * sx), d * Sg⟩
/-- `g^tφ = −a (P − d)/(dΣ)`. -/
def itp : Frac 5 := ⟨-(a * (Pp - d)), d * Sg⟩
/-- `g^φφ = (d − a² s)/(d s Σ)`. -/
def ipp : Frac 5 := ⟨d - a ^ 2 * sx, d * sx * Sg⟩
/-- `g^rr = d/Σ`. -/
def irr : Frac 5 := ⟨d, Sg⟩
/-- `g^xx = s/Σ`. -/
def ixx : Frac 5 := ⟨sx, Sg⟩

/-! ## The potential and the field -/

/-- The numerator of `E`: `q (r² − a² x²)`. -/
def En : ZExp 5 := q * (r ^ 2 - a ^ 2 * x ^ 2)
/-- The numerator of `𝓑`: `2 q a r x`. -/
def Bn : ZExp 5 := 2 * q * a * r * x
/-- `E = q (r² − a² x²)/Σ²`. -/
def Ef : Frac 5 := ⟨En, Sg ^ 2⟩
/-- `𝓑 = 2 q a r x/Σ²`. -/
def Bf : Frac 5 := ⟨Bn, Sg ^ 2⟩
/-- `A_t = −q r/Σ`. -/
def At : Frac 5 := ⟨-(q * r), Sg⟩
/-- `A_φ = q r a s/Σ`. -/
def Ap : Frac 5 := ⟨q * r * a * sx, Sg⟩
/-- `F_rt = E`. -/
def Frt : Frac 5 := ⟨En, Sg ^ 2⟩
/-- `F_rφ = −a s E`. -/
def Frp : Frac 5 := ⟨-(a * sx * En), Sg ^ 2⟩
/-- `F_xt = a 𝓑`. -/
def Fxt : Frac 5 := ⟨a * Bn, Sg ^ 2⟩
/-- `F_xφ = −P 𝓑`. -/
def Fxp : Frac 5 := ⟨-(Pp * Bn), Sg ^ 2⟩
/-- `F^{rt} = −P E/Σ`. -/
def Urt : Frac 5 := ⟨-(Pp * En), Sg ^ 3⟩
/-- `F^{rφ} = −a E/Σ`. -/
def Urp : Frac 5 := ⟨-(a * En), Sg ^ 3⟩
/-- `F^{xt} = −a s 𝓑/Σ`. -/
def Uxt : Frac 5 := ⟨-(a * sx * Bn), Sg ^ 3⟩
/-- `F^{xφ} = −𝓑/Σ`. -/
def Uxp : Frac 5 := ⟨-Bn, Sg ^ 3⟩
/-- `E² + 𝓑²`. -/
def EB2 : Frac 5 := Ef * Ef + Bf * Bf

/-- Certificates of the hand-written statements of this module. -/
macro "mx_poly" : tactic =>
  `(tactic| (frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx,
      itt, itp, ipp, irr, ixx, Urt, Urp, Uxt, Uxp, EB2, En, Bn, Sg, sx, Pp,
      δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]; ring))

/-- `F_rt = ∂_r A_t = E`. -/
theorem field_rt :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5) (imp [] (Frac.eqn (Frac.d δr At) Frt)) :=
  derive_imp _ _ (by mx_poly)

/-- `F_rφ = ∂_r A_φ = −a s E`. -/
theorem field_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5) (imp [] (Frac.eqn (Frac.d δr Ap) Frp)) :=
  derive_imp _ _ (by mx_poly)

/-- `F_xt = ∂_x A_t = a 𝓑`. -/
theorem field_xt :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5) (imp [] (Frac.eqn (Frac.d δx At) Fxt)) :=
  derive_imp _ _ (by mx_poly)

/-- `F_xφ = ∂_x A_φ = −P 𝓑`. -/
theorem field_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5) (imp [] (Frac.eqn (Frac.d δx Ap) Fxp)) :=
  derive_imp _ _ (by mx_poly)

/-- `eq:dF` for `(r, x, t)`: `∂_r F_xt − ∂_x F_rt = 0`. -/
theorem closed_t :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δr Fxt - Frac.d δx Frt) (Frac.ofZ 0))) :=
  derive_imp _ _ (by mx_poly)

/-- `eq:dF` for `(r, x, φ)`: `∂_r F_xφ − ∂_x F_rφ = 0`. -/
theorem closed_p :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δr Fxp - Frac.d δx Frp) (Frac.ofZ 0))) :=
  derive_imp _ _ (by mx_poly)

/-! ## Raising the indices (`eq:density`) -/

/-- `F^{rt} = g^{rr} (g^{tt} F_rt + g^{tφ} F_rφ) = −P E/Σ`. -/
theorem raise_rt :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (irr * (itt * Frt + itp * Frp)) Urt)) :=
  derive_imp _ _ (by mx_poly)

/-- `F^{rφ} = g^{rr} (g^{φt} F_rt + g^{φφ} F_rφ) = −a E/Σ`. -/
theorem raise_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (irr * (itp * Frt + ipp * Frp)) Urp)) :=
  derive_imp _ _ (by mx_poly)

/-- `F^{xt} = g^{xx} (g^{tt} F_xt + g^{tφ} F_xφ) = −a s 𝓑/Σ`. -/
theorem raise_xt :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (ixx * (itt * Fxt + itp * Fxp)) Uxt)) :=
  derive_imp _ _ (by mx_poly)

/-- `F^{xφ} = g^{xx} (g^{φt} F_xt + g^{φφ} F_xφ) = −𝓑/Σ`. -/
theorem raise_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (ixx * (itp * Fxt + ipp * Fxp)) Uxp)) :=
  derive_imp _ _ (by mx_poly)

/-! ## The divergence equation (`eq:maxwell`) -/

/-- `∂_r(Σ F^{rt}) + ∂_x(Σ F^{xt}) = 0`. -/
theorem maxwell_t :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δr (Frac.ofZ Sg * Urt) + Frac.d δx (Frac.ofZ Sg * Uxt))
        (Frac.ofZ 0))) :=
  derive_imp _ _ (by mx_poly)

/-- `∂_r(Σ F^{rφ}) + ∂_x(Σ F^{xφ}) = 0`. -/
theorem maxwell_p :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δr (Frac.ofZ Sg * Urp) + Frac.d δx (Frac.ofZ Sg * Uxp))
        (Frac.ofZ 0))) :=
  derive_imp _ _ (by mx_poly)

/-! ## The invariants (`eq:F2`, `eq:sumSquares`) -/

/-- `F_rt F^{rt} + F_rφ F^{rφ} = −E²`. -/
theorem F2_electric :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frt * Urt + Frp * Urp) (-(Ef * Ef)))) :=
  derive_imp _ _ (by mx_poly)

/-- `F_xt F^{xt} + F_xφ F^{xφ} = 𝓑²`. -/
theorem F2_magnetic :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Fxt * Uxt + Fxp * Uxp) (Bf * Bf))) :=
  derive_imp _ _ (by mx_poly)

/-- `E² + 𝓑² = q²/Σ²`. -/
theorem field_norm :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5) (imp [] (Frac.eqn EB2 ⟨q ^ 2, Sg ^ 2⟩)) :=
  derive_imp _ _ (by mx_poly)

/-! ## The stress tensor of `eq:EM` -/

/-! ## The entry `T_{tt}` -/

/-- The common denominator of the terms of `T_{tt}`. -/
def Ttt_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `2 F_{tr} g^{rr} F_{tr}` over the common denominator. -/
def Ttt_n1 : ZExp 5 := 2 * d * q ^ 2 * (a * x - r) ^ 2 * (a * x + r) ^ 2
/-- `2 F_{tr} g^{rr} F_{tr}`, reduced to the common denominator. -/
theorem Ttt_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Frt * irr * Frt)) (⟨Ttt_n1, Ttt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Ttt_n1, Ttt_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{tx} g^{xx} F_{tx}` over the common denominator. -/
def Ttt_n2 : ZExp 5 := -8 * a ^ 4 * q ^ 2 * r ^ 2 * x ^ 2 * (x - 1) * (x + 1)
/-- `2 F_{tx} g^{xx} F_{tx}`, reduced to the common denominator. -/
theorem Ttt_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fxt * ixx * Fxt)) (⟨Ttt_n2, Ttt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Ttt_n2, Ttt_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g_{tt} F_{αβ} F^{αβ} = g_{tt} (𝓑² − E²)` over the common denominator. -/
def Ttt_n3 : ZExp 5 := q ^ 2 * (a ^ 2 * x ^ 2 - a ^ 2 + d) * (a ^ 2 * x ^ 2 - 2 * a * r * x - r ^
    2) * (a ^ 2 * x ^ 2 + 2 * a * r * x - r ^ 2)
/-- `½ g_{tt} F_{αβ} F^{αβ} = g_{tt} (𝓑² − E²)`, reduced to the common denominator. -/
theorem Ttt_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gtt * (Bf * Bf - Ef * Ef)) (⟨Ttt_n3, Ttt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Ttt_n3, Ttt_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `T_{tt}` (`eq:stress` in coordinates): the signed sum of its terms is `EB2 * (⟨d, Sg⟩ + ⟨sx * a
^ 2, Sg⟩)`. -/
theorem stress_tt :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Ttt_n1 + Ttt_n2 - Ttt_n3, Ttt_cd⟩) (EB2 * (⟨d, Sg⟩ + ⟨sx * a ^ 2, Sg⟩))))
          :=
  derive_imp _ _ (by
    frac_poly R ρ h [Ttt_n1, Ttt_n2, Ttt_n3, Ttt_cd, EB2, At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt,
        gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, δr_0,
        δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ## The entry `T_{tp}` -/

/-- The common denominator of the terms of `T_{tp}`. -/
def Ttp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `2 F_{tr} g^{rr} F_{pr}` over the common denominator. -/
def Ttp_n1 : ZExp 5 := 2 * a * d * q ^ 2 * (x - 1) * (x + 1) * (a * x - r) ^ 2 * (a * x + r) ^ 2
/-- `2 F_{tr} g^{rr} F_{pr}`, reduced to the common denominator. -/
theorem Ttp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Frt * irr * Frp)) (⟨Ttp_n1, Ttp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Ttp_n1, Ttp_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{tx} g^{xx} F_{px}` over the common denominator. -/
def Ttp_n2 : ZExp 5 := 8 * a ^ 3 * q ^ 2 * r ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1)
/-- `2 F_{tx} g^{xx} F_{px}`, reduced to the common denominator. -/
theorem Ttp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fxt * ixx * Fxp)) (⟨Ttp_n2, Ttp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Ttp_n2, Ttp_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g_{tp} F_{αβ} F^{αβ} = g_{tp} (𝓑² − E²)` over the common denominator. -/
def Ttp_n3 : ZExp 5 := -a * q ^ 2 * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (a ^ 2 * x ^ 2 - 2 *
    a * r * x - r ^ 2) * (a ^ 2 * x ^ 2 + 2 * a * r * x - r ^ 2)
/-- `½ g_{tp} F_{αβ} F^{αβ} = g_{tp} (𝓑² − E²)`, reduced to the common denominator. -/
theorem Ttp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gtp * (Bf * Bf - Ef * Ef)) (⟨Ttp_n3, Ttp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Ttp_n3, Ttp_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `T_{tp}` (`eq:stress` in coordinates): the signed sum of its terms is `-(EB2 * (⟨d * a * sx,
Sg⟩ + ⟨sx * a * Pp, Sg⟩))`. -/
theorem stress_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Ttp_n1 + Ttp_n2 - Ttp_n3, Ttp_cd⟩) (-(EB2 * (⟨d * a * sx, Sg⟩ + ⟨sx * a *
          Pp, Sg⟩))))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Ttp_n1, Ttp_n2, Ttp_n3, Ttp_cd, EB2, At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt,
        gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, δr_0,
        δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ## The entry `T_{rr}` -/

/-- The common denominator of the terms of `T_{rr}`. -/
def Trr_cd : ZExp 5 := d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `2 F_{rt} g^{tt} F_{rt}` over the common denominator. -/
def Trr_n1 : ZExp 5 := -2 * q ^ 2 * (a * x - r) ^ 2 * (a * x + r) ^ 2 * (a ^ 4 + a ^ 2 * d * x ^ 2
    - a ^ 2 * d + 2 * a ^ 2 * r ^ 2 + r ^ 4)
/-- `2 F_{rt} g^{tt} F_{rt}`, reduced to the common denominator. -/
theorem Trr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Frt * itt * Frt)) (⟨Trr_n1, Trr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Trr_n1, Trr_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{rt} g^{tp} F_{rp}` over the common denominator. -/
def Trr_n2 : ZExp 5 := -2 * a ^ 2 * q ^ 2 * (x - 1) * (x + 1) * (a * x - r) ^ 2 * (a * x + r) ^ 2 *
    (a ^ 2 - d + r ^ 2)
/-- `2 F_{rt} g^{tp} F_{rp}`, reduced to the common denominator. -/
theorem Trr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Frt * itp * Frp)) (⟨Trr_n2, Trr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Trr_n2, Trr_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{rp} g^{pt} F_{rt}` over the common denominator. -/
def Trr_n3 : ZExp 5 := -2 * a ^ 2 * q ^ 2 * (x - 1) * (x + 1) * (a * x - r) ^ 2 * (a * x + r) ^ 2 *
    (a ^ 2 - d + r ^ 2)
/-- `2 F_{rp} g^{pt} F_{rt}`, reduced to the common denominator. -/
theorem Trr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Frp * itp * Frt)) (⟨Trr_n3, Trr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Trr_n3, Trr_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{rp} g^{pp} F_{rp}` over the common denominator. -/
def Trr_n4 : ZExp 5 := -2 * a ^ 2 * q ^ 2 * (x - 1) * (x + 1) * (a * x - r) ^ 2 * (a * x + r) ^ 2 *
    (a ^ 2 * x ^ 2 - a ^ 2 + d)
/-- `2 F_{rp} g^{pp} F_{rp}`, reduced to the common denominator. -/
theorem Trr_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Frp * ipp * Frp)) (⟨Trr_n4, Trr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Trr_n4, Trr_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g_{rr} F_{αβ} F^{αβ} = g_{rr} (𝓑² − E²)` over the common denominator. -/
def Trr_n5 : ZExp 5 := -q ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * x ^ 2 - 2 * a * r * x - r ^
    2) * (a ^ 2 * x ^ 2 + 2 * a * r * x - r ^ 2)
/-- `½ g_{rr} F_{αβ} F^{αβ} = g_{rr} (𝓑² − E²)`, reduced to the common denominator. -/
theorem Trr_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (grr * (Bf * Bf - Ef * Ef)) (⟨Trr_n5, Trr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Trr_n5, Trr_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `T_{rr}` (`eq:stress` in coordinates): the signed sum of its terms is `-(EB2 * ⟨Sg, d⟩)`. -/
theorem stress_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Trr_n1 + Trr_n2 + Trr_n3 + Trr_n4 - Trr_n5, Trr_cd⟩) (-(EB2 * ⟨Sg, d⟩))))
          :=
  derive_imp _ _ (by
    frac_poly R ρ h [Trr_n1, Trr_n2, Trr_n3, Trr_n4, Trr_n5, Trr_cd, EB2, At, Ap, Ef, Bf, Frt, Frp,
        Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg,
        sx, Pp, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ## The entry `T_{rx}` -/

/-- The common denominator of the terms of `T_{rx}`. -/
def Trx_cd : ZExp 5 := d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `2 F_{rt} g^{tt} F_{xt}` over the common denominator. -/
def Trx_n1 : ZExp 5 := 4 * a ^ 2 * q ^ 2 * r * x * (a * x - r) * (a * x + r) * (a ^ 4 + a ^ 2 * d *
    x ^ 2 - a ^ 2 * d + 2 * a ^ 2 * r ^ 2 + r ^ 4)
/-- `2 F_{rt} g^{tt} F_{xt}`, reduced to the common denominator. -/
theorem Trx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Frt * itt * Fxt)) (⟨Trx_n1, Trx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Trx_n1, Trx_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{rt} g^{tp} F_{xp}` over the common denominator. -/
def Trx_n2 : ZExp 5 := -4 * a ^ 2 * q ^ 2 * r * x * (a ^ 2 + r ^ 2) * (a * x - r) * (a * x + r) *
    (a ^ 2 - d + r ^ 2)
/-- `2 F_{rt} g^{tp} F_{xp}`, reduced to the common denominator. -/
theorem Trx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Frt * itp * Fxp)) (⟨Trx_n2, Trx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Trx_n2, Trx_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{rp} g^{pt} F_{xt}` over the common denominator. -/
def Trx_n3 : ZExp 5 := 4 * a ^ 4 * q ^ 2 * r * x * (x - 1) * (x + 1) * (a * x - r) * (a * x + r) *
    (a ^ 2 - d + r ^ 2)
/-- `2 F_{rp} g^{pt} F_{xt}`, reduced to the common denominator. -/
theorem Trx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Frp * itp * Fxt)) (⟨Trx_n3, Trx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Trx_n3, Trx_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{rp} g^{pp} F_{xp}` over the common denominator. -/
def Trx_n4 : ZExp 5 := -4 * a ^ 2 * q ^ 2 * r * x * (a ^ 2 + r ^ 2) * (a * x - r) * (a * x + r) *
    (a ^ 2 * x ^ 2 - a ^ 2 + d)
/-- `2 F_{rp} g^{pp} F_{xp}`, reduced to the common denominator. -/
theorem Trx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Frp * ipp * Fxp)) (⟨Trx_n4, Trx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Trx_n4, Trx_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `T_{rx}` (`eq:stress` in coordinates): the signed sum of its terms is `Frac.ofZ 0`. -/
theorem stress_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Trx_n1 + Trx_n2 + Trx_n3 + Trx_n4, Trx_cd⟩) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Trx_n1, Trx_n2, Trx_n3, Trx_n4, Trx_cd, EB2, At, Ap, Ef, Bf, Frt, Frp, Fxt,
        Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx,
        Pp, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ## The entry `T_{xx}` -/

/-- The common denominator of the terms of `T_{xx}`. -/
def Txx_cd : ZExp 5 := d * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `2 F_{xt} g^{tt} F_{xt}` over the common denominator. -/
def Txx_n1 : ZExp 5 := -8 * a ^ 4 * q ^ 2 * r ^ 2 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 4 + a ^ 2 * d
    * x ^ 2 - a ^ 2 * d + 2 * a ^ 2 * r ^ 2 + r ^ 4)
/-- `2 F_{xt} g^{tt} F_{xt}`, reduced to the common denominator. -/
theorem Txx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fxt * itt * Fxt)) (⟨Txx_n1, Txx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Txx_n1, Txx_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{xt} g^{tp} F_{xp}` over the common denominator. -/
def Txx_n2 : ZExp 5 := 8 * a ^ 4 * q ^ 2 * r ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a
    ^ 2 - d + r ^ 2)
/-- `2 F_{xt} g^{tp} F_{xp}`, reduced to the common denominator. -/
theorem Txx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fxt * itp * Fxp)) (⟨Txx_n2, Txx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Txx_n2, Txx_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{xp} g^{pt} F_{xt}` over the common denominator. -/
def Txx_n3 : ZExp 5 := 8 * a ^ 4 * q ^ 2 * r ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a
    ^ 2 - d + r ^ 2)
/-- `2 F_{xp} g^{pt} F_{xt}`, reduced to the common denominator. -/
theorem Txx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fxp * itp * Fxt)) (⟨Txx_n3, Txx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Txx_n3, Txx_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{xp} g^{pp} F_{xp}` over the common denominator. -/
def Txx_n4 : ZExp 5 := -8 * a ^ 2 * q ^ 2 * r ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * x ^ 2 -
    a ^ 2 + d)
/-- `2 F_{xp} g^{pp} F_{xp}`, reduced to the common denominator. -/
theorem Txx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fxp * ipp * Fxp)) (⟨Txx_n4, Txx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Txx_n4, Txx_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g_{xx} F_{αβ} F^{αβ} = g_{xx} (𝓑² − E²)` over the common denominator. -/
def Txx_n5 : ZExp 5 := d * q ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * x ^ 2 - 2 * a * r * x - r
    ^ 2) * (a ^ 2 * x ^ 2 + 2 * a * r * x - r ^ 2)
/-- `½ g_{xx} F_{αβ} F^{αβ} = g_{xx} (𝓑² − E²)`, reduced to the common denominator. -/
theorem Txx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gxx * (Bf * Bf - Ef * Ef)) (⟨Txx_n5, Txx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Txx_n5, Txx_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `T_{xx}` (`eq:stress` in coordinates): the signed sum of its terms is `EB2 * ⟨Sg, sx⟩`. -/
theorem stress_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Txx_n1 + Txx_n2 + Txx_n3 + Txx_n4 - Txx_n5, Txx_cd⟩) (EB2 * ⟨Sg, sx⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Txx_n1, Txx_n2, Txx_n3, Txx_n4, Txx_n5, Txx_cd, EB2, At, Ap, Ef, Bf, Frt, Frp,
        Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg,
        sx, Pp, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ## The entry `T_{pp}` -/

/-- The common denominator of the terms of `T_{pp}`. -/
def Tpp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `2 F_{pr} g^{rr} F_{pr}` over the common denominator. -/
def Tpp_n1 : ZExp 5 := 2 * a ^ 2 * d * q ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a * x - r) ^ 2 * (a * x
    + r) ^ 2
/-- `2 F_{pr} g^{rr} F_{pr}`, reduced to the common denominator. -/
theorem Tpp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Frp * irr * Frp)) (⟨Tpp_n1, Tpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Tpp_n1, Tpp_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{px} g^{xx} F_{px}` over the common denominator. -/
def Tpp_n2 : ZExp 5 := -8 * a ^ 2 * q ^ 2 * r ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) ^ 2 * (x - 1) * (x + 1)
/-- `2 F_{px} g^{xx} F_{px}`, reduced to the common denominator. -/
theorem Tpp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fxp * ixx * Fxp)) (⟨Tpp_n2, Tpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Tpp_n2, Tpp_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g_{pp} F_{αβ} F^{αβ} = g_{pp} (𝓑² − E²)` over the common denominator. -/
def Tpp_n3 : ZExp 5 := q ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 - 2 * a * r * x - r ^ 2) * (a ^ 2
    * x ^ 2 + 2 * a * r * x - r ^ 2) * (a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + 2 * a ^ 2 * r ^ 2 +
    r ^ 4)
/-- `½ g_{pp} F_{αβ} F^{αβ} = g_{pp} (𝓑² − E²)`, reduced to the common denominator. -/
theorem Tpp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gpp * (Bf * Bf - Ef * Ef)) (⟨Tpp_n3, Tpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt, gtp, gpp, grr, gxx, itt, itp, ipp,
        irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, Tpp_n3, Tpp_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `T_{pp}` (`eq:stress` in coordinates): the signed sum of its terms is `EB2 * (⟨d * a ^ 2 * sx ^
2, Sg⟩ + ⟨sx * Pp ^ 2, Sg⟩)`. -/
theorem stress_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Tpp_n1 + Tpp_n2 - Tpp_n3, Tpp_cd⟩) (EB2 * (⟨d * a ^ 2 * sx ^ 2, Sg⟩ + ⟨sx
          * Pp ^ 2, Sg⟩)))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Tpp_n1, Tpp_n2, Tpp_n3, Tpp_cd, EB2, At, Ap, Ef, Bf, Frt, Frp, Fxt, Fxp, gtt,
        gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Urt, Urp, Uxt, Uxp, En, Bn, Sg, sx, Pp, δr_0,
        δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)


end LeanProofs.IPRA.Geometry.KerrNewmanMaxwell
