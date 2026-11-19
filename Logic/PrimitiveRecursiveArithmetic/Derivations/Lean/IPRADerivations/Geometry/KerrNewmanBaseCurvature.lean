import IPRADerivations.Geometry.KerrNewmanBase

/-!
# The base block of the radial-function metric: curvature (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, proof of `lem:offshell`, `eq:basecurv`:
"Put `W = 2d(r² − a² x²) − r v Σ + 2a²((2r² + a²) x² − r²)`. Differentiating `eq:basegamma` in
the two-dimensional version of `eq:ricci` yields
`R(h)_{rr} = W/(2dΣ²)`, `R(h)_{rx} = 0`, `R(h)_{xx} = W/(2sΣ²)`."

The convention `eq:ricci` in two dimensions, for the base metric `h = diag(Σ/d, Σ/s)`:

`R_{ij} = Σ_k ∂_k γ^k_{ij} − ∂_j Σ_k γ^k_{ik} +
        Σ_k γ^k_{ij} Σ_l γ^l_{kl} − Σ_{k,l} γ^l_{ik} γ^k_{jl}`.

The connection coefficients are the fractions of `eq:basegamma` (`Grrr`, …, `Gxxx`; they are the
coefficients of `h` by `Geometry/KerrNewmanBase.gamma_rrr`, …), with the traces
`trR = γ^r_{rr} + γ^x_{rx}`, `trX = γ^r_{rx} + γ^x_{xx}`. For each entry `(i, j)` the formula has
nine terms. Each term, with its derivative taken by the formal derivations `∂_r`, `∂_x` of
`Foundations/FormalDerivation`, is reduced to a numerator over one common denominator
(`rr_t1`, …, `rr_t9`, and likewise `rx_t*`, `xx_t*`), and the signed sum of the nine
numerators is the stated fraction:

* `ricci_rr`: `R(h)_{rr} = W/(2dΣ²)`;
* `ricci_rx`: `R(h)_{rx} = 0`;
* `ricci_xx`: `R(h)_{xx} = W/(2sΣ²)`.

The numerators were proposed by a computer algebra script; every identity here is checked by
Lean as an identity of fractions cleared of denominators, a closed sentence of iPRA certified in
every commutative ring. The signs of the nine terms in each sum follow the displayed formula:
`+ t1 + t2 − t3 + t4 + t5 − t6 − t7 − t8 − t9`.

Not derived: the fiber block, the traces `eq:traces` and the assembly of `lem:offshell`.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanBaseCurvature

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.KerrNewmanBase
open ZExp

local notation "r" => (ZExp.var 0 : ZExp 6)
local notation "x" => (ZExp.var 1 : ZExp 6)
local notation "a" => (ZExp.var 2 : ZExp 6)
local notation "d" => (ZExp.var 3 : ZExp 6)
local notation "v" => (ZExp.var 4 : ZExp 6)
local notation "w" => (ZExp.var 5 : ZExp 6)

/-- `γ^r_{rr} = r/Σ − v/(2d)`. -/
def Grrr : Frac 6 := ⟨r, Sg⟩ - ⟨v, 2 * d⟩
/-- `γ^r_{rx} = a² x/Σ`. -/
def Grrx : Frac 6 := ⟨a ^ 2 * x, Sg⟩
/-- `γ^r_{xx} = −r d/(Σ s)`. -/
def Grxx : Frac 6 := -⟨r * d, Sg * sx⟩
/-- `γ^x_{rr} = −a² x s/(Σ d)`. -/
def Gxrr : Frac 6 := -⟨a ^ 2 * x * sx, Sg * d⟩
/-- `γ^x_{rx} = r/Σ`. -/
def Gxrx : Frac 6 := ⟨r, Sg⟩
/-- `γ^x_{xx} = a² x/Σ + x/s`. -/
def Gxxx : Frac 6 := ⟨a ^ 2 * x, Sg⟩ + ⟨x, sx⟩
/-- `Σ_k γ^k_{rk}`. -/
def trR : Frac 6 := Grrr + Gxrx
/-- `Σ_k γ^k_{xk}`. -/
def trX : Frac 6 := Grrx + Gxxx

/-- `W = 2d(r² − a² x²) − r v Σ + 2a²((2r² + a²) x² − r²)` (`eq:W`). -/
def Wn : ZExp 6 :=
  2 * d * (r ^ 2 - a ^ 2 * x ^ 2) - r * v * Sg + 2 * a ^ 2 * ((2 * r ^ 2 + a ^ 2) * x ^ 2 - r ^ 2)

/-! ## The common denominators and the numerators of the terms -/

/-- The common denominator of the terms of `R(h)_{rr}`. -/
def cd_rr : ZExp 6 := 4 * Sg ^ 2 * d ^ 2
/-- `∂_r γ^r_{rr}`, over the common denominator. -/
def rr_t1_n : ZExp 6 := -2 * Sg ^ 2 * d * w + 2 * Sg ^ 2 * v ^ 2 + 4 * Sg * d ^ 2 -
    8 * d ^ 2 * r ^ 2
/-- `∂_x γ^x_{rr}`, over the common denominator. -/
def rr_t2_n : ZExp 6 := -4 * Sg * a ^ 2 * d * sx + 8 * Sg * a ^ 2 * d * x ^ 2 +
    8 * a ^ 4 * d * sx * x ^ 2
/-- `∂_r Σ_k γ^k_{rk}`, over the common denominator. -/
def rr_t3_n : ZExp 6 := -2 * Sg ^ 2 * d * w + 2 * Sg ^ 2 * v ^ 2 + 8 * Sg * d ^ 2 -
    16 * d ^ 2 * r ^ 2
/-- `γ^r_{rr} Σ_l γ^l_{rl}`, over the common denominator. -/
def rr_t4_n : ZExp 6 := Sg ^ 2 * v ^ 2 - 6 * Sg * d * r * v + 8 * d ^ 2 * r ^ 2
/-- `γ^x_{rr} Σ_l γ^l_{xl}`, over the common denominator. -/
def rr_t5_n : ZExp 6 := -4 * Sg * a ^ 2 * d * x ^ 2 - 8 * a ^ 4 * d * sx * x ^ 2
/-- `γ^r_{rr} γ^r_{rr}`, over the common denominator. -/
def rr_t6_n : ZExp 6 := Sg ^ 2 * v ^ 2 - 4 * Sg * d * r * v + 4 * d ^ 2 * r ^ 2
/-- `γ^x_{rr} γ^r_{rx}`, over the common denominator. -/
def rr_t7_n : ZExp 6 := -4 * a ^ 4 * d * sx * x ^ 2
/-- `γ^r_{rx} γ^x_{rr}`, over the common denominator. -/
def rr_t8_n : ZExp 6 := -4 * a ^ 4 * d * sx * x ^ 2
/-- `γ^x_{rx} γ^x_{rx}`, over the common denominator. -/
def rr_t9_n : ZExp 6 := 4 * d ^ 2 * r ^ 2
/-- The common denominator of the terms of `R(h)_{rx}`. -/
def cd_rx : ZExp 6 := 2 * Sg ^ 2 * d * sx
/-- `∂_r γ^r_{rx}`, over the common denominator. -/
def rx_t1_n : ZExp 6 := -4 * a ^ 2 * d * r * sx * x
/-- `∂_x γ^x_{rx}`, over the common denominator. -/
def rx_t2_n : ZExp 6 := -4 * a ^ 2 * d * r * sx * x
/-- `∂_x Σ_k γ^k_{rk}`, over the common denominator. -/
def rx_t3_n : ZExp 6 := -8 * a ^ 2 * d * r * sx * x
/-- `γ^r_{rx} Σ_l γ^l_{rl}`, over the common denominator. -/
def rx_t4_n : ZExp 6 := -Sg * a ^ 2 * sx * v * x + 4 * a ^ 2 * d * r * sx * x
/-- `γ^x_{rx} Σ_l γ^l_{xl}`, over the common denominator. -/
def rx_t5_n : ZExp 6 := 2 * Sg * d * r * x + 4 * a ^ 2 * d * r * sx * x
/-- `γ^r_{rr} γ^r_{xr}`, over the common denominator. -/
def rx_t6_n : ZExp 6 := -Sg * a ^ 2 * sx * v * x + 2 * a ^ 2 * d * r * sx * x
/-- `γ^x_{rr} γ^r_{xx}`, over the common denominator. -/
def rx_t7_n : ZExp 6 := 2 * a ^ 2 * d * r * sx * x
/-- `γ^r_{rx} γ^x_{xr}`, over the common denominator. -/
def rx_t8_n : ZExp 6 := 2 * a ^ 2 * d * r * sx * x
/-- `γ^x_{rx} γ^x_{xx}`, over the common denominator. -/
def rx_t9_n : ZExp 6 := 2 * Sg * d * r * x + 2 * a ^ 2 * d * r * sx * x
/-- The common denominator of the terms of `R(h)_{xx}`. -/
def cd_xx : ZExp 6 := 2 * Sg ^ 2 * sx ^ 2
/-- `∂_r γ^r_{xx}`, over the common denominator. -/
def xx_t1_n : ZExp 6 := -2 * Sg * d * sx - 2 * Sg * r * sx * v + 4 * d * r ^ 2 * sx
/-- `∂_x γ^x_{xx}`, over the common denominator. -/
def xx_t2_n : ZExp 6 := 2 * Sg ^ 2 * sx + 4 * Sg ^ 2 * x ^ 2 + 2 * Sg * a ^ 2 * sx ^ 2 -
    4 * a ^ 4 * sx ^ 2 * x ^ 2
/-- `∂_x Σ_k γ^k_{xk}`, over the common denominator. -/
def xx_t3_n : ZExp 6 := 2 * Sg ^ 2 * sx + 4 * Sg ^ 2 * x ^ 2 + 4 * Sg * a ^ 2 * sx ^ 2 -
    8 * a ^ 4 * sx ^ 2 * x ^ 2
/-- `γ^r_{xx} Σ_l γ^l_{rl}`, over the common denominator. -/
def xx_t4_n : ZExp 6 := Sg * r * sx * v - 4 * d * r ^ 2 * sx
/-- `γ^x_{xx} Σ_l γ^l_{xl}`, over the common denominator. -/
def xx_t5_n : ZExp 6 := 2 * Sg ^ 2 * x ^ 2 + 6 * Sg * a ^ 2 * sx * x ^ 2 +
    4 * a ^ 4 * sx ^ 2 * x ^ 2
/-- `γ^r_{xr} γ^r_{xr}`, over the common denominator. -/
def xx_t6_n : ZExp 6 := 2 * a ^ 4 * sx ^ 2 * x ^ 2
/-- `γ^x_{xr} γ^r_{xx}`, over the common denominator. -/
def xx_t7_n : ZExp 6 := -2 * d * r ^ 2 * sx
/-- `γ^r_{xx} γ^x_{xr}`, over the common denominator. -/
def xx_t8_n : ZExp 6 := -2 * d * r ^ 2 * sx
/-- `γ^x_{xx} γ^x_{xx}`, over the common denominator. -/
def xx_t9_n : ZExp 6 := 2 * Sg ^ 2 * x ^ 2 + 4 * Sg * a ^ 2 * sx * x ^ 2 +
    2 * a ^ 4 * sx ^ 2 * x ^ 2

/-- Certificates of this module. -/
macro "kc_poly" : tactic =>
  `(tactic| (frac_poly R ρ h [Grrr, Grrx, Grxx, Gxrr, Gxrx, Gxxx, trR, trX, Wn,
      cd_rr, cd_rx, cd_xx, rr_t1_n, rr_t2_n, rr_t3_n, rr_t4_n, rr_t5_n, rr_t6_n, rr_t7_n,
      rr_t8_n, rr_t9_n, rx_t1_n, rx_t2_n, rx_t3_n, rx_t4_n, rx_t5_n, rx_t6_n, rx_t7_n, rx_t8_n,
      rx_t9_n, xx_t1_n, xx_t2_n, xx_t3_n, xx_t4_n, xx_t5_n, xx_t6_n, xx_t7_n, xx_t8_n, xx_t9_n,
      Sg, sx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]; ring))

/-! ## The entry `R(h)_{rr}` -/


/-- `∂_r γ^r_{rr}` reduced to the common denominator. -/
theorem rr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Grrr) ⟨rr_t1_n, cd_rr⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `∂_x γ^x_{rr}` reduced to the common denominator. -/
theorem rr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gxrr) ⟨rr_t2_n, cd_rr⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `∂_r Σ_k γ^k_{rk}` reduced to the common denominator. -/
theorem rr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr trR) ⟨rr_t3_n, cd_rr⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `γ^r_{rr} Σ_l γ^l_{rl}` reduced to the common denominator. -/
theorem rr_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Grrr * trR) ⟨rr_t4_n, cd_rr⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `γ^x_{rr} Σ_l γ^l_{xl}` reduced to the common denominator. -/
theorem rr_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gxrr * trX) ⟨rr_t5_n, cd_rr⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `γ^r_{rr} γ^r_{rr}` reduced to the common denominator. -/
theorem rr_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Grrr * Grrr) ⟨rr_t6_n, cd_rr⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `γ^x_{rr} γ^r_{rx}` reduced to the common denominator. -/
theorem rr_t7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gxrr * Grrx) ⟨rr_t7_n, cd_rr⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `γ^r_{rx} γ^x_{rr}` reduced to the common denominator. -/
theorem rr_t8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Grrx * Gxrr) ⟨rr_t8_n, cd_rr⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `γ^x_{rx} γ^x_{rx}` reduced to the common denominator. -/
theorem rr_t9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gxrx * Gxrx) ⟨rr_t9_n, cd_rr⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `R(h)_{rr}`: the signed sum of the numerators of its nine terms over `cd_rr` is the
fraction `W / (2 * d * Sg ^ 2)`. -/
theorem ricci_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn ⟨rr_t1_n + rr_t2_n - rr_t3_n + rr_t4_n + rr_t5_n - rr_t6_n - rr_t7_n -
        rr_t8_n - rr_t9_n, cd_rr⟩ ⟨Wn, 2 * d * Sg ^ 2⟩)) :=
  derive_imp _ _ (by kc_poly)

/-! ## The entry `R(h)_{rx}` -/


/-- `∂_r γ^r_{rx}` reduced to the common denominator. -/
theorem rx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Grrx) ⟨rx_t1_n, cd_rx⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `∂_x γ^x_{rx}` reduced to the common denominator. -/
theorem rx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gxrx) ⟨rx_t2_n, cd_rx⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `∂_x Σ_k γ^k_{rk}` reduced to the common denominator. -/
theorem rx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx trR) ⟨rx_t3_n, cd_rx⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `γ^r_{rx} Σ_l γ^l_{rl}` reduced to the common denominator. -/
theorem rx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Grrx * trR) ⟨rx_t4_n, cd_rx⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `γ^x_{rx} Σ_l γ^l_{xl}` reduced to the common denominator. -/
theorem rx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gxrx * trX) ⟨rx_t5_n, cd_rx⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `γ^r_{rr} γ^r_{xr}` reduced to the common denominator. -/
theorem rx_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Grrr * Grrx) ⟨rx_t6_n, cd_rx⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `γ^x_{rr} γ^r_{xx}` reduced to the common denominator. -/
theorem rx_t7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gxrr * Grxx) ⟨rx_t7_n, cd_rx⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `γ^r_{rx} γ^x_{xr}` reduced to the common denominator. -/
theorem rx_t8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Grrx * Gxrx) ⟨rx_t8_n, cd_rx⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `γ^x_{rx} γ^x_{xx}` reduced to the common denominator. -/
theorem rx_t9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gxrx * Gxxx) ⟨rx_t9_n, cd_rx⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `R(h)_{rx}`: the signed sum of the numerators of its nine terms over `cd_rx` is the
fraction `0 / (1)`. -/
theorem ricci_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn ⟨rx_t1_n + rx_t2_n - rx_t3_n + rx_t4_n + rx_t5_n - rx_t6_n - rx_t7_n -
        rx_t8_n - rx_t9_n, cd_rx⟩ ⟨0, 1⟩)) :=
  derive_imp _ _ (by kc_poly)

/-! ## The entry `R(h)_{xx}` -/


/-- `∂_r γ^r_{xx}` reduced to the common denominator. -/
theorem xx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Grxx) ⟨xx_t1_n, cd_xx⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `∂_x γ^x_{xx}` reduced to the common denominator. -/
theorem xx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gxxx) ⟨xx_t2_n, cd_xx⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `∂_x Σ_k γ^k_{xk}` reduced to the common denominator. -/
theorem xx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx trX) ⟨xx_t3_n, cd_xx⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `γ^r_{xx} Σ_l γ^l_{rl}` reduced to the common denominator. -/
theorem xx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Grxx * trR) ⟨xx_t4_n, cd_xx⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `γ^x_{xx} Σ_l γ^l_{xl}` reduced to the common denominator. -/
theorem xx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gxxx * trX) ⟨xx_t5_n, cd_xx⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `γ^r_{xr} γ^r_{xr}` reduced to the common denominator. -/
theorem xx_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Grrx * Grrx) ⟨xx_t6_n, cd_xx⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `γ^x_{xr} γ^r_{xx}` reduced to the common denominator. -/
theorem xx_t7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gxrx * Grxx) ⟨xx_t7_n, cd_xx⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `γ^r_{xx} γ^x_{xr}` reduced to the common denominator. -/
theorem xx_t8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Grxx * Gxrx) ⟨xx_t8_n, cd_xx⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `γ^x_{xx} γ^x_{xx}` reduced to the common denominator. -/
theorem xx_t9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gxxx * Gxxx) ⟨xx_t9_n, cd_xx⟩)) :=
  derive_imp _ _ (by kc_poly)

/-- `R(h)_{xx}`: the signed sum of the numerators of its nine terms over `cd_xx` is the
fraction `W / (2 * sx * Sg ^ 2)`. -/
theorem ricci_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn ⟨xx_t1_n + xx_t2_n - xx_t3_n + xx_t4_n + xx_t5_n - xx_t6_n - xx_t7_n -
        xx_t8_n - xx_t9_n, cd_xx⟩ ⟨Wn, 2 * sx * Sg ^ 2⟩)) :=
  derive_imp _ _ (by kc_poly)


end LeanProofs.IPRA.Geometry.KerrNewmanBaseCurvature
