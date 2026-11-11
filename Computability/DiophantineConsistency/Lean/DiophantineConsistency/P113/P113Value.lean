import DiophantineConsistency.ZRows.ThreeRoot

/-! # The twelve-integer 1084/123 polynomial of package 113, register by register

Package 113 (`con-zfc-diophantine-forms/113-saturated-pell/integer12_saturated/rational.json`,
`PROOF.md`): twelve unrestricted integer unknowns `j C z h r v w T c n t s` (`x 0 … x 11`), 123
operations, exact degree 1084, at the six fixed integers `beta K0 MC MF cone_A cone_B`
(`p 0 … p 5`) of the source34 tuple.

**The front** (`J … eta`) is package 138's front with the native index `k = R + 1 + h X Y`.
**The guard** is the pair `Pair = G·η·ζ − (t² − G − η·ζ + 1)²` of the determinant
`G = (cone_A F)(cone_B C) − (q − cone_A F − cone_B C)²` and the window product `η·ζ`
(`ζ = k − η`), with its weighted Pell cofactor `Dg81 = (243 Pair − 324) s² + 81 = 81 Dg`.
**The saturation** is the product `E · Df` of the first norm `E = 1 + ℓ(ℓ + 1) k²`
(`ℓ = X Y²`) and the strong norm `Df = 1 + Δ U² E`, `U = s r c²`.
**The output** is the norm of three square roots over the four radicands
`fs = δ Z²`, `fa = 9 δ S² E Df`, `fb = δ S² Dg81`, `fc = S² Cy`,

    value = Pe² − 64 fs fc fa fb,   Pe = (fs + fc − fa − fb)² − 4 (fs fc + fa fb).

It is homogeneous of degree four in the radicands, so scaling all four by `δ` gives the
three-root norm `ZRowsThreeRoot.norm3` at `δ Z` (`value_scale`).

The register equations `*_def` hold by `rfl`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.P113Value
open ZRowsThreeRoot

section Generic
variable {𝔸 : Type*} [CommRing 𝔸]

/-- The registers of package 113's polynomial. -/
structure Regs (𝔸 : Type*) where
  J : 𝔸
  q : 𝔸
  W0 : 𝔸
  X : 𝔸
  Y : 𝔸
  a : 𝔸
  H : 𝔸
  Delta : 𝔸
  F : 𝔸
  R : 𝔸
  k : 𝔸
  eta : 𝔸
  zeta : 𝔸
  G : 𝔸
  Pair : 𝔸
  Dg81 : 𝔸
  ell : 𝔸
  E : 𝔸
  U : 𝔸
  Df : 𝔸
  Q : 𝔸
  delta : 𝔸
  b : 𝔸
  V : 𝔸
  Cy : 𝔸
  K : 𝔸
  S : 𝔸
  zc : 𝔸
  Ac : 𝔸
  Z : 𝔸
  fs : 𝔸
  fa : 𝔸
  fb : 𝔸
  fc : 𝔸
  Pe : 𝔸

/-- The registers at the ports `p` and the twelve unknowns `x`. -/
def regs (p : Fin 6 → 𝔸) (x : Fin 12 → 𝔸) : Regs 𝔸 :=
  let J := 6 * x 0 + 1
  let q := p 0 * J + 1
  let W0 := 12 * x 6 + 4
  let X := q * W0
  let Y := (2 * x 5 + 1) * q ^ 3
  let a := (X + 1) * Y
  let H := 4 * a + 3
  let Delta := a * a + H
  let F := (p 1 + W0) * x 1 - x 2 * (q - 1)
  let R := (q * (q - F) - x 1) * (q * q - 1) + (p 2 + q * p 3) * J
  let k := R + 1 + x 3 * X * Y
  let eta := x 8 - Y * k
  let zeta := k - eta
  let G := (p 4 * F) * (p 5 * x 1) - (q - p 4 * F - p 5 * x 1) ^ 2
  let Pair := G * eta * zeta - (x 10 * x 10 - G - eta * zeta + 1) ^ 2
  let Dg81 := (243 * Pair - 324) * (x 11 * x 11) + 81
  let ell := X * Y * Y
  let E := 1 + ell * (ell + 1) * (k * k)
  let U := x 11 * x 4 * (x 8 * x 8)
  let Df := 1 + Delta * (U * U) * E
  let Q := Delta * Delta * (U * U) * E
  let delta := Q - 1
  let b := x 8 - R + 4 * U * E * x 7
  let V := Df * b - x 8
  let Cy := Q * (V * V) - 1
  let K := X * (X + 2 * a * x 8) - 1
  let S := U * H ^ 5
  let zc := H * x 7 + K
  let Ac := (zc * zc + 3 * (H * H)) * (zc ^ 3 - 19 * H ^ 3)
  let Z := S * (x 9 + V) - Ac
  let fs := delta * (Z * Z)
  let fa := 9 * delta * (S * S) * E * Df
  let fb := delta * (S * S) * Dg81
  let fc := S * S * Cy
  let Pe := (fs + fc - fa - fb) ^ 2 - 4 * (fs * fc + fa * fb)
  { J, q, W0, X, Y, a, H, Delta, F, R, k, eta, zeta, G, Pair, Dg81, ell, E, U, Df, Q, delta,
    b, V, Cy, K, S, zc, Ac, Z, fs, fa, fb, fc, Pe }

/-- The value of the 123-operation polynomial. -/
def value (p : Fin 6 → 𝔸) (x : Fin 12 → 𝔸) : 𝔸 :=
  (regs p x).Pe * (regs p x).Pe -
    64 * ((regs p x).fs * (regs p x).fc * (regs p x).fa * (regs p x).fb)

/-! ## Register equations (by `rfl`) -/

section Defs
variable (p : Fin 6 → 𝔸) (x : Fin 12 → 𝔸)
local notation "𝓡" => regs p x

theorem J_def : (𝓡).J = 6 * x 0 + 1 := rfl
theorem q_def : (𝓡).q = p 0 * (𝓡).J + 1 := rfl
theorem W0_def : (𝓡).W0 = 12 * x 6 + 4 := rfl
theorem X_def : (𝓡).X = (𝓡).q * (𝓡).W0 := rfl
theorem Y_def : (𝓡).Y = (2 * x 5 + 1) * (𝓡).q ^ 3 := rfl
theorem a_def : (𝓡).a = ((𝓡).X + 1) * (𝓡).Y := rfl
theorem H_def : (𝓡).H = 4 * (𝓡).a + 3 := rfl
theorem Delta_def : (𝓡).Delta = (𝓡).a * (𝓡).a + (𝓡).H := rfl
theorem F_def : (𝓡).F = (p 1 + (𝓡).W0) * x 1 - x 2 * ((𝓡).q - 1) := rfl
theorem R_def : (𝓡).R =
    ((𝓡).q * ((𝓡).q - (𝓡).F) - x 1) * ((𝓡).q * (𝓡).q - 1) + (p 2 + (𝓡).q * p 3) * (𝓡).J := rfl
theorem k_def : (𝓡).k = (𝓡).R + 1 + x 3 * (𝓡).X * (𝓡).Y := rfl
theorem eta_def : (𝓡).eta = x 8 - (𝓡).Y * (𝓡).k := rfl
theorem zeta_def : (𝓡).zeta = (𝓡).k - (𝓡).eta := rfl
theorem G_def : (𝓡).G =
    (p 4 * (𝓡).F) * (p 5 * x 1) - ((𝓡).q - p 4 * (𝓡).F - p 5 * x 1) ^ 2 := rfl
theorem Pair_def : (𝓡).Pair =
    (𝓡).G * (𝓡).eta * (𝓡).zeta - (x 10 * x 10 - (𝓡).G - (𝓡).eta * (𝓡).zeta + 1) ^ 2 := rfl
theorem Dg81_def : (𝓡).Dg81 = (243 * (𝓡).Pair - 324) * (x 11 * x 11) + 81 := rfl
theorem ell_def : (𝓡).ell = (𝓡).X * (𝓡).Y * (𝓡).Y := rfl
theorem E_def : (𝓡).E = 1 + (𝓡).ell * ((𝓡).ell + 1) * ((𝓡).k * (𝓡).k) := rfl
theorem U_def : (𝓡).U = x 11 * x 4 * (x 8 * x 8) := rfl
theorem Df_def : (𝓡).Df = 1 + (𝓡).Delta * ((𝓡).U * (𝓡).U) * (𝓡).E := rfl
theorem Q_def : (𝓡).Q = (𝓡).Delta * (𝓡).Delta * ((𝓡).U * (𝓡).U) * (𝓡).E := rfl
theorem delta_def : (𝓡).delta = (𝓡).Q - 1 := rfl
theorem b_def : (𝓡).b = x 8 - (𝓡).R + 4 * (𝓡).U * (𝓡).E * x 7 := rfl
theorem V_def : (𝓡).V = (𝓡).Df * (𝓡).b - x 8 := rfl
theorem Cy_def : (𝓡).Cy = (𝓡).Q * ((𝓡).V * (𝓡).V) - 1 := rfl
theorem K_def : (𝓡).K = (𝓡).X * ((𝓡).X + 2 * (𝓡).a * x 8) - 1 := rfl
theorem S_def : (𝓡).S = (𝓡).U * (𝓡).H ^ 5 := rfl
theorem zc_def : (𝓡).zc = (𝓡).H * x 7 + (𝓡).K := rfl
theorem Ac_def : (𝓡).Ac =
    ((𝓡).zc * (𝓡).zc + 3 * ((𝓡).H * (𝓡).H)) * ((𝓡).zc ^ 3 - 19 * (𝓡).H ^ 3) := rfl
theorem Z_def : (𝓡).Z = (𝓡).S * (x 9 + (𝓡).V) - (𝓡).Ac := rfl
theorem fs_def : (𝓡).fs = (𝓡).delta * ((𝓡).Z * (𝓡).Z) := rfl
theorem fa_def : (𝓡).fa = 9 * (𝓡).delta * ((𝓡).S * (𝓡).S) * (𝓡).E * (𝓡).Df := rfl
theorem fb_def : (𝓡).fb = (𝓡).delta * ((𝓡).S * (𝓡).S) * (𝓡).Dg81 := rfl
theorem fc_def : (𝓡).fc = (𝓡).S * (𝓡).S * (𝓡).Cy := rfl
theorem Pe_def : (𝓡).Pe =
    ((𝓡).fs + (𝓡).fc - (𝓡).fa - (𝓡).fb) ^ 2 - 4 * ((𝓡).fs * (𝓡).fc + (𝓡).fa * (𝓡).fb) := rfl
theorem value_def : value p x = (𝓡).Pe * (𝓡).Pe - 64 * ((𝓡).fs * (𝓡).fc * (𝓡).fa * (𝓡).fb) :=
  rfl

/-- **The output is a scaled three-root norm**: `δ⁴ · value = N(δZ; δ fc, δ fa, δ fb)`. -/
theorem value_scale :
    (𝓡).delta ^ 4 * value p x =
      norm3 ((𝓡).delta * (𝓡).Z) ((𝓡).delta * (𝓡).fc) ((𝓡).delta * (𝓡).fa)
        ((𝓡).delta * (𝓡).fb) := by
  rw [value_def, Pe_def, fs_def]
  unfold norm3
  ring

end Defs

end Generic

end DiophantineConsistency.P113Value
