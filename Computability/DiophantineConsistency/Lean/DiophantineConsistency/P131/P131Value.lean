import DiophantineConsistency.P138.P138Value

/-! # The two-root 810/112 polynomial of package 131, register by register

Package 131 (`con-zfc-diophantine-forms/131-shared-pell-caps-round16/scalar/two_root`), form
`two_root11_degree810.json` (degree 810, 112 operations). Its eleven unrestricted integer
unknowns, in order, are `j C z h r v w T c n s` (`x 0 … x 10`); its six fixed integers are
`beta K0 MC MF cone_A cone_B` (`p 0 … p 5`): the unknowns and the ports of package 138.

**The front is package 138's.** DAG nodes 17–84 and 101–120 compute the registers
`J … Budget, L, Dt, D4, P, K, H2, H3, zc, Ac, S` of `P138Value.regsK` with the short index
`k = 1 + R + h (q² (q² · 4))` (`P138Value.kS`), up to the operand order of two products
(`L` and `P`), which the endpoint module closes by `ring`. The front registers are therefore
*not* restated here: they are read from `P138Value.regsK p x κ`.

**The back end is new.** Package 138 multiplies the guard by the main Pell norm (`BP = P·Dm`),
scales the strong ordinate by `A` (`U = A r c²`) and has one outer square root. This form has
neither factor (`U = r c²`, the strong norm is built on `P` alone), lets the linear slot read
the strong root (`Z = S (n + V) − Ac`), and ends with a two-root norm:

    Inner² − 4 δ · Guard · Aux,   Inner = δ (Z² − Guard) − Aux,
    Guard = S² P Df,   Aux = S² Cy,   δ = Q − 1,   Cy = Q V² − 1.

`backK p x κ` evaluates the back-end registers in an arbitrary commutative ring, row by row in
the order and with the operand order of the JSON DAG (unnamed nodes are inlined), reading the
front from `regsK p x κ`; `valueK p x κ` is the output (node 135), and `value` fills the `k`
slot with the short index.

The register equations `*_def` hold by `rfl`; the closed forms (`*_eq`) and the three shapes
of the output (`value_norm`, `value_norm'`, and the degenerate shapes `value_S_zero`,
`value_Z_zero`) are proved by `ring` with the registers as atoms, never by expanding the
degree-810 output. This module imports neither Foundation nor Mathlib's matrices. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.P131Value
open P138Value

section Generic
variable {𝔸 : Type*} [CommRing 𝔸]

/-- The back-end registers of the two-root circuit (DAG nodes 85–100 and 110, 121–130). -/
structure Back (𝔸 : Type*) where
  U : 𝔸
  UP : 𝔸
  strong : 𝔸
  Df : 𝔸
  Q : 𝔸
  delta : 𝔸
  b : 𝔸
  V : 𝔸
  Cy : 𝔸
  S2 : 𝔸
  Z : 𝔸
  Aux : 𝔸
  Guard : 𝔸
  Inner : 𝔸

/-- The back end, row by row, over the front `P138Value.regsK p x κ`. -/
def backK (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) (κ : 𝔸) : Back 𝔸 :=
  let f := regsK p x κ
  let U := x 4 * f.c2
  let UP := f.P * U
  let strong := UP * (f.Delta * U)
  let Df := 1 + strong
  let Q := f.Delta * strong
  let delta := Q - 1
  let b := x 8 - f.R + x 7 * (4 * UP)
  let V := Df * b - x 8
  let Cy := V * (Q * V) - 1
  let S2 := f.S * f.S
  let Z := f.S * (x 9 + V) - f.Ac
  let Aux := Cy * S2
  let Guard := Df * (f.P * S2)
  let Inner := delta * (Z * Z - Guard) - Aux
  { U := U, UP := UP, strong := strong, Df := Df, Q := Q, delta := delta, b := b, V := V,
    Cy := Cy, S2 := S2, Z := Z, Aux := Aux, Guard := Guard, Inner := Inner }

/-- The output `Inner² − Guard · (Aux · (4 δ))` at the `k` slot `κ` (node 135). -/
def valueK (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) (κ : 𝔸) : 𝔸 :=
  let B := backK p x κ
  B.Inner * B.Inner - B.Guard * (B.Aux * (4 * B.delta))

/-- The value of the 112-operation circuit: the `k` slot holds the short index. -/
abbrev value (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 := valueK p x (kS p x)

/-! ### Register equations (by `rfl`) -/

section Defs
variable (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) (κ : 𝔸)
local notation "𝓡" => regsK p x κ
local notation "𝓑" => backK p x κ

theorem value_def :
    valueK p x κ = (𝓑).Inner * (𝓑).Inner - (𝓑).Guard * ((𝓑).Aux * (4 * (𝓑).delta)) := rfl
theorem U_def : (𝓑).U = x 4 * (𝓡).c2 := rfl
theorem UP_def : (𝓑).UP = (𝓡).P * (𝓑).U := rfl
theorem strong_def : (𝓑).strong = (𝓑).UP * ((𝓡).Delta * (𝓑).U) := rfl
theorem Df_def : (𝓑).Df = 1 + (𝓑).strong := rfl
theorem Q_def : (𝓑).Q = (𝓡).Delta * (𝓑).strong := rfl
theorem delta_def : (𝓑).delta = (𝓑).Q - 1 := rfl
theorem b_def : (𝓑).b = x 8 - (𝓡).R + x 7 * (4 * (𝓑).UP) := rfl
theorem V_def : (𝓑).V = (𝓑).Df * (𝓑).b - x 8 := rfl
theorem Cy_def : (𝓑).Cy = (𝓑).V * ((𝓑).Q * (𝓑).V) - 1 := rfl
theorem S2_def : (𝓑).S2 = (𝓡).S * (𝓡).S := rfl
theorem Z_def : (𝓑).Z = (𝓡).S * (x 9 + (𝓑).V) - (𝓡).Ac := rfl
theorem Aux_def : (𝓑).Aux = (𝓑).Cy * (𝓑).S2 := rfl
theorem Guard_def : (𝓑).Guard = (𝓑).Df * ((𝓡).P * (𝓑).S2) := rfl
theorem Inner_def : (𝓑).Inner = (𝓑).delta * ((𝓑).Z * (𝓑).Z - (𝓑).Guard) - (𝓑).Aux := rfl

/-! ### Closed forms in the notation of `TWO_ROOT_PROOF.md` -/

theorem U_eq : (𝓑).U = x 4 * x 8 ^ 2 := by rw [U_def, c2_def]; ring

theorem strong_eq : (𝓑).strong = (𝓡).Delta * (𝓑).U ^ 2 * (𝓡).P := by
  rw [strong_def, UP_def]; ring

theorem Df_eq : (𝓑).Df = 1 + (𝓡).Delta * (𝓑).U ^ 2 * (𝓡).P := by rw [Df_def, strong_eq]

theorem Q_eq : (𝓑).Q = (𝓡).Delta ^ 2 * (𝓑).U ^ 2 * (𝓡).P := by rw [Q_def, strong_eq]; ring

theorem Q_Df : (𝓑).Q = (𝓡).Delta * ((𝓑).Df - 1) := by rw [Q_eq, Df_eq]; ring

theorem b_eq : (𝓑).b = x 8 - (𝓡).R + 4 * (𝓑).U * (𝓡).P * x 7 := by rw [b_def, UP_def]; ring

theorem V_eq : (𝓑).V = (𝓑).Df * (x 8 - (𝓡).R + 4 * (𝓑).U * (𝓡).P * x 7) - x 8 := by
  rw [V_def, b_eq]

theorem Cy_eq : (𝓑).Cy = (𝓑).Q * (𝓑).V ^ 2 - 1 := by rw [Cy_def]; ring

theorem Guard_eq : (𝓑).Guard = (𝓡).S ^ 2 * ((𝓡).P * (𝓑).Df) := by rw [Guard_def, S2_def]; ring

theorem Aux_eq : (𝓑).Aux = (𝓡).S ^ 2 * (𝓑).Cy := by rw [Aux_def, S2_def]; ring

/-- **The first norm form.** With `𝓘 = δ Z² + δ S² P Df − S² Cy` and `𝓣 = 2 δ Z S`, the output
is `𝓘² − 𝓣² · (P Df)`: at a zero with `𝓣 ≠ 0`, `P · Df` is a square. -/
theorem value_norm : valueK p x κ =
    ((𝓑).delta * (𝓑).Z ^ 2 + (𝓑).delta * (𝓡).S ^ 2 * ((𝓡).P * (𝓑).Df) - (𝓡).S ^ 2 * (𝓑).Cy) ^ 2 -
      (2 * (𝓑).delta * (𝓑).Z * (𝓡).S) ^ 2 * ((𝓡).P * (𝓑).Df) := by
  rw [value_def, Inner_def, Guard_eq, Aux_eq]; ring

/-- **The second norm form.** With `𝓘' = δ Z² − δ S² P Df + S² Cy` and `𝓣' = 2 Z S`, the
output is `𝓘'² − 𝓣'² · (δ Cy)`: at a zero with `𝓣' ≠ 0`, `δ · Cy` is a square. -/
theorem value_norm' : valueK p x κ =
    ((𝓑).delta * (𝓑).Z ^ 2 - (𝓑).delta * (𝓡).S ^ 2 * ((𝓡).P * (𝓑).Df) + (𝓡).S ^ 2 * (𝓑).Cy) ^ 2 -
      (2 * (𝓑).Z * (𝓡).S) ^ 2 * ((𝓑).delta * (𝓑).Cy) := by
  rw [value_def, Inner_def, Guard_eq, Aux_eq]; ring

/-- The output where `S = 0`: `δ² Ac⁴`. -/
theorem value_S_zero (hS : (𝓡).S = 0) : valueK p x κ = ((𝓑).delta * (𝓡).Ac ^ 2) ^ 2 := by
  rw [value_def, Inner_def, Guard_eq, Aux_eq, Z_def, hS]; ring

/-- The output where `Z = 0`: `S⁴ (δ P Df − Cy)²`. -/
theorem value_Z_zero (hZ : (𝓑).Z = 0) :
    valueK p x κ = ((𝓡).S ^ 2 * ((𝓑).delta * ((𝓡).P * (𝓑).Df) - (𝓑).Cy)) ^ 2 := by
  rw [value_norm, hZ]; ring

end Defs

/-! ### The back end does not read `x 3` -/

section Forms
variable (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸)

/-- The back end does not read `x 3` except through the `k` slot. -/
theorem backK_update (κ t : 𝔸) : backK p (Function.update x 3 t) κ = backK p x κ := rfl

theorem valueK_update (κ t : 𝔸) : valueK p (Function.update x 3 t) κ = valueK p x κ := rfl

end Forms
end Generic

#print axioms DiophantineConsistency.P131Value.value_norm
#print axioms DiophantineConsistency.P131Value.value_norm'
#print axioms DiophantineConsistency.P131Value.value_S_zero
#print axioms DiophantineConsistency.P131Value.value_Z_zero
#print axioms DiophantineConsistency.P131Value.V_eq
#print axioms DiophantineConsistency.P131Value.Q_eq
#print axioms DiophantineConsistency.P131Value.backK_update

end DiophantineConsistency.P131Value
