import DiophantineConsistency.P137.P137Front

/-! # The 398/121 polynomial of package 135, register by register

Package 135 (`con-zfc-diophantine-forms/135-cofinal-anchors-round17/scalar`), form
`weak_cofactor11_none.json` (degree 398, 121 operations: 77 multiplications, 24 additions,
20 subtractions). Its eleven unrestricted integer unknowns, in order, are
`j C z h r v w T c n s` (`x 0 … x 10`); its six fixed integers are
`beta K0 MC MF cone_A cone_B` (`p 0 … p 5`): the unknowns and the ports of package 138.

**The front and the carrier** (DAG nodes 18–75, 81–82 and 100–130) are, node for node, the
registers of `P137Front.front p x`: the weak ordinate `Y = v q` and the saturated carrier
`S = M⁴ (H M (r s))`, `Z = n S − Ac`.

**The back end** (nodes 76–80, 83–99 and 131–144) is the linear-cofactor back end with
radical weight 4 and the guard discriminant `Dguard = Budget − 4`:

    P = Dt + Pg (Dguard Pg),  Pg = s Dt;   B = A (r Dm);      U = c² (r Dm);
    strong = (Delta c²)(A U);              Df = 1 + strong;   Q = Delta strong;
    b = (c − R) + T (4 (A U));             V = Df b − c;      Cy = V (Q V) − 1;
    pa = δ Z²;   pb = P (δ S²);   pc = Cy (Df (B (4 S²)));    δ = Q − 1;
    output = (pa + pb − pc)² − pb (4 pa).

`back p x` evaluates the back-end registers in an arbitrary commutative ring, row by row in
the order and with the operand order of the JSON DAG (unnamed nodes are inlined); `value p x`
is the output (node 144).

The register equations `*_def` hold by `rfl`; the closed forms (`*_eq`) and the norm form of
the output (`value_eq_product`: `𝓘² − 𝓣² P` with `𝓘 = δ Z² + δ S² P − 4 S² B Df Cy` and
`𝓣 = 2 δ Z S`) are proved by `ring` with the registers as atoms, never by expanding the
degree-398 output. This module imports neither Foundation nor Mathlib's matrices. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.P135WValue
open P137Front

section Generic
variable {𝔸 : Type*} [CommRing 𝔸]

/-- The back-end registers of the 398/121 circuit (DAG nodes 76–99 and 131–140). -/
structure Back (𝔸 : Type*) where
  Dguard : 𝔸
  Pg : 𝔸
  P : 𝔸
  rDm : 𝔸
  B : 𝔸
  U : 𝔸
  AU : 𝔸
  strong : 𝔸
  Df : 𝔸
  Q : 𝔸
  delta : 𝔸
  b : 𝔸
  V : 𝔸
  Cy : 𝔸
  Z2 : 𝔸
  pa : 𝔸
  pb : 𝔸
  pc : 𝔸
  inner : 𝔸

/-- The back end, row by row, over the weak front `P137Front.front p x`. -/
def back (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : Back 𝔸 :=
  let f := front p x
  let Dguard := f.Budget - 4
  let Pg := x 10 * f.Dt
  let P := f.Dt + Pg * (Dguard * Pg)
  let rDm := x 4 * f.Dm
  let B := f.A * rDm
  let U := f.c2 * rDm
  let AU := f.A * U
  let strong := f.Delta * f.c2 * AU
  let Df := 1 + strong
  let Q := f.Delta * strong
  let delta := Q - 1
  let b := x 8 - f.R + x 7 * (4 * AU)
  let V := Df * b - x 8
  let Cy := V * (Q * V) - 1
  let Z2 := f.Z * f.Z
  let pa := delta * Z2
  let pb := P * (delta * f.S2)
  let pc := Cy * (Df * (B * (4 * f.S2)))
  let inner := pa + pb - pc
  { Dguard, Pg, P, rDm, B, U, AU, strong, Df, Q, delta, b, V, Cy, Z2, pa, pb, pc, inner }

/-- The value of the 121-operation circuit (node 144). -/
def value (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 :=
  let B := back p x
  B.inner * B.inner - B.pb * (4 * B.pa)

/-! ### Register equations (by `rfl`) -/

section Defs
variable (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸)
local notation "𝓕" => front p x
local notation "𝓑" => back p x

theorem value_def : value p x = (𝓑).inner * (𝓑).inner - (𝓑).pb * (4 * (𝓑).pa) := rfl
theorem Dguard_def : (𝓑).Dguard = (𝓕).Budget - 4 := rfl
theorem Pg_def : (𝓑).Pg = x 10 * (𝓕).Dt := rfl
theorem P_def : (𝓑).P = (𝓕).Dt + (𝓑).Pg * ((𝓑).Dguard * (𝓑).Pg) := rfl
theorem rDm_def : (𝓑).rDm = x 4 * (𝓕).Dm := rfl
theorem B_def : (𝓑).B = (𝓕).A * (𝓑).rDm := rfl
theorem U_def : (𝓑).U = (𝓕).c2 * (𝓑).rDm := rfl
theorem AU_def : (𝓑).AU = (𝓕).A * (𝓑).U := rfl
theorem strong_def : (𝓑).strong = (𝓕).Delta * (𝓕).c2 * (𝓑).AU := rfl
theorem Df_def : (𝓑).Df = 1 + (𝓑).strong := rfl
theorem Q_def : (𝓑).Q = (𝓕).Delta * (𝓑).strong := rfl
theorem delta_def : (𝓑).delta = (𝓑).Q - 1 := rfl
theorem b_def : (𝓑).b = x 8 - (𝓕).R + x 7 * (4 * (𝓑).AU) := rfl
theorem V_def : (𝓑).V = (𝓑).Df * (𝓑).b - x 8 := rfl
theorem Cy_def : (𝓑).Cy = (𝓑).V * ((𝓑).Q * (𝓑).V) - 1 := rfl
theorem Z2_def : (𝓑).Z2 = (𝓕).Z * (𝓕).Z := rfl
theorem pa_def : (𝓑).pa = (𝓑).delta * (𝓑).Z2 := rfl
theorem pb_def : (𝓑).pb = (𝓑).P * ((𝓑).delta * (𝓕).S2) := rfl
theorem pc_def : (𝓑).pc = (𝓑).Cy * ((𝓑).Df * ((𝓑).B * (4 * (𝓕).S2))) := rfl
theorem inner_def : (𝓑).inner = (𝓑).pa + (𝓑).pb - (𝓑).pc := rfl

/-! ### Closed forms -/

/-- `P = Dt · (1 + Dguard Dt s²)`. -/
theorem P_eq : (𝓑).P = (𝓕).Dt * (1 + (𝓑).Dguard * (𝓕).Dt * x 10 ^ 2) := by
  rw [P_def, Pg_def]; ring

/-- `B = A r Dm`. -/
theorem B_eq : (𝓑).B = (𝓕).A * x 4 * (𝓕).Dm := by rw [B_def, rDm_def]; ring

/-- `strong = Δ c⁴ B`. -/
theorem strong_eq : (𝓑).strong = (𝓕).Delta * x 8 ^ 4 * (𝓑).B := by
  rw [strong_def, AU_def, U_def, B_def, c2_def]; ring

theorem Df_eq : (𝓑).Df = 1 + (𝓕).Delta * x 8 ^ 4 * (𝓑).B := by rw [Df_def, strong_eq]

theorem Q_eq : (𝓑).Q = (𝓕).Delta ^ 2 * x 8 ^ 4 * (𝓑).B := by rw [Q_def, strong_eq]; ring

theorem Q_Df : (𝓑).Q = (𝓕).Delta * ((𝓑).Df - 1) := by rw [Q_def, Df_def]; ring

/-- `A U = c² B`. -/
theorem AU_eq : (𝓑).AU = x 8 ^ 2 * (𝓑).B := by rw [AU_def, U_def, B_def, c2_def]; ring

theorem b_eq : (𝓑).b = x 8 - (𝓕).R + 4 * x 8 ^ 2 * (𝓑).B * x 7 := by rw [b_def, AU_eq]; ring

theorem V_eq : (𝓑).V = (𝓑).Df * (x 8 - (𝓕).R + 4 * x 8 ^ 2 * (𝓑).B * x 7) - x 8 := by
  rw [V_def, b_eq]

theorem Cy_eq : (𝓑).Cy = (𝓑).Q * (𝓑).V ^ 2 - 1 := by rw [Cy_def]; ring

/-- **The norm form of the output**: `𝓘² − 𝓣² P` with
`𝓘 = δ Z² + δ S² P − 4 S² B Df Cy` and `𝓣 = 2 δ Z S`. -/
theorem value_eq_product : value p x =
    ((𝓑).delta * (𝓕).Z ^ 2 + (𝓑).delta * (𝓕).S ^ 2 * (𝓑).P -
        4 * (𝓕).S ^ 2 * (𝓑).B * (𝓑).Df * (𝓑).Cy) ^ 2 -
      (2 * (𝓑).delta * (𝓕).Z * (𝓕).S) ^ 2 * (𝓑).P := by
  rw [value_def, inner_def, pa_def, pb_def, pc_def, Z2_def, S2_def]; ring

/-- The output where `S = 0`: `(δ Ac²)²`. -/
theorem value_S_zero (hS : (𝓕).S = 0) : value p x = ((𝓑).delta * (𝓕).Ac ^ 2) ^ 2 := by
  rw [value_eq_product, Z_eq, hS]; ring

/-- The zero criterion used by completeness: `Z = S (α + β)`, `P = β²` and
`4 B Df Cy = δ α²`. -/
theorem value_eq_zero_of (α β : 𝔸) (hZ : (𝓕).Z = (𝓕).S * (α + β)) (hP : (𝓑).P = β ^ 2)
    (hC : 4 * (𝓑).B * (𝓑).Df * (𝓑).Cy = (𝓑).delta * α ^ 2) : value p x = 0 := by
  rw [value_eq_product, hZ, hP]
  have h : 4 * (𝓕).S ^ 2 * (𝓑).B * (𝓑).Df * (𝓑).Cy = (𝓕).S ^ 2 * ((𝓑).delta * α ^ 2) := by
    rw [← hC]; ring
  rw [h]; ring

end Defs
end Generic

#print axioms DiophantineConsistency.P135WValue.value_eq_product
#print axioms DiophantineConsistency.P135WValue.value_S_zero
#print axioms DiophantineConsistency.P135WValue.value_eq_zero_of
#print axioms DiophantineConsistency.P135WValue.V_eq
#print axioms DiophantineConsistency.P135WValue.Q_eq
#print axioms DiophantineConsistency.P135WValue.P_eq

end DiophantineConsistency.P135WValue
