import DiophantineConsistency.P137.P137Front

/-! # The 648/115 polynomial of package 137, register by register

Package 137 (`con-zfc-diophantine-forms/137-odd-helpers-saturated-carriers/integer`), form
`weak_product11_none.json` (degree 648, 115 operations: 73 multiplications, 23 additions,
19 subtractions). Its eleven unrestricted integer unknowns, in order, are
`j C z h r v w T c n s` (`x 0 … x 10`); its six fixed integers are
`beta K0 MC MF cone_A cone_B` (`p 0 … p 5`): the unknowns and the ports of package 138.

**The front and the carrier** (DAG nodes 18–75, 83–84 and 103–133) are the registers of
`P137Front.front p x`: the weak ordinate `Y = v q` and the saturated carrier
`S = M⁴ (H M (r s))`, `Z = n S − Ac`.

**The back end** (nodes 76–102 and 134–139) is package 138's product back end with the guard
discriminant `D4 = 12 Budget − 16`:

    P = Dt + Pg (D4 Pg),  Pg = s Dt;      BP = P Dm;        U = A (r c²);
    strong = (BP U)(Delta U);             Df = 1 + strong;  Q = Delta strong;
    b = (c − R) + T (4 BP U);             V = Df b − c;     Cy = V (Q V) − 1;
    output = Z (δ Z) − Cy (Df (BP S²)),   δ = Q − 1.

`back p x` evaluates the back-end registers in an arbitrary commutative ring, row by row in
the order and with the operand order of the JSON DAG (unnamed nodes are inlined); `value p x`
is the output (node 139).

The register equations `*_def` hold by `rfl`; the closed forms (`*_eq`) and the product form
of the output (`value_eq_product`: `δ Z² − S² (BP Df Cy)`) are proved by `ring` with the
registers as atoms, never by expanding the degree-648 output. This module imports neither
Foundation nor Mathlib's matrices. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.P137Value
open P137Front

section Generic
variable {𝔸 : Type*} [CommRing 𝔸]

/-- The back-end registers of the 648/115 circuit (DAG nodes 76–102). -/
structure Back (𝔸 : Type*) where
  D4 : 𝔸
  Pg : 𝔸
  P : 𝔸
  BP : 𝔸
  Ub : 𝔸
  U : 𝔸
  UBP : 𝔸
  strong : 𝔸
  Df : 𝔸
  Q : 𝔸
  delta : 𝔸
  b : 𝔸
  V : 𝔸
  Cy : 𝔸

/-- The back end, row by row, over the weak front `P137Front.front p x`. -/
def back (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : Back 𝔸 :=
  let f := front p x
  let D4 := 12 * f.Budget - 16
  let Pg := x 10 * f.Dt
  let P := f.Dt + Pg * (D4 * Pg)
  let BP := P * f.Dm
  let Ub := x 4 * f.c2
  let U := f.A * Ub
  let UBP := BP * U
  let strong := UBP * (f.Delta * U)
  let Df := 1 + strong
  let Q := f.Delta * strong
  let delta := Q - 1
  let b := x 8 - f.R + x 7 * (4 * UBP)
  let V := Df * b - x 8
  let Cy := V * (Q * V) - 1
  { D4, Pg, P, BP, Ub, U, UBP, strong, Df, Q, delta, b, V, Cy }

/-- The value of the 115-operation circuit (node 139). -/
def value (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 :=
  let f := front p x
  let B := back p x
  f.Z * (B.delta * f.Z) - B.Cy * (B.Df * (B.BP * f.S2))

/-! ### Register equations (by `rfl`) -/

section Defs
variable (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸)
local notation "𝓕" => front p x
local notation "𝓑" => back p x

theorem value_def : value p x =
    (𝓕).Z * ((𝓑).delta * (𝓕).Z) - (𝓑).Cy * ((𝓑).Df * ((𝓑).BP * (𝓕).S2)) := rfl
theorem D4_def : (𝓑).D4 = 12 * (𝓕).Budget - 16 := rfl
theorem Pg_def : (𝓑).Pg = x 10 * (𝓕).Dt := rfl
theorem P_def : (𝓑).P = (𝓕).Dt + (𝓑).Pg * ((𝓑).D4 * (𝓑).Pg) := rfl
theorem BP_def : (𝓑).BP = (𝓑).P * (𝓕).Dm := rfl
theorem Ub_def : (𝓑).Ub = x 4 * (𝓕).c2 := rfl
theorem U_def : (𝓑).U = (𝓕).A * (𝓑).Ub := rfl
theorem UBP_def : (𝓑).UBP = (𝓑).BP * (𝓑).U := rfl
theorem strong_def : (𝓑).strong = (𝓑).UBP * ((𝓕).Delta * (𝓑).U) := rfl
theorem Df_def : (𝓑).Df = 1 + (𝓑).strong := rfl
theorem Q_def : (𝓑).Q = (𝓕).Delta * (𝓑).strong := rfl
theorem delta_def : (𝓑).delta = (𝓑).Q - 1 := rfl
theorem b_def : (𝓑).b = x 8 - (𝓕).R + x 7 * (4 * (𝓑).UBP) := rfl
theorem V_def : (𝓑).V = (𝓑).Df * (𝓑).b - x 8 := rfl
theorem Cy_def : (𝓑).Cy = (𝓑).V * ((𝓑).Q * (𝓑).V) - 1 := rfl

/-! ### Closed forms in the notation of `PROOF.md` -/

/-- `D4 = 4 (3 Budget − 4)`. -/
theorem D4_eq : (𝓑).D4 = 4 * (3 * (𝓕).Budget - 4) := by rw [D4_def]; ring

/-- `P = Dt · (1 + D4 Dt s²)`. -/
theorem P_eq : (𝓑).P = (𝓕).Dt * (1 + (𝓑).D4 * (𝓕).Dt * x 10 ^ 2) := by
  rw [P_def, Pg_def]; ring

theorem U_eq : (𝓑).U = (𝓕).A * (x 4 * x 8 ^ 2) := by rw [U_def, Ub_def, c2_def]; ring

theorem strong_eq : (𝓑).strong = (𝓕).Delta * (𝓑).U ^ 2 * (𝓑).BP := by
  rw [strong_def, UBP_def]; ring

theorem Df_eq : (𝓑).Df = 1 + (𝓕).Delta * (𝓑).U ^ 2 * (𝓑).BP := by rw [Df_def, strong_eq]

theorem Q_eq : (𝓑).Q = (𝓕).Delta ^ 2 * (𝓑).U ^ 2 * (𝓑).BP := by rw [Q_def, strong_eq]; ring

theorem Q_Df : (𝓑).Q = (𝓕).Delta * ((𝓑).Df - 1) := by rw [Q_eq, Df_eq]; ring

theorem b_eq : (𝓑).b = x 8 - (𝓕).R + 4 * (𝓑).U * (𝓑).BP * x 7 := by rw [b_def, UBP_def]; ring

theorem V_eq : (𝓑).V = (𝓑).Df * (x 8 - (𝓕).R + 4 * (𝓑).U * (𝓑).BP * x 7) - x 8 := by
  rw [V_def, b_eq]

theorem Cy_eq : (𝓑).Cy = (𝓑).Q * (𝓑).V ^ 2 - 1 := by rw [Cy_def]; ring

/-- **The product form of the output**: `δ Z² − S² (BP · Df · Cy)`. -/
theorem value_eq_product : value p x =
    ((𝓑).Q - 1) * (𝓕).Z ^ 2 - (𝓕).S ^ 2 * ((𝓑).BP * (𝓑).Df * ((𝓑).Q * (𝓑).V ^ 2 - 1)) := by
  rw [value_def, delta_def, Cy_eq, S2_def]; ring

/-- The output where `S = 0`: `δ Ac²`. -/
theorem value_S_zero (hS : (𝓕).S = 0) : value p x = ((𝓑).Q - 1) * (𝓕).Ac ^ 2 := by
  rw [value_eq_product, Z_eq, hS]; ring

end Defs
end Generic

#print axioms DiophantineConsistency.P137Value.value_eq_product
#print axioms DiophantineConsistency.P137Value.value_S_zero
#print axioms DiophantineConsistency.P137Value.V_eq
#print axioms DiophantineConsistency.P137Value.Q_eq
#print axioms DiophantineConsistency.P137Value.P_eq

end DiophantineConsistency.P137Value
