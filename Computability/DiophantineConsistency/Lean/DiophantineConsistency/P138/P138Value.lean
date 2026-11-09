import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! # The 924/107 polynomial of package 138, register by register

Package 138 (`con-zfc-diophantine-forms/138-semantic-signs/integer11`), native
form `parity_saturated11_native.json`. Its eleven unrestricted integer unknowns,
in order, are `j C z h r v w T c n s` (`x 0 … x 10`); its six fixed integers are
`beta K0 MC MF cone_A cone_B` (`p 0 … p 5`).

`regs p x` evaluates every named register of the circuit in an arbitrary
commutative ring, row by row in the order and with the operand order of the
JSON DAG (unnamed DAG nodes are inlined). `value p x` is the output node 130,

    Q (Z² − RG V²) + (RG − Z²).

The register equations `*_def` hold by `rfl`; the closed forms below (`*_eq`)
and the identity (4) of `PROOF.md` (`value_eq`) are proved by `ring` with the
registers as atoms, never by expanding the degree-924 output.
This module imports neither Foundation nor Mathlib's matrices. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.P138Value

section Generic
variable {𝔸 : Type*} [CommRing 𝔸]

/-- The named registers of the circuit (`named_registers` of the JSON). -/
structure Regs (𝔸 : Type*) where
  J : 𝔸
  qm : 𝔸
  q : 𝔸
  q2 : 𝔸
  q3 : 𝔸
  W : 𝔸
  X : 𝔸
  Y : 𝔸
  E : 𝔸
  a : 𝔸
  H : 𝔸
  Delta : 𝔸
  A : 𝔸
  F : 𝔸
  R : 𝔸
  q24 : 𝔸
  k : 𝔸
  Yk : 𝔸
  eta : 𝔸
  Derr : 𝔸
  Budget : 𝔸
  L : 𝔸
  Dt : 𝔸
  D4 : 𝔸
  Pg : 𝔸
  P : 𝔸
  c2 : 𝔸
  Dm : 𝔸
  BP : 𝔸
  U : 𝔸
  UBP : 𝔸
  strong : 𝔸
  Df : 𝔸
  Q : 𝔸
  V : 𝔸
  K : 𝔸
  H2 : 𝔸
  H3 : 𝔸
  zc : 𝔸
  zc2 : 𝔸
  Ac : 𝔸
  S : 𝔸
  Z : 𝔸
  RG : 𝔸
  Z2 : 𝔸
  V2 : 𝔸

/-- The registers, row by row as in the DAG (nodes 17–129). -/
def regs (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : Regs 𝔸 :=
  let J := x 0 * 6 + 1
  let qm := p 0 * J
  let q := 1 + qm
  let q2 := q * q
  let q3 := q * q2
  let W := x 6 * 12 + 4
  let X := q * W
  let Y := q3 * (1 + x 5 * 2)
  let E := X * Y
  let a := Y + E
  let H := 4 * a + 3
  let Delta := H + a * a
  let A := 2 + a
  let F := x 1 * (p 1 + W) - x 2 * qm
  let R := (q * (q - F) - x 1) * (q2 - 1) + J * (p 2 + p 3 * q)
  let q24 := q2 * 4
  let k := 1 + R + x 3 * E
  let Yk := Y * k
  let eta := x 8 - Yk
  let Derr := (p 4 * F - q) * (p 4 * F - q) + (x 1 * p 5 - q) * (x 1 * p 5 - q)
  let Budget := k * k * (q2 - Derr) - eta * (q24 * eta)
  let L := E * Yk
  let Dt := 1 + L * (k + L)
  let D4 := Budget - 4
  let Pg := x 10 * Dt
  let P := Dt + Pg * (D4 * Pg)
  let c2 := x 8 * x 8
  let Dm := 1 + Delta * c2
  let BP := P * Dm
  let U := A * (x 4 * c2)
  let UBP := BP * U
  let strong := UBP * (Delta * U)
  let Df := 1 + strong
  let Q := Delta * strong
  let V := Df * (x 8 - R + x 7 * (4 * UBP)) - x 8
  let K := 2 + X * (x 8 * 3 - X * 2)
  let H2 := H * H
  let H3 := H * H2
  let zc := K + x 7 * H
  let zc2 := zc * zc
  let Ac := (zc2 + 3 * H2) * (zc * zc2 - H3 * 19)
  let S := H * (x 4 * x 10)
  let Z := x 9 * S - Ac
  let RG := Df * (BP * (S * S))
  let Z2 := Z * Z
  let V2 := V * V
  { J, qm, q, q2, q3, W, X, Y, E, a, H, Delta, A, F, R, q24, k, Yk, eta, Derr, Budget, L, Dt,
    D4, Pg, P, c2, Dm, BP, U, UBP, strong, Df, Q, V, K, H2, H3, zc, zc2, Ac, S, Z, RG, Z2, V2 }

/-- The value of the 107-operation circuit (output node 130). -/
def value (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 :=
  let r := regs p x
  r.Q * (r.Z2 - r.RG * r.V2) + (r.RG - r.Z2)

/-! ### Register equations (by `rfl`) -/

section Defs
variable (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸)
local notation "𝓡" => regs p x

theorem value_def : value p x = (𝓡).Q * ((𝓡).Z2 - (𝓡).RG * (𝓡).V2) + ((𝓡).RG - (𝓡).Z2) := rfl
theorem J_def : (𝓡).J = x 0 * 6 + 1 := rfl
theorem qm_def : (𝓡).qm = p 0 * (𝓡).J := rfl
theorem q_def : (𝓡).q = 1 + (𝓡).qm := rfl
theorem q2_def : (𝓡).q2 = (𝓡).q * (𝓡).q := rfl
theorem q3_def : (𝓡).q3 = (𝓡).q * (𝓡).q2 := rfl
theorem W_def : (𝓡).W = x 6 * 12 + 4 := rfl
theorem X_def : (𝓡).X = (𝓡).q * (𝓡).W := rfl
theorem Y_def : (𝓡).Y = (𝓡).q3 * (1 + x 5 * 2) := rfl
theorem E_def : (𝓡).E = (𝓡).X * (𝓡).Y := rfl
theorem a_def : (𝓡).a = (𝓡).Y + (𝓡).E := rfl
theorem H_def : (𝓡).H = 4 * (𝓡).a + 3 := rfl
theorem Delta_def : (𝓡).Delta = (𝓡).H + (𝓡).a * (𝓡).a := rfl
theorem A_def : (𝓡).A = 2 + (𝓡).a := rfl
theorem F_def : (𝓡).F = x 1 * (p 1 + (𝓡).W) - x 2 * (𝓡).qm := rfl
theorem R_def : (𝓡).R = ((𝓡).q * ((𝓡).q - (𝓡).F) - x 1) * ((𝓡).q2 - 1) +
    (𝓡).J * (p 2 + p 3 * (𝓡).q) := rfl
theorem q24_def : (𝓡).q24 = (𝓡).q2 * 4 := rfl
theorem k_def : (𝓡).k = 1 + (𝓡).R + x 3 * (𝓡).E := rfl
theorem Yk_def : (𝓡).Yk = (𝓡).Y * (𝓡).k := rfl
theorem eta_def : (𝓡).eta = x 8 - (𝓡).Yk := rfl
theorem Derr_def : (𝓡).Derr = (p 4 * (𝓡).F - (𝓡).q) * (p 4 * (𝓡).F - (𝓡).q) +
    (x 1 * p 5 - (𝓡).q) * (x 1 * p 5 - (𝓡).q) := rfl
theorem Budget_def : (𝓡).Budget = (𝓡).k * (𝓡).k * ((𝓡).q2 - (𝓡).Derr) -
    (𝓡).eta * ((𝓡).q24 * (𝓡).eta) := rfl
theorem L_def : (𝓡).L = (𝓡).E * (𝓡).Yk := rfl
theorem Dt_def : (𝓡).Dt = 1 + (𝓡).L * ((𝓡).k + (𝓡).L) := rfl
theorem D4_def : (𝓡).D4 = (𝓡).Budget - 4 := rfl
theorem Pg_def : (𝓡).Pg = x 10 * (𝓡).Dt := rfl
theorem P_def : (𝓡).P = (𝓡).Dt + (𝓡).Pg * ((𝓡).D4 * (𝓡).Pg) := rfl
theorem c2_def : (𝓡).c2 = x 8 * x 8 := rfl
theorem Dm_def : (𝓡).Dm = 1 + (𝓡).Delta * (𝓡).c2 := rfl
theorem BP_def : (𝓡).BP = (𝓡).P * (𝓡).Dm := rfl
theorem U_def : (𝓡).U = (𝓡).A * (x 4 * (𝓡).c2) := rfl
theorem UBP_def : (𝓡).UBP = (𝓡).BP * (𝓡).U := rfl
theorem strong_def : (𝓡).strong = (𝓡).UBP * ((𝓡).Delta * (𝓡).U) := rfl
theorem Df_def : (𝓡).Df = 1 + (𝓡).strong := rfl
theorem Q_def : (𝓡).Q = (𝓡).Delta * (𝓡).strong := rfl
theorem V_def : (𝓡).V = (𝓡).Df * (x 8 - (𝓡).R + x 7 * (4 * (𝓡).UBP)) - x 8 := rfl
theorem K_def : (𝓡).K = 2 + (𝓡).X * (x 8 * 3 - (𝓡).X * 2) := rfl
theorem H2_def : (𝓡).H2 = (𝓡).H * (𝓡).H := rfl
theorem H3_def : (𝓡).H3 = (𝓡).H * (𝓡).H2 := rfl
theorem zc_def : (𝓡).zc = (𝓡).K + x 7 * (𝓡).H := rfl
theorem zc2_def : (𝓡).zc2 = (𝓡).zc * (𝓡).zc := rfl
theorem Ac_def : (𝓡).Ac = ((𝓡).zc2 + 3 * (𝓡).H2) * ((𝓡).zc * (𝓡).zc2 - (𝓡).H3 * 19) := rfl
theorem S_def : (𝓡).S = (𝓡).H * (x 4 * x 10) := rfl
theorem Z_def : (𝓡).Z = x 9 * (𝓡).S - (𝓡).Ac := rfl
theorem RG_def : (𝓡).RG = (𝓡).Df * ((𝓡).BP * ((𝓡).S * (𝓡).S)) := rfl
theorem Z2_def : (𝓡).Z2 = (𝓡).Z * (𝓡).Z := rfl
theorem V2_def : (𝓡).V2 = (𝓡).V * (𝓡).V := rfl

/-! ### Closed forms in the notation of `PROOF.md` -/

theorem q_eq : (𝓡).q = p 0 * (6 * x 0 + 1) + 1 := by
  rw [q_def, qm_def, J_def]; ring

theorem qm_eq : (𝓡).qm = (𝓡).q - 1 := by rw [q_def]; ring

theorem W_eq : (𝓡).W = 12 * x 6 + 4 := by rw [W_def]; ring

theorem Y_eq : (𝓡).Y = (2 * x 5 + 1) * (𝓡).q ^ 3 := by
  rw [Y_def, q3_def, q2_def]; ring

theorem a_eq : (𝓡).a = (𝓡).X * (𝓡).Y + (𝓡).Y := by rw [a_def, E_def]; ring

theorem A_eq : (𝓡).A = (𝓡).a + 2 := by rw [A_def]; ring

theorem H_eq : (𝓡).H = 4 * (𝓡).a + 3 := H_def p x

theorem Delta_eq : (𝓡).Delta = (𝓡).A ^ 2 - 1 := by
  rw [Delta_def, A_def, H_def]; ring

theorem F_eq : (𝓡).F = (p 1 + (𝓡).W) * x 1 - x 2 * ((𝓡).q - 1) := by
  rw [F_def, qm_eq]; ring

theorem R_eq : (𝓡).R = ((𝓡).q * ((𝓡).q - (𝓡).F) - x 1) * ((𝓡).q ^ 2 - 1) +
    (p 2 + (𝓡).q * p 3) * (𝓡).J := by
  rw [R_def, q2_def]; ring

theorem k_eq : (𝓡).k = (𝓡).R + 1 + x 3 * (𝓡).E := by rw [k_def]; ring

theorem eta_eq : (𝓡).eta = x 8 - (𝓡).Y * (𝓡).k := by rw [eta_def, Yk_def]

theorem Derr_eq : (𝓡).Derr = (p 4 * (𝓡).F - (𝓡).q) ^ 2 + (p 5 * x 1 - (𝓡).q) ^ 2 := by
  rw [Derr_def]; ring

theorem Budget_eq : (𝓡).Budget = (𝓡).k ^ 2 * ((𝓡).q ^ 2 - (𝓡).Derr) -
    4 * (𝓡).q ^ 2 * (𝓡).eta ^ 2 := by
  rw [Budget_def, q24_def, q2_def]; ring

theorem L_eq : (𝓡).L = (𝓡).X * (𝓡).Y ^ 2 * (𝓡).k := by
  rw [L_def, E_def, Yk_def]; ring

theorem Dt_eq : (𝓡).Dt = 1 + ((𝓡).X * (𝓡).Y ^ 2) * ((𝓡).X * (𝓡).Y ^ 2 + 1) * (𝓡).k ^ 2 := by
  rw [Dt_def, L_eq]; ring

theorem D4_eq : (𝓡).D4 = (𝓡).Budget - 4 := D4_def p x

/-- `P = Dt · Dg` with the guard `Dg = 1 + D Dt s²`, `D = Budget − 4`. -/
theorem P_eq : (𝓡).P = (𝓡).Dt * (1 + (𝓡).D4 * (𝓡).Dt * x 10 ^ 2) := by
  rw [P_def, Pg_def]; ring

theorem Dm_eq : (𝓡).Dm = 1 + (𝓡).Delta * x 8 ^ 2 := by rw [Dm_def, c2_def]; ring

theorem BP_eq : (𝓡).BP = (𝓡).Dm * (𝓡).P := by rw [BP_def]; ring

theorem U_eq : (𝓡).U = (𝓡).A * x 4 * x 8 ^ 2 := by rw [U_def, c2_def]; ring

theorem strong_eq : (𝓡).strong = (𝓡).Delta * (𝓡).U ^ 2 * (𝓡).BP := by
  rw [strong_def, UBP_def]; ring

theorem Df_eq : (𝓡).Df = 1 + (𝓡).Delta * (𝓡).U ^ 2 * (𝓡).BP := by
  rw [Df_def, strong_eq]

theorem Q_eq : (𝓡).Q = (𝓡).Delta ^ 2 * (𝓡).U ^ 2 * (𝓡).BP := by
  rw [Q_def, strong_eq]; ring

theorem V_eq : (𝓡).V = (𝓡).Df * (x 8 - (𝓡).R + 4 * (𝓡).U * (𝓡).BP * x 7) - x 8 := by
  rw [V_def, UBP_def]; ring

theorem K_eq : (𝓡).K = (𝓡).X * (3 * x 8 - 2 * (𝓡).X) + 2 := by rw [K_def]; ring

theorem zc_eq : (𝓡).zc = (𝓡).H * x 7 + (𝓡).K := by rw [zc_def]; ring

theorem Ac_eq : (𝓡).Ac = ((𝓡).zc ^ 2 + 3 * (𝓡).H ^ 2) * ((𝓡).zc ^ 3 - 19 * (𝓡).H ^ 3) := by
  rw [Ac_def, zc2_def, H2_def, H3_def, H2_def]; ring

theorem S_eq : (𝓡).S = x 10 * x 4 * (𝓡).H := by rw [S_def]; ring

theorem Z_eq : (𝓡).Z = (𝓡).S * x 9 - (𝓡).Ac := by rw [Z_def]; ring

theorem RG_eq : (𝓡).RG = (𝓡).S ^ 2 * (𝓡).BP * (𝓡).Df := by rw [RG_def]; ring

/-- **Identity (4)** of `PROOF.md`: the output is `(Q − 1) Z² − RG (Q V² − 1)`. -/
theorem value_eq : value p x = ((𝓡).Q - 1) * (𝓡).Z ^ 2 - (𝓡).RG * ((𝓡).Q * (𝓡).V ^ 2 - 1) := by
  rw [value_def, Z2_def, V2_def]; ring

/-- The zero set in register form: `δ Z² = S² BP Df Cy`. -/
theorem value_eq_product : value p x =
    ((𝓡).Q - 1) * (𝓡).Z ^ 2 - (𝓡).S ^ 2 * (𝓡).BP * (𝓡).Df * ((𝓡).Q * (𝓡).V ^ 2 - 1) := by
  rw [value_eq, RG_eq]

end Defs
end Generic

#print axioms DiophantineConsistency.P138Value.value_eq
#print axioms DiophantineConsistency.P138Value.value_eq_product
#print axioms DiophantineConsistency.P138Value.P_eq
#print axioms DiophantineConsistency.P138Value.Dt_eq

end DiophantineConsistency.P138Value
