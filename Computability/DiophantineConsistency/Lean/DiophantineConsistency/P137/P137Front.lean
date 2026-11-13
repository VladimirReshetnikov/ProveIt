import DiophantineConsistency.P138.P138Value

/-! # The weak front and the saturated carrier of the eleven-integer weak equations

Two eleven-integer equations share their first registers node for node:

* package 137's `integer/weak_product11_none.json` (exact degree 648, 115 operations);
* package 135's `scalar/weak_cofactor11_none.json` (exact degree 398, 121 operations).

Both read the unknowns `j C z h r v w T c n s` (`x 0 .. x 10`) and the six ports
`beta K0 MC MF cone_A cone_B` (`p 0 .. p 5`) of package 138. Against `P138Value.regsK`:

* the *weak front* has `Y = v q` in place of `Y = q³ (2v + 1)`; every register that does not
  read `v` (`J, qm, q, q2, W, X, F, R, Derr, c2, K`) is the same term as in `regsK`;
* the *saturated carrier* is `M = 2 q²`, `Dcar = H M`, `S = M⁴ Dcar r s = M⁵ H r s`,
  `zc = T Dcar + K M + H (v − q²)`, `Ac = (zc² + 3 Dcar²)(zc³ − 19 Dcar³)`, `Z = n S − Ac`.

`front p x` is the record of these registers, in the operand order of the two JSON files. The
guard and the back end differ between the two equations and live in their own modules.

The second half of the module is the *transfer*: if `v = (1 + 2v') q²`, the weak front at `x`
is the front of `P138Value.regsK` at `Function.update x 5 v'` with the native index. Soundness
recovers such a `v'` from a zero and then runs package 138's leaf chain unchanged. -/
set_option autoImplicit false
namespace DiophantineConsistency.P137Front
open P138Value

section Generic
variable {𝔸 : Type*} [CommRing 𝔸]

/-- The registers shared by the two weak equations. -/
structure Front (𝔸 : Type*) where
  J : 𝔸
  qm : 𝔸
  q : 𝔸
  q2 : 𝔸
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
  k : 𝔸
  c2 : 𝔸
  Yk : 𝔸
  eta : 𝔸
  Derr : 𝔸
  Budget : 𝔸
  L : 𝔸
  Dt : 𝔸
  Dm : 𝔸
  K : 𝔸
  M : 𝔸
  Dcar : 𝔸
  M2 : 𝔸
  M4 : 𝔸
  Dcar2 : 𝔸
  Dcar3 : 𝔸
  S : 𝔸
  S2 : 𝔸
  zc : 𝔸
  zc2 : 𝔸
  Ac : 𝔸
  Z : 𝔸

/-- The weak front and the saturated carrier, gate for gate. -/
def front (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : Front 𝔸 :=
  let J := x 0 * 6 + 1
  let qm := p 0 * J
  let q := 1 + qm
  let q2 := q * q
  let W := x 6 * 12 + 4
  let X := q * W
  let Y := x 5 * q
  let E := X * Y
  let a := Y + E
  let H := 4 * a + 3
  let Delta := H + a * a
  let A := a + 2
  let F := x 1 * (p 1 + W) - x 2 * qm
  let R := (q * (q - F) - x 1) * (q2 - 1) + J * (p 2 + p 3 * q)
  let k := 1 + R + x 3 * E
  let c2 := x 8 * x 8
  let Yk := Y * k
  let eta := x 8 - Yk
  let Derr := (p 4 * F - q) * (p 4 * F - q) + (x 1 * p 5 - q) * (x 1 * p 5 - q)
  let Budget := k * k * (q2 - Derr) - eta * (eta * (q2 * 4))
  let L := E * Yk
  let Dt := 1 + L * (k + L)
  let Dm := 1 + Delta * c2
  let K := 2 + X * (x 8 * 3 - X * 2)
  let M := q2 * 2
  let Dcar := H * M
  let M2 := M * M
  let M4 := M2 * M2
  let Dcar2 := Dcar * Dcar
  let Dcar3 := Dcar * Dcar2
  let S := M4 * (Dcar * (x 4 * x 10))
  let S2 := S * S
  let zc := x 7 * Dcar + K * M + H * (x 5 - q2)
  let zc2 := zc * zc
  let Ac := (zc2 + 3 * Dcar2) * (zc * zc2 - Dcar3 * 19)
  let Z := x 9 * S - Ac
  { J, qm, q, q2, W, X, Y, E, a, H, Delta, A, F, R, k, c2, Yk, eta, Derr, Budget, L, Dt, Dm, K,
    M, Dcar, M2, M4, Dcar2, Dcar3, S, S2, zc, zc2, Ac, Z }

section Defs
variable (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸)
local notation "𝓕" => front p x

/-! ### Register equations -/

theorem J_def : (𝓕).J = x 0 * 6 + 1 := rfl
theorem qm_def : (𝓕).qm = p 0 * (𝓕).J := rfl
theorem q_def : (𝓕).q = 1 + (𝓕).qm := rfl
theorem q2_def : (𝓕).q2 = (𝓕).q * (𝓕).q := rfl
theorem W_def : (𝓕).W = x 6 * 12 + 4 := rfl
theorem X_def : (𝓕).X = (𝓕).q * (𝓕).W := rfl
theorem Y_def : (𝓕).Y = x 5 * (𝓕).q := rfl
theorem E_def : (𝓕).E = (𝓕).X * (𝓕).Y := rfl
theorem a_def : (𝓕).a = (𝓕).Y + (𝓕).E := rfl
theorem H_def : (𝓕).H = 4 * (𝓕).a + 3 := rfl
theorem Delta_def : (𝓕).Delta = (𝓕).H + (𝓕).a * (𝓕).a := rfl
theorem A_def : (𝓕).A = (𝓕).a + 2 := rfl
theorem F_def : (𝓕).F = x 1 * (p 1 + (𝓕).W) - x 2 * (𝓕).qm := rfl
theorem R_def : (𝓕).R = ((𝓕).q * ((𝓕).q - (𝓕).F) - x 1) * ((𝓕).q2 - 1) +
    (𝓕).J * (p 2 + p 3 * (𝓕).q) := rfl
theorem k_def : (𝓕).k = 1 + (𝓕).R + x 3 * (𝓕).E := rfl
theorem c2_def : (𝓕).c2 = x 8 * x 8 := rfl
theorem Yk_def : (𝓕).Yk = (𝓕).Y * (𝓕).k := rfl
theorem eta_def : (𝓕).eta = x 8 - (𝓕).Yk := rfl
theorem Derr_def : (𝓕).Derr = (p 4 * (𝓕).F - (𝓕).q) * (p 4 * (𝓕).F - (𝓕).q) +
    (x 1 * p 5 - (𝓕).q) * (x 1 * p 5 - (𝓕).q) := rfl
theorem Budget_def : (𝓕).Budget = (𝓕).k * (𝓕).k * ((𝓕).q2 - (𝓕).Derr) -
    (𝓕).eta * ((𝓕).eta * ((𝓕).q2 * 4)) := rfl
theorem L_def : (𝓕).L = (𝓕).E * (𝓕).Yk := rfl
theorem Dt_def : (𝓕).Dt = 1 + (𝓕).L * ((𝓕).k + (𝓕).L) := rfl
theorem Dm_def : (𝓕).Dm = 1 + (𝓕).Delta * (𝓕).c2 := rfl
theorem K_def : (𝓕).K = 2 + (𝓕).X * (x 8 * 3 - (𝓕).X * 2) := rfl
theorem M_def : (𝓕).M = (𝓕).q2 * 2 := rfl
theorem Dcar_def : (𝓕).Dcar = (𝓕).H * (𝓕).M := rfl
theorem M2_def : (𝓕).M2 = (𝓕).M * (𝓕).M := rfl
theorem M4_def : (𝓕).M4 = (𝓕).M2 * (𝓕).M2 := rfl
theorem Dcar2_def : (𝓕).Dcar2 = (𝓕).Dcar * (𝓕).Dcar := rfl
theorem Dcar3_def : (𝓕).Dcar3 = (𝓕).Dcar * (𝓕).Dcar2 := rfl
theorem S_def : (𝓕).S = (𝓕).M4 * ((𝓕).Dcar * (x 4 * x 10)) := rfl
theorem S2_def : (𝓕).S2 = (𝓕).S * (𝓕).S := rfl
theorem zc_def : (𝓕).zc = x 7 * (𝓕).Dcar + (𝓕).K * (𝓕).M + (𝓕).H * (x 5 - (𝓕).q2) := rfl
theorem zc2_def : (𝓕).zc2 = (𝓕).zc * (𝓕).zc := rfl
theorem Ac_def : (𝓕).Ac = ((𝓕).zc2 + 3 * (𝓕).Dcar2) * ((𝓕).zc * (𝓕).zc2 - (𝓕).Dcar3 * 19) := rfl
theorem Z_def : (𝓕).Z = x 9 * (𝓕).S - (𝓕).Ac := rfl

/-! ### The registers that do not read `v` are those of `P138Value.regsK` -/

theorem J_regs (κ : 𝔸) : (𝓕).J = (regsK p x κ).J := rfl
theorem qm_regs (κ : 𝔸) : (𝓕).qm = (regsK p x κ).qm := rfl
theorem q_regs (κ : 𝔸) : (𝓕).q = (regsK p x κ).q := rfl
theorem q2_regs (κ : 𝔸) : (𝓕).q2 = (regsK p x κ).q2 := rfl
theorem W_regs (κ : 𝔸) : (𝓕).W = (regsK p x κ).W := rfl
theorem X_regs (κ : 𝔸) : (𝓕).X = (regsK p x κ).X := rfl
theorem F_regs (κ : 𝔸) : (𝓕).F = (regsK p x κ).F := rfl
theorem R_regs (κ : 𝔸) : (𝓕).R = (regsK p x κ).R := rfl
theorem Derr_regs (κ : 𝔸) : (𝓕).Derr = (regsK p x κ).Derr := rfl
theorem K_regs (κ : 𝔸) : (𝓕).K = (regsK p x κ).K := rfl

/-! ### Closed forms -/

theorem qm_eq : (𝓕).qm = (𝓕).q - 1 := by rw [q_def]; ring

/-- `a = Y (1 + X)`. -/
theorem a_eq : (𝓕).a = (𝓕).Y * (1 + (𝓕).X) := by rw [a_def, E_def]; ring

/-- `a = q · v (1 + X)`: the modulus `q` divides `a`. -/
theorem a_eq_q : (𝓕).a = (𝓕).q * (x 5 * (1 + (𝓕).X)) := by rw [a_eq, Y_def]; ring

theorem Delta_eq : (𝓕).Delta = (𝓕).A ^ 2 - 1 := by rw [Delta_def, A_def, H_def]; ring

theorem eta_eq : (𝓕).eta = x 8 - (𝓕).Y * (𝓕).k := by rw [eta_def, Yk_def]

theorem Budget_eq : (𝓕).Budget = (𝓕).k ^ 2 * ((𝓕).q ^ 2 - (𝓕).Derr) -
    4 * (𝓕).q ^ 2 * (𝓕).eta ^ 2 := by
  rw [Budget_def, q2_def]; ring

theorem L_eq : (𝓕).L = (𝓕).X * (𝓕).Y ^ 2 * (𝓕).k := by rw [L_def, E_def, Yk_def]; ring

theorem Dt_eq : (𝓕).Dt = 1 + ((𝓕).X * (𝓕).Y ^ 2) * ((𝓕).X * (𝓕).Y ^ 2 + 1) * (𝓕).k ^ 2 := by
  rw [Dt_def, L_eq]; ring

theorem Dm_eq : (𝓕).Dm = 1 + (𝓕).Delta * x 8 ^ 2 := by rw [Dm_def, c2_def]; ring

theorem M_eq : (𝓕).M = 2 * (𝓕).q ^ 2 := by rw [M_def, q2_def]; ring

/-- `S = M⁵ H r s`. -/
theorem S_eq : (𝓕).S = (𝓕).M ^ 5 * ((𝓕).H * (x 4 * x 10)) := by
  rw [S_def, M4_def, M2_def, Dcar_def]; ring

/-- `zc = M (T H + K) + H (v − q²)`. -/
theorem zc_eq : (𝓕).zc = (𝓕).M * (x 7 * (𝓕).H + (𝓕).K) + (𝓕).H * (x 5 - (𝓕).q2) := by
  rw [zc_def, Dcar_def]; ring

theorem Ac_eq : (𝓕).Ac = ((𝓕).zc ^ 2 + 3 * (𝓕).Dcar ^ 2) * ((𝓕).zc ^ 3 - 19 * (𝓕).Dcar ^ 3) := by
  rw [Ac_def, zc2_def, Dcar3_def, Dcar2_def]; ring

/-- The carrier quintic, expanded in powers of `M`. -/
theorem Ac_quintic : (𝓕).Ac = (𝓕).zc ^ 5 + 3 * (𝓕).H ^ 2 * (𝓕).M ^ 2 * (𝓕).zc ^ 3 +
    -(19 * (𝓕).H ^ 3) * (𝓕).M ^ 3 * (𝓕).zc ^ 2 + -(57 * (𝓕).H ^ 5) * (𝓕).M ^ 5 := by
  rw [Ac_eq, Dcar_def]; ring

theorem Z_eq : (𝓕).Z = (𝓕).S * x 9 - (𝓕).Ac := by rw [Z_def]; ring

/-- The projector register `Kq = X (X + 2 a c) − 1`. -/
def Kq : 𝔸 := (𝓕).X * ((𝓕).X + 2 * (𝓕).a * x 8) - 1

theorem K_Kq : (𝓕).K = (𝓕).H * (𝓕).X * x 8 - 2 * Kq p x := by
  unfold Kq; rw [K_def, H_def]; ring

end Defs

/-! ### Transfer to `P138Value.regsK` once `v = (1 + 2v') q²` -/

section Transfer
variable (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) (v' : 𝔸)
local notation "𝓕" => front p x
local notation "x'" => Function.update x 5 v'

theorem tr_q (κ : 𝔸) : (regsK p x' κ).q = (𝓕).q := rfl
theorem tr_q2 (κ : 𝔸) : (regsK p x' κ).q2 = (𝓕).q2 := rfl
theorem tr_X (κ : 𝔸) : (regsK p x' κ).X = (𝓕).X := rfl
theorem tr_F (κ : 𝔸) : (regsK p x' κ).F = (𝓕).F := rfl
theorem tr_R (κ : 𝔸) : (regsK p x' κ).R = (𝓕).R := rfl
theorem tr_Derr (κ : 𝔸) : (regsK p x' κ).Derr = (𝓕).Derr := rfl

omit [CommRing 𝔸] in
theorem upd_3 : x' 3 = x 3 := Function.update_of_ne (by decide) _ _
omit [CommRing 𝔸] in
theorem upd_4 : x' 4 = x 4 := Function.update_of_ne (by decide) _ _
omit [CommRing 𝔸] in
theorem upd_8 : x' 8 = x 8 := Function.update_of_ne (by decide) _ _
omit [CommRing 𝔸] in
theorem upd_10 : x' 10 = x 10 := Function.update_of_ne (by decide) _ _

theorem tr_Y (hv : x 5 = (1 + v' * 2) * (front p x).q2) (κ : 𝔸) :
    (regsK p x' κ).Y = (𝓕).Y := by
  rw [P138Value.Y_eq, Function.update_self, tr_q, Y_def, hv, q2_def]; ring

theorem tr_E (hv : x 5 = (1 + v' * 2) * (front p x).q2) (κ : 𝔸) :
    (regsK p x' κ).E = (𝓕).E := by
  rw [P138Value.E_def, tr_X, tr_Y p x v' hv, E_def]

theorem tr_a (hv : x 5 = (1 + v' * 2) * (front p x).q2) (κ : 𝔸) :
    (regsK p x' κ).a = (𝓕).a := by
  rw [P138Value.a_def, tr_Y p x v' hv, tr_E p x v' hv, a_def]

theorem tr_H (hv : x 5 = (1 + v' * 2) * (front p x).q2) (κ : 𝔸) :
    (regsK p x' κ).H = (𝓕).H := by
  rw [P138Value.H_def, tr_a p x v' hv, H_def]

theorem tr_Delta (hv : x 5 = (1 + v' * 2) * (front p x).q2) (κ : 𝔸) :
    (regsK p x' κ).Delta = (𝓕).Delta := by
  rw [P138Value.Delta_def, tr_H p x v' hv, tr_a p x v' hv, Delta_def]

theorem tr_A (hv : x 5 = (1 + v' * 2) * (front p x).q2) (κ : 𝔸) :
    (regsK p x' κ).A = (𝓕).A := by
  rw [P138Value.A_def, tr_a p x v' hv, A_def]; ring

theorem tr_Dm (hv : x 5 = (1 + v' * 2) * (front p x).q2) (κ : 𝔸) :
    (regsK p x' κ).Dm = (𝓕).Dm := by
  rw [P138Value.Dm_eq, tr_Delta p x v' hv, upd_8, Dm_eq]

/-- The native index at the updated point is the weak index. -/
theorem tr_kN (hv : x 5 = (1 + v' * 2) * (front p x).q2) : kN p x' = (𝓕).k := by
  rw [kN_eq p x' 0, tr_R, tr_E p x v' hv, upd_3, k_def]; ring

theorem tr_k (hv : x 5 = (1 + v' * 2) * (front p x).q2) :
    (regsK p x' (kN p x')).k = (𝓕).k := by
  rw [k_reg, tr_kN p x v' hv]

theorem tr_eta (hv : x 5 = (1 + v' * 2) * (front p x).q2) :
    (regsK p x' (kN p x')).eta = (𝓕).eta := by
  rw [P138Value.eta_eq, tr_Y p x v' hv, tr_k p x v' hv, upd_8, eta_eq]

theorem tr_Budget (hv : x 5 = (1 + v' * 2) * (front p x).q2) :
    (regsK p x' (kN p x')).Budget = (𝓕).Budget := by
  rw [P138Value.Budget_eq, tr_k p x v' hv, tr_q, tr_Derr, tr_eta p x v' hv, Budget_eq]

theorem tr_Dt (hv : x 5 = (1 + v' * 2) * (front p x).q2) :
    (regsK p x' (kN p x')).Dt = (𝓕).Dt := by
  rw [P138Value.Dt_eq, tr_X, tr_Y p x v' hv, tr_k p x v' hv, Dt_eq]

end Transfer
end Generic

#print axioms DiophantineConsistency.P137Front.Ac_quintic
#print axioms DiophantineConsistency.P137Front.K_Kq
#print axioms DiophantineConsistency.P137Front.tr_Budget
#print axioms DiophantineConsistency.P137Front.tr_Dt
#print axioms DiophantineConsistency.P137Front.tr_Dm

end DiophantineConsistency.P137Front
