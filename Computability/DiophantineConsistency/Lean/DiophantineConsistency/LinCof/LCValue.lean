import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! # The linear-cofactor family, register by register

The eleven-integer equations of package 172
(`con-zfc-diophantine-forms/172-pooled-powers-round21/part2/…/scalar/integer11`),
`integer11_degree298_ops146.json` (298/146) and `integer11_degree300_ops144.json` (300/144),
are two members of the *linear-cofactor* family: free scale `Y = v`, linear cofactor
`B = r·A·Dm`, carrier at `Dc = H·M` with `M = 2q³`, a whole-expression center `Ψ`, and the
two-radical norm

    N = (pa + pb − pc)² − 4·pa·pb,   pa = δ Z²,  pb = δ S² P,  pc = wt S² B Df Cy,

with radical weight `wt = 1024`.

Their eleven unrestricted integer unknowns, in order, are `j C z h r v w T c n s`
(`x 0 … x 10`); their six fixed integers are `beta K0 MC MF cone_A cone_B` (`p 0 … p 5`).

The two DAGs agree gate for gate, operand order included, except in four registers:

| slot | register | 298/146 | 300/144 |
|---|---|---|---|
| `κ` | `k`   | `1 + R + h·ell`, `ell = v·E` | `1 + R + h·E` |
| `ω` | `kq2` | `q2 · k`                     | `k · q3` |
| `Λ` | `L`   | `ell · k`                    | `E · Yk` |
| `ψ` | `Psi` | `V·lam + UT·(rc4·(cm2·gamma − c2) + Delta·A·64)` | `V·lam + UT·((rc4·cm2 + A·8)·(gamma − 1))` |

So the circuit is written once, with these four registers and the radical weight as parameters:
`regsK p x κ ω Λ ψ wt`
evaluates every named register in an arbitrary commutative ring, row by row with the operand
order of the JSON DAGs (unnamed DAG nodes are inlined), and `valueK p x κ ω Λ ψ wt` is the output.
The slot fillers of the two forms (`k298`, `kq298`, `L298`, `psi298`; `k300`, `kq300`, `L300`,
`psi300`) read only registers that do not depend on the slots, at the dummy slots `0`.

What the soundness argument uses about the slots is `SlotLaw p x κ ω Λ e`:

    ω = κ · q^(2+e),        Λ = X · Y² · κ,

with `e = 0` for 298/146 (budget power `q⁶`) and `e = 1` for 300/144 (budget power `q⁸`), so that

    Budget = Y² · B0 − k² · q^(6+2e),   B0 = k² (q² − Derr) − 4 q² η².

The center `ψ` is unconstrained: soundness never reads it. The weight `wt` is the fifth slot: the
two forms of package 172 use `1024`; soundness needs only that it is an even nonzero square
(`LCNorm.Weight`), so the same circuit serves the sibling forms with weight `4` and `64`.

The register equations `*_def` hold by `rfl`; the closed forms (`*_eq`) and the value identity
(`value_eq`) are proved by `ring` with the registers as atoms, never by expanding the output.
This module imports neither Foundation nor Mathlib's matrices. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.LCValue

section Generic
variable {𝔸 : Type*} [CommRing 𝔸]

/-- The named registers of the circuit (`named_registers` of the JSON DAGs; `ell` is named only
in 298/146, and the registers inside the two centers are not fields). -/
structure Regs (𝔸 : Type*) where
  J : 𝔸
  qm : 𝔸
  q : 𝔸
  q2 : 𝔸
  W : 𝔸
  X : 𝔸
  Y : 𝔸
  E : 𝔸
  ell : 𝔸
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
  q3 : 𝔸
  Yeta : 𝔸
  kq2 : 𝔸
  Budget : 𝔸
  L : 𝔸
  Dt : 𝔸
  Dguard : 𝔸
  Pg : 𝔸
  P : 𝔸
  Dm : 𝔸
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
  K : 𝔸
  M : 𝔸
  Dc : 𝔸
  M2 : 𝔸
  M4 : 𝔸
  Dc2 : 𝔸
  Dc3 : 𝔸
  S : 𝔸
  S2 : 𝔸
  zc : 𝔸
  zc2 : 𝔸
  Ac : 𝔸
  c4 : 𝔸
  rc4 : 𝔸
  U2 : 𝔸
  UT : 𝔸
  cm2 : 𝔸
  gamma : 𝔸
  lam : 𝔸
  Psi : 𝔸
  Z : 𝔸
  Z2 : 𝔸
  pa : 𝔸
  pb : 𝔸
  pc : 𝔸
  inner : 𝔸

/-- The registers, row by row as in the DAGs, with the slots `k := κ`, `kq2 := ω`, `L := Λ`,
`Psi := ψ` and the radical weight `wt` (the constant factor of `pc`). `x 3` is not read. -/
def regsK (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) (κ ω Λ ψ wt : 𝔸) : Regs 𝔸 :=
  let J := x 0 * 6 + 1
  let qm := p 0 * J
  let q := 1 + qm
  let q2 := q * q
  let W := x 6 * 12 + 4
  let X := q * W
  let Y := x 5
  let E := Y * X
  let ell := Y * E
  let a := Y + E
  let H := 4 * a + 3
  let Delta := H + a * a
  let A := a + 2
  let F := x 1 * (p 1 + W) - x 2 * qm
  let R := (q * (q - F) - x 1) * (q2 - 1) + J * (p 2 + p 3 * q)
  let k := κ
  let c2 := x 8 * x 8
  let Yk := Y * k
  let eta := x 8 - Yk
  let Derr := (p 4 * F - q) * (p 4 * F - q) + (x 1 * p 5 - q) * (x 1 * p 5 - q)
  let q3 := q * q2
  let Yeta := Y * eta
  let kq2 := ω
  let Budget := Yk * Yk * (q2 - Derr) - q2 * (Yeta * (4 * Yeta) + kq2 * kq2)
  let L := Λ
  let Dt := 1 + L * (k + L)
  let Dguard := Budget - 4
  let Pg := x 10 * Dt
  let P := Dt + Pg * (Dguard * Pg)
  let Dm := 1 + Delta * c2
  let rDm := x 4 * Dm
  let B := A * rDm
  let U := c2 * rDm
  let AU := A * U
  let strong := Delta * c2 * AU
  let Df := 1 + strong
  let Q := Delta * strong
  let delta := Q - 1
  let b := x 8 - R + x 7 * (4 * AU)
  let V := Df * b - x 8
  let Cy := V * (Q * V) - 1
  let K := 2 + X * (x 8 * 3 - X * 2)
  let M := 2 * q3
  let Dc := H * M
  let M2 := M * M
  let M4 := M2 * M2
  let Dc2 := Dc * Dc
  let Dc3 := Dc * Dc2
  let S := M4 * (Dc * (x 4 * x 10))
  let S2 := S * S
  let zc := x 7 * Dc + K * M + H * (Y - q3)
  let zc2 := zc * zc
  let Ac := (zc2 + 3 * Dc2) * (zc * zc2 - Dc3 * 19)
  let c4 := c2 * c2
  let rc4 := x 4 * c4
  let U2 := U * U
  let UT := x 7 * U2
  let cm2 := c2 - 2
  let gamma := 4 + Delta * 8
  let lam := 4 * (U * gamma - rc4)
  let Psi := ψ
  let Z := S * (x 9 + Psi) - Ac
  let Z2 := Z * Z
  let pa := delta * Z2
  let pb := P * (delta * S2)
  let pc := Cy * (Df * (B * (S2 * wt)))
  let inner := pa + pb - pc
  { J, qm, q, q2, W, X, Y, E, ell, a, H, Delta, A, F, R, k, c2, Yk, eta, Derr, q3, Yeta, kq2,
    Budget, L, Dt, Dguard, Pg, P, Dm, rDm, B, U, AU, strong, Df, Q, delta, b, V, Cy, K, M, Dc,
    M2, M4, Dc2, Dc3, S, S2, zc, zc2, Ac, c4, rc4, U2, UT, cm2, gamma, lam, Psi, Z, Z2, pa, pb,
    pc, inner }

/-- The output `inner · inner − pb · (4 · pa)` at the slots `κ ω Λ ψ wt`. -/
def valueK (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) (κ ω Λ ψ wt : 𝔸) : 𝔸 :=
  let r := regsK p x κ ω Λ ψ wt
  r.inner * r.inner - r.pb * (4 * r.pa)

/-- The inner budget `B0 = k² (q² − Derr) − 4 q² η²` (the register `Budget` of package 138;
not a register here). -/
def B0 (r : Regs 𝔸) : 𝔸 := r.k ^ 2 * (r.q ^ 2 - r.Derr) - 4 * r.q ^ 2 * r.eta ^ 2

/-! ### The slot fillers of the two forms

Every register read below is independent of the slots (`*_slot`), and is read at the dummy
slots `0`. -/

/-- 298/146: `k = 1 + R + h · ell` (nodes 52–54). -/
def k298 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 :=
  1 + (regsK p x 0 0 0 0 0).R + x 3 * (regsK p x 0 0 0 0 0).ell

/-- 298/146: `kq2 = q2 · k` (node 67). -/
def kq298 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 := (regsK p x 0 0 0 0 0).q2 * k298 p x

/-- 298/146: `L = ell · k` (node 77). -/
def L298 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 := (regsK p x 0 0 0 0 0).ell * k298 p x

/-- 298/146: the center `Ψ = V·lam + UT·(rc4·(cm2·gamma − c2) + (Delta·A)·64)`
(nodes 145–154). -/
def psi298 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 :=
  let r := regsK p x 0 0 0 0 0
  r.V * r.lam + r.UT * (r.rc4 * (r.cm2 * r.gamma - r.c2) + r.Delta * r.A * 64)

/-- 300/144: `k = 1 + R + h · E` (nodes 51–53). -/
def k300 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 :=
  1 + (regsK p x 0 0 0 0 0).R + x 3 * (regsK p x 0 0 0 0 0).E

/-- 300/144: `kq2 = k · q3` (node 66). -/
def kq300 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 := k300 p x * (regsK p x 0 0 0 0 0).q3

/-- 300/144: `L = E · Yk` (node 76). -/
def L300 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 :=
  (regsK p x 0 0 0 0 0).E * ((regsK p x 0 0 0 0 0).Y * k300 p x)

/-- 300/144: the center `Ψ = V·lam + UT·((rc4·cm2 + A·8)·(gamma − 1))` (nodes 144–151). -/
def psi300 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 :=
  let r := regsK p x 0 0 0 0 0
  r.V * r.lam + r.UT * ((r.rc4 * r.cm2 + r.A * 8) * (r.gamma - 1))

/-- The registers of the 298/146 circuit. -/
abbrev regs298 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : Regs 𝔸 :=
  regsK p x (k298 p x) (kq298 p x) (L298 p x) (psi298 p x) 1024

/-- The value of the 146-operation circuit (output node 172). -/
abbrev value298 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 :=
  valueK p x (k298 p x) (kq298 p x) (L298 p x) (psi298 p x) 1024

/-- The registers of the 300/144 circuit. -/
abbrev regs300 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : Regs 𝔸 :=
  regsK p x (k300 p x) (kq300 p x) (L300 p x) (psi300 p x) 1024

/-- The value of the 144-operation circuit (output node 169). -/
abbrev value300 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 :=
  valueK p x (k300 p x) (kq300 p x) (L300 p x) (psi300 p x) 1024

/-! ### Register equations (by `rfl`) -/

section Defs
variable (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) (κ ω Λ ψ wt : 𝔸)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

theorem value_def : valueK p x κ ω Λ ψ wt = (𝓡).inner * (𝓡).inner - (𝓡).pb * (4 * (𝓡).pa) := rfl
theorem J_def : (𝓡).J = x 0 * 6 + 1 := rfl
theorem qm_def : (𝓡).qm = p 0 * (𝓡).J := rfl
theorem q_def : (𝓡).q = 1 + (𝓡).qm := rfl
theorem q2_def : (𝓡).q2 = (𝓡).q * (𝓡).q := rfl
theorem W_def : (𝓡).W = x 6 * 12 + 4 := rfl
theorem X_def : (𝓡).X = (𝓡).q * (𝓡).W := rfl
/-- The scale is the free unknown `v`. -/
theorem Y_def : (𝓡).Y = x 5 := rfl
theorem E_def : (𝓡).E = (𝓡).Y * (𝓡).X := rfl
theorem ell_def : (𝓡).ell = (𝓡).Y * (𝓡).E := rfl
theorem a_def : (𝓡).a = (𝓡).Y + (𝓡).E := rfl
theorem H_def : (𝓡).H = 4 * (𝓡).a + 3 := rfl
theorem Delta_def : (𝓡).Delta = (𝓡).H + (𝓡).a * (𝓡).a := rfl
theorem A_def : (𝓡).A = (𝓡).a + 2 := rfl
theorem F_def : (𝓡).F = x 1 * (p 1 + (𝓡).W) - x 2 * (𝓡).qm := rfl
theorem R_def : (𝓡).R = ((𝓡).q * ((𝓡).q - (𝓡).F) - x 1) * ((𝓡).q2 - 1) +
    (𝓡).J * (p 2 + p 3 * (𝓡).q) := rfl
/-- The `k` slot. -/
theorem k_reg : (𝓡).k = κ := rfl
theorem c2_def : (𝓡).c2 = x 8 * x 8 := rfl
theorem Yk_def : (𝓡).Yk = (𝓡).Y * (𝓡).k := rfl
theorem eta_def : (𝓡).eta = x 8 - (𝓡).Yk := rfl
theorem Derr_def : (𝓡).Derr = (p 4 * (𝓡).F - (𝓡).q) * (p 4 * (𝓡).F - (𝓡).q) +
    (x 1 * p 5 - (𝓡).q) * (x 1 * p 5 - (𝓡).q) := rfl
theorem q3_def : (𝓡).q3 = (𝓡).q * (𝓡).q2 := rfl
theorem Yeta_def : (𝓡).Yeta = (𝓡).Y * (𝓡).eta := rfl
/-- The `kq2` slot. -/
theorem kq2_reg : (𝓡).kq2 = ω := rfl
theorem Budget_def : (𝓡).Budget = (𝓡).Yk * (𝓡).Yk * ((𝓡).q2 - (𝓡).Derr) -
    (𝓡).q2 * ((𝓡).Yeta * (4 * (𝓡).Yeta) + (𝓡).kq2 * (𝓡).kq2) := rfl
/-- The `L` slot. -/
theorem L_reg : (𝓡).L = Λ := rfl
theorem Dt_def : (𝓡).Dt = 1 + (𝓡).L * ((𝓡).k + (𝓡).L) := rfl
theorem Dguard_def : (𝓡).Dguard = (𝓡).Budget - 4 := rfl
theorem Pg_def : (𝓡).Pg = x 10 * (𝓡).Dt := rfl
theorem P_def : (𝓡).P = (𝓡).Dt + (𝓡).Pg * ((𝓡).Dguard * (𝓡).Pg) := rfl
theorem Dm_def : (𝓡).Dm = 1 + (𝓡).Delta * (𝓡).c2 := rfl
theorem rDm_def : (𝓡).rDm = x 4 * (𝓡).Dm := rfl
theorem B_def : (𝓡).B = (𝓡).A * (𝓡).rDm := rfl
theorem U_def : (𝓡).U = (𝓡).c2 * (𝓡).rDm := rfl
theorem AU_def : (𝓡).AU = (𝓡).A * (𝓡).U := rfl
theorem strong_def : (𝓡).strong = (𝓡).Delta * (𝓡).c2 * (𝓡).AU := rfl
theorem Df_def : (𝓡).Df = 1 + (𝓡).strong := rfl
theorem Q_def : (𝓡).Q = (𝓡).Delta * (𝓡).strong := rfl
theorem delta_def : (𝓡).delta = (𝓡).Q - 1 := rfl
theorem b_def : (𝓡).b = x 8 - (𝓡).R + x 7 * (4 * (𝓡).AU) := rfl
theorem V_def : (𝓡).V = (𝓡).Df * (𝓡).b - x 8 := rfl
theorem Cy_def : (𝓡).Cy = (𝓡).V * ((𝓡).Q * (𝓡).V) - 1 := rfl
theorem K_def : (𝓡).K = 2 + (𝓡).X * (x 8 * 3 - (𝓡).X * 2) := rfl
theorem M_def : (𝓡).M = 2 * (𝓡).q3 := rfl
theorem Dc_def : (𝓡).Dc = (𝓡).H * (𝓡).M := rfl
theorem M2_def : (𝓡).M2 = (𝓡).M * (𝓡).M := rfl
theorem M4_def : (𝓡).M4 = (𝓡).M2 * (𝓡).M2 := rfl
theorem Dc2_def : (𝓡).Dc2 = (𝓡).Dc * (𝓡).Dc := rfl
theorem Dc3_def : (𝓡).Dc3 = (𝓡).Dc * (𝓡).Dc2 := rfl
theorem S_def : (𝓡).S = (𝓡).M4 * ((𝓡).Dc * (x 4 * x 10)) := rfl
theorem S2_def : (𝓡).S2 = (𝓡).S * (𝓡).S := rfl
theorem zc_def : (𝓡).zc = x 7 * (𝓡).Dc + (𝓡).K * (𝓡).M + (𝓡).H * ((𝓡).Y - (𝓡).q3) := rfl
theorem zc2_def : (𝓡).zc2 = (𝓡).zc * (𝓡).zc := rfl
theorem Ac_def : (𝓡).Ac = ((𝓡).zc2 + 3 * (𝓡).Dc2) * ((𝓡).zc * (𝓡).zc2 - (𝓡).Dc3 * 19) := rfl
theorem c4_def : (𝓡).c4 = (𝓡).c2 * (𝓡).c2 := rfl
theorem rc4_def : (𝓡).rc4 = x 4 * (𝓡).c4 := rfl
theorem U2_def : (𝓡).U2 = (𝓡).U * (𝓡).U := rfl
theorem UT_def : (𝓡).UT = x 7 * (𝓡).U2 := rfl
theorem cm2_def : (𝓡).cm2 = (𝓡).c2 - 2 := rfl
theorem gamma_def : (𝓡).gamma = 4 + (𝓡).Delta * 8 := rfl
theorem lam_def : (𝓡).lam = 4 * ((𝓡).U * (𝓡).gamma - (𝓡).rc4) := rfl
/-- The center slot. -/
theorem Psi_reg : (𝓡).Psi = ψ := rfl
theorem Z_def : (𝓡).Z = (𝓡).S * (x 9 + (𝓡).Psi) - (𝓡).Ac := rfl
theorem Z2_def : (𝓡).Z2 = (𝓡).Z * (𝓡).Z := rfl
theorem pa_def : (𝓡).pa = (𝓡).delta * (𝓡).Z2 := rfl
theorem pb_def : (𝓡).pb = (𝓡).P * ((𝓡).delta * (𝓡).S2) := rfl
theorem pc_def : (𝓡).pc = (𝓡).Cy * ((𝓡).Df * ((𝓡).B * ((𝓡).S2 * wt))) := rfl
theorem inner_def : (𝓡).inner = (𝓡).pa + (𝓡).pb - (𝓡).pc := rfl

/-! ### Closed forms in the notation of `PROOF.md` §1 -/

theorem q_eq : (𝓡).q = p 0 * (6 * x 0 + 1) + 1 := by
  rw [q_def, qm_def, J_def]; ring

theorem qm_eq : (𝓡).qm = (𝓡).q - 1 := by rw [q_def]; ring

theorem W_eq : (𝓡).W = 12 * x 6 + 4 := by rw [W_def]; ring

theorem q2_eq : (𝓡).q2 = (𝓡).q ^ 2 := by rw [q2_def]; ring

theorem q3_eq : (𝓡).q3 = (𝓡).q ^ 3 := by rw [q3_def, q2_def]; ring

theorem E_eq : (𝓡).E = (𝓡).X * (𝓡).Y := by rw [E_def]; ring

theorem ell_eq : (𝓡).ell = (𝓡).X * (𝓡).Y ^ 2 := by rw [ell_def, E_def]; ring

theorem a_eq : (𝓡).a = (𝓡).X * (𝓡).Y + (𝓡).Y := by rw [a_def, E_def]; ring

theorem A_eq : (𝓡).A = (𝓡).a + 2 := A_def p x κ ω Λ ψ wt

theorem H_eq : (𝓡).H = 4 * (𝓡).a + 3 := H_def p x κ ω Λ ψ wt

theorem Delta_eq : (𝓡).Delta = (𝓡).A ^ 2 - 1 := by
  rw [Delta_def, A_def, H_def]; ring

theorem F_eq : (𝓡).F = (p 1 + (𝓡).W) * x 1 - x 2 * ((𝓡).q - 1) := by
  rw [F_def, qm_eq]; ring

theorem R_eq : (𝓡).R = ((𝓡).q * ((𝓡).q - (𝓡).F) - x 1) * ((𝓡).q ^ 2 - 1) +
    (p 2 + (𝓡).q * p 3) * (𝓡).J := by
  rw [R_def, q2_def]; ring

theorem eta_eq : (𝓡).eta = x 8 - (𝓡).Y * (𝓡).k := by rw [eta_def, Yk_def]

theorem Derr_eq : (𝓡).Derr = (p 4 * (𝓡).F - (𝓡).q) ^ 2 + (p 5 * x 1 - (𝓡).q) ^ 2 := by
  rw [Derr_def]; ring

/-- The budget before the slot law: `Budget = Y² · B0 − q² · kq2²`. -/
theorem Budget_eq_kq : (𝓡).Budget = (𝓡).Y ^ 2 * B0 (𝓡) - (𝓡).q ^ 2 * (𝓡).kq2 ^ 2 := by
  rw [Budget_def, Yeta_def, Yk_def, q2_def, B0]; ring

theorem Dguard_eq : (𝓡).Dguard = (𝓡).Budget - 4 := Dguard_def p x κ ω Λ ψ wt

/-- `P = Dt · Dg` with the guard `Dg = 1 + D Dt s²`, `D = Budget − 4`. -/
theorem P_eq : (𝓡).P = (𝓡).Dt * (1 + (𝓡).Dguard * (𝓡).Dt * x 10 ^ 2) := by
  rw [P_def, Pg_def]; ring

theorem Dm_eq : (𝓡).Dm = 1 + (𝓡).Delta * x 8 ^ 2 := by rw [Dm_def, c2_def]; ring

/-- The linear cofactor `B = r · A · Dm`. -/
theorem B_eq : (𝓡).B = x 4 * (𝓡).A * (𝓡).Dm := by rw [B_def, rDm_def]; ring

theorem U_eq : (𝓡).U = x 4 * x 8 ^ 2 * (𝓡).Dm := by rw [U_def, rDm_def, c2_def]; ring

/-- `A·U = c² · B`. -/
theorem AU_eq : (𝓡).AU = x 8 ^ 2 * (𝓡).B := by
  rw [AU_def, U_def, B_def, c2_def]; ring

/-- `strong = Δ · I²` with `I² = c⁴ · B`. -/
theorem strong_eq : (𝓡).strong = (𝓡).Delta * (x 8 ^ 4 * (𝓡).B) := by
  rw [strong_def, AU_eq, c2_def]; ring

theorem Df_eq : (𝓡).Df = 1 + (𝓡).Delta * (x 8 ^ 4 * (𝓡).B) := by
  rw [Df_def, strong_eq]

theorem Q_eq : (𝓡).Q = (𝓡).Delta ^ 2 * (x 8 ^ 4 * (𝓡).B) := by
  rw [Q_def, strong_eq]; ring

theorem delta_eq : (𝓡).delta = (𝓡).Q - 1 := delta_def p x κ ω Λ ψ wt

theorem V_eq : (𝓡).V = (𝓡).Df * (x 8 - (𝓡).R + 4 * (𝓡).A * (𝓡).U * x 7) - x 8 := by
  rw [V_def, b_def, AU_def]; ring

theorem Cy_eq : (𝓡).Cy = (𝓡).Q * (𝓡).V ^ 2 - 1 := by rw [Cy_def]; ring

theorem K_eq : (𝓡).K = (𝓡).X * (3 * x 8 - 2 * (𝓡).X) + 2 := by rw [K_def]; ring

theorem M_eq : (𝓡).M = 2 * (𝓡).q ^ 3 := by rw [M_def, q3_eq]

theorem Dc_eq : (𝓡).Dc = (𝓡).H * (𝓡).M := Dc_def p x κ ω Λ ψ wt

/-- `S = s · r · H · M⁵`. -/
theorem S_eq : (𝓡).S = x 10 * x 4 * (𝓡).H * (𝓡).M ^ 5 := by
  rw [S_def, M4_def, M2_def, Dc_def]; ring

/-- `S = (M⁴ · s · r) · Dc`: the carrier modulus divides `S`. -/
theorem S_eq_Dc : (𝓡).S = (𝓡).M ^ 4 * (x 10 * x 4) * (𝓡).Dc := by
  rw [S_def, M4_def, M2_def]; ring

/-- `zc = Dc · T + M · K + H · (Y − q³)`. -/
theorem zc_eq : (𝓡).zc = (𝓡).Dc * x 7 + (𝓡).M * (𝓡).K + (𝓡).H * ((𝓡).Y - (𝓡).q ^ 3) := by
  rw [zc_def, q3_eq]; ring

theorem Ac_eq : (𝓡).Ac = ((𝓡).zc ^ 2 + 3 * (𝓡).Dc ^ 2) * ((𝓡).zc ^ 3 - 19 * (𝓡).Dc ^ 3) := by
  rw [Ac_def, zc2_def, Dc2_def, Dc3_def, Dc2_def]; ring

theorem Z_eq : (𝓡).Z = (𝓡).S * (x 9 + (𝓡).Psi) - (𝓡).Ac := Z_def p x κ ω Λ ψ wt

theorem pa_eq : (𝓡).pa = (𝓡).delta * (𝓡).Z ^ 2 := by rw [pa_def, Z2_def]; ring

theorem pb_eq : (𝓡).pb = (𝓡).delta * (𝓡).S ^ 2 * (𝓡).P := by rw [pb_def, S2_def]; ring

theorem pc_eq : (𝓡).pc = wt * (𝓡).S ^ 2 * (𝓡).B * (𝓡).Df * (𝓡).Cy := by
  rw [pc_def, S2_def]; ring

/-- **The two-radical norm**: the output is `(pa + pb − pc)² − 4·pa·pb`. -/
theorem value_eq : valueK p x κ ω Λ ψ wt =
    ((𝓡).pa + (𝓡).pb - (𝓡).pc) ^ 2 - 4 * (𝓡).pa * (𝓡).pb := by
  rw [value_def, inner_def]; ring

/-- The zero set in register form. -/
theorem value_eq_product : valueK p x κ ω Λ ψ wt =
    ((𝓡).delta * (𝓡).Z ^ 2 + (𝓡).delta * (𝓡).S ^ 2 * (𝓡).P -
        wt * (𝓡).S ^ 2 * (𝓡).B * (𝓡).Df * (𝓡).Cy) ^ 2 -
      4 * ((𝓡).delta * (𝓡).Z ^ 2) * ((𝓡).delta * (𝓡).S ^ 2 * (𝓡).P) := by
  rw [value_eq, pa_eq, pb_eq, pc_eq]

/-- **Completeness identity**: if `Z = S (α + β)`, `P = β²` and `wt B Df Cy = δ α²`, the
output vanishes (one conjugate factor of the norm is zero). -/
theorem value_eq_zero_of (α β : 𝔸) (hZ : (𝓡).Z = (𝓡).S * (α + β)) (hP : (𝓡).P = β ^ 2)
    (hC : wt * (𝓡).B * (𝓡).Df * (𝓡).Cy = (𝓡).delta * α ^ 2) : valueK p x κ ω Λ ψ wt = 0 := by
  rw [value_eq_product, hZ, hP]
  have h : wt * (𝓡).S ^ 2 * (𝓡).B * (𝓡).Df * (𝓡).Cy = (𝓡).S ^ 2 * ((𝓡).delta * α ^ 2) := by
    rw [← hC]; ring
  rw [h]; ring

/-! ### The front registers do not read the slots -/

section Slot
variable (κ' ω' Λ' ψ' wt' : 𝔸)
local notation "𝓡'" => regsK p x κ' ω' Λ' ψ' wt'

theorem J_slot : (𝓡).J = (𝓡').J := rfl
theorem q_slot : (𝓡).q = (𝓡').q := rfl
theorem q2_slot : (𝓡).q2 = (𝓡').q2 := rfl
theorem q3_slot : (𝓡).q3 = (𝓡').q3 := rfl
theorem W_slot : (𝓡).W = (𝓡').W := rfl
theorem X_slot : (𝓡).X = (𝓡').X := rfl
theorem Y_slot : (𝓡).Y = (𝓡').Y := rfl
theorem E_slot : (𝓡).E = (𝓡').E := rfl
theorem ell_slot : (𝓡).ell = (𝓡').ell := rfl
theorem a_slot : (𝓡).a = (𝓡').a := rfl
theorem H_slot : (𝓡).H = (𝓡').H := rfl
theorem Delta_slot : (𝓡).Delta = (𝓡').Delta := rfl
theorem A_slot : (𝓡).A = (𝓡').A := rfl
theorem F_slot : (𝓡).F = (𝓡').F := rfl
theorem R_slot : (𝓡).R = (𝓡').R := rfl
theorem Derr_slot : (𝓡).Derr = (𝓡').Derr := rfl
theorem c2_slot : (𝓡).c2 = (𝓡').c2 := rfl
theorem U_slot : (𝓡).U = (𝓡').U := rfl
theorem V_slot : (𝓡).V = (𝓡').V := rfl
theorem lam_slot : (𝓡).lam = (𝓡').lam := rfl
theorem UT_slot : (𝓡).UT = (𝓡').UT := rfl
theorem rc4_slot : (𝓡).rc4 = (𝓡').rc4 := rfl
theorem cm2_slot : (𝓡).cm2 = (𝓡').cm2 := rfl
theorem gamma_slot : (𝓡).gamma = (𝓡').gamma := rfl

end Slot

/-! ### The slot law -/

/-- What soundness uses about the slots `k`, `kq2`, `L`: `kq2 = k · q^(2+e)` and
`L = X · Y² · k`. The budget power is `q^(6+2e)`. -/
structure SlotLaw (e : ℕ) : Prop where
  kq_eq : ω = κ * (regsK p x 0 0 0 0 0).q ^ (2 + e)
  L_eq : Λ = (regsK p x 0 0 0 0 0).X * (regsK p x 0 0 0 0 0).Y ^ 2 * κ

variable {p x κ ω Λ} {e : ℕ}

theorem SlotLaw.kq2_eq (h : SlotLaw p x κ ω Λ e) : (𝓡).kq2 = (𝓡).k * (𝓡).q ^ (2 + e) :=
  h.kq_eq

theorem SlotLaw.L_reg_eq (h : SlotLaw p x κ ω Λ e) : (𝓡).L = (𝓡).X * (𝓡).Y ^ 2 * (𝓡).k :=
  h.L_eq

/-- `Budget = Y² · B0 − k² · q^(6+2e)`. -/
theorem SlotLaw.Budget_eq (h : SlotLaw p x κ ω Λ e) :
    (𝓡).Budget = (𝓡).Y ^ 2 * B0 (𝓡) - (𝓡).k ^ 2 * (𝓡).q ^ (6 + 2 * e) := by
  rw [Budget_eq_kq, h.kq2_eq ψ wt]
  have hp : (𝓡).q ^ (6 + 2 * e) = (𝓡).q ^ 2 * ((𝓡).q ^ (2 + e)) ^ 2 := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  rw [hp]; ring

/-- `Dt = 1 + ℓ (ℓ + 1) k²` with `ℓ = X Y²`. -/
theorem SlotLaw.Dt_eq (h : SlotLaw p x κ ω Λ e) :
    (𝓡).Dt = 1 + ((𝓡).X * (𝓡).Y ^ 2) * ((𝓡).X * (𝓡).Y ^ 2 + 1) * (𝓡).k ^ 2 := by
  rw [Dt_def, h.L_reg_eq ψ wt]; ring

end Defs

/-! ### The two forms satisfy the slot law -/

section Forms
variable (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸)

theorem k298_def : (regs298 p x).k = 1 + (regs298 p x).R + x 3 * (regs298 p x).ell := rfl
theorem kq298_def : (regs298 p x).kq2 = (regs298 p x).q2 * (regs298 p x).k := rfl
theorem L298_def : (regs298 p x).L = (regs298 p x).ell * (regs298 p x).k := rfl

/-- The 298/146 index: `k = R + 1 + h · X Y²`. -/
theorem k298_eq : (regs298 p x).k =
    (regs298 p x).R + 1 + x 3 * ((regs298 p x).X * (regs298 p x).Y ^ 2) := by
  rw [k298_def, ell_eq]; ring

theorem k300_def : (regs300 p x).k = 1 + (regs300 p x).R + x 3 * (regs300 p x).E := rfl
theorem kq300_def : (regs300 p x).kq2 = (regs300 p x).k * (regs300 p x).q3 := rfl
theorem L300_def : (regs300 p x).L = (regs300 p x).E * (regs300 p x).Yk := rfl

/-- The 300/144 index: `k = R + 1 + h · X Y`. -/
theorem k300_eq : (regs300 p x).k =
    (regs300 p x).R + 1 + x 3 * ((regs300 p x).X * (regs300 p x).Y) := by
  rw [k300_def, E_eq]; ring

/-- 298/146 satisfies the slot law with budget power `q⁶`. -/
theorem slotLaw298 : SlotLaw p x (k298 p x) (kq298 p x) (L298 p x) 0 where
  kq_eq := by
    rw [kq298, q2_eq]; ring
  L_eq := by
    rw [L298, ell_eq]

/-- 300/144 satisfies the slot law with budget power `q⁸`. -/
theorem slotLaw300 : SlotLaw p x (k300 p x) (kq300 p x) (L300 p x) 1 where
  kq_eq := by
    rw [kq300, q3_eq]
  L_eq := by
    rw [L300, E_eq]; ring

/-- The 298/146 center in the notation of `PROOF.md`:
`Ψ = λ V + U² T (r c⁴ (γ (c² − 2) − c²) + 64 A Δ)`. -/
theorem psi298_eq : (regs298 p x).Psi = (regs298 p x).lam * (regs298 p x).V +
    (regs298 p x).U ^ 2 * x 7 * (x 4 * x 8 ^ 4 * ((regs298 p x).gamma * (x 8 ^ 2 - 2) - x 8 ^ 2) +
      64 * (regs298 p x).A * (regs298 p x).Delta) := by
  have h0 : (regs298 p x).Psi = (regsK p x 0 0 0 0 0).V * (regsK p x 0 0 0 0 0).lam +
      (regsK p x 0 0 0 0 0).UT * ((regsK p x 0 0 0 0 0).rc4 *
        ((regsK p x 0 0 0 0 0).cm2 * (regsK p x 0 0 0 0 0).gamma - (regsK p x 0 0 0 0 0).c2) +
        (regsK p x 0 0 0 0 0).Delta * (regsK p x 0 0 0 0 0).A * 64) := rfl
  rw [h0, UT_def, U2_def, rc4_def, c4_def, cm2_def, c2_def]
  show _ = (regsK p x 0 0 0 0 0).lam * (regsK p x 0 0 0 0 0).V +
    (regsK p x 0 0 0 0 0).U ^ 2 * x 7 * (x 4 * x 8 ^ 4 *
      ((regsK p x 0 0 0 0 0).gamma * (x 8 ^ 2 - 2) - x 8 ^ 2) +
      64 * (regsK p x 0 0 0 0 0).A * (regsK p x 0 0 0 0 0).Delta)
  ring

/-- The 300/144 center in the notation of `PROOF.md`:
`Ψ = λ V + U² T (γ − 1) (r c⁴ (c² − 2) + 8 A)`. -/
theorem psi300_eq : (regs300 p x).Psi = (regs300 p x).lam * (regs300 p x).V +
    (regs300 p x).U ^ 2 * x 7 * (((regs300 p x).gamma - 1) *
      (x 4 * x 8 ^ 4 * (x 8 ^ 2 - 2) + 8 * (regs300 p x).A)) := by
  have h0 : (regs300 p x).Psi = (regsK p x 0 0 0 0 0).V * (regsK p x 0 0 0 0 0).lam +
      (regsK p x 0 0 0 0 0).UT * (((regsK p x 0 0 0 0 0).rc4 * (regsK p x 0 0 0 0 0).cm2 +
        (regsK p x 0 0 0 0 0).A * 8) * ((regsK p x 0 0 0 0 0).gamma - 1)) := rfl
  rw [h0, UT_def, U2_def, rc4_def, c4_def, cm2_def, c2_def]
  show _ = (regsK p x 0 0 0 0 0).lam * (regsK p x 0 0 0 0 0).V +
    (regsK p x 0 0 0 0 0).U ^ 2 * x 7 * (((regsK p x 0 0 0 0 0).gamma - 1) *
      (x 4 * x 8 ^ 4 * (x 8 ^ 2 - 2) + 8 * (regsK p x 0 0 0 0 0).A))
  ring

/-! ### Neither circuit reads `x 3` except through the `k` slot -/

theorem regsK_update (κ ω Λ ψ wt t : 𝔸) :
    regsK p (Function.update x 3 t) κ ω Λ ψ wt = regsK p x κ ω Λ ψ wt := rfl

theorem valueK_update (κ ω Λ ψ wt t : 𝔸) :
    valueK p (Function.update x 3 t) κ ω Λ ψ wt = valueK p x κ ω Λ ψ wt := by
  unfold valueK; rw [regsK_update]

end Forms
end Generic

#print axioms DiophantineConsistency.LCValue.value_eq
#print axioms DiophantineConsistency.LCValue.value_eq_product
#print axioms DiophantineConsistency.LCValue.value_eq_zero_of
#print axioms DiophantineConsistency.LCValue.P_eq
#print axioms DiophantineConsistency.LCValue.SlotLaw.Budget_eq
#print axioms DiophantineConsistency.LCValue.SlotLaw.Dt_eq
#print axioms DiophantineConsistency.LCValue.slotLaw298
#print axioms DiophantineConsistency.LCValue.slotLaw300
#print axioms DiophantineConsistency.LCValue.k298_eq
#print axioms DiophantineConsistency.LCValue.k300_eq
#print axioms DiophantineConsistency.LCValue.psi298_eq
#print axioms DiophantineConsistency.LCValue.psi300_eq
#print axioms DiophantineConsistency.LCValue.regsK_update

end DiophantineConsistency.LCValue
