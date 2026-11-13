import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! # The ten-positive 75-operation, degree-402 trace equation

Package 163 (`con-zfc-diophantine-forms/163-trace-radical`), compact chart
`q3`, weight `L = V²`: the circuit `equations/trace75_degree402.json`.
Its ten unknowns, in order, are `J, F, alpha, i, T, w, s, n, eta, zeta`,
all strictly positive. The four fixed ports are `beta, K0, MC, MF`.

`value75` evaluates the circuit in any commutative ring. Its definitions
follow the 75 circuit rows: the circuit's `Dtau` is `E`, its `Df` is `F0`,
its `trace_f` is `f`, its `P1mu2` is `hD`, and its `Dg` is `E * F0`
(written `G` in the paper; here `Gn`, since the circuit's `G` is the rank
part `h(q - F) + alpha`).

The section-3 identities of the paper are ring identities and are proved
here for every commutative ring. This module imports neither Foundation
nor Mathlib's matrices, so model-side and polynomial-side modules can both
use it. `regs` needs only `+`, `-`, `*` and the numerals 1–4, so the literal
syntax in `TenPositiveTrace75Syntax` is `regs` itself, read in `Expr`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.TenPositiveTrace75

section Generic
variable {R : Type*} [Add R] [Sub R] [Mul R] [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4]

/-- The named registers of the circuit at ports `p` and unknowns `v`. -/
structure Regs (R : Type*) where
  h : R
  q : R
  C : R
  X : R
  Y : R
  k : R
  c : R
  Am1 : R
  A : R
  H : R
  Delta : R
  E : R
  rank : R
  e : R
  B : R
  U : R
  a : R
  F0 : R
  f : R
  Q : R
  b : R
  V : R
  K : R
  D : R
  Z : R
  M : R
  Gn : R

/-- The registers, row by row as in the circuit. -/
def regs (p : Fin 4 → R) (v : Fin 10 → R) : Regs R :=
  let J := v 0
  let F := v 1
  let alpha := v 2
  let i := v 3
  let T := v 4
  let w := v 5
  let s := v 6
  let n := v 7
  let eta := v 8
  let zeta := v 9
  let h := p 0 * J
  let q := h + 1
  let Y := q * q * q * s
  let C := q - F - alpha
  let X := w * q
  let k := eta + zeta
  let c := k * Y + eta
  let XY := X * Y
  let Am1 := XY + Y
  let H := 4 * Am1 - 1
  let E := XY * (k * Y) * (XY * (k * Y) + k) + 1
  let rank := (h * (q - F) + alpha) * (q * q - 1) + (p 2 + q * p 3) * J
  let e := k - rank - 1
  let B := (p 1 + w) * C - F
  let U := i * (c * c)
  let Delta := Am1 * (Am1 + 2)
  let a := Delta * (U * E) * U
  let F0 := a + 1
  let f := a + F0
  let Q := Delta * (4 * (a * F0))
  let b := c * T - rank
  let V := f * b - c
  let K := X * (3 * c - 2 * X) + 2
  let D := XY
  let Z := h * XY * (H * (n - V * V * B) + K) - H * (XY * B + h * e)
  let M := h * XY * H
  { h, q, C, X, Y, k, c, Am1, A := Am1 + 1, H, Delta, E, rank, e, B, U, a, F0, f, Q,
    b, V, K, D, Z, M, Gn := E * F0 }

/-- The value of the 75-operation circuit (its output row `N`). -/
def value75 (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs p v
  r.Q * (r.Z * r.Z - r.M * r.M * r.Gn * (r.V * r.V)) +
    (r.M * r.M * r.Gn - r.Z * r.Z)


/-! ### Register equations

Each register is stated in terms of the previous ones. These hold by `rfl`,
so later proofs can run `ring` with the registers as atoms, instead of
expanding them into the ten unknowns (which exhausts memory). -/

section Defs
variable (p : Fin 4 → R) (v : Fin 10 → R)
local notation "𝓡" => regs p v

theorem h_def : (𝓡).h = p 0 * v 0 := rfl
theorem q_def : (𝓡).q = (𝓡).h + 1 := rfl
theorem Y_def : (𝓡).Y = (𝓡).q * (𝓡).q * (𝓡).q * v 6 := rfl
theorem C_def : (𝓡).C = (𝓡).q - v 1 - v 2 := rfl
theorem X_def : (𝓡).X = v 5 * (𝓡).q := rfl
theorem k_def : (𝓡).k = v 8 + v 9 := rfl
theorem c_def : (𝓡).c = (𝓡).k * (𝓡).Y + v 8 := rfl
theorem Am1_def : (𝓡).Am1 = (𝓡).X * (𝓡).Y + (𝓡).Y := rfl
theorem A_def : (𝓡).A = (𝓡).Am1 + 1 := rfl
theorem H_def : (𝓡).H = 4 * (𝓡).Am1 - 1 := rfl
theorem E_def : (𝓡).E = (𝓡).X * (𝓡).Y * ((𝓡).k * (𝓡).Y) *
    ((𝓡).X * (𝓡).Y * ((𝓡).k * (𝓡).Y) + (𝓡).k) + 1 := rfl
theorem rank_def : (𝓡).rank = ((𝓡).h * ((𝓡).q - v 1) + v 2) * ((𝓡).q * (𝓡).q - 1) +
    (p 2 + (𝓡).q * p 3) * v 0 := rfl
theorem e_def : (𝓡).e = (𝓡).k - (𝓡).rank - 1 := rfl
theorem B_def : (𝓡).B = (p 1 + v 5) * (𝓡).C - v 1 := rfl
theorem U_def : (𝓡).U = v 3 * ((𝓡).c * (𝓡).c) := rfl
theorem Delta_def : (𝓡).Delta = (𝓡).Am1 * ((𝓡).Am1 + 2) := rfl
theorem a_def : (𝓡).a = (𝓡).Delta * ((𝓡).U * (𝓡).E) * (𝓡).U := rfl
theorem F0_def : (𝓡).F0 = (𝓡).a + 1 := rfl
theorem f_def : (𝓡).f = (𝓡).a + (𝓡).F0 := rfl
theorem Q_def : (𝓡).Q = (𝓡).Delta * (4 * ((𝓡).a * (𝓡).F0)) := rfl
theorem b_def : (𝓡).b = (𝓡).c * v 4 - (𝓡).rank := rfl
theorem V_def : (𝓡).V = (𝓡).f * (𝓡).b - (𝓡).c := rfl
theorem K_def : (𝓡).K = (𝓡).X * (3 * (𝓡).c - 2 * (𝓡).X) + 2 := rfl
theorem D_def : (𝓡).D = (𝓡).X * (𝓡).Y := rfl
theorem Z_def : (𝓡).Z = (𝓡).h * ((𝓡).X * (𝓡).Y) *
    ((𝓡).H * (v 7 - (𝓡).V * (𝓡).V * (𝓡).B) + (𝓡).K) -
    (𝓡).H * ((𝓡).X * (𝓡).Y * (𝓡).B + (𝓡).h * (𝓡).e) := rfl
theorem M_def : (𝓡).M = (𝓡).h * ((𝓡).X * (𝓡).Y) * (𝓡).H := rfl
theorem Gn_def : (𝓡).Gn = (𝓡).E * (𝓡).F0 := rfl
theorem value75_def : value75 p v = (𝓡).Q * ((𝓡).Z * (𝓡).Z - (𝓡).M * (𝓡).M * (𝓡).Gn * ((𝓡).V * (𝓡).V)) +
    ((𝓡).M * (𝓡).M * (𝓡).Gn - (𝓡).Z * (𝓡).Z) := rfl

end Defs

end Generic

variable {R : Type*} [CommRing R]

/-! ### Ring identities of the paper's Sections 2 and 3 -/

section Identities
variable (p : Fin 4 → R) (v : Fin 10 → R)
local notation "𝓡" => regs p v

/-- (2.2): `P = (Q - 1) Z² - M² G (Q V² - 1)`. -/
theorem value75_eq :
    value75 p v = ((𝓡).Q - 1) * (𝓡).Z ^ 2 - (𝓡).M ^ 2 * (𝓡).Gn * ((𝓡).Q * (𝓡).V ^ 2 - 1) := by
  rw [value75_def]
  ring

/-- `Delta = A² - 1`. -/
theorem delta_eq : (𝓡).Delta = (𝓡).A ^ 2 - 1 := by
  rw [Delta_def, A_def]; ring

/-- `H = 4A - 5`. -/
theorem H_eq : (𝓡).H = 4 * (𝓡).A - 5 := by
  rw [H_def, A_def]; ring

/-- `f = 1 + 2a`. -/
theorem f_eq : (𝓡).f = 1 + 2 * (𝓡).a := by
  rw [f_def, F0_def]; ring

/-- (3.1), first identity: `f² = 1 + 4 a F0`. -/
theorem f_sq : (𝓡).f ^ 2 = 1 + 4 * (𝓡).a * (𝓡).F0 := by
  rw [f_def, F0_def]; ring

/-- `a = Delta U² E`. -/
theorem a_eq : (𝓡).a = (𝓡).Delta * (𝓡).U ^ 2 * (𝓡).E := by
  rw [a_def]; ring

/-- (3.1), second identity: `Q = Delta (f² - 1)`. -/
theorem Q_eq : (𝓡).Q = (𝓡).Delta * ((𝓡).f ^ 2 - 1) := by
  rw [Q_def, f_sq]; ring

/-- `Q = 4 Delta² U² G`. -/
theorem Q_eq' : (𝓡).Q = 4 * (𝓡).Delta ^ 2 * (𝓡).U ^ 2 * (𝓡).Gn := by
  have hq := Q_def p v
  have h3 := a_eq p v
  have h2 := Gn_def p v
  linear_combination hq + 4 * (𝓡).Delta * (𝓡).F0 * h3 - 4 * (𝓡).Delta ^ 2 * (𝓡).U ^ 2 * h2

/-- (3.1), third identity: `f - 1 = 2 Delta i² c⁴ E`. -/
theorem f_sub_one : (𝓡).f - 1 = 2 * (𝓡).Delta * v 3 ^ 2 * (𝓡).c ^ 4 * (𝓡).E := by
  rw [f_eq, a_def, U_def]; ring

/-- `f = 1 + c d` with `d = 2 Delta i² c³ E`; in particular `f ≡ 1 (mod c)`. -/
theorem f_one_mod_c : (𝓡).f = 1 + (𝓡).c * (2 * (𝓡).Delta * v 3 ^ 2 * (𝓡).c ^ 3 * (𝓡).E) := by
  have := f_sub_one p v
  linear_combination this

/-- `E = 1 + v' (v' + 1) k²` with `v' = X Y²`. -/
theorem E_eq : (𝓡).E = 1 + (𝓡).X * (𝓡).Y ^ 2 * ((𝓡).X * (𝓡).Y ^ 2 + 1) * (𝓡).k ^ 2 := by
  rw [E_def]; ring

/-- With `I = 2 U g` and `G = g²`: `f² - Delta I² = 1`. -/
theorem strong_norm (g : R) (hg : (𝓡).Gn = g ^ 2) :
    (𝓡).f ^ 2 - (𝓡).Delta * (2 * (𝓡).U * g) ^ 2 = 1 := by
  have h1 := f_sq p v
  have h3 := a_eq p v
  have h2 := Gn_def p v
  linear_combination h1 + 4 * (𝓡).F0 * h3 - 4 * (𝓡).Delta * (𝓡).U ^ 2 * h2 +
    4 * (𝓡).Delta * (𝓡).U ^ 2 * hg

/-- With `G = g²`: `Q = (Delta I)²`, `I = 2 U g`. -/
theorem Q_strong (g : R) (hg : (𝓡).Gn = g ^ 2) :
    (𝓡).Q = ((𝓡).Delta * (2 * (𝓡).U * g)) ^ 2 := by
  rw [Q_eq', hg]; ring

/-- (6.1): `V = f (c T - R) - c`. -/
theorem V_eq : (𝓡).V = (𝓡).f * ((𝓡).c * v 4 - (𝓡).rank) - (𝓡).c := by
  rw [V_def, b_def]

/-- (5.1): `R = (h C + q alpha)(q² - 1) + (MC + q MF) J`. -/
theorem rank_eq_C : (𝓡).rank = ((𝓡).h * (𝓡).C + (𝓡).q * v 2) * ((𝓡).q ^ 2 - 1) +
    (p 2 + (𝓡).q * p 3) * v 0 := by
  rw [rank_def, C_def, q_def]; ring

end Identities

end DiophantineConsistency.TenPositiveTrace75
