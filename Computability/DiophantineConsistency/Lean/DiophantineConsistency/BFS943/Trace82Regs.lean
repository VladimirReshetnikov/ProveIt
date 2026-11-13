import DiophantineConsistency.BFS943.Trace79Regs

/-! # The ten-positive 82-operation, degree-240 free-plain equation

Package 172 (`con-zfc-diophantine-forms/172-pooled-powers-round21`), mode
`free_plain`: the circuit `scalar/positive10/positive10_degree240_ops82.json`.
Ten positive unknowns `J, F, α, i, T, w, s, n, η, ζ`, the four direct-BFS943
ports `β, K0, MC, MF`, transport weight `L = bV`. Relative to the 80/258
circuit (chart `q1`) it changes two things:

* the strip is free: `c = k s + η` (row `kY = k s`), while the Pell base keeps
  the scale `λ = q`: `A - 1 = q s (X + 1)` (rows `qY = q s`,
  `XY = X qY`, `Am1 = XY + qY`), and `v = X (q s)²` (row `qkY = q kY`,
  `V0k = XY qkY`);
* the denominator is `D = q⁷` (rows `q6 = q4 q2`, `D = q6 q`).

So the registers are those of `TenPositiveTrace79.regsAt` at
`X = q (q w)`, `Y = q s` (the scaled ordinate `λ s`, which is the register `Y`
here) and `W = q w`, except that `c` is `k s + η` instead of `k Y + η`.
`regsAtC` is `regsAt` with `c` as a parameter (`regsAt_eq`, `rfl`); `regs` is
its 82 instance with the 82 `D`, `Z`, `M`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.TenPositiveTrace82
open DiophantineConsistency.TenPositiveTrace75 (Regs)
open DiophantineConsistency.TenPositiveTrace79 (regsAt)

section Generic
variable {R : Type*} [Add R] [Sub R] [Mul R] [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4]

/-- `TenPositiveTrace79.regsAt` with the strip value `c` as a parameter. -/
def regsAtC (p : Fin 4 → R) (v : Fin 10 → R) (X Y W c : R) : Regs R :=
  let J := v 0
  let F := v 1
  let alpha := v 2
  let i := v 3
  let T := v 4
  let n := v 7
  let eta := v 8
  let zeta := v 9
  let h := p 0 * J
  let q := h + 1
  let C := q - F - alpha
  let k := eta + zeta
  let XY := X * Y
  let Am1 := XY + Y
  let H := 4 * Am1 - 1
  let E := XY * (k * Y) * (XY * (k * Y) + k) + 1
  let rank := (h * (q - F) + alpha) * (q * q - 1) + (p 2 + q * p 3) * J
  let e := k - rank - 1
  let B := (p 1 + W) * C - F
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

theorem regsAt_eq (p : Fin 4 → R) (v : Fin 10 → R) (X Y W : R) :
    regsAt p v X Y W = regsAtC p v X Y W ((v 8 + v 9) * Y + v 8) := rfl

/-- The 82 registers: `X = q (q w)`, `Y = q s`, `W = q w`, `c = k s + η`,
`D = q⁷`, carrier `Z = h D [H (n - b V B) + K] - H [D B + h (e - q⁴ s)]`,
multiplier `M = h D H`. -/
def regs (p : Fin 4 → R) (v : Fin 10 → R) : Regs R :=
  let r := regsAtC p v ((p 0 * v 0 + 1) * ((p 0 * v 0 + 1) * v 5)) ((p 0 * v 0 + 1) * v 6)
    ((p 0 * v 0 + 1) * v 5) ((v 8 + v 9) * v 6 + v 8)
  let D := r.q * r.q * (r.q * r.q) * (r.q * r.q) * r.q
  let L := r.b * r.V
  { r with D := D,
           Z := r.h * D * (r.H * (v 7 - L * r.B) + r.K) -
             r.H * (D * r.B + r.h * (r.e - r.q * r.q * (r.q * r.q) * v 6)),
           M := r.h * D * r.H }

/-- The value of the 82-operation circuit (its output row `N`). -/
def value82 (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs p v
  r.Q * (r.Z * r.Z - r.M * r.M * r.Gn * (r.V * r.V)) +
    (r.M * r.M * r.Gn - r.Z * r.Z)

theorem value82_norm (p : Fin 4 → R) (v : Fin 10 → R) :
    value82 p v = TenPositiveTrace76.normValue (regs p v) (regs p v).Z := rfl

section Defs
variable (p : Fin 4 → R) (v : Fin 10 → R)
local notation "𝓡" => regs p v

theorem h_def : (𝓡).h = p 0 * v 0 := rfl
theorem q_def : (𝓡).q = (𝓡).h + 1 := rfl
theorem Y_def : (𝓡).Y = (𝓡).q * v 6 := rfl
theorem C_def : (𝓡).C = (𝓡).q - v 1 - v 2 := rfl
theorem X_def : (𝓡).X = (𝓡).q * ((𝓡).q * v 5) := rfl
theorem k_def : (𝓡).k = v 8 + v 9 := rfl
theorem c_def : (𝓡).c = (𝓡).k * v 6 + v 8 := rfl
theorem Am1_def : (𝓡).Am1 = (𝓡).X * (𝓡).Y + (𝓡).Y := rfl
theorem A_def : (𝓡).A = (𝓡).Am1 + 1 := rfl
theorem H_def : (𝓡).H = 4 * (𝓡).Am1 - 1 := rfl
theorem E_def : (𝓡).E = (𝓡).X * (𝓡).Y * ((𝓡).k * (𝓡).Y) *
    ((𝓡).X * (𝓡).Y * ((𝓡).k * (𝓡).Y) + (𝓡).k) + 1 := rfl
theorem rank_def : (𝓡).rank = ((𝓡).h * ((𝓡).q - v 1) + v 2) * ((𝓡).q * (𝓡).q - 1) +
    (p 2 + (𝓡).q * p 3) * v 0 := rfl
theorem e_def : (𝓡).e = (𝓡).k - (𝓡).rank - 1 := rfl
theorem B_def : (𝓡).B = (p 1 + (𝓡).q * v 5) * (𝓡).C - v 1 := rfl
theorem U_def : (𝓡).U = v 3 * ((𝓡).c * (𝓡).c) := rfl
theorem Delta_def : (𝓡).Delta = (𝓡).Am1 * ((𝓡).Am1 + 2) := rfl
theorem a_def : (𝓡).a = (𝓡).Delta * ((𝓡).U * (𝓡).E) * (𝓡).U := rfl
theorem F0_def : (𝓡).F0 = (𝓡).a + 1 := rfl
theorem f_def : (𝓡).f = (𝓡).a + (𝓡).F0 := rfl
theorem Q_def : (𝓡).Q = (𝓡).Delta * (4 * ((𝓡).a * (𝓡).F0)) := rfl
theorem b_def : (𝓡).b = (𝓡).c * v 4 - (𝓡).rank := rfl
theorem V_def : (𝓡).V = (𝓡).f * (𝓡).b - (𝓡).c := rfl
theorem K_def : (𝓡).K = (𝓡).X * (3 * (𝓡).c - 2 * (𝓡).X) + 2 := rfl
theorem D_def : (𝓡).D = (𝓡).q * (𝓡).q * ((𝓡).q * (𝓡).q) * ((𝓡).q * (𝓡).q) * (𝓡).q := rfl
theorem Z_def : (𝓡).Z = (𝓡).h * (𝓡).D * ((𝓡).H * (v 7 - (𝓡).b * (𝓡).V * (𝓡).B) + (𝓡).K) -
    (𝓡).H * ((𝓡).D * (𝓡).B + (𝓡).h * ((𝓡).e - (𝓡).q * (𝓡).q * ((𝓡).q * (𝓡).q) * v 6)) := rfl
theorem M_def : (𝓡).M = (𝓡).h * (𝓡).D * (𝓡).H := rfl
theorem Gn_def : (𝓡).Gn = (𝓡).E * (𝓡).F0 := rfl
theorem value82_def : value82 p v = (𝓡).Q * ((𝓡).Z * (𝓡).Z - (𝓡).M * (𝓡).M * (𝓡).Gn * ((𝓡).V * (𝓡).V)) +
    ((𝓡).M * (𝓡).M * (𝓡).Gn - (𝓡).Z * (𝓡).Z) := rfl

end Defs

end Generic

variable {R : Type*} [CommRing R]

section Identities
variable (p : Fin 4 → R) (v : Fin 10 → R)
local notation "𝓡" => regs p v

/-- `P = (Q - 1) Z² - M² G (Q V² - 1)`. -/
theorem value82_eq :
    value82 p v = ((𝓡).Q - 1) * (𝓡).Z ^ 2 - (𝓡).M ^ 2 * (𝓡).Gn * ((𝓡).Q * (𝓡).V ^ 2 - 1) := by
  rw [value82_def]
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

/-- `f² = 1 + 4 a F0`. -/
theorem f_sq : (𝓡).f ^ 2 = 1 + 4 * (𝓡).a * (𝓡).F0 := by
  rw [f_def, F0_def]; ring

/-- `a = Delta U² E`. -/
theorem a_eq : (𝓡).a = (𝓡).Delta * (𝓡).U ^ 2 * (𝓡).E := by
  rw [a_def]; ring

/-- `Q = Delta (f² - 1)`. -/
theorem Q_eq : (𝓡).Q = (𝓡).Delta * ((𝓡).f ^ 2 - 1) := by
  rw [Q_def, f_sq]; ring

/-- `Q = 4 Delta² U² G`. -/
theorem Q_eq' : (𝓡).Q = 4 * (𝓡).Delta ^ 2 * (𝓡).U ^ 2 * (𝓡).Gn := by
  have hq := Q_def p v
  have h3 := a_eq p v
  have h2 := Gn_def p v
  linear_combination hq + 4 * (𝓡).Delta * (𝓡).F0 * h3 - 4 * (𝓡).Delta ^ 2 * (𝓡).U ^ 2 * h2

/-- `f - 1 = 2 Delta i² c⁴ E`. -/
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

/-- `V = f (c T - R) - c`. -/
theorem V_eq : (𝓡).V = (𝓡).f * ((𝓡).c * v 4 - (𝓡).rank) - (𝓡).c := by
  rw [V_def, b_def]

/-- `R = (h C + q alpha)(q² - 1) + (MC + q MF) J`. -/
theorem rank_eq_C : (𝓡).rank = ((𝓡).h * (𝓡).C + (𝓡).q * v 2) * ((𝓡).q ^ 2 - 1) +
    (p 2 + (𝓡).q * p 3) * v 0 := by
  rw [rank_def, C_def, q_def]; ring

end Identities

end DiophantineConsistency.TenPositiveTrace82
