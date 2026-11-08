import DiophantineConsistency.BFS943.Trace82Regs

/-! # The ten-positive 87-operation, degree-214 free-inverse equation

Package 172 (`con-zfc-diophantine-forms/172-pooled-powers-round21`), mode
`free_inverse`: the circuit `scalar/positive10/positive10_degree214_ops87.json`.
Ten positive unknowns `J, F, α, i, T, w, s, n, η, ζ`, the four direct-BFS943
ports `β, K0, MC, MF`, transport weight `L = bV`. Relative to the 82/240
free-plain circuit it changes three things:

* `Wbase = w` and `X = q w` (rows `X = w q`, `K0w = K0 + w`); the Pell base
  keeps the scale `λ = q` (`A - 1 = q s (X + 1)`, `v = X (q s)²`) and the
  strip is free (`c = k s + η`);
* the denominator is `D = 6 q⁷` (row `sixq7`);
* the offset is the inverse-Lucas correction
  `eclear = 6 (e - q⁴ s) - v k (k² - 4)` (rows `inverse_cubic`, `eclear`).

So the registers are `TenPositiveTrace82.regsAtC p v X Y W c` at `X = q w`,
`Y = q s`, `W = w`, `c = k s + η`, with `D`, `Z`, `M` replaced. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.TenPositiveTrace87
open DiophantineConsistency.TenPositiveTrace75 (Regs)
open DiophantineConsistency.TenPositiveTrace82 (regsAtC)

section Generic
variable {R : Type*} [Add R] [Sub R] [Mul R] [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4]
  [OfNat R 6]

/-- The 87 registers: `X = q w`, `Y = q s`, `W = w`, `c = k s + η`,
`D = 6 q⁷`, carrier `Z = h D [H (n - b V B) + K] - H [D B + h eclear]`,
multiplier `M = h D H`. -/
def regs (p : Fin 4 → R) (v : Fin 10 → R) : Regs R :=
  let r := regsAtC p v ((p 0 * v 0 + 1) * v 5) ((p 0 * v 0 + 1) * v 6)
    (v 5) ((v 8 + v 9) * v 6 + v 8)
  let D := 6 * (r.q * r.q * (r.q * r.q) * (r.q * r.q) * r.q)
  let L := r.b * r.V
  let ecl := 6 * (r.e - r.q * r.q * (r.q * r.q) * v 6) - r.X * r.Y * r.Y * r.k * (r.k * r.k - 4)
  { r with D := D,
           Z := r.h * D * (r.H * (v 7 - L * r.B) + r.K) - r.H * (D * r.B + r.h * ecl),
           M := r.h * D * r.H }

/-- The inverse-Lucas offset `eclear = 6 (e - q⁴ s) - v k (k² - 4)`, `v = X Y²`. -/
def ecl (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs p v
  6 * (r.e - r.q * r.q * (r.q * r.q) * v 6) - r.X * r.Y * r.Y * r.k * (r.k * r.k - 4)

/-- The value of the 87-operation circuit (its output row `N`). -/
def value87 (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs p v
  r.Q * (r.Z * r.Z - r.M * r.M * r.Gn * (r.V * r.V)) +
    (r.M * r.M * r.Gn - r.Z * r.Z)

theorem value87_norm (p : Fin 4 → R) (v : Fin 10 → R) :
    value87 p v = TenPositiveTrace76.normValue (regs p v) (regs p v).Z := rfl

section Defs
variable (p : Fin 4 → R) (v : Fin 10 → R)
local notation "𝓡" => regs p v

theorem h_def : (𝓡).h = p 0 * v 0 := rfl
theorem q_def : (𝓡).q = (𝓡).h + 1 := rfl
theorem Y_def : (𝓡).Y = (𝓡).q * v 6 := rfl
theorem C_def : (𝓡).C = (𝓡).q - v 1 - v 2 := rfl
theorem X_def : (𝓡).X = (𝓡).q * v 5 := rfl
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
theorem D_def : (𝓡).D =
    6 * ((𝓡).q * (𝓡).q * ((𝓡).q * (𝓡).q) * ((𝓡).q * (𝓡).q) * (𝓡).q) := rfl
theorem ecl_def : ecl p v = 6 * ((𝓡).e - (𝓡).q * (𝓡).q * ((𝓡).q * (𝓡).q) * v 6) -
    (𝓡).X * (𝓡).Y * (𝓡).Y * (𝓡).k * ((𝓡).k * (𝓡).k - 4) := rfl
theorem Z_def : (𝓡).Z = (𝓡).h * (𝓡).D * ((𝓡).H * (v 7 - (𝓡).b * (𝓡).V * (𝓡).B) + (𝓡).K) -
    (𝓡).H * ((𝓡).D * (𝓡).B + (𝓡).h * ecl p v) := rfl
theorem M_def : (𝓡).M = (𝓡).h * (𝓡).D * (𝓡).H := rfl
theorem Gn_def : (𝓡).Gn = (𝓡).E * (𝓡).F0 := rfl
theorem value87_def : value87 p v = (𝓡).Q * ((𝓡).Z * (𝓡).Z - (𝓡).M * (𝓡).M * (𝓡).Gn * ((𝓡).V * (𝓡).V)) +
    ((𝓡).M * (𝓡).M * (𝓡).Gn - (𝓡).Z * (𝓡).Z) := rfl

end Defs

end Generic

variable {R : Type*} [CommRing R]

section Identities
variable (p : Fin 4 → R) (v : Fin 10 → R)
local notation "𝓡" => regs p v

/-- `P = (Q - 1) Z² - M² G (Q V² - 1)`. -/
theorem value87_eq :
    value87 p v = ((𝓡).Q - 1) * (𝓡).Z ^ 2 - (𝓡).M ^ 2 * (𝓡).Gn * ((𝓡).Q * (𝓡).V ^ 2 - 1) := by
  rw [value87_def]
  ring

theorem delta_eq : (𝓡).Delta = (𝓡).A ^ 2 - 1 := by
  rw [Delta_def, A_def]; ring

theorem H_eq : (𝓡).H = 4 * (𝓡).A - 5 := by
  rw [H_def, A_def]; ring

theorem f_eq : (𝓡).f = 1 + 2 * (𝓡).a := by
  rw [f_def, F0_def]; ring

theorem f_sq : (𝓡).f ^ 2 = 1 + 4 * (𝓡).a * (𝓡).F0 := by
  rw [f_def, F0_def]; ring

theorem a_eq : (𝓡).a = (𝓡).Delta * (𝓡).U ^ 2 * (𝓡).E := by
  rw [a_def]; ring

theorem Q_eq : (𝓡).Q = (𝓡).Delta * ((𝓡).f ^ 2 - 1) := by
  rw [Q_def, f_sq]; ring

theorem Q_eq' : (𝓡).Q = 4 * (𝓡).Delta ^ 2 * (𝓡).U ^ 2 * (𝓡).Gn := by
  have hq := Q_def p v
  have h3 := a_eq p v
  have h2 := Gn_def p v
  linear_combination hq + 4 * (𝓡).Delta * (𝓡).F0 * h3 - 4 * (𝓡).Delta ^ 2 * (𝓡).U ^ 2 * h2

theorem f_sub_one : (𝓡).f - 1 = 2 * (𝓡).Delta * v 3 ^ 2 * (𝓡).c ^ 4 * (𝓡).E := by
  rw [f_eq, a_def, U_def]; ring

theorem f_one_mod_c : (𝓡).f = 1 + (𝓡).c * (2 * (𝓡).Delta * v 3 ^ 2 * (𝓡).c ^ 3 * (𝓡).E) := by
  have := f_sub_one p v
  linear_combination this

theorem E_eq : (𝓡).E = 1 + (𝓡).X * (𝓡).Y ^ 2 * ((𝓡).X * (𝓡).Y ^ 2 + 1) * (𝓡).k ^ 2 := by
  rw [E_def]; ring

theorem strong_norm (g : R) (hg : (𝓡).Gn = g ^ 2) :
    (𝓡).f ^ 2 - (𝓡).Delta * (2 * (𝓡).U * g) ^ 2 = 1 := by
  have h1 := f_sq p v
  have h3 := a_eq p v
  have h2 := Gn_def p v
  linear_combination h1 + 4 * (𝓡).F0 * h3 - 4 * (𝓡).Delta * (𝓡).U ^ 2 * h2 +
    4 * (𝓡).Delta * (𝓡).U ^ 2 * hg

theorem Q_strong (g : R) (hg : (𝓡).Gn = g ^ 2) :
    (𝓡).Q = ((𝓡).Delta * (2 * (𝓡).U * g)) ^ 2 := by
  rw [Q_eq', hg]; ring

theorem V_eq : (𝓡).V = (𝓡).f * ((𝓡).c * v 4 - (𝓡).rank) - (𝓡).c := by
  rw [V_def, b_def]

theorem rank_eq_C : (𝓡).rank = ((𝓡).h * (𝓡).C + (𝓡).q * v 2) * ((𝓡).q ^ 2 - 1) +
    (p 2 + (𝓡).q * p 3) * v 0 := by
  rw [rank_def, C_def, q_def]; ring

end Identities

end DiophantineConsistency.TenPositiveTrace87
