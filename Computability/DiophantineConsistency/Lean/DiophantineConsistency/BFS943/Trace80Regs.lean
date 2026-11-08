import DiophantineConsistency.BFS943.Trace79Regs

/-! # The ten-positive 80-operation, degree-258 trace equation (chart q1)

Package 163 (`con-zfc-diophantine-forms/163-trace-radical`), compact chart
`q1`, weight `L = bV`: the circuit `equations/trace80_degree258.json`. It has
the ten unknowns and four ports of the 75/76/79 circuits. Relative to 79/290
it changes four rows: `Y = q s` (instead of `q² s`), the transport base
`Wbase = q w` (new row, used in `X = q Wbase` and `K0w = K0 + Wbase`), and the
denominator `D = q⁴ q²` (instead of `q⁴ q`); the offset `e - q⁴ s` is the 79
one.

The 80 registers `regs` are the q1 instance of `TenPositiveTrace79.regsAt`
(`X = q (q w)`, `Y = q s`, `W = q w`) with the 80 denominator, carrier and
multiplier. The register lemmas below are those of `TenPositiveTrace79` (by
`rfl`), with `Y_def`, `X_def`, `B_def`, `D_def`, `Z_def`, `M_def` changed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.TenPositiveTrace80
open DiophantineConsistency.TenPositiveTrace75 (Regs)
open DiophantineConsistency.TenPositiveTrace79 (regsAt)

section Generic
variable {R : Type*} [Add R] [Sub R] [Mul R] [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4]

/-- The 80 registers: the q1 instance with `D = q⁴ q²`, carrier
`Z = h D [H (n - b V B) + K] - H [D B + h (e - q⁴ s)]` and `M = h D H`. -/
def regs (p : Fin 4 → R) (v : Fin 10 → R) : Regs R :=
  let r := regsAt p v ((p 0 * v 0 + 1) * ((p 0 * v 0 + 1) * v 5)) ((p 0 * v 0 + 1) * v 6)
    ((p 0 * v 0 + 1) * v 5)
  let D := r.q * r.q * (r.q * r.q) * (r.q * r.q)
  let L := r.b * r.V
  { r with D := D,
           Z := r.h * D * (r.H * (v 7 - L * r.B) + r.K) -
             r.H * (D * r.B + r.h * (r.e - r.q * r.q * (r.q * r.q) * v 6)),
           M := r.h * D * r.H }

/-- The value of the 80-operation circuit (its output row `N`). -/
def value80 (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs p v
  r.Q * (r.Z * r.Z - r.M * r.M * r.Gn * (r.V * r.V)) +
    (r.M * r.M * r.Gn - r.Z * r.Z)

theorem value80_norm (p : Fin 4 → R) (v : Fin 10 → R) :
    value80 p v = TenPositiveTrace76.normValue (regs p v) (regs p v).Z := rfl

section Defs
variable (p : Fin 4 → R) (v : Fin 10 → R)
local notation "𝓡" => regs p v

theorem h_def : (𝓡).h = p 0 * v 0 := rfl
theorem q_def : (𝓡).q = (𝓡).h + 1 := rfl
theorem Y_def : (𝓡).Y = (𝓡).q * v 6 := rfl
theorem C_def : (𝓡).C = (𝓡).q - v 1 - v 2 := rfl
theorem X_def : (𝓡).X = (𝓡).q * ((𝓡).q * v 5) := rfl
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
theorem D_def : (𝓡).D = (𝓡).q * (𝓡).q * ((𝓡).q * (𝓡).q) * ((𝓡).q * (𝓡).q) := rfl
theorem Z_def : (𝓡).Z = (𝓡).h * (𝓡).D * ((𝓡).H * (v 7 - (𝓡).b * (𝓡).V * (𝓡).B) + (𝓡).K) -
    (𝓡).H * ((𝓡).D * (𝓡).B + (𝓡).h * ((𝓡).e - (𝓡).q * (𝓡).q * ((𝓡).q * (𝓡).q) * v 6)) := rfl
theorem M_def : (𝓡).M = (𝓡).h * (𝓡).D * (𝓡).H := rfl
theorem Gn_def : (𝓡).Gn = (𝓡).E * (𝓡).F0 := rfl
theorem value80_def : value80 p v = (𝓡).Q * ((𝓡).Z * (𝓡).Z - (𝓡).M * (𝓡).M * (𝓡).Gn * ((𝓡).V * (𝓡).V)) +
    ((𝓡).M * (𝓡).M * (𝓡).Gn - (𝓡).Z * (𝓡).Z) := rfl

end Defs

end Generic

variable {R : Type*} [CommRing R]

section Identities
variable (p : Fin 4 → R) (v : Fin 10 → R)
local notation "𝓡" => regs p v

/-- `P = (Q - 1) Z² - M² G (Q V² - 1)`. -/
theorem value80_eq :
    value80 p v = ((𝓡).Q - 1) * (𝓡).Z ^ 2 - (𝓡).M ^ 2 * (𝓡).Gn * ((𝓡).Q * (𝓡).V ^ 2 - 1) := by
  rw [value80_def]
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

end DiophantineConsistency.TenPositiveTrace80
