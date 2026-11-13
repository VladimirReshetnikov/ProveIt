import DiophantineConsistency.BFS943.Trace82Regs
import DiophantineConsistency.BFS943.InverseLucasThird

/-! # The eleven-positive 104-operation, degree-174 constant-dilation equation

Package 184 (`con-zfc-diophantine-forms/184-pell-growth-210/compact11`), the
circuit `constant_dilation11.json` (104 operations, exact degree 174; proof:
`PROOF_constant_dilation.md`). Eleven positive unknowns
`J, F, α, i, T, w, s, n, η, ζ, κ`, the four direct-BFS943 ports
`β, K0, MC, MF`, transport weight `L = bV`. In the notation of that proof
(`s` is its `Y`):

* `X = q w`, free strip `c = k s + η`, constant Pell dilation `λ = 210`:
  `A - 1 = 210 (X s + s)`, `v0 = X s²`, `ell = 44100 v0 k`;
* `D = q⁷`, `M = h D`; the offset is `e* - q⁴ s` with the integral third-order
  inverse `e* = k - R - 1 - corr(k, v0)` (`InverseLucasThird.corr`);
* the carrier is `Z = M (n + κ - L B) - (D B + h (e* - q⁴ s))`, and the output
  is `(3 N + 1) (P0 + 1) - 1` with `P0 = Q (Z² - M² G V²) + (M² G - Z²)` and
  `N = K - κ H`.

`regs p v` (over the first ten unknowns) is the *core* register map: the rows
of the JSON in their own shape (`Am1 = 210 (X s + s)`, `E = ell (ell + k) + 1`,
…; the register `Y` is `210 s`), with the 87-shaped carrier
`Z = h D [H (n - b V B) + K] - H [D B + h ecl]` and `M = h D H`.
`valueC = normValue (regs p v) (regs p v).Z` is its norm. `value104 p v` (over
all eleven unknowns) is the literal circuit. Identically
`Zcore = H Z₁₀₄ + h D N` and `Mcore = H M₁₀₄` (`core_Z`, `core_M`), so at
`N = 0` the core norm is `H² P0` (`core_norm`). -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.TenPositiveTrace104
open DiophantineConsistency.TenPositiveTrace75 (Regs)

section Generic
variable {R : Type*} [Add R] [Sub R] [Mul R] [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4]
  [OfNat R 8] [OfNat R 27] [OfNat R 160] [OfNat R 210] [OfNat R 324] [OfNat R 675]
  [OfNat R 7350] [OfNat R 44100] [OfNat R 5402250] [OfNat R 5672362500]

/-- The core registers (the first ten unknowns `J, F, α, i, T, w, s, n, η, ζ`),
row by row as in the JSON, with the 87-shaped carrier `Z` and `M = h D H`. -/
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
  let q2 := q * q
  let q4 := q2 * q2
  let q3 := q2 * q
  let q7 := q4 * q3
  let C := q - F - alpha
  let X := q * w
  let k := eta + zeta
  let c := k * s + eta
  let Am1 := 210 * (X * s + s)
  let Delta := Am1 * (Am1 + 2)
  let H := 4 * Am1 - 1
  let v0 := X * s * s
  let ell := 44100 * (v0 * k)
  let E := ell * (ell + k) + 1
  let rank := (h * (q - F) + alpha) * (q2 - 1) + (p 2 + q * p 3) * J
  let e := k - rank - 1
  let corr := (v0 * k) * (k * k - 4) *
    (v0 * (5672362500 * v0 * (675 * (k * k * (k * k)) - 324 * (k * k) + 160) -
      5402250 * (27 * (k * k) + 8)) + 7350)
  let ec := (e - corr) - q4 * s
  let B := (p 1 + w) * C - F
  let U := i * (c * c)
  let a := Delta * (U * E) * U
  let F0 := a + 1
  let f := a + F0
  let Q := Delta * (4 * (a * F0))
  let b := c * T - rank
  let V := f * b - c
  let K := X * (3 * c - 2 * X) + 2
  let Z := h * q7 * (H * (n - b * V * B) + K) - H * (q7 * B + h * ec)
  let M := h * q7 * H
  { h, q, C, X, Y := 210 * s, k, c, Am1, A := Am1 + 1, H, Delta, E, rank, e, B, U, a, F0, f,
    Q, b, V, K, D := q7, Z, M, Gn := E * F0 }

/-- The offset `ec = (e - corr) - q⁴ s` (rows `estar`, `ec`). -/
def ecl (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs p v
  let v0 := r.X * v 6 * v 6
  (r.e - (v0 * r.k) * (r.k * r.k - 4) *
    (v0 * (5672362500 * v0 * (675 * (r.k * r.k * (r.k * r.k)) - 324 * (r.k * r.k) + 160) -
      5402250 * (27 * (r.k * r.k) + 8)) + 7350)) - r.q * r.q * (r.q * r.q) * v 6

/-- The core norm: `normValue` at the core carrier. -/
def valueC (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs p v
  r.Q * (r.Z * r.Z - r.M * r.M * r.Gn * (r.V * r.V)) +
    (r.M * r.M * r.Gn - r.Z * r.Z)

/-- The first ten of the eleven unknowns. -/
def core (v : Fin 11 → R) : Fin 10 → R := fun j => v j.castSucc

/-- The literal 104-operation circuit (its output row `P`), eleven unknowns
`J, F, α, i, T, w, s, n, η, ζ, κ`. -/
def value104 (p : Fin 4 → R) (v : Fin 11 → R) : R :=
  let r := regs p (core v)
  let kappa := v 10
  let M := r.h * r.D
  let Z := M * (v 7 + kappa - r.b * r.V * r.B) - (r.D * r.B + r.h * ecl p (core v))
  let P0 := r.Q * (Z * Z - M * M * r.Gn * (r.V * r.V)) + (M * M * r.Gn - Z * Z)
  let N := r.K - kappa * r.H
  (3 * N + 1) * (P0 + 1) - 1

theorem valueC_norm (p : Fin 4 → R) (v : Fin 10 → R) :
    valueC p v = TenPositiveTrace76.normValue (regs p v) (regs p v).Z := rfl

section Defs
variable (p : Fin 4 → R) (v : Fin 10 → R)
local notation "𝓡" => regs p v

theorem h_def : (𝓡).h = p 0 * v 0 := rfl
theorem q_def : (𝓡).q = (𝓡).h + 1 := rfl
theorem Y_def : (𝓡).Y = 210 * v 6 := rfl
theorem C_def : (𝓡).C = (𝓡).q - v 1 - v 2 := rfl
theorem X_def : (𝓡).X = (𝓡).q * v 5 := rfl
theorem k_def : (𝓡).k = v 8 + v 9 := rfl
theorem c_def : (𝓡).c = (𝓡).k * v 6 + v 8 := rfl
theorem Am1_def : (𝓡).Am1 = 210 * ((𝓡).X * v 6 + v 6) := rfl
theorem A_def : (𝓡).A = (𝓡).Am1 + 1 := rfl
theorem H_def : (𝓡).H = 4 * (𝓡).Am1 - 1 := rfl
theorem E_def : (𝓡).E = 44100 * ((𝓡).X * v 6 * v 6 * (𝓡).k) *
    (44100 * ((𝓡).X * v 6 * v 6 * (𝓡).k) + (𝓡).k) + 1 := rfl
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
theorem D_def : (𝓡).D = (𝓡).q * (𝓡).q * ((𝓡).q * (𝓡).q) * ((𝓡).q * (𝓡).q * (𝓡).q) := rfl
theorem ecl_def : ecl p v = ((𝓡).e - ((𝓡).X * v 6 * v 6 * (𝓡).k) * ((𝓡).k * (𝓡).k - 4) *
    ((𝓡).X * v 6 * v 6 * (5672362500 * ((𝓡).X * v 6 * v 6) *
      (675 * ((𝓡).k * (𝓡).k * ((𝓡).k * (𝓡).k)) - 324 * ((𝓡).k * (𝓡).k) + 160) -
      5402250 * (27 * ((𝓡).k * (𝓡).k) + 8)) + 7350)) -
    (𝓡).q * (𝓡).q * ((𝓡).q * (𝓡).q) * v 6 := rfl
theorem Z_def : (𝓡).Z = (𝓡).h * (𝓡).D * ((𝓡).H * (v 7 - (𝓡).b * (𝓡).V * (𝓡).B) + (𝓡).K) -
    (𝓡).H * ((𝓡).D * (𝓡).B + (𝓡).h * ecl p v) := rfl
theorem M_def : (𝓡).M = (𝓡).h * (𝓡).D * (𝓡).H := rfl
theorem Gn_def : (𝓡).Gn = (𝓡).E * (𝓡).F0 := rfl
theorem valueC_def : valueC p v = (𝓡).Q * ((𝓡).Z * (𝓡).Z - (𝓡).M * (𝓡).M * (𝓡).Gn * ((𝓡).V * (𝓡).V)) +
    ((𝓡).M * (𝓡).M * (𝓡).Gn - (𝓡).Z * (𝓡).Z) := rfl

end Defs

end Generic

variable {R : Type*} [CommRing R]

section Identities
variable (p : Fin 4 → R) (v : Fin 10 → R)
local notation "𝓡" => regs p v

/-- `P = (Q - 1) Z² - M² G (Q V² - 1)`. -/
theorem valueC_eq :
    valueC p v = ((𝓡).Q - 1) * (𝓡).Z ^ 2 - (𝓡).M ^ 2 * (𝓡).Gn * ((𝓡).Q * (𝓡).V ^ 2 - 1) := by
  rw [valueC_def]
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
  rw [E_def, Y_def]; ring

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

/-- The offset through the integral inverse: `ec = T3(k, v0) - R - 1 - q⁴ s`. -/
theorem ecl_T3 : ecl p v = InverseLucasThird.T3 (𝓡).k ((𝓡).X * v 6 * v 6) - (𝓡).rank - 1 -
    (𝓡).q ^ 4 * v 6 := by
  rw [ecl_def, e_def]
  simp only [InverseLucasThird.T3, InverseLucasThird.corr]
  ring

end Identities

section Literal
variable (p : Fin 4 → R) (v : Fin 11 → R)

/-- The literal carrier `Z₁₀₄ = h D (n + κ - L B) - (D B + h ec)`. -/
def Z104 : R :=
  (regs p (core v)).h * (regs p (core v)).D *
      (v 7 + v 10 - (regs p (core v)).b * (regs p (core v)).V * (regs p (core v)).B) -
    ((regs p (core v)).D * (regs p (core v)).B + (regs p (core v)).h * ecl p (core v))

/-- The literal norm `P0` at multiplier `M₁₀₄ = h D`. -/
def P0 : R :=
  let r := regs p (core v)
  r.Q * (Z104 p v * Z104 p v - r.h * r.D * (r.h * r.D) * r.Gn * (r.V * r.V)) +
    (r.h * r.D * (r.h * r.D) * r.Gn - Z104 p v * Z104 p v)

/-- The unit factor `N = K - κ H`. -/
def N104 : R := (regs p (core v)).K - v 10 * (regs p (core v)).H

theorem value104_eq : value104 p v = (3 * N104 p v + 1) * (P0 p v + 1) - 1 := rfl

theorem core_n : core v 7 = v 7 := rfl

/-- `Zcore = H Z₁₀₄ + h D N`. -/
theorem core_Z : (regs p (core v)).Z =
    (regs p (core v)).H * Z104 p v + (regs p (core v)).h * (regs p (core v)).D * N104 p v := by
  rw [Z_def]
  simp only [Z104, N104, core_n]
  ring

/-- At `N = 0` the core norm is `H² P0`. -/
theorem core_norm (hN : N104 p v = 0) :
    valueC p (core v) = (regs p (core v)).H ^ 2 * P0 p v := by
  rw [valueC_def, core_Z, hN, M_def]
  simp only [P0]
  ring

end Literal

end DiophantineConsistency.TenPositiveTrace104
