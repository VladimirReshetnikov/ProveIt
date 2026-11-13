import DiophantineConsistency.ModelArithmetic
import DiophantineConsistency.WeightedExpressionDegree

/-! # Package 170's q⁴ residue carrier: 13 positive unknowns, 72 operations, degree 154

`value72 p v` is the circuit
`con-zfc-diophantine-forms/170-quotient-carriers/compact/fixed_13_residue_q4_72_degree154.json`
(`FIXED_CARRIER_PROOF.md` §6.1: the reduced form (4) with `t = q⁴ n - k + R`
and `m = A q² i`), row by row, at ports `p = (β, K0, MC, MF)`
and the thirteen unknowns `J, F, α, z, f, n, i, T, s, w, η, ζ, γ` as
`v 0, …, v 12`:

  `q = β J + 1`, `X = w q`, `Y = s q³`, `E = X Y`, `k = η + ζ`, `ℓ = E k Y`,
  `A = ℓ (ℓ + k) + 1`, `c = k Y + η`, `a = E + Y`, `H = 4 a + 3`,
  `Δ = a² + H`, `D = X + a c + γ H`, `N1 = D² - Δ c²`,
  `R = ((q-1)(q-F) + α)(q² - 1) + (MC + q MF) J`, `t = q⁴ n - k + R`,
  `Nt = (K0 + w)(q - F - α) + (q - F) - z (q-1)`, `m = q² i A`,
  `S = m Δ c²`, `I = m c²`, `Ns = f² - I S`, `Q = Δ (f² - 1)`,
  `V = f² (c T - R) - c`, `B = Q (t² - A V²) - t² + A`,

  `P = N1 · Nt · (3 B + 1) · Ns - 1`.

`expression p` reads it in `Expr (Fin 13)` (ports as integer constants);
`evalRing_expression` evaluates it in every commutative ring, and
`Q170Syntax72.literal_zero_iff` turns a model zero into the ring equation in
the model's ring of differences. `value72_factors` names the four factors. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Q170Form72

section Generic
variable {R : Type*} [Add R] [Sub R] [Mul R] [OfNat R 1] [OfNat R 3] [OfNat R 4]

/-- The literal 72-operation circuit; unknowns `J, F, α, z, f, n, i, T, s, w, η, ζ, γ`. -/
def value72 (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  let J := v 0
  let F := v 1
  let alpha := v 2
  let z := v 3
  let f := v 4
  let n := v 5
  let i := v 6
  let T := v 7
  let s := v 8
  let w := v 9
  let eta := v 10
  let zeta := v 11
  let gamma := v 12
  let qm := p 0 * J
  let q := qm + 1
  let q2 := q * q
  let q3 := q2 * q
  let X := w * q
  let Y := s * q3
  let E := X * Y
  let k := eta + zeta
  let kY := k * Y
  let ell := E * kY
  let A := ell * (ell + k) + 1
  let c := kY + eta
  let a := E + Y
  let H := 4 * a + 3
  let Delta := a * a + H
  let D := X + a * c + gamma * H
  let c2 := c * c
  let Dc2 := Delta * c2
  let N1 := D * D - Dc2
  let qF := q - F
  let C := qF - alpha
  let R := (qm * qF + alpha) * (q2 - 1) + (p 2 + q * p 3) * J
  let q4 := q2 * q2
  let t := q4 * n - k + R
  let Nt := (p 1 + w) * C + qF - z * qm
  let iA := q2 * i * A
  let S := iA * Dc2
  let I := iA * c2
  let f2 := f * f
  let Ns := f2 - I * S
  let Q := Delta * (f2 - 1)
  let V := f2 * (c * T - R) - c
  let t2 := t * t
  let B := Q * (t2 - A * (V * V)) - t2 + A
  N1 * Nt * (3 * B + 1) * Ns - 1

end Generic

/-- The fixed ports as integer constants. -/
def ports (p : Fin 4 → ℤ) : Fin 4 → Expr (Fin 13) := fun j => .constant (p j)

/-- The literal 72-operation polynomial at ports `p = (beta, K0, MC, MF)`. -/
def expression (p : Fin 4 → ℤ) : Expr (Fin 13) := value72 (ports p) Expr.var

/-- The literal syntax evaluates to the circuit value in every commutative ring. -/
theorem evalRing_expression {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (expression p).evalRing v = value72 (fun j => (p j : R)) v := by
  simp only [expression, value72, ports, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant,
    Nat.cast_ofNat, Nat.cast_one]

/-- The four factors, in named form (a definitional unfolding). -/
theorem value72_factors {R : Type*} [CommRing R] (p : Fin 4 → R) (v : Fin 13 → R)
    (q X Y E k A c a H Delta D R0 t Nt m S I f2 V B : R)
    (hq : q = p 0 * v 0 + 1) (hX : X = v 9 * q) (hY : Y = v 8 * (q * q * q))
    (hE : E = X * Y) (hk : k = v 10 + v 11) (hA : A = E * (k * Y) * (E * (k * Y) + k) + 1)
    (hc : c = k * Y + v 10) (ha : a = E + Y) (hH : H = 4 * a + 3) (hDelta : Delta = a * a + H)
    (hD : D = X + a * c + v 12 * H)
    (hR0 : R0 = (p 0 * v 0 * (q - v 1) + v 2) * (q * q - 1) + (p 2 + q * p 3) * v 0)
    (ht : t = q * q * (q * q) * v 5 - k + R0)
    (hNt : Nt = (p 1 + v 9) * (q - v 1 - v 2) + (q - v 1) - v 3 * (p 0 * v 0))
    (hm : m = q * q * v 6 * A) (hS : S = m * (Delta * (c * c))) (hI : I = m * (c * c))
    (hf2 : f2 = v 4 * v 4) (hV : V = f2 * (c * v 7 - R0) - c)
    (hB : B = Delta * (f2 - 1) * (t * t - A * (V * V)) - t * t + A) :
    value72 p v = (D * D - Delta * (c * c)) * Nt * (3 * B + 1) * (f2 - I * S) - 1 := by
  subst_vars
  rfl

end DiophantineConsistency.Q170Form72

namespace Q170Syntax72
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing Q170Form72
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def literal (p : Fin 4 → ℕ) : Expr (Fin 13) :=
  Q170Form72.expression (fun j => (p j : ℤ))

theorem literal_zero_iff (p : Fin 4 → ℕ) (v : Fin 13 → V) :
    InternalZero (literal p) v ↔
      value72 (fun j => ((p j : ℕ) : DiffRing V)) (fun j => ι (v j)) = 0 := by
  rw [internalZero_iff]
  unfold literal
  rw [Q170Form72.evalRing_expression]
  simp only [Int.cast_natCast]

#print axioms Q170Syntax72.literal_zero_iff
end Q170Syntax72
