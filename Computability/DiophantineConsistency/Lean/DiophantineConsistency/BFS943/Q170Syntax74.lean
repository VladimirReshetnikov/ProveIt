import DiophantineConsistency.ModelArithmetic
import DiophantineConsistency.WeightedExpressionDegree

/-! # Package 170's rational carrier: 12 positive unknowns, 74 operations, degree 438

`value74 p v` is the circuit
`con-zfc-diophantine-forms/170-quotient-carriers/compact/fixed_12_rational_74_degree438.json`
(`FIXED_CARRIER_PROOF.md` §7, (18)), row by row, at ports `p = (β, K0, MC, MF)`
and the twelve unknowns `J, F, α, z, n, i, T, s, w, η, ζ, γ` as
`v 0, …, v 11`:

  `q = β J + 1`, `X = w q`, `Y = s q³`, `E = X Y`, `k = η + ζ`, `ℓ = E k Y`,
  `A = ℓ (ℓ + k) + 1`, `c = k Y + η`, `a = E + Y`, `H = 4 a + 3`,
  `Δ = a² + H`, `D = X + a c + γ H`, `N1 = D² - Δ c²`,
  `R = ((q-1)(q-F) + α)(q² - 1) + (MC + q MF) J`, `e = k - R - 1`, `t = E n + e`,
  `Nt = (K0 + w)(q - F - α) + (q - F) - z (q-1)`, `m = i (a + 2) D`,
  `S0 = m Δ c²`, `I = m c²`, `W = A (I S0)`, `F2 = 1 + W`, `Q = Δ W`,
  `V = F2 (c T - R) - c`, `G = A F2`, `B = Q (t² - E² G V²) - t² + E² G`,

  `P = N1 · Nt · (3 B + 1) - 1`.

`expression p` reads it in `Expr (Fin 12)` (ports as integer constants);
`evalRing_expression` evaluates it in every commutative ring, and
`Q170Syntax74.literal_zero_iff` turns a model zero into the ring equation in
the model's ring of differences. `value74_factors` names the three factors. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Q170Form74

section Generic
variable {R : Type*} [Add R] [Sub R] [Mul R] [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4]

/-- The literal 74-operation circuit; unknowns `J, F, α, z, n, i, T, s, w, η, ζ, γ`. -/
def value74 (p : Fin 4 → R) (v : Fin 12 → R) : R :=
  let J := v 0
  let F := v 1
  let alpha := v 2
  let z := v 3
  let n := v 4
  let i := v 5
  let T := v 6
  let s := v 7
  let w := v 8
  let eta := v 9
  let zeta := v 10
  let gamma := v 11
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
  let e := k - R - 1
  let t := E * n + e
  let Nt := (p 1 + w) * C + qF - z * qm
  let mult := i * (a + 2) * D
  let S0 := mult * Dc2
  let I := mult * c2
  let W := A * (I * S0)
  let f2 := 1 + W
  let Q := Delta * W
  let V := f2 * (c * T - R) - c
  let G := A * f2
  let t2 := t * t
  let EG := E * E * G
  let B := Q * (t2 - EG * (V * V)) - t2 + EG
  N1 * Nt * (3 * B + 1) - 1

end Generic

/-- The fixed ports as integer constants. -/
def ports (p : Fin 4 → ℤ) : Fin 4 → Expr (Fin 12) := fun j => .constant (p j)

/-- The literal 74-operation polynomial at ports `p = (beta, K0, MC, MF)`. -/
def expression (p : Fin 4 → ℤ) : Expr (Fin 12) := value74 (ports p) Expr.var

/-- The literal syntax evaluates to the circuit value in every commutative ring. -/
theorem evalRing_expression {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 12 → R) :
    (expression p).evalRing v = value74 (fun j => (p j : R)) v := by
  simp only [expression, value74, ports, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant,
    Nat.cast_ofNat, Nat.cast_one]

/-- The three factors, in named form (a definitional unfolding). -/
theorem value74_factors {R : Type*} [CommRing R] (p : Fin 4 → R) (v : Fin 12 → R)
    (q X Y E k A c a H Delta D R0 t Nt m S0 I W f2 V G B : R)
    (hq : q = p 0 * v 0 + 1) (hX : X = v 8 * q) (hY : Y = v 7 * (q * q * q))
    (hE : E = X * Y) (hk : k = v 9 + v 10) (hA : A = E * (k * Y) * (E * (k * Y) + k) + 1)
    (hc : c = k * Y + v 9) (ha : a = E + Y) (hH : H = 4 * a + 3) (hDelta : Delta = a * a + H)
    (hD : D = X + a * c + v 11 * H)
    (hR0 : R0 = (p 0 * v 0 * (q - v 1) + v 2) * (q * q - 1) + (p 2 + q * p 3) * v 0)
    (ht : t = E * v 4 + (k - R0 - 1))
    (hNt : Nt = (p 1 + v 8) * (q - v 1 - v 2) + (q - v 1) - v 3 * (p 0 * v 0))
    (hm : m = v 5 * (a + 2) * D) (hS0 : S0 = m * (Delta * (c * c))) (hI : I = m * (c * c))
    (hW : W = A * (I * S0)) (hf2 : f2 = 1 + W) (hV : V = f2 * (c * v 6 - R0) - c)
    (hG : G = A * f2)
    (hB : B = Delta * W * (t * t - E * E * G * (V * V)) - t * t + E * E * G) :
    value74 p v = (D * D - Delta * (c * c)) * Nt * (3 * B + 1) - 1 := by
  subst_vars
  rfl

end DiophantineConsistency.Q170Form74

namespace Q170Syntax74
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing Q170Form74
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def literal (p : Fin 4 → ℕ) : Expr (Fin 12) :=
  Q170Form74.expression (fun j => (p j : ℤ))

theorem literal_zero_iff (p : Fin 4 → ℕ) (v : Fin 12 → V) :
    InternalZero (literal p) v ↔
      value74 (fun j => ((p j : ℕ) : DiffRing V)) (fun j => ι (v j)) = 0 := by
  rw [internalZero_iff]
  unfold literal
  rw [Q170Form74.evalRing_expression]
  simp only [Int.cast_natCast]

#print axioms Q170Syntax74.literal_zero_iff
end Q170Syntax74
