import DiophantineConsistency.Representation
import Mathlib.Data.Fin.VecNotation

/-! # Matrix-free data of the Jones nine-variable syntax

The free-quantity record, the rank code, the closed two-radicand combiner
and input removal, with their original names. The proofs stay in
`NinePolynomial`, `RefinedPair` and `JonesSyntax`. These definitions are
separated because those proofs import Mathlib's matrices, whose
`Matrix.map` collides with Foundation's; keeping the data Matrix-free lets
model-internal (Foundation) modules name the same syntax. -/

namespace DiophantineConsistency.NinePolynomial

/-- The free Jones quantities with their coefficient ring made explicit. -/
structure RingVars (A : Type*) where
  (R N b g G h s w φ i j : A)

namespace RingVars

variable {R : Type*} [Add R] [Sub R] [Mul R] [Pow R ℕ]
  [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4] [OfNat R 5] [OfNat R 8]
  (v : RingVars R)

def U : R := v.N ^ 2 * v.w
def Y : R := v.N ^ 2 * v.s
def M : R := v.R * v.Y
def P : R := 2 * v.M ^ 2 * v.U
def K : R := v.R + 1 + v.h * (v.P - 1)
def A : R := v.M * (v.U + 1)
def B' : R := 2 * v.R + 1
def W : R := v.b * v.w
def C : R := v.B' + v.W + v.φ
def J : R := 4 * v.A - 5
def Q : R := 3 * v.W * v.C - 2 * (v.W ^ 2 - 1)
def D : R := (v.A ^ 2 - 1) * v.C ^ 2 + 1
def E : R := v.i * v.J * v.D * v.C ^ 2
def F : R := (v.A ^ 2 - 1) * v.E ^ 2 + 1
def Gp : R := v.A + v.F * (v.C * v.D + 1 - v.A)
def H : R := v.B' + v.j * v.C
def I : R := (v.Gp ^ 2 - 1) * v.H ^ 2 + 1

def rad : Fin 2 → R := ![(v.P ^ 2 - 1) * v.K ^ 2 + 1, v.D * v.F * v.I]
def wt : Fin 2 → R := fun k => v.rad k ^ 2 + 2
def dvsr : R := (v.J * v.F) ^ 2
def dvnd : R := (v.Q * v.F + v.J * (v.H - v.C)) ^ 2
def marg : R := v.K ^ 2 * v.G - 4 * (v.C - v.K * v.Y) ^ 2 * v.G - 8 * v.g * v.K ^ 2

end RingVars

/-- The rank coding polynomial, written over any commutative coefficient ring. -/
def rankCode {R : Type*} [Add R] [Sub R] [Mul R] [Pow R ℕ] [OfNat R 1] [OfNat R 2] (x z b e g l n q θ lam : R) : R :=
  (g + e * q ^ 3 + l * q ^ 5 +
    (2 * (e - z * lam) * (1 + x * b ^ 5 + g) ^ 4 + lam * b ^ 5 + lam * b ^ 5 * q ^ 4) * q ^ 7) *
      (n ^ 2 - n) +
  (q ^ 3 - b * l + l + θ * lam * q ^ 3 + (b ^ 5 - 2) * q ^ 8) * (n ^ 2 - 1)

end DiophantineConsistency.NinePolynomial

namespace DiophantineConsistency.RefinedPair

/-- Literal ordinary-polynomial formula for two radicands. -/
def value {R : Type*} [Add R] [Sub R] [Mul R] [Pow R ℕ]
    [OfNat R 1] [OfNat R 2] [OfNat R 4] (A0 A1 V0 V1 n B C D : R) : R :=
  let K := B * (2 * D - 1)
  let T := B * n + C - K * (C + V0 * V1)
  (T ^ 2 + K ^ 2 * A0 - K ^ 2 * V0 ^ 2 * A1) ^ 2 - 4 * T ^ 2 * K ^ 2 * A0

end DiophantineConsistency.RefinedPair

namespace DiophantineConsistency.JonesSyntax

/-- Replace the input by the fixed numeral 1 in the syntax itself. -/
def removeInput (e : Expr (Fin 10)) : Expr (Fin 9) :=
  e.subst (Fin.cons (.constant 1) (fun i => .var i))

end DiophantineConsistency.JonesSyntax
