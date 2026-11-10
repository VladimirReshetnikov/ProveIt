import DiophantineConsistency.SharingSeed14Degree124

/-! SOURCE-ONLY: readable formula in formal integer expression syntax. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Readable
abbrev E := Expr (Fin 15)
def positive (i : Fin 15) : E := Expr.var i + 1
def judge : E := positive 1
def bound : E := positive 2
def slack : E := positive 3
def divisor : E := positive 4
def factor : E := positive 5
def index : E := positive 6
def clock : E := positive 7
def height : E := positive 8
def width : E := positive 9
def count : E := positive 10
def left : E := positive 11
def right : E := positive 12
def target : E := positive 13
def extra : E := positive 14

def base (p : Fin 4 → ℤ) : E := Expr.constant (p 0) * judge
def unit (p : Fin 4 → ℤ) : E := base p + 1
def window (p : Fin 4 → ℤ) : E := unit p - bound - slack
def horizontal (p : Fin 4 → ℤ) : E := width * unit p
def vertical (p : Fin 4 → ℤ) : E := height * (unit p * unit p * unit p)
def product (p : Fin 4 → ℤ) : E := horizontal p * vertical p
def gap : E := left + right
def length (p : Fin 4 → ℤ) : E := product p * gap * vertical p
def center (p : Fin 4 → ℤ) : E := gap * vertical p + left
def sum (p : Fin 4 → ℤ) : E := product p + vertical p
def weight (p : Fin 4 → ℤ) : E := 4 * sum p + 3
def delta (p : Fin 4 → ℤ) : E := sum p * sum p + weight p
def root (p : Fin 4 → ℤ) : E := horizontal p + sum p * center p + extra * weight p
def rank (p : Fin 4 → ℤ) : E :=
  (base p * (unit p - bound) + slack) * (unit p * unit p - 1) +
    (Expr.constant (p 2) + unit p * Expr.constant (p 3)) * judge
def carry (p : Fin 4 → ℤ) : E := product p * count + gap - rank p
def inner (p : Fin 4 → ℤ) : E := factor * factor * (center p * clock - rank p) - center p
def scale (p : Fin 4 → ℤ) : E := index * (root p * root p - 1)

def first (p : Fin 4 → ℤ) : E := root p * root p - delta p * (center p * center p) - 1
def second (p : Fin 4 → ℤ) : E := carry p * carry p - length p * (length p + gap) - 1
def third (p : Fin 4 → ℤ) : E :=
  (Expr.constant (p 1) + width) * window p + (unit p - bound) - divisor * base p - 1
def fourth (p : Fin 4 → ℤ) : E :=
  target * target - (scale p * scale p) * (target * target - inner p * inner p) - 1
def fifth (p : Fin 4 → ℤ) : E := delta p * (factor * factor) - scale p * scale p - delta p

def seed (p : Fin 4 → ℤ) : E :=
  first p * first p + second p * second p + third p * third p +
    fourth p * fourth p + fifth p * fifth p
end DiophantineConsistency.Sign14Readable
