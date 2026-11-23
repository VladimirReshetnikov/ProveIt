import Std

/-!
Natural-number computations for the finite coefficients in Ramanujan's
inequality. These two small identities belong to the host language. The
bounds for the analytic remainders are proved in the accompanying report.
-/
namespace PrimeCounting.Growth

def fac : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fac n

/-- Pascal recursion with a structurally decreasing row index. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _+1 => 0
  | n+1, j+1 => choose n (j+1) + choose n j

def sumThrough (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | j+1 => sumThrough f j + f (j+1)

def leftCoeff (d : Nat) : Nat :=
  sumThrough (fun j => fac j * fac (d-j)) d

def rightCoeff (d : Nat) : Nat :=
  sumThrough (fun j => choose d j * fac j) d

theorem square_coefficients :
    (List.range 5).map leftCoeff = [1, 2, 5, 16, 64] := rfl

theorem shifted_coefficients :
    (List.range 5).map rightCoeff = [1, 2, 5, 16, 65] := rfl

end PrimeCounting.Growth
