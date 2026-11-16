import ApplicationTargets

/-!
# Finite divided-power arithmetic and polynomial ODE targets

The Leibniz target requests exactly N+1 coefficients of both inputs to return
N coefficients of their derivatives; undifferentiated factors are truncated.
No inverse factorial or division by a coefficient index occurs.
-/

namespace IPRAFramework.Hurwitz

open FiniteAlgebra

def choose : Nat → Nat → Nat
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k => match k with
    | 0 => 1
    | k + 1 => choose n k + choose n (k + 1)

theorem choose_succ_succ (n k : Nat) :
    choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl

def multiply (N : Nat) (a b : Jet N) : Jet N :=
  Vector.ofFn fun i =>
    ((List.range (i.val + 1)).map fun j =>
      Rat.ofInt (Int.ofNat (choose i.val j)) *
        a.toList.getD j 0 * b.toList.getD (i.val - j) 0).foldl (· + ·) 0

def ops (N : Nat) : RingOps (Jet N) :=
  { jetOps N with mul := multiply N }

def derivative (N : Nat) (a : Jet (N + 1)) : Jet N :=
  Vector.ofFn fun i => a.get i.succ

def LeibnizGoal : Prop :=
  ∀ N (a b : Jet (N + 1)),
    derivative N (multiply (N + 1) a b) =
      (ops N).add
        (multiply N (derivative N a) (jetTruncate N b))
        (multiply N (jetTruncate N a) (derivative N b))

/-- Variables 0 and 1 denote time and the scalar unknown, respectively. -/
def odeValue (N : Nat) (p : Polynomial Rat 2) (y : Jet N) : Jet N :=
  evaluate (ops N) (mapPolynomial (jetConstant N) p)
    (Vector.ofFn fun i : Fin 2 => if i.val = 0 then jetVariable N else y)

def odeStep (N : Nat) (p : Polynomial Rat 2) (y : Jet N) (k : Nat) : Jet N :=
  let coefficient := (odeValue N p y).toList.getD k 0
  Vector.ofFn fun i => if i.val = k + 1 then coefficient else y.get i

def odeIter (N : Nat) (p : Polynomial Rat 2) (initial : Rat) : Nat → Jet N
  | 0 => jetConstant N initial
  | k + 1 => odeStep N p (odeIter N p initial k) k

def odeProducer (N : Nat) (p : Polynomial Rat 2) (initial : Rat) : Jet N :=
  odeIter N p initial (N - 1)

def satisfiesODE (N : Nat) (p : Polynomial Rat 2) (initial : Rat) (y : Jet N) : Prop :=
  y.toList.getD 0 0 = initial ∧
    ∀ k, k + 1 < N →
      y.toList.getD (k + 1) 0 = (odeValue N p y).toList.getD k 0

def PolynomialODEGoal : Prop :=
  ∀ N, 0 < N → ∀ (p : Polynomial Rat 2) (initial : Rat),
    satisfiesODE N p initial (odeProducer N p initial) ∧
      ∀ y : Jet N, satisfiesODE N p initial y → y = odeProducer N p initial

def quadraticODE : Polynomial Rat 2 :=
  [{ coefficient := 1,
     exponents := Vector.ofFn fun i => if i.val = 1 then 2 else 0 }]

-- Executed exact coefficient diagnostic, not the universal ODE proof.
#eval decide ((odeProducer 8 quadraticODE 1).toList = [1, 1, 2, 6, 24, 120, 720, 5040])

end IPRAFramework.Hurwitz
