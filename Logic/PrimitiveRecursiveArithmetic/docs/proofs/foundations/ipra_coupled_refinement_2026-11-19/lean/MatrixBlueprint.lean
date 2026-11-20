import SmallGainBlueprint

/-!
# Finite Neumann inverse: definitions and named proof targets

Std-only host definitions. Target propositions below are not asserted to hold
by a Lean proof in this file, and are not asserted as axioms. The report gives
their finite mathematical proofs and the route to literal Prf PRAAx proofs.
-/

namespace CoupledIPRA.Matrices

def mzero {d : Nat} : Mat d := fun _ _ => 0
def ident {d : Nat} : Mat d := fun i j => if i = j then 1 else 0
def madd {d : Nat} (A B : Mat d) : Mat d := fun i j => A i j + B i j
def msub {d : Nat} (A B : Mat d) : Mat d := fun i j => A i j - B i j
def mmul {d : Nat} (A B : Mat d) : Mat d :=
  fun i j => sumQ (fun k => A i k * B k j)

def mpow {d : Nat} (K : Mat d) : Nat → Mat d
  | 0 => ident
  | n + 1 => mmul K (mpow K n)

def neumann {d : Nat} (K : Mat d) : Nat → Mat d
  | 0 => mzero
  | n + 1 => madd (neumann K n) (mpow K n)

def matrixNorm {d : Nat} (w : Vec d) (M : Mat d) : Rat :=
  maxZeroQ (fun i => sumQ (fun j => absQ (M i j) * w j) / w i)

def positiveWeights {d : Nat} (w : Vec d) : Prop := ∀ i, 0 < w i
def qOf (s : Nat) : Rat := 1 - 1 / (s : Rat)

def inverseSteps (s H k : Nat) : Nat := s * (k + H + 2)
def inverseName {d : Nat} (K : Mat d) (s H k : Nat) : Mat d :=
  neumann K (inverseSteps s H k)

def MatrixNormTarget : Prop :=
  ∀ {d} (w : Vec d), 0 < d → positiveWeights w →
    matrixNorm w ident = 1 ∧
    (∀ A, 0 ≤ matrixNorm w A) ∧
    (∀ A B, matrixNorm w (madd A B) ≤ matrixNorm w A + matrixNorm w B) ∧
    (∀ A B, matrixNorm w (mmul A B) ≤ matrixNorm w A * matrixNorm w B) ∧
    (∀ A i j, absQ (A i j) ≤ (w i / w j) * matrixNorm w A)

def FiniteNeumannIdentityTarget : Prop :=
  ∀ {d} (K : Mat d) n,
    mmul (msub ident K) (neumann K n) = msub ident (mpow K n) ∧
    mmul (neumann K n) (msub ident K) = msub ident (mpow K n)

def FiniteNeumannBoundsTarget : Prop :=
  ∀ {d} (w : Vec d) (K : Mat d) (s : Nat),
    0 < d → positiveWeights w → 1 ≤ s → matrixNorm w K ≤ qOf s →
    (∀ n, matrixNorm w (neumann K n) ≤ (s : Rat)) ∧
    (∀ n m, n ≤ m → matrixNorm w (msub (neumann K m) (neumann K n)) ≤
      (s : Rat) * (qOf s)^n)

def InverseNameTarget : Prop :=
  ∀ {d} (w : Vec d) (K : Mat d) (s H : Nat),
    0 < d → positiveWeights w → 1 ≤ s → matrixNorm w K ≤ qOf s →
    (s : Rat) ≤ (2 : Rat)^H →
    (∀ k l, matrixNorm w (msub (inverseName K s H k) (inverseName K s H l)) ≤
      dyadic (min k l + 2)) ∧
    (∀ k, matrixNorm w (msub ident (mmul (msub ident K) (inverseName K s H k))) ≤
      dyadic (k + 2)) ∧
    (∀ k, matrixNorm w (msub ident (mmul (inverseName K s H k) (msub ident K))) ≤
      dyadic (k + 2))

def FiniteInverseStabilityTarget : Prop :=
  ∀ {d} (w : Vec d) (K L : Mat d) (s : Nat),
    0 < d → positiveWeights w → 1 ≤ s →
    matrixNorm w K ≤ qOf s → matrixNorm w L ≤ qOf s → ∀ n,
      matrixNorm w (msub (neumann K n) (neumann L n)) ≤
        (s : Rat)^2 * matrixNorm w (msub K L)

def inverseDefect {d : Nat} (D B : Mat d) : Mat d := msub ident (mmul B D)
def preconditionedName {d : Nat} (D B : Mat d) (s H k : Nat) : Mat d :=
  mmul (inverseName (inverseDefect D B) s H k) B

def InvertiblePreconditioner {d : Nat} (B Binv : Mat d) : Prop :=
  mmul B Binv = ident ∧ mmul Binv B = ident

def PreconditionedResidualTarget : Prop :=
  ∀ {d} (w : Vec d) (D B Binv : Mat d) (s H : Nat),
    0 < d → positiveWeights w → 1 ≤ s → InvertiblePreconditioner B Binv →
    matrixNorm w (inverseDefect D B) ≤ qOf s → ∀ k,
      matrixNorm w (msub ident (mmul (preconditionedName D B s H k) D)) ≤
        (qOf s)^(inverseSteps s H k) ∧
      matrixNorm w (msub ident (mmul D (preconditionedName D B s H k))) ≤
        matrixNorm w Binv * matrixNorm w B * (qOf s)^(inverseSteps s H k)

#check matrixNorm
#check inverseName
#check FiniteNeumannIdentityTarget
#check InverseNameTarget
#check PreconditionedResidualTarget

end CoupledIPRA.Matrices
