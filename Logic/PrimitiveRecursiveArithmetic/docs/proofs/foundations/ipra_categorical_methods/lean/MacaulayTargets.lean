/-
Uncompiled Mathlib-oriented specification, not a completed formalization.
No declaration below asserts an unproved theorem as an axiom or uses sorry.
The executable producer is in macaulay.py; the paper gives its finite-loop
proof. A definition whose value is a Prop is an outstanding target.
This file concerns HOST semantics. Reifying these operations as PR symbols
and constructing Prf PRAAx derivations is a separate final stage.
-/
import Mathlib

namespace IPRAMacaulay

abbrev Poly (r : ℕ) := MvPolynomial (Fin r) ℚ
abbrev Vec (n : ℕ) := Fin n → ℚ

def exponent (r D z : ℕ) : Fin r → ℕ :=
  fun i => (z / (D + 1) ^ i.val) % (D + 1)

def total (r : ℕ) (a : Fin r → ℕ) : ℕ := ∑ i, a i

def exponents (r D : ℕ) : List (Fin r → ℕ) :=
  (List.range ((D + 1) ^ r)).map (exponent r D)

def monomial {r : ℕ} (a : Fin r → ℕ) : Poly r :=
  ∏ i, (MvPolynomial.X i) ^ a i

def lowMonomials (r d : ℕ) : List (Poly r) :=
  ((exponents r d).filter (fun a => decide (total r a ≤ d))).map monomial

def borderMonomials (r d : ℕ) : List (Poly r) :=
  ((exponents r (d + 1)).filter
    (fun a => decide (total r a = d + 1))).map monomial

def generatorMultiples {r s : ℕ} (D : ℕ) (f : Fin s → Poly r) : List (Poly r) :=
  (List.finRange s).flatMap fun i =>
    if (f i).totalDegree ≤ D then
      (((exponents r (D - (f i).totalDegree)).filter
        (fun a => decide (total r a ≤ D - (f i).totalDegree))).map
          (fun a => monomial a * f i))
    else []

def sourceColumns {r s : ℕ} (d D : ℕ) (f : Fin s → Poly r) : List (Poly r) :=
  lowMonomials r d ++ generatorMultiples D f

def coefficient {r : ℕ} (a : Fin r → ℕ) (p : Poly r) : ℚ :=
  p.coeff (Finsupp.equivFunOnFinite.symm a)

def coefficientVector {r : ℕ} (D : ℕ) (p : Poly r) : Vec ((D + 1) ^ r) :=
  fun i => coefficient (exponent r D i.val) p

def macaulayMatrix {r s : ℕ} (d D : ℕ) (f : Fin s → Poly r) :
    Matrix (Fin ((D + 1) ^ r)) (Fin (sourceColumns d D f).length) ℚ :=
  fun i j => coefficientVector D ((sourceColumns d D f).get j) i

def ClosureAccepted {r s : ℕ} (d D : ℕ) (f : Fin s → Poly r) : Prop :=
  d + 1 ≤ D ∧ ∀ b ∈ borderMonomials r d,
    ∃ c : Vec (sourceColumns d D f).length,
      (macaulayMatrix d D f).mulVec c = coefficientVector D b

def LinearSolveCorrect {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) (v : Vec m)
    (answer : Sum (Vec n) (Vec m)) : Prop :=
  match answer with
  | .inl c => A.mulVec c = v
  | .inr u => Matrix.vecMul u A = 0 ∧ (∑ i, u i * v i) ≠ 0

def SolverTarget
    (solve : {m n : ℕ} → Matrix (Fin m) (Fin n) ℚ → Vec m → Sum (Vec n) (Vec m)) :
    Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ) (v : Vec m),
    LinearSolveCorrect A v (solve A v)

structure ActionData (r s N : ℕ) where
  generators : Fin N → Poly r
  constantIndex : Fin N
  matrix : Fin r → Matrix (Fin N) (Fin N) ℚ
  witnesses : Fin r → Fin N → Fin s → Poly r

def CheckAction {r s N : ℕ} (f : Fin s → Poly r) (a : ActionData r s N) : Prop :=
  a.generators a.constantIndex = 1 ∧
  ∀ k j, MvPolynomial.X k * a.generators j -
      ∑ i, MvPolynomial.C (a.matrix k i j) * a.generators i =
    ∑ l, a.witnesses k j l * f l

def CommonZero {r s : ℕ} (f : Fin s → Poly r) (p : Fin r → ℚ) : Prop :=
  ∀ i, MvPolynomial.eval p (f i) = 0

def EvaluationVector {r s N : ℕ} (a : ActionData r s N) (p : Fin r → ℚ) : Vec N :=
  fun j => MvPolynomial.eval p (a.generators j)

def EvaluationTarget : Prop :=
  ∀ (r s N : ℕ) (f : Fin s → Poly r) (a : ActionData r s N) (p : Fin r → ℚ),
    CheckAction f a → CommonZero f p →
      EvaluationVector a p a.constantIndex = 1 ∧
      ∀ k, Matrix.vecMul (EvaluationVector a p) (a.matrix k) =
        fun j => p k * EvaluationVector a p j

def DenominatorGridTarget : Prop :=
  ∀ (N : ℕ) (M : Matrix (Fin N) (Fin N) ℚ) (Δ R : ℕ)
    (v : Vec N) (x : ℚ),
    0 < Δ → v ≠ 0 → Matrix.vecMul v M = (fun j => x * v j) →
    (∀ i j, ∃ z : ℤ, (Δ : ℚ) * M i j = z) →
    (∀ j, ∑ i, |(Δ : ℚ) * M i j| ≤ (R : ℚ)) →
    ∃ z : ℤ, |z| ≤ (R : ℤ) ∧ x = (z : ℚ) / Δ

def CompleteList {r s : ℕ} (f : Fin s → Poly r) (L : List (Fin r → ℚ)) : Prop :=
  L.Nodup ∧ ∀ p, p ∈ L ↔ CommonZero f p

/- Remaining implementation order:
1. Prove coefficient encoding/exponent enumeration and bounded array lemmas.
2. Implement the supplied bounded RREF algorithm and prove SolverTarget from
   the row-operation invariant, carrying an inverse operation log.
3. Retain generator labels (i, alpha) alongside generatorMultiples; use solved
   column coefficients to assemble ActionData and prove CheckAction.
4. Prove EvaluationTarget by finite sums and polynomial evaluation.
5. Primitive-scale v using a product of denominators and gcd; Bezout proves
   integral eigenvalues. A finite maximum proves DenominatorGridTarget.
6. Implement the mixed-radix integer grid and exact filter; prove CompleteList.
7. Replace abstract rational/polynomial structures by coded natural-number
   lists and PR terms; Booleanize all bounded invariants. Construct the
   corresponding Prf PRAAx proofs. The host theorems alone do not provide this.

Crucial scope: ClosureAccepted is a finite linear-algebra criterion at the
given d,D. No declaration promises that increasing them will terminate for
all inputs, nor that a finite rational point set implies acceptance.
-/

end IPRAMacaulay
