import Std

/-!
# Complete, executable definitions for the rational enumeration target

This file defines programs and proposition-valued targets. It deliberately
does not assert `EnumerationGoal` as a theorem. Matrices are stored by columns:
`action[k][j][i]` is entry i,j of the integral matrix for coordinate k.
Polynomial lists can contain repeated monomials and zero coefficients;
the checker compares their collected coefficients, not their list order.
-/

namespace FiniteAlgebra.Targets

structure Monomial (n : Nat) where
  coefficient : Rat
  exponents : Vector Nat n
  deriving DecidableEq

abbrev Polynomial (n : Nat) := List (Monomial n)

def constant (n : Nat) (a : Rat) : Polynomial n :=
  [{ coefficient := a, exponents := Vector.replicate n 0 }]

def variablePolynomial {n : Nat} (k : Fin n) : Polynomial n :=
  [{ coefficient := 1, exponents := Vector.ofFn (fun i => if i = k then 1 else 0) }]

def scale {n : Nat} (a : Rat) (P : Polynomial n) : Polynomial n :=
  P.map (fun t => { t with coefficient := a * t.coefficient })

def sub {n : Nat} (P Q : Polynomial n) : Polynomial n := P ++ scale (-1) Q

def mul {n : Nat} (P Q : Polynomial n) : Polynomial n :=
  P.flatMap (fun t => Q.map (fun u => {
    coefficient := t.coefficient * u.coefficient,
    exponents := Vector.ofFn (fun i => t.exponents[i] + u.exponents[i]) }))

def coefficientAt {n : Nat} (P : Polynomial n) (e : Vector Nat n) : Rat :=
  (P.map (fun t => if t.exponents = e then t.coefficient else 0)).foldl (· + ·) 0

def polynomialEq {n : Nat} (P Q : Polynomial n) : Bool :=
  (P ++ Q).all (fun t => decide (coefficientAt P t.exponents = coefficientAt Q t.exponents))

def monomialValue {n : Nat} (p : List Rat) (t : Monomial n) : Rat :=
  t.coefficient * ((t.exponents.toList.zip p).map (fun (e, x) => x ^ e)).foldl (· * ·) 1

def evaluate {n : Nat} (P : Polynomial n) (p : List Rat) : Rat :=
  (P.map (monomialValue p)).foldl (· + ·) 0

def linearCombination {n d : Nat} (c : Vector Rat d)
    (B : Vector (Polynomial n) d) : Polynomial n :=
  (c.toList.zip B.toList).flatMap (fun (a, b) => scale a b)

def idealCombination {n s : Nat} (H F : Vector (Polynomial n) s) : Polynomial n :=
  (H.toList.zip F.toList).flatMap (fun (h, f) => mul h f)

structure Certificate (n s d : Nat) where
  basis : Vector (Polynomial n) d
  unitCoefficients : Vector Rat d
  unitWitness : Vector (Polynomial n) s
  delta : Vector Nat n
  action : Vector (Vector (Vector Int d) d) n
  actionWitness : Vector (Vector (Vector (Polynomial n) s) d) n

def unitResidual {n s d : Nat} (C : Certificate n s d) : Polynomial n :=
  sub (constant n 1) (linearCombination C.unitCoefficients C.basis)

def actionResidual {n s d : Nat} (C : Certificate n s d)
    (k : Fin n) (j : Fin d) : Polynomial n :=
  sub (scale (C.delta[k] : Rat) (mul (variablePolynomial k) C.basis[j]))
    (linearCombination (C.action[k][j].map (fun (z : Int) => (z : Rat))) C.basis)

def certificateOK {n s d : Nat} (F : Vector (Polynomial n) s)
    (C : Certificate n s d) : Bool :=
  decide (0 < d) && C.delta.toList.all (fun q => decide (0 < q)) &&
    polynomialEq (unitResidual C) (idealCombination C.unitWitness F) &&
    (List.finRange n).all (fun k => (List.finRange d).all (fun j =>
      polynomialEq (actionResidual C k j) (idealCombination C.actionWitness[k][j] F)))

def columnBound {d : Nat} (A : Vector (Vector Int d) d) : Nat :=
  (A.toList.map (fun column => (column.toList.map Int.natAbs).foldl (· + ·) 0)).foldl max 0

def coordinateGrid (delta bound : Nat) : List Rat :=
  (List.range (2 * bound + 1)).map (fun j =>
    (((Int.ofNat j - Int.ofNat bound) : Int) : Rat) / (delta : Rat))

def cartesian : List (List Rat) → List (List Rat)
  | [] => [[]]
  | xs :: xss => xs.flatMap (fun x => (cartesian xss).map (fun tail => x :: tail))

def grid {n s d : Nat} (C : Certificate n s d) : List (List Rat) :=
  cartesian ((List.finRange n).map (fun k => coordinateGrid C.delta[k] (columnBound C.action[k])))

def zeroTest {n s : Nat} (F : Vector (Polynomial n) s) (p : List Rat) : Bool :=
  decide (p.length = n) && F.toList.all (fun f => decide (evaluate f p = 0))

def enumerate {n s d : Nat} (F : Vector (Polynomial n) s)
    (C : Certificate n s d) : List (List Rat) :=
  if certificateOK F C then (grid C).filter (zeroTest F) else []

/-- Finite coefficient checking implies equality at every well-formed point. -/
def EvaluationTransportGoal : Prop :=
  ∀ n (P Q : Polynomial n) (p : Vector Rat n),
    polynomialEq P Q = true → evaluate P p.toList = evaluate Q p.toList

/-- The certificate's identities evaluate to the unit and action laws. -/
def CertificateSoundnessGoal : Prop :=
  ∀ n s d (F : Vector (Polynomial n) s) (C : Certificate n s d) (p : Vector Rat n),
    certificateOK F C = true → zeroTest F p.toList = true →
    evaluate (unitResidual C) p.toList = 0 ∧
      ∀ k j, evaluate (actionResidual C k j) p.toList = 0

/-- Every rational zero is contained in the explicitly computable finite grid. -/
def GridCompletenessGoal : Prop :=
  ∀ n s d (F : Vector (Polynomial n) s) (C : Certificate n s d) (p : Vector Rat n),
    certificateOK F C = true → zeroTest F p.toList = true → p.toList ∈ grid C

/-- The desired full specification, not a theorem supplied by this file. -/
def EnumerationGoal : Prop :=
  ∀ n s d (F : Vector (Polynomial n) s) (C : Certificate n s d) (p : Vector Rat n),
    certificateOK F C = true →
      (p.toList ∈ enumerate F C ↔ zeroTest F p.toList = true)

/-- Once grid completeness is proved, finite filtering finishes the theorem. -/
theorem enumeration_of_gridCompleteness (h : GridCompletenessGoal) : EnumerationGoal := by
  intro n s d F C p hc
  simp only [enumerate, hc, ↓reduceIte, List.mem_filter]
  exact ⟨fun hp => hp.2, fun hz => ⟨h n s d F C p hc hz, hz⟩⟩

end FiniteAlgebra.Targets

#print axioms FiniteAlgebra.Targets.enumeration_of_gridCompleteness
