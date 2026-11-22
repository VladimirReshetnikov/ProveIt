import ObservableAnalysis.Budget
import ObservableAnalysis.FiniteMinimum
import ObservableAnalysis.Neumann

/-!
# Explicit specifications for the remaining formalization

This module supplies definitions, not claimed proofs of completion, measure
theory, analytic functional calculus, or an iPRA interpretation theorem.
Structures whose fields are laws are *obligations to implement*, not new
axioms or automatically available instances.

In particular, `PRCode.eval` is a Lean metatheoretic evaluator.  It is NOT
a primitive-recursive universal evaluator, and it is NEVER introduced as
one function symbol of iPRA.  Each externally fixed `PRCode` instead expands
to its own primitive-recursive definition and finite defining equations.
-/

namespace ObservableAnalysis.Blueprint

/-- A finite tuple of natural inputs.  Its arity is fixed in each recipe. -/
abbrev Args (n : Nat) := Fin n → Nat

def cons {n : Nat} (a : Nat) (xs : Args n) : Args (n + 1) := Fin.cases a xs

/-- Ordinary primitive-recursive syntax, indexed by input arity. -/
inductive PRCode : Nat → Type
  | zero (n : Nat) : PRCode n
  | successor : PRCode 1
  | projection {n : Nat} (i : Fin n) : PRCode n
  | composition {n m : Nat} (outer : PRCode m) (inner : Fin m → PRCode n) : PRCode n
  | recursion {n : Nat} (base : PRCode n) (step : PRCode (n + 2)) : PRCode (n + 1)

/--
Metatheoretic interpretation of a code.  The recursion argument is first;
the step inputs are `(iteration index, previous value, remaining inputs)`.
The uniform evaluator itself is not asserted to be primitive recursive.
-/
def PRCode.eval : {n : Nat} → PRCode n → Args n → Nat
  | _, .zero _, _ => 0
  | _, .successor, xs => xs 0 + 1
  | _, .projection i, xs => xs i
  | _, .composition outer inner, xs => outer.eval (fun i => (inner i).eval xs)
  | _, .recursion base step, xs =>
      Nat.rec (base.eval (fun i => xs i.succ))
        (fun k value => step.eval (cons k (cons value (fun i => xs i.succ)))) (xs 0)

def unary (f : PRCode 1) (x : Nat) : Nat := f.eval (fun _ => x)

def binary (f : PRCode 2) (x y : Nat) : Nat := f.eval (cons x (cons y (fun i => Fin.elim0 i)))

def epsilon (n : Nat) : Rat := 1 / (2 : Rat) ^ n

/--
Required rational-code module.  A concrete normalized signed numerator /
positive denominator encoding must implement these fields and prove laws.
No instance is supplied by this blueprint.
-/
structure RationalCodes where
  decode : Nat → Rat
  zeroCode : Nat
  oneCode : Nat
  addCode : PRCode 2
  mulCode : PRCode 2
  negCode : PRCode 1
  leCode : PRCode 2
  zero_correct : decode zeroCode = 0
  one_correct : decode oneCode = 1
  add_correct : ∀ a b, decode (binary addCode a b) = decode a + decode b
  mul_correct : ∀ a b, decode (binary mulCode a b) = decode a * decode b
  neg_correct : ∀ a, decode (unary negCode a) = -decode a
  le_correct : ∀ a b, binary leCode a b = 1 ↔ decode a ≤ decode b

structure MetricData (Q : RationalCodes) where
  admissibleCode : PRCode 1
  distanceCode : PRCode 2

def MetricData.Valid {Q : RationalCodes} (X : MetricData Q) (a : Nat) : Prop :=
  unary X.admissibleCode a = 1

def MetricData.distance {Q : RationalCodes} (X : MetricData Q) (a b : Nat) : Rat :=
  Q.decode (binary X.distanceCode a b)

/-- A pseudometric suffices; separated equality is introduced only at completion. -/
structure MetricLaws {Q : RationalCodes} (X : MetricData Q) : Prop where
  nonnegative : ∀ a b, X.Valid a → X.Valid b → 0 ≤ X.distance a b
  reflexive : ∀ a, X.Valid a → X.distance a a = 0
  symmetric : ∀ a b, X.Valid a → X.Valid b → X.distance a b = X.distance b a
  triangle : ∀ a b c, X.Valid a → X.Valid b → X.Valid c →
    X.distance a c ≤ X.distance a b + X.distance b c

/-- A represented name is one fixed unary recipe, not an arbitrary internal function. -/
structure Name where
  approximation : PRCode 1

def Name.at (x : Name) (n : Nat) : Nat := unary x.approximation n

structure RegularName {Q : RationalCodes} (X : MetricData Q) (x : Name) : Prop where
  admissible : ∀ n, X.Valid (x.at n)
  regular : ∀ m n, X.distance (x.at m) (x.at n) ≤ epsilon m + epsilon n

/-- An explicit schedule is data, and its correctness remains a separate obligation. -/
structure EqualitySchedule {Q : RationalCodes} (X : MetricData Q) (x y : Name) where
  schedule : PRCode 1
  correct : ∀ k n, unary schedule k ≤ n → X.distance (x.at n) (y.at n) ≤ epsilon k

structure ModulatedMap {Q : RationalCodes} (X Y : MetricData Q) where
  mapCode : PRCode 1
  modulusCode : PRCode 1
  map_admissible : ∀ a, X.Valid a → Y.Valid (unary mapCode a)
  continuity : ∀ k a b, X.Valid a → X.Valid b →
    X.distance a b ≤ epsilon (unary modulusCode k) →
      Y.distance (unary mapCode a) (unary mapCode b) ≤ epsilon k

/-- Finite nets include a bounded cardinality recipe and a bounded point selector. -/
structure FiniteNetData {Q : RationalCodes} (X : MetricData Q) where
  sizeCode : PRCode 1
  pointCode : PRCode 2
  size_positive : ∀ k, 0 < unary sizeCode k
  admissible : ∀ k i, i < unary sizeCode k → X.Valid (binary pointCode k i)
  cover : ∀ k a, X.Valid a →
    ∃ i, i < unary sizeCode k ∧ X.distance a (binary pointCode k i) ≤ epsilon k

/- `cover` above is a specification.  For an internal iPRA producer use a
   bounded least-index scan over the supplied finite net.  Its comparison
   predicate and iteration bound must be fixed PR recipes. -/

/-- A simple function on a supplied finite disjoint partition. -/
structure SimpleData (Q : RationalCodes) where
  cells : Nat
  weightCode : PRCode 1
  valueCode : PRCode 1

def SimpleData.weight {Q : RationalCodes} (s : SimpleData Q) (i : Nat) : Rat :=
  Q.decode (unary s.weightCode i)

def SimpleData.value {Q : RationalCodes} (s : SimpleData Q) (i : Nat) : Rat :=
  Q.decode (unary s.valueCode i)

def SimpleData.integral {Q : RationalCodes} (s : SimpleData Q) : Rat :=
  sumQ (fun i => s.weight i * s.value i) s.cells

def SimpleData.l1norm {Q : RationalCodes} (s : SimpleData Q) : Rat :=
  sumQ (fun i => s.weight i * (s.value i).abs) s.cells

def SimpleData.NonnegativeWeights {Q : RationalCodes} (s : SimpleData Q) : Prop :=
  ∀ i, i < s.cells → 0 ≤ s.weight i

/--
An infinite summation assertion is replaced by inequalities for *all finite
tails*, with a fixed PR index schedule.  This is the intended proof boundary
for L1 limits and normed-algebra power series.
-/
structure MajorantTail (Q : RationalCodes) where
  termCode : PRCode 1
  scheduleCode : PRCode 1
  nonnegative : ∀ i, 0 ≤ Q.decode (unary termCode i)
  finite_tail : ∀ k start length, unary scheduleCode k ≤ start →
    sumQ (fun j => Q.decode (unary termCode (start + j))) length ≤ epsilon k

/--
Finite formulas for a compact continuous structure; atom evaluators,
connective moduli and quantifier nets are separate parameters.  Quantifiers
are evaluated by bounded minima/maxima only after those parameters are given.
-/
inductive ContinuousFormula
  | atom (symbol : Nat) (variables : List Nat)
  | rationalConstant (code : Nat)
  | oneMinus (p : ContinuousFormula)
  | truncatedSub (p q : ContinuousFormula)
  | infimum (boundVar : Nat) (p : ContinuousFormula)
  | supremum (boundVar : Nat) (p : ContinuousFormula)

/-- Certificate data accepted by the proved finite budget verifier. -/
structure BudgetCertificate where
  vertices : Nat
  error : Nat → Rat
  localError : Nat → Rat
  sinkWeight : Nat → Rat
  reverseWeight : Nat → Rat
  amplification : Nat → Nat → Rat
  error_nonnegative : ∀ u, u < vertices → 0 ≤ error u
  weight_nonnegative : ∀ v, v < vertices → 0 ≤ reverseWeight v
  local_bound : ∀ v, v < vertices →
    error v ≤ localError v + sumQ (fun u => amplification v u * error u) vertices
  balance : ∀ u, u < vertices →
    sinkWeight u + sumQ (fun v => reverseWeight v * amplification v u) vertices ≤ reverseWeight u

/-- A completed bridge from the specification record to the finite kernel. -/
theorem BudgetCertificate.sound (C : BudgetCertificate) :
    sumQ (fun u => C.sinkWeight u * C.error u) C.vertices ≤
      sumQ (fun v => C.reverseWeight v * C.localError v) C.vertices :=
  weighted_budget_supersolution C.vertices C.error C.localError C.sinkWeight
    C.reverseWeight C.amplification C.error_nonnegative C.weight_nonnegative
    C.local_bound C.balance

#print axioms PRCode.eval
#print axioms BudgetCertificate.sound

end ObservableAnalysis.Blueprint
