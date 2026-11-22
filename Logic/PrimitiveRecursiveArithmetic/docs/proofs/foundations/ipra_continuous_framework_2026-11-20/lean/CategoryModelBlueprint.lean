import Mathlib

/-!
# Completion and continuous formula evaluation: UNCOMPILED BLUEPRINT

This file defines host-level interfaces, algorithms, and proposition-valued
formalization obligations. It contains no `sorry` and no asserted theorem that
would pretend an unproved obligation has been discharged. These definitions
have not been compiled in the delivery environment.

An eventual host proof is NOT by itself an iPRA derivation. The final phase must
replace each rational relation by its numerator/positive-denominator encoding,
compile finite loops using quantifier-free Boolean invariants, and return
`Prf PRAAx` proof objects through the repository's interfaces.
-/

namespace ContinuousIPRA.CategoryModelBlueprint

def eps (n : Nat) : Rat := 1 / (2 : Rat) ^ n

structure RationalCore where
  valid : Nat → Bool
  dist : Nat → Nat → Rat
  nonneg : ∀ a b, valid a = true → valid b = true → 0 ≤ dist a b
  refl : ∀ a, valid a = true → dist a a = 0
  symm : ∀ a b, valid a = true → valid b = true → dist a b = dist b a
  triangle : ∀ a b c, valid a = true → valid b = true → valid c = true →
    dist a c ≤ dist a b + dist b c

-- A pseudometric is sufficient: the final equivalence identifies zero distance.
def Regular (A : RationalCore) (a : Nat → Nat) : Prop :=
  (∀ n, A.valid (a n) = true) ∧
  ∀ m n, A.dist (a m) (a n) ≤ eps m + eps n

def SameName (A : RationalCore) (a b : Nat → Nat) : Prop :=
  ∀ m n, A.dist (a m) (b n) ≤ eps m + eps n

def completionDiagonal (a : Nat → Nat → Nat) (n : Nat) : Nat :=
  a (n + 2) (n + 2)

def CompletionDiagonalObligation (A : RationalCore) : Prop :=
  ∀ a : Nat → Nat → Nat,
    (∀ r, Regular A (a r)) →
    (∀ r s m n,
      A.dist (a r m) (a s n) ≤ eps r + eps s + eps m + eps n) →
    Regular A (completionDiagonal a)

structure CoreMap (A B : RationalCore) where
  value : Nat → Nat → Nat
  modulus : Nat → Nat
  monotone : Monotone modulus
  regular : ∀ a, A.valid a = true → Regular B (value a)
  variation : ∀ a b k r s,
    A.valid a = true → A.valid b = true →
    A.dist a b ≤ eps (modulus k) →
    B.dist (value a r) (value b s) ≤ eps k + eps r + eps s

def extendName {A B : RationalCore} (F : CoreMap A B) (a : Nat → Nat)
    (n : Nat) : Nat :=
  F.value (a (F.modulus (n + 3) + n + 3)) (n + 3)

def ExtensionObligation (A B : RationalCore) : Prop :=
  ∀ (F : CoreMap A B) (a b : Nat → Nat),
    Regular A a → Regular A b →
    Regular B (extendName F a) ∧
      (SameName A a b → SameName B (extendName F a) (extendName F b))

structure DenseNets (A : RationalCore) where
  points : Nat → List Nat
  nonempty : ∀ K, points K ≠ []
  valid : ∀ K a, a ∈ points K → A.valid a = true
  select : Nat → Nat → Nat
  select_lt : ∀ K a, A.valid a = true → select K a < (points K).length
  cover : ∀ K a, A.valid a = true →
    A.dist a ((points K).getD (select K a) 0) ≤ eps K

def tupleDist (A : RationalCore) (xs ys : List Nat) : Rat :=
  (List.zipWith A.dist xs ys).foldl max 0

def validTuple (A : RationalCore) (xs : List Nat) : Prop :=
  ∀ x, x ∈ xs → A.valid x = true

structure AtomicData (A : RationalCore) where
  count : Nat
  arity : Nat → Nat
  value : Nat → Nat → List Nat → Rat
  lip : Nat → Nat
  err : Nat → Nat  -- 0 for exact atoms, 1 for error at most eps K
  inUnit : ∀ i K xs, i < count → xs.length = arity i → validTuple A xs →
    0 ≤ value i K xs ∧ value i K xs ≤ 1
  variation : ∀ i K K' xs ys,
    i < count → xs.length = arity i → ys.length = arity i →
    validTuple A xs → validTuple A ys →
    |value i K xs - value i K' ys| ≤
      (lip i : Rat) * tupleDist A xs ys + (err i : Rat) * (eps K + eps K')

inductive Formula where
  | atom (symbol : Nat) (variables : List Nat)
  | const (q : Rat)
  | compl (p : Formula)
  | min (p q : Formula)
  | max (p q : Formula)
  | mean (p q : Formula)
  | sub (p q : Formula)
  | inf (p : Formula)
  | sup (p : Formula)
  deriving Repr

-- Slot 0 is the most recently bound variable; `inf`/`sup` prepend a value.
def wellFormed {A : RationalCore} (S : AtomicData A) : Nat → Formula → Bool
  | v, .atom i xs => decide (i < S.count) &&
      decide (xs.length = S.arity i) && xs.all (fun j => decide (j < v))
  | _, .const q => decide (0 ≤ q ∧ q ≤ 1)
  | v, .compl p => wellFormed S v p
  | v, .min p q => wellFormed S v p && wellFormed S v q
  | v, .max p q => wellFormed S v p && wellFormed S v q
  | v, .mean p q => wellFormed S v p && wellFormed S v q
  | v, .sub p q => wellFormed S v p && wellFormed S v q
  | v, .inf p => wellFormed S (v + 1) p
  | v, .sup p => wellFormed S (v + 1) p

def weights {A : RationalCore} (S : AtomicData A) : Formula → Nat × Nat
  | .atom i _ => (S.lip i, S.err i)
  | .const _ => (0, 0)
  | .compl p => weights S p
  | .min p q =>
      (max (weights S p).1 (weights S q).1,
       max (weights S p).2 (weights S q).2)
  | .max p q =>
      (max (weights S p).1 (weights S q).1,
       max (weights S p).2 (weights S q).2)
  | .mean p q =>
      (max (weights S p).1 (weights S q).1,
       max (weights S p).2 (weights S q).2)
  | .sub p q =>
      (2 * max (weights S p).1 (weights S q).1,
       2 * max (weights S p).2 (weights S q).2)
  | .inf p => ((weights S p).1, (weights S p).2 + (weights S p).1)
  | .sup p => ((weights S p).1, (weights S p).2 + (weights S p).1)

def evaluate {A : RationalCore} (S : AtomicData A) (N : DenseNets A) :
    Formula → Nat → List Nat → Rat
  | .atom i xs, K, env => S.value i K (xs.map (fun j => env.getD j 0))
  | .const q, _, _ => q
  | .compl p, K, env => 1 - evaluate S N p K env
  | .min p q, K, env => min (evaluate S N p K env) (evaluate S N q K env)
  | .max p q, K, env => max (evaluate S N p K env) (evaluate S N q K env)
  | .mean p q, K, env => (evaluate S N p K env + evaluate S N q K env) / 2
  | .sub p q, K, env => max (evaluate S N p K env - evaluate S N q K env) 0
  | .inf p, K, env =>
      (N.points K).foldl (fun best x => min best (evaluate S N p K (x :: env))) 1
  | .sup p, K, env =>
      (N.points K).foldl (fun best x => max best (evaluate S N p K (x :: env))) 0

/-- Theorem model-comparison in the paper: host-level target, NOT a proved theorem. -/
def FiniteComparisonObligation (A : RationalCore) (S : AtomicData A)
    (N : DenseNets A) : Prop :=
  ∀ p K K' xs ys,
    xs.length = ys.length → wellFormed S xs.length p = true →
    validTuple A xs → validTuple A ys →
    |evaluate S N p K xs - evaluate S N p K' ys| ≤
      ((weights S p).1 : Rat) * tupleDist A xs ys +
      ((weights S p).2 : Rat) * (eps K + eps K')

/-!
Formalization order and exact object-theory bridge:

1. Rational arithmetic: guarded positive denominators, abs-difference,
   max, finite min/max, powers of two, and rational separation.
2. `Regular` and `SameName`: arithmetical formulas (with Trace/Eval relations
   in the coded-name reading), not decidable predicates on complete names.
3. Prove `CompletionDiagonalObligation` and `ExtensionObligation` in host Lean.
   Construct parallel `Prf PRAAx` derivations of every rational estimate.
4. Define coded syntax, arity checking, finite net tables, environment tables,
   and the evaluator's state transitions as fixed PR definitions.
5. Prove finite argmin/argmax perturbation using the certified net selector.
6. Compile the bottom-up table invariant: for every bounded pair of environments
   and every already processed syntax node, the rational comparison holds.
   Booleanize this invariant; apply only quantifier-free object induction.
7. Export the resulting sentence as a `Prf PRAAx` derivation. Instantiate the
   actual atomic and net-selector derivations; do not treat host record fields
   as object proofs.
8. Prove semantic adequacy separately: completed model values are the limits
   of these regular names. This metatheorem is not reflection for arbitrary
   accepted iPRA proofs.
9. Add two-structure error coefficients A_phi/B_phi and their analogous table
   comparison. Completion invariance follows by setting atomic distortion to
   zero and using density tolerances tending to zero.

No library-wide cartesian-closure or model-compactness theorem is presumed.
Relational totality alone does not provide the variable-length batch of atom
traces needed by evaluate: that is an explicit additional input/obligation.
-/

end ContinuousIPRA.CategoryModelBlueprint
