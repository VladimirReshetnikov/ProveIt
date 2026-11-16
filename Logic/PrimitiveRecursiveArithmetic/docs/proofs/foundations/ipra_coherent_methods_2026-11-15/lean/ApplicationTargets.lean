import Std

/-!
# Executable finite algebra and precise lifting targets

The finite-array algorithms are definitions.  The named `...Goal : Prop`
declarations are *unproved targets*, not axioms.  `RingLaws` and
`FiltrationLaws` enumerate the local hypotheses completely; no field assumes
the lifting conclusion.  Uniform PR presentation and object-iPRA proofs of
these laws are separate requirements documented in FORMALIZATION.md.
-/

namespace IPRAFramework.FiniteAlgebra

structure RingOps (R : Type) where
  zero : R
  one : R
  add : R → R → R
  neg : R → R
  mul : R → R → R

structure RingLaws {R : Type} (o : RingOps R) : Prop where
  add_assoc : ∀ x y z, o.add (o.add x y) z = o.add x (o.add y z)
  add_comm : ∀ x y, o.add x y = o.add y x
  zero_add : ∀ x, o.add o.zero x = x
  neg_add : ∀ x, o.add (o.neg x) x = o.zero
  mul_assoc : ∀ x y z, o.mul (o.mul x y) z = o.mul x (o.mul y z)
  mul_comm : ∀ x y, o.mul x y = o.mul y x
  one_mul : ∀ x, o.mul o.one x = x
  mul_add : ∀ x y z, o.mul x (o.add y z) = o.add (o.mul x y) (o.mul x z)

def sub {R : Type} (o : RingOps R) (x y : R) : R := o.add x (o.neg y)
def sum {R : Type} (o : RingOps R) (xs : List R) : R := xs.foldl o.add o.zero

def natCast {R : Type} (o : RingOps R) : Nat → R
  | 0 => o.zero
  | n + 1 => o.add (natCast o n) o.one

def power {R : Type} (o : RingOps R) (x : R) : Nat → R
  | 0 => o.one
  | n + 1 => o.mul (power o x n) x

abbrev Point (R : Type) (d : Nat) := Vector R d
abbrev Matrix (R : Type) (d : Nat) := Vector (Vector R d) d

structure Monomial (R : Type) (d : Nat) where
  coefficient : R
  exponents : Vector Nat d

abbrev Polynomial (R : Type) (d : Nat) := List (Monomial R d)
abbrev System (R : Type) (d : Nat) := Vector (Polynomial R d) d

def evalMonomial {R : Type} {d : Nat} (o : RingOps R)
    (t : Monomial R d) (x : Point R d) : R :=
  (List.ofFn fun i : Fin d => (x.get i, t.exponents.get i)).foldl
    (fun a xe => o.mul a (power o xe.1 xe.2)) t.coefficient

def evaluate {R : Type} {d : Nat} (o : RingOps R)
    (p : Polynomial R d) (x : Point R d) : R :=
  sum o (p.map fun t => evalMonomial o t x)

def partialDerivative {R : Type} {d : Nat} (o : RingOps R)
    (p : Polynomial R d) (j : Fin d) : Polynomial R d :=
  p.map fun t =>
    { coefficient := o.mul (natCast o (t.exponents.get j)) t.coefficient
      exponents := Vector.ofFn fun i =>
        if i = j then t.exponents.get i - 1 else t.exponents.get i }

def evaluateSystem {R : Type} {d : Nat} (o : RingOps R)
    (p : System R d) (x : Point R d) : Point R d :=
  Vector.ofFn fun i => evaluate o (p.get i) x

def jacobian {R : Type} {d : Nat} (o : RingOps R)
    (p : System R d) (x : Point R d) : Matrix R d :=
  Vector.ofFn fun i => Vector.ofFn fun j => evaluate o (partialDerivative o (p.get i) j) x

def vectorSub {R : Type} {d : Nat} (o : RingOps R)
    (x y : Point R d) : Point R d :=
  Vector.ofFn fun i => sub o (x.get i) (y.get i)

def vectorAdd {R : Type} {d : Nat} (o : RingOps R)
    (x y : Point R d) : Point R d :=
  Vector.ofFn fun i => o.add (x.get i) (y.get i)

def matrixSub {R : Type} {d : Nat} (o : RingOps R)
    (a b : Matrix R d) : Matrix R d :=
  Vector.ofFn fun i => vectorSub o (a.get i) (b.get i)

def matrixVector {R : Type} {d : Nat} (o : RingOps R)
    (a : Matrix R d) (x : Point R d) : Point R d :=
  Vector.ofFn fun i => sum o (List.ofFn fun j => o.mul ((a.get i).get j) (x.get j))

def matrixMultiply {R : Type} {d : Nat} (o : RingOps R)
    (a b : Matrix R d) : Matrix R d :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    sum o (List.ofFn fun k => o.mul ((a.get i).get k) ((b.get k).get j))

def identity {R : Type} (o : RingOps R) (d : Nat) : Matrix R d :=
  Vector.ofFn fun i => Vector.ofFn fun j => if i = j then o.one else o.zero

def inVector {R : Type} {d : Nat} (member : Nat → R → Bool)
    (k : Nat) (v : Point R d) : Prop := v.toList.all (member k) = true

def inMatrix {R : Type} {d : Nat} (member : Nat → R → Bool)
    (k : Nat) (a : Matrix R d) : Prop :=
  a.toList.all (fun row => row.toList.all (member k)) = true

structure FiltrationLaws {R : Type} (o : RingOps R)
    (member : Nat → R → Bool) (N : Nat) : Prop where
  all_zero : ∀ x, member 0 x = true
  descending : ∀ k x, member (k + 1) x = true → member k x = true
  vanishes : ∀ x, member N x = true ↔ x = o.zero
  contains_zero : ∀ k, member k o.zero = true
  add_closed : ∀ k x y, member k x = true → member k y = true →
    member k (o.add x y) = true
  neg_closed : ∀ k x, member k x = true → member k (o.neg x) = true
  multiplicative : ∀ i j x y, member i x = true → member j y = true →
    member (i + j) (o.mul x y) = true

def isRoot {R : Type} {d : Nat} (o : RingOps R)
    (p : System R d) (x : Point R d) : Prop :=
  evaluateSystem o p x = Vector.replicate d o.zero

def congruent {R : Type} {d : Nat} (o : RingOps R)
    (member : Nat → R → Bool) (k : Nat) (x y : Point R d) : Prop :=
  inVector member k (vectorSub o x y)

structure LiftingInput {R : Type} {d : Nat} (o : RingOps R)
    (member : Nat → R → Bool) (N : Nat)
    (p : System R d) (seed : Point R d) (u : Matrix R d) : Prop where
  positive : 0 < N
  ring : RingLaws o
  filtration : FiltrationLaws o member N
  seed_residual : inVector member 1 (evaluateSystem o p seed)
  right_inverse : inMatrix member 1
    (matrixSub o (identity o d) (matrixMultiply o (jacobian o p seed) u))
  left_inverse : inMatrix member 1
    (matrixSub o (identity o d) (matrixMultiply o u (jacobian o p seed)))

def frozenIter {R : Type} {d : Nat} (o : RingOps R)
    (p : System R d) (u : Matrix R d) (seed : Point R d) : Nat → Point R d
  | 0 => seed
  | n + 1 =>
      let x := frozenIter o p u seed n
      vectorSub o x (matrixVector o u (evaluateSystem o p x))

def FrozenLiftingGoal : Prop :=
  ∀ (R : Type) (d N : Nat) (o : RingOps R) (member : Nat → R → Bool)
    (p : System R d) (seed : Point R d) (u : Matrix R d),
    LiftingInput o member N p seed u →
    let out := frozenIter o p u seed (N - 1)
    isRoot o p out ∧ congruent o member 1 out seed ∧
      ∀ x : Point R d, isRoot o p x → congruent o member 1 x seed → x = out

def PrecisionInvariantGoal : Prop :=
  ∀ (R : Type) (d N : Nat) (o : RingOps R) (member : Nat → R → Bool)
    (p : System R d) (seed : Point R d) (u : Matrix R d),
    LiftingInput o member N p seed u →
    ∀ r, r < N →
      congruent o member 1 (frozenIter o p u seed r) seed ∧
      inVector member (r + 1) (evaluateSystem o p (frozenIter o p u seed r))

def TaylorRemainderGoal : Prop :=
  ∀ (R : Type) (d N : Nat) (o : RingOps R) (member : Nat → R → Bool),
    RingLaws o → FiltrationLaws o member N →
    ∀ (p : System R d) (x h : Point R d) (k : Nat), inVector member k h →
      inVector member (2 * k)
        (vectorSub o (vectorSub o (evaluateSystem o p (vectorAdd o x h))
          (evaluateSystem o p x)) (matrixVector o (jacobian o p x) h))

def JacobianCongruenceGoal : Prop :=
  ∀ (R : Type) (d N : Nat) (o : RingOps R) (member : Nat → R → Bool),
    RingLaws o → FiltrationLaws o member N →
    ∀ (p : System R d) (x a : Point R d), congruent o member 1 x a →
      inMatrix member 1 (matrixSub o (jacobian o p x) (jacobian o p a))

/-- These are canonical exact rational operations, not real approximations. -/
def rationalOps : RingOps Rat where
  zero := 0
  one := 1
  add := (· + ·)
  neg := Neg.neg
  mul := (· * ·)

abbrev Jet (N : Nat) := Vector Rat N

def jetOps (N : Nat) : RingOps (Jet N) where
  zero := Vector.replicate N 0
  one := Vector.ofFn fun i => if i.val = 0 then 1 else 0
  add := fun x y => Vector.ofFn fun i => x.get i + y.get i
  neg := fun x => Vector.ofFn fun i => -x.get i
  mul := fun x y => Vector.ofFn fun i =>
    ((List.range (i.val + 1)).map fun j =>
      x.toList.getD j 0 * y.toList.getD (i.val - j) 0).foldl (· + ·) 0

def jetMember (N k : Nat) (x : Jet N) : Bool :=
  (x.toList.take (min k N)).all fun a => decide (a = 0)

def jetConstant (N : Nat) (a : Rat) : Jet N :=
  Vector.ofFn fun i => if i.val = 0 then a else 0

def jetVariable (N : Nat) : Jet N :=
  Vector.ofFn fun i => if i.val = 1 then 1 else 0

def jetTruncate (M : Nat) {N : Nat} (x : Jet N) : Jet M :=
  Vector.ofFn fun i => x.toList.getD i.val 0

def jetProducer {d : Nat} (N : Nat) (p : System (Jet N) d)
    (seed : Point (Jet N) d) (u : Matrix (Jet N) d) : Point (Jet N) d :=
  frozenIter (jetOps N) p u seed (N - 1)

def JetPresentationGoal : Prop :=
  ∀ N, RingLaws (jetOps N) ∧ FiltrationLaws (jetOps N) (jetMember N) N

/-- Canonical residues. `positive` is proof data ensuring the finite carrier
is inhabited; the concrete residue lifting inputs have modulus q^N. -/
def residueOps (M : Nat) (positive : 0 < M) : RingOps (Fin M) where
  zero := ⟨0, positive⟩
  one := ⟨1 % M, Nat.mod_lt _ positive⟩
  add := fun x y => ⟨(x.val + y.val) % M, Nat.mod_lt _ positive⟩
  neg := fun x => ⟨(M - x.val) % M, Nat.mod_lt _ positive⟩
  mul := fun x y => ⟨(x.val * y.val) % M, Nat.mod_lt _ positive⟩

def residueMember (q N k : Nat) (x : Fin (q ^ N)) : Bool :=
  decide (x.val % (q ^ min k N) = 0)

def residueProducer {d : Nat} (q N : Nat) (positive : 0 < q ^ N)
    (p : System (Fin (q ^ N)) d) (seed : Point (Fin (q ^ N)) d)
    (u : Matrix (Fin (q ^ N)) d) : Point (Fin (q ^ N)) d :=
  frozenIter (residueOps (q ^ N) positive) p u seed (N - 1)

def ResiduePresentationGoal : Prop :=
  ∀ q N, 2 ≤ q → ∀ positive : 0 < q ^ N,
    RingLaws (residueOps (q ^ N) positive) ∧
    FiltrationLaws (residueOps (q ^ N) positive) (residueMember q N) N

structure HomLaws {R S : Type} (a : RingOps R) (b : RingOps S) (f : R → S) : Prop where
  zero : f a.zero = b.zero
  one : f a.one = b.one
  add : ∀ x y, f (a.add x y) = b.add (f x) (f y)
  neg : ∀ x, f (a.neg x) = b.neg (f x)
  mul : ∀ x y, f (a.mul x y) = b.mul (f x) (f y)

def mapPolynomial {R S : Type} {d : Nat} (f : R → S)
    (p : Polynomial R d) : Polynomial S d :=
  p.map fun t => { coefficient := f t.coefficient, exponents := t.exponents }

def mapSystem {R S : Type} {d : Nat} (f : R → S) (p : System R d) : System S d :=
  Vector.ofFn fun i => mapPolynomial f (p.get i)

def mapPoint {R S : Type} {d : Nat} (f : R → S) (x : Point R d) : Point S d :=
  Vector.ofFn fun i => f (x.get i)

def EvaluationTransportGoal : Prop :=
  ∀ (R S : Type) (d : Nat) (a : RingOps R) (b : RingOps S) (f : R → S),
    HomLaws a b f → ∀ (p : Polynomial R d) (x : Point R d),
      evaluate b (mapPolynomial f p) (mapPoint f x) = f (evaluate a p x)

def LiftTransportGoal : Prop :=
  ∀ (R S : Type) (d N M : Nat) (a : RingOps R) (b : RingOps S)
    (memA : Nat → R → Bool) (memB : Nat → S → Bool) (f : R → S)
    (p : System R d) (seedA : Point R d) (inverseA : Matrix R d)
    (seedB : Point S d) (inverseB : Matrix S d),
    LiftingInput a memA N p seedA inverseA →
    LiftingInput b memB M (mapSystem f p) seedB inverseB →
    HomLaws a b f →
    (∀ x, memA 1 x = true → memB 1 (f x) = true) →
    congruent b memB 1 (mapPoint f seedA) seedB →
    mapPoint f (frozenIter a p inverseA seedA (N - 1)) =
      frozenIter b (mapSystem f p) inverseB seedB (M - 1)

def JetTruncationGoal : Prop :=
  ∀ M N, M ≤ N →
    HomLaws (jetOps N) (jetOps M) (jetTruncate M) ∧
      ∀ k (x : Jet N), jetMember N k x = true → jetMember M k (jetTruncate M x) = true

def residueProjection (q N M : Nat) (positive : 0 < q ^ M)
    (x : Fin (q ^ N)) : Fin (q ^ M) :=
  ⟨x.val % (q ^ M), Nat.mod_lt _ positive⟩

def ResidueProjectionGoal : Prop :=
  ∀ q N M, 2 ≤ q → M ≤ N → ∀ (posN : 0 < q ^ N) (posM : 0 < q ^ M),
    HomLaws (residueOps (q ^ N) posN) (residueOps (q ^ M) posM)
      (residueProjection q N M posM) ∧
        ∀ x, residueMember q N 1 x = true →
          residueMember q M 1 (residueProjection q N M posM x) = true

end IPRAFramework.FiniteAlgebra
