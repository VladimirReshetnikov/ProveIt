import Mathlib

/-!
# Relational names: an uncompiled Lean blueprint

STATUS: This file has not been compiled in the present environment.

The definitions below are host-level specifications. In particular, a field
with type `Nat -> Nat` does not certify primitive recursiveness. A future
object implementation must give actual `PR` terms for the one-step machine,
coding maps, trace checker, and code constructors, then derive their laws in
`Prf PRAAx`. The `...Target` definitions state obligations; they do not prove
them. The two small theorems at the end prove only finite logical assembly of
already supplied termination witnesses.

The accompanying paper proves rational slack removal, name-setoid laws,
fixed-call closure, and the diagonal-completion estimates in human-readable
form. This file exposes their exact dependencies without disguising a
requested theorem as a supplied interface instance.
-/

namespace IPRAContinuous.RelationalNames

/-- The numeric pairing used in the paper, not a universal evaluator. -/
def pair (a b : Nat) : Nat := (a + b) * (a + b) + a

def eps (n : Nat) : ℚ := (1 : ℚ) / (2 : ℚ) ^ n

/--
An abstract deterministic machine interface. Every data field must eventually
be realized by an actual primitive-recursive symbol. `decode` is the fixed
total signed-rational decoder. `halt_absorbing` is a specification requiring
an object-theory derivation in the final implementation.
-/
structure TraceKernel where
  initial : Nat → Nat → Nat
  step : Nat → Nat → Nat
  halted : Nat → Bool
  output : Nat → Nat
  decode : Nat → ℚ
  halt_absorbing : ∀ e s, halted s = true → step e s = s

def run (K : TraceKernel) (e x : Nat) : Nat → Nat
  | 0 => K.initial e x
  | n + 1 => K.step e (run K e x n)

def traceCheck (K : TraceKernel) (e x t a : Nat) : Bool :=
  K.halted (run K e x t) && decide (K.output (run K e x t) = a)

def Trace (K : TraceKernel) (e x t a : Nat) : Prop :=
  traceCheck K e x t a = true

def Eval (K : TraceKernel) (e x a : Nat) : Prop :=
  ∃ t, Trace K e x t a

def Total (K : TraceKernel) (e : Nat) : Prop :=
  ∀ x, ∃ t a, Trace K e x t a

def DeterminismTarget (K : TraceKernel) : Prop :=
  ∀ e x t u a b,
    Trace K e x t a → Trace K e x u b → a = b

/-- This property has unbounded number quantifiers; it is not a QF invariant. -/
def Regular (K : TraceKernel) (e : Nat) : Prop :=
  ∀ i j t u a b,
    Trace K e i t a → Trace K e j u b →
      |K.decode a - K.decode b| ≤ eps i + eps j

def Name (K : TraceKernel) (e : Nat) : Prop :=
  Total K e ∧ Regular K e

def Near (K : TraceKernel) (e f : Nat) (r : ℚ) : Prop :=
  ∀ i j t u a b,
    Trace K e i t a → Trace K f j u b →
      |K.decode a - K.decode b| ≤ r + eps i + eps j

def Equivalent (K : TraceKernel) (e f : Nat) : Prop :=
  Near K e f 0

def RationalSlackTarget : Prop :=
  ∀ v w C : ℚ, 0 ≤ C →
    (∀ k : Nat, v ≤ w + C * eps k) → v ≤ w

def TailRationalSlackTarget : Prop :=
  ∀ (v w C : ℚ) (k₀ : Nat), 0 ≤ C →
    (∀ k : Nat, k₀ ≤ k → v ≤ w + C * eps k) → v ≤ w

def NearTriangleTarget (K : TraceKernel) : Prop :=
  ∀ (e f g : Nat) (r s : ℚ),
    Total K f → Near K e f r → Near K f g s → Near K e g (r + s)

def NameSetoidTarget (K : TraceKernel) : Prop :=
  (∀ e, Name K e → Equivalent K e e) ∧
  (∀ e f, Equivalent K e f → Equivalent K f e) ∧
  (∀ e f g, Name K f → Equivalent K e f → Equivalent K f g →
    Equivalent K e g)

/--
Finite sequential composition. The `splice` field is an unimplemented
machine-code obligation, not an assertion that it has been proved here.
`code outer inner` executes `inner`, then passes its numeric output to `outer`.
-/
structure SequentialComposition (K : TraceKernel) where
  code : Nat → Nat → Nat
  splice : ∀ outer inner x t a u b,
    Trace K inner x t a → Trace K outer a u b →
      ∃ v, Trace K (code outer inner) x v b

/--
The fixed two-call addition constructor, with both trace directions.
Actual PR code constructors and trace assemblers are required in the object
implementation. No runtime bound uniform over all name codes is asserted.
-/
structure SumConstructor (K : TraceKernel) where
  code : Nat → Nat → Nat
  addValue : Nat → Nat → Nat
  addValue_spec : ∀ a b, K.decode (addValue a b) = K.decode a + K.decode b
  assemble : ∀ e f n t a u b,
    Trace K e (n + 2) t a → Trace K f (n + 2) u b →
      ∃ v, Trace K (code e f) n v (addValue a b)
  decompose : ∀ e f n v o,
    Trace K (code e f) n v o →
      ∃ t a u b,
        Trace K e (n + 2) t a ∧ Trace K f (n + 2) u b ∧
        K.decode o = K.decode a + K.decode b

def SumNameTarget (K : TraceKernel) (S : SumConstructor K) : Prop :=
  ∀ e f, Name K e → Name K f → Name K (S.code e f)

def SumCongruenceTarget (K : TraceKernel) (S : SumConstructor K) : Prop :=
  ∀ e e' f f',
    Name K e → Name K e' → Name K f → Name K f' →
    Equivalent K e e' → Equivalent K f f' →
    Equivalent K (S.code e f) (S.code e' f')

def JointTotal (K : TraceKernel) (e : Nat) : Prop :=
  ∀ n i, ∃ t a, Trace K e (pair n i) t a

def RowRegular (K : TraceKernel) (e : Nat) : Prop :=
  ∀ n i j t u a b,
    Trace K e (pair n i) t a → Trace K e (pair n j) u b →
      |K.decode a - K.decode b| ≤ eps i + eps j

/-- `mu` is a specified PR numerical family in the executable reading. -/
def MonotoneModulus (mu : Nat → Nat → Nat) : Prop :=
  ∀ p k l, k ≤ l → mu p k ≤ mu p l

def UniformCauchy
    (K : TraceKernel) (e : Nat) (mu : Nat → Nat → Nat) (p : Nat) : Prop :=
  ∀ k n m i j t u a b,
    mu p k ≤ n → mu p k ≤ m →
    Trace K e (pair n i) t a → Trace K e (pair m j) u b →
      |K.decode a - K.decode b| ≤ eps k + eps i + eps j

structure RowConstructor (K : TraceKernel) where
  code : Nat → Nat → Nat
  assemble : ∀ e n i t a,
    Trace K e (pair n i) t a → ∃ u, Trace K (code e n) i u a
  decompose : ∀ e n i u a,
    Trace K (code e n) i u a → ∃ t, Trace K e (pair n i) t a

/--
One matrix call per output precision: x_k = a_(mu(p,k+2),k+2).
For a relational modulus code, replace this interface by finite sequential
calls and supply its totality and monotonicity formulas. Do not normalize
that modulus by a variable-length scan without its own totality argument.
-/
structure DiagonalConstructor (K : TraceKernel) (mu : Nat → Nat → Nat) where
  code : Nat → Nat → Nat
  assemble : ∀ e p k t a,
    Trace K e (pair (mu p (k + 2)) (k + 2)) t a →
      ∃ u, Trace K (code e p) k u a
  decompose : ∀ e p k u a,
    Trace K (code e p) k u a →
      ∃ t, Trace K e (pair (mu p (k + 2)) (k + 2)) t a

def CompletionTarget
    (K : TraceKernel) (mu : Nat → Nat → Nat)
    (R : RowConstructor K) (D : DiagonalConstructor K mu) : Prop :=
  ∀ e p,
    MonotoneModulus mu → JointTotal K e → RowRegular K e →
    UniformCauchy K e mu p →
    Name K (D.code e p) ∧
      ∀ k n, mu p (k + 2) ≤ n →
        Near K (R.code e n) (D.code e p) (eps (k + 2))

/-- One successful trace and raw output for each listed request. -/
abbrev BatchWitness := List (Nat × Nat)

def batchCheck
    (K : TraceKernel) (e : Nat) (requests : List Nat) (w : BatchWitness) : Bool :=
  decide (requests.length = w.length) &&
    (requests.zip w).all (fun qa => traceCheck K e qa.1 qa.2.1 qa.2.2)

def BatchTotal (K : TraceKernel) (e : Nat) : Prop :=
  ∀ requests : List Nat, ∃ w : BatchWitness, batchCheck K e requests w = true

/-
There is deliberately no theorem here inferring `BatchTotal K e` from
`Total K e`. A variable-length tuple of unbounded termination witnesses is a
separate collection obligation. A bounded checker for a proposed tuple does
not construct it. Fixed PR clocks or explicit batch certificates discharge
the nonadaptive interface. Adaptive loops additionally need a finite demand
envelope or their own execution/totality contract.

Lists in this host specification must be replaced by natural-number list
codes and proved PR folds in the object-language implementation.
-/

structure ClockContract (K : TraceKernel) (e : Nat) where
  time : Nat → Nat
  value : Nat → Nat
  correct : ∀ x, Trace K e x (time x) (value x)

/-- Pure finite logical witness assembly; not a universal evaluator theorem. -/
theorem total_composition
    (K : TraceKernel) (C : SequentialComposition K)
    (outer inner : Nat) (hInner : Total K inner) (hOuter : Total K outer) :
    Total K (C.code outer inner) := by
  intro x
  obtain ⟨t, a, ht⟩ := hInner x
  obtain ⟨u, b, hu⟩ := hOuter a
  obtain ⟨v, hv⟩ := C.splice outer inner x t a u b ht hu
  exact ⟨v, b, hv⟩

/-- One selected matrix witness establishes each diagonal computation. -/
theorem total_diagonal
    (K : TraceKernel) (mu : Nat → Nat → Nat)
    (D : DiagonalConstructor K mu) (e p : Nat)
    (h : JointTotal K e) : Total K (D.code e p) := by
  intro k
  obtain ⟨t, a, ht⟩ := h (mu p (k + 2)) (k + 2)
  obtain ⟨u, hu⟩ := D.assemble e p k t a ht
  exact ⟨u, a, hu⟩

end IPRAContinuous.RelationalNames
