import Init

/-!
# Equality from two-sided atomic indiscernibility

This file uses Lean's core library only. It proves a semantic leaf theorem for
the proposed equality erasure; it does not formalize set theory, a syntactic
proof translation, a Turing-machine compiler, or a consistency equivalence.

Formulas use de Bruijn variables. On an arbitrary membership structure,
two-sided atomic indiscernibility is an equivalence relation and a congruence.
Equality-free satisfaction is invariant under pointwise equivalent valuations.
An explicit equality-erasing translation interprets equality by this relation.
-/

namespace AtomicEquality

universe u

abbrev Relation (A : Type u) := A → A → Prop
abbrev Valuation (A : Type u) := Nat → A

/-- Equal columns and equal rows of the membership relation. -/
def Indiscernible {A : Type u} (R : Relation A) (a b : A) : Prop :=
  (∀ z, R z a ↔ R z b) ∧ (∀ z, R a z ↔ R b z)

theorem indiscernible_refl {A : Type u} (R : Relation A) (a : A) :
    Indiscernible R a a :=
  ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem indiscernible_symm {A : Type u} {R : Relation A} {a b : A}
    (h : Indiscernible R a b) : Indiscernible R b a :=
  ⟨fun z => (h.1 z).symm, fun z => (h.2 z).symm⟩

theorem indiscernible_trans {A : Type u} {R : Relation A} {a b c : A}
    (hab : Indiscernible R a b) (hbc : Indiscernible R b c) :
    Indiscernible R a c :=
  ⟨fun z => (hab.1 z).trans (hbc.1 z),
   fun z => (hab.2 z).trans (hbc.2 z)⟩

theorem membership_congr {A : Type u} {R : Relation A} {a a' b b' : A}
    (ha : Indiscernible R a a') (hb : Indiscernible R b b') :
    R a b ↔ R a' b' :=
  (ha.2 b).trans (hb.1 a')

def atomicSetoid {A : Type u} (R : Relation A) : Setoid A where
  r := Indiscernible R
  iseqv :=
    ⟨indiscernible_refl R, indiscernible_symm, indiscernible_trans⟩

/-- Adding a value for the newly bound variable zero. -/
def push {A : Type u} (a : A) (v : Valuation A) : Valuation A
  | 0 => a
  | n + 1 => v n

def ValuationRelated {A : Type u} (R : Relation A)
    (v w : Valuation A) : Prop :=
  ∀ n, Indiscernible R (v n) (w n)

theorem push_related {A : Type u} {R : Relation A}
    {v w : Valuation A} {a b : A}
    (hvw : ValuationRelated R v w) (hab : Indiscernible R a b) :
    ValuationRelated R (push a v) (push b w) := by
  intro n
  cases n with
  | zero => exact hab
  | succ n => exact hvw n

/-- Equality-free first-order formulas in one binary relation. -/
inductive Formula where
  | atom : Nat → Nat → Formula
  | bot : Formula
  | conj : Formula → Formula → Formula
  | impl : Formula → Formula → Formula
  | biimp : Formula → Formula → Formula
  | all : Formula → Formula

def Sat {A : Type u} (R : Relation A) (v : Valuation A) :
    Formula → Prop
  | .atom i j => R (v i) (v j)
  | .bot => False
  | .conj p q => Sat R v p ∧ Sat R v q
  | .impl p q => Sat R v p → Sat R v q
  | .biimp p q => Sat R v p ↔ Sat R v q
  | .all p => ∀ a, Sat R (push a v) p

private theorem implication_congr {P P' Q Q' : Prop}
    (hP : P ↔ P') (hQ : Q ↔ Q') : (P → Q) ↔ (P' → Q') :=
  ⟨fun h hp' => hQ.mp (h (hP.mpr hp')),
   fun h hp => hQ.mpr (h (hP.mp hp))⟩

private theorem conjunction_congr {P P' Q Q' : Prop}
    (hP : P ↔ P') (hQ : Q ↔ Q') : (P ∧ Q) ↔ (P' ∧ Q') :=
  ⟨fun h => ⟨hP.mp h.1, hQ.mp h.2⟩,
   fun h => ⟨hP.mpr h.1, hQ.mpr h.2⟩⟩

private theorem biimplication_congr {P P' Q Q' : Prop}
    (hP : P ↔ P') (hQ : Q ↔ Q') : (P ↔ Q) ↔ (P' ↔ Q') :=
  ⟨fun h => hP.symm.trans (h.trans hQ),
   fun h => hP.trans (h.trans hQ.symm)⟩

/-- Every equality-free formula respects two-sided atomic indiscernibility. -/
theorem satisfaction_invariant {A : Type u} (R : Relation A)
    (p : Formula) {v w : Valuation A}
    (hvw : ValuationRelated R v w) : Sat R v p ↔ Sat R w p := by
  induction p generalizing v w with
  | atom i j => exact membership_congr (hvw i) (hvw j)
  | bot => exact Iff.rfl
  | conj p q ihp ihq =>
      exact conjunction_congr (ihp hvw) (ihq hvw)
  | impl p q ihp ihq =>
      exact implication_congr (ihp hvw) (ihq hvw)
  | biimp p q ihp ihq =>
      exact biimplication_congr (ihp hvw) (ihq hvw)
  | all p ih =>
      constructor
      · intro hp a
        exact (ih (push_related hvw (indiscernible_refl R a))).mp (hp a)
      · intro hp a
        exact (ih (push_related hvw (indiscernible_refl R a))).mpr (hp a)

/-- First-order formulas with an additional equality atom. -/
inductive FormulaWithEquality where
  | atom : Nat → Nat → FormulaWithEquality
  | equal : Nat → Nat → FormulaWithEquality
  | bot : FormulaWithEquality
  | conj : FormulaWithEquality → FormulaWithEquality → FormulaWithEquality
  | impl : FormulaWithEquality → FormulaWithEquality → FormulaWithEquality
  | biimp : FormulaWithEquality → FormulaWithEquality → FormulaWithEquality
  | all : FormulaWithEquality → FormulaWithEquality

/-- The equality relation is an explicit semantic parameter. -/
def SatWithEquality {A : Type u} (R E : Relation A) (v : Valuation A) :
    FormulaWithEquality → Prop
  | .atom i j => R (v i) (v j)
  | .equal i j => E (v i) (v j)
  | .bot => False
  | .conj p q => SatWithEquality R E v p ∧ SatWithEquality R E v q
  | .impl p q => SatWithEquality R E v p → SatWithEquality R E v q
  | .biimp p q => SatWithEquality R E v p ↔ SatWithEquality R E v q
  | .all p => ∀ a, SatWithEquality R E (push a v) p

/-- Under the new binder, all old variables are shifted by one. -/
def equalityFormula (i j : Nat) : Formula :=
  .all (.conj
    (.biimp (.atom 0 (i + 1)) (.atom 0 (j + 1)))
    (.biimp (.atom (i + 1) 0) (.atom (j + 1) 0)))

theorem equalityFormula_correct {A : Type u} (R : Relation A)
    (v : Valuation A) (i j : Nat) :
    Sat R v (equalityFormula i j) ↔ Indiscernible R (v i) (v j) := by
  constructor
  · intro h
    exact ⟨fun a => (h a).1, fun a => (h a).2⟩
  · intro h a
    exact ⟨h.1 a, h.2 a⟩

def eraseEquality : FormulaWithEquality → Formula
  | .atom i j => .atom i j
  | .equal i j => equalityFormula i j
  | .bot => .bot
  | .conj p q => .conj (eraseEquality p) (eraseEquality q)
  | .impl p q => .impl (eraseEquality p) (eraseEquality q)
  | .biimp p q => .biimp (eraseEquality p) (eraseEquality q)
  | .all p => .all (eraseEquality p)

/-- Erasure interprets equality by atomic indiscernibility, not literal equality. -/
theorem equality_erasure_correct {A : Type u} (R : Relation A)
    (p : FormulaWithEquality) (v : Valuation A) :
    Sat R v (eraseEquality p) ↔
      SatWithEquality R (Indiscernible R) v p := by
  induction p generalizing v with
  | atom i j => exact Iff.rfl
  | equal i j => exact equalityFormula_correct R v i j
  | bot => exact Iff.rfl
  | conj p q ihp ihq =>
      exact conjunction_congr (ihp v) (ihq v)
  | impl p q ihp ihq =>
      exact implication_congr (ihp v) (ihq v)
  | biimp p q ihp ihq =>
      exact biimplication_congr (ihp v) (ihq v)
  | all p ih =>
      constructor
      · intro h a
        exact (ih (push a v)).mp (h a)
      · intro h a
        exact (ih (push a v)).mpr (h a)

#print axioms indiscernible_refl
#print axioms indiscernible_symm
#print axioms indiscernible_trans
#print axioms membership_congr
#print axioms satisfaction_invariant
#print axioms equalityFormula_correct
#print axioms equality_erasure_correct

end AtomicEquality
