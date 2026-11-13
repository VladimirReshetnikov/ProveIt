import DiophantineConsistency.IPRAQuantifierFree

/-!
An explicit equality-only intuitionistic first-order reference theory.

It is a precise intensional-code version of the first-order quantifier extension
of intuitionistic PRA₀ described by Joan Moschovakis, *Intuitionistic Reverse
Analysis*, pp. 1–2:
https://www.math.ucla.edu/~joan/techgothenburghandout.pdf
Its constructor-based PR symbols and defining equations are specified in the
style of Klaus Aehlig, *Induction and Inductive Definitions in Fragments*,
Definitions 2.1–2.2:
https://www.linta.de/~aehlig/university/pub/04-jsl.pdf
That paper's surrounding logic is classical; this definition uses
intuitionistic first-order logic with primitive positive connectives.

This module only specifies the reference theory. It does not assert its
equivalence with the existing native theory, translate less-than, or prove an
equation endpoint. Equal standard functions with different finite construction
codes remain distinct symbols.
-/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAEqualityOnlyReference
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRATheory IPRAQuantifierFree

inductive EqualityRel : ℕ → Type
  | eq : EqualityRel 2
  deriving DecidableEq

def language : Language where
  Func := Code
  Rel := EqualityRel

abbrev TermN (n : ℕ) := Semiterm language Empty n

def applyCode {n m : ℕ} (c : Code m) (v : Fin m → TermN n) : TermN n := .func c v
def vars (n : ℕ) : Fin n → TermN n := fun i => .bvar i

def equalClosure {n : ℕ} (a b : TermN n) : Sentenceᵢ language :=
  ∀⁰* (Semiformulaᵢ.rel EqualityRel.eq ![a,b])

def zeroEquation (n : ℕ) : Sentenceᵢ language :=
  equalClosure (applyCode (.zero n) (vars n)) (applyCode (.zero 0) Fin.elim0)
def projectionEquation {n : ℕ} (i : Fin n) : Sentenceᵢ language :=
  equalClosure (applyCode (.proj i) (vars n)) (.bvar i)
def compositionEquation {m n : ℕ} (f : Code m) (g : Codes n m) : Sentenceᵢ language :=
  equalClosure (applyCode (.comp f g) (vars n))
    (applyCode f (fun i => applyCode (getCode g i) (vars n)))
def recursionBaseEquation {n : ℕ} (f : Code n) (g : Code (n+2)) : Sentenceᵢ language :=
  let params : Fin n → TermN n := vars n
  equalClosure (applyCode (.prec f g) (Fin.cases (applyCode (.zero 0) Fin.elim0) params))
    (applyCode f params)
def recursionStepEquation {n : ℕ} (f : Code n) (g : Code (n+2)) : Sentenceᵢ language :=
  let params : Fin n → TermN (n+1) := fun i => .bvar i.succ
  let counter : TermN (n+1) := .bvar 0
  let previous := applyCode (.prec f g) (Fin.cases counter params)
  equalClosure (applyCode (.prec f g)
    (Fin.cases (applyCode .succ (fun _ => counter)) params))
    (applyCode g (Fin.cases counter (Fin.cases previous params)))

inductive DefiningEquation : Sentenceᵢ language → Prop
  | zero (n : ℕ) : DefiningEquation (zeroEquation n)
  | projection {n : ℕ} (i : Fin n) : DefiningEquation (projectionEquation i)
  | composition {m n : ℕ} (f : Code m) (g : Codes n m) :
      DefiningEquation (compositionEquation f g)
  | recursionBase {n : ℕ} (f : Code n) (g : Code (n+2)) :
      DefiningEquation (recursionBaseEquation f g)
  | recursionStep {n : ℕ} (f : Code n) (g : Code (n+2)) :
      DefiningEquation (recursionStepEquation f g)

def successorNonzero : Sentenceᵢ language :=
  ∀⁰* (∼(Semiformulaᵢ.rel EqualityRel.eq
    ![applyCode .succ (fun _ => .bvar 0), applyCode (.zero 0) Fin.elim0]) : Semisentenceᵢ language 1)

def eqRefl : Sentenceᵢ language :=
  ∀⁰* (Semiformulaᵢ.rel EqualityRel.eq ![#0,#0] : Semisentenceᵢ language 1)
def eqLeft {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Semisentenceᵢ language (n+2) :=
  Rew.subst (Fin.cases #0 (fun i => #i.succ.succ)) ▹ φ
def eqRight {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Semisentenceᵢ language (n+2) :=
  Rew.subst (Fin.cases #1 (fun i => #i.succ.succ)) ▹ φ
def eqSubstitution {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Sentenceᵢ language :=
  ∀⁰* ((Semiformulaᵢ.rel EqualityRel.eq ![#0,#1]) 🡒 (eqLeft φ 🡒 eqRight φ))
inductive EqualityAxiom : Sentenceᵢ language → Prop
  | refl : EqualityAxiom eqRefl
  | substitution {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : EqualityAxiom (eqSubstitution φ)

def atZero {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Semisentenceᵢ language n :=
  Rew.subst (Fin.cases (applyCode (.zero 0) Fin.elim0) (fun i => #i)) ▹ φ
def atSucc {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Semisentenceᵢ language (n+1) :=
  Rew.subst (Fin.cases (applyCode .succ (fun _ => #0)) (fun i => #i.succ)) ▹ φ
def inductionAxiom {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Sentenceᵢ language :=
  ∀⁰* (atZero φ 🡒 (∀⁰ (φ 🡒 atSucc φ)) 🡒 ∀⁰ φ)

inductive ReferenceAxiom : Sentenceᵢ language → Prop
  | equality {σ} : EqualityAxiom σ → ReferenceAxiom σ
  | defining {σ} : DefiningEquation σ → ReferenceAxiom σ
  | successorNonzero : ReferenceAxiom successorNonzero
  | induction {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : OpenI φ → ReferenceAxiom (inductionAxiom φ)

def referenceTheory : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language) := ⟨{σ | ReferenceAxiom σ}⟩

end DiophantineConsistency.IPRAEqualityOnlyReference
