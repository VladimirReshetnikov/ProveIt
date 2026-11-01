import DiophantineConsistency.IPRANativeInduction
/-! A candidate native intuitionistic PRA theory in the full PR-code language.
Its comparison with standard presentations and the GG axiom images is separate. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRANativeTheory
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRAQuantifierFree IPRANativeInduction

def equalClosureI {n : ℕ} (a b : TermN n) : Sentenceᵢ language :=
  ∀⁰* (Semiformulaᵢ.rel Language.ORing.Rel.eq ![a,b])

def zeroEquationI (n : ℕ) : Sentenceᵢ language :=
  equalClosureI (applyCode (.zero n) (vars n)) (applyCode (.zero 0) Fin.elim0)
def projectionEquationI {n : ℕ} (i : Fin n) : Sentenceᵢ language :=
  equalClosureI (applyCode (.proj i) (vars n)) (.bvar i)
def compositionEquationI {m n : ℕ} (f : Code m) (g : Codes n m) : Sentenceᵢ language :=
  equalClosureI (applyCode (.comp f g) (vars n))
    (applyCode f (fun i => applyCode (getCode g i) (vars n)))
def recursionBaseEquationI {n : ℕ} (f : Code n) (g : Code (n+2)) : Sentenceᵢ language :=
  let params : Fin n → TermN n := vars n
  equalClosureI (applyCode (.prec f g) (Fin.cases (applyCode (.zero 0) Fin.elim0) params))
    (applyCode f params)
def recursionStepEquationI {n : ℕ} (f : Code n) (g : Code (n+2)) : Sentenceᵢ language :=
  let params : Fin n → TermN (n+1) := fun i => .bvar i.succ
  let counter : TermN (n+1) := .bvar 0
  let previous := applyCode (.prec f g) (Fin.cases counter params)
  equalClosureI (applyCode (.prec f g)
    (Fin.cases (applyCode .succ (fun _ => counter)) params))
    (applyCode g (Fin.cases counter (Fin.cases previous params)))

inductive DefiningEquationI : Sentenceᵢ language → Prop
  | zero (n : ℕ) : DefiningEquationI (zeroEquationI n)
  | projection {n : ℕ} (i : Fin n) : DefiningEquationI (projectionEquationI i)
  | composition {m n : ℕ} (f : Code m) (g : Codes n m) :
      DefiningEquationI (compositionEquationI f g)
  | recursionBase {n : ℕ} (f : Code n) (g : Code (n+2)) :
      DefiningEquationI (recursionBaseEquationI f g)
  | recursionStep {n : ℕ} (f : Code n) (g : Code (n+2)) :
      DefiningEquationI (recursionStepEquationI f g)

def succNonzeroI : Sentenceᵢ language :=
  ∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq
    ![applyCode .succ (fun _ => .bvar 0), applyCode (.zero 0) Fin.elim0]) : Semisentenceᵢ language 1)
def succInjectiveI : Sentenceᵢ language :=
  ∀⁰* ((Semiformulaᵢ.rel Language.ORing.Rel.eq
      ![applyCode .succ (fun _ => .bvar 0), applyCode .succ (fun _ => .bvar 1)]) 🡒
    (Semiformulaᵢ.rel Language.ORing.Rel.eq ![.bvar 0, .bvar 1]) : Semisentenceᵢ language 2)
def orderDefinitionI : Sentenceᵢ language :=
  ∀⁰* ((Semiformulaᵢ.rel Language.ORing.Rel.lt ![.bvar 0, .bvar 1]) 🡘
    (Semiformulaᵢ.rel Language.ORing.Rel.eq
      ![applyCode ltBitCode (fun i => .bvar i), applyCode oneCode Fin.elim0]) : Semisentenceᵢ language 2)
inductive BasicAxiomI : Sentenceᵢ language → Prop
  | succNonzero : BasicAxiomI succNonzeroI
  | succInjective : BasicAxiomI succInjectiveI
  | orderDefinition : BasicAxiomI orderDefinitionI

/-- Full intuitionistic Leibniz equality, with arbitrarily many parameters. -/
def eqReflI : Sentenceᵢ language :=
  ∀⁰* (Semiformulaᵢ.rel Language.ORing.Rel.eq ![#0,#0] : Semisentenceᵢ language 1)
def eqLeft {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Semisentenceᵢ language (n+2) :=
  Rew.subst (Fin.cases #0 (fun i => #i.succ.succ)) ▹ φ
def eqRight {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Semisentenceᵢ language (n+2) :=
  Rew.subst (Fin.cases #1 (fun i => #i.succ.succ)) ▹ φ
def eqSubstitutionI {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Sentenceᵢ language :=
  ∀⁰* ((Semiformulaᵢ.rel Language.ORing.Rel.eq ![#0,#1]) 🡒 (eqLeft φ 🡒 eqRight φ))
inductive EqualityAxiomI : Sentenceᵢ language → Prop
  | refl : EqualityAxiomI eqReflI
  | substitution {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : EqualityAxiomI (eqSubstitutionI φ)

inductive NativeAxiom : Sentenceᵢ language → Prop
  | equality {σ} : EqualityAxiomI σ → NativeAxiom σ
  | defining {σ} : DefiningEquationI σ → NativeAxiom σ
  | basic {σ} : BasicAxiomI σ → NativeAxiom σ
  | induction {σ} : σ ∈ nativeInduction → NativeAxiom σ

def nativeTheory : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language) := ⟨{σ | NativeAxiom σ}⟩
/-- Every finite-parameter native open-induction instance belongs to the theory. -/
theorem induction_mem {n : ℕ} (φ : Semisentenceᵢ language (n+1)) (h : OpenI φ) :
    inductionAxiom φ ∈ nativeTheory.theory :=
  NativeAxiom.induction ⟨n, φ, h, rfl⟩

end DiophantineConsistency.IPRANativeTheory
