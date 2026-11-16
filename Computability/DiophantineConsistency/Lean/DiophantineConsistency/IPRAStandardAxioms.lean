import DiophantineConsistency.IPRANativeTheory

/-! The syntax of successor-step induction and the axioms of standard iPRA.
The induction conversions and provability comparison are separate proof modules. -/
set_option autoImplicit false

namespace DiophantineConsistency

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAFiniteFunctionCodes
open IPRANativeInduction IPRANativeTheory IPRAQuantifierFree

namespace IPRASuccessorInduction

def succTerm (n : ℕ) : TermN (n+1) := .func Code.succ (fun _ => #0)
def atSucc {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Semisentenceᵢ language (n+1) :=
  Rew.subst (Fin.cases (succTerm n) (fun i => #i.succ)) ▹ φ

def succStepBody {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Semisentenceᵢ language n :=
  ∀⁰ (φ 🡒 atSucc φ)
def succInductionBody {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Semisentenceᵢ language n :=
  atZero φ 🡒 succStepBody φ 🡒 ∀⁰ φ
def succInductionAxiom {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Sentenceᵢ language :=
  ∀⁰* (succInductionBody φ)

end IPRASuccessorInduction

namespace IPRAStandardTheory

open IPRASuccessorInduction

/-- Reflexivity, and replacement for atomic formulas with arbitrary parameters. -/
inductive StandardEqualityAxiom : Sentenceᵢ language → Prop
  | refl : StandardEqualityAxiom eqReflI
  | atomic {n k : ℕ} (r : language.Rel k) (ts : Fin k → TermN (n+1)) :
      StandardEqualityAxiom (eqSubstitutionI (Semiformulaᵢ.rel r ts))

inductive StandardAxiom : Sentenceᵢ language → Prop
  | equality {σ} : StandardEqualityAxiom σ → StandardAxiom σ
  | defining {σ} : DefiningEquationI σ → StandardAxiom σ
  | basic {σ} : BasicAxiomI σ → StandardAxiom σ
  | induction {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : OpenI φ →
      StandardAxiom (succInductionAxiom φ)

/-- Standard intuitionistic primitive recursive arithmetic. -/
def standardTheory : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language) := ⟨{σ | StandardAxiom σ}⟩

end IPRAStandardTheory
end DiophantineConsistency
