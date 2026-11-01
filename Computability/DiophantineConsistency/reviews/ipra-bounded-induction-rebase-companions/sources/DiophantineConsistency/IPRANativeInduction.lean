import DiophantineConsistency.IPRAQuantifierFree
/-! A finite-parameter intuitionistic quantifier-free induction schema using
the same x+1 step term as Foundation. This is only the schema syntax; no
claim is made here about translated classical induction axioms. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRANativeInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open PRALanguage PRATheory IPRAQuantifierFree

/-- The same x+1 term used by Foundation's classical `succInd`. -/
def stepTerm (n : ℕ) : TermN (n+1) :=
  .func addCode ![#0, .func oneCode Fin.elim0]

def zeroTerm (n : ℕ) : TermN n := .func (.zero 0) Fin.elim0

def atZero {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Semisentenceᵢ language n :=
  Rew.subst (Fin.cases (zeroTerm n) (fun i => #i)) ▹ φ

def atStep {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Semisentenceᵢ language (n+1) :=
  Rew.subst (Fin.cases (stepTerm n) (fun i => #i.succ)) ▹ φ

def inductionBody {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Semisentenceᵢ language n :=
  atZero φ 🡒 (∀⁰ (φ 🡒 atStep φ)) 🡒 ∀⁰ φ

def inductionAxiom {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Sentenceᵢ language :=
  ∀⁰* (inductionBody φ)

def nativeInduction : Set (Sentenceᵢ language) :=
  {σ | ∃ n, ∃ φ : Semisentenceᵢ language (n+1), OpenI φ ∧ σ = inductionAxiom φ}
/-- The GG image of any open matrix is eligible for native induction.
This is not yet the translated classical induction axiom. -/
theorem translated_matrix_nativeInduction {n : ℕ}
    (φ : Semisentence language (n+1)) (h : φ.Open) :
    inductionAxiom φᴺ ∈ nativeInduction :=
  ⟨n, φᴺ, gg_preserves_open φ h, rfl⟩
end DiophantineConsistency.IPRANativeInduction
