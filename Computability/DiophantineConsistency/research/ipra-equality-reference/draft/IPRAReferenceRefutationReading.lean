import DiophantineConsistency.IPRAOrderErasure
import DiophantineConsistency.IPRAFoundationZFCMappedNegation

/-! Uncompiled draft: read Foundation arithmetic NNF directly in the
equality-only reference language. This uses the *same* Foundation ZFC proof
predicate, not an arbitrary alternative coding. Neither the proposed syntactic
identity nor any semantics/proof-coding comparison has been checked. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAReferenceRefutationReading
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open IPRAOrderErasure IPRAEqualityOnlyReference

def translatedTerm {ξ : Type} {n : ℕ} (t : Semiterm ℒₒᵣ ξ n) :
    Semiterm IPRAEqualityOnlyReference.language ξ n :=
  Semiterm.lMap termsToReference (Semiterm.lMap PRALanguage.embedding t)

def atom {ξ : Type} {n k : ℕ} (r : Language.ORing.Rel k)
    (v : Fin k → Semiterm ℒₒᵣ ξ n) : Semiformulaᵢ IPRAEqualityOnlyReference.language ξ n :=
  match r with
  | .eq => .rel EqualityRel.eq (fun i => translatedTerm (v i))
  | .lt => .rel EqualityRel.eq
      ![.func PRATheory.ltBitCode (fun i => translatedTerm (v i)), .func PRALanguage.oneCode Fin.elim0]

def read {ξ : Type} : ∀ {n : ℕ}, Semiformula ℒₒᵣ ξ n →
    Semiformulaᵢ IPRAEqualityOnlyReference.language ξ n
  | _, .verum => ⊤
  | _, .falsum => ⊥
  | _, .rel r v => atom r v
  | _, .nrel r v => ∼atom r v
  | _, .and p q => read p ⋏ read q
  | _, .or p q => read p ⋎ read q
  | _, .all p => ∀⁰ read p
  | _, .exs p => ∃⁰ read p

theorem read_eq_erasure {ξ : Type} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n) :
    read φ = erase (IPRANativeFormula.native (Semiformula.lMap PRALanguage.embedding φ)) := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r v => cases r <;> simp [read, atom, translatedTerm, Semiformula.lMap, Semiformula.lMapAux,
      IPRANativeFormula.native, erase, PRALanguage.embedding, Language.ORing.embedding, Function.comp_def]
  | nrel r v => cases r <;> simp [read, atom, translatedTerm, Semiformula.lMap, Semiformula.lMapAux,
      IPRANativeFormula.native, erase, PRALanguage.embedding, Language.ORing.embedding,
      Semiformulaᵢ.neg_def, Function.comp_def]
  | and p q ihp ihq => simp [read, Semiformula.lMap, Semiformula.lMapAux, IPRANativeFormula.native, erase, ihp, ihq]
  | or p q ihp ihq => simp [read, Semiformula.lMap, Semiformula.lMapAux, IPRANativeFormula.native, erase, ihp, ihq]
  | all p ih => simp [read, Semiformula.lMap, Semiformula.lMapAux, IPRANativeFormula.native, erase, ih]
  | exs p ih => simp [read, Semiformula.lMap, Semiformula.lMapAux, IPRANativeFormula.native, erase, ih]

def refutation : Sentenceᵢ IPRAEqualityOnlyReference.language :=
  read FoundationHAConsistencyNormalization.rho

theorem refutation_eq_erased_native :
    refutation = erase (IPRAFoundationZFCMappedNegation.mappedNativeRefutation PRALanguage.embedding) := by
  exact read_eq_erasure FoundationHAConsistencyNormalization.rho

end DiophantineConsistency.IPRAReferenceRefutationReading
