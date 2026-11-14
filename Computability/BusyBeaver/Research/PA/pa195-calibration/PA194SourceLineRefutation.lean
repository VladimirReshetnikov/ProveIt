import PA194SourceLineSoundness
import PA194ContradictionInternalRefutation
/-! Conditional model-internal PA refutation from a valid numerical source
line history containing the distinguished contradiction code. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194SourceLineRefutation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194SourceOutputWF PA194SourceLineSoundness PA194ContradictionTranslation PA194ContradictionInternalRefutation
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem line_refutes_PA (lines : M) (seed : M → Prop)
    (hseed : ∀ x, seed x → Provable (𝗣𝗔 : ArithmeticTheory) (translated x))
    (hline : ∀ i < len lines, seed lines.[i] ∨
      (∃ j < i, ∃ k < i, lines.[k] = 4*cantor lines.[j] lines.[i]) ∨
      (∃ j < i, ∃ label, lines.[i] = 4*cantor lines.[j] label+2))
    (i : M) (hi : i < len lines) (hcontra : lines.[i] = 1) :
    Provable (𝗣𝗔 : ArithmeticTheory) (^⊥ : M) := by
  have h := line_sound lines seed hseed hline i hi
  rw [hcontra] at h
  unfold translated at h
  rw [positive_code_one] at h
  exact contradiction_provable_implies_falsum h

#print axioms line_refutes_PA
end models
end PA194SourceLineRefutation
