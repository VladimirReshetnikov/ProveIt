import PA194SourceUniversalPreservation
import PA194SourceMPPreservation
/-! Conditional soundness of model-internal numerical source proof lines.
The seed-axiom and machine-trace obligations are explicit assumptions. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194SourceLineSoundness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194SourceOutputWF
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

noncomputable def translated (x : M) : M := π₁ (F fixedTranslation (fun _ => x))

lemma translated_definable : 𝚺₁-Function₁ (translated (M := M)) := by
  have hg : 𝚺₁.DefinableFunction (fun v : Fin 1 → M => F fixedTranslation v) :=
    HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph fixedTranslation)
  haveI : 𝚺₁-Function₁ (fun x : M => F fixedTranslation (fun _ => x)) := by
    change 𝚺₁.DefinableFunction (fun v : Fin 1 → M => F fixedTranslation (fun _ => v 0))
    convert hg using 1
    funext v
    congr 1
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  unfold translated
  definability

lemma translatedProvable_definable : 𝚺₁-Predicate (fun x : M => Provable (𝗣𝗔 : ArithmeticTheory) (translated x)) := by
  haveI := translated_definable (M := M)
  definability

def good (x : M) : Prop := Provable (𝗣𝗔 : ArithmeticTheory) (translated x)

lemma good_definable : 𝚺₁-Predicate (good (M := M)) := translatedProvable_definable

/-- An internal line list is closed by numerical MP and universal rules,
conditionally on the supplied seeds being internally PA provable. -/
theorem line_sound (lines : M) (seed : M → Prop)
    (hseed : ∀ x, seed x → Provable (𝗣𝗔 : ArithmeticTheory) (translated x))
    (hline : ∀ i < len lines, seed lines.[i] ∨
      (∃ j < i, ∃ k < i, lines.[k] = 4*cantor lines.[j] lines.[i]) ∨
      (∃ j < i, ∃ label, lines.[i] = 4*cantor lines.[j] label+2)) :
    ∀ i < len lines, Provable (𝗣𝗔 : ArithmeticTheory) (translated lines.[i]) := by
  haveI := good_definable (M := M)
  have hdef : 𝚺₁-Predicate (fun n : M => ∀ i < n, i < len lines → good lines.[i]) := by
    definability
  have hall : ∀ n : M, ∀ i < n, i < len lines → good lines.[i] := by
    intro n
    induction n using ISigma1.sigma1_succ_induction
    · exact hdef
    case zero => intro i hi; exact False.elim (not_lt_zero hi)
    case succ n ih =>
      intro i hi hil
      by_cases hlt : i < n
      · exact ih i hlt hil
      · have hieq : i = n := le_antisymm (lt_succ_iff_le.mp hi) (le_of_not_gt hlt)
        subst i
        rcases hline n hil with (hs | ⟨j,hj,k,hk,himp⟩ | ⟨j,hj,label,hall⟩)
        · exact hseed _ hs
        · have hminor := ih j hj (lt_trans hj hil)
          have hmajor := ih k hk (lt_trans hk hil)
          rw [himp] at hmajor
          exact PA194SourceMPPreservation.mp lines.[j] lines.[n] hmajor hminor
        · have hminor := ih j hj (lt_trans hj hil)
          rw [hall]
          exact PA194SourceUniversalPreservation.source_universal_preservation label lines.[j] hminor
  intro i hi
  exact hall (len lines) i hi hi

#print axioms line_sound
end models
end PA194SourceLineSoundness
