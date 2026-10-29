import DiophantineConsistency.PRANonzero
import DiophantineConsistency.PRAExhaustion

/-! Characterize the represented nonzero bit in every candidate-PRA model. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRANonzeroCharacter
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAExhaustion PRANonzero

def nonzeroCharacterSentence : Sentence language :=
  ∀⁰* ((Semiformula.rel Language.ORing.Rel.eq
      ![applyCode nonzeroCode (fun _ => .bvar 0), applyCode oneCode Fin.elim0]) 🡘
    (Semiformula.nrel Language.ORing.Rel.eq
      ![.bvar 0, applyCode (.zero 0) Fin.elim0]) : Semisentence language 1)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelOneNeZero : (Structure.func (L := language) oneCode Fin.elim0 : M) ≠
    Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  have h := Theory.models (T := PRA) M (Or.inr BasicAxiom.succNonzero)
  simp [models_iff, succNonzero, Semiformula.eval_allClosure] at h
  have hh := h ![z]
  rw [eqRel] at hh
  have hz : (fun i : Fin 0 => Semiterm.val ![z] Empty.elim (Fin.elim0 i : TermN 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hs : Structure.func (L := language) Code.succ (fun _ => z) ≠ z := by
    simpa [applyCode, Function.comp_def, hz, z] using hh
  have ho := modelComposition (M := M) Code.succ (.cons (.zero 0) (.nil 0))
    (Fin.elim0 : Fin 0 → M)
  have harg : (fun i : Fin 1 => Structure.func (L := language)
      (getCode (.cons (.zero 0) (.nil 0)) i) (Fin.elim0 : Fin 0 → M)) = fun _ => z := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [harg] at ho
  change Structure.func (L := language) oneCode Fin.elim0 = _ at ho
  rw [ho]
  exact hs

theorem modelNonzeroCharacter (x : M) :
    Structure.func (L := language) nonzeroCode (fun _ => x) =
      Structure.func (L := language) oneCode Fin.elim0 ↔
      x ≠ Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  have hEx := modelExhaustion (M := M)
  simp only [models_iff, exhaustionSentence, Semiformula.eval_univCl, Semiformula.eval_all] at hEx
  have hb := (body_eval x (fun _ => x)).mp (hEx (fun _ => x) x)
  constructor
  · intro hv hx
    subst x
    have hzero := modelNonzeroZero (M := M)
    exact modelOneNeZero (M := M) (hv.symm.trans hzero)
  · intro hx
    rcases hb with hz | hs
    · exact False.elim (hx hz)
    · rw [←hs]
      exact modelNonzeroSucc _

theorem modelNonzeroCharacterSentence : M↓[language] ⊧ nonzeroCharacterSentence := by
  simp only [models_iff, nonzeroCharacterSentence, Semiformula.eval_allClosure, LogicalConnective.iff]
  intro e
  trace_state
  sorry

end models
end DiophantineConsistency.PRANonzeroCharacter
