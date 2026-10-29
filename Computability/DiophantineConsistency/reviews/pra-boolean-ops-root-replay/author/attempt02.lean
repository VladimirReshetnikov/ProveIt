import DiophantineConsistency.PRAIsZero
import DiophantineConsistency.PRAAdditionZeroLeft

/-! Boolean operations represented by fixed primitive-recursive codes. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRABooleanOps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAAdditionZeroLeft
  PRAExhaustion PRAMultiplication PRANonzero PRANonzeroCharacter PRAIsZero

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

def IsBit (x : M) : Prop :=
  x = Structure.func (L := language) (Code.zero 0) Fin.elim0 ∨
  x = Structure.func (L := language) oneCode Fin.elim0

theorem modelOneSuccZero : (Structure.func (L := language) oneCode Fin.elim0 : M) =
    Structure.func (L := language) Code.succ
      (fun _ => Structure.func (L := language) (Code.zero 0) Fin.elim0) := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let o : M := Structure.func (L := language) oneCode Fin.elim0
  have h := modelAddOne z
  have h' := modelZeroLeft o
  exact h'.symm.trans h

theorem modelNonzeroBit (x : M) : IsBit (Structure.func (L := language) nonzeroCode (fun _ => x)) := by
  have hex := modelExhaustion (M := M)
  simp only [models_iff, exhaustionSentence, Semiformula.eval_univCl, Semiformula.eval_all] at hex
  rcases (body_eval x (fun _ => x)).mp (hex (fun _ => x) x) with hz | hs
  · left
    rw [hz]
    exact modelNonzeroZero
  · right
    rw [←hs]
    exact modelNonzeroSucc _

theorem modelIsZeroBit (x : M) : IsBit (Structure.func (L := language) isZeroCode (fun _ => x)) := by
  have hex := modelExhaustion (M := M)
  simp only [models_iff, exhaustionSentence, Semiformula.eval_univCl, Semiformula.eval_all] at hex
  rcases (body_eval x (fun _ => x)).mp (hex (fun _ => x) x) with hz | hs
  · right
    rw [hz]
    exact modelIsZeroZero
  · left
    rw [←hs]
    exact modelIsZeroSucc _

theorem modelMulOne (x : M) :
    Structure.func (L := language) mulCode
      ![x, Structure.func (L := language) oneCode Fin.elim0] = x := by
  rw [modelOneSuccZero, modelMulSucc, modelMulZero, modelZeroLeft]

theorem modelMulBit (x y : M) (hx : IsBit x) (hy : IsBit y) :
    IsBit (Structure.func (L := language) mulCode ![x,y]) ∧
      (Structure.func (L := language) mulCode ![x,y] =
        Structure.func (L := language) oneCode Fin.elim0 ↔
        x = Structure.func (L := language) oneCode Fin.elim0 ∧
        y = Structure.func (L := language) oneCode Fin.elim0) := by
  rcases hy with hy | hy
  · rw [hy, modelMulZero]
    constructor
    · exact Or.inl rfl
    · have hne := modelOneNeZero (M := M)
      constructor
      · intro he
        exact False.elim (hne he.symm)
      · rintro ⟨_,he⟩
        exact False.elim (hne he.symm)
  · rw [hy, modelMulOne]
    constructor
    · exact hx
    · simp

theorem modelNotBit (x : M) (hx : IsBit x) :
    IsBit (Structure.func (L := language) isZeroCode (fun _ => x)) ∧
      (Structure.func (L := language) isZeroCode (fun _ => x) =
        Structure.func (L := language) oneCode Fin.elim0 ↔
        x ≠ Structure.func (L := language) oneCode Fin.elim0) := by
  constructor
  · exact modelIsZeroBit x
  · rw [modelIsZeroCharacter]
    rcases hx with hz | ho
    · rw [hz]
      have hne := modelOneNeZero (M := M)
      simp [Ne.symm hne]
    · rw [ho]
      have hne := modelOneNeZero (M := M)
      simp [hne]

end models
end DiophantineConsistency.PRABooleanOps
