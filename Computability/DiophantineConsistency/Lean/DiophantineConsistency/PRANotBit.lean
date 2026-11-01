import DiophantineConsistency.PRABooleanOps
import DiophantineConsistency.PRAOpenFormulaCompiler
set_option autoImplicit false
namespace DiophantineConsistency.PRANotBit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAIsZero PRAOpenFormulaCompiler PRABooleanOps PRANonzeroCharacter

def z {n : ℕ} : TermN n := applyCode (.zero 0) Fin.elim0
def o {n : ℕ} : TermN n := applyCode oneCode Fin.elim0
def arg {n : ℕ} (c : Code n) : TermN n := applyCode c (vars n)
def notarg {n : ℕ} (c : Code n) : TermN n := applyCode (notCode c) (vars n)
def matrix {n : ℕ} (c : Code n) : Semisentence language n :=
  ((.rel .eq ![arg c,z]) ⋎ (.rel .eq ![arg c,o])) 🡒
    ((.rel .eq ![notarg c,z]) 🡘 (.rel .eq ![arg c,o]))
def sentence {n : ℕ} (c : Code n) : Sentence language := ∀⁰* matrix c
theorem matrix_open {n : ℕ} (c : Code n) : (matrix c).Open := by simp [matrix, Semiformula.Open]

section model
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
theorem modelSentence {n : ℕ} (c : Code n) : M↓[language] ⊧ sentence c := by
  simp only [models_iff, sentence, Semiformula.eval_allClosure]
  intro e
  simp [matrix, eqRel, applyCode, vars, arg, notarg, z, o, Function.comp_def]
  have hz : (fun i : Fin 0 => Semiterm.val e Empty.elim (Fin.elim0 i : TermN n)) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz, modelNotCode]
  let x := Structure.func (L := language) c e
  have hb := modelIsZeroBit x
  have hc := modelIsZeroCharacter x
  have hn := modelOneNeZero (M := M)
  simp only [IsBit] at hb
  have hx : x = Structure.func (L := language) (Code.zero 0) Fin.elim0 →
      x = Structure.func (L := language) oneCode Fin.elim0 → False := fun h₀ h₁ => hn (h₁.symm.trans h₀)
  have hi : Structure.func (L := language) isZeroCode (fun _ => x) = Structure.func (L := language) (Code.zero 0) Fin.elim0 →
      Structure.func (L := language) isZeroCode (fun _ => x) = Structure.func (L := language) oneCode Fin.elim0 → False :=
    fun h₀ h₁ => hn (h₁.symm.trans h₀)
  change x = _ ∨ x = _ → _
  tauto
end model

theorem PRA_proves_sentence {n : ℕ} (c : Code n) : PRA ⊢ sentence c := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence c
end DiophantineConsistency.PRANotBit
