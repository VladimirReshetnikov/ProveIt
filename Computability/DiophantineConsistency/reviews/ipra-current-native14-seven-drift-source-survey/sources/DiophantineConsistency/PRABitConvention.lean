import DiophantineConsistency.PRABooleanOps
set_option autoImplicit false
namespace DiophantineConsistency.PRABitConvention
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAIsZero PRABooleanOps PRANonzeroCharacter

def z : TermN 1 := applyCode (.zero 0) Fin.elim0
def o : TermN 1 := applyCode oneCode Fin.elim0
def iz : TermN 1 := applyCode isZeroCode (fun _ => #0)
def matrix : Semisentence language 1 :=
  ((.rel .eq ![#0,z]) ⋎ (.rel .eq ![#0,o])) 🡒
    ((.rel .eq ![iz,z]) 🡘 (.rel .eq ![#0,o]))
def sentence : Sentence language := ∀⁰* matrix
theorem matrix_open : matrix.Open := by simp [matrix, Semiformula.Open]

section model
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
theorem modelSentence : M↓[language] ⊧ sentence := by
  simp only [models_iff, sentence, Semiformula.eval_allClosure]
  intro e
  simp [matrix, eqRel, applyCode, z, o, iz, Function.comp_def]
  have hz : (fun i : Fin 0 => Semiterm.val e Empty.elim (Fin.elim0 i : TermN 1)) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz]
  have hb := modelIsZeroBit (e 0)
  have hc := modelIsZeroCharacter (e 0)
  have hn := modelOneNeZero (M := M)
  simp only [IsBit] at hb
  have hx : e 0 = Structure.func (L := language) (Code.zero 0) Fin.elim0 →
      e 0 = Structure.func (L := language) oneCode Fin.elim0 → False :=
    fun h₀ h₁ => hn (h₁.symm.trans h₀)
  have hi : Structure.func (L := language) isZeroCode (fun _ => e 0) = Structure.func (L := language) (Code.zero 0) Fin.elim0 →
      Structure.func (L := language) isZeroCode (fun _ => e 0) = Structure.func (L := language) oneCode Fin.elim0 → False :=
    fun h₀ h₁ => hn (h₁.symm.trans h₀)
  tauto
end model

theorem PRA_proves_sentence : PRA ⊢ sentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence
end DiophantineConsistency.PRABitConvention
