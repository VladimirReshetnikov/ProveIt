import DiophantineConsistency.PRAHistoryInsertCode

/-! Exceptional source alias I(0,0)=0. -/
set_option autoImplicit false
namespace PA194ZeroAlias
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

/-- PA194's source implication constructor, before decoding. -/
def sourceImp (a b : Nat) : Nat := 4 * ((a+b) * (a+b+1) / 2 + b)

theorem sourceImp_zero : sourceImp 0 0 = 0 := by decide

/-- Chosen arithmetic translation of source truth code zero. -/
noncomputable def truth : ArithmeticSentence := “0 = 0”

theorem PA_proves_zero_alias : (𝗣𝗔 : ArithmeticTheory) ⊢ truth 🡘 (truth 🡒 truth) := by
  letI : 𝗘𝗤 ℒₒᵣ ⪯ (𝗣𝗔 : ArithmeticTheory) :=
    Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₀) (inferInstance : 𝗜𝚺₀ ⪯ 𝗣𝗔)
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  simp [models_iff, truth, LogicalConnective.iff,
    Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

#print axioms sourceImp_zero
#print axioms PA_proves_zero_alias
end PA194ZeroAlias
