import PA194NameFactsProof
import PA194ZeroDomainExistence
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194ZeroDomainExistence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194Schematic PA194GuardedCompiler PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
open M6.PA.RelationalSource M6.PA.RelationalSource.Ordinal
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem z1_code : (tHyp sZ1 : Bootstrapping.Formula V SourceL).val = (⌜zeroExists⌝ : V) := by
  change (tHyp sZ1 : Bootstrapping.Formula V SourceL).val =
    (⌜(∃⁰ (domain (.bvar 0) ⋏ zero (.bvar 0)) : Proposition M6.PA.RelationalSource.language)⌝ : V)
  rw [Semiformula.quote_ex,Semiformula.quote_and,
    ←domainCode_quote (.bvar (0 : Fin 1)),←zeroCode_quote (.bvar (0 : Fin 1))]
  simp [tHyp,sZ1,instS_sDom,instS_sZero,tDom_val,tZero_val,Semiterm.quote_def]
#print axioms z1_code
end generic
end PA194ZeroDomainExistence
