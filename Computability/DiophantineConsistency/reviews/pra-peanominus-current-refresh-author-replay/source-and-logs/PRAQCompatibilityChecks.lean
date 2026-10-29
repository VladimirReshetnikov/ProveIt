import DiophantineConsistency.PRAQCompatibility

set_option autoImplicit false
namespace DiophantineConsistency.PRAQCompatibilityChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAQCompatibility

example : qSuccNeZero ∈ RobinsonQ := qSuccNeZero_mem
example : qSuccInj ∈ RobinsonQ := qSuccInj_mem
example : qZeroOrSucc ∈ RobinsonQ := qZeroOrSucc_mem
example : qAddZero ∈ RobinsonQ := qAddZero_mem
example : qAddSucc ∈ RobinsonQ := qAddSucc_mem
example : qMulZero ∈ RobinsonQ := qMulZero_mem
example : qMulSucc ∈ RobinsonQ := qMulSucc_mem
example {σ : Sentence ℒₒᵣ} (h : σ ∈ 𝗘𝗤 ℒₒᵣ) : PRA ⊢ Semiformula.lMap embedding σ :=
  PRA_proves_qEquality h
example {σ : Sentence ℒₒᵣ} (h : RobinsonQ σ) (hn : σ ≠ qLtDef) :
    PRA ⊢ Semiformula.lMap embedding σ := PRA_proves_qExceptOrder h hn
example : PRA ⊢ Semiformula.lMap embedding qAddSucc := PRA_proves_qAddSucc
example : PRA ⊢ Semiformula.lMap embedding qMulSucc := PRA_proves_qMulSucc

#print axioms model_qEquality
#print axioms model_qSuccNeZero
#print axioms model_qSuccInj
#print axioms model_qZeroOrSucc
#print axioms model_qAddZero
#print axioms model_qAddSucc
#print axioms model_qMulZero
#print axioms model_qMulSucc
#print axioms PRA_proves_qExceptOrder
end DiophantineConsistency.PRAQCompatibilityChecks
