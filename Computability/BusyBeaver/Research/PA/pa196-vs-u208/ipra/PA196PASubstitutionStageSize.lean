import PA196PASubstitutionStageChild

/-! Every element occurring in an arithmetic substitution stage is below the
stage index. This is a lower bound on a stage containing an element, not
the upper stage bound needed for witness extraction. -/
set_option autoImplicit false
namespace PA196PASubstitutionStageSize
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PA196PASubstitutionStageChild

variable {V : Type} [Nonempty V] [Structure language V] [Structure.Eq language V]
  [V↓[language] ⊧* PRA]
local instance : Zero V := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One V := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add V := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul V := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT V := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

omit [Structure.Eq language V] [V↓[language] ⊧* PRA] in
theorem element_lt_stage {node s : V} (h : node ∈ substStage s) : node < s := by
  rcases zero_or_succ s with rfl | ⟨t,rfl⟩
  · simp [substStage, substFix] at h
  · have ht := ((substFix (V := V)).mem_limSeq_succ_iff (v := ![])).mp h
    exact lt_succ_iff_le.mpr ht.1

#print axioms element_lt_stage
end PA196PASubstitutionStageSize
