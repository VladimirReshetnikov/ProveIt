import PA196PASubstitutionStageCases

/-! Exact recursive predecessor-stage cases for arithmetic substitution.
In each binary branch *both* recursive children are recorded. -/
set_option autoImplicit false
namespace PA196PASubstitutionStageResults
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PA196PASubstitutionPhi PA196PASubstitutionStageChild

variable {V : Type} [Nonempty V] [Structure language V] [Structure.Eq language V]
  [V↓[language] ⊧* PRA]
local instance : Zero V := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One V := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add V := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul V := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT V := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def recursiveChildrenWithResults (C : Set V) (w p y : V) : Prop :=
  (∃ a b ya yb, p = a ^⋏ b ∧ y = ya ^⋏ yb ∧ ⟪w,a,ya⟫ ∈ C ∧ ⟪w,b,yb⟫ ∈ C) ∨
  (∃ a b ya yb, p = a ^⋎ b ∧ y = ya ^⋎ yb ∧ ⟪w,a,ya⟫ ∈ C ∧ ⟪w,b,yb⟫ ∈ C) ∨
  (∃ a ya, p = ^∀ a ∧ y = ^∀ ya ∧ ⟪qVec ℒₒᵣ w,a,ya⟫ ∈ C) ∨
  (∃ a ya, p = ^∃ a ∧ y = ^∃ ya ∧ ⟪qVec ℒₒᵣ w,a,ya⟫ ∈ C)

omit [Structure.Eq language V] [V↓[language] ⊧* PRA] in
theorem stage_succ_result_cases (node s : V) (h : node ∈ substStage (s+1)) :
    ∃ w p y, node = ⟪w,p,y⟫ ∧ IsUFormula ℒₒᵣ p ∧
      (atomic p ∨ recursiveChildrenWithResults {z | z ∈ substStage s} w p y) := by
  have hphi := ((substFix (V := V)).mem_limSeq_succ_iff (v := ![])).mp h
  obtain ⟨w,p,y,hn,hp,hcase⟩ := hphi.2
  refine ⟨w,p,y,hn,hp,?_⟩
  rcases hcase with ⟨k,r,v,he,_⟩ | ⟨k,r,v,he,_⟩ | ⟨he,_⟩ | ⟨he,_⟩ |
      ⟨a,b,ya,yb,ha,hb,he,hy⟩ | ⟨a,b,ya,yb,ha,hb,he,hy⟩ |
      ⟨a,ya,ha,he,hy⟩ | ⟨a,ya,ha,he,hy⟩
  · exact Or.inl (Or.inl ⟨k,r,v,he⟩)
  · exact Or.inl (Or.inr (Or.inl ⟨k,r,v,he⟩))
  · exact Or.inl (Or.inr (Or.inr (Or.inl he)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr he)))
  · exact Or.inr (Or.inl ⟨a,b,ya,yb,he,by simpa [Substs.construction] using hy,ha,hb⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a,b,ya,yb,he,by simpa [Substs.construction] using hy,ha,hb⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a,ya,he,by simpa [Substs.construction] using hy,by simpa [Substs.construction, substStage] using ha⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a,ya,he,by simpa [Substs.construction] using hy,by simpa [Substs.construction, substStage] using ha⟩)))

#print axioms stage_succ_result_cases
end PA196PASubstitutionStageResults
