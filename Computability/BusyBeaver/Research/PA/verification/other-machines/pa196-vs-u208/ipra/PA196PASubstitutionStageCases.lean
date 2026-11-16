import PA196PASubstitutionStageChild

/-! Exact recursive predecessor-stage cases for arithmetic substitution.
In each binary branch *both* recursive children are recorded. -/
set_option autoImplicit false
namespace PA196PASubstitutionStageCases
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

def recursiveChildren (C : Set V) (w p : V) : Prop :=
  (∃ a b ya yb, p = a ^⋏ b ∧ ⟪w,a,ya⟫ ∈ C ∧ ⟪w,b,yb⟫ ∈ C) ∨
  (∃ a b ya yb, p = a ^⋎ b ∧ ⟪w,a,ya⟫ ∈ C ∧ ⟪w,b,yb⟫ ∈ C) ∨
  (∃ a ya, p = ^∀ a ∧ ⟪qVec ℒₒᵣ w,a,ya⟫ ∈ C) ∨
  (∃ a ya, p = ^∃ a ∧ ⟪qVec ℒₒᵣ w,a,ya⟫ ∈ C)

omit [Structure.Eq language V] [V↓[language] ⊧* PRA] in
theorem stage_succ_cases (node s : V) (h : node ∈ substStage (s+1)) :
    ∃ w p y, node = ⟪w,p,y⟫ ∧ IsUFormula ℒₒᵣ p ∧
      (atomic p ∨ recursiveChildren {z | z ∈ substStage s} w p) := by
  have hphi := ((substFix (V := V)).mem_limSeq_succ_iff (v := ![])).mp h
  obtain ⟨w,p,y,hn,hp,hcase⟩ := hphi.2
  refine ⟨w,p,y,hn,hp,?_⟩
  rcases hcase with ⟨k,r,v,he,_⟩ | ⟨k,r,v,he,_⟩ | ⟨he,_⟩ | ⟨he,_⟩ |
      ⟨a,b,ya,yb,ha,hb,he,_⟩ | ⟨a,b,ya,yb,ha,hb,he,_⟩ |
      ⟨a,ya,ha,he,_⟩ | ⟨a,ya,ha,he,_⟩
  · exact Or.inl (Or.inl ⟨k,r,v,he⟩)
  · exact Or.inl (Or.inr (Or.inl ⟨k,r,v,he⟩))
  · exact Or.inl (Or.inr (Or.inr (Or.inl he)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr he)))
  · exact Or.inr (Or.inl ⟨a,b,ya,yb,he,ha,hb⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a,b,ya,yb,he,ha,hb⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a,ya,he,by simpa [Substs.construction, substStage] using ha⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a,ya,he,by simpa [Substs.construction, substStage] using ha⟩)))

#print axioms stage_succ_cases
end PA196PASubstitutionStageCases
