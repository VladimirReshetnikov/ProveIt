import PA196PASubstitutionPath

/-! The recursive branches of the actual substitution fixpoint satisfy the
one-step relation used by PA196PASubstitutionPath. This exposes one child,
not a full coded chain or an upper bound on the fixpoint stage. -/
set_option autoImplicit false
namespace PA196PASubstitutionPhi
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA196PASubstitutionPath
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne

variable {V : Type} [Nonempty V] [Structure language V] [Structure.Eq language V]
  [V↓[language] ⊧* PRA]
local instance : Zero V := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One V := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add V := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul V := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT V := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def atomic (p : V) : Prop :=
  (∃ k r v, p = ^rel k r v) ∨ (∃ k r v, p = ^nrel k r v) ∨ p = ^⊤ ∨ p = ^⊥

omit [Structure.Eq language V] [V↓[language] ⊧* PRA] in
theorem phi_atomic_or_child (C : Set V) (node : V)
    (h : (Substs.construction (V := V) ℒₒᵣ).Phi ℒₒᵣ C node) :
    ∃ w p y, node = ⟪w,p,y⟫ ∧ IsUFormula ℒₒᵣ p ∧
      (atomic p ∨ ∃ w' p' y', ⟪w',p',y'⟫ ∈ C ∧ step w p w' p') := by
  obtain ⟨w,p,y,hn,hp,hcase⟩ := h
  refine ⟨w,p,y,hn,hp,?_⟩
  rcases hcase with ⟨k,r,v,he,_⟩ | ⟨k,r,v,he,_⟩ | ⟨he,_⟩ | ⟨he,_⟩ |
      ⟨a,b,ya,yb,ha,hb,he,_⟩ | ⟨a,b,ya,yb,ha,hb,he,_⟩ |
      ⟨a,ya,ha,he,_⟩ | ⟨a,ya,ha,he,_⟩
  · exact Or.inl (Or.inl ⟨k,r,v,he⟩)
  · exact Or.inl (Or.inr (Or.inl ⟨k,r,v,he⟩))
  · exact Or.inl (Or.inr (Or.inr (Or.inl he)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr he)))
  · exact Or.inr ⟨w,a,ya,ha,Or.inl ⟨a,b,he,Or.inl rfl,rfl⟩⟩
  · exact Or.inr ⟨w,a,ya,ha,Or.inr (Or.inl ⟨a,b,he,Or.inl rfl,rfl⟩)⟩
  · exact Or.inr ⟨qVec ℒₒᵣ w,a,ya,by simpa [Substs.construction] using ha,
      Or.inr (Or.inr (Or.inl ⟨a,he,rfl,rfl⟩))⟩
  · exact Or.inr ⟨qVec ℒₒᵣ w,a,ya,by simpa [Substs.construction] using ha,
      Or.inr (Or.inr (Or.inr ⟨a,he,rfl,rfl⟩))⟩

#print axioms phi_atomic_or_child
end PA196PASubstitutionPhi
