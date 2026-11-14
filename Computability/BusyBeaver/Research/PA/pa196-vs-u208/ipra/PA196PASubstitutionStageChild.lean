import PA196PASubstitutionPhi

/-! Every actual substitution-fixpoint element at a successor stage is atomic
or has an exact recursive child in the previous stage. This is a one-step
statement, not yet a bound on substitution output or a coded entire path. -/
set_option autoImplicit false
namespace PA196PASubstitutionStageChild
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PA196PASubstitutionPath PA196PASubstitutionPhi

variable {V : Type} [Nonempty V] [Structure language V] [Structure.Eq language V]
  [V↓[language] ⊧* PRA]
local instance : Zero V := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One V := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add V := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul V := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT V := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def substFix := (Substs.construction (V := V) ℒₒᵣ).construction ℒₒᵣ
noncomputable def substStage (s : V) : V := (substFix (V := V)).limSeq ![] s

omit [Structure.Eq language V] [V↓[language] ⊧* PRA] in
theorem stage_succ_atomic_or_child (node s : V) (h : node ∈ substStage (s+1)) :
    ∃ w p y, node = ⟪w,p,y⟫ ∧ IsUFormula ℒₒᵣ p ∧
      (atomic p ∨ ∃ w' p' y', ⟪w',p',y'⟫ ∈ substStage s ∧ step w p w' p') := by
  have hphi := ((substFix (V := V)).mem_limSeq_succ_iff (v := ![])).mp h
  exact phi_atomic_or_child _ _ hphi.2

#print axioms stage_succ_atomic_or_child
end PA196PASubstitutionStageChild
