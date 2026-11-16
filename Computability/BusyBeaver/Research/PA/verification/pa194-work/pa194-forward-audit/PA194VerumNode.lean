import PA194AllInversion
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace PA194VerumNode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PA194TermShiftCodeModel PA194PathIterator PA194BranchSeed
 PA194AllFields PA194AllInversion
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem context_node (s t payload : M) :
    F context (fun _ => pair s (pair t payload)+1) = s := by
  have hroot : F root (fun _ => pair s (pair t payload)+1) = pair s (pair t payload) := by
    rw [root,modelUnary,modelProjection]
    exact modelPredAddOne _
  rw [context,modelUnary,hroot,modelPi1Code firstProjection firstProjection_certified,pi₁_pair]

theorem verum_inversion (T : Theory M6.PA.RelationalSource.language) [T.Δ₁]
    {d : M} (hd : Derivation T d) (ht : F tag (fun _ => d) = 1) :
    ∃ s, d = verumIntro s ∧ IsFormulaSet M6.PA.RelationalSource.language s ∧ qqVerum ∈ s := by
  obtain ⟨hs,hcases⟩ := hd.case
  rcases hcases with (⟨s,p,rfl,hp,hn⟩ | ⟨s,rfl,hv⟩ |
    ⟨s,p,q,dp,dq,rfl,hpq,hp,hq⟩ | ⟨s,p,q,dp,rfl,hpq,hp⟩ |
    ⟨s,p,dp,rfl,hall,hp⟩ | ⟨s,p,t,dp,rfl,hex,htm,hp⟩ |
    ⟨s,dp,rfl,hsub,hp⟩ | ⟨s,dp,rfl,hsub,hp⟩ |
    ⟨s,p,dp,dq,rfl,hp,hq⟩ | ⟨s,p,rfl,hp,hT⟩)
  all_goals simp only [axL,verumIntro,andIntro,orIntro,allIntro,exsIntro,wkRule,shiftRule,cutRule,axm,tag_node] at ht
  all_goals try { norm_num at ht }
  exact ⟨s,rfl,by simpa using hs,hv⟩
theorem selected_verum (T : Theory M6.PA.RelationalSource.language) [T.Δ₁]
    {d : M} (hd : Derivation T d) (ht : F tag (fun _ => d) = 1) :
    IsFormulaSet M6.PA.RelationalSource.language (F context (fun _ => d)) ∧
      qqVerum ∈ F context (fun _ => d) := by
  obtain ⟨s,rfl,hs,hv⟩ := verum_inversion T hd ht
  have h : F context (fun _ => verumIntro s) = s := by
    change F context (fun _ => pair s (pair 1 0)+1) = s
    exact context_node s 1 0
  simpa only [h] using And.intro hs hv

#print axioms context_node
#print axioms selected_verum
#print axioms verum_inversion
end models
end PA194VerumNode
