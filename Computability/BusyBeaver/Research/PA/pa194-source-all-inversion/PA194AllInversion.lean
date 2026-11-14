import PA194AllChoiceGraph
/-! Rule-tag inversion and universal-premise choice for internal Foundation
proof codes. This is a rule-specific component, not a whole proof compiler. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace PA194AllInversion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PA194TermShiftCodeModel PA194PathIterator PA194BranchSeed
 PA194AllFields PA194AllChoiceGraph
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

theorem tag_node (s t payload : M) : F tag (fun _ => pair s (pair t payload)+1) = t := by
  have hroot : F root (fun _ => pair s (pair t payload)+1) = pair s (pair t payload) := by
    rw [root,modelUnary,modelProjection]
    exact modelPredAddOne _
  rw [tag,modelUnary,rest,modelUnary,hroot,
    modelPi2Code secondProjection secondProjection_certified,pi₂_pair,
    modelPi1Code firstProjection firstProjection_certified,pi₁_pair]

theorem all_inversion (T : Theory M6.PA.RelationalSource.language) [T.Δ₁]
    {d : M} (hd : Derivation T d) (ht : F tag (fun _ => d) = 4) :
    ∃ s p dp, d = allIntro s p dp ∧ IsFormulaSet M6.PA.RelationalSource.language s ∧
      ^∀ p ∈ s ∧ DerivationOf T dp (insert (free M6.PA.RelationalSource.language p)
        (setShift M6.PA.RelationalSource.language s)) := by
  obtain ⟨hs,hcases⟩ := hd.case
  rcases hcases with (⟨s,p,rfl,hp,hn⟩ | ⟨s,rfl,hv⟩ |
    ⟨s,p,q,dp,dq,rfl,hpq,hp,hq⟩ | ⟨s,p,q,dp,rfl,hpq,hp⟩ |
    ⟨s,p,dp,rfl,hall,hp⟩ | ⟨s,p,t,dp,rfl,hex,htm,hp⟩ |
    ⟨s,dp,rfl,hsub,hp⟩ | ⟨s,dp,rfl,hsub,hp⟩ |
    ⟨s,p,dp,dq,rfl,hp,hq⟩ | ⟨s,p,rfl,hp,hT⟩)
  all_goals simp only [axL,verumIntro,andIntro,orIntro,allIntro,exsIntro,wkRule,shiftRule,cutRule,axm,tag_node] at ht
  all_goals try { norm_num at ht }
  exact ⟨s,p,dp,rfl,by simpa using hs,hall,hp⟩

theorem all_graph_from_derivation (T : Theory M6.PA.RelationalSource.language) [T.Δ₁]
    {d q y : M} (hd : Derivation T d) (ht : F tag (fun _ => d) = 4)
    (hq : q ∈ fstIdx (F child (fun _ => d)))
    (hy : choiceGraph.val.Eval ![y,d,q] Empty.elim) :
    let s := F context (fun _ => d)
    let p := F body (fun _ => d)
    (q = free M6.PA.RelationalSource.language p ∧ y = 0) ∨
      ∃ u, y = u+1 ∧ u ∈ s ∧ shift M6.PA.RelationalSource.language u = q := by
  obtain ⟨s,p,dp,rfl,hs,hall,hdp⟩ := all_inversion T hd ht
  have hf := fields_all s p dp
  rw [hf.2.2.2] at hq
  rw [hdp.1] at hq
  change (q = free M6.PA.RelationalSource.language (F body (fun _ => allIntro s p dp)) ∧ y = 0) ∨
    ∃ u, y = u+1 ∧ u ∈ F context (fun _ => allIntro s p dp) ∧
      shift M6.PA.RelationalSource.language u = q
  rw [hf.1,hf.2.2.1]
  exact all_choice_graph T s p dp q y hdp hq hy

#print axioms all_graph_from_derivation

#print axioms all_inversion
end models
end PA194AllInversion
