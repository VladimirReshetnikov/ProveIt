import PA194AllChoice
/-! Exact Foundation all-introduction fields and premise selection.
The distinguished free formula remains an explicit input. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
namespace PA194AllFields
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PA194TermShiftCodeModel PA194PathIterator PA194BranchSeed PA194AllChoice

noncomputable def root : Code 1 := unary predCode (.proj 0)
noncomputable def context : Code 1 := unary firstProjection root
noncomputable def rest : Code 1 := unary secondProjection root
noncomputable def tag : Code 1 := unary firstProjection rest
noncomputable def args : Code 1 := unary secondProjection rest
noncomputable def body : Code 1 := unary firstProjection args
noncomputable def child : Code 1 := unary secondProjection args

/-- Decode the conclusion set from an all-introduction node, then classify
an actual premise member against an explicitly supplied distinguished formula. -/
noncomputable def nodeChoice : Code 3 := .comp choiceCode
  (.cons (unary context (.proj 0)) (.cons (.proj 1) (.cons (.proj 2) (.nil 3))))

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

theorem fields_all (s p dp : M) :
    let e : Fin 1 → M := fun _ => allIntro s p dp
    F context e = s ∧ F tag e = 4 ∧ F body e = p ∧ F child e = dp := by
  dsimp only
  have hroot : F root (fun _ => allIntro s p dp) = pair s (pair 4 (pair p dp)) := by
    rw [root,modelUnary,modelProjection]
    change F predCode (fun _ => pair s (pair 4 (pair p dp))+1) = _
    exact modelPredAddOne _
  have hc : F context (fun _ => allIntro s p dp) = s := by
    rw [context,modelUnary,hroot,modelPi1Code firstProjection firstProjection_certified,pi₁_pair]
  have hr : F rest (fun _ => allIntro s p dp) = pair 4 (pair p dp) := by
    rw [rest,modelUnary,hroot,modelPi2Code secondProjection secondProjection_certified,pi₂_pair]
  have ht : F tag (fun _ => allIntro s p dp) = 4 := by
    rw [tag,modelUnary,hr,modelPi1Code firstProjection firstProjection_certified,pi₁_pair]
  have ha : F args (fun _ => allIntro s p dp) = pair p dp := by
    rw [args,modelUnary,hr,modelPi2Code secondProjection secondProjection_certified,pi₂_pair]
  have hp : F body (fun _ => allIntro s p dp) = p := by
    rw [body,modelUnary,ha,modelPi1Code firstProjection firstProjection_certified,pi₁_pair]
  have hd : F child (fun _ => allIntro s p dp) = dp := by
    rw [child,modelUnary,ha,modelPi2Code secondProjection secondProjection_certified,pi₂_pair]
  exact ⟨hc,ht,hp,hd⟩
theorem node_choice_model (s p dp special q : M) :
    F nodeChoice ![allIntro s p dp,special,q] = F choiceCode ![s,special,q] := by
  rw [nodeChoice,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change F (unary context (.proj 0)) ![allIntro s p dp,special,q] = s
    rw [modelUnary,modelProjection]
    exact (fields_all s p dp).1
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact modelProjection 1 _
    · refine Fin.cases ?_ (fun l => Fin.elim0 l) k
      exact modelProjection 2 _

theorem all_node_choice (T : Theory M6.PA.RelationalSource.language) [T.Δ₁]
    (s p dp q : M)
    (hdp : DerivationOf T dp (insert (free M6.PA.RelationalSource.language p)
      (setShift M6.PA.RelationalSource.language s)))
    (hq : q ∈ insert (free M6.PA.RelationalSource.language p)
      (setShift M6.PA.RelationalSource.language s)) :
    let value := F nodeChoice ![allIntro s p dp, free M6.PA.RelationalSource.language p,q]
    (q = free M6.PA.RelationalSource.language p ∧ value = 0) ∨
      ∃ u, value = u+1 ∧ u ∈ s ∧ shift M6.PA.RelationalSource.language u = q := by
  rw [node_choice_model]
  exact all_premise_choice T s p dp q hdp hq

#print axioms all_node_choice

#print axioms fields_all
end models
end PA194AllFields
