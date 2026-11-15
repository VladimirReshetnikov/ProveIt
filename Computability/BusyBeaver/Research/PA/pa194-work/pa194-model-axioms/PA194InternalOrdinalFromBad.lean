import PA194BadOrdinalEliminate
import PA194InductionPackaging
import PA194InternalOrdinalConclusion
import PA194DomainSuccessorWitness
import PA194SuccessorMemberAt
import PA194BadInsideEliminate
import PA194LeastBadEliminate
import PA194ContextualBaseShift
import PA194LeastMemberProjection
import PA194DirectBadGreatest
import PA194LeastWitnessOpen
import PA194TraceLeastExists
import PA194GreatestBadEliminate
import PA194BadTraceStepShift
import PA194FixedInstanceShift
import PA194LeastDummyIndex
import PA194GreatestWitnessOpen
import PA194GreatestBadContradiction
import PA194GreatestBadStep
import PA194ContextContradictionCode
import PA194GreatestMemberProjection
import PA194OrdinalStepApplicationCode
import PA194LeastBadDirectGoodTransitive
import PA194LeastBadDirectMemberGood
import PA194LeastBadMemberGoodCode
import PA194DomainTransitiveInstances
import PA194LeastExcludesInstances
import PA194OrdinalBadNotZeroCode
import PA194ContextAndProjectionCode
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace PA194InternalOrdinalFromBad
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ContextAllCode PA194OrdinalFixed PA194BadOrdinalEliminate PA194InductionPackaging PA194InternalOrdinalConclusion PA194DomainSuccessorWitness PA194DomainSuccessorAt PA194DomainSuccessorClosedModel PA194DomainSuccessorClosedTemplate PA194SuccessorMemberAt PA194SuccessorMemberClosedTemplate PA194SuccessorMemberClosedModel PA194BadInsideEliminate PA194DomainLeastClosedTemplate PA194SeparationWitnessFromRoot PA194LeastBadEliminate PA194DomainGreatestClosedModel PA194DomainLeastClosedTemplate PA194DomainLeastClosedModel PA194TraceLeastExists PA194ContextualBaseShift PA194LeastMemberProjection PA194DirectBadGreatest PA194LeastWitnessOpen PA194GreatestBadEliminate PA194OrdinalStepFromProperty PA194TraceDirectShift PA194DomainGreatestClosedTemplate PA194InternalInductionBaseShift PA194MemberDomainClosedModel PA194GreatestSuccessorClosedModel PA194GreatestWitnessOpen PA194LeastDummyIndex PA194FixedInstanceShift PA194BadTraceStepShift PA194GreatestBadContradiction PA194GreatestBadStep PA194ContextContradictionCode PA194TraceDirectMember PA194GreatestSuccessorClosedTemplate PA194MemberDomainClosedTemplate PA194InductionStepShiftCode PA194GreatestMemberProjection PA194GreatestSuccessorAtCode PA194DomainInstances PA194MemberDomainAtCode PA194OrdinalStepApplicationCode PA194OrdinalStepQuote PA194InternalOrdinalStep PA194LeastBadDirectGoodTransitive PA194TraceDirectSyntax PA194LeastBadDirectMemberGood PA194LeastBadMemberGoodCode PA194DomainTransitiveInstances PA194DomainTransitiveAtCode PA194DomainTransitiveClosedModel PA194DomainTransitiveClosedTemplate PA194LeastExcludesClosedModel PA194FullSepWitnessBranch PA194FixedSyntaxQuote PA194TraceMemberBackwardCode PA194LeastExcludesInstances PA194LeastExcludesAtCode PA194LeastExcludesClosedTemplate PA194TraceMemberForwardCode PA194OrdinalBadNotZeroCode PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalBaseQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance boundSepZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance boundSepOne : One M := ⟨F oneCode Fin.elim0⟩
local instance boundSepAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance boundSepMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance boundSepLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance boundSepIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open M6.PA.RelationalSource M6.PA.RelationalSource.Ordinal

/-- In the full source, arbitrary internal base and step imply the conclusion. -/
noncomputable def ordinalConclusionFromBaseStep (Γ : Sequent M SourceL) (p : M)
    (hp : IsSemiformula SourceL 1 p)
    (hb : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL) Γ)
    (hstep : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ) :
    (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert (⟨inductionConclusionCode (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M) p,
      inductionConclusionCode_scoped _ _ (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL) Γ := by
  let T : InternalTheory M SourceL := fullSourceInternal
  let P : Semiformula M SourceL 1 := ⟨p, by simpa using hp⟩
  let D : Semiformula M SourceL 1 := ⌜PA194OrdinalBaseQuote.domainTemplate⌝
  let body : Semiformula M SourceL 1 := ∼D ⋎ P
  let dom : Formula M SourceL := D.subst ![Semiterm.fvar 0]
  let prop : Formula M SourceL := P.shift.subst ![Semiterm.fvar 0]
  let target : Sequent M SourceL := insert prop (insert (∼dom) Γ.shift)
  let hd : T ⊢!ᵈᵉʳ insert dom target := TDerivation.em dom (by simp [target]) (by simp [target])
  let hn : T ⊢!ᵈᵉʳ insert (∼prop) target := TDerivation.em prop (by simp [target]) (by simp [target])
  let hb0 := contextualBaseShiftProof T Γ p hp hb
  let hs0 := contextualStepShiftProof T Γ p hp hstep
  let hb' : T ⊢!ᵈᵉʳ insert (⟨baseCode (shift SourceL p), inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp.shift⟩ : Formula M SourceL) target := TDerivation.wk hb0 (by intro y hy; simp [target] at hy ⊢; tauto)
  let hs' : T ⊢!ᵈᵉʳ insert (⟨stepCode (shift SourceL p), stepCode_scoped _ hp.shift⟩ : Formula M SourceL) target :=
    TDerivation.wk hs0 (by intro y hy; simp [target] at hy ⊢; tauto)
  let absurd := badOrdinalEliminateFromTheory target (shift SourceL p) 0 prop hp.shift hd hn hb' hs'
  have he : insert prop target = insert (∼dom) (insert prop Γ.shift) := by
    apply Sequent.ext
    intro y
    simp [target]
    tauto
  let dbody := TDerivation.cast he absurd
  let target' := insert (∼dom ⋎ prop) Γ.shift
  let dbody' : T ⊢!ᵈᵉʳ insert (∼dom) (insert prop target') := TDerivation.wk dbody (by intro y hy; simp [target'] at hy ⊢; tauto)
  let disj : T ⊢!ᵈᵉʳ target' := TDerivation.or' (by simp [target']) dbody'
  have hf : D.shift = D := by apply Semiformula.ext; exact typed_quote_shift_fixed PA194OrdinalBaseQuote.domainTemplate (by decide)
  have hopen : body.free = ∼dom ⋎ prop := by
    simp [body,dom,prop,Bootstrapping.Semiformula.free,Semiformula.shift_substs,hf]
  let di := TDerivation.cast (congrArg (fun f => insert f Γ.shift) hopen.symm) disj
  let all := contextAllProof T Γ body di
  have hc : (∀⁰ body) = (⟨inductionConclusionCode (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M) p,
      inductionConclusionCode_scoped _ _ (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL) := by
    apply Semiformula.ext
    rfl
  exact TDerivation.cast (congrArg (fun f => insert f Γ) hc) all

/-- Every internally coded property has an ordinal induction proof in the full source. -/
theorem ordinalInductionInternalProvable (p : M) (hp : IsSemiformula SourceL 1 p) :
    letI := adjunctiveFullSepTheoryDelta
    Provable adjunctiveFullSepTheory (ordinalInductionCode p) := by
  let T : InternalTheory M SourceL := fullSourceInternal
  let base : Formula M SourceL := ⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
    (Semiformula.quote_isSemiformul₁ _) hp⟩
  let step : Formula M SourceL := ⟨stepCode p, stepCode_scoped p hp⟩
  let conclusion : Formula M SourceL := ⟨inductionConclusionCode (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M) p,
    inductionConclusionCode_scoped _ _ (Semiformula.quote_isSemiformul₁ _) hp⟩
  let Γ : Sequent M SourceL := insert (∼step) (insert (∼base) ∅)
  let hb : T ⊢!ᵈᵉʳ insert base Γ := TDerivation.em base (by simp [Γ]) (by simp [Γ])
  let hs : T ⊢!ᵈᵉʳ insert step Γ := TDerivation.em step (by simp [Γ]) (by simp [Γ])
  let hc := ordinalConclusionFromBaseStep Γ p hp hb hs
  have hseq : Derivable T.theory
      (insert (neg SourceL (ordinalStepFromProperty (⌜domainOne⌝ : M) (⌜domainZero⌝ : M)
          (⌜successorTemplate⌝ : M) p))
        (insert (inductionConclusionCode (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M) p)
          (insert (neg SourceL (inductionBaseCode (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M)
            (⌜zeroTemplate⌝ : M) p)) (∅ : M)))) := by
    have h := hc.toDerivable
    have he : (insert conclusion Γ).val =
      (insert (neg SourceL (ordinalStepFromProperty (⌜domainOne⌝ : M) (⌜domainZero⌝ : M)
          (⌜successorTemplate⌝ : M) p))
        (insert (inductionConclusionCode (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M) p)
          (insert (neg SourceL (inductionBaseCode (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M)
            (⌜zeroTemplate⌝ : M) p)) (∅ : M)))) := by
      apply mem_ext
      intro y
      simp [Γ,conclusion,base,step,baseCode,stepCode]
      tauto
    rw [← he]
    exact h
  exact ordinal_code_of_induction_sequent T p hp hseq

#print axioms ordinalConclusionFromBaseStep
#print axioms ordinalInductionInternalProvable
end models
end PA194InternalOrdinalFromBad
