import PA194CompressedSourceFrame
import PA194ActiveFirstHit
import PA194Site10Hit
import PA194ControllerHaltReach

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194CompressedSourceOrbit
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion TableDispatch PA194FiniteControls
open PA194SourceControllerCode PA194CompressedSourceFrame PA194Stepper PA194StepperCompose
open PA194ActivePrefix PA194ActiveFirstHit PA194Site10Hit PA194ClockInvariantDefinable
open PA194IteratedSimulation PA194SourceSite31Physical PA194Path27Header PA194ZeroRuns

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- The positive physical segment for a nonterminal controller instruction.
The gap and spare count before and after the segment are allowed to be
nonstandard model elements. -/
def Advance (spare : M) : Prop :=
  ∀ s : M, F pc ![s] < modelNumeral M 3673 → F pc ![s] ≠ modelNumeral M 10 →
    ∀ gap count : M, ∃ nextGap nextCount : M,
      F pc ![F step ![s]] < modelNumeral M 3673 ∧
      PA194CompressedTape.Reach1 (F sourceRootCode ![s,gap,count,spare])
        (F sourceRootCode ![F step ![s],nextGap,nextCount,spare])

def activeFlag (seed time : M) : M := F (active run (atSite10 pc)) ![time,seed]
def state (seed time : M) : M := F run ![time,seed]
def sourcePC (seed time : M) : M := F pc ![state seed time]

def Aligned (seed start spare n : M) : Prop :=
  sourcePC seed n < modelNumeral M 3673 ∧ ∃ t gap count : M, n ≤ t ∧
      F stepper ![t,start] = F sourceRootCode ![state seed n,gap,count,spare]

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem rootDef :
    𝚺₁-Function₄ (fun s g c spare : M => F sourceRootCode ![s,g,c,spare]) := by
  have h : 𝚺₁.DefinableFunction (fun e : Fin 4 → M => F sourceRootCode e) :=
    HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) sourceRootCode)
  convert h using 1
  funext e
  apply congrArg (fun args : Fin 4 → M => F sourceRootCode args)
  funext i
  fin_cases i <;> rfl

private theorem alignmentFormulaDef (a p s l : M → M) (r : M → M → M → M → M)
    (spare bound : M) (ha : 𝚺₁-Function₁ a) (hp : 𝚺₁-Function₁ p) (hs : 𝚺₁-Function₁ s)
    (hl : 𝚺₁-Function₁ l) (hr : 𝚺₁-Function₄ r) :
    𝚺₁-Predicate (fun n : M => a n ≠ 1 ∨ p n < bound ∧
      ∃ t g c, n ≤ t ∧ l t = r (s n) g c spare) := by
  haveI := ha
  haveI := hp
  haveI := hs
  haveI := hl
  haveI := hr
  definability

theorem alignmentDef (seed start spare : M) :
    𝚺₁-Predicate (fun n : M => activeFlag seed n ≠ 1 ∨ Aligned seed start spare n) := by
  have ha : 𝚺₁-Function₁ (activeFlag seed) :=
    bindBinary _ seed (binaryCodeDef (active run (atSite10 pc)))
  have hs : 𝚺₁-Function₁ (state seed) := bindBinary _ seed (binaryCodeDef run)
  have hp : 𝚺₁-Function₁ (sourcePC seed) :=
    composeUnary (fun q : M => F pc ![q]) (state seed) (unaryCodeDef pc) hs
  have hl : 𝚺₁-Function₁ (fun t : M => F stepper ![t,start]) :=
    bindBinary _ start (binaryCodeDef stepper)
  exact alignmentFormulaDef (activeFlag seed) (sourcePC seed) (state seed)
    (fun t => F stepper ![t,start]) (fun s g c spare => F sourceRootCode ![s,g,c,spare])
    spare (modelNumeral M 3673) ha hp hs hl rootDef

/-- Follow the controller for an arbitrary model-length active prefix.
The induction carries a physical clock, header gap and spare count as
existential witnesses. -/
theorem synchronize
    (seed start spare : M) (hbase : Aligned seed start spare 0)
    (advance : Advance spare) :
    ∀ n : M, activeFlag seed n = 1 → Aligned seed start spare n := by
  have h : ∀ n : M, activeFlag seed n ≠ 1 ∨ Aligned seed start spare n := by
    intro n
    induction n using ISigma1.sigma1_succ_induction with
    | hP => exact alignmentDef seed start spare
    | zero => exact Or.inr hbase
    | succ n ih =>
      classical
      by_cases ha : activeFlag seed (n+1) = 1
      · right
        obtain ⟨ha0,hhit⟩ := activeContinues run (atSite10 pc) n seed ha
        obtain ⟨hpc,t,gap,count,hbound,ht⟩ := ih.resolve_left (not_not_intro ha0)
        have hnormal : sourcePC seed n ≠ modelNumeral M 10 := by
          intro he
          apply (atSite10Model pc _).mpr he
          let x := state seed n
          have hv : (![x] : Fin 1 → M) = fun _ => x := by
            funext k
            exact Fin.cases rfl (fun j => Fin.elim0 j) k
          change F (atSite10 pc) ![x] = (0 : M)
          rw [hv]
          exact hhit
        obtain ⟨nextGap,nextCount,hpc',c,hc,hstep⟩ := advance (state seed n) hpc hnormal gap count
        have hs : state seed (n+1) = F step ![state seed n] := iterateSucc step n seed
        refine ⟨?_,t+c,nextGap,nextCount,?_,?_⟩
        · change F pc ![state seed (n+1)] < modelNumeral M 3673
          rw [hs]
          exact hpc'
        · apply add_le_add hbound
          rcases zero_or_succ c with (rfl | ⟨j,rfl⟩)
          · exact (_root_.lt_irrefl _ hc).elim
          · simpa only [zero_add] using (add_le_add (zero_le : (0 : M) ≤ j) (le_rfl : (1 : M) ≤ 1))
        · change F stepper ![F addCode ![t,c],start] = _
          rw [modelStepperCompose,ht,hstep,hs]
      · exact Or.inl ha
  exact fun n hn => (h n).resolve_left (not_not_intro hn)

theorem site10Halts (s gap count spare : M) (hpc : F pc ![s] = modelNumeral M 10) :
    ¬ pi₁ (F stepper ![modelNumeral M 3,F sourceRootCode ![s,gap,count,spare]]) <
      modelNumeral M 194 := by
  rw [sourceRootCodeCorrect s gap count spare ⟨10,by decide⟩ hpc]
  unfold physicalFrame
  rw [PA194HaltPathSegment.haltPathSegment,modelPairCode,pi₁_pair]
  exact _root_.lt_irrefl _

/-- The physical and source halt events coincide under the startup and
nonterminal instruction contracts. The proof ranges over all clocks of a
PRA model and uses the first source halt instruction. -/
theorem equivalent (seed start spare : M) (hbase : Aligned seed start spare 0)
    (advance : Advance spare) :
    (∃ t : M, ¬ pi₁ (F stepper ![t,start]) < modelNumeral M 194) ↔
      ∃ n : M, sourcePC seed n = modelNumeral M 3674 := by
  have hseed : F pc ![seed] < modelNumeral M 3673 := by
    have hz : state seed (0 : M) = seed := iterateZero step seed
    have hp := hbase.1
    change F pc ![state seed (0 : M)] < modelNumeral M 3673 at hp
    rw [hz] at hp
    exact hp
  apply Iff.trans _ (PA194ControllerHaltReach.reachesHaltIffSite10 seed hseed).symm
  constructor
  · rintro ⟨time,htime⟩
    have hprefix : activeFlag seed (time+1) ≠ 1 := by
      intro ha
      obtain ⟨hpc,t,gap,count,hbound,hclock⟩ := synchronize seed start spare hbase advance _ ha
      obtain ⟨site,hsite⟩ := modelBelowNumeral 3673 (sourcePC seed (time+1)) hpc
      rw [sourceRootCodeCorrect _ gap count spare site hsite] at hclock
      have hle : time ≤ time+1 := le_add_of_nonneg_right (zero_le : (0 : M) ≤ 1)
      exact htime (PA194CompressedRootContracts.noInteriorHalt start site.val _ _ time t
        (le_trans hle hbound) hclock)
    obtain ⟨i,_,_,hi⟩ := boundedHit run (atSite10 pc) seed time hprefix
    exact ⟨i,(atSite10Model pc _).mp hi⟩
  · rintro ⟨i,hi⟩
    obtain ⟨j,_,ha,hj⟩ := hitHasActivePredecessor run (atSite10 pc) seed i
      ((atSite10Model pc _).mpr hi)
    obtain ⟨_,t,gap,count,_,hclock⟩ := synchronize seed start spare hbase advance _ ha
    refine ⟨F addCode ![t,modelNumeral M 3],?_⟩
    rw [modelStepperCompose,hclock]
    exact site10Halts _ gap count spare ((atSite10Model pc _).mp hj)

#print axioms rootDef
#print axioms alignmentDef
#print axioms synchronize
#print axioms equivalent
end models
end PA194CompressedSourceOrbit
