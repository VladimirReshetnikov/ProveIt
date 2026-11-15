import PA194ControllerHaltRun
import PA194SourceReachable
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ControllerHaltReach
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PA194FiniteControls PA194StateOne
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters PA194SourceRegisterRelation
open PA194SourceInstructionCalibration PA194SourceBoundedStep PA194SourceTargetBounds PA194SourcePCBound
open PA194SourceNoMalformed PA194SourceHaltUnique PA194ControllerHaltCharacterization PA194SourceSentinel PA194IteratedSimulation
open PA194ControllerHaltRun PA194SourceReachable PA194ClockInvariantDefinable
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem boundedPCases (s : M) (h : F pc ![s] < modelNumeral M 3675) :
    F pc ![s] < modelNumeral M 3673 ∨ F pc ![s] = modelNumeral M 3673 ∨
      F pc ![s] = modelNumeral M 3674 := by
  obtain ⟨i,hi⟩ := modelBelowNumeral 3675 (F pc ![s]) h
  have cases : i.val < 3673 ∨ i.val=3673 ∨ i.val=3674 := by have := i.isLt; omega
  rcases cases with hw | hm | hh
  · left; rw [hi]; exact modelNumeralStrict _ _ hw
  · right; left; simpa [hm] using hi
  · right; right; simpa [hh] using hi

theorem nextHaltBack (s : M) (hbound : F pc ![s] < modelNumeral M 3675)
    (hnext : F pc ![F step ![s]] = modelNumeral M 3674) :
    F pc ![s] = modelNumeral M 10 ∨ F pc ![s] = modelNumeral M 3674 := by
  rcases boundedPCases s hbound with hw | hm | hh
  · exact Or.inl ((nextHaltIffSite10 s hw).mp hnext)
  · rw [stepMalformed s hm,hm] at hnext
    exact False.elim ((ne_of_lt (modelNumeralStrict 3673 3674 (by decide))) hnext)
  · exact Or.inr hh

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem noHaltOrEarlierDef (f : M → M) (hf : 𝚺₁-Function₁ f) :
    𝚺₁-Predicate (fun n : M => f n ≠ modelNumeral M 3674 ∨
      ∃ i : M, i < n ∧ f i = modelNumeral M 10) := by
  haveI := hf
  definability

theorem haltAfterSite10 (seed n : M) (hseed : F pc ![seed] < modelNumeral M 3673) :
    F pc ![F run ![n,seed]] = modelNumeral M 3674 →
      ∃ i : M, i < n ∧ F pc ![F run ![i,seed]] = modelNumeral M 10 := by
  let f : M → M := fun i => F pc ![F run ![i,seed]]
  have hr : 𝚺₁-Function₁ (fun i : M => F run ![i,seed]) :=
    bindBinary _ seed (binaryCodeDef (M := M) run)
  have hf : 𝚺₁-Function₁ f := composeUnary _ _ (unaryCodeDef (M := M) pc) hr
  have hp := noHaltOrEarlierDef f hf
  have hb : F pc ![seed] < modelNumeral M 3675 :=
    lt_trans hseed (modelNumeralStrict 3673 3675 (by decide))
  have hbound := runPCBound seed hb
  have hmain : ∀ n : M, f n ≠ modelNumeral M 3674 ∨
      ∃ i : M, i < n ∧ f i = modelNumeral M 10 := by
    intro n
    induction n using ISigma1.sigma1_succ_induction with
    | hP => exact hp
    | zero =>
      left
      dsimp only [f]
      rw [run,iterateZero]
      exact ne_of_lt (lt_trans hseed (modelNumeralStrict 3673 3674 (by decide)))
    | succ n ih =>
      classical
      have hn : n < n+1 := lt_add_of_pos_right n (Arithmetic.zero_lt_one : (0 : M) < 1)
      rcases ih with hnot | ⟨i,hi,hsite⟩
      · by_cases hnext : f (n+1) = modelNumeral M 3674
        · right
          have hnext' : F pc ![F step ![F run ![n,seed]]] = modelNumeral M 3674 := by
            simpa only [f,run,iterateSucc] using hnext
          rcases nextHaltBack (F run ![n,seed]) (hbound n) hnext' with hsite | hhalt
          · exact ⟨n,hn,hsite⟩
          · exact False.elim (hnot hhalt)
        · exact Or.inl hnext
      · exact Or.inr ⟨i,lt_trans hi hn,hsite⟩
  intro hn
  exact (hmain n).resolve_left (not_not_intro hn)

theorem reachesHaltIffSite10 (seed : M) (hseed : F pc ![seed] < modelNumeral M 3673) :
    (∃ n : M, F pc ![F run ![n,seed]] = modelNumeral M 3674) ↔
      (∃ n : M, F pc ![F run ![n,seed]] = modelNumeral M 10) := by
  constructor
  · rintro ⟨n,hn⟩
    obtain ⟨i,_,hi⟩ := haltAfterSite10 seed n hseed hn
    exact ⟨i,hi⟩
  · rintro ⟨n,hn⟩
    refine ⟨n+1,?_⟩
    rw [run,iterateSucc]
    change F pc ![F step ![F run ![n,seed]]] = modelNumeral M 3674
    rw [site10Step _ hn,pcModel,pi₁_pair]
#print axioms boundedPCases
#print axioms nextHaltBack
#print axioms haltAfterSite10
#print axioms reachesHaltIffSite10
end models
end PA194ControllerHaltReach
