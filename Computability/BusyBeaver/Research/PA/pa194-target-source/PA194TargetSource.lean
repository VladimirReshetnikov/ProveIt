import PA194SchedulerHalt
import PA194SourceLineRefutation
import PA194SourceHead1Preservation
import PA194SourceHead2Preservation
import PA194SourceDiagonalPreservation
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000
namespace PA194TargetSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetLeaves PA194TargetGate PA194TargetExtendedStep PA194TargetProofLeaf
 PA194SourceLineSoundness PA194SourceRho8Preservation PA194SourceHead6Preservation
 PA194SourceEqualityPreservation PA194SourceHead5Preservation PA194SourceHead1Preservation
 PA194SourceHead2Preservation PA194SourceOutputWF
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
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

local notation "good" => PA194SourceLineSoundness.good

theorem diagonal_seed (a : M) : good (diagonalValue a) := by
  simpa [PA194SourceLineSoundness.good,diagonalValue,impValue,allValue,impSource,allSource,
    PA194SourceLineSoundness.translated,PA194SourceRho8Preservation.translated] using
      (PA194SourceDiagonalPreservation.diagonal a)

theorem target_sound
    (hgate : ∀ a b c : M, c ≠ a → c ≠ b → good (oldBundleValue a b c))
    (result : M) (hp : TargetProvable result) : good result := by
  rcases hp with ⟨p,hp⟩
  apply targetProof_sound good (PA194SourceLineSoundness.good_definable (M := M)) ?_ ?_ ?_ ?_ p result hp
  · intro a b
    rw [machineHead1_model]
    simpa [PA194SourceLineSoundness.good,head1Value,exValue,negValue,allValue,impValue,
      PA194SourceHead1Preservation.exSource,impSource,allSource,
      PA194SourceLineSoundness.translated,PA194SourceRho8Preservation.translated] using
      (PA194SourceHead1Preservation.head1 a b)
  · intro a b hb
    exact PA194SourceUniversalPreservation.source_universal_preservation a b hb
  · intro a b ha hi
    exact PA194SourceMPPreservation.mp a b hi ha
  · refine ⟨?_,?_,?_,?_,?_,?_,hgate,diagonal_seed⟩
    · intro a b c
      simpa [PA194SourceLineSoundness.good,head2Value,impValue,allValue,impSource,allSource,
        PA194SourceLineSoundness.translated,PA194SourceRho8Preservation.translated] using
        (PA194SourceHead2Preservation.head2 a b c)
    · intro a b c
      simpa [PA194SourceLineSoundness.good,head3Value,impValue,memValue,eqValue,impSource,memSource,eqSource,
        PA194SourceLineSoundness.translated,PA194SourceRho8Preservation.translated] using
        (PA194SourceEqualityPreservation.head3 c a b)
    · intro a b c
      simpa [PA194SourceLineSoundness.good,head4Value,impValue,memValue,eqValue,impSource,memSource,eqSource,
        PA194SourceLineSoundness.translated,PA194SourceRho8Preservation.translated] using
        (PA194SourceEqualityPreservation.head4 c a b)
    · intro a b
      simpa [PA194SourceLineSoundness.good,head5Value,exValue,negValue,allValue,impValue,eqValue,impSource,allSource,eqSource,
        PA194SourceLineSoundness.translated,PA194SourceRho8Preservation.translated] using
        (PA194SourceHead5Preservation.head5 a b)
    · intro a b c
      simpa [PA194SourceLineSoundness.good,head6Value,impValue,allValue,impSource,allSource,
        PA194SourceLineSoundness.translated,PA194SourceRho8Preservation.translated] using
        (PA194SourceHead6Preservation.head6 a b c)
    · intro a b c u hu
      simpa [PA194SourceLineSoundness.good,rho8Value,impValue,impSource,
        PA194SourceLineSoundness.translated,PA194SourceRho8Preservation.translated] using
        (PA194SourceRho8Preservation.rho8 a b c u)
theorem target_refutes_PA
    (hgate : ∀ a b c : M, c ≠ a → c ≠ b → good (oldBundleValue a b c))
    (hp : TargetProvable (1 : M)) : Provable (𝗣𝗔 : ArithmeticTheory) (^⊥ : M) := by
  have h := target_sound hgate (1 : M) hp
  unfold PA194SourceLineSoundness.good PA194SourceLineSoundness.translated at h
  rw [PA194ContradictionTranslation.positive_code_one] at h
  exact PA194ContradictionInternalRefutation.contradiction_provable_implies_falsum h

theorem scheduler_halt_refutes_PA
    (hgate : ∀ a b c : M, c ≠ a → c ≠ b → good (oldBundleValue a b c))
    {m : Nat} (n l t w h : Code m) (e : Fin m → M)
    (hs : PA194MachineStack.SoundStore (F t e) (F w e) (F h e))
    (hh : F (PA194SchedulerCode.halt n l t h) e = 1) :
    Provable (𝗣𝗔 : ArithmeticTheory) (^⊥ : M) :=
  target_refutes_PA hgate (PA194SchedulerHalt.halt_implies_provable n l t w h e hs hh)

#print axioms diagonal_seed
#print axioms target_sound
#print axioms target_refutes_PA
#print axioms scheduler_halt_refutes_PA
end models
end PA194TargetSource
