import PA194GatedModelLength
import PA194ActiveFirstHit
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194GatedActiveHit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PA194Stepper PA194StepperCompose PA194ActivePrefix PA194ActiveFirstHit PA194GatedModelLength
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


/-- Bounded source hit from physical halt; the PR active-prefix first-hit
    supplier is discharged. Physical contracts remain explicit. -/
theorem haltToCodeHit
    (run : Code 2) (hit : Code 1) (seed : M)
    (frame elapsed : M → M) (good halt : M → Prop) (start : M)
    (hsync : ∀ n, F (active run hit) ![n,seed] = 1 →
      good (F run ![n,seed]) ∧
      F stepper ![elapsed n,start] = frame (F run ![n,seed]) ∧ n ≤ elapsed n)
    (hpersist : ∀ t u, t ≤ u → halt (F stepper ![t,start]) → halt (F stepper ![u,start]))
    (hframe : ∀ s, good s → ¬ halt (frame s))
    (t : M) (hh : halt (F stepper ![t,start])) :
    ∃ i, i ≤ t ∧ F hit ![F run ![i,seed]] ≠ 0 := by
  apply haltToSourceHit (fun n => F run ![n,seed]) frame elapsed
    (fun n => F (active run hit) ![n,seed] = 1) good
    (fun s => F hit ![s] ≠ 0) halt start hsync hpersist hframe _ t hh
  intro n hn
  obtain ⟨i,hi,_,hhit⟩ := boundedHit run hit seed n hn
  exact ⟨i,hi,hhit⟩

/-- Physical halt from source hit; the PR active-prefix first-hit supplier
    is discharged. Synchronization and halt-segment contracts remain explicit. -/
theorem codeHitToHalt
    (run : Code 2) (hit : Code 1) (seed : M)
    (frame elapsed haltCost : M → M) (good halt : M → Prop) (start : M)
    (hsync : ∀ n, F (active run hit) ![n,seed] = 1 →
      good (F run ![n,seed]) ∧
      F stepper ![elapsed n,start] = frame (F run ![n,seed]) ∧ n ≤ elapsed n)
    (hhaltSegment : ∀ s, good s → F hit ![s] ≠ 0 →
      halt (F stepper ![haltCost s,frame s]))
    (n : M) (hh : F hit ![F run ![n,seed]] ≠ 0) :
    ∃ i, i ≤ n ∧ halt (F stepper ![F addCode ![elapsed i,haltCost (F run ![i,seed])],start]) := by
  apply sourceHitToHalt (fun n => F run ![n,seed]) frame elapsed haltCost
    (fun n => F (active run hit) ![n,seed] = 1) good
    (fun s => F hit ![s] ≠ 0) halt start hsync _ hhaltSegment n hh
  exact hitHasActivePredecessor run hit seed
#print axioms haltToCodeHit
#print axioms codeHitToHalt
end models
end PA194GatedActiveHit
