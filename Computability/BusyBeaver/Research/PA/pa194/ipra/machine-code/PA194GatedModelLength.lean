import PA194ConditionalModelLength
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194GatedModelLength
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PA194Stepper PA194StepperCompose
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

/-- Conditional synchronization only before the first ready-to-halt source
    instruction. `active` is a prefix property, not physical nonhalting. -/
theorem simulateBeforeHalt
    (state next frame elapsed cost : M → M) (active : M → Prop)
    (good normal : M → Prop) (start : M)
    (hdef : 𝚺₁-Predicate (fun n : M => active n → good (state n) ∧
      F stepper ![elapsed n,start] = frame (state n) ∧ n ≤ elapsed n))
    (hbase : active 0 → good (state 0) ∧
      F stepper ![elapsed 0,start] = frame (state 0) ∧ (0 : M) ≤ elapsed 0)
    (hactive : ∀ n, active (n+1) → active n ∧ normal (state n))
    (hnext : ∀ n, state (n+1) = next (state n))
    (hclock : ∀ n, elapsed (n+1) = F addCode ![elapsed n,cost (state n)])
    (hpres : ∀ s, good s → normal s → good (next s))
    (hsegment : ∀ s, good s → normal s → F stepper ![cost s,frame s] = frame (next s))
    (hpositive : ∀ s, good s → normal s → (1 : M) ≤ cost s) :
    ∀ n, active n → good (state n) ∧
      F stepper ![elapsed n,start] = frame (state n) ∧ n ≤ elapsed n := by
  intro n
  induction n using ISigma1.sigma1_succ_induction with
  | hP => exact hdef
  | zero => exact hbase
  | succ n ih =>
    intro ha
    obtain ⟨ha0,hnormal⟩ := hactive n ha
    obtain ⟨hg,hphysical,hbound⟩ := ih ha0
    constructor
    · rw [hnext]
      exact hpres (state n) hg hnormal
    · constructor
      · rw [hnext,hclock,modelStepperCompose,hphysical,hsegment (state n) hg hnormal]
      · rw [hclock]
        change n+1 ≤ elapsed n + cost (state n)
        exact add_le_add hbound (hpositive (state n) hg hnormal)

/-- A literal halt yields an earlier source hit, conditional on a bounded
    first-hit supplier and persistence/nonhalting-frame properties. -/
theorem haltToSourceHit
    (state frame elapsed : M → M) (active : M → Prop) (good hit halt : M → Prop) (start : M)
    (hsync : ∀ n, active n → good (state n) ∧
      F stepper ![elapsed n,start] = frame (state n) ∧ n ≤ elapsed n)
    (hpersist : ∀ t u, t ≤ u → halt (F stepper ![t,start]) → halt (F stepper ![u,start]))
    (hframe : ∀ s, good s → ¬ halt (frame s))
    (hfirst : ∀ t, ¬ active (t+1) → ∃ i, i ≤ t ∧ hit (state i))
    (t : M) (hh : halt (F stepper ![t,start])) :
    ∃ i, i ≤ t ∧ hit (state i) := by
  apply hfirst t
  intro ha
  obtain ⟨hg,hframeEq,hbound⟩ := hsync (t+1) ha
  have ht : t ≤ t+1 := by exact le_add_of_nonneg_right (zero_le : (0 : M) ≤ 1)
  have hlater := hpersist t (elapsed (t+1)) (le_trans ht hbound) hh
  apply hframe (state (t+1)) hg
  rw [←hframeEq]
  exact hlater

/-- A source hit yields a literal halt, conditional on an active first-hit
    witness and the source halt-instruction's physical segment contract. -/
theorem sourceHitToHalt
    (state frame elapsed haltCost : M → M) (active : M → Prop) (good hit halt : M → Prop) (start : M)
    (hsync : ∀ n, active n → good (state n) ∧
      F stepper ![elapsed n,start] = frame (state n) ∧ n ≤ elapsed n)
    (hfirst : ∀ n, hit (state n) → ∃ i, i ≤ n ∧ active i ∧ hit (state i))
    (hhaltSegment : ∀ s, good s → hit s → halt (F stepper ![haltCost s,frame s]))
    (n : M) (hh : hit (state n)) :
    ∃ i, i ≤ n ∧ halt (F stepper ![F addCode ![elapsed i,haltCost (state i)],start]) := by
  obtain ⟨i,hibound,hiactive,hihit⟩ := hfirst n hh
  obtain ⟨hgood,hframeEq,_⟩ := hsync i hiactive
  refine ⟨i,hibound,?_⟩
  rw [modelStepperCompose,hframeEq]
  exact hhaltSegment (state i) hgood hihit
#print axioms simulateBeforeHalt
#print axioms haltToSourceHit
#print axioms sourceHitToHalt
end models
end PA194GatedModelLength
