import PA194GatedModelLength
import PA194CompressedTape
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ExistentialModelLength
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

/-- Synchronization with an existential physical clock. Each verified instruction
can supply its own positive clock without a uniform expression for its cost. -/
def Aligned (state frame : M → M) (good : M → Prop) (start n : M) : Prop :=
  good (state n) ∧ ∃ t : M, n ≤ t ∧ F stepper ![t,start] = frame (state n)

theorem simulateBeforeHalt
    (state next frame : M → M) (active good normal : M → Prop) (start : M)
    (hdef : 𝚺₁-Predicate (fun n : M => active n → Aligned state frame good start n))
    (hbase : active 0 → Aligned state frame good start 0)
    (hactive : ∀ n, active (n+1) → active n ∧ normal (state n))
    (hnext : ∀ n, state (n+1) = next (state n))
    (hpres : ∀ s, good s → normal s → good (next s))
    (hsegment : ∀ s, good s → normal s →
      PA194CompressedTape.Reach1 (frame s) (frame (next s))) :
    ∀ n, active n → Aligned state frame good start n := by
  intro n
  induction n using ISigma1.sigma1_succ_induction with
  | hP => exact hdef
  | zero => exact hbase
  | succ n ih =>
    intro ha
    obtain ⟨ha0, hnormal⟩ := hactive n ha
    obtain ⟨hg, t, hbound, ht⟩ := ih ha0
    obtain ⟨c, hc, hstep⟩ := hsegment (state n) hg hnormal
    refine ⟨by rw [hnext]; exact hpres _ hg hnormal, t+c, ?_, ?_⟩
    · apply add_le_add hbound
      rcases zero_or_succ c with (rfl | ⟨j, rfl⟩)
      · exact (_root_.lt_irrefl _ hc).elim
      · simpa only [zero_add] using (add_le_add (zero_le : (0 : M) ≤ j) (le_rfl : (1 : M) ≤ 1))
    · change F stepper ![F addCode ![t,c],start] = frame (state (n+1))
      rw [modelStepperCompose, ht, hstep, hnext]

/-- A literal halt forces an earlier source hit if all active roots are safe. -/
theorem haltToSourceHit
    (state frame : M → M) (active good hit halt : M → Prop) (start : M)
    (hsync : ∀ n, active n → Aligned state frame good start n)
    (hpersist : ∀ t u, t ≤ u → halt (F stepper ![t,start]) → halt (F stepper ![u,start]))
    (hframe : ∀ s, good s → ¬ halt (frame s))
    (hfirst : ∀ t, ¬ active (t+1) → ∃ i, i ≤ t ∧ hit (state i))
    (t : M) (hh : halt (F stepper ![t,start])) :
    ∃ i, i ≤ t ∧ hit (state i) := by
  apply hfirst t
  intro ha
  obtain ⟨hg, u, hbound, heq⟩ := hsync (t+1) ha
  have ht : t ≤ t+1 := le_add_of_nonneg_right (zero_le : (0 : M) ≤ 1)
  exact hframe _ hg (heq ▸ hpersist t u (le_trans ht hbound) hh)

/-- A source hit executes a halting segment from the first active hit root. -/
theorem sourceHitToHalt
    (state frame : M → M) (active good hit halt : M → Prop) (start : M)
    (hsync : ∀ n, active n → Aligned state frame good start n)
    (hfirst : ∀ n, hit (state n) → ∃ i, i ≤ n ∧ active i ∧ hit (state i))
    (hhaltSegment : ∀ s, good s → hit s → ∃ c : M, halt (F stepper ![c,frame s]))
    (n : M) (hh : hit (state n)) :
    ∃ t : M, halt (F stepper ![t,start]) := by
  obtain ⟨i, _, hi, hhit⟩ := hfirst n hh
  obtain ⟨hg, t, _, heq⟩ := hsync i hi
  obtain ⟨c, hc⟩ := hhaltSegment _ hg hhit
  exact ⟨t+c, by
    change halt (F stepper ![F addCode ![t,c],start])
    rw [modelStepperCompose, heq]
    exact hc⟩

#print axioms simulateBeforeHalt
#print axioms haltToSourceHit
#print axioms sourceHitToHalt
end models
end PA194ExistentialModelLength
