import DirectBFSHaltPacking
import DirectBFSCellPulseEquality
import DirectBFSGenericChosenRank
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace DirectBFSHaltChosenRank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPow ArithmeticPacking ArithmeticPackingBlocks
open DirectBFSConstructedWord DirectBFSFourFieldsPacking DirectBFSHaltCanonicalPacking
open CompactCanonicalPerturbation CompactRankVariation
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] DirectBFSFourFieldsPacking.kernel DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho CompactSymbolicPorts.highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def baseCell (T : V) : V → V := cellWord (row T) (fun _ => 0)

theorem halt_pulse_stable (T : V) (δ : V → V) [𝚺₁-Function₁ δ]
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0)
    (hb : ∀ j, δ j≤1) (hzero : δ 0=0) :
    (𝚺₁-Function₁ (row T)) ∧
    PackingInput (590069:V) (kernel:V) (CompactConcreteIncrement.mask:V) (CompactSymbolicPorts.highNat:V)
      (length T) (stride T) (perturb (baseCell T) δ) := by
  have h := DirectBFSHaltPacking.halt_pack T δ hT (by rw [hzero]; simp)
  have heq : perturb (baseCell T) δ = cellWord (row T) δ := by
    funext j
    exact (DirectBFSCellPulseEquality.cell_pulse (row T) δ j (hb j)).symm
  exact ⟨h.1, by rw [heq]; exact h.2.2.2.2.2⟩

theorem halt_chosen_rank (T c : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0)
    (hK : (kernel:V)%342946332593=264033855341) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j≤1) ∧
      (∀ j, δ j≠0 → 0<j ∧ j+1<length T ∧ j+stride T<length T) ∧
      PackingInput (590069:V) (kernel:V) (CompactConcreteIncrement.mask:V) (CompactSymbolicPorts.highNat:V)
        (length T) (stride T) (cellWord (row T) δ) ∧
      windowRank (kernel:V) (length T) (stride T) c (cellWord (row T) δ) % (590069*length T) =
        (590069*stride T) % (590069*length T) := by
  letI : 𝚺₁-Function₁ (fun _ : V => (0:V)) := by definability
  have hp := DirectBFSHaltPacking.halt_pack T (fun _ => 0) hT (by simp)
  letI : 𝚺₁-Function₁ (row T) := hp.1
  letI : 𝚺₁-Function₁ (baseCell T) := cellWord_definable (row T) (fun _ => 0)
  have he : length T = power 581197 ((2*T+3)+1) := (CompactHaltDimensions.dimensions T).2.2.2
  have hs : stride T = power 581197 (T+1) := rfl
  have hbase : PackingInput 590069 (kernel:V) CompactConcreteIncrement.mask (CompactSymbolicPorts.highNat:V)
      (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) (baseCell T) := by
    simpa only [←he,←hs,baseCell] using hp.2.2.2.2.2
  have hstable : ∀ δ : V → V, (𝚺₁-Function₁ δ) → (∀ j, δ j≤1) →
      (∀ j, δ j≠0 → 0<j ∧ j+1<power 581197 ((2*T+3)+1) ∧
        j+power 581197 (T+1)<power 581197 ((2*T+3)+1)) →
      PackingInput 590069 (kernel:V) CompactConcreteIncrement.mask (CompactSymbolicPorts.highNat:V)
        (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) (perturb (baseCell T) δ) := by
    intro δ hd hb hsafety
    letI : 𝚺₁-Function₁ δ := hd
    have hz : δ 0=0 := by
      by_contra hn
      exact (_root_.lt_irrefl (0:V)) (hsafety 0 hn).1
    have h := halt_pulse_stable T δ hT hb hz
    simpa only [←he,←hs] using h.2
  obtain ⟨δ,hd,hb,hsafety,hpack,hcal⟩ := DirectBFSGenericChosenRank.chosen_rank_if_stable
    (kernel:V) hK T CompactConcreteIncrement.mask (CompactSymbolicPorts.highNat:V) c hbase hstable
  have heq : perturb (baseCell T) δ = cellWord (row T) δ := by
    funext j
    exact (DirectBFSCellPulseEquality.cell_pulse (row T) δ j (hb j)).symm
  rw [heq] at hpack hcal
  exact ⟨δ,hd,hb,by simpa only [he,hs] using hsafety,
    by simpa only [he,hs] using hpack, by simpa only [he,hs] using hcal⟩
#print axioms DirectBFSHaltChosenRank.halt_pulse_stable
#print axioms DirectBFSHaltChosenRank.halt_chosen_rank
end DirectBFSHaltChosenRank
