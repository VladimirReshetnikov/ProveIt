import DiophantineConsistency.Source34.Source34TileMatch
import DiophantineConsistency.Compact44.CompactLocalWord
import DiophantineConsistency.Compact44.OldWordIdentification
import DiophantineConsistency.ArithmeticWangSoundness

/-! # Halting from the leaf facts at the source34 ports

`Mixed121Halt` at the source34 tuple. It completes the source34 calibration.

* `graph_anchored_match`: block `0`'s row is the Start tile `0`;
* `graph_local_word`: the row word satisfies Compact44's local Wang-word
  predicate `CompactLocalWord.Word`, through
  `CompactFieldCastBridge.lookup_matches` applied to `Source34TileMatch`;
* `halts_of_facts`: Compact44's tile-set-generic tail
  (`OldWordIdentificationDraft.local_to_marked`,
  `ArithmeticWangSoundness.marked_halts`) turns the word into a halting run
  of machine 215. The source34 tuple uses the same 943 Wang tiles in the same
  order as 121x8801.

So any positive valuation satisfying `CompactLeafFacts.LeafFacts` at the
source34 ports gives internal halting of machine 215. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Source34Halt
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticRepunit ArithmeticPackingBlocks
open Mixed121BlockWord (row row_definable)
open Source34BlockWord
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho

theorem graph_anchored_match (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N W s : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ s<N ∧
      Blocks 10 (row C N 1) N W ∧ row C N 1 0=0 ∧
      (∀ h<N, row C N 1 h<943 ∧ row C N 1 h≠1) ∧
      ∀ h<N, ∃ i j l : Fin 943,
        row C N 1 h=(i.val:V) ∧ row C N 1 (cyc N h s)=(j.val:V) ∧
        row C N 1 (cyc N h 1)=(l.val:V) ∧
        (Compact943Data.row i).2.2.2=(Compact943Data.row j).2.1 ∧
        (Compact943Data.row i).2.2.1=(Compact943Data.row l).1 := by
  obtain ⟨N,W,s,hN,hq,hs,hW,hbound,hfields⟩ := Source34TileMatch.graph_tile_match v hv hz
  obtain ⟨N',W',hN',hq',hJ',hW',hrows,_⟩ := graph_all_block_word v hv hz
  obtain ⟨N'',w'',hN'',hq'',hJ'',hle'',hw'',hv5'',hcarry'',h0,hzero,hbool⟩ :=
    Source34Clean.graph_support_carry v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  have hNN' : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N' N''
  let C : V := 1+v 0*(Source34Ports.ports 0:V)-v 1-v 2
  let n : V := 8801*N
  have hnge : (8801:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8801)
    simpa only [n,mul_one] using h
  have ht : (4393:V)<n := lt_of_lt_of_le (by norm_num) hnge
  obtain ⟨i, hi0, hsel, _⟩ := hrows 0 hN
  simp only [mul_zero, zero_add] at hsel
  have hone : Mixed121Band.selDigit n C 4393 4393 Mixed121Occupied.origin=1 := by
    unfold Mixed121Band.selDigit
    have hs0 : cyc n (4393:V) (((4393 - Mixed121Occupied.origin.val : ℕ)) : V)=0 := by
      have hh := Mixed121Selected.source_cell n 4393 0 (by simpa using ht) (by norm_num)
      simpa [Mixed121Occupied.origin] using hh
    rw [hs0]
    exact h0
  have hio : i = Mixed121Occupied.origin := by
    by_contra hne
    have := hsel.2 Mixed121Occupied.origin (Ne.symm hne)
    rw [hone] at this
    exact _root_.one_ne_zero this
  have hrow0 : row C N 1 0 = 0 := by
    rw [hi0, hio]
    simp [Mixed121Occupied.origin]
  exact ⟨N,W,s,hN,hq,hs,hW,hrow0,hbound,hfields⟩

theorem graph_local_word (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N W s : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ s<N ∧
      Blocks 10 (row C N 1) N W ∧ CompactLocalWord.Word (row C N 1) N s := by
  obtain ⟨N,W,s,hN,hq,hs,hW,hzero,hbound,hfields⟩ := graph_anchored_match v hv hz
  have hm := CompactFieldCastBridge.lookup_matches CompactLocalWord.field
    (fun f hf m => CompactLocalWord.field_cast f hf m) (row _ N 1) N s hN hfields
  refine ⟨N,W,s,hN,hq,hs,hW,?_⟩
  exact ⟨hN,fun j hj => (hbound j hj).1,fun j hj => (hbound j hj).2,hzero,hm.1,hm.2⟩

/-- **Halting from the leaf facts at the source34 ports.** -/
theorem halts_of_facts (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  obtain ⟨N,W,s,hN,hq,hs,hW,hword⟩ := graph_local_word v hv hz
  let C : V := 1+v 0*(Source34Ports.ports 0:V)-v 1-v 2
  let b : V → V := row C N 1
  letI : 𝚺₁-Function₁ b := row_definable C N 1
  have hm := OldWordIdentificationDraft.local_to_marked hword
  letI : 𝚺₁-Function₁ (fun j => CompactInverseDraft.inverseLookup (b j)) := hm.1
  obtain ⟨t,_,hh⟩ := ArithmeticWangSoundness.marked_halts hm.2
  exact ⟨t,hh⟩
end Source34Halt
#print axioms Source34Halt.graph_anchored_match
#print axioms Source34Halt.graph_local_word
#print axioms Source34Halt.halts_of_facts
