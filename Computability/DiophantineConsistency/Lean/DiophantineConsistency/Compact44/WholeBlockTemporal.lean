import DiophantineConsistency.Compact44.WholeBlockPhase
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace WholeBlockTemporal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactBitRotation
open CleanGeometry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_source (N C E k : V) (hN : 0<N) (hk : k<8807*N)
    (hC : C<Exp.exp (67*(8807*N))) (haligned : E%67=0)
    (hcell : ((E/67)%(8807*N))%8807=0)
    (hzero : ∀ j<8807*N, ¬Bad (j%8807) → dig 67 C j=0)
    (hsafe : ¬Bad (k%8807)) :
    dig 67 (temporalWord (8807*N) E C) k=0 := by
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  rw [AlignedTemporalAnchor.digit C (8807*N) E k hn hk hC haligned]
  apply hzero _ (cyc_lt hn _ _)
  rw [WholeBlockPhase.shift_phase N k ((E/67)%(8807*N)) hN hcell]
  exact hsafe

theorem target_and_predecessor (N C E k : V) (hN : 0<N) (hk : k<8807*N)
    (hC : C<Exp.exp (67*(8807*N))) (haligned : E%67=0)
    (hcell : ((E/67)%(8807*N))%8807=0)
    (hzero : ∀ j<8807*N, ¬Bad (j%8807) → dig 67 C j=0)
    (hp : k%8807=2195 ∨ k%8807=3296 ∨ k%8807=4393 ∨ k%8807=5495) :
    dig 67 (temporalWord (8807*N) E C) (cyc (8807*N) k 1)=0 ∧
    ((k%8807=4393 ∨ k%8807=5495) → dig 67 (temporalWord (8807*N) E C) k=0) := by
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  constructor
  · apply zero_source N C E (cyc (8807*N) k 1) hN (cyc_lt hn _ _) hC haligned hcell hzero
    rw [CyclicAnyPhase.cyc_period 8807 N k 1 (by norm_num) hN]
    exact WholeBlockPhase.predecessor_safe _ hp
  · intro hdec
    exact zero_source N C E k hN hk hC haligned hcell hzero (WholeBlockPhase.decoder_safe _ hdec)
#print axioms WholeBlockTemporal.zero_source
#print axioms WholeBlockTemporal.target_and_predecessor
end WholeBlockTemporal
