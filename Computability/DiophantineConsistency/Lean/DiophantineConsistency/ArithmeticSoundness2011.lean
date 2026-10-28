import DiophantineConsistency.ArithmeticWindowZero
import DiophantineConsistency.ArithmeticWangSoundness

/-! Soundness side of the polynomial bridge, in every model of IΣ1: a positive
zero of the literal current polynomial makes the represented decimal215 run
halt. The cell-decoding step (window interface ⇒ cyclic marked Wang word) is the
explicit premise `CellBridge`; everything else is proved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticSoundness2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticWindowInterface ArithmeticCurrentSentence2011 ArithmeticWindowZero

/-- The hypotheses of `ArithmeticWangSoundness.marked_halts_of_cyclic` at cell count `N`:
a Σ1-definable cyclic tile word `a` on `[0,N)` with stride `s`. -/
def MarkedCyclic {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (N : V) : Prop :=
  ∃ a : V → V, (𝚺₁-Function₁ a) ∧ ∃ s : V,
    (∀ j < N, a j < 942) ∧ a 0 = 0 ∧
    (∀ j < N, ArithmeticWangTable.eastC (a j) =
      ArithmeticWangTable.westC (a ((j + N - 1) % N))) ∧
    (∀ j < N, ArithmeticWangTable.southC (a j) =
      ArithmeticWangTable.northC (a ((j + N * (s + 1) - s) % N)))

/-- **The cell-decoding premise**: every internal window yields a cyclic marked word. -/
def CellBridge : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (N W C F : V),
    Window N W C F → MarkedCyclic N

/-- **Zero ⇒ halt.** -/
theorem zero_halts (hc : CellBridge) {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (u : Fin 14 → V) (h : PositiveZero u) :
    ∃ t : V, first (ArithmeticMachineRun215.run t) = 0 := by
  obtain ⟨N, W, C, F, hw⟩ := window_of_zero u h
  obtain ⟨a, ha, s, hlt, h0, hE, hS⟩ := hc V N W C F hw
  haveI := ha
  obtain ⟨t, -, ht⟩ :=
    ArithmeticWangSoundness.marked_halts_of_cyclic (a := a) (s := s) hw.N_pos hlt h0 hE hS
  exact ⟨t, ht⟩

/-- **The soundness half of `PolynomialBridge`.** -/
theorem sentence_of_no_halt (hc : CellBridge) {V : Type} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (hn : ¬∃ time : V, first (ArithmeticMachineRun215.run time) = 0) :
    FoundationHACurrentNoZero2011.classicalSentence.Evalb (M := V) ![] := by
  rw [classicalSentence_iff]
  rintro ⟨u, hu⟩
  exact hn (zero_halts hc u hu)

end DiophantineConsistency.ArithmeticSoundness2011
