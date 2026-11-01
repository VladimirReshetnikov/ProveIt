import DiophantineConsistency.ArithmeticWindowZero
import DiophantineConsistency.ArithmeticCellWindow

/-! Soundness side of the polynomial bridge, in every model of IΣ1: a positive
zero of the literal current polynomial makes the represented decimal215 run
halt. The chain is
`PositiveZero` ⇒ `Window` (`ArithmeticWindowZero`) ⇒ marked cyclic Wang word
(`ArithmeticCellWindow`, the cell decoding S9–S12) ⇒ halt
(`ArithmeticWangSoundness.marked_halts`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticSoundness2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticWindowInterface ArithmeticCurrentSentence2011 ArithmeticWindowZero

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **Zero ⇒ halt.** -/
theorem zero_halts (u : Fin 14 → V) (h : PositiveZero u) :
    ∃ t : V, first (ArithmeticMachineRun215.run t) = 0 := by
  obtain ⟨N, W, C, F, hw⟩ := window_of_zero u h
  obtain ⟨t, -, ht⟩ := ArithmeticCellWindow.window_halts hw
  exact ⟨t, ht⟩

/-- **Zero ⇒ halt, with an explicit witness bound.** The halting time is below
`q u = β·u₀ + 1`, so it is found by a bounded search over an affine function of
one coordinate: the witness map is elementary. -/
theorem zero_halts_below (u : Fin 14 → V) (h : PositiveZero u) :
    ∃ t < ArithmeticCarrierRadix2011.q u, first (ArithmeticMachineRun215.run t) = 0 := by
  obtain ⟨N, hq, hw⟩ := window_of_positive_zero u h
  obtain ⟨t, htN, ht⟩ := ArithmeticCellWindow.window_halts hw
  refine ⟨t, ?_, ht⟩
  have hN : N ≤ 94517 * N := le_mul_of_one_le_left (by simp) (by simp)
  calc t < N := htN
    _ < Exp.exp N := lt_exp N
    _ ≤ Exp.exp (94517 * N) := exp_monotone_le.mpr hN
    _ = ArithmeticCarrierRadix2011.q u := hq.symm

/-- **The soundness half of `PolynomialBridge`.** -/
theorem sentence_of_no_halt
    (hn : ¬∃ time : V, first (ArithmeticMachineRun215.run time) = 0) :
    FoundationHACurrentNoZero2011.classicalSentence.Evalb (M := V) ![] := by
  rw [classicalSentence_iff]
  rintro ⟨u, hu⟩
  exact hn (zero_halts u hu)

end DiophantineConsistency.ArithmeticSoundness2011
