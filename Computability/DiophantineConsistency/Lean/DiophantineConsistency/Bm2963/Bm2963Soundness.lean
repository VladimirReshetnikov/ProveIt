import DiophantineConsistency.Bm2963.Bm2963WindowZero
import DiophantineConsistency.Bm2963.Bm2963CellWindow

/-! # Soundness at the block-mask2963 ports

The counterpart of `ArithmeticSoundness2011`, in every model of IΣ1: a positive
zero of the literal Carrier65 expression at the block-mask2963 ports
(`Bm2963Ports.PositiveZero`) makes the represented decimal215 run halt. The chain
is `PositiveZero` ⇒ `Window` (`Bm2963WindowZero`) ⇒ marked cyclic Wang word
(`Bm2963CellWindow`, the cell decoding `Bm2963CellLocal` … `Bm2963Occupation`) ⇒
halt (`ArithmeticWangSoundness.marked_halts`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Bm2963Soundness
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC ArithmeticCantor
open Bm2963WindowInterface Bm2963WindowZero
attribute [local irreducible] Bm2963Kernel.K Bm2963MaskData.radix Bm2963MaskData.beta
  Bm2963MaskData.lowPort Bm2963MaskData.highPort

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **Zero ⇒ halt.** -/
theorem zero_halts (u : Fin 14 → V) (h : Bm2963Ports.PositiveZero u) :
    ∃ t : V, first (ArithmeticMachineRun215.run t) = 0 := by
  obtain ⟨N, W, C, F, hw⟩ := window_of_zero u h
  obtain ⟨t, -, ht⟩ := Bm2963CellWindow.window_halts hw
  exact ⟨t, ht⟩

/-- **Zero ⇒ halt, with an explicit witness bound.** The halting time is below
`q u = β·u₀ + 1`, so the witness map is a bounded search over an affine function
of one coordinate. -/
theorem zero_halts_below (u : Fin 14 → V) (h : Bm2963Ports.PositiveZero u) :
    ∃ t < Bm2963CarrierRadix.q u, first (ArithmeticMachineRun215.run t) = 0 := by
  obtain ⟨N, hq, hw⟩ := window_of_positive_zero u h
  obtain ⟨t, htN, ht⟩ := Bm2963CellWindow.window_halts hw
  refine ⟨t, ?_, ht⟩
  have hN : N ≤ 139261 * N := le_mul_of_one_le_left (by simp) (by simp)
  calc t < N := htN
    _ < Exp.exp N := lt_exp N
    _ ≤ Exp.exp (139261 * N) := exp_monotone_le.mpr hN
    _ = Bm2963CarrierRadix.q u := hq.symm

end Bm2963Soundness

#print axioms Bm2963Soundness.zero_halts
#print axioms Bm2963Soundness.zero_halts_below
