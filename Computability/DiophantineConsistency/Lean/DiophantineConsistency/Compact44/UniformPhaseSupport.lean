import DiophantineConsistency.Compact44.ForeignBandsZero
import DiophantineConsistency.Compact44.HighMaskLocal
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace UniformPhaseSupport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticWindowBits ArithmeticCyclicWord ArithmeticBinaryCarry ArithmeticRepunit
open ArithmeticMaskConstants CompactHighPopulation CompactSymbolicPorts CleanGeometry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_zero (N C target offset : V) (hN : 0<N)
    (hzero : ∀ j<8807*N, ¬Bad (j%8807) → dig 67 C j=0)
    (hphase : ¬Bad (cyc 8807 (target%8807) offset)) :
    dig 67 C (cyc (8807*N) target offset)=0 := by
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  apply hzero _ (cyc_lt hn _ _)
  rwa [CyclicAnyPhase.cyc_period 8807 N target offset (by norm_num) hN]

theorem local_nocarry (N F target : V) (hN : 0<N) (ht : target<8807*N)
    (ht0 : 0<target) (hphase : target%8807=4393 ∨ target%8807=5495)
    (hhigh : NoCarry F ((highNat:V)*rep (67*8807) N-1)) :
    NoCarry (dig 67 F target) (Exp.exp 51-2) := by
  have hd0 : 1≤dig 67 (highNat:V) 0 := by rw [HighMaskLocal.origin]; norm_num
  have hh := high_mask_digits 67 8807 N F (highNat:V) (by norm_num) hN CompactHighPopulation.model_lt hd0 hhigh
  have h := hh.2 target ht ht0
  rcases hphase with hp | hp
  · rw [hp,HighMaskLocal.target4393] at h
    exact h
  · rw [hp,HighMaskLocal.target5495] at h
    exact h
#print axioms UniformPhaseSupport.source_zero
#print axioms UniformPhaseSupport.local_nocarry
end UniformPhaseSupport
