import DiophantineConsistency.BlockSelectedMarker
import DiophantineConsistency.DecodedSelectorShift
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace BlockOrbit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem forward_back (N h s : V) (hN : 0<N) (hh : h<N) :
    cyc N ((h+s)%N) s = h := by
  have he := DecodedSelectorShift.cyclic_shift N h s s hN le_rfl
  rw [tsub_self] at he
  have hz : cyc N h 0=h := by
    unfold cyc
    rw [zero_mod,tsub_zero,mod_add_remove_right hN,mod_eq_self_of_lt hh]
  exact he.trans hz
#print axioms BlockOrbit.forward_back
end BlockOrbit
