import DiophantineConsistency.Sign33CurrentWindows
import DiophantineConsistency.Sign33FiveWitnesses
import DiophantineConsistency.ArithmeticCarrierSoundness2011

/-! Five conditional representatives derived from a maintained current zero. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33CurrentFiveWitnesses
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem five_witnesses_of_current_zero (v : Fin 14 → V)
    (hz : ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression v) :
    let w : Fin 14 → V := fun j => v j+1
    let q := (CurrentMasks2011.beta : V)*w 0+1
    let Y := w 7*q^3
    let E := (w 8*q)*Y
    let k := w 10+w 11
    let r := ((q-1)*(q-w 1)+w 2)*(q^2-1)+
      ((CurrentMasks2011.lowPort : V)+q*((CurrentMasks2011.highPort+CurrentMasks2011.beta : ℕ):V))*w 0
    let c := k*Y+w 10
    let x := w 4*w 4*c*w 6
    let z := w 4*w 4*r+c
    ∃ gap tau inner val negative : V,
      ι gap = (ι q-1)*(ι q-ι (w 1))+ι (w 2) ∧
      ι tau = ι E*ι (w 9)+ι k-ι r ∧
      ι inner = ι c*ι (w 6)-ι r ∧
      ι val = ι (w 4)*ι (w 4)*(ι c*ι (w 6)-ι r)-ι c ∧
      ι negative = ι (w 12)*ι (w 12)-(ι x-ι z)*(ι x-ι z) := by
  dsimp only
  let w : Fin 14 → V := fun j => v j+1
  let q := (CurrentMasks2011.beta : V)*w 0+1
  let Y := w 7*q^3
  let E := (w 8*q)*Y
  let k := w 10+w 11
  let r := ((q-1)*(q-w 1)+w 2)*(q^2-1)+
    ((CurrentMasks2011.lowPort : V)+q*((CurrentMasks2011.highPort+CurrentMasks2011.beta : ℕ):V))*w 0
  let c := k*Y+w 10
  let a := E+Y
  let S := delta a*w 5*c*c
  let x := w 4*w 4*c*w 6
  let z := w 4*w 4*r+c
  have hw : ∀ j, 0<w j := fun j => lt_of_lt_of_le _root_.zero_lt_one le_add_self
  have hq : 1≤q := by dsimp [q]; exact le_add_self
  have hN : 1≤w 9 := pos_iff_one_le.mp (hw 9)
  have hc : 0<c := by dsimp [c]; exact lt_of_lt_of_le (hw 10) le_add_self
  have hd : 0<delta a := by unfold delta; exact mul_pos (by simp) (by simp)
  have hS : 0<S := by dsimp [S]; exact mul_pos (mul_pos (mul_pos hd (hw 5)) hc) hc
  have hwin := Sign33CurrentWindows.windows_of_current_zero v hz
  change 0<q-w 1-w 2 ∧ r+2<E ∧ 2*r<c at hwin
  obtain ⟨hgap, hr, hhalf⟩ := hwin
  obtain ⟨_, _, _, hstrict, haux⟩ := ArithmeticCarrierSoundness2011.current_natural_equations v hz
  exact Sign33FiveWitnesses.five_witnesses_of_windows_and_norms
    q (w 1) (w 2) E (w 9) k r a c (w 6) (w 4) (w 5) S x z (w 12)
    hq hN hgap hr hc (hw 6) (hw 4) (hw 5) hhalf hstrict hS (hw 12) haux
end DiophantineConsistency.Sign33CurrentFiveWitnesses
#print axioms DiophantineConsistency.Sign33CurrentFiveWitnesses.five_witnesses_of_current_zero
