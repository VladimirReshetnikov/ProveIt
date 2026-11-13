import DiophantineConsistency.Sign33Windows
import DiophantineConsistency.ArithmeticCarrierSoundness2011

/-! Derive the three natural windows from a maintained natural source zero. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33CurrentWindows
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem windows_of_current_zero (v : Fin 14 → V)
    (hz : ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression v) :
    let w : Fin 14 → V := fun j => v j+1
    let q := (CurrentMasks2011.beta : V)*w 0+1
    let E := (w 8*q)*(w 7*q^3)
    let r := ((q-1)*(q-w 1)+w 2)*(q^2-1)+
      ((CurrentMasks2011.lowPort : V)+q*((CurrentMasks2011.highPort+CurrentMasks2011.beta : ℕ):V))*w 0
    let c := (w 10+w 11)*(w 7*q^3)+w 10
    0<q-w 1-w 2 ∧ r+2<E ∧ 2*r<c := by
  dsimp only
  set w : Fin 14 → V := fun j => v j+1
  have hw : ∀ j, 0 < w j := fun j => lt_of_lt_of_le _root_.zero_lt_one le_add_self
  obtain ⟨hbeta, hMC, hMF⟩ := ArithmeticCarrierSoundness2011.current_bounds (V := V)
  have hbeta0 : (0 : V) < (CurrentMasks2011.beta : V) := lt_of_lt_of_le (by norm_num) hbeta
  obtain ⟨ht, hfirst, hmain, hstrong, haux⟩ :=
    ArithmeticCarrierSoundness2011.current_natural_equations v hz
  exact Sign33Windows.windows_from_maintained_norms
    (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V) (CurrentMasks2011.lowPort:V)
    ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)
    (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) (w 9)
    (w 10) (w 11) (w 12) (w 13)
    hbeta0 hMC hMF (hw 0) (hw 1) (hw 2) (hw 3) (hw 4) (hw 5) (hw 6) (hw 7)
    (hw 8) (hw 9) (hw 10) (hw 11) (hw 12) (hw 13) ht hfirst hmain hstrong haux
end DiophantineConsistency.Sign33CurrentWindows
#print axioms DiophantineConsistency.Sign33CurrentWindows.windows_of_current_zero
