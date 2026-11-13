import DiophantineConsistency.ParityPreviousPhase
import DiophantineConsistency.TemporalEvenCarry
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FractionalAnchorConflict
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry CompactBitRotation
variable {V ι : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [Fintype ι]

theorem conflict (n C E F : V) (a e : ι→V) (hn : 0<n) (hC : C<Exp.exp (67*n))
    (h : CarryInput 67 n F 1 (GenericBandCarryFamily.cap (ι:=ι))
      (GenericBandCarryFamily.coefficient a) (GenericBandCarryFamily.word n C e (temporalWord n E C)))
    (t : V) (ht : t<n) (hroom : (∑ j, a j*3)+1<Exp.exp 66) (hr0 : 0<E%67)
    (hpar : (1 + dig 67 (temporalWord n E C) t +
      carry 67 n (GenericBandCarryFamily.coefficient a) (GenericBandCarryFamily.word n C e (temporalWord n E C)) (cyc n t 1))%2=0)
    (hb : dig 67 C (cyc n (cyc n t 1) ((E/67)%n))≤1)
    (hbprev : dig 67 C (cyc n (cyc n (cyc n t 1) ((E/67)%n)) 1)≤1) : False := by
  let T := temporalWord n E C
  let X := GenericBandCarryFamily.word n C e T
  let A := GenericBandCarryFamily.coefficient a
  have hprev : dig 67 C (cyc n (cyc n t ((E/67)%n)) 1)≤1 := by
    rw [TemporalSourcePredecessor.cyclic_commute n t ((E/67)%n) 1 hn]
    exact hb
  have he := FractionalBooleanWindows.even_if_previous_boolean C n E t hn ht hC hr0 hprev
  have hcb := carry_le h (cyc_lt hn t 1)
  have hc1 := TemporalEvenCarry.carry_one _ _ hcb he hpar
  have hhalf := FractionalBooleanWindows.half_if_both_boolean C n E (cyc n t 1)
    hn (cyc_lt hn t 1) hC hb hbprev
  have hc0 := (TemporalCarryReset.clean n C T F a e h t ht hroom hhalf).1
  rw [hc1] at hc0
  exact _root_.one_ne_zero hc0
#print axioms FractionalAnchorConflict.conflict
end FractionalAnchorConflict
