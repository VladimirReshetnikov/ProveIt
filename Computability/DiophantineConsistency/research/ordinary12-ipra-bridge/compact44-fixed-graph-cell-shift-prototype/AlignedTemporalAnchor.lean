import DiophantineConsistency.AlignedAnchorPhase
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace AlignedTemporalAnchor
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry CompactBitRotation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem digit (C n E t : V) (hn : 0<n) (ht : t<n) (hC : C<Exp.exp (67*n))
    (haligned : E%67=0) :
    dig 67 (temporalWord n E C) t = dig 67 C (cyc n t ((E/67)%n)) := by
  have h := TemporalSourceUnified.digit C n E t hn ht hC
  dsimp only at h
  rw [haligned] at h
  have hd := dig_lt 67 C (cyc n t ((E/67)%n))
  have hp := dig_lt 67 C (cyc n (cyc n t ((E/67)%n)) 1)
  simp only [exp_zero,mul_one,tsub_zero,mod_eq_self_of_lt hd,
    div_eq_zero_of_lt _ hp,add_zero] at h
  exact h

theorem digit_le_three (C n E t : V) (hn : 0<n) (ht : t<n) (hC : C<Exp.exp (67*n))
    (hcap : ∀ j<n, dig 67 C j≤3) (haligned : E%67=0) :
    dig 67 (temporalWord n E C) t≤3 := by
  rw [digit C n E t hn ht hC haligned]
  exact hcap _ (cyc_lt hn _ _)

variable {ι : Type*} [Fintype ι]
theorem anchor_nonzero (n C E F : V) (a e : ι→V)
    (hn : 0<n) (hC : C<Exp.exp (67*n)) (hcap : ∀ j<n, dig 67 C j≤3)
    (h : CarryInput 67 n F 1 (GenericBandCarryFamily.cap (ι:=ι))
      (GenericBandCarryFamily.coefficient a) (GenericBandCarryFamily.word n C e (temporalWord n E C)))
    (t : V) (ht : t<n) (hroom : (∑ j, a j*3)+1<Exp.exp 66) (haligned : E%67=0)
    (hpar : (1 + dig 67 (temporalWord n E C) t +
      carry 67 n (GenericBandCarryFamily.coefficient a) (GenericBandCarryFamily.word n C e (temporalWord n E C)) (cyc n t 1))%2=0) :
    dig 67 C (cyc n t ((E/67)%n))≠0 := by
  have hthree : (3:V)≤Exp.exp 66 := by
    have h4 : Exp.exp (2:V)=4 := by
      rw [show (2:V)=1+1 by norm_num,exp_succ,exp_one]
      norm_num
    have h := exp_monotone_le.mpr (show (2:V)≤66 by norm_num)
    rw [h4] at h
    exact le_trans (by norm_num) h
  have hpred := digit_le_three C n E (cyc n t 1) hn (cyc_lt hn _ _) hC hcap haligned
  have hc0 := (TemporalCarryReset.clean n C (temporalWord n E C) F a e h t ht hroom (le_trans hpred hthree)).1
  have hsource := digit C n E t hn ht hC haligned
  intro hz
  rw [hc0,hsource,hz] at hpar
  norm_num at hpar
#print axioms AlignedTemporalAnchor.digit
#print axioms AlignedTemporalAnchor.digit_le_three
#print axioms AlignedTemporalAnchor.anchor_nonzero
end AlignedTemporalAnchor
