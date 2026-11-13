import DiophantineConsistency.Compact44.ParityAnchorPhase
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FractionalBooleanWindows
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem even_if_previous_boolean (X n E t : V) (hn : 0<n) (ht : t<n)
    (hX : X<Exp.exp (67*n)) (hr0 : 0<E%67)
    (hb : dig 67 X (cyc n (cyc n t ((E/67)%n)) 1)≤1) :
    dig 67 (rot 1 (67*n) X (E%(67*n))) t%2=0 := by
  let r : V := E%67
  let j : V := cyc n t ((E/67)%n)
  have hr : r<67 := mod_lt _ (by norm_num)
  have hrpos : 0<r := hr0
  have hdiv : dig 67 X (cyc n j 1)/Exp.exp (67-r)=0 :=
    TemporalCleanNumerics.boolean_high_zero r _ hr hb
  have hm : (2:V) ∣ Exp.exp 67 := by
    rw [show (67:V)=66+1 by norm_num,exp_succ]
    exact dvd_mul_right _ _
  have her : Exp.exp r=2*Exp.exp (r-1) := by
    calc
      _ = Exp.exp ((r-1)+1) := congrArg Exp.exp (tsub_add_cancel_of_le (pos_iff_one_le.mp hrpos)).symm
      _ = _ := exp_succ _
  have heven (x : V) : ((x*Exp.exp r)%Exp.exp 67)%2=0 := by
    rw [ArithmeticModularCancellation.mod_mod_of_dvd (by norm_num : (0:V)<2) hm]
    rw [her, show x*(2*Exp.exp (r-1))=2*(x*Exp.exp (r-1)) by ring,mod_mul_self_right]
  have h := TemporalSourceUnified.digit X n E t hn ht hX
  dsimp only at h
  change dig 67 (rot 1 (67*n) X (E%(67*n))) t =
      (dig 67 X j*Exp.exp r)%Exp.exp 67 + dig 67 X (cyc n j 1)/Exp.exp (67-r) at h
  rw [h,hdiv,add_zero]
  exact heven _

theorem half_if_both_boolean (X n E t : V) (hn : 0<n) (ht : t<n)
    (hX : X<Exp.exp (67*n))
    (hx : dig 67 X (cyc n t ((E/67)%n))≤1)
    (hy : dig 67 X (cyc n (cyc n t ((E/67)%n)) 1)≤1) :
    dig 67 (rot 1 (67*n) X (E%(67*n))) t≤Exp.exp 66 := by
  let r : V := E%67
  let j : V := cyc n t ((E/67)%n)
  have hr : r<67 := mod_lt _ (by norm_num)
  have hdiv : dig 67 X (cyc n j 1)/Exp.exp (67-r)=0 :=
    TemporalCleanNumerics.boolean_high_zero r _ hr hy
  have h := TemporalSourceUnified.digit X n E t hn ht hX
  dsimp only at h
  change dig 67 (rot 1 (67*n) X (E%(67*n))) t =
      (dig 67 X j*Exp.exp r)%Exp.exp 67 + dig 67 X (cyc n j 1)/Exp.exp (67-r) at h
  rw [h,hdiv,add_zero]
  exact TemporalCleanNumerics.boolean_low_bound r _ hr hx
#print axioms FractionalBooleanWindows.even_if_previous_boolean
#print axioms FractionalBooleanWindows.half_if_both_boolean
end FractionalBooleanWindows
