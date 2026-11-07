import DiophantineConsistency.Mixed121.W121.TemporalSourceUnified
import DiophantineConsistency.Mixed121.W121.TemporalCleanNumerics
/-! Width-121 port of `Compact44/FractionalBooleanWindows` by `research/mixed121-calibration/tools/width_port.py`: the accepted proof
body with the width literals 67/66/65 replaced by 121/120/119. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace W121.FractionalBooleanWindows
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem even_if_previous_boolean (X n E t : V) (hn : 0<n) (ht : t<n)
    (hX : X<Exp.exp (121*n)) (hr0 : 0<E%121)
    (hb : dig 121 X (cyc n (cyc n t ((E/121)%n)) 1)≤1) :
    dig 121 (rot 1 (121*n) X (E%(121*n))) t%2=0 := by
  let r : V := E%121
  let j : V := cyc n t ((E/121)%n)
  have hr : r<121 := mod_lt _ (by norm_num)
  have hrpos : 0<r := hr0
  have hdiv : dig 121 X (cyc n j 1)/Exp.exp (121-r)=0 :=
    W121.TemporalCleanNumerics.boolean_high_zero r _ hr hb
  have hm : (2:V) ∣ Exp.exp 121 := by
    rw [show (121:V)=120+1 by norm_num,exp_succ]
    exact dvd_mul_right _ _
  have her : Exp.exp r=2*Exp.exp (r-1) := by
    calc
      _ = Exp.exp ((r-1)+1) := congrArg Exp.exp (tsub_add_cancel_of_le (pos_iff_one_le.mp hrpos)).symm
      _ = _ := exp_succ _
  have heven (x : V) : ((x*Exp.exp r)%Exp.exp 121)%2=0 := by
    rw [ArithmeticModularCancellation.mod_mod_of_dvd (by norm_num : (0:V)<2) hm]
    rw [her, show x*(2*Exp.exp (r-1))=2*(x*Exp.exp (r-1)) by ring,mod_mul_self_right]
  have h := W121.TemporalSourceUnified.digit X n E t hn ht hX
  dsimp only at h
  change dig 121 (rot 1 (121*n) X (E%(121*n))) t =
      (dig 121 X j*Exp.exp r)%Exp.exp 121 + dig 121 X (cyc n j 1)/Exp.exp (121-r) at h
  rw [h,hdiv,add_zero]
  exact heven _

theorem half_if_both_boolean (X n E t : V) (hn : 0<n) (ht : t<n)
    (hX : X<Exp.exp (121*n))
    (hx : dig 121 X (cyc n t ((E/121)%n))≤1)
    (hy : dig 121 X (cyc n (cyc n t ((E/121)%n)) 1)≤1) :
    dig 121 (rot 1 (121*n) X (E%(121*n))) t≤Exp.exp 120 := by
  let r : V := E%121
  let j : V := cyc n t ((E/121)%n)
  have hr : r<121 := mod_lt _ (by norm_num)
  have hdiv : dig 121 X (cyc n j 1)/Exp.exp (121-r)=0 :=
    W121.TemporalCleanNumerics.boolean_high_zero r _ hr hy
  have h := W121.TemporalSourceUnified.digit X n E t hn ht hX
  dsimp only at h
  change dig 121 (rot 1 (121*n) X (E%(121*n))) t =
      (dig 121 X j*Exp.exp r)%Exp.exp 121 + dig 121 X (cyc n j 1)/Exp.exp (121-r) at h
  rw [h,hdiv,add_zero]
  exact W121.TemporalCleanNumerics.boolean_low_bound r _ hr hx
#print axioms W121.FractionalBooleanWindows.even_if_previous_boolean
#print axioms W121.FractionalBooleanWindows.half_if_both_boolean
end W121.FractionalBooleanWindows
