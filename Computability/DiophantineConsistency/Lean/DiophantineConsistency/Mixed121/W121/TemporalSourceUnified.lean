import DiophantineConsistency.Mixed121.W121.TemporalSourceStraddle
/-! Width-121 port of `Compact44/TemporalSourceUnified` by `research/mixed121-calibration/tools/width_port.py`: the accepted proof
body with the width literals 67/66/65 replaced by 121/120/119. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace W121.TemporalSourceUnified
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem digit (X n E t : V) (hn : 0<n) (ht : t<n) (hX : X<Exp.exp (121*n)) :
    let q := (E/121)%n
    let r := E%121
    let j := cyc n t q
    dig 121 (rot 1 (121*n) X (E%(121*n))) t =
      (dig 121 X j*Exp.exp r)%Exp.exp 121 + dig 121 X (cyc n j 1)/Exp.exp (121-r) := by
  let q := (E/121)%n
  let r := E%121
  change dig 121 (rot 1 (121*n) X (E%(121*n))) t =
    (dig 121 X (cyc n t q)*Exp.exp r)%Exp.exp 121 +
      dig 121 X (cyc n (cyc n t q) 1)/Exp.exp (121-r)
  have hs := W121.TemporalShiftSplit.reduced n E hn
  dsimp only at hs
  have he : E%(121*n)=121*q+r := hs.1
  have hq : q<n := hs.2.1
  have hr : r<121 := hs.2.2
  by_cases hrz : r=0
  · have he0 : E%(121*n)=121*q := by simpa only [hrz,add_zero] using he
    have h := W121.TemporalOtherWindows.aligned X n E t q ht hq he0 hX
    have hd := dig_lt 121 X (cyc n t q)
    have hp := dig_lt 121 X (cyc n (cyc n t q) 1)
    simp only [hrz,exp_zero,mul_one,tsub_zero,mod_eq_self_of_lt hd,
      div_eq_zero_of_lt _ hp,add_zero]
    exact h
  · have hrpos : 0<r := pos_iff_ne_zero.mpr hrz
    rcases lt_trichotomy q t with hqt | hqt | htq
    · exact W121.TemporalSourceNonwrap.nonwrap X n E t q r ht hq hqt hrpos hr he hX
    · have heq : E%(121*n)=121*t+r := by rw [←hqt]; exact he
      have h := W121.TemporalSourceStraddle.straddle X n E t r ht hrpos hr heq hX
      simpa only [hqt] using h
    · exact W121.TemporalSourceWrapped.wrapped X n E t q r ht hq htq hrpos hr he
#print axioms W121.TemporalSourceUnified.digit
end W121.TemporalSourceUnified
