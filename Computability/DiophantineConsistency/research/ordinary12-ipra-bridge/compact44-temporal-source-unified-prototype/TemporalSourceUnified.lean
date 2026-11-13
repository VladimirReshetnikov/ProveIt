import DiophantineConsistency.TemporalSourceStraddle
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TemporalSourceUnified
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem digit (X n E t : V) (hn : 0<n) (ht : t<n) (hX : X<Exp.exp (67*n)) :
    let q := (E/67)%n
    let r := E%67
    let j := cyc n t q
    dig 67 (rot 1 (67*n) X (E%(67*n))) t =
      (dig 67 X j*Exp.exp r)%Exp.exp 67 + dig 67 X (cyc n j 1)/Exp.exp (67-r) := by
  let q := (E/67)%n
  let r := E%67
  change dig 67 (rot 1 (67*n) X (E%(67*n))) t =
    (dig 67 X (cyc n t q)*Exp.exp r)%Exp.exp 67 +
      dig 67 X (cyc n (cyc n t q) 1)/Exp.exp (67-r)
  have hs := TemporalShiftSplit.reduced n E hn
  dsimp only at hs
  have he : E%(67*n)=67*q+r := hs.1
  have hq : q<n := hs.2.1
  have hr : r<67 := hs.2.2
  by_cases hrz : r=0
  · have he0 : E%(67*n)=67*q := by simpa only [hrz,add_zero] using he
    have h := TemporalOtherWindows.aligned X n E t q ht hq he0 hX
    have hd := dig_lt 67 X (cyc n t q)
    have hp := dig_lt 67 X (cyc n (cyc n t q) 1)
    simp only [hrz,exp_zero,mul_one,tsub_zero,mod_eq_self_of_lt hd,
      div_eq_zero_of_lt _ hp,add_zero]
    exact h
  · have hrpos : 0<r := pos_iff_ne_zero.mpr hrz
    rcases lt_trichotomy q t with hqt | hqt | htq
    · exact TemporalSourceNonwrap.nonwrap X n E t q r ht hq hqt hrpos hr he hX
    · have heq : E%(67*n)=67*t+r := by rw [←hqt]; exact he
      have h := TemporalSourceStraddle.straddle X n E t r ht hrpos hr heq hX
      simpa only [hqt] using h
    · exact TemporalSourceWrapped.wrapped X n E t q r ht hq htq hrpos hr he
#print axioms TemporalSourceUnified.digit
end TemporalSourceUnified
