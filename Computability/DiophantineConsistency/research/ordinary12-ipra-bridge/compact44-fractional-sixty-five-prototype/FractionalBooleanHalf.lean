import DiophantineConsistency.FractionalTemporalHalf
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FractionalBooleanHalf
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem digit_le_half (X n E t : V) (hn : 0<n) (ht : t<n)
    (hX : X<Exp.exp (67*n)) (hcap : ∀ j<n, dig 67 X j≤3)
    (hr65 : E%67≤65) (hb : dig 67 X (cyc n t ((E/67)%n))≤1) :
    dig 67 (rot 1 (67*n) X (E%(67*n))) t ≤ Exp.exp 66 := by
  let r : V := E%67
  let j : V := cyc n t ((E/67)%n)
  have hr' : r≤65 := hr65
  have hjp : cyc n j 1<n := cyc_lt hn _ _
  have h2r : (2:V)+r≤67 := by
    have h := add_le_add (show (2:V)≤2 from le_rfl) hr'
    simpa only [show (2:V)+65=67 by norm_num] using h
  have hdiff : (2:V)≤67-r := (le_tsub_iff_right (le_trans hr' (by norm_num))).2 h2r
  have hE : (4:V)≤Exp.exp (67-r) := by
    have h := exp_monotone_le.mpr hdiff
    have h4 : Exp.exp (2:V)=4 := by
      rw [show (2:V)=1+1 by norm_num,exp_succ,exp_one]
      norm_num
    simpa only [h4] using h
  have hdiv : dig 67 X (cyc n j 1)/Exp.exp (67-r)=0 :=
    div_eq_zero_of_lt _ (lt_of_le_of_lt (hcap _ hjp) (lt_of_lt_of_le (by norm_num) hE))
  have hr : r<67 := lt_of_le_of_lt hr' (by norm_num)
  have h := TemporalSourceUnified.digit X n E t hn ht hX
  dsimp only at h
  change dig 67 (rot 1 (67*n) X (E%(67*n))) t =
      (dig 67 X j*Exp.exp r)%Exp.exp 67 + dig 67 X (cyc n j 1)/Exp.exp (67-r) at h
  rw [h,hdiv,add_zero]
  exact TemporalCleanNumerics.boolean_low_bound r (dig 67 X j) hr hb
#print axioms FractionalBooleanHalf.digit_le_half
end FractionalBooleanHalf
