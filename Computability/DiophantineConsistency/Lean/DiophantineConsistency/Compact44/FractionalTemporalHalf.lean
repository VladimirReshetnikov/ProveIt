import DiophantineConsistency.Compact44.FractionalTemporalEven
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FractionalTemporalHalf
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem digit_le_half (X n E t : V) (hn : 0<n) (ht : t<n)
    (hX : X<Exp.exp (67*n)) (hcap : ∀ j<n, dig 67 X j≤3)
    (hr64 : E%67≤64) :
    dig 67 (rot 1 (67*n) X (E%(67*n))) t ≤ Exp.exp 66 := by
  let r : V := E%67
  let j : V := cyc n t ((E/67)%n)
  have hr' : r≤64 := hr64
  have hj : j<n := cyc_lt hn _ _
  have hjp : cyc n j 1<n := cyc_lt hn _ _
  have h2r : (2:V)+r≤67 := by
    have h := add_le_add (show (2:V)≤2 from le_rfl) hr'
    exact le_trans h (by norm_num)
  have hdiff : (2:V)≤67-r := (le_tsub_iff_right (le_trans hr' (by norm_num))).2 h2r
  have hE : (4:V)≤Exp.exp (67-r) := by
    have h := exp_monotone_le.mpr hdiff
    have h4 : Exp.exp (2:V)=4 := by
      rw [show (2:V)=1+1 by norm_num,exp_succ,exp_one]
      norm_num
    simpa only [h4] using h
  have hdiv : dig 67 X (cyc n j 1)/Exp.exp (67-r)=0 :=
    div_eq_zero_of_lt _ (lt_of_le_of_lt (hcap _ hjp) (lt_of_lt_of_le (by norm_num) hE))
  have hpow : Exp.exp r≤Exp.exp 64 := exp_monotone_le.mpr hr'
  have hmul : dig 67 X j*Exp.exp r ≤ 3*Exp.exp 64 :=
    mul_le_mul (hcap _ hj) hpow (by simp) (by simp)
  have h66 : Exp.exp (66:V)=4*Exp.exp 64 := by
    rw [show (66:V)=64+1+1 by norm_num,exp_succ,exp_succ]
    ring
  have hupper : (3:V)*Exp.exp 64≤Exp.exp 66 := by
    rw [h66]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by simp)
  have h := TemporalSourceUnified.digit X n E t hn ht hX
  dsimp only at h
  change dig 67 (rot 1 (67*n) X (E%(67*n))) t =
      (dig 67 X j*Exp.exp r)%Exp.exp 67 + dig 67 X (cyc n j 1)/Exp.exp (67-r) at h
  rw [h,hdiv,add_zero]
  exact le_trans (mod_le _ _) (le_trans hmul hupper)
#print axioms FractionalTemporalHalf.digit_le_half
end FractionalTemporalHalf
