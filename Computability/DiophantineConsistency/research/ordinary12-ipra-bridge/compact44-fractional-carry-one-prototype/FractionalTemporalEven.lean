import DiophantineConsistency.FixedGraphAnchorNonzero
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FractionalTemporalEven
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem even_digit (X n E t : V) (hn : 0<n) (ht : t<n)
    (hX : X<Exp.exp (67*n)) (hcap : ∀ j<n, dig 67 X j≤3)
    (hr0 : 0<E%67) (hr65 : E%67≤65) :
    dig 67 (rot 1 (67*n) X (E%(67*n))) t % 2=0 := by
  let r : V := E%67
  let j : V := cyc n t ((E/67)%n)
  have hr' : r≤65 := hr65
  have hrpos : 0<r := hr0
  have hj : j<n := cyc_lt hn _ _
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
#print axioms FractionalTemporalEven.even_digit
end FractionalTemporalEven
