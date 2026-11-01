import DiophantineConsistency.ArithmeticHalfBinomial
/-! Additive support for the two half-binomial lemmas absent from a historical
provider. The original module is not replaced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticHalfBinomialCompat
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem rank_lower_of_radix (q F alpha J MC MF h : V)
    (hq16 : 16≤q) (halpha : 0<alpha) (hq : q=Exp.exp h) :
    3*h+1≤((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J := by
  let R := ((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J
  have hR : q^2-1≤R := by
    have h1 : 1≤(q-1)*(q-F)+alpha :=
      le_trans (pos_iff_one_le.mp halpha) (le_add_of_nonneg_left (by simp))
    exact le_trans (le_mul_of_one_le_left (by simp) h1) (le_add_of_nonneg_right (by simp))
  have hhq : h+1≤q := by rw [hq]; exact lt_iff_succ_le.mp (lt_exp h)
  have hsq : 3*h+1+1≤q^2 := calc
    3*h+1+1≤3*(h+1)+(16:V) := by
      have he : 3*h+1+1+(3+14:V)=3*(h+1)+16 := by ring
      rw [←he]; exact le_add_of_nonneg_right (by simp)
    _≤3*q+q := add_le_add (mul_le_mul_of_nonneg_left hhq (by simp)) hq16
    _=4*q := by ring
    _≤q*q := mul_le_mul_of_nonneg_right (le_trans (by norm_num : (4:V)≤16) hq16) (by simp)
    _=q^2 := by ring
  exact le_trans (le_tsub_of_add_le_right hsq) hR

/-- Recover a half-index at least four from a doubled index at least five. -/
theorem half_index_of_ge_five (n R : V) (hn5 : 5≤n) (hnR : 2*n=R+1) :
    ∃ r, r+1=n ∧ 4≤r ∧ R=2*r+1 := by
  have hn1 : 1≤n := le_trans (by simp) hn5
  let r : V := n-1
  have hrn : r+1=n := tsub_add_cancel_of_le hn1
  have hr4 : 4≤r := by
    apply (add_le_add_iff_right (1:V)).mp
    rw [hrn]
    simpa only [show (4:V)+1=5 by ring] using hn5
  have hR : R=2*r+1 := by
    apply add_right_cancel (b:=(1:V))
    rw [←hnR,←hrn]; ring
  exact ⟨r,hrn,hr4,hR⟩

end DiophantineConsistency.ArithmeticHalfBinomialCompat
