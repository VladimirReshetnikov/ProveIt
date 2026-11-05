import DiophantineConsistency.ArithmeticPellPowerRecovery

/-! Unchecked draft: the scale interval makes the first Pell ordinate unique. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainFirstOrdinateUnique
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellPowerRecovery
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem double_lt_of_index_lt (B n m : V) (hnm : n<m) :
    2*ycoord n B<ycoord m B := by
  have hcoef : (2:V)≤2*B+3 := by simp
  have hle := mul_le_mul_of_nonneg_right hcoef (Arithmetic.zero_le (ycoord n B))
  exact lt_of_lt_of_le (lt_of_le_of_lt hle (y_lower B n))
    ((y_strictMono B).monotone (lt_iff_succ_le.mp hnm))

theorem not_double (Y c k k' eta eta' : V) (hY : 1≤Y)
    (hEtaLt : eta<k) (hEta' : 0<eta') (hc : c=k*Y+eta) (hc' : c=k'*Y+eta') :
    ¬(2*k<k') := by
  have hUp : c<(Y+1)*k := by
    rw [hc]
    calc
      k*Y+eta<k*Y+k := _root_.add_lt_add_of_le_of_lt (le_refl _) hEtaLt
      _=(Y+1)*k := by ring
  have hLow : Y*k'<c := by
    rw [hc']
    simpa only [mul_comm] using lt_add_of_pos_right (k'*Y) hEta'
  have hYbound : Y+1≤2*Y := by
    calc
      Y+1≤Y+Y := _root_.add_le_add (le_refl Y) hY
      _=2*Y := by ring
  intro htwo
  have hh : (Y+1)*k<c := calc
    (Y+1)*k≤(2*Y)*k := mul_le_mul_of_nonneg_right hYbound (Arithmetic.zero_le _)
    _=Y*(2*k) := by ring
    _≤Y*k' := mul_le_mul_of_nonneg_left (le_of_lt htwo) (Arithmetic.zero_le _)
    _<c := hLow
  exact (not_lt_of_ge (le_of_lt hUp)) hh

theorem first_index_unique (B Y c k k' eta eta' n n' : V) (hY : 1≤Y)
    (hEta : 0<eta) (hEtaLt : eta<k)
    (hEta' : 0<eta') (hEtaLt' : eta'<k')
    (hc : c=k*Y+eta) (hc' : c=k'*Y+eta')
    (hk : k=2*ycoord n B) (hk' : k'=2*ycoord n' B) :
    n=n' ∧ k=k' := by
  have hIdx : n=n' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hh := double_lt_of_index_lt B n n' hlt
      have hk2 : 2*k<k' := by rw [hk,hk'];
        simpa only [mul_assoc] using mul_lt_mul_of_pos_left hh (by norm_num : (0:V)<2)
      exact (not_double Y c k k' eta eta' hY hEtaLt hEta' hc hc') hk2
    · have hh := double_lt_of_index_lt B n' n hgt
      have hk2 : 2*k'<k := by rw [hk,hk'];
        simpa only [mul_assoc] using mul_lt_mul_of_pos_left hh (by norm_num : (0:V)<2)
      exact (not_double Y c k' k eta' eta hY hEtaLt' hEta hc' hc) hk2
  refine ⟨hIdx,?_⟩
  rw [hk,hk',hIdx]

#print axioms double_lt_of_index_lt
#print axioms not_double
#print axioms first_index_unique
end FreeMainFirstOrdinateUnique
