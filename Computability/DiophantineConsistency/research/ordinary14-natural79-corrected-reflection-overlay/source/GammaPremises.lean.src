import GammaZeroNarrow
import DiophantineConsistency.ArithmeticPellClassification
import DiophantineConsistency.BFS943.Direct80IndexOne

/-! Source-only fact-level route to the narrow gamma hypotheses. The two
norms, recurrence and rank bounds are explicit; no graph binding is claimed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.GammaPremisesDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellFirstNorm
open GammaZeroNarrowDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The first and main norms exclude the first Pell index one. This is a
fact-level statement; a literal graph zero is not a hypothesis. -/
theorem large_ordinate_of_two_norms (m tau k eta zeta X Y d : V)
    (hm : 0<m) (heta : 0<eta) (hzeta : 0<zeta) (hY : 1≤Y)
    (hk : k=eta+zeta)
    (hfirst : tau*tau=1+m*(m+1)*k*k)
    (hmain : d*d=1+((X*Y+Y+1)*(X*Y+Y+3))*
      ((eta+Y*k)*(eta+Y*k))) : 8*m+4≤k := by
  let a : V := X*Y+Y
  let c : V := eta+Y*k
  have hmain' : d*d=1+delta a*c*c := by simpa [a,c,delta,mul_assoc] using hmain
  obtain ⟨j,_,_,hj⟩ := ArithmeticPellClassification.solution_index a d c hmain'
  have hYle : Y≤a+1 := by dsimp [a]; nlinarith
  have hbase : (a+1)*(0+1)-1=a := by simp
  have hc : (eta+zeta)*Y+eta=ycoord j ((a+1)*(0+1)-1) := by
    rw [hbase,hj]
    dsimp [c]
    rw [hk]
    ring
  have hkne : k≠2 := by
    intro hk2
    have hsum : eta+zeta=2 := by rw [←hk]; exact hk2
    exact Direct80IndexOne.impossible Y (a+1) 0 eta zeta j hY hYle heta hzeta hsum hc
  have hkpos : 0<k := by rw [hk]; exact add_pos heta hzeta
  obtain ⟨n,_,_,hcoord⟩ := positive_parameter_solution m tau k hm hfirst
  have hnpos : 0<n := pos_iff_ne_zero.mpr (by
    intro hn0
    apply ne_of_gt hkpos
    simpa [hn0] using hcoord.symm)
  have hnne : n≠1 := by
    intro hn1
    have hy1 : ycoord 1 (2*(m-1)+1)=1 := by simpa using y_succ (0:V) _
    apply hkne
    rw [hn1,hy1] at hcoord
    simpa using hcoord.symm
  have hngt : 1<n := lt_of_le_of_ne (pos_iff_one_le.mp hnpos) (Ne.symm hnne)
  have hn2 : 2≤n := by simpa only [show (1:V)+1=2 by ring] using lt_iff_succ_le.mp hngt
  exact first_ordinate_lower m n k hm hn2 hcoord

/-- Explicit rank/radix inputs turn the Pell bound into the two inequalities
needed by `gamma_zero_impossible`. -/
theorem narrow_inequalities (q X Y k eta R : V)
    (hq : 2≤q) (hX : q≤X) (hY : q^3≤Y) (heta : 0<eta)
    (hk : 8*(X*Y*Y)+4≤k) (hR : R+q^3+q+1≤q^4) :
    R+1<k ∧ X<eta+Y*k := by
  have hqpos : 0<q := lt_of_lt_of_le (by simp : (0:V)<2) hq
  have hYpos : 0<Y := lt_of_lt_of_le (pow_pos hqpos 3) hY
  have hY1 : 1≤Y := pos_iff_one_le.mp hYpos
  have hq4 : q^4≤X*Y*Y := calc
    q^4=q*q^3 := by ring
    _≤X*Y := mul_le_mul hX hY (by simp) (by simp)
    _≤X*Y*Y := le_mul_of_one_le_right (by simp) hY1
  have hm : X*Y*Y<k := lt_of_lt_of_le (by nlinarith [show (0:V)≤X*Y*Y by simp]) hk
  have hR' : R+1≤q^4 := by nlinarith
  have hX' : X≤X*Y*Y := by
    calc
      X≤X*Y := le_mul_of_one_le_right (by simp) hY1
      _≤X*Y*Y := le_mul_of_one_le_right (by simp) hY1
  have hkY : k≤Y*k := by
    simpa only [mul_comm] using (le_mul_of_one_le_right (show (0:V)≤k by simp) hY1)
  constructor
  · exact lt_of_le_of_lt (le_trans hR' hq4) hm
  · exact lt_of_lt_of_le (lt_of_le_of_lt hX' hm) (le_trans hkY (by simp))

end DiophantineConsistency.GammaPremisesDraft

#print axioms DiophantineConsistency.GammaPremisesDraft.large_ordinate_of_two_norms
#print axioms DiophantineConsistency.GammaPremisesDraft.narrow_inequalities
