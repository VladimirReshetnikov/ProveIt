import DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011

/-! Private additive compatibility for two upstream helper declarations, built
against the historical 87 provider. The declarations and proofs are copied
from the post-merge source; they extend the same namespaces. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011
open DiophantineConsistency.ArithmeticAdaptiveQuotients2011
open DiophantineConsistency.ArithmeticAdaptiveTransport2011
open DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
namespace DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011
theorem positive_Y_quotient_of_facts (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hM : 0<(1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V)))*(v 0*(p 0:V)))
    (hY : 0<v 7) (hquotients : Quotients p v) :
    ∃ s : V, 0<s ∧ v 7 =
      ((1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))))*s := by
  have hq : 0<1+v 0*(p 0:V) := by simp
  have hQ := mul_pos hq (mul_pos hq hq)
  obtain ⟨t,d,_,_,ht,_,_,_⟩ := hquotients
  obtain ⟨s,hs⟩ := quotient_forces_Y_divisible p v hM hQ t ht
  exact ⟨s,pos_of_mul_pos_right (by rw [←hs]; exact hY) (by simp),hs⟩

end DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011
namespace DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011
theorem main_oriented_of_facts (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hquotients : Quotients p v) (htransport : TransportPositive p v)
    (hY : ∃ s : V, 0<s ∧ v 7 =
      ((1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))))*s) :
    MainOriented p v := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let Q : V := q*(q*q)
  let U : V := v 7*(q*q)
  let E : V := v 6*v 7
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let a : V := E+v 7
  let H : V := 3+4*a
  let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  let dp : V := U*(v 6+a*c)+H*(U*v 12+E*q+R+1)
  let dn : V := H*k
  let z := pairEval (rootTerm (factors (fun j => (p j:ℤ))).2.1) v
  have hp := scaled_parameters_positive p v hb hv
  have hq : 1<q := hp.1
  have hq1 : (1:V)≤q := le_of_lt hq
  have hq2 : (2:V)≤q := by simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp hq
  have hU : 0<U := hp.2.2.1
  have hk : 0<k := hp.2.2.2.1
  have hsum : v 1+v 2<q := tsub_pos_iff_lt.mp htransport.2
  have hF : v 1≤q := le_trans (by simp : v 1≤v 1+v 2) (le_of_lt hsum)
  obtain ⟨s,hs,hsY⟩ := hY
  have hQ8 : (8:V)≤Q := calc
    8=2*(2*2) := by norm_num
    _≤q*(q*q) := mul_le_mul hq2 (mul_le_mul hq2 hq2 (by simp) (by simp)) (by simp) (by simp)
  have hY8 : (8:V)≤v 7 := calc
    8≤Q := hQ8
    _≤Q*s := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hs)
    _=v 7 := hsY.symm
  have hpos : dn<dp := main_parts_positive U (v 6) (v 7) k (v 9) (v 12) q R hU hY8 hk
  obtain ⟨first,main,_,hmainp,_,_,hmain,hnorm⟩ := hquotients
  have hre : Equivalent z (dp,dn) := main_root_rep p v hq1 hF
  have hmag : magnitude z=magnitude (dp,dn) := magnitude_equivalent hre
  have heq : dp=dn+(dp-dn) := by rw [add_comm,tsub_add_cancel_of_le (le_of_lt hpos)]
  have hcan : magnitude (dp,dn)=dp-dn := magnitude_of_add heq
  have hdiff : dp-dn=U*main := hcan.symm.trans (hmag.symm.trans hmain)
  have hpart : Equivalent (dp,dn) (natural (U*main)) := by
    change dp+0=dn+U*main
    simpa only [add_zero,hdiff] using heq
  refine ⟨main,hmainp,equivalent_trans hre hpart,?_⟩
  exact hnorm


end DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011
