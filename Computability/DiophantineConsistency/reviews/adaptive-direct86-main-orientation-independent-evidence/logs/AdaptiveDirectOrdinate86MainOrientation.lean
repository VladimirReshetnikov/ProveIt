import DiophantineConsistency.AdaptiveDirectOrdinate86TransportQuotient
import DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011

/-! Positive main root from the actual direct-ordinate zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86MainOrientation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveFirstDivisibility2011
open ArithmeticAdaptiveTransport2011 ArithmeticAdaptiveMainOrientation2011
open AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86Quotients AdaptiveDirectOrdinate86Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem expressionAt_Y_quotient86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) :
    ∃ s : V, 0<s ∧ v 7 =
      ((1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))))*s := by
  have hparams := scaled_parameters_positive p v hb hv
  obtain ⟨t,d,_,_,ht,_,_,_⟩ := expressionAt_quotients86 p v hb hv hz
  have hq : 0<1+v 0*(p 0:V) := lt_trans (by simp : (0:V)<1) hparams.1
  have hQ : 0<(1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))) :=
    mul_pos hq (mul_pos hq hq)
  obtain ⟨s,hs⟩ := quotient_forces_Y_divisible p v hparams.2.1 hQ t ht
  exact ⟨s,pos_of_mul_pos_right (by rw [←hs]; exact hv 7) (by simp),hs⟩

theorem expressionAt_main_oriented86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) : MainOriented p v := by
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
  have htransport := expressionAt_transport_positive86 p v hb hv hz
  have hsum : v 1+v 2<q := tsub_pos_iff_lt.mp htransport.2
  have hF : v 1≤q := le_trans (by simp : v 1≤v 1+v 2) (le_of_lt hsum)
  obtain ⟨s,hs,hsY⟩ := expressionAt_Y_quotient86 p v hb hv hz
  have hQ8 : (8:V)≤Q := calc
    8=2*(2*2) := by norm_num
    _≤q*(q*q) := mul_le_mul hq2 (mul_le_mul hq2 hq2 (by simp) (by simp)) (by simp) (by simp)
  have hY8 : (8:V)≤v 7 := calc
    8≤Q := hQ8
    _≤Q*s := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hs)
    _=v 7 := hsY.symm
  have hpos : dn<dp := main_parts_positive U (v 6) (v 7) k (v 9) (v 12) q R hU hY8 hk
  obtain ⟨first,main,_,hmainp,_,_,hmain,hnorm⟩ := expressionAt_quotients86 p v hb hv hz
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

end DiophantineConsistency.AdaptiveDirectOrdinate86MainOrientation
