import QuotientFacts

/-! Source-only folded parent signed-pair quotient fact. No graph binding,
Bt sign, positive quotient of Bt, Lean elaboration or endpoint is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ParentQuotientFactsDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticSignedPairs ArithmeticAdaptiveQuotients2011
open ArithmeticAdaptiveFirstDivisibility2011 ArithmeticGcdNormalization
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A folded parent scaled first norm forces q³|Y and b dividing the
magnitude of the signed Bt pair. It does not choose the sign of Bt. -/
theorem quotient_and_signed_divisibility (b Y P r k Bp Bn D : V)
    (hb : 0<b) (hY : 0<Y) (hD : 0<D)
    (hfield : let q := 1+b; let Q := q*(q*q); let M := Q*b; let W := 1+k*b
      (ι (M*(P+r)+b*Y+Bn*(W*Q))-ι (Bp*(W*Q)))*
        (ι (M*(P+r)+b*Y+Bn*(W*Q))-ι (Bp*(W*Q)))=(ι M*ι M)*ι D) :
    let q := 1+b
    let Q := q*(q*q)
    ∃ s tau : V, 0<s ∧ Y=Q*s ∧ 0<tau ∧ tau*tau=D ∧ b∣magnitude (Bp,Bn) := by
  let q : V := 1+b
  let Q : V := q*(q*q)
  let M : V := Q*b
  let W : V := 1+k*b
  let L : V := 3+3*b+b*b+k*Q
  let z := (M*(P+r)+b*Y+Bn*(W*Q),Bp*(W*Q))
  have hq : 0<q := by dsimp [q]; simp
  have hQ : 0<Q := by dsimp [Q]; exact mul_pos hq (mul_pos hq hq)
  have hM : 0<M := mul_pos hQ hb
  have hsq : magnitude z*magnitude z=M*M*D := by
    apply ι_injective
    simp only [map_mul,P72Root.ι_magnitude_sq]
    exact hfield
  obtain ⟨tau,ht,hn⟩ := scaled_quotient M (magnitude z) D hM hsq
  have htpos : 0<tau := pos_of_mul_pos_left (by rw [hn]; exact hD) (Arithmetic.zero_le tau)
  have hQdiv : Q∣magnitude z := by
    refine ⟨b*tau,?_⟩
    rw [ht]
    dsimp [M]
    ring
  have hQmod := magnitude_mod z Q hQ hQdiv
  change (M*(P+r)+b*Y+Bn*(W*Q))%Q=(Bp*(W*Q))%Q at hQmod
  have hleftQ : M*(P+r)+b*Y+Bn*(W*Q)=b*Y+Q*(b*(P+r)+Bn*W) := by dsimp [M]; ring
  have hrightQ : Bp*(W*Q)=Q*(Bp*W) := by ring
  have hzeroQ : (Q*(Bp*W))%Q=0 := by rw [mul_comm]; exact mod_mul_self_left _ _
  rw [hleftQ,hrightQ,mod_add_mul' _ _ hQ,hzeroQ] at hQmod
  have hby : Q∣b*Y := mod_eq_zero_iff_dvd.mp hQmod
  have hunit : Bez b Q 1 := by
    refine ⟨q*q+q+1,0,0,1,?_⟩
    dsimp [q,Q]
    ring
  obtain ⟨s,hs⟩ := unit_certificate_cancel hunit hby
  have hspos : 0<s := by
    apply pos_iff_ne_zero.mpr
    intro hs0
    have : Y=0 := by rw [hs,hs0,mul_zero]
    exact (ne_of_gt hY) this
  have hbdiv : b∣magnitude z := by
    refine ⟨Q*tau,?_⟩
    rw [ht]
    dsimp [M]
    ring
  have hbmod := magnitude_mod z b hb hbdiv
  change (M*(P+r)+b*Y+Bn*(W*Q))%b=(Bp*(W*Q))%b at hbmod
  have hWQ : W*Q=1+b*L := by dsimp [W,Q,q,L]; ring
  have hleftb : M*(P+r)+b*Y+Bn*(W*Q)=Bn+b*(Q*(P+r)+Y+Bn*L) := by
    rw [hWQ]
    dsimp [M]
    ring
  have hrightb : Bp*(W*Q)=Bp+b*(Bp*L) := by rw [hWQ]; ring
  rw [hleftb,hrightb,mod_add_mul' _ _ hb,mod_add_mul' _ _ hb] at hbmod
  have hbBt : b∣magnitude (Bp,Bn) := dvd_magnitude_of_mod hb hbmod.symm
  exact ⟨s,tau,hspos,hs,htpos,hn,hbBt⟩

end DiophantineConsistency.ParentQuotientFactsDraft

#print axioms DiophantineConsistency.ParentQuotientFactsDraft.quotient_and_signed_divisibility
