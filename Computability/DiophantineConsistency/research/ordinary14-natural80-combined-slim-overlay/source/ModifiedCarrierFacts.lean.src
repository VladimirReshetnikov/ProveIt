import DiophantineConsistency.Compact44.P72Power
import DiophantineConsistency.Compact44.CompactFixedBeta
import DiophantineConsistency.ArithmeticAdaptiveMersenne2011
import DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011
import DiophantineConsistency.ArithmeticAdaptiveFactorThree2011

/-! Source-only fact-level proposal for the modified main carrier. The
positivity, balance, recurrence and Pell hypotheses are explicit. No graph,
provider, elaboration or endpoint result is claimed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModifiedCarrierFactsDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticSignedPairs ArithmeticAdaptiveFirstDivisibility2011
open ArithmeticAdaptiveMainOrientation2011 ArithmeticAdaptiveFactorThree2011
open ArithmeticAdaptiveMersenne2011 ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Existing main-parts dominance specialized to the modified carrier,
which omits the old X*Y*q term. No old gamma or graph zero is assumed. -/
theorem modified_main_parts_positive (U X Y k eta gamma R : V)
    (hU : 0<U) (hY : 8≤Y) (hk : 0<k) :
    let a := X*Y+Y
    let c := eta+Y*k
    let H := 3+4*a
    H*k<U*(X+a*c)+H*(U*gamma+R+1) := by
  simpa only [mul_zero,add_zero] using
    (main_parts_positive U X Y k eta gamma (0:V) R hU hY hk)

/-- From an explicitly oriented modified balance and U=q⁵*s, recover the
q⁴ signed rank congruence. The factor-three cancellation does not assume
3 is coprime to q. -/
theorem q4_from_modified_balance (q Y X R k U s A d gamma : V)
    (hq : 0<q) (hY : q^3∣Y) (hU : U=q^5*s)
    (hbal : U*d+(3+4*Y*(X+1))*k =
      U*A+(3+4*Y*(X+1))*(U*gamma+R+1)) :
    q^4∣magnitude (R+1,k) := by
  let H : V := 3+4*Y*(X+1)
  have hm5 : 0<q^5 := pow_pos hq _
  have he : H*(R+1)+q^5*(s*(A+H*gamma)) = H*k+q^5*(s*d) := by
    calc
      H*(R+1)+q^5*(s*(A+H*gamma)) = U*A+H*(U*gamma+R+1) := by rw [hU]; ring
      _=U*d+H*k := by simpa only [H] using hbal.symm
      _=H*k+q^5*(s*d) := by rw [hU]; ring
  have hmod : (H*(R+1))%(q^5)=(H*k)%(q^5) := by
    have h := congrArg (fun z : V => z%(q^5)) he
    rwa [mod_add_mul' _ _ hm5,mod_add_mul' _ _ hm5] at h
  have hdiv : q^5∣H*magnitude (R+1,k) := by
    have h := dvd_magnitude_of_mod hm5 hmod
    have heq : magnitude (H*(R+1),H*k)=H*magnitude (R+1,k) := by
      dsimp [magnitude]
      rw [mul_add H ((R+1)-k) (k-(R+1)),mul_tsub H (R+1) k,mul_tsub H k (R+1)]
    rwa [heq] at h
  exact cancel_factor_three q Y X _ hq hY (by simpa only [H] using hdiv)

/-- The modified carrier and exact k-index relation give a natural balance
modulo H. No subtraction or positivity of gamma−W is used. -/
theorem modified_carrier_mod (U H d X a c gamma k R W : V)
    (hU : 0<U) (hH : 0<H) (hk : k=R+1+U*W)
    (hbal : U*d+H*k=U*(X+a*c)+H*(U*gamma+R+1)) :
    d%H=(X+a*c)%H := by
  have hl : U*d+H*k=U*(d+H*W)+H*(R+1) := by rw [hk]; ring
  have hr : U*(X+a*c)+H*(U*gamma+R+1)=U*(X+a*c+H*gamma)+H*(R+1) := by ring
  rw [hl,hr] at hbal
  have he : d+H*W=X+a*c+H*gamma :=
    mul_left_cancel₀ (ne_of_gt hU) (add_right_cancel hbal)
  have h := congrArg (fun z : V => z%H) he
  rwa [mod_add_mul' _ _ hH,mod_add_mul' _ _ hH] at h

/-- Proposed modified-carrier client for the existing fact-level power
recovery theorem. All Pell coordinates, indices and size premises are
explicit; no literal-zero wrapper is applied. -/
theorem modified_carrier_power (U H d X Y k R a c gamma W n m eta zeta : V)
    (hU : 0<U) (hHpos : 0<H) (hk : k=R+1+U*W)
    (hbal : U*d+H*k=U*(X+a*c)+H*(U*gamma+R+1))
    (hX16 : 16≤X) (hY0 : 0<Y) (hzeta : 0<zeta)
    (hkdef : k=eta+zeta) (hc : c=eta+Y*k) (hH : H=3+4*a)
    (ha : a=X*Y+Y)
    (hny : 2*ycoord n (2*((X*Y)*Y-1)+1)=k)
    (hn13 : 13≤n) (hnR : 2*n=R+1) (hmR : m=R)
    (hmx : xcoord m a=d) (hmy : ycoord m a=c) : X=Exp.exp R := by
  apply P72Power.power_of_mod X Y k R H d c a n m eta zeta
    hX16 hY0 hzeta hkdef hc hH ha hny hn13 hnR hmR hmx hmy
  exact modified_carrier_mod U H d X a c gamma k R W hU hHpos hk hbal

/-- Explicit Mersenne cancellation after a separately established power
identity and q∣3X. This is false for arbitrary q without the radix premise. -/
theorem mersenne_divides_X (t R q J X : V) (ht : 4≤t)
    (hq : q=(Exp.exp t-1)*J+1) (hX : X=Exp.exp R) (hdiv : q∣3*X) : q∣X := by
  rw [hX] at hdiv ⊢
  exact cancel_three t R q J ht hq hdiv

/-- Concrete symbolic beta specialization using the existing model beta
identity, not a theorem about external bytes. -/
theorem compact_beta_divides_X (J R X : V) (hX : X=Exp.exp R)
    (hdiv : (1+J*(CompactFixedBeta.betaNat:V))∣3*X) :
    (1+J*(CompactFixedBeta.betaNat:V))∣X := by
  let t : V := (67:V)*8807
  have ht : 4≤t := by dsimp [t]; norm_num
  have hb : (CompactFixedBeta.betaNat:V)=Exp.exp t-1 := by
    have h := CompactFixedBeta.beta_identity (V:=V)
    change (CompactFixedBeta.betaNat:V)+1=Exp.exp t at h
    rw [←h,add_tsub_cancel_right]
  have hq : 1+J*(CompactFixedBeta.betaNat:V)=(Exp.exp t-1)*J+1 := by rw [←hb]; ring
  exact mersenne_divides_X t R _ J X ht hq hX hdiv

end DiophantineConsistency.ModifiedCarrierFactsDraft

#print axioms DiophantineConsistency.ModifiedCarrierFactsDraft.modified_main_parts_positive
#print axioms DiophantineConsistency.ModifiedCarrierFactsDraft.q4_from_modified_balance
#print axioms DiophantineConsistency.ModifiedCarrierFactsDraft.modified_carrier_mod
#print axioms DiophantineConsistency.ModifiedCarrierFactsDraft.modified_carrier_power
#print axioms DiophantineConsistency.ModifiedCarrierFactsDraft.mersenne_divides_X
#print axioms DiophantineConsistency.ModifiedCarrierFactsDraft.compact_beta_divides_X
