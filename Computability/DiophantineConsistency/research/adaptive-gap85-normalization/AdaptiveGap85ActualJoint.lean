import DiophantineConsistency.AdaptiveGap85FirstDivisibility
import DiophantineConsistency.AdaptiveGap85JointObstruction
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ActualJoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticGcdNormalization
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveScaledNorms2011
open ArithmeticAdaptiveQuotients2011 ArithmeticAdaptiveFirstDivisibility2011
open AdaptiveGap85Literal AdaptiveGap85Quotients AdaptiveGap85FirstDivisibility
open AdaptiveGap85JointObstruction AdaptiveGap85JointResidue
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The first actual factor forces the joint transport residue, with no
normalization or sign hypothesis on the transport factor. -/
theorem actual_zero_transport_mod (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    let b : V := v 0*(p 0:V)
    (v 1)%b=(v 2*(v 6+(p 1:V)))%b := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let Q : V := q*(q*q)
  let k : V := v 9+v 10
  let ell : V := (v 6*v 7)*(v 7*k)
  let M : V := Q*b
  let W : V := 1+k*b
  let A : V := v 6+(p 1:V)*q
  let Bp : V := v 2*A
  let Bn : V := v 1*q
  let z := pairEval (rootTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).1) v
  have hbpos : 0<b := mul_pos (hv 0) hb
  obtain ⟨t,d,_,_,ht,_,_,_⟩ := expressionAt_quotients85 p v hb hv hz
  change magnitude z=M*t at ht
  have hdiv : b∣magnitude z := ⟨Q*t,by rw [ht]; dsimp [M]; ring⟩
  have hzmod := magnitude_mod z b hbpos hdiv
  have hpair := equivalent_mod hbpos (first_root_rep85 p v) hzmod
  change (M*(ell+k+v 8)+v 7*b+Bn*(W*Q))%b = (Bp*(W*Q))%b at hpair
  have hWQ : W*Q=1+b*(k*Q+(q*q+q+1)) := by dsimp [W,Q,q]; ring
  have hleft : M*(ell+k+v 8)+v 7*b+Bn*(W*Q) =
      Bn+b*(Q*(ell+k+v 8)+v 7+Bn*(k*Q+(q*q+q+1))) := by
    rw [hWQ]
    dsimp [M]
    ring
  have hright : Bp*(W*Q)=Bp+b*(Bp*(k*Q+(q*q+q+1))) := by rw [hWQ]; ring
  rw [hleft,hright,mod_add_mul' _ _ hbpos,mod_add_mul' _ _ hbpos] at hpair
  have hbn : Bn=v 1+b*(v 1) := by dsimp [Bn,q]; ring
  have hbp : Bp=v 2*(v 6+(p 1:V))+b*(v 2*(p 1:V)) := by dsimp [Bp,A,q]; ring
  rw [hbn,hbp,mod_add_mul' _ _ hbpos,mod_add_mul' _ _ hbpos] at hpair
  exact hpair
/-- If b divides X+K, then every positive endpoint of the three-shift
coordinate orbit fails the reverse gap. This is conditional and does not
assert existence of a zero satisfying that divisibility. -/
theorem actual_zero_conditional_orbit_blocks (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v)
    (hA : v 0*(p 0:V) ∣ v 6+(p 1:V))
    (h : Relation.ReflTransGen (LiteralStep p) v w)
    (hwF : 0<w 1) (hwC : 0<w 2) :
    ¬ w 1+w 2<1+w 0*(p 0:V) := by
  let b : V := v 0*(p 0:V)
  have hbpos : 0<b := mul_pos (hv 0) hb
  change b∣v 6+(p 1:V) at hA
  have hm := actual_zero_transport_mod p v hb hv hz
  change (v 1)%b=(v 2*(v 6+(p 1:V)))%b at hm
  obtain ⟨t,ht⟩ := hA
  have hproduct : b ∣ v 2*(v 6+(p 1:V)) := ⟨v 2*t,by rw [ht]; ring⟩
  have hF : b∣v 1 := mod_eq_zero_iff_dvd.mp (hm.trans (mod_eq_zero_iff_dvd.mpr hproduct))
  have hAq : b ∣ v 6+(p 1:V)*(1+b) := by
    refine ⟨t+(p 1:V),?_⟩
    calc
      _ = (v 6+(p 1:V))+b*(p 1:V) := by ring
      _ = _ := by rw [ht]; ring
  exact literal_orbit_blocks_of_divisible_A_F p v w hbpos h hAq hF hwF hwC
end DiophantineConsistency.AdaptiveGap85ActualJoint
