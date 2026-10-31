import DiophantineConsistency.AdaptiveGap85AuxSigned
import DiophantineConsistency.AdaptiveGap85StrongNorm
import DiophantineConsistency.AdaptiveGap85GenericSignedHalfIndex

/-! Conditional signed-rank half-index for an actual 85 zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ActualSignedHalf
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticPellRecurrence
open ArithmeticPellHalfIndex ArithmeticPellResidueAux
open ArithmeticAdaptiveStrongNorm2011 AdaptiveGap85Literal AdaptiveGap85StrongNorm
open AdaptiveGap85AuxSigned AdaptiveGap85GenericSignedHalfIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def rankMagnitude (p : Fin 4 → ℕ) (v : Fin 13 → V) : V :=
  let q : V := 1+v 0*(p 0:V)
  let q2 : V := q*q
  let neg : V := q*v 1+v 2
  let rp : V := q2*q2+neg+v 0*((p 2:V)+(p 3:V)*q)
  let rn : V := q2+neg*q2
  absdiff rp rn

/-- The main Pell index equals the magnitude of the actual signed rank,
under explicit growth and half-size hypotheses. -/
theorem expressionAt_signed_half85 (p : Fin 4 → ℕ) (v : Fin 13 → V) (m : V)
    (hv : ∀ j,0<v j) (hm6 : 6≤m)
    (hmy : ycoord m (v 6*v 7+v 7)=v 9+v 7*(v 9+v 10))
    (hR : 0<rankMagnitude p v)
    (hhalf : 2*rankMagnitude p v<v 9+v 7*(v 9+v 10))
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    m=rankMagnitude p v := by
  let q : V := 1+v 0*(p 0:V)
  let q2 : V := q*q
  let c : V := v 9+v 7*(v 9+v 10)
  let a : V := v 6*v 7+v 7
  let neg : V := q*v 1+v 2
  let rp : V := q2*q2+neg+v 0*((p 2:V)+(p 3:V)*q)
  let rn : V := q2+neg*q2
  let R : V := absdiff rp rn
  let f : V := v 3
  let i : V := v 4
  let z : V := absdiff (f*f*(v 5*c+rn)) (f*f*rp+c)
  have hc : 0<c := add_pos (hv 9) (mul_pos (hv 7) (add_pos (hv 9) (hv 10)))
  have hm : 0<m := lt_of_lt_of_le (by simp : (0:V)<6) hm6
  change ycoord m a=c at hmy
  change 0<R at hR
  change 2*R<c at hhalf
  have hbig : (a+2)*delta a*delta a<c := by rw [←hmy]; exact large_of_six a m hm6
  have hstrong := expressionAt_strong_norm85 p v hz
  change ((c*c)*i)*((c*c)*i)+((3+4*a)+a*a)=((3+4*a)+a*a)*(f*f) at hstrong
  have hi : c*c*i=i*c*c := by ring
  have hd : (3+4*a)+a*a=delta a := by unfold delta; ring
  rw [hi,hd] at hstrong
  have hmain : xcoord m a*xcoord m a=1+delta a*c*c := by
    have h := norm m a
    rw [hmy] at h
    exact h
  have haux := expressionAt_aux_signed85 p v hz
  change ((c*c)*i)*((c*c)*i)*z*z+v 11*v 11=1+((c*c)*i)*((c*c)*i)*(v 11*v 11) at haux
  rw [hi] at haux
  have ha : (i*c*c)*(i*c*c)*z*z+v 11*v 11=1+(i*c*c)*(i*c*c)*v 11*v 11 := by
    simpa only [mul_assoc] using haux
  exact signed_half_index_of_facts a c (xcoord m a) f i (v 5) rp rn (v 11) m hc (hv 4) (hv 3) hm (hv 11) hmy hR hhalf hmain hstrong hbig ha
end DiophantineConsistency.AdaptiveGap85ActualSignedHalf
