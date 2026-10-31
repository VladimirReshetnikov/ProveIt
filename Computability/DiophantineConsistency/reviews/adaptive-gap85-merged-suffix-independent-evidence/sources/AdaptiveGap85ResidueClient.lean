import DiophantineConsistency.AdaptiveGap85StrongNorm
import DiophantineConsistency.AdaptiveGap85SignedResidue

/-! Signed auxiliary residue for a sufficiently large actual main index. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ResidueClient
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticPellRecurrence ArithmeticPellHalfIndex ArithmeticPellResidueAux
open ArithmeticAdaptiveStrongNorm2011 AdaptiveGap85Literal AdaptiveGap85StrongNorm AdaptiveGap85SignedResidue
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- If the main index is at least six, the auxiliary root and signed rank have the same residue up to sign. -/
theorem expressionAt_signed_residue85 (p : Fin 4 → ℕ) (v : Fin 13 → V) (m : V)
    (hv : ∀ j,0<v j) (hm6 : 6≤m)
    (hmy : ycoord m (v 6*v 7+v 7)=v 9+v 7*(v 9+v 10))
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    let q : V := 1+v 0*(p 0:V)
    let q2 : V := q*q
    let c : V := v 9+v 7*(v 9+v 10)
    let neg : V := q*v 1+v 2
    let rp : V := q2*q2+neg+v 0*((p 2:V)+(p 3:V)*q)
    let rn : V := q2+neg*q2
    SignMod c (absdiff (v 3*v 3*(v 5*c+rn)) (v 3*v 3*rp+c)) (absdiff rp rn) := by
  let c : V := v 9+v 7*(v 9+v 10)
  let a : V := v 6*v 7+v 7
  have hc : 0<c := add_pos (hv 9) (mul_pos (hv 7) (add_pos (hv 9) (hv 10)))
  change ycoord m a=c at hmy
  have hm : 0<m := lt_of_lt_of_le (by simp : (0:V)<6) hm6
  have hbig : (a+2)*delta a*delta a<c := by
    rw [←hmy]
    exact large_of_six a m hm6
  have hstrong := expressionAt_strong_norm85 p v hz
  change ((c*c)*v 4)*((c*c)*v 4)+((3+4*a)+a*a)=((3+4*a)+a*a)*(v 3*v 3) at hstrong
  have hs : (v 4*c*c)*(v 4*c*c)+delta a=delta a*(v 3*v 3) := by
    have hd : (3+4*a)+a*a=delta a := by unfold delta; ring
    rw [hd] at hstrong
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hstrong
  have hfmod := square_mod_one_of_relaxed_auxiliary a c m (v 4) (v 3) hm (hv 4) (hv 3) hc hmy hs hbig
  exact signed_rank_residue c (v 3) (v 5) _ _ hc hfmod
end DiophantineConsistency.AdaptiveGap85ResidueClient
