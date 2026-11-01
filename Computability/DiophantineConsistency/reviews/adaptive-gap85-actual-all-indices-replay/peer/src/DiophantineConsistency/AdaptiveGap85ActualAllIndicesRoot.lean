import DiophantineConsistency.AdaptiveGap85Indices
import DiophantineConsistency.AdaptiveGap85SignedRank
import DiophantineConsistency.AdaptiveGap85FirstDivisibility
import DiophantineConsistency.AdaptiveGap85ThirdMainSyntax
import DiophantineConsistency.AdaptiveGap85AllIndicesRoot
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ActualAllIndicesRoot
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 ArithmeticPellRecurrence
open AdaptiveGap85Literal AdaptiveGap85Indices AdaptiveGap85FirstDivisibility AdaptiveGap85SignedRank
open AdaptiveGap85ThirdMainSyntax AdaptiveGap85AllIndicesRoot
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Every actual positive 85-zero has an internal main Pell index satisfying
one of these signed-root congruences. This does not exclude such zeros. -/
theorem actual_zero_root_congruences (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    ∃ m : V, 0<m ∧ ycoord m (v 6*v 7+v 7)=v 9+v 7*(v 9+v 10) ∧
      ((27*v 6)%(4*(v 7*(v 6+1))+3)=(27*Exp.exp m)%(4*(v 7*(v 6+1))+3) ∨
       (27*(1+Exp.exp m*v 6))%(4*(v 7*(v 6+1))+3)=0) := by
  let q : V := 1+v 0*(p 0:V)
  let U : V := v 7*(q*q)
  let E : V := v 6*v 7
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let a : V := E+v 7
  let H : V := 3+4*a
  let neg : V := q*v 1+v 2
  let rp : V := (q*q)*(q*q)+neg+v 0*((p 2:V)+(p 3:V)*q)
  let rn : V := q*q+neg*(q*q)
  let A : V := U*v 12+E*q+rp+1
  let B : V := k+rn
  let z := pairEval (rootTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).2.1) v
  have ha : a=v 7*(v 6+1) := by dsimp [a,E]; ring
  obtain ⟨first,main,n,m,hf,hm,hnp,hmp,hnk,hmc,hfirst,hmain,hnx,hny,hmx,hmy⟩ := expressionAt_indices85 p v hb hv hz
  obtain ⟨s,_,hs⟩ := expressionAt_Y_quotient85 p v hb hv hz
  have hqY : q∣v 7 := by
    refine ⟨q*q*s,?_⟩
    change v 7=(q*(q*q))*s at hs
    calc
      _ = (q*(q*q))*s := hs
      _ = q*(q*q*s) := by ring
  have hY1 : 1≤v 7 := pos_iff_one_le.mp (hv 7)
  have he := main_root_signed85 p v
  change Equivalent z (U*(v 6+a*c)+H*A,H*B) at he
  change magnitude z=U*main at hmain
  have horient := magnitude_orientation z (U*(v 6+a*c)+H*A) (H*B) (U*main) he hmain
  change xcoord m a=main at hmx
  change ycoord m a=c at hmy
  rw [←hmx,←hmy,ha] at horient
  dsimp only [H,U] at horient
  have hroot :
      (v 7*q*q)*xcoord m (v 7*(v 6+1))+(4*(v 7*(v 6+1))+3)*B =
        (v 7*q*q)*(v 6+(v 7*(v 6+1))*ycoord m (v 7*(v 6+1)))+(4*(v 7*(v 6+1))+3)*A ∨
      (v 7*q*q)*xcoord m (v 7*(v 6+1))+(v 7*q*q)*(v 6+(v 7*(v 6+1))*ycoord m (v 7*(v 6+1)))+
        (4*(v 7*(v 6+1))+3)*A=(4*(v 7*(v 6+1))+3)*B := by
    rcases horient with hpos | hneg
    · left; convert hpos using 1 <;> ring
    · right; convert hneg using 1 <;> ring
  exact ⟨m,hmp,hmy,root_congruences (v 6) (v 7) q m A B hY1 hqY hroot⟩
end DiophantineConsistency.AdaptiveGap85ActualAllIndicesRoot
