import DiophantineConsistency.AdaptiveGap85SignedRank
import DiophantineConsistency.AdaptiveGap85FirstDivisibility

/-! A signed main-root congruence without rank or root orientation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85SignedCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 AdaptiveGap85Literal AdaptiveGap85Quotients
open ArithmeticAdaptiveFirstDivisibility2011 AdaptiveGap85FirstDivisibility AdaptiveGap85SignedRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual zero forces a modulo-q⁵ equality for the signed rank pair. -/
theorem expressionAt_signed_congruence85 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    let q : V := 1+v 0*(p 0:V)
    let q2 : V := q*q
    let E : V := v 6*v 7
    let k : V := v 9+v 10
    let a : V := E+v 7
    let H : V := 3+4*a
    let neg : V := q*v 1+v 2
    let rp : V := q2*q2+neg+v 0*((p 2:V)+(p 3:V)*q)
    let rn : V := q2+neg*q2
    (H*(E*q+rp+1))%(q^5)=(H*(k+rn))%(q^5) := by
  let q : V := 1+v 0*(p 0:V)
  let q2 : V := q*q
  let U : V := v 7*q2
  let E : V := v 6*v 7
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let a : V := E+v 7
  let H : V := 3+4*a
  let neg : V := q*v 1+v 2
  let rp : V := q2*q2+neg+v 0*((p 2:V)+(p 3:V)*q)
  let rn : V := q2+neg*q2
  let z := pairEval (rootTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).2.1) v
  have hq : 0<q := by dsimp [q]; simp
  have hm : 0<q^5 := pow_pos hq _
  obtain ⟨s,_,hs⟩ := expressionAt_Y_quotient85 p v hb hv hz
  obtain ⟨_,main,_,_,_,_,hmain,_⟩ := expressionAt_quotients85 p v hb hv hz
  have hU : U=q^5*s := by dsimp [U,q2]; rw [hs]; ring
  have hd : q^5∣magnitude z := by
    refine ⟨s*main,?_⟩
    change magnitude z=U*main at hmain
    rw [hmain,hU]
    ring
  have hmod := magnitude_mod z (q^5) hm hd
  have he := equivalent_mod hm (main_root_signed85 p v) hmod
  change (U*(v 6+a*c)+H*(U*v 12+E*q+rp+1))%(q^5) = (H*(k+rn))%(q^5) at he
  have hleft : U*(v 6+a*c)+H*(U*v 12+E*q+rp+1) =
      H*(E*q+rp+1)+q^5*(s*(v 6+a*c)+H*(s*v 12)) := by rw [hU]; ring
  rw [hleft,mod_add_mul' _ _ hm] at he
  exact he
end DiophantineConsistency.AdaptiveGap85SignedCongruence
