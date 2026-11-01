import DiophantineConsistency.AdaptiveGap85Indices
import DiophantineConsistency.AdaptiveGap85SignedRank
import DiophantineConsistency.AdaptiveGap85FirstDivisibility
import DiophantineConsistency.AdaptiveGap85SignedOrientationTemplate
import DiophantineConsistency.AdaptiveGap85ThirdMainSyntax
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85NoThirdMain
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 ArithmeticPellRecurrence ArithmeticPellCongruences
open AdaptiveGap85Literal AdaptiveGap85Quotients AdaptiveGap85FirstDivisibility
open AdaptiveGap85SignedRank AdaptiveGap85ThirdMainSyntax AdaptiveGap85SignedOrientationTemplate
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- An actual positive 85-zero cannot have third main Pell ordinate. This is a
necessary restriction, not a proof that arbitrary 85-zeros do not exist. -/
theorem actual_zero_not_third_main (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    v 9+v 7*(v 9+v 10) ≠ ycoord 3 (v 6*v 7+v 7) := by
  intro h3
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
  have hc3 : c=ycoord 3 a := h3
  obtain ⟨first,main,hf,hm,hfirst,hnorm,hmain,hmnorm⟩ := expressionAt_quotients85 p v hb hv hz
  have hn : first*first=1+((v 6*v 7)*v 7)*(((v 6*v 7)*v 7)+1)*k*k := by
    change first*first=1+((v 6*v 7)*(v 7*k))*(((v 6*v 7)*(v 7*k))+k) at hnorm
    calc
      _ = 1+((v 6*v 7)*(v 7*k))*(((v 6*v 7)*(v 7*k))+k) := hnorm
      _ = _ := by ring
  have hmn : main*main=1+delta a*c*c := by
    change main*main=1+((3+4*a)+a*a)*(c*c) at hmnorm
    calc
      _ = 1+((3+4*a)+a*a)*(c*c) := hmnorm
      _ = _ := by unfold delta; ring
  obtain ⟨m,_,hmx,hmy⟩ := ArithmeticPellClassification.solution_index a main c hmn
  have hm3 : m=3 := (y_strictMono a).injective (hmy.trans hc3)
  have hmain3 : main=4*a*a*a+24*a*a+45*a+26 := by
    rw [hm3] at hmx
    exact hmx.symm.trans (third_coordinates a).2
  have hcv : c=4*(a*a+4*a+3)+3 := hc3.trans (third_coordinates a).1
  obtain ⟨s,_,hs⟩ := expressionAt_Y_quotient85 p v hb hv hz
  have hq3 : q*q*q∣v 7 := by
    refine ⟨s,?_⟩
    change v 7=(q*(q*q))*s at hs
    calc
      _ = (q*(q*q))*s := hs
      _ = (q*q*q)*s := by ring
  have hq2 : 2≤q := by
    have hh : 1≤v 0*(p 0:V) := pos_iff_one_le.mp (mul_pos (hv 0) hb)
    have h := add_le_add (le_refl (1:V)) hh
    change (2:V)≤1+v 0*(p 0:V)
    simpa only [show (1:V)+1=2 by ring] using h
  have h8 : (8:V)≤q*q*q := by
    have h4 : (4:V)≤q*q := by
      have hh := mul_le_mul hq2 hq2 (by simp) (by simp)
      calc
        _ = 2*2 := by ring
        _ ≤ _ := hh
    have hh := mul_le_mul h4 hq2 (by simp) (by simp)
    calc
      _ = 4*2 := by ring
      _ ≤ _ := hh
  have hY8 : 8≤v 7 := le_trans h8 (Arithmetic.le_of_dvd (hv 7) hq3)
  have hX1 : 1≤v 6 := pos_iff_one_le.mp (hv 6)
  have hkpos : 0<k := add_pos (hv 9) (hv 10)
  have he := main_root_signed85 p v
  change Equivalent z (U*(v 6+a*c)+H*A,H*B) at he
  change magnitude z=U*main at hmain
  have horient := magnitude_orientation z (U*(v 6+a*c)+H*A) (H*B) (U*main) he hmain
  rw [hmain3,hcv,ha] at horient
  dsimp only [H,U] at horient
  have hroot :
      (v 7*q*q)*(4*(v 7*(v 6+1))*(v 7*(v 6+1))*(v 7*(v 6+1))+
        24*(v 7*(v 6+1))*(v 7*(v 6+1))+45*(v 7*(v 6+1))+26)+(4*(v 7*(v 6+1))+3)*B =
        (v 7*q*q)*(v 6+(v 7*(v 6+1))*(4*((v 7*(v 6+1))*(v 7*(v 6+1))+4*(v 7*(v 6+1))+3)+3)) +
        (4*(v 7*(v 6+1))+3)*A ∨
      (v 7*q*q)*(4*(v 7*(v 6+1))*(v 7*(v 6+1))*(v 7*(v 6+1))+
        24*(v 7*(v 6+1))*(v 7*(v 6+1))+45*(v 7*(v 6+1))+26)+
        (v 7*q*q)*(v 6+(v 7*(v 6+1))*(4*((v 7*(v 6+1))*(v 7*(v 6+1))+4*(v 7*(v 6+1))+3)+3)) +
        (4*(v 7*(v 6+1))+3)*A = (4*(v 7*(v 6+1))+3)*B := by
    rcases horient with hpos | hneg
    · left; convert hpos using 1 <;> ring
    · right; convert hneg using 1 <;> ring
  have hc : v 9+v 7*k=4*((v 7*(v 6+1))*(v 7*(v 6+1))+4*(v 7*(v 6+1))+3)+3 := by
    change c=_
    rw [hcv,ha]
  have hn' : first*first=1+(v 6*v 7*v 7)*((v 6*v 7*v 7)+1)*k*k := hn
  exact exclude_signed_orientation_template (v 6) (v 7) q first k (v 9) (v 10) A B
    hX1 hY8 hq2 hkpos (hv 9) (hv 10) hq3 hn' rfl hc hroot
end DiophantineConsistency.AdaptiveGap85NoThirdMain
