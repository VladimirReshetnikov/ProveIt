import DiophantineConsistency.ArithmeticAdaptiveConstructionWitness2011
import DiophantineConsistency.ArithmeticAdaptiveConstructionAuxFactor2011
import DiophantineConsistency.ArithmeticAdaptiveConstructionAuxBind2011

/-! Bind the literal auxiliary factor to the concrete witness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionAuxChosen2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011 ArithmeticPellRecurrence
  ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveAuxNorm2011 ArithmeticSignedPairs
  ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveConstructionWitness2011
  ArithmeticAdaptiveConstructionAuxFactor2011 ArithmeticAdaptiveConstructionAuxBind2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A given exact positive auxiliary coordinate and oriented seed make the
concrete witness's literal auxiliary factor a positive unit. -/
theorem aux_unit_of_coordinate (v : Fin 14 → V) (r aux gamma : V)
    (hv : ∀ j, 0<v j)
    (he : Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v)
    (hF : v 1≤ArithmeticCarrierRadix2011.q v)
    (horient : let q := ArithmeticCarrierRadix2011.q v
      let Y := v 7*q^3
      let c := (v 10+v 11)*Y+v 10
      let L := v 4*v 4*c*v 6
      let M := v 4*v 4*rank v+c
      L=(L-M)+(M-L)+c+v 4*v 4*rank v)
    (hu : let q := ArithmeticCarrierRadix2011.q v
      let Y := v 7*q^3
      let c := (v 10+v 11)*Y+v 10
      let L := v 4*v 4*c*v 6
      let M := v 4*v 4*rank v+c
      aux+((L-M)+(M-L))=v 12) :
    (ArithmeticAdaptiveFactorMagnitude2011.pairEval (factors CurrentWindowCarry2011.ports).2.2.1 (witness v r aux gamma)).1 =
      (ArithmeticAdaptiveFactorMagnitude2011.pairEval (factors CurrentWindowCarry2011.ports).2.2.1 (witness v r aux gamma)).2+1 := by
  let q := ArithmeticCarrierRadix2011.q v
  let X := q*v 8
  let Y := v 7*q^3
  let k := v 10+v 11
  let c := k*Y+v 10
  let a := X*Y+Y
  let delta := (a+1)*(a+3)
  let R := rank v
  let L := v 4*v 4*c*v 6
  let M := v 4*v 4*R+c
  let z := (L-M)+(M-L)
  let I := delta*v 5*c*c
  have hu' : aux+z=v 12 := hu
  have hL : L=M+z := by
    change L=z+c+v 4*v 4*R at horient
    rw [horient]
    dsimp only [M]
    ring
  have hzmag : magnitude (L,M)=z := magnitude_of_add hL
  have hLy : L+aux=M+v 12 := by rw [hL,←hu']; ring
  have hymag : magnitude (L+aux,M)=v 12 := magnitude_of_add hLy
  have hnorm : I*I*z*z+v 12*v 12=1+I*I*v 12*v 12 := by
    have hh := he.2.2.2.2
    let Iold := (((v 8*q)*Y+Y)+1)*(((v 8*q)*Y+Y)+3)*v 5*c*c
    change Iold*Iold*z*z+v 12*v 12=1+Iold*Iold*v 12*v 12 at hh
    have hX : v 8*q=X := by dsimp only [X]; ring
    have hIold : Iold=I := by
      dsimp only [Iold,I,delta,a]
      rw [hX]
    rw [hIold] at hh
    exact hh
  have hq1 : 1+v 0*(CurrentMasks2011.beta:V)=q := by
    change 1+v 0*(CurrentMasks2011.beta:V)=(CurrentMasks2011.beta:V)*v 0+1
    ring
  have hc : v 10+Y*k=c := by dsimp only [c]; ring
  have hL' : (v 4*v 4)*v 6*c=L := by dsimp only [L]; ring
  have hI : (c*c)*(delta*v 5)=I := by dsimp only [I]; ring
  rw [←currentPorts_cast]
  apply auxiliary_unit_of_norm currentPorts (witness v r aux gamma)
  · change v 1≤1+v 0*(CurrentMasks2011.beta:V)
    rw [hq1]; exact hF
  · exact witness_strong_norm v r aux gamma hv he
  · change let q' := 1+v 0*(CurrentMasks2011.beta:V)
      let c' := v 10+Y*k
      let I' := (c'*c')*(delta*v 5)
      let R' := ((q'-1)*(q'-v 1)+v 2)*(q'^2-1)+
        ((CurrentMasks2011.lowPort:V)+q'*((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V))*v 0
      let L' := (v 4*v 4)*v 6*c'
      let M' := (v 4*v 4)*R'+c'
      let z' := magnitude (L',M')
      let y' := magnitude (L'+aux,M')
      I'*I'*z'*z'+y'*y'=1+I'*I'*y'*y'
    dsimp only
    rw [hq1,hc,hL']
    change (c*c*(delta*v 5))*(c*c*(delta*v 5))*magnitude (L,M)*magnitude (L,M)+
      magnitude (L+aux,M)*magnitude (L+aux,M)=
      1+(c*c*(delta*v 5))*(c*c*(delta*v 5))*magnitude (L+aux,M)*magnitude (L+aux,M)
    rw [hI,hzmag,hymag]
    exact hnorm
end DiophantineConsistency.ArithmeticAdaptiveConstructionAuxChosen2011
