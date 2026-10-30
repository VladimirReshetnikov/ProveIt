import DiophantineConsistency.ArithmeticAdaptiveConstructionWitness2011
import DiophantineConsistency.ArithmeticAdaptiveConstructionMainFactor2011
import DiophantineConsistency.ArithmeticAdaptiveConstructionCorrectionSeed2011

/-! The actual outer seed gives the concrete witness's literal main unit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionMainChosen2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011 ArithmeticOuterSeed
  ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveFactorMagnitude2011
  ArithmeticAdaptiveConstructionWitness2011 ArithmeticAdaptiveConstructionMainFactor2011
  ArithmeticAdaptiveConstructionCorrectionSeed2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The given exact correction makes the concrete witness's literal main
factor a unit. The choice of gamma is made by a separate seed theorem. -/
theorem main_unit_of_correction (v : Fin 14 → V) (u r aux gamma t : V)
    (hF : v 1≤ArithmeticCarrierRadix2011.q v)
    (hq : ArithmeticCarrierRadix2011.q v=Exp.exp u)
    (hX : Exp.exp (rank v)=ArithmeticCarrierRadix2011.q v*v 8)
    (hseed : SeedRelations u (rank v) (v 7) (v 9) (v 10) (v 11) (v 13))
    (hk : (v 10+v 11)=rank v+1+
      ((v 7*(ArithmeticCarrierRadix2011.q v)^3)*(ArithmeticCarrierRadix2011.q v)^2)*t)
    (hgamma : gamma+v 8=v 13+t) :
    (ArithmeticAdaptiveFactorMagnitude2011.pairEval (factors CurrentWindowCarry2011.ports).2.1 (witness v r aux gamma)).1 =
      (ArithmeticAdaptiveFactorMagnitude2011.pairEval (factors CurrentWindowCarry2011.ports).2.1 (witness v r aux gamma)).2+1 := by
  let q := ArithmeticCarrierRadix2011.q v
  let X := q*v 8
  let Y := v 7*q^3
  let k := v 10+v 11
  let a := X*Y+Y
  let c := k*Y+v 10
  let H := 3+4*a
  let D := H+a*a
  let R := rank v
  let U := Y*(q*q)
  have hk' : k=R+1+U*t := by
    simpa only [k,U,Y,q,R,pow_two] using hk
  have hnorm : (X+a*c+H*v 13)*(X+a*c+H*v 13)=1+D*(c*c) := by
    have hh := hseed.2.1
    rw [←hq,hX] at hh
    convert hh using 1 <;> dsimp only [X,Y,k,a,c,H,D,q,R] <;> ring
  have hq1 : 1+v 0*(CurrentMasks2011.beta:V)=q := by
    change 1+v 0*(CurrentMasks2011.beta:V)=(CurrentMasks2011.beta:V)*v 0+1
    ring
  have hqm : q-1=v 0*(CurrentMasks2011.beta:V) := by
    rw [←hq1]
    simp
  have hrank : (v 2+(q-v 1)*(v 0*(CurrentMasks2011.beta:V)))*(q*q-1)+
      v 0*((CurrentMasks2011.lowPort:V)+((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)*q)=R := by
    change _ = ((q-1)*(q-v 1)+v 2)*(q^2-1)+
      ((CurrentMasks2011.lowPort:V)+q*((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V))*v 0
    rw [hqm]
    ring
  have hshift : U*gamma+X*Y*q+R+1=k+U*v 13 := by
    rw [hk']
    calc U*gamma+X*Y*q+R+1 = U*(gamma+v 8)+R+1 := by dsimp only [U,X]; ring
      _ = U*(v 13+t)+R+1 := by rw [hgamma]
      _ = R+1+U*t+U*v 13 := by ring
  rw [←currentPorts_cast]
  apply main_factor_of_additive currentPorts (witness v r aux gamma) (v 13)
  · change v 1≤1+v 0*(CurrentMasks2011.beta:V)
    rw [hq1]
    exact hF
  · change let q' := 1+v 0*(CurrentMasks2011.beta:V)
      Y*(q'*q')*gamma+X*Y*q'+
      ((v 2+(q'-v 1)*(v 0*(CurrentMasks2011.beta:V)))*(q'*q'-1)+
      v 0*((CurrentMasks2011.lowPort:V)+((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)*q'))+1=
        k+Y*(q'*q')*v 13
    dsimp only
    rw [hq1,hrank]
    exact hshift
  · change (X+a*(v 10+Y*k)+H*v 13)*(X+a*(v 10+Y*k)+H*v 13)=
      1+D*((v 10+Y*k)*(v 10+Y*k))
    convert hnorm using 1 <;> dsimp only [c] <;> ring
end DiophantineConsistency.ArithmeticAdaptiveConstructionMainChosen2011
