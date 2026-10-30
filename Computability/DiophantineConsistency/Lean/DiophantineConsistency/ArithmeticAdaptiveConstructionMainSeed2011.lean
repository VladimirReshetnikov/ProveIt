import DiophantineConsistency.ArithmeticAdaptiveConstructionCorrectionSeed2011
import DiophantineConsistency.ArithmeticAdaptiveConstructionMainExact2011

/-! Bind the complete scaled main norm to the actual outer-seed relation. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionMainSeed2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticOuterSeed ArithmeticAdaptiveConstructionCorrectionSeed2011
  ArithmeticAdaptiveConstructionMainExact2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual outer seed, phase and multiplier yield a positive adaptive
main coordinate and its complete scaled norm. -/
theorem positive_main_of_seed (u R s n eta zeta gammaOld w : V)
    (hs : 0<s) (hg : 0<gammaOld) (hphase : R%4=3)
    (hXq : Exp.exp R=Exp.exp u*w)
    (hseed : SeedRelations u R s n eta zeta gammaOld) :
    let q := Exp.exp u
    let X := Exp.exp R
    let Y := s*q^3
    let k := eta+zeta
    let a := X*Y+Y
    let c := k*Y+eta
    let H := 4*a+3
    let delta := (a+1)*(a+3)
    ∃ gamma : V, 0<gamma ∧
      let D := (Y*q^2)*(X+a*c)+H*((Y*q^2)*gamma+q*(X*Y)-(k-R-1))
      D*D=(Y*q^2)*(Y*q^2)*(1+delta*c*c) := by
  obtain ⟨t,gamma,hgpos,hk,hgamma⟩ := positive_correction_of_seed u R s n eta zeta gammaOld w hs hg hphase hXq hseed
  dsimp only
  refine ⟨gamma,hgpos,?_⟩
  dsimp only [SeedRelations] at hseed
  have hnorm := hseed.2.1
  have hnorm' : (Exp.exp R+(Exp.exp R*(s*(Exp.exp u)^3)+s*(Exp.exp u)^3)*
      ((eta+zeta)*(s*(Exp.exp u)^3)+eta)+(4*(Exp.exp R*(s*(Exp.exp u)^3)+s*(Exp.exp u)^3)+3)*gammaOld)*
      (Exp.exp R+(Exp.exp R*(s*(Exp.exp u)^3)+s*(Exp.exp u)^3)*
      ((eta+zeta)*(s*(Exp.exp u)^3)+eta)+(4*(Exp.exp R*(s*(Exp.exp u)^3)+s*(Exp.exp u)^3)+3)*gammaOld)=
      1+(Exp.exp R*(s*(Exp.exp u)^3)+s*(Exp.exp u)^3+1)*
        (Exp.exp R*(s*(Exp.exp u)^3)+s*(Exp.exp u)^3+3)*
        ((eta+zeta)*(s*(Exp.exp u)^3)+eta)*((eta+zeta)*(s*(Exp.exp u)^3)+eta) := by
    simpa only [mul_comm gammaOld (4*(Exp.exp R*(s*(Exp.exp u)^3)+s*(Exp.exp u)^3)+3)] using hnorm
  exact main_norm_exact (Exp.exp u) (Exp.exp R) (s*(Exp.exp u)^3) w gamma gammaOld t R (eta+zeta)
    (Exp.exp R*(s*(Exp.exp u)^3)+s*(Exp.exp u)^3) ((eta+zeta)*(s*(Exp.exp u)^3)+eta)
    (4*(Exp.exp R*(s*(Exp.exp u)^3)+s*(Exp.exp u)^3)+3)
    ((Exp.exp R*(s*(Exp.exp u)^3)+s*(Exp.exp u)^3+1)*
      (Exp.exp R*(s*(Exp.exp u)^3)+s*(Exp.exp u)^3+3)) hXq hk hgamma hnorm'
end DiophantineConsistency.ArithmeticAdaptiveConstructionMainSeed2011
