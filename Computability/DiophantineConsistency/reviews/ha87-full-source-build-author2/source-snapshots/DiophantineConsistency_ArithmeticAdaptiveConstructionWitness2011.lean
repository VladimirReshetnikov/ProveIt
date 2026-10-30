import DiophantineConsistency.ArithmeticAdaptiveConstructionFactorLemmas2011
import DiophantineConsistency.ArithmeticAdaptiveConstructionStrong2011

/-! The explicit positive-coordinate adaptive vector and its strong factor. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionWitness2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011 ArithmeticAdaptiveStrongNorm2011
  ArithmeticAdaptiveConstructionStrong2011 ArithmeticAdaptiveConstructionFactorLemmas2011
  ArithmeticAdaptiveFactorMagnitude2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The thirteen source coordinates from the old vector and three newly
chosen positive correction coordinates. -/
def witness (v : Fin 14 → V) (r u gamma : V) : Fin 13 → V :=
  let q := ArithmeticCarrierRadix2011.q v
  let X := q*v 8
  let Y := v 7*q^3
  let a := X*Y+Y
  let delta := (a+1)*(a+3)
  ![v 0,v 1,v 2,v 4,delta*v 5,v 6,X,Y,r,v 10,v 11,u,gamma]

/-- The actual old strong equation supplies the additive strong norm for the
explicit adaptive vector, including the required rescaling of coordinate i. -/
theorem witness_strong_norm (v : Fin 14 → V) (r u gamma : V)
    (hv : ∀ j, 0<v j)
    (he : Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v) :
    StrongNorm (witness v r u gamma) := by
  let q := ArithmeticCarrierRadix2011.q v
  let X := q*v 8
  let Y := v 7*q^3
  let k := v 10+v 11
  let c := k*Y+v 10
  let a := X*Y+Y
  let delta := (a+1)*(a+3)
  have hf : (1:V)≤v 4*v 4 := one_le_mul (pos_iff_one_le.mp (hv 4)) (pos_iff_one_le.mp (hv 4))
  have hold : (delta*v 5*c*c)^2=delta*(v 4*v 4-1) := by
    have h := adaptive_strong_of_equations v he
    dsimp only at h
    convert h using 1 <;> dsimp only [delta,a,c,k,X,Y,q] <;> ring
  have hn : (delta*v 5*c*c)*(delta*v 5*c*c)+delta=delta*(v 4*v 4) := by
    calc _=(delta*v 5*c*c)^2+delta := by ring
         _=delta*(v 4*v 4-1)+delta := by rw [hold]
         _=delta*((v 4*v 4-1)+1) := by ring
         _=delta*(v 4*v 4) := by rw [tsub_add_cancel_of_le hf]
  change ((v 10+Y*k)*(v 10+Y*k)*(delta*v 5))*
      ((v 10+Y*k)*(v 10+Y*k)*(delta*v 5))+((3+4*a)+a*a) =
    ((3+4*a)+a*a)*(v 4*v 4)
  convert hn using 1 <;> dsimp only [delta,c] <;> ring

/-- The actual strong factor of the explicit witness is the positive unit. -/
theorem witness_strong_unit (p : Fin 4 → ℕ) (v : Fin 14 → V) (r u gamma : V)
    (hv : ∀ j, 0<v j)
    (he : Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v) :
    (ArithmeticAdaptiveFactorMagnitude2011.pairEval (factors (fun j => (p j:ℤ))).2.2.2 (witness v r u gamma)).1 =
      (ArithmeticAdaptiveFactorMagnitude2011.pairEval (factors (fun j => (p j:ℤ))).2.2.2 (witness v r u gamma)).2+1 :=
  strong_unit_of_norm p _ (witness_strong_norm v r u gamma hv he)
end DiophantineConsistency.ArithmeticAdaptiveConstructionWitness2011
