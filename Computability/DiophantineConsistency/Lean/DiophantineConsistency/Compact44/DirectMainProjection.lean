import DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011

/-! Generic IΣ₁-model lemmas for a direct U*G main contribution.
These assume the displayed arithmetic hypotheses; they do not establish
those hypotheses for any candidate graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectMainProjection
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticAdaptiveMainOrientation2011 ArithmeticAdaptiveQuotients2011
open ArithmeticAdaptiveFirstDivisibility2011 ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticSignedPairs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The direct U*G root has positive orientation under the same scale and
size hypotheses; there is no requirement that G split as gamma+w. -/
theorem direct_parts_positive (U X Y k eta G R : V)
    (hU : 0 < U) (hY : 8 ≤ Y) (hk : 0 < k) :
    let a := X*Y+Y
    let c := eta+Y*k
    let H := 3+4*a
    H*k < U*(X+a*c)+H*(U*G+R+1) := by
  have h := main_parts_positive U X Y k eta G 0 R hU hY hk
  simpa only [mul_zero,add_zero] using h

/-- Positive scale cancels from the direct signed-root balance. -/
theorem cancel_direct_root (U X a c H G R W main : V) (hU : 0<U)
    (hroot : U*(X+a*c)+H*(U*G+R+1) = H*(R+1+U*W)+U*main) :
    X+a*c+H*G = main+H*W := by
  apply mul_left_cancel₀ (ne_of_gt hU)
  apply add_right_cancel (b:=H*(R+1))
  calc
    U*(X+a*c+H*G)+H*(R+1) = U*(X+a*c)+H*(U*G+R+1) := by ring
    _ = H*(R+1+U*W)+U*main := hroot
    _ = U*(main+H*W)+H*(R+1) := by ring

/-- Direct main-root balance and a Pell projection force X=P whenever both
are below H. This uses no gamma subtraction and no q-divisibility premise. -/
theorem direct_projection (U X a c H G R W main P t : V)
    (hU : 0<U) (hH : 0<H) (hX : X<H) (hP : P<H)
    (hroot : U*(X+a*c)+H*(U*G+R+1) = H*(R+1+U*W)+U*main)
    (hproj : main=P+a*c+H*t) : X=P := by
  have heq := cancel_direct_root U X a c H G R W main hU hroot
  have hm : (X+a*c)%H = main%H := by
    have h := congrArg (fun z : V => z%H) heq
    rw [mod_add_mul' _ _ hH, mod_add_mul' _ _ hH] at h
    exact h
  have hm' : (X+a*c)%H = (P+a*c)%H := by
    rw [hm,hproj,mod_add_mul' _ _ hH]
  have hmod : X%H=P%H := mod_cancel hH hm'
  rw [mod_eq_self_of_lt hX,mod_eq_self_of_lt hP] at hmod
  exact hmod

#print axioms DirectMainProjection.direct_parts_positive
#print axioms DirectMainProjection.cancel_direct_root
#print axioms DirectMainProjection.direct_projection
end DirectMainProjection
