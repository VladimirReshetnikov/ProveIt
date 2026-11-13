import Absorb88Signs
import Mathlib.Tactic.LinearCombination

/-! Unchecked draft: signed transport divisibility without a transport bound. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Absorb88SignedDivisibility
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb88 Absorb88First Absorb88FirstQuotient Absorb88Transport Absorb88Signs
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Pure ring step, retaining both possible signs of the first root. -/
theorem signed_divisor {R : Type*} [CommRing R] (b q k r Bp Bn first : R)
    (h : b*r+Bn*((1+k*b)*q)=Bp*((1+k*b)*q)+b*first ∨
         Bp*((1+k*b)*q)=b*r+Bn*((1+k*b)*q)+b*first) :
    b ∣ q*(Bp-Bn) := by
  rcases h with hp | hn
  · refine ⟨r-first-k*q*(Bp-Bn), ?_⟩
    linear_combination -hp
  · refine ⟨r+first-k*q*(Bp-Bn), ?_⟩
    linear_combination hn

/-- Any actual positive graph zero gives signed b-divisibility in the model
    difference ring. No sign or order hypothesis on the transport is used. -/
theorem graph_signed_transport_divisibility (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let A : V := (p 1:V)+v 5
    let Bp : V := q*A
    let Bn : V := (v 1+v 2)*A+v 1
    (ι b : DiffRing V) ∣ (ι q)*(ι Bp-ι Bn) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let k : V := v 8+v 9
  let W : V := 1+k*b
  let A : V := (p 1:V)+v 5
  let Bp : V := q*A
  let Bn : V := (v 1+v 2)*A+v 1
  let zp : Pair V := (b*(v 7)+Bn*(W*q),Bp*(W*q))
  have hb0 : 0<b := mul_pos (hv 0) hb
  obtain ⟨first,_,hroot,_⟩ := first_root p v hz hb0
  have hmag : magnitude zp=b*first := by
    have he := magnitude_equivalent (root_rep p v)
    exact he.symm.trans hroot
  have hs := magnitude_cases zp.1 zp.2 (b*first) hmag
  apply signed_divisor (ι b) (ι q) (ι k) (ι (v 7)) (ι Bp) (ι Bn) (ι first)
  rcases hs with hp | hn
  · left
    have hh := congrArg (fun x : V => (ι x : DiffRing V)) hp
    dsimp only [zp,W] at hh
    simpa only [map_add,map_mul,map_one] using hh
  · right
    have hh := congrArg (fun x : V => (ι x : DiffRing V)) hn
    dsimp only [zp,W] at hh
    simpa only [map_add,map_mul,map_one] using hh

#print axioms Absorb88SignedDivisibility.signed_divisor
#print axioms Absorb88SignedDivisibility.graph_signed_transport_divisibility
end Absorb88SignedDivisibility
