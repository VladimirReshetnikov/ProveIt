import Absorb88SignedDivisibility

/-! Unchecked draft: remove the unit factor q=1+b from signed divisibility. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Absorb88SignedUnscaled
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb88 Absorb88First
open AdaptiveEquationSyntax2011 ModelDifferenceRing Absorb88SignedDivisibility
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A factor congruent to one modulo b may be removed in any commutative ring. -/
theorem remove_one_add {R : Type*} [CommRing R] (b z : R)
    (h : b ∣ (1+b)*z) : b ∣ z := by
  obtain ⟨s,hs⟩ := h
  refine ⟨s-z, ?_⟩
  calc
    z=(1+b)*z-b*z := by ring
    _=b*s-b*z := by rw [hs]
    _=b*(s-z) := by ring

/-- The unscaled signed transport difference is divisible by b, without a
    sign assumption for that difference or a natural subtraction claim. -/
theorem graph_signed_unscaled_divisibility (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let A : V := (p 1:V)+v 5
    let Bp : V := q*A
    let Bn : V := (v 1+v 2)*A+v 1
    (ι b : DiffRing V) ∣ (ι Bp-ι Bn) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let A : V := (p 1:V)+v 5
  let Bp : V := q*A
  let Bn : V := (v 1+v 2)*A+v 1
  have h := graph_signed_transport_divisibility p v hb hv hz
  change (ι b : DiffRing V) ∣ (ι q)*(ι Bp-ι Bn) at h
  have hq : (ι q : DiffRing V)=1+ι b := by simp only [q,map_add,map_one]
  rw [hq] at h
  exact remove_one_add (ι b) (ι Bp-ι Bn) h

#print axioms Absorb88SignedUnscaled.remove_one_add
#print axioms Absorb88SignedUnscaled.graph_signed_unscaled_divisibility
end Absorb88SignedUnscaled
