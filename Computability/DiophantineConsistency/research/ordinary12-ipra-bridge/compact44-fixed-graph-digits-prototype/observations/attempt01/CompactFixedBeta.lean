import DiophantineConsistency.CompactMaskBoundFinish
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactFixedBeta
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def betaNat : ℕ := 2^(67*8807)-1

/-- Generic standard beta cast, proved without evaluating a concrete power. -/
theorem beta_identity_generic (n : ℕ) : (((2^n-1:ℕ):V)+1)=Exp.exp (n:V) := by
  have h := congrArg (fun z : ℕ => (z:V)) (Nat.sub_add_cancel (Nat.one_le_two_pow (n:=n)))
  rw [Nat.cast_add, Nat.cast_one, ← ArithmeticStandardCasts.cast_exp] at h
  exact h

/-- The fixed symbolic radix, without expanding the huge numeral. -/
theorem beta_identity : (betaNat:V)+1=Exp.exp ((67:V)*8807) := by
  have h := beta_identity_generic (V:=V) (67*8807)
  simpa only [betaNat,Nat.cast_mul,Nat.cast_ofNat] using h

theorem bounds (J : V) (hJ : 0<J) :
    let β : V := betaNat
    let L : V := CompactConcreteIncrement.mask
    let H : V := ((Nat.ofDigits (2^67) CompactHighPopulation.highDigits : ℕ):V)
    0<β ∧ L<β ∧ β+H<2*β ∧ 1≤H*J := by
  exact CompactMaskBoundFinish.bounds (betaNat:V) J beta_identity hJ
end CompactFixedBeta
#print axioms CompactFixedBeta.beta_identity_generic
#print axioms CompactFixedBeta.beta_identity
#print axioms CompactFixedBeta.bounds
