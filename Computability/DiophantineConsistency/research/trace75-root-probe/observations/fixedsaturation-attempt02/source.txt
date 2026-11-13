import Trace75Saturation
import Trace75FixedBounds
import DiophantineConsistency.CompactLowExact
import DiophantineConsistency.CompactLowEven
import DiophantineConsistency.CompactHighResidue

/-! Specialization of the actual trace75 graph saturation to symbolic compact masks. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75FixedSaturation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticBinaryPopulation ArithmeticBinaryCarry
open Trace75Factors Trace75Rank Trace75FixedBounds
attribute [local irreducible] CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_fixed_saturation (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hv : ∀j,0<v j) (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    ∃ N : V, 0<N ∧ v 0=rep (67*8807) N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      3*((67*8807)*N)+2≤population (rankNat p v) ∧
      NoCarry (q p v-v 1-v 2-1) ((p 2:V)*v 0+1) ∧
      NoCarry (v 1) ((highNat:V)*v 0-1) := by
  obtain ⟨h31,hl,hh⟩ := fixed_bounds (V:=V) p hp0 hp2 hp3
  have hb : (p 0:V)+1=Exp.exp ((67:V)*8807) := by rw [hp0]; exact beta_identity
  have hlv : (p 2:V)=CompactConcreteIncrement.mask := by rw [hp2]; unfold lowNat CompactConcreteIncrement.mask; rfl
  have hhigh : (highNat:V)=((Nat.ofDigits (2^67) CompactHighPopulation.highDigits : ℕ):V) := by
    have he : highNat=Nat.ofDigits (2^67) CompactHighPopulation.highDigits := by unfold highNat; rfl
    rw [he]
  have hport : (p 3:V)=(highNat:V)+(p 0:V) := by rw [hp3,hp0,Nat.cast_add,add_comm]
  have hMC : (p 2:V)<Exp.exp ((67:V)*8807) := by rw [hlv]; exact CompactConcreteMask.model_lt
  have hHP : (highNat:V)<Exp.exp ((67:V)*8807) := by rw [hhigh]; exact CompactHighPopulation.model_lt
  have hMC2 : (p 2:V)%2=0 := by rw [hlv]; exact CompactLowEven.low_even
  have hHP8 : (highNat:V)%8=4 := by rw [hhigh]; exact CompactHighResidue.model_mod_eight
  have hsum : population (p 2:V)+population (highNat:V)=(67:V)*8807 := by
    rw [hlv,hhigh]
    change population ((Nat.ofDigits (2^67) (CompactListMask.digits (2^67) 8807 1063 CompactConcreteMask.support) : ℕ):V)+_=_
    rw [CompactLowExact.model_population,CompactHighPopulation.model_population]
    norm_num
  have hHPJ : 1≤(highNat:V)*v 0 := by
    have h := CompactFixedBeta.bounds (v 0) (hv 0)
    rw [hhigh]
    exact h.2.2.2
  exact Trace75Saturation.graph_saturation p v ((67:V)*8807) (highNat:V)
    h31 hl hh hv hz (by norm_num) hb hport hMC hHP hMC2 hHP8 hsum hHPJ

#print axioms Trace75FixedSaturation.graph_fixed_saturation
end Trace75FixedSaturation
