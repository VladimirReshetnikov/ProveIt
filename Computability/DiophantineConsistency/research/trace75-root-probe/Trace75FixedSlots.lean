import Trace75FixedDigits
import DiophantineConsistency.CompactMixedIncrement

/-! Slotwise low-mask no-carry for the actual 80 graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
noncomputable section
namespace Trace75FixedSlots
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing TenPositiveTrace75 ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits CompactSymbolicPorts
open Trace75Factors Trace75Rank Trace75NaturalTransport
attribute [local irreducible] CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

-- The general increment lemma is the existing CompactPositionCarry argument,
-- reproduced here to bind its exact proof source to this selected provider.
theorem increment_digits (m N C MC : V) (hm : 0 < m) (hN : 0 < N)
    (hMC : MC < Exp.exp (67*m))
    (hMC0 : dig 67 MC 0 = Exp.exp 67-2) (hC : 1 ≤ C)
    (hnc : NoCarry (C-1) (MC * rep (67*m) N + 1)) :
    dig 67 C 0 = 1 ∧ ∀ k < m*N, 0 < k → NoCarry (dig 67 C k) (dig 67 MC (k % m)) := by
  have h2 : (2:V) ≤ Exp.exp 67 := by
    simpa using exp_monotone_le.mpr (show (1:V) ≤ 67 by norm_num)
  set e := Exp.exp (67:V)-2
  have he : Exp.exp (67:V) = e+2 := (tsub_add_cancel_of_le h2).symm
  have hρ1 : Exp.exp (67:V)-1=e+1 := by
    rw [he, show e+2=(e+1)+1 by ring, add_tsub_cancel_right]
  have hmN : 0 < m*N := mul_pos hm hN
  have hJ : ∀ k < m*N, dig 67 (MC * rep (67*m) N) k = dig 67 MC (k % m) :=
    dig_mul_rep 67 m MC hMC N
  have h0 : dig 67 (MC * rep (67*m) N) 0 = e := by
    rw [hJ 0 hmN, zero_mod, hMC0]
  obtain ⟨hinc0, hinck⟩ := dig_add_one 67 (MC * rep (67*m) N)
    (by rw [h0, he]; exact (add_lt_add_iff_left e).mpr one_lt_two)
  have hz : dig 67 (C-1) 0 = 0 := by
    apply noCarry_ones 67 _ (dig_lt 67 _ 0)
    simpa only [hinc0, h0, ←hρ1] using noCarry_dig 67 _ _ 0 hnc
  have hC1 : C-1+1=C := tsub_add_cancel_of_le hC
  obtain ⟨hc0, hck⟩ := dig_add_one 67 (C-1)
    (by rw [hz, zero_add, he]; exact lt_of_lt_of_le one_lt_two (le_add_of_nonneg_left (by simp)))
  rw [hC1] at hc0 hck
  refine ⟨by rw [hc0,hz,zero_add], ?_⟩
  intro k hk hk0
  simpa only [hinck k hk0, hJ k hk, ←hck k hk0] using noCarry_dig 67 _ _ k hnc


theorem graph_fixed_slots (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=CompactFixedBeta.betaNat) (hp2 : p 2=lowNat)
    (hp3 : p 3=CompactFixedBeta.betaNat+highNat)
    (hv : ∀j,0<v j) (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    ∃ N : V, 0<N ∧ v 0=rep (67*8807) N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      0<Cnat p v ∧ dig 67 (Cnat p v) 0=1 ∧
      (∀ j<8807*N, 0<j → NoCarry (dig 67 (Cnat p v) j) (dig 67 (lowNat:V) (j%8807))) ∧
      NoCarry (v 1) ((highNat:V)*v 0-1) := by
  obtain ⟨N,hN,hJ,hq,_hpop,hlow,hhigh⟩ :=
    Trace75FixedSaturation.graph_fixed_saturation p v hp0 hp2 hp3 hv hz
  obtain ⟨h31,hl,hh⟩ := Trace75FixedBounds.fixed_bounds (V:=V) p hp0 hp2 hp3
  obtain ⟨_t,hC,_ht⟩ := graph_natural_transport p v h31 hl hh hv hz
  have hmask : (lowNat:V)<Exp.exp (67*8807) := by
    unfold lowNat
    exact CompactConcreteMask.model_lt
  have hmask0 : dig 67 (lowNat:V) 0=Exp.exp 67-2 := by
    unfold lowNat
    exact CompactConcreteMask.model_origin
  have hn : NoCarry (Cnat p v-1) ((lowNat:V)*rep (67*8807) N+1) := by
    simpa only [Cnat,hp2,hJ] using hlow
  obtain ⟨hzero,hslots⟩ := increment_digits 8807 N (Cnat p v) (lowNat:V)
    (by norm_num) hN hmask hmask0 (pos_iff_one_le.mp hC) hn
  exact ⟨N,hN,hJ,hq,hC,hzero,hslots,hhigh⟩

#print axioms Trace75FixedSlots.increment_digits
#print axioms Trace75FixedSlots.graph_fixed_slots
end Trace75FixedSlots
