import DiophantineConsistency.CompactSameWitnessSaturation2
import DiophantineConsistency.CompactMixedIncrement
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
noncomputable section
namespace CompactPositionCarry
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits CompactSymbolicPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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

/-- Per-slot no-carry for the exact symbolic fixed tuple and graph witness.
    This does not establish the retained low port or any word rotation. -/
theorem symbolic_position_noCarry (K : ℕ) (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat K lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat K lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      v 5=q*w ∧ (((p 1:V)+w)*C)%(v 0*(p 0:V))=v 1 ∧ dig 67 C 0=1 ∧
      (∀ k<8807*N, 0<k → NoCarry (dig 67 C k) (dig 67 (lowNat:V) (k%8807))) ∧
      NoCarry (v 1) ((highNat:V)*v 0-1) := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,hcongr,h0,hlim,hlow,hhigh⟩ :=
    CompactSameWitnessSaturation.fixed_graph_saturation K v hv hz
  let p := ports CompactFixedBeta.betaNat K lowNat highNat
  let q : V := 1+v 0*(p 0:V)
  let C : V := q-v 1-v 2
  have hC : 1≤C := by
    have h := mod_le C (Exp.exp (67:V))
    rw [←dig_zero_index 67 C,h0] at h
    exact h
  have hmask : (lowNat:V)<Exp.exp (67*8807) := CompactConcreteMask.model_lt
  have hmask0 : dig 67 (lowNat:V) 0=Exp.exp 67-2 := CompactConcreteMask.model_origin
  have hn : NoCarry (C-1) ((lowNat:V)*rep (67*8807) N+1) := by
    change NoCarry (C-1) ((lowNat:V)*v 0+1) at hlow
    simpa only [hJ] using hlow
  have hextract := increment_digits 8807 N C (lowNat:V) (by norm_num) hN hmask hmask0 hC hn
  exact ⟨N,w,hN,hq,hJ,hv5,hcongr,h0,hextract.2,hhigh⟩
end CompactPositionCarry
#print axioms CompactPositionCarry.increment_digits
#print axioms CompactPositionCarry.symbolic_position_noCarry
