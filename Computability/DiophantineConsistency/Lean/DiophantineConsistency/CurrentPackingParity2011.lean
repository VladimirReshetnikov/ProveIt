import DiophantineConsistency.CurrentPackingRank2011

/-! The actual low mask fixes the constructed rank at3 modulo4.
No positive source-system zero or auxiliary Pell seed is assumed. -/

namespace DiophantineConsistency.CurrentPackingParity2011

open Jones1982 CurrentMasks2011 CurrentPackingRank2011
  CurrentWordScalarWitness2011 CurrentWordConstruction2011 CurrentWordCopies2011

set_option Elab.async false
set_option maxRecDepth 10000

variable {N : ℕ} [NeZero N]

theorem q_mod_four : q N % 4 = 0 := by
  rw [q_binary]
  apply Nat.mod_eq_zero_of_dvd
  change 2^2 ∣ 2^(width*N)
  apply pow_dvd_pow
  have hw : 2 ≤ width := by decide
  have hN := NeZero.pos N
  nlinarith

theorem repunit_mod_four : NativeMaskPopulation.repunit width N % 4 = 1 := by
  have h := NativeMaskPopulation.repunit_mod_eight
    (by decide : 3 ≤ width) (NeZero.pos N)
  omega

private theorem blocks_mod_four (q A B C D E : ℕ)
    (hq : q%4=0) (hA : A%4=0) (hB : B%4=3) :
    (A+B+q*C+q^2*D+q^3*E)%4=3 := by
  norm_num [Nat.add_mod,Nat.mul_mod,Nat.pow_mod,hq,hA,hB]

/-- The actual adjusted low mask, not just its evenness, fixes the rank class. -/
theorem fourBlocks_mod_four (C F : ℕ)
    (hm : (C-1) &&& (lowPort*NativeMaskPopulation.repunit width N+1) = 0) :
    fourBlocks N C F % 4 = 3 := by
  have hM : (lowPort*NativeMaskPopulation.repunit width N+1) % 4 = 3 := by
    norm_num [Nat.add_mod,Nat.mul_mod,lowPort_four,repunit_mod_four]
  have hl := congrArg (fun z : ℕ => z % 2^2) hm
  rw [Nat.and_mod_two_pow] at hl
  change (C-1)%4 &&& (lowPort*NativeMaskPopulation.repunit width N+1)%4 = 0 at hl
  rw [hM] at hl
  have hpre : (C-1)%4 = 0 := by
    simpa only [show (3:ℕ)=2^2-1 by decide,
      Nat.and_two_pow_sub_one_eq_mod,Nat.mod_mod] using hl
  exact blocks_mod_four (q N) (C-1) (lowPort*NativeMaskPopulation.repunit width N+1)
    (F+(highPort*NativeMaskPopulation.repunit width N-1)) (q N-C) (q N-F-1)
    q_mod_four hpre hM

/-- All required rank facts refer to the same particular constructed packing. -/
theorem packing_rank (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (s : ℕ) (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentNativePacking2011.Facts a dummy s k digits) :
    ∃ R r : ℕ,
      (R : ℤ) = rank N (source a dummy (shiftedStartMarker a (s : ZMod N)))
        (normalized digits) ∧ σ 2 R = 3*(width*N)+2 ∧
      R%4 = 3 ∧ R=2*r+1 ∧ 2*(width*N)<R := by
  obtain ⟨R,hR,hpop⟩ := packing_rank_population a dummy s k digits hf
  have hC := hf.scalars.source_pos
  have hb := hf.scalars.balance
  have ha := hf.scalars.alpha_pos
  have hCF : source a dummy (shiftedStartMarker a (s : ZMod N))+
      normalized digits < q N := by omega
  have he : R = fourBlocks N (source a dummy (shiftedStartMarker a (s : ZMod N)))
      (normalized digits) := by
    apply Int.ofNat.inj
    exact hR.trans (fourBlocks_cast _ _ hC hCF).symm
  have hmod : R%4 = 3 := by rw [he]; exact fourBlocks_mod_four _ _ hf.low_mask
  have hbound := rank_gt_twice_window _ _ hC hCF
  rw [← hR] at hbound
  have hn : 2*(width*N)<R := by exact_mod_cast hbound
  exact ⟨R,R/2,hR,hpop,hmod,by omega,hn⟩

end DiophantineConsistency.CurrentPackingParity2011
