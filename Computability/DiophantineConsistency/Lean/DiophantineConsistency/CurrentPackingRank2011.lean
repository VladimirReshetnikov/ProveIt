import DiophantineConsistency.CurrentNativePacking2011
import DiophantineConsistency.NativePackingPopulation
import DiophantineConsistency.NativeRankVariation

/-! Exact population of the actual constructed rank, before Pell witnesses.
The source high-mask port contains its beta shift exactly once. -/

namespace DiophantineConsistency.CurrentPackingRank2011

open Jones1982 CurrentMasks2011 CurrentWordScalarWitness2011
  CurrentWordConstruction2011 CurrentWordCopies2011 NativeMaskPopulation

set_option Elab.async false
set_option maxRecDepth 10000

theorem q_binary (N : ℕ) : q N = 2^(width*N) := by
  unfold q radix width
  rw [← pow_mul]
  congr 1
  ring

/-- The rank uses the actual once-shifted fourth source port. -/
def rank (N C F : ℕ) : ℤ :=
  NativeRankVariation.windowRank (q N : ℤ) C F lowPort (highPort+beta : ℕ)
    (repunit width N)

def fourBlocks (N C F : ℕ) : ℕ :=
  (C-1)+(lowPort*repunit width N+1)+q N*(F+(highPort*repunit width N-1))+
    q N^2*(q N-C)+q N^3*(q N-F-1)

variable {N : ℕ} [NeZero N]

theorem repeated_mask_bounds :
    lowPort*repunit width N+1 < q N ∧ highPort*repunit width N-1 < q N := by
  have hJ := CurrentNativePacking2011.repunit_pos (N:=N)
  have hb := CurrentNativePacking2011.repunit_balance (N:=N)
  have hL := Nat.mul_lt_mul_of_pos_right lowPort_lt hJ
  have hH := Nat.mul_lt_mul_of_pos_right highPort_lt hJ
  omega

theorem repeated_mask_population :
    σ 2 (lowPort*repunit width N+1)+σ 2 (highPort*repunit width N-1) = width*N+2 := by
  have hL : lowPort < radix^2011 := by have := lowPort_lt; unfold beta at this; omega
  have hH : highPort < radix^2011 := by have := highPort_lt; unfold beta at this; omega
  have hLB : lowPort < 2^width := by simpa only [radix,width,pow_mul] using hL
  have hHB : highPort < 2^width := by simpa only [radix,width,pow_mul] using hH
  exact repeated_native_mask_population (by decide) (NeZero.pos N)
    hLB hHB lowPort_even highPort_four population

/-- Ordinary integer binding is proved after every natural subtraction's domain. -/
theorem fourBlocks_cast (C F : ℕ) (hC : 0<C) (hCF : C+F<q N) :
    (fourBlocks N C F : ℤ) = rank N C F := by
  have hJ := CurrentNativePacking2011.repunit_pos (N:=N)
  have hHJ : 1 ≤ highPort*repunit width N := Nat.mul_pos highPort_pos hJ
  have hCq : C ≤ q N := by omega
  have hFq : F+1 ≤ q N := by omega
  have hb := congrArg (fun n : ℕ => (n : ℤ))
    (CurrentNativePacking2011.repunit_balance (N:=N))
  push_cast at hb
  have hbeta : (beta : ℤ)*repunit width N = (q N : ℤ)-1 := by omega
  have hh := NativeSourceMask.packing_four_block (C:=(C:ℤ)) (F:=(F:ℤ))
    (MC:=(lowPort:ℤ)) (MF:=(highPort:ℤ)) hbeta
  have hB : (fourBlocks N C F : ℤ) =
      ((C : ℤ)-1)+((lowPort : ℤ)*repunit width N+1)+
      (q N : ℤ)*(F+((highPort : ℤ)*repunit width N-1))+
      (q N : ℤ)^2*((q N : ℤ)-C)+(q N : ℤ)^3*((q N : ℤ)-F-1) := by
    unfold fourBlocks
    push_cast [Nat.cast_sub (by omega : 1 ≤ C),Nat.cast_sub hHJ,
      Nat.cast_sub hCq,Nat.cast_sub (by omega : 1 ≤ q N-F),
      Nat.cast_sub (by omega : F ≤ q N)]
    ring
  rw [hB,← hh]
  unfold rank NativeRankVariation.windowRank
  push_cast
  ring

omit [NeZero N] in
/-- The positive complement in the top block supplies a large rank before
any population or Pell premise is used. -/
theorem fourBlocks_ge_cube (C F : ℕ) (hC : 0<C) (hCF : C+F<q N) :
    q N^3 ≤ fourBlocks N C F := by
  have ht : 1 ≤ q N-F-1 := by omega
  have hm := Nat.mul_le_mul_left (q N^3) ht
  simp only [Nat.mul_one] at hm
  unfold fourBlocks
  omega

theorem rank_gt_twice_window (C F : ℕ) (hC : 0<C) (hCF : C+F<q N) :
    (2*(width*N) : ℕ) < rank N C F := by
  have hu : width*N < q N := by rw [q_binary]; exact Nat.lt_two_pow_self
  have hw : 0 < width*N := Nat.mul_pos (by decide) (NeZero.pos N)
  have hq : 2 ≤ q N := by omega
  have hsq : 2 ≤ q N^2 := by nlinarith
  have hc : 2*(width*N) < q N^3 := by
    calc
      2*(width*N) < 2*q N := Nat.mul_lt_mul_of_pos_left hu (by decide)
      _ ≤ q N^3 := by rw [pow_succ]; exact Nat.mul_le_mul_right (q N) hsq
  have hn := hc.trans_le (fourBlocks_ge_cube C F hC hCF)
  have hz : ((2*(width*N) : ℕ) : ℤ) < (fourBlocks N C F : ℤ) := by exact_mod_cast hn
  rwa [fourBlocks_cast C F hC hCF] at hz

theorem fourBlocks_population (C F : ℕ) (hC : 0<C) (hCF : C+F<q N)
    (hmC : (C-1) &&& (lowPort*repunit width N+1) = 0)
    (hmF : F &&& (highPort*repunit width N-1) = 0) :
    σ 2 (fourBlocks N C F) = 3*(width*N)+2 := by
  obtain ⟨hM,hH⟩ := repeated_mask_bounds (N:=N)
  have hA : C-1 < q N := by omega
  have hF : F < q N := by omega
  have hh := NativePackingPopulation.calibrated_population
    (u:=width*N) (A:=C-1) (F:=F)
    (M:=lowPort*repunit width N+1) (H:=highPort*repunit width N-1)
    (by simpa only [q_binary] using hA)
    (by simpa only [q_binary] using hF)
    (by simpa only [q_binary] using hM)
    (by simpa only [q_binary] using hH)
    hmC hmF repeated_mask_population
  have he : q N-1-(C-1) = q N-C := by omega
  rw [← q_binary,he] at hh
  simpa only [fourBlocks,Nat.sub_sub,Nat.add_comm 1 F] using hh

/-- The same constructed packing has the exact population required by the
remaining Pell construction. No source-system zero or population is assumed. -/
theorem packing_rank_population (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (s : ℕ) (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentNativePacking2011.Facts a dummy s k digits) :
    ∃ R : ℕ,
      (R : ℤ) = rank N (source a dummy (shiftedStartMarker a (s : ZMod N)))
        (normalized digits) ∧ σ 2 R = 3*(width*N)+2 := by
  have hC := hf.scalars.source_pos
  have hb := hf.scalars.balance
  have ha := hf.scalars.alpha_pos
  have hCF : source a dummy (shiftedStartMarker a (s : ZMod N))+
      normalized digits < q N := by omega
  refine ⟨fourBlocks N (source a dummy (shiftedStartMarker a (s : ZMod N)))
    (normalized digits),fourBlocks_cast _ _ hC hCF,?_⟩
  exact fourBlocks_population _ _ hC hCF hf.low_mask hf.high_mask

end DiophantineConsistency.CurrentPackingRank2011
