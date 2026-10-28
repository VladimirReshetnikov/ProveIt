import DiophantineConsistency.CurrentDummyMutation2011
import DiophantineConsistency.CurrentWordTopBounds2011

/-!
# A sufficient physical safety bound for one actual dummy update

Only the two canonical position inequalities are assumed. A coarse bound on
the complete literal kernel is enough; no coefficient-collision enumeration
or high-mask premise is needed. The old normalized word remains the original
one throughout the ordinary transport and rank equalities.
-/

namespace DiophantineConsistency.CurrentDummySafety2011

open CurrentMasks2011 CurrentWordConstruction2011 CurrentWordClause2011
  CurrentDummyMutation2011 NativeRankVariation
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

theorem kernel_exponent_le (t : CurrentKernel2011.Term) :
    CurrentKernel2011.exponent t ≤ 2020 := by
  rcases t with j | e
  · fin_cases j <;> decide
  · change 1005-CurrentKernel2011.position e ≤ 2020
    omega

private theorem weighted_powers_le {α : Type*} [Fintype α]
    (ρ : ℕ) (c e : α → ℕ) (L : ℕ) (hρ : 1 ≤ ρ) (he : ∀ i, e i ≤ L) :
    (∑ i, c i*ρ^(e i)) ≤ (∑ i, c i)*ρ^L := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hρ (he i))

/-- The actual total coefficient mass is tiny relative to radix squared. -/
theorem kernel_upper_bound : CurrentKernel2011.K < radix^2022 := by
  have h := weighted_powers_le radix CurrentKernel2011.coefficient
    CurrentKernel2011.exponent 2020 (by decide) kernel_exponent_le
  rw [CurrentKernel2011.coefficient_mass] at h
  change CurrentKernel2011.K ≤ 7659829036801887*radix^2020 at h
  calc
    CurrentKernel2011.K ≤ 7659829036801887*radix^2020 := h
    _ < radix^2*radix^2020 :=
      Nat.mul_lt_mul_of_pos_right (by decide) (pow_pos (by decide) _)
    _ = radix^2022 := by rw [← pow_add]

attribute [local irreducible] CurrentKernel2011.K

theorem displacement_power (s : ℕ) : 2^(displacement s) = radix^(2011*s) := by
  unfold displacement CurrentMasks2011.radix
  rw [pow_mul]

theorem dummyIncrement_power {N : ℕ} (j : ZMod N) :
    dummyIncrement j = radix^(977+2011*j.val) := by
  rw [dummyIncrement, ← pow_mul, ← pow_add]

theorem temporal_dummy_power {N : ℕ} (s : ℕ) (j : ZMod N) :
    2^(displacement s)*dummyIncrement j = radix^(977+2011*(j.val+s)) := by
  rw [displacement_power, dummyIncrement_power, ← pow_add]
  congr 1
  omega

theorem kernel_dummy_bound {N : ℕ} (j : ZMod N) :
    CurrentKernel2011.K*dummyIncrement j < radix^(2999+2011*j.val) := by
  rw [dummyIncrement_power]
  calc
    CurrentKernel2011.K*radix^(977+2011*j.val) <
        radix^2022*radix^(977+2011*j.val) :=
      Nat.mul_lt_mul_of_pos_right kernel_upper_bound (pow_pos (by decide) _)
    _ = radix^(2999+2011*j.val) := by rw [← pow_add]; congr 1; omega

/-- These inequalities use the actual canonical cell representative.
They allow stride zero but exclude a one-cell modulus or a final-cell update. -/
theorem safe_exponent_bounds {N : ℕ} (s : ℕ) (j : ZMod N)
    (hnext : j.val+1 < N) (htime : j.val+s < N) :
    4022 ≤ N*2011 ∧ 2999+2011*j.val ≤ N*2011-1023 ∧
      977+2011*(j.val+s) ≤ N*2011-1034 := by
  omega

/-- A positive ordinary increment with two whole high fields to spare.
This numerical result does not assume a word, Boolean controls, or carries. -/
theorem safe_increment_bound {N : ℕ} (s : ℕ) (j : ZMod N)
    (hnext : j.val+1 < N) (htime : j.val+s < N) :
    0 < (CurrentKernel2011.K+2^(displacement s))*dummyIncrement j ∧
      (CurrentKernel2011.K+2^(displacement s))*dummyIncrement j < radix^(N*2011-2) := by
  obtain ⟨hm,hkexp,htexp⟩ := safe_exponent_bounds s j hnext htime
  have hbase : 1 ≤ radix := by decide
  have hk : CurrentKernel2011.K*dummyIncrement j < radix^(N*2011-3) :=
    (kernel_dummy_bound j).trans_le
      (Nat.pow_le_pow_right hbase (by omega))
  have ht : 2^(displacement s)*dummyIncrement j ≤ radix^(N*2011-3) := by
    rw [temporal_dummy_power]
    exact Nat.pow_le_pow_right hbase (by omega)
  constructor
  · have hp : 0 < 2^(displacement s) := pow_pos (by decide) _
    exact Nat.mul_pos (by omega) (dummyIncrement_pos j)
  · rw [Nat.add_mul]
    calc
      CurrentKernel2011.K*dummyIncrement j+2^(displacement s)*dummyIncrement j <
          2*radix^(N*2011-3) := by omega
      _ ≤ radix^(N*2011-2) := by
        have he : N*2011-2 = (N*2011-3)+1 := by omega
        rw [he,pow_succ]
        simpa only [Nat.mul_comm] using
          Nat.mul_le_mul_right (radix^(N*2011-3)) (by decide : 2 ≤ radix)

/-- The same bound expressed with the actual whole-word quotient. -/
theorem safe_increment_div_bound {N : ℕ} (s : ℕ) (j : ZMod N)
    (hnext : j.val+1 < N) (htime : j.val+s < N) :
    (CurrentKernel2011.K+2^(displacement s))*dummyIncrement j < radix^(N*2011)/radix^2 := by
  have hm := (safe_exponent_bounds s j hnext htime).1
  have he : N*2011 = (N*2011-2)+2 := by omega
  have hq : radix^(N*2011)/radix^2 = radix^(N*2011-2) := by
    conv_lhs => rw [he,pow_add]
    exact Nat.mul_div_cancel _ (pow_pos (by decide) _)
  rw [hq]
  exact (safe_increment_bound s j hnext htime).2

private theorem nonwrap_of_short {ρ m F δ : ℕ} (hρ : 2 ≤ ρ) (hm : 2 ≤ m)
    (hF : F < ρ^(m-1)) (hδ : δ < ρ^(m-2)) : F+δ < ρ^m-1 := by
  have hδ' := hδ.trans_le (Nat.pow_le_pow_right
    (by omega : 1 ≤ ρ) (by omega : m-2 ≤ m-1))
  have hcapacity := Nat.mul_le_mul_right (ρ^(m-1)) hρ
  have he : ρ*ρ^(m-1) = ρ^m := by
    rw [← pow_succ']; congr 1; omega
  rw [he] at hcapacity
  omega

variable {N : ℕ} [NeZero N]

/-- Discharge the mutation's nonwrapping premise for the original actual F. -/
theorem normalized_nonwrap_of_safe (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ i, dummy i ≤ 1) (hm : ∀ i, marker i ≤ 1) (s : ℕ)
    (j : ZMod N) (hnext : j.val+1 < N) (htime : j.val+s < N)
    (carry digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) carry digits) :
    NativeCyclicConvolution.word radix digits+
      (CurrentKernel2011.K+2^(displacement s))*dummyIncrement j < radix^(N*2011)-1 := by
  exact nonwrap_of_short (by decide)
    (by have := (safe_exponent_bounds s j hnext htime).1; omega)
    (CurrentWordTopBounds2011.normalized_word_top_bound a dummy marker hd hm s carry digits hf)
    (safe_increment_bound s j hnext htime).2

/-- Any two actual normalizations give the exact ordinary F increment at
a safe unused dummy; no nonwrapping bound is supplied. -/
theorem safe_normalized_increment (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ i, dummy i ≤ 1) (hm : ∀ i, marker i ≤ 1) (s : ℕ)
    (j : ZMod N) (hj : dummy j = 0) (hnext : j.val+1 < N) (htime : j.val+s < N)
    (carry digits carry' digits' : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) carry digits)
    (hf' : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a (Function.update dummy j 1) marker)
        (displacement s) carry' digits') :
    NativeCyclicConvolution.word radix digits' = NativeCyclicConvolution.word radix digits+
      (CurrentKernel2011.K+2^(displacement s))*dummyIncrement j :=
  normalized_increment a dummy marker hd hm s j hj carry digits carry' digits' hf hf'
    (normalized_nonwrap_of_safe a dummy marker hd hm s j hnext htime carry digits hf)

/-- Construct the new normalization and retain both ordinary word equalities. -/
theorem exists_safe_normalized_increment (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ i, dummy i ≤ 1) (hm : ∀ i, marker i ≤ 1) (s : ℕ)
    (j : ZMod N) (hj : dummy j = 0) (hnext : j.val+1 < N) (htime : j.val+s < N)
    (carry digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) carry digits) :
    ∃ carry' digits' : ZMod (N*2011) → ℕ,
      CurrentCarryConstruction2011.Facts
        (CurrentWordConstruction2011.word a (Function.update dummy j 1) marker)
          (displacement s) carry' digits' ∧
      NativeCyclicConvolution.word radix
          (CurrentWordConstruction2011.word a (Function.update dummy j 1) marker) =
        NativeCyclicConvolution.word radix (CurrentWordConstruction2011.word a dummy marker)+
          dummyIncrement j ∧
      NativeCyclicConvolution.word radix digits' = NativeCyclicConvolution.word radix digits+
        (CurrentKernel2011.K+2^(displacement s))*dummyIncrement j := by
  obtain ⟨carry',digits',hf',he⟩ := exists_normalized_increment a dummy marker hd hm s j hj
    carry digits hf
      (normalized_nonwrap_of_safe a dummy marker hd hm s j hnext htime carry digits hf)
  exact ⟨carry',digits',hf',source_increment a dummy marker j hj,he⟩

/-- The actual rank decrement now needs physical position bounds in place
of the former ordinary nonwrapping hypothesis. -/
theorem safe_rank_decrement (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ i, dummy i ≤ 1) (hm : ∀ i, marker i ≤ 1) (s : ℕ)
    (j : ZMod N) (hj : dummy j = 0) (hnext : j.val+1 < N) (htime : j.val+s < N)
    (carry digits carry' digits' : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) carry digits)
    (hf' : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a (Function.update dummy j 1) marker)
        (displacement s) carry' digits') (MC MF J : ℤ) :
    windowRank (R := ℤ) (radix^(N*2011) : ℕ)
      (NativeCyclicConvolution.word radix
        (CurrentWordConstruction2011.word a (Function.update dummy j 1) marker))
      (NativeCyclicConvolution.word radix digits') MC MF J =
    windowRank (R := ℤ) (radix^(N*2011) : ℕ)
      (NativeCyclicConvolution.word radix (CurrentWordConstruction2011.word a dummy marker))
      (NativeCyclicConvolution.word radix digits) MC MF J-
        rankGamma (R := ℤ) (radix^(N*2011) : ℕ) (CurrentKernel2011.K+2^(displacement s) : ℕ)
          (radix^977 : ℕ)*(radix^2011 : ℤ)^j.val :=
  rank_decrement a dummy marker hd hm s j hj carry digits carry' digits' hf hf'
    (normalized_nonwrap_of_safe a dummy marker hd hm s j hnext htime carry digits hf) MC MF J

end DiophantineConsistency.CurrentDummySafety2011
