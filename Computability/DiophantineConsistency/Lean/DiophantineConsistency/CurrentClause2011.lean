import DiophantineConsistency.CurrentKernel2011
import DiophantineConsistency.CurrentSparseDigits2011
import DiophantineConsistency.CurrentHighDigits2011
import DiophantineConsistency.WangTiles942Permutation
import DiophantineConsistency.NativePreliminaryCount2011

/-!
# The literal current clause, before count or alignment recovery

Periodic support kills the two unwanted bare inputs at field1005. Every
reflected summand is retained, including coefficient collisions. The low
clause residue counts the actual942 physical selectors; no decoded labels,
one-selector bound, zero incoming carry or temporal alignment is assumed.
-/

namespace DiophantineConsistency.CurrentClause2011

open NativeCyclicConvolution CurrentMasks2011 WangTiles942
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

variable {N : ℕ} [NeZero (N * 2011)]

theorem addition_residue (b : ZMod (N * 2011)) (e : ℕ) :
    (b + (e : ZMod (N * 2011))).val % 2011 = (b.val + e) % 2011 := by
  have hh : (((b + (e : ZMod (N * 2011))).val : ℕ) : ZMod (N * 2011)) =
      ((b.val + e : ℕ) : ZMod (N * 2011)) := by
    simp only [Nat.cast_add, ZMod.natCast_zmod_val]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hh).of_dvd ⟨N, by ring⟩

theorem subtraction_residue (k : ZMod (N * 2011)) (e : ℕ) :
    ((k - (e : ZMod (N * 2011))).val + e) % 2011 = k.val % 2011 := by
  have hh : (((k - (e : ZMod (N * 2011))).val + e : ℕ) : ZMod (N * 2011)) =
      (k.val : ZMod (N * 2011)) := by
    simp only [Nat.cast_add, ZMod.natCast_zmod_val, sub_add_cancel]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hh).of_dvd ⟨N, by ring⟩

theorem clause_target_residue (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    (b + (1005 : ZMod (N * 2011))).val % 2011 = 1005 := by
  rw [show (1005 : ZMod (N * 2011)) = ((1005 : ℕ) : ZMod (N * 2011)) from rfl,
    addition_residue, Nat.add_mod, hb]

theorem clause_mask (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    CurrentHighDigits2011.maskDigits (b + 1005) = 2 ^ 45 - 4 := by
  have hr := clause_target_residue b hb
  have hn : b + (1005 : ZMod (N * 2011)) ≠ 0 := by
    intro hz
    rw [hz, ZMod.val_zero, Nat.zero_mod] at hr
    contradiction
  rw [CurrentHighDigits2011.maskDigits_nonzero _ hn, hr,
    CurrentHighDigits2011.cellDigit_clause]

/-- The exact unnormalized clause receives the selector1 bare term and
the whole reflected coefficient sum, with no lost reflected collision. -/
theorem clause_convolution (c : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    convolution CurrentKernel2011.folded c (b + 1005) = c (b + 1) +
      ∑ e : CurrentKernel2011.Entry,
        2 * CurrentKernel2011.weight e * c (b + (CurrentKernel2011.position e : ZMod (N * 2011))) := by
  have hr := clause_target_residue b hb
  have he (e : ℕ) :
      (((b + 1005 - (e : ZMod (N * 2011))).val % 2011) + e) % 2011 = 1005 := by
    have hh := (subtraction_residue (b + 1005) e).trans hr
    simpa only [Nat.add_mod, Nat.mod_mod] using hh
  have h18 : (b + 1005 - 18).val % 2011 = 987 := by
    have hh := he 18
    norm_num only [Nat.cast_ofNat] at hh
    have hl := Nat.mod_lt (b + 1005 - 18).val (by decide : 0 < 2011)
    omega
  have h2020 : (b + 1005 - 2020).val % 2011 = 996 := by
    have hh := he 2020
    norm_num only [Nat.cast_ofNat] at hh
    have hl := Nat.mod_lt (b + 1005 - 2020).val (by decide : 0 < 2011)
    omega
  have hz18 : c (b + 1005 - 18) = 0 := by
    apply hc
    rw [h18]
    simp only [lowSupport_def, Finset.mem_union, Finset.mem_range,
      Finset.mem_Ico, Finset.mem_singleton]
    omega
  have hz2020 : c (b + 1005 - 2020) = 0 := by
    apply hc
    rw [h2020]
    simp only [lowSupport_def, Finset.mem_union, Finset.mem_range,
      Finset.mem_Ico, Finset.mem_singleton]
    omega
  rw [CurrentKernel2011.convolution_eq, hz18, hz2020, zero_add, add_zero,
    show b + 1005 - (1004 : ZMod (N * 2011)) = b + 1 by ring]
  apply congrArg (fun z : ℕ => c (b + 1) + z)
  apply Finset.sum_congr rfl
  intro e _
  have hp : CurrentKernel2011.position e ≤ 1005 :=
    (CurrentKernel2011.position_le e).trans (by decide)
  have hidx : b + 1005 - ((1005 - CurrentKernel2011.position e : ℕ) : ZMod (N * 2011)) =
      b + (CurrentKernel2011.position e : ZMod (N * 2011)) := by
    rw [Nat.cast_sub hp]
    ring
  rw [hidx]

def selectorCount (c : ZMod (N * 2011) → ℕ) (b : ZMod (N * 2011)) : ℕ :=
  ∑ i : Fin 942, c (b + (physicalPosition i : ZMod (N * 2011)))

omit [NeZero (N * 2011)] in
/-- This is the count of all physical selector fields, by the proved actual
floor-rank bijection, rather than a supplied sorting permutation. -/
theorem selectorCount_eq_prefix (c : ZMod (N * 2011) → ℕ) (b : ZMod (N * 2011)) :
    selectorCount c b = PaddingStaircase.prefixSum (fun j => c (b + (j : ZMod (N * 2011)))) 942 := by
  have he := Equiv.sum_comp physicalEquiv
    (fun p : Fin 942 => c (b + (p.val : ZMod (N * 2011))))
  change selectorCount c b = ∑ p : Fin 942, c (b + (p.val : ZMod (N * 2011))) at he
  rw [he, PaddingStaircase.prefixSum]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => c (b + (j : ZMod (N * 2011)))) 942

private def selectorUnit : CurrentKernel2011.Entry → ℕ
  | .inl _ => 2
  | .inr _ => 0

theorem reflected_weight_mod (e : CurrentKernel2011.Entry) :
    2 * CurrentKernel2011.weight e ≡ selectorUnit e [MOD 2048] := by
  rcases e with i | j | j | j | j
  · change (2 * selectorWeight (tile i)) % 2048 = 2 % 2048
    simp only [selectorWeight]
    omega
  all_goals
    change (2 * 2 ^ _) % 2048 = 0 % 2048
    fin_cases j <;> decide

/-- Every reflected label weight is0 modulo2048; every reflected selector
weight is2. Its exact low residue is available before label decoding. -/
theorem clause_low_residue (c : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    convolution CurrentKernel2011.folded c (b + 1005) ≡
      2 * selectorCount c b + c (b + 1) [MOD 2048] := by
  have hs := Nat.ModEq.sum (s := Finset.univ) (fun e _ =>
    (reflected_weight_mod e).mul_right (c (b + (CurrentKernel2011.position e : ZMod (N * 2011)))))
  have hu : (∑ e : CurrentKernel2011.Entry,
      selectorUnit e * c (b + (CurrentKernel2011.position e : ZMod (N * 2011)))) =
      2 * selectorCount c b := by
    simp only [Fintype.sum_sum_type, selectorUnit, zero_mul, Finset.sum_const_zero,
      add_zero, selectorCount, CurrentKernel2011.position, Finset.mul_sum]
  rw [hu] at hs
  rw [clause_convolution c hc b hb]
  simpa only [Nat.add_comm] using hs.add_left (c (b + 1))

/-- The actual normalized clause keeps its bounded incoming carry and
unaligned temporal digit. Reduction by the radix loses neither low term. -/
theorem normalized_clause_residue
    (c r carry digits : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (hlocal : ∀ k, convolution CurrentKernel2011.folded c k + r k + carry (k - 1) =
      digits k + radix * carry k)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    digits (b + 1005) % 2048 =
      (2 * selectorCount c b + carry (b + 1004) + c (b + 1) + r (b + 1005)) % 2048 := by
  have hm : digits (b + 1005) ≡
      convolution CurrentKernel2011.folded c (b + 1005) + r (b + 1005) +
        carry (b + 1005 - 1) [MOD 2048] := by
    change _ % 2048 = _ % 2048
    rw [hlocal]
    simp only [Nat.add_mod, Nat.mul_mod, show radix % 2048 = 0 from by decide,
      Nat.zero_mul, Nat.zero_mod, add_zero, Nat.mod_mod]
  have hh := hm.trans (((clause_low_residue c hc b hb).add_right (r (b + 1005))).add_right
    (carry (b + 1005 - 1)))
  have hp : b + (1005 : ZMod (N * 2011)) - 1 = b + 1004 := by ring
  have he : 2 * selectorCount c b + c (b + 1) + r (b + 1005) +
      carry (b + 1005 - 1) =
      2 * selectorCount c b + carry (b + 1004) + c (b + 1) + r (b + 1005) := by
    rw [hp]
    omega
  rw [he] at hh
  exact hh

theorem normalized_clause_mask (digits : ZMod (N * 2011) → ℕ)
    (hm : ∀ k, digits k &&& CurrentHighDigits2011.maskDigits k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    digits (b + 1005) &&& (2 ^ 45 - 4) = 0 := by
  simpa only [clause_mask b hb] using hm (b + 1005)

end DiophantineConsistency.CurrentClause2011
