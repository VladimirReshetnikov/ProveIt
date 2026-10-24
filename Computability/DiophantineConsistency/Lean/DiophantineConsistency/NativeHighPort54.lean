import DiophantineConsistency.NativeCleanBands54
import DiophantineConsistency.NativeSourceOrigin54
import DiophantineConsistency.NativeWordPopulation

/-! # The exact compact54 high mask and its repeated radix digits -/

namespace DiophantineConsistency.NativeHighPort54

open NativeCyclicConvolution NativeRadixDigits NativeVariableMask
  NativeStencil54 NativeClause54 NativeMaskPopulation NativeSourceMask
  NativeSparseDigits54 NativeBinaryScale
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- All31 nonzero mask digits, including the population padding. -/
def entries : List (ℕ × ℕ) :=
  [(0,4),(2409,clauseMask),(3015,clauseMask)] ++
  ((List.range 10).map fun j => (528+j,1)) ++
  ((List.range 11).map fun j => (585+j,1)) ++
  [(1203,1),(1807,1)] ++
  ((List.range 4).map fun j => (4823+j,2^87-1)) ++ [(4827,2^38-1)]

theorem entries_length : entries.length = 31 := by decide

def position (i : Fin 31) : ℕ := entries[i.val].1
def coefficient (i : Fin 31) : ℕ := entries[i.val].2

theorem position_injective : Function.Injective position := by decide

theorem position_lt (i : Fin 31) : position i < cellLength := by
  have h : ∀ i : Fin 31, position i < cellLength := by decide
  exact h i

theorem coefficient_lt (i : Fin 31) : coefficient i < radix - 1 := by
  have h : ∀ i : Fin 31, coefficient i < radix - 1 := by decide
  exact h i

def cellDigit (j : ℕ) : ℕ := ∑ i : Fin 31, if position i = j then coefficient i else 0

/-- A short symbolic native MF port; the fourth source port adds beta once. -/
def highPort (r : ℕ) : ℕ := ∑ i : Fin 31, coefficient i * r ^ position i

theorem cellDigit_at (i : Fin 31) : cellDigit (position i) = coefficient i := by
  simp [cellDigit, position_injective.eq_iff]

theorem cellDigit_lt (j : ℕ) : cellDigit j < radix - 1 := by
  classical
  by_cases he : ∃ i, position i = j
  · obtain ⟨i, rfl⟩ := he
    rw [cellDigit_at]
    exact coefficient_lt i
  · have hz : cellDigit j = 0 := by
      simp only [cellDigit]
      apply Finset.sum_eq_zero
      intro i _
      exact if_neg (fun hi => he ⟨i,hi⟩)
    rw [hz]
    decide

theorem cellDigit_zero : cellDigit 0 = 4 := cellDigit_at ⟨0,by decide⟩
theorem cellDigit_left : cellDigit 2409 = clauseMask := cellDigit_at ⟨1,by decide⟩
theorem cellDigit_right : cellDigit 3015 = clauseMask := cellDigit_at ⟨2,by decide⟩

theorem cell_sum (r : ℕ) :
    (∑ j ∈ Finset.range cellLength, cellDigit j * r ^ j) = highPort r := by
  classical
  simp only [cellDigit, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_range,
    if_pos (position_lt i)]

def geometric (r m : ℕ) : ℕ := ∑ j ∈ Finset.range m, r ^ j

private theorem block_sum (r a m c : ℕ) :
    ((List.range m).map fun j => c * r ^ (a+j)).sum = c * r ^ a * geometric r m := by
  rw [← List.sum_toFinset _ (show (List.range m).Nodup from List.nodup_range)]
  simp only [List.toFinset_range, pow_add, ← mul_assoc, ← Finset.mul_sum]
  rfl

/-- The exact one-page native MF recipe, before the source adds beta. -/
theorem highPort_recipe (r : ℕ) : highPort r =
    4 + clauseMask * (r^2409+r^3015) +
      r^528 * geometric r 10 + r^585 * geometric r 11 + r^1203+r^1807 +
      (2^87-1)*r^4823*geometric r 4 + (2^38-1)*r^4827 := by
  rw [highPort, ← Fin.sum_ofFn]
  change (List.ofFn (fun i : Fin entries.length => entries[i.val].2 * r^entries[i.val].1)).sum = _
  rw [List.ofFn_getElem_eq_map entries (fun p => p.2*r^p.1)]
  simp only [entries,List.map_append,List.sum_append,List.map_cons,List.sum_cons,
    List.map_nil,List.sum_nil,List.map_map,Function.comp_def,pow_zero,mul_one,add_zero]
  rw [block_sum r 528 10 1, block_sum r 585 11 1, block_sum r 4823 4 (2^87-1)]
  ring

/-- The one-cell word is exactly the symbolic high port. -/
theorem word_cell :
    letI : NeZero cellLength := ⟨by decide⟩
    word radix (fun k : ZMod cellLength => cellDigit k.val) = highPort radix := by
  letI : NeZero cellLength := ⟨by decide⟩
  rw [word_eq_ofDigits, Jones1982.ofDigits_ofFn]
  simp only [finEquiv_val]
  rw [Fin.sum_univ_eq_sum_range (fun j => cellDigit j * radix ^ j) cellLength,cell_sum]

theorem highPort_lt : highPort radix < radix ^ cellLength - 1 := by
  letI : NeZero cellLength := ⟨by decide⟩
  have hh := word_lt_mersenne (by decide : 1 < radix)
    (fun k : ZMod cellLength => cellDigit k.val) (fun k => cellDigit_lt k.val)
  rwa [word_cell] at hh

theorem highPort_mod_radix : highPort radix % radix = 4 := by
  letI : NeZero cellLength := ⟨by decide⟩
  rw [← word_cell, NativeSourceOrigin54.word_mod_radix, ZMod.val_zero, cellDigit_zero]
  decide

theorem highPort_mod_eight : highPort radix % 8 = 4 := by
  have he : highPort radix ≡ 4 [MOD radix] := by
    change highPort radix % radix = 4 % radix
    rw [highPort_mod_radix]
    decide
  have hh := he.of_dvd (show 8 ∣ radix from pow_dvd_pow 2 (by decide : 3 ≤ 89))
  exact hh

/-- Exact binary population, using an injective31-position sparse table. -/
theorem highPort_population : Jones1982.σ 2 (highPort radix) = 520 := by
  classical
  letI : NeZero cellLength := ⟨by decide⟩
  let p : Fin 31 → ZMod cellLength := fun i => (position i : ZMod cellLength)
  have hp : Function.Injective p := by
    intro i j hij
    apply position_injective
    have hh := congrArg ZMod.val hij
    simpa only [p,ZMod.val_natCast,Nat.mod_eq_of_lt (position_lt i),
      Nat.mod_eq_of_lt (position_lt j)] using hh
  have he : (fun k : ZMod cellLength => ∑ i : Fin 31, if p i = k then coefficient i else 0) =
      (fun k => cellDigit k.val) := by
    funext k
    apply Finset.sum_congr rfl
    intro i _
    have hk : p i = k ↔ position i = k.val := by
      constructor
      · intro hh
        have hv := congrArg ZMod.val hh
        simpa only [p,ZMod.val_natCast,Nat.mod_eq_of_lt (position_lt i)] using hv
      · intro hh
        apply ZMod.val_injective
        simpa only [p,ZMod.val_natCast,Nat.mod_eq_of_lt (position_lt i)] using hh
    simp only [hk]
  have hpop := NativeWordPopulation.sparse_population 89 p hp coefficient
    (fun i => lt_of_lt_of_le (coefficient_lt i) (Nat.sub_le _ _))
  rw [he] at hpop
  change Jones1982.σ 2 (word radix (fun k : ZMod cellLength => cellDigit k.val)) = _ at hpop
  rw [word_cell] at hpop
  apply hpop.trans
  decide

variable {N : ℕ} [NeZero (N * cellLength)]

/-- The final subtraction is one unit at the origin; it causes no borrow. -/
def maskDigits (k : ZMod (N * cellLength)) : ℕ :=
  cellDigit (k.val % cellLength) - if k = 0 then 1 else 0

omit [NeZero (N * cellLength)] in
theorem maskDigits_lt (k : ZMod (N * cellLength)) : maskDigits k < radix := by
  have h := cellDigit_lt (k.val % cellLength)
  unfold maskDigits
  omega

omit [NeZero (N * cellLength)] in
theorem maskDigits_left (k : ZMod (N * cellLength))
    (hk : k.val % cellLength = 2409) : maskDigits k = clauseMask := by
  have hk0 : k ≠ 0 := by intro he; subst k; simp at hk
  simp only [maskDigits,hk,hk0,if_false,Nat.sub_zero,cellDigit_left]

omit [NeZero (N * cellLength)] in
theorem maskDigits_right (k : ZMod (N * cellLength))
    (hk : k.val % cellLength = 3015) : maskDigits k = clauseMask := by
  have hk0 : k ≠ 0 := by intro he; subst k; simp at hk
  simp only [maskDigits,hk,hk0,if_false,Nat.sub_zero,cellDigit_right]

/-- The complete repeated high-mask word, including origin decrement. -/
theorem mask_word :
    word radix (maskDigits (N := N)) = highPort radix * repunit (89 * cellLength) N - 1 := by
  have he : (fun k : ZMod (N * cellLength) =>
      maskDigits k + if k = 0 then 1 else 0) =
      (fun k => cellDigit (k.val % cellLength)) := by
    funext k
    by_cases hk : k = 0
    · subst k
      simp [maskDigits,cellDigit_zero]
    · simp [maskDigits,hk]
  have hw := congrArg (word radix) he
  rw [word_add,word_origin] at hw
  have hp := word_periodic (N := N) radix (by decide : 0 < cellLength)
    (fun j : Fin cellLength => cellDigit j.val)
  change word radix (fun k : ZMod (N * cellLength) => cellDigit (k.val % cellLength)) = _ at hp
  rw [hp] at hw
  rw [Fin.sum_univ_eq_sum_range (fun j => cellDigit j * radix ^ j) cellLength,
    cell_sum,show (∑ k : Fin N, (radix ^ cellLength) ^ k.val) =
      repunit (89 * cellLength) N from periodic_factor 89 cellLength N] at hw
  omega

/-- Both actual clause-mask tests follow from the literal source. The
high-mask word and its digit bound are now proved rather than supplied. -/
theorem source_clause_masks (ports : Fin 4 → ℤ)
    (h : Interface ports (89 * cellLength) NativeLowPort54.lowPort (highPort radix))
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0)
    (hq : sourceQ ports x = (2 ^ (89 * cellLength)) ^ N)
    (hK : (ports 1).toNat = rawWord radix) :
    ∃ c : ZMod (N * cellLength) → ℕ,
      word radix c = gap ports x ∧ c 0 = 1 ∧
      (∀ k, c k < 2 ^ periodicBits k) ∧
      (∀ k, k.val % cellLength = 2409 →
        (NativeCleanBands54.localContribution c k 2409 +
          NativeWindowConvolution54.temporalDigits x c k) &&& clauseMask = 0) ∧
      (∀ k, k.val % cellLength = 3015 →
        (NativeCleanBands54.localContribution c k 3015 +
          NativeWindowConvolution54.temporalDigits x c k) &&& clauseMask = 0) := by
  have hJ := source_J_eq_repunit ports (by decide : 0 < 89 * cellLength) h.beta x hq
  obtain ⟨c,hC,h0,hbits,hleft,hright⟩ := NativeCleanBands54.source_clean_bands
    ports h x hx hs hq hK (maskDigits (N := N)) maskDigits_lt (by rw [mask_word,← hJ])
  refine ⟨c,hC,h0,hbits,?_,?_⟩
  · intro k hk
    simpa only [maskDigits_left k hk] using hleft k hk
  · intro k hk
    simpa only [maskDigits_right k hk] using hright k hk

end DiophantineConsistency.NativeHighPort54
