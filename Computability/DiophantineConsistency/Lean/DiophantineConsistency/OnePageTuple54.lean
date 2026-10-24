import DiophantineConsistency.OnePageModes54
import DiophantineConsistency.OnePageLowPort54

/-! # Symbolic binding of the one-page local coefficients and compact54 ports -/

namespace DiophantineConsistency.OnePageTuple54

open NativeClauseModes54 NativeModesData54 NativeLocalCoefficients54
open NativeClauseBits54 NativeStencil54 OnePageModes54
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- Natural form of the page equality indicator. Its signed-square form
agrees because all indices lie between zero and 456. -/
def delta (i j : Fin 457) : ℕ :=
  (Q - (Int.natAbs ((i.val : ℤ) - j.val)) ^ 2) / Q

theorem delta_eq (i j : Fin 457) : delta i j = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    norm_num [delta,Q]
  · have hd : Int.natAbs ((i.val : ℤ) - j.val) ≠ 0 := by
      intro hz
      have he := Int.natAbs_eq_zero.mp hz
      apply h
      exact Fin.ext (by omega)
    have hp : 0 < (Int.natAbs ((i.val : ℤ) - j.val)) ^ 2 :=
      pow_pos (Nat.pos_of_ne_zero hd) _
    have hlt : Q - (Int.natAbs ((i.val : ℤ) - j.val)) ^ 2 < Q :=
      Nat.sub_lt (by decide : 0 < Q) hp
    simpa only [delta,if_neg h] using Nat.div_eq_of_lt hlt

/-- The literal integer quotient used for equality on the page. -/
def integerDelta (i j : Fin 457) : ℤ :=
  ((Q : ℤ) - ((i.val : ℤ) - j.val)^2) / (Q : ℤ)

private theorem integerDelta_indicator (d : ℤ) (hlo : -456 ≤ d) (hhi : d ≤ 456) :
    ((Q : ℤ)-d^2)/(Q : ℤ) = if d=0 then 1 else 0 := by
  have hs : d^2 < (Q : ℤ) := by
    have hmul := mul_nonneg (show 0 ≤ 456-d by omega) (show 0 ≤ 456+d by omega)
    norm_num [Q]
    nlinarith
  by_cases h : d=0
  · subst d; norm_num [Q]
  · have hp := sq_pos_of_ne_zero h
    have hn0 : 0 ≤ (Q : ℤ)-d^2 := by omega
    have hn1 : (Q : ℤ)-d^2 < (Q : ℤ) := by omega
    simp only [if_neg h]
    unfold Q at *
    omega

theorem integerDelta_eq (i j : Fin 457) :
    integerDelta i j = if i=j then 1 else 0 := by
  rw [integerDelta,integerDelta_indicator _ (by omega) (by omega)]
  have he : (i.val : ℤ)-j.val=0 ↔ i=j := by
    constructor
    · intro h; exact Fin.ext (by omega)
    · intro h; subst j; omega
  simp only [he]

theorem integerDelta_cast (i j : Fin 457) : integerDelta i j = (delta i j : ℤ) := by
  rw [integerDelta_eq,delta_eq]
  split_ifs <;> rfl

private theorem flags (i : Fin 457) :
    rightFlag (unsortedMode i).2 = (if i=455 then 1 else 0) ∧
    leftFlag (unsortedMode i).2 = (if i=456 then 1 else 0) := by
  have h : List.ofFn (fun j : Fin 457 =>
      (rightFlag (unsortedMode j).2,leftFlag (unsortedMode j).2)) =
      List.ofFn (fun j : Fin 457 => (if j=455 then 1 else 0,if j=456 then 1 else 0)) := by rfl
  have he := congrFun (List.ofFn_injective h) i
  exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩

/-- Exactly the signed arithmetic coefficient formula on the page. -/
def integerCoefficient (i : Fin 457) : ℤ :=
  (1 + 255 * 2^9 + 255 * 2^18 + 2^27 + 2^29) +
    2^29 * (encode (unsortedMode i).1 : ℤ) -
    255 * 2^9 * integerDelta i 455 - 255 * 2^18 * integerDelta i 456 -
    2^27 * (integerDelta i 455 + integerDelta i 456)

theorem integerCoefficient_eq (i : Fin 457) : integerCoefficient i =
    (selectorCoefficient (unsortedMode i).2 (unsortedMode i).1 : ℤ) := by
  have hr : delta i 455 = rightFlag (unsortedMode i).2 := by
    rw [delta_eq,(flags i).1]
  have hl : delta i 456 = leftFlag (unsortedMode i).2 := by
    rw [delta_eq,(flags i).2]
  unfold integerCoefficient
  simp only [integerDelta_cast]
  rw [hr,hl]
  generalize (unsortedMode i).2 = kind
  generalize (unsortedMode i).1 = t
  cases kind <;>
    simp only [selectorCoefficient,rightFlag,leftFlag,Nat.sub_zero,Nat.sub_self,
      Nat.mul_zero,Nat.mul_one,Nat.add_zero,
      Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_zero,Nat.cast_pow] <;> ring

def coefficient (i : Fin 457) : ℕ := (integerCoefficient i).toNat

theorem coefficient_eq (i : Fin 457) : coefficient i =
    selectorCoefficient (unsortedMode i).2 (unsortedMode i).1 := by
  simp only [coefficient,integerCoefficient_eq,Int.toNat_natCast]

/-- All non-selector assignment entries, in fixed finite blocks. The
west bit at 539 carries an additional anchor contribution. -/
def auxiliaryEntries : List (ℕ × ℕ) :=
  ((List.range 11).map fun j => (539+j,2^(29+j)+(if j=0 then 2^71 else 0))) ++
  ((List.range 10).map fun j => (528+j,2^(40+j))) ++
  ((List.range 11).map fun j => (517+j,2^(50+j))) ++
  ((List.range 10).map fun j => (495+j,2^(61+j))) ++
  ((List.range 8).map fun j => (567+j,(2^9+2^29*(2+2^33))*2^j)) ++
  ((List.range 8).map fun j => (575+j,(2^18+2^29*(2^22+2^33))*2^j)) ++
  [(583,2^27+2^29*(2^11+2^32)),(1203,2^71),(1807,2^71),(507,0),(508,0)]

private theorem auxiliaryEntries_eq : auxiliaryEntries =
    ((List.finRange 42).map fun j => (copyPosition j,copyBitCoefficient j)) ++
    ((List.finRange 8).map fun j => (567+j.val,rightBitCoefficient j)) ++
    ((List.finRange 8).map fun j => (575+j.val,leftBitCoefficient j)) ++
    [(583,commonBitCoefficient),(1203,anchorCoefficient),(1807,anchorCoefficient),
      (507,0),(508,0)] := by rfl

theorem entries_split : entries =
    (modeList.zipIdx.map fun p => (p.2,selectorCoefficient p.1.2 p.1.1)) ++
      auxiliaryEntries := by
  rw [auxiliaryEntries_eq]
  simp only [entries,List.append_assoc]

attribute [local irreducible] modeList

private theorem zipIdx_modes : List.ofFn (fun i : Fin 457 => (mode i,i.val)) = modeList.zipIdx := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_zipIdx,modeList_length]
  · intro j h₁ h₂
    simp only [List.getElem_ofFn,List.getElem_zipIdx,mode,Nat.zero_add]

private theorem selectors_sum (ρ : ℕ) :
    ((modeList.zipIdx.map fun p => (p.2,selectorCoefficient p.1.2 p.1.1)).map
      fun p => p.2 * (ρ^(2409-p.1)+ρ^(3015-p.1))).sum =
    ∑ i : Fin 457, selectorCoefficient (mode i).2 (mode i).1 *
      (ρ^(2409-i.val)+ρ^(3015-i.val)) := by
  rw [← zipIdx_modes,List.map_map,List.map_ofFn,Fin.sum_ofFn]
  rfl

attribute [local irreducible] mode unsortedMode coefficient integerCoefficient arithmeticRank
  selectorCoefficient encode permutation tailPermutation

def selectorWord (ρ : ℕ) : ℕ := ∑ i : Fin 457,
  coefficient i * (ρ^(2409-arithmeticRank i)+ρ^(3015-arithmeticRank i))

theorem selectorWord_eq (ρ : ℕ) : selectorWord ρ =
    ∑ i : Fin 457, selectorCoefficient (mode i).2 (mode i).1 *
      (ρ^(2409-i.val)+ρ^(3015-i.val)) := by
  simp only [selectorWord,coefficient_eq,unsortedMode_eq,arithmeticRank_eq]
  exact Equiv.sum_comp permutation (fun i : Fin 457 =>
    selectorCoefficient (mode i).2 (mode i).1 *
      (ρ^(2409-i.val)+ρ^(3015-i.val)))

attribute [local irreducible] selectorWord auxiliaryEntries

def stencilWord (ρ : ℕ) : ℕ :=
  ρ^33+ρ^68+ρ^664+ρ^1268+selectorWord ρ+
    (auxiliaryEntries.map fun p => p.2*(ρ^(2409-p.1)+ρ^(3015-p.1))).sum+ρ^4877

/-- Exact symbolic K identity for every radix, with no 434054-bit expansion. -/
theorem stencilWord_eq_rawWord (ρ : ℕ) : stencilWord ρ = rawWord ρ := by
  rw [rawWord_eq,entries_split,List.map_append,List.sum_append,selectors_sum,
    ← selectorWord_eq]
  unfold stencilWord cellLength
  simp only [show (4831 : ℕ)+46=4877 by decide]
  omega

end DiophantineConsistency.OnePageTuple54
