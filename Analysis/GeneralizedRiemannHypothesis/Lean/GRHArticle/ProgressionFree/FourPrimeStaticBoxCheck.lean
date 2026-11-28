import GRHArticle.ProgressionFree.FourPrimeMaskBoxSoundness
import GRHArticle.ProgressionFree.FourPrimeLowBoxSoundness

/-!
# Replay with a supplied ordering

Coverage of the rectangular prefix and its target are computed directly.
The order may be supplied as a fixed list because the soundness proof
does not assume any property of it.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

private theorem fourPrimeEncode_decode (j : ℕ) : fourPrimeEncode (fourPrimeDecode j) = j := by
  change j%9 + 9*(j/9%9 + 9*(j/81%3 + 3*(j/243))) = j
  omega

private def codeInPrefix (r : Fin 4 → ℕ) (j : ℕ) : Bool :=
  decide (j%9 ≤ r 0 ∧ j/9%9 ≤ r 1 ∧ j/81%3 ≤ r 2 ∧ j/243 ≤ r 3)

private theorem codeInPrefix_iff (r : Fin 4 → ℕ) (j : ℕ) :
    codeInPrefix r j = true ↔ fourPrimeDecode j ∈ exponentBox r := by
  rw [codeInPrefix,decide_eq_true_eq,mem_exponentBox]
  constructor
  · rintro ⟨h₀,h₁,h₂,h₃⟩ i
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
    · exact h₃
  · intro h
    exact ⟨h 0,h 1,h 2,h 3⟩

private def prefixCodes (r : Fin 4 → ℕ) : List ℕ :=
  (List.range 729).filter (codeInPrefix r)

private theorem mem_prefixCodes (r : Fin 4 → ℕ) (j : ℕ) :
    j ∈ prefixCodes r ↔ j < 729 ∧ fourPrimeDecode j ∈ exponentBox r := by
  simp only [prefixCodes,List.mem_filter,List.mem_range,codeInPrefix_iff]

private theorem codeMask_covers (r : Fin 4 → ℕ) (hr : ∀ i, r i ≤ fourPrimeLowBoxLimit i)
    {a : Fin 4 → ℕ} (ha : a ∈ exponentBox r) :
    (fourPrimeCodeMask (prefixCodes r)).testBit (fourPrimeEncode a) = true := by
  have hFull : a ∈ exponentBox fourPrimeLowBoxLimit :=
    mem_exponentBox.mpr fun i ↦ (mem_exponentBox.mp ha i).trans (hr i)
  apply testBit_fourPrimeCodeMask
  apply (mem_prefixCodes r _).mpr
  exact ⟨fourPrimeEncode_lt hFull,(fourPrimeDecode_encode hFull).symm ▸ ha⟩

/-- The integer target computed directly from the prefix's codes. -/
def fourPrimeDirectTarget (q r : Fin 4 → ℕ) : ℕ :=
  ((prefixCodes r).map fun j ↦
    if fourPrimeBoxGood (fourPrimeDecode j) then fourPrimeBoxScore q (fourPrimeDecode j) else 0).sum

/-- Computing the greedy target never requires sorting the candidates. -/
theorem fourPrimeDirectTarget_eq (q r : Fin 4 → ℕ) (hr : ∀ i, r i ≤ fourPrimeLowBoxLimit i) :
    fourPrimeDirectTarget q r = fourPrimeBoxTarget q r := by
  let L := prefixCodes r
  let S := L.toFinset
  let f (a : Fin 4 → ℕ) := if fourPrimeBoxGood a then fourPrimeBoxScore q a else 0
  have hN : L.Nodup := List.nodup_range.filter _
  have hM : (L : Multiset ℕ) = S.val := congrArg Finset.val (List.toFinset_eq hN)
  have hCollect : S.image fourPrimeDecode = exponentBox r := by
    ext a
    constructor
    · intro ha
      obtain ⟨j,hj,rfl⟩ := mem_image.mp ha
      exact ((mem_prefixCodes r j).mp (List.mem_toFinset.mp hj)).2
    · intro ha
      have hf : a ∈ exponentBox fourPrimeLowBoxLimit :=
        mem_exponentBox.mpr fun i ↦ (mem_exponentBox.mp ha i).trans (hr i)
      exact mem_image.mpr ⟨fourPrimeEncode a,List.mem_toFinset.mpr ((mem_prefixCodes r _).mpr
        ⟨fourPrimeEncode_lt hf,(fourPrimeDecode_encode hf).symm ▸ ha⟩),fourPrimeDecode_encode hf⟩
  have hInj : Set.InjOn fourPrimeDecode (S : Set ℕ) := by
    intro x _ y _ h
    simpa only [fourPrimeEncode_decode] using congrArg fourPrimeEncode h
  rw [fourPrimeBoxTarget_eq_sum,←hCollect,sum_image hInj]
  change (Multiset.map (fun j ↦ f (fourPrimeDecode j)) (L : Multiset ℕ)).sum = _
  rw [hM]
  rfl

/-- Initial state for a supplied ordering and an independently computed box. -/
def fourPrimeStaticBoxState (q r : Fin 4 → ℕ) (order : List ℕ) : GPMaskCheckpoint :=
  let mask := fourPrimeCodeMask (prefixCodes r)
  ⟨order.filter mask.testBit,[],(mask,fourPrimeMaskCapacity q mask)⟩

/-- Execute the cache-backed search with a supplied candidate ordering. -/
def fourPrimeStaticBoxCheck (q r : Fin 4 → ℕ) (order : List ℕ) : Bool :=
  finiteGPCachedMaskCheckAt (fourPrimeMaskCapacityUpdate q) fourPrimeBoxCompletion
    (fourPrimeDirectTarget q r) (fourPrimeStaticBoxState q r order)

/-- The supplied order can affect speed but never the score certified
by a successful check. -/
theorem fourPrimeBoxScore_le_target_of_staticCheck
    (q r : Fin 4 → ℕ) (hP : q 0 = 2 ∨ q 0 = 3)
    (hr : ∀ i, r i ≤ fourPrimeLowBoxLimit i) (order : List ℕ)
    (hc : fourPrimeStaticBoxCheck q r order = true)
    (F : Set (Fin 4 → ℕ)) (hF : ThreeAPFree F) :
    letI : DecidablePred (· ∈ F) := fun _ ↦ Classical.propDecidable _
    (∑ a ∈ exponentBox r, if a ∈ F then fourPrimeBoxScore q a else 0) ≤ fourPrimeBoxTarget q r := by
  let mask := fourPrimeCodeMask (prefixCodes r)
  have h : finiteGPCachedMaskCheck (fourPrimeMaskCapacityUpdate q) fourPrimeBoxCompletion
      (fourPrimeDirectTarget q r) (order.filter mask.testBit) [] (mask,fourPrimeMaskCapacity q mask) = true := hc
  rw [finiteGPCachedMaskCheck_eq _ _ (fourPrimeMaskCapacityUpdate_correct q)] at h
  rw [fourPrimeDirectTarget_eq q r hr] at h
  exact fourPrimeBoxScore_le_of_maskCertificate q r hP hr (order.filter mask.testBit) mask _
    (fun _ ha ↦ codeMask_covers r hr ha) h F hF

end GRHArticle.ProgressionFree
