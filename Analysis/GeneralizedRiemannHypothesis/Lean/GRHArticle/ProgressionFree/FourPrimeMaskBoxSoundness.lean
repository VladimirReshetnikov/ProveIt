import GRHArticle.ProgressionFree.FourPrimeMaskBoxCheck

/-!
# Soundness of the optimized low-box check

Mixed-radix coding preserves every exponent vector and its integer score.
The coordinates within each row inherit progression-freeness, and a
recorded midpoint completion can never belong to the admitted set.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

/-- Success of the mask certificate bounds the inflated score of every
admitted subset, provided the initial mask covers the desired box. -/
theorem fourPrimeBoxScore_le_of_maskCertificate
    (q r : Fin 4 → ℕ) (hP : q 0 = 2 ∨ q 0 = 3)
    (hR : ∀ i, r i ≤ fourPrimeLowBoxLimit i)
    (order : List ℕ) (mask target : ℕ)
    (hCover : ∀ a ∈ exponentBox r, mask.testBit (fourPrimeEncode a) = true)
    (hc : finiteGPMaskCheck (fourPrimeMaskCapacity q) fourPrimeBoxCompletion target order [] mask = true)
    (F : Set (Fin 4 → ℕ)) (hF : ThreeAPFree F) :
    letI : DecidablePred (· ∈ F) := fun _ ↦ Classical.propDecidable _
    (∑ a ∈ exponentBox r, if a ∈ F then fourPrimeBoxScore q a else 0) ≤ target := by
  classical
  let S := (exponentBox r).filter (· ∈ F)
  let A := S.image fourPrimeEncode
  have hFull (a : Fin 4 → ℕ) (ha : a ∈ S) : a ∈ exponentBox fourPrimeLowBoxLimit :=
    mem_exponentBox.mpr fun i ↦ (mem_exponentBox.mp (mem_filter.mp ha).1 i).trans (hR i)
  have hDec (x : ℕ) (hx : x ∈ A) : fourPrimeDecode x ∈ F ∧ fourPrimeEncode (fourPrimeDecode x) = x := by
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
    rw [fourPrimeDecode_encode (hFull a ha)]
    exact ⟨(mem_filter.mp ha).2,rfl⟩
  have hRange : A ⊆ range 729 := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
    exact mem_range.mpr (fourPrimeEncode_lt (hFull a ha))
  have hRows (row : ℕ) (_ : row < 81) : ThreeAPFree (fourPrimeRowSubset A row : Set ℕ) := by
    intro a ha b hb c hc hMid
    obtain ⟨x,hx,hax⟩ := mem_image.mp ha
    obtain ⟨y,hy,hby⟩ := mem_image.mp hb
    obtain ⟨z,hz,hcz⟩ := mem_image.mp hc
    have hX : fourPrimeDecode x = fourPrimeRowPoint row a := by
      rw [fourPrimeDecode_eq_rowPoint,(mem_filter.mp hx).2,hax]
    have hY : fourPrimeDecode y = fourPrimeRowPoint row b := by
      rw [fourPrimeDecode_eq_rowPoint,(mem_filter.mp hy).2,hby]
    have hZ : fourPrimeDecode z = fourPrimeRowPoint row c := by
      rw [fourPrimeDecode_eq_rowPoint,(mem_filter.mp hz).2,hcz]
    have hE : fourPrimeDecode x + fourPrimeDecode z = fourPrimeDecode y + fourPrimeDecode y := by
      rw [hX,hY,hZ]
      funext i
      fin_cases i
      · exact hMid
      · rfl
      · rfl
      · rfl
    have he := hF (hDec x (mem_filter.mp hx).1).1 (hDec y (mem_filter.mp hy).1).1
      (hDec z (mem_filter.mp hz).1).1 hE
    rw [hX,hY] at he
    exact congrFun he 0
  have hClose (x : ℕ) (hx : x ∈ A) (y : ℕ) (hy : y ∈ A) (z : ℕ)
      (hz : fourPrimeBoxCompletion x y = some z) : z ∉ A := by
    intro hZ
    obtain ⟨hne,hMid⟩ := fourPrimeBoxCompletion_spec hz
    have he := hF (hDec x hx).1 (hDec y hy).1 (hDec z hZ).1 hMid
    exact hne ((hDec x hx).2.symm.trans ((congrArg fourPrimeEncode he).trans (hDec y hy).2))
  have hInit : gpMaskContains A mask := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
    exact hCover a (mem_filter.mp ha).1
  have hScore := finiteGPMaskCheck_sound (fourPrimeMaskCapacity q) fourPrimeBoxCompletion
    target (fun n ↦ fourPrimeBoxScore q (fourPrimeDecode n)) A
    (fun mask hMask ↦ sum_fourPrimeCodeScore_le_maskCapacity q hP A hRange hRows mask hMask)
    hClose order mask hInit hc
  have hInj : Set.InjOn fourPrimeEncode (S : Set (Fin 4 → ℕ)) := by
    intro a ha b hb he
    have hd := congrArg fourPrimeDecode he
    simpa only [fourPrimeDecode_encode (hFull a ha),fourPrimeDecode_encode (hFull b hb)] using hd
  rw [←sum_filter]
  change (∑ a ∈ S, fourPrimeBoxScore q a) ≤ _
  rw [show A = S.image fourPrimeEncode from rfl,sum_image hInj] at hScore
  exact (le_of_eq (sum_congr rfl (fun a ha ↦ congrArg (fourPrimeBoxScore q)
    (fourPrimeDecode_encode (hFull a ha)).symm))).trans hScore

/-- Success of the optimized checker bounds the inflated integer score of
every progression-free subset of the rectangular prefix. -/
theorem fourPrimeBoxScore_le_target_of_maskCheck
    (q r : Fin 4 → ℕ) (hP : q 0 = 2 ∨ q 0 = 3)
    (hR : ∀ i, r i ≤ fourPrimeLowBoxLimit i) (hc : fourPrimeMaskBoxCheck q r = true)
    (F : Set (Fin 4 → ℕ)) (hF : ThreeAPFree F) :
    letI : DecidablePred (· ∈ F) := fun _ ↦ Classical.propDecidable _
    (∑ a ∈ exponentBox r, if a ∈ F then fourPrimeBoxScore q a else 0) ≤ fourPrimeBoxTarget q r := by
  apply fourPrimeBoxScore_le_of_maskCertificate q r hP hR (fourPrimeBoxCodes q r)
    (fourPrimeCodeMask (fourPrimeBoxCodes q r)) (fourPrimeBoxTarget q r) _ hc F hF
  intro a ha
  have hm : gpMaskContains {fourPrimeEncode a} (fourPrimeCodeMask (fourPrimeBoxCodes q r)) :=
    gpMaskContains_fourPrimeBoxCodes q r (by
      intro x hx
      exact ⟨a,ha,(mem_singleton.mp hx).symm⟩)
  exact hm _ (mem_singleton_self _)

end GRHArticle.ProgressionFree
