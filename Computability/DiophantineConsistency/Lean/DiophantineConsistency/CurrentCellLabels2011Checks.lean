import DiophantineConsistency.CurrentCellLabels2011

namespace DiophantineConsistency.CurrentCellLabels2011Checks

open CurrentCellLabels2011 CurrentClause2011 CurrentMasks2011 WangTiles942
  NativeCyclicConvolution NativeCyclicRotation

-- Exact physical orientation follows the complete kernel coefficient map.
example : CurrentKernel2011.position (.inr (.inl (0 : Fin 8))) = 978 := rfl
example : CurrentKernel2011.position (.inr (.inr (.inl (0 : Fin 9)))) = 960 := rfl
example : CurrentKernel2011.position (.inr (.inr (.inr (.inl (0 : Fin 8))))) = 969 := rfl
example : CurrentKernel2011.position (.inr (.inr (.inr (.inr (0 : Fin 9))))) = 942 := rfl

variable {N : ℕ} [NeZero (N * 2011)]

-- Neither incoming-zero nor occupation nor whole-field alignment is supplied.
example (c carry digits : ZMod (N * 2011) → ℕ) (W : ℕ)
    (hc : ∀ k, c k ≤ 1)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (hk : ∀ k, carry k ≤ 57)
    (hlocal : ∀ k, convolution CurrentKernel2011.folded c k + binaryRotation 47 W c k +
      carry (k - 1) = digits k + radix * carry k)
    (hmask : ∀ k, digits k &&& CurrentHighDigits2011.maskDigits k = 0)
    (hphase : W % 47 = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    (hn : selectorCount c b ≤ 1) :
    CellDecoded c carry W b ∧ carry (b + 1005) = 0 :=
  decode_cell c carry digits W hc hsupport hk hlocal hmask hphase b hb hn

-- The actually forced Start field recovers its actual South complement510.
example (c carry : ZMod (N * 2011) → ℕ) (W : ℕ) (hc : ∀ k, c k ≤ 1)
    (h0 : c 0 = 1) (hdecoded : CellDecoded c carry W 0) :
    binaryWord (fun j => c (((942 + j : ℕ) : ZMod (N * 2011)))) 9 = 510 := by
  have hi : selectorValue c 0 0 = 1 := by
    simpa only [selectorValue, physicalPosition_zero, Nat.cast_zero, zero_add] using h0
  have hword := hdecoded.word_of_selected 0 hi
  have hs := (labels_of_word c 0 hc 0 hword).2.2.2
  simpa only [zero_add, start_zero] using hs

-- The generic chosen index is unique, with no table expansion or occupation axiom.
example (f : Fin 942 → ℕ) (i : Fin 942) (h : Selected f i) : ∃! j, f j = 1 :=
  ⟨i, h.1, h.unique⟩

#print axioms clause_convolution_word
#print axioms sum_le_one_cases
#print axioms decode_cell
#print axioms labels_of_word
#print axioms CellDecoded.word_of_selected

end DiophantineConsistency.CurrentCellLabels2011Checks
