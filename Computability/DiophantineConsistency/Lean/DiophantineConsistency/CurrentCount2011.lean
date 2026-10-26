import DiophantineConsistency.CurrentClause2011

/-!
# The literal clause gives preliminary count in every phase

All clause, count, Boolean temporal-source and incoming-carry bindings
are discharged from the actual convolution and normalization data. Only
the middle phases request the actual483 padding premises. Their separate
literal derivation is the remaining input to unconditional count recovery.
-/

namespace DiophantineConsistency.CurrentCount2011

open NativeCyclicConvolution NativeCyclicRotation NativeBooleanRotation
  CurrentMasks2011 CurrentClause2011 PaddingStaircase

set_option Elab.async false

variable {N : ℕ} [NeZero (N * 2011)]

def MiddlePadding (c digits : ZMod (N * 2011) → ℕ) (b : ZMod (N * 2011)) : Prop :=
  ∃ u : ℕ → ℕ,
    (∀ j, 1 ≤ j → j ≤ 483 → u j ≤ 2) ∧
    (∀ j, 1 ≤ j → j ≤ 483 →
      digits (b + ((63 + j : ℕ) : ZMod (N * 2011))) % 16 =
        (2 * prefixSum (fun f => c (b + (f : ZMod (N * 2011)))) j + u j) % 16) ∧
    (∀ j, 1 ≤ j → j ≤ 483 →
      digits (b + ((63 + j : ℕ) : ZMod (N * 2011))) &&& 8 = 0)

/-- No clause residue, mask, temporal scale/source, or initial count bound
is supplied: each is derived from the literal normalized current word. -/
theorem count_le_one_of_middle_padding
    (c carry digits : ZMod (N * 2011) → ℕ) (W : ℕ)
    (hc : ∀ k, c k ≤ 1)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (hk : ∀ k, carry k ≤ 57)
    (hlocal : ∀ k, convolution CurrentKernel2011.folded c k + binaryRotation 47 W c k +
      carry (k - 1) = digits k + radix * carry k)
    (hmask : ∀ k, digits k &&& CurrentHighDigits2011.maskDigits k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    (hpadding : 7 ≤ W % 47 → W % 47 ≤ 10 → MiddlePadding c digits b) :
    selectorCount c b ≤ 1 := by
  classical
  let bit : ℕ → ℕ := fun j => c (b + (j : ZMod (N * 2011)))
  let pdigit : ℕ → ℕ := fun j => digits (b + ((63 + j : ℕ) : ZMod (N * 2011)))
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℕ,
      7 ≤ W % 47 → W % 47 ≤ 10 →
        (∀ j, 1 ≤ j → j ≤ 483 → u j ≤ 2) ∧
        (∀ j, 1 ≤ j → j ≤ 483 → pdigit j % 16 = (2 * prefixSum bit j + u j) % 16) ∧
        (∀ j, 1 ≤ j → j ≤ 483 → pdigit j &&& 8 = 0) := by
    by_cases hm : 7 ≤ W % 47 ∧ W % 47 ≤ 10
    · obtain ⟨u, hu⟩ := hpadding hm.1 hm.2
      exact ⟨u, fun _ _ => hu⟩
    · exact ⟨fun _ => 0, fun h₁ h₂ => False.elim (hm ⟨h₁, h₂⟩)⟩
  have hr := normalized_clause_residue c (binaryRotation 47 W c) carry digits
    hsupport hlocal b hb
  rw [rotation_eq_scaled (by decide : 0 < 47) W c hc (b + 1005),
    selectorCount_eq_prefix] at hr
  have hm := normalized_clause_mask digits hmask b hb
  have hcount := NativePreliminaryCount2011.total_le_one_all_phases bit u pdigit
    (fun j _ => hc (b + (j : ZMod (N * 2011))))
    (hk (b + 1004)) (hc (b + 1))
    (hc ((b + 1005) - ((W / 47 : ℕ) : ZMod (N * 2011)))) hr hm hu
  exact (selectorCount_eq_prefix c b).trans_le hcount

end DiophantineConsistency.CurrentCount2011
