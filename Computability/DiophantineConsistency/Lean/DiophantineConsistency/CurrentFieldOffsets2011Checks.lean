import DiophantineConsistency.CurrentFieldOffsets2011

namespace DiophantineConsistency.CurrentFieldOffsets2011Checks

open CurrentFieldOffsets2011 CurrentCellTranslation2011 CurrentClause2011 CurrentMasks2011
open scoped BigOperators

set_option maxRecDepth 10000

variable {N : ℕ} [NeZero (N * 2011)]

-- Exact endpoint: only support, count and the three source equalities.
example (c : ZMod (N * 2011) → ℕ) (t : ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (hcount : ∀ b : Cell N, selectorCount c (b : ZMod (N * 2011)) ≤ 1)
    (hmarker : c (1004 - (t : ZMod (N * 2011))) = 1)
    (h961 : c (961 - (t : ZMod (N * 2011))) = 1)
    (h962 : c (962 - (t : ZMod (N * 2011))) = 1) :
    t % 2011 = 0 ∨ t % 2011 = 19 ∨ t % 2011 = 20 :=
  coarse_offset c t hsupport hcount hmarker h961 h962

-- The marker alone excludes18 without count, labels or a current marker value.
example (c : ZMod (N * 2011) → ℕ) (t : ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (hmarker : c (1004 - (t : ZMod (N * 2011))) = 1)
    (hr : t % 2011 = 18) : False := by
  have h := marker_remainder_bounds c hsupport t hmarker
  omega

-- At the lower middle endpoint21 the selector pair is940/941, both counted.
example (c : ZMod (N * 2011) → ℕ) (t : ℕ)
    (hcount : ∀ b : Cell N, selectorCount c (b : ZMod (N * 2011)) ≤ 1)
    (h961 : c (961 - (t : ZMod (N * 2011))) = 1)
    (h962 : c (962 - (t : ZMod (N * 2011))) = 1)
    (hr : t % 2011 = 21) : False :=
  not_middle_offset c t hcount h961 h962 ⟨by omega, by omega⟩

-- At the upper middle endpoint961 the selector pair is0/1, still distinct.
example (c : ZMod (N * 2011) → ℕ) (t : ℕ)
    (hcount : ∀ b : Cell N, selectorCount c (b : ZMod (N * 2011)) ≤ 1)
    (h961 : c (961 - (t : ZMod (N * 2011))) = 1)
    (h962 : c (962 - (t : ZMod (N * 2011))) = 1)
    (hr : t % 2011 = 961) : False :=
  not_middle_offset c t hcount h961 h962 ⟨by omega, by omega⟩

-- Generic distinctness is an index condition; no finite table is evaluated.
example (f : Fin 942 → ℕ) (hi : f 940 = 1) (hj : f 941 = 1) :
    2 ≤ ∑ a, f a := two_ones_sum_ge_two f 940 941 (by decide) hi hj

#print axioms two_ones_sum_ge_two
#print axioms marker_remainder_bounds
#print axioms remainder_le_961
#print axioms two_distinct_selectors_force_count
#print axioms not_middle_offset
#print axioms coarse_offset

end DiophantineConsistency.CurrentFieldOffsets2011Checks
