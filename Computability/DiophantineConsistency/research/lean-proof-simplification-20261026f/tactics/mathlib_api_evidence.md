# Pinned mathlib API evidence

These excerpts establish source-level API/precedent, not candidate compilation.

## [Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1070–1081](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean#L1070-L1081)
to_additive generates add_eq_zero_iff_of_nonneg.
```lean
1070: @[to_additive]
1071: theorem mul_eq_one_iff_of_one_le [MulLeftMono α]
1072:     [MulRightMono α] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
1073:     a * b = 1 ↔ a = 1 ∧ b = 1 :=
1074:   Iff.intro
1075:     (fun hab : a * b = 1 =>
1076:       have : a ≤ 1 := hab ▸ le_mul_of_le_of_one_le le_rfl hb
1077:       have : a = 1 := le_antisymm this ha
1078:       have : b ≤ 1 := hab ▸ le_mul_of_one_le_of_le ha le_rfl
1079:       have : b = 1 := le_antisymm this hb
1080:       And.intro ‹a = 1› ‹b = 1›)
1081:     (by rintro ⟨rfl, rfl⟩; rw [mul_one])
```

## [Mathlib/NumberTheory/Dioph.lean:213–222](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/Dioph.lean#L213-L222)
Conditional simp precedent only; no proposed import.
```lean
213: 
214: @[simp] theorem sumsq_nonneg (x : α → ℕ) : ∀ l, 0 ≤ sumsq l x
215:   | [] => le_refl 0
216:   | p::ps => by
217:     rw [sumsq]
218:     exact add_nonneg (mul_self_nonneg _) (sumsq_nonneg _ ps)
219: 
220: theorem sumsq_eq_zero (x) : ∀ l, sumsq l x = 0 ↔ l.Forall fun a : Poly α => a x = 0
221:   | [] => eq_self_iff_true _
222:   | p::ps => by simp [sumsq, add_eq_zero_iff_of_nonneg, mul_self_nonneg, sumsq_eq_zero]
```

## [Mathlib/Algebra/Quaternion.lean:1113–1122](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Algebra/Quaternion.lean#L1113-L1122)
Explicit rewrite and nonnegativity fallback precedent.
```lean
1113: variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {a : ℍ[R]}
1114: 
1115: @[simp]
1116: theorem normSq_eq_zero : normSq a = 0 ↔ a = 0 := by
1117:   refine ⟨fun h => ?_, fun h => h.symm ▸ normSq.map_zero⟩
1118:   rw [normSq_def', add_eq_zero_iff_of_nonneg, add_eq_zero_iff_of_nonneg, add_eq_zero_iff_of_nonneg]
1119:     at h
1120:   · apply ext a 0 <;> apply eq_zero_of_pow_eq_zero
1121:     exacts [h.1.1.1, h.1.1.2, h.1.2, h.2]
1122:   all_goals apply_rules [sq_nonneg, add_nonneg]
```

## [Mathlib/Data/Finset/Basic.lean:353–358](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Data/Finset/Basic.lean#L353-L358)
filter_mem_eq_inter declaration.
```lean
353: 
354: theorem filter_union_right (s : Finset α) :
355:     s.filter p ∪ s.filter q = s.filter fun x => p x ∨ q x := by grind
356: 
357: theorem filter_mem_eq_inter {s t : Finset α} [∀ i, Decidable (i ∈ t)] :
358:     (s.filter fun i => i ∈ t) = s ∩ t := by grind
```
