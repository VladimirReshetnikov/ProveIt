import DiophantineConsistency.FreeCarrierRatio
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Coordinate transport independent of the supplied scalar evaluator. -/

namespace DiophantineConsistency.FreeCarrierCoordinates

/-- Positive slots are `b,g,h,s,w,C,i,j+1,n`; the internal `j` may be zero. -/
theorem exists_positive_zero
    (evaluate : ℕ → ℕ → FreeCarrierRatio.FreeVars → ℕ → ℤ) :
    (∃ x : Fin 9 → ℕ, (∀ i, 0 < x i) ∧
      evaluate (x 0) (x 1) ⟨x 2, x 3, x 4, x 5, x 6, x 7 - 1⟩ (x 8) = 0) ↔
      ∃ b g : ℕ, 0 < b ∧ 0 < g ∧ ∃ v : FreeCarrierRatio.FreeVars,
        0 < v.h ∧ 0 < v.s ∧ 0 < v.w ∧ 0 < v.C ∧ 0 < v.i ∧
          ∃ n : ℕ, 0 < n ∧ evaluate b g v n = 0 := by
  constructor
  · rintro ⟨x, hp, hz⟩
    exact ⟨x 0, x 1, hp 0, hp 1, ⟨x 2, x 3, x 4, x 5, x 6, x 7 - 1⟩,
      hp 2, hp 3, hp 4, hp 5, hp 6, x 8, hp 8, hz⟩
  · rintro ⟨b, g, hb, hg, v, hh, hs, hw, hC, hi, n, hn, hz⟩
    refine ⟨![b, g, v.h, v.s, v.w, v.C, v.i, v.j + 1, n], ?_, ?_⟩
    · intro i
      fin_cases i <;> simp_all
    · simpa using hz

/-- Successor assignments parametrize precisely the pointwise positive tuples. -/
theorem exists_positive_iff_successors {σ : Type*} (P : (σ → ℕ) → Prop) :
    (∃ x : σ → ℕ, (∀ i, 0 < x i) ∧ P x) ↔ ∃ x : σ → ℕ, P (fun i => x i + 1) := by
  constructor
  · rintro ⟨x, hx, hP⟩
    refine ⟨fun i => x i - 1, ?_⟩
    convert hP using 1
    funext i
    exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr (hx i))
  · rintro ⟨x, hP⟩
    exact ⟨fun i => x i + 1, fun i => Nat.succ_pos _, hP⟩

end DiophantineConsistency.FreeCarrierCoordinates
