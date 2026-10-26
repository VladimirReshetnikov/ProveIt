import DiophantineConsistency.FreeCarrierRatio
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
PROPOSED, NOT COMPILED IN THIS REVIEW.
A reusable extraction of the byte-identical coordinate-packaging proofs in
SplitSourceExistence.lean:98-157 and GapSourceExistence66.lean:53-112 at
60e9c5d620c6c387d932876cfa2d9376f64ea56c.

The evaluator is arbitrary; no source, coefficient, carry or consistency
property is assumed. Slot 7 is j+1 in a positive tuple, but is the unrestricted
natural j in a natural tuple. All other eight coordinates are strictly positive.
This file is a proposal artifact, not a repository modification or checked patch.
-/

namespace DiophantineConsistency.NineCoordinatePackagingProposal

abbrev Evaluator := ℕ → ℕ → FreeCarrierRatio.FreeVars → ℕ → ℤ

def HasZero (evaluate : Evaluator) : Prop :=
  ∃ b g : ℕ, 0 < b ∧ 0 < g ∧ ∃ v : FreeCarrierRatio.FreeVars,
    0 < v.h ∧ 0 < v.s ∧ 0 < v.w ∧ 0 < v.C ∧ 0 < v.i ∧
      ∃ n : ℕ, 0 < n ∧ evaluate b g v n = 0

/-- Positive slots: b, g, h, s, w, C, i, j+1, n. -/
def positiveVars (x : Fin 9 → ℕ) : FreeCarrierRatio.FreeVars :=
  ⟨x 2, x 3, x 4, x 5, x 6, x 7 - 1⟩

def positiveValue (evaluate : Evaluator) (x : Fin 9 → ℕ) : ℤ :=
  evaluate (x 0) (x 1) (positiveVars x) (x 8)

theorem exists_positive_zero_iff_hasZero (evaluate : Evaluator) :
    (∃ x : Fin 9 → ℕ, (∀ i, 0 < x i) ∧ positiveValue evaluate x = 0) ↔
      HasZero evaluate := by
  constructor
  · rintro ⟨x, hpos, hzero⟩
    exact ⟨x 0, x 1, hpos 0, hpos 1, positiveVars x,
      hpos 2, hpos 3, hpos 4, hpos 5, hpos 6, x 8, hpos 8, hzero⟩
  · rintro ⟨b, g, hb, hg, v, hh, hs, hw, hC, hi, n, hn, hzero⟩
    let x : Fin 9 → ℕ := ![b, g, v.h, v.s, v.w, v.C, v.i, v.j + 1, n]
    have hp : ∀ i, 0 < x i := by
      intro i
      fin_cases i
      · exact hb
      · exact hg
      · exact hh
      · exact hs
      · exact hw
      · exact hC
      · exact hi
      · exact Nat.succ_pos _
      · exact hn
    have hv : positiveVars x = v := by
      cases v
      rfl
    refine ⟨x, hp, ?_⟩
    change evaluate b g (positiveVars x) n = 0
    rw [hv]
    exact hzero

/-- Natural slots: b-1, g-1, h-1, s-1, w-1, C-1, i-1, j, n-1. -/
def naturalVars (x : Fin 9 → ℕ) : FreeCarrierRatio.FreeVars :=
  ⟨x 2 + 1, x 3 + 1, x 4 + 1, x 5 + 1, x 6 + 1, x 7⟩

def naturalValue (evaluate : Evaluator) (x : Fin 9 → ℕ) : ℤ :=
  evaluate (x 0 + 1) (x 1 + 1) (naturalVars x) (x 8 + 1)

theorem positiveValue_successors (evaluate : Evaluator) (x : Fin 9 → ℕ) :
    positiveValue evaluate (fun i => x i + 1) = naturalValue evaluate x := rfl

theorem exists_natural_zero_iff_hasZero (evaluate : Evaluator) :
    (∃ x : Fin 9 → ℕ, naturalValue evaluate x = 0) ↔ HasZero evaluate := by
  rw [← exists_positive_zero_iff_hasZero evaluate]
  constructor
  · rintro ⟨x, hzero⟩
    exact ⟨fun i => x i + 1, fun i => Nat.succ_pos _,
      by rw [positiveValue_successors]; exact hzero⟩
  · rintro ⟨x, hpos, hzero⟩
    let y : Fin 9 → ℕ := fun i => x i - 1
    have he : (fun i => y i + 1) = x := by
      funext i
      exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr (hpos i))
    refine ⟨y, ?_⟩
    rw [← positiveValue_successors, he]
    exact hzero

#print axioms DiophantineConsistency.NineCoordinatePackagingProposal.exists_positive_zero_iff_hasZero
#print axioms DiophantineConsistency.NineCoordinatePackagingProposal.exists_natural_zero_iff_hasZero

end DiophantineConsistency.NineCoordinatePackagingProposal
