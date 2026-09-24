import Diophantine.Paper1976.FiveSquareGrowth
import Diophantine.Paper1976.RefinedWeightBounds

/-!
# The ten-witness, five-square prime criterion

Equation (24) supplies the two growth inequalities used by the proof of
Theorem 3.9. Together with the four remaining square conditions, divisibility,
and the positive polynomial margin, it gives a criterion with ten natural
witnesses. All radicands are the integer polynomials already used by the
unconditional refined weight bounds.
-/

namespace JSWW1976

open RefinedWeightBounds

/-- The integer polynomial (24) agrees with its natural growth radicand. -/
@[simp] theorem RefinedWeightBounds.mergedRadicand_natCast (k n x : ℕ) :
    mergedRadicand k n x = (fiveSquareRadicand k n x : ℤ) := by
  have hT : 1 ≤ U (2 * k) n := by unfold U; omega
  have he : elim39U (2 * (k : ℤ)) n = (U (2 * k) n : ℤ) := by
    simp [elim39U, U]
  unfold mergedRadicand fiveSquareRadicand fiveSquareSecond
  rw [he]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_sub hT,
    Nat.cast_ofNat, Nat.cast_one]

/-- Five square tests, one divisibility condition, and one positive margin.
The ten lower-case arguments after `k` are the only witnesses. -/
structure FiveSquareSys39 (k n x w m i j p l r z : ℕ) : Prop where
  squares : ∀ a : Fin 5, IsSquare (fiveRadicands k n x w m i j p l r z a)
  dvd : let v := elim39Values k n x w m i j p l r z; v.F ∣ v.H - v.C
  margin : let v := elim39Values k n x w m i j p l r z;
    0 < elim39Margin v.C v.K v.L v.R v.S w x

/-- The replacement square has exactly the growth consequences needed later. -/
theorem FiveSquareSys39.toReducedGrowthSys39 {k n x w m i j p l r z : ℕ}
    (hk : 1 ≤ k) (h : FiveSquareSys39 k n x w m i j p l r z) :
    ReducedGrowthSys39 k n x w m i j p l r z := by
  have h0 := h.squares 0
  change IsSquare (mergedRadicand k n x) at h0
  rw [mergedRadicand_natCast, Int.isSquare_natCast_iff] at h0
  obtain ⟨_, hn, hx⟩ := fiveSquareRadicand_growth hk h0
  refine ⟨hn, hx, ?_, h.dvd, h.margin⟩
  intro a
  fin_cases a
  · exact h.squares 1
  · exact h.squares 2
  · exact h.squares 3
  · exact h.squares 4

/-- Adding (24) to a reduced growth solution supplies the five-square system. -/
theorem ReducedGrowthSys39.toFiveSquareSys39 {k n x w m i j p l r z : ℕ}
    (h : ReducedGrowthSys39 k n x w m i j p l r z)
    (h0 : IsSquare (fiveSquareRadicand k n x)) :
    FiveSquareSys39 k n x w m i j p l r z := by
  refine ⟨?_, h.dvd, h.margin⟩
  intro a
  fin_cases a
  · change IsSquare (mergedRadicand k n x)
    rw [mergedRadicand_natCast, Int.isSquare_natCast_iff]
    exact h0
  · exact h.squares 0
  · exact h.squares 1
  · exact h.squares 2
  · exact h.squares 3

/-- Sufficiency of the five-square criterion, with no old second-square premise. -/
theorem FiveSquareSys39.prime {k n x w m i j p l r z : ℕ}
    (hk : 1 ≤ k) (h : FiveSquareSys39 k n x w m i j p l r z) : Nat.Prime (k + 1) :=
  (h.toReducedGrowthSys39 hk).prime hk

/-- The replacement criterion preserves exactly ten natural witnesses. -/
theorem theorem_3_9_five_square {k : ℕ} (hk : 1 ≤ k) :
    Nat.Prime (k + 1) ↔
      ∃ n x w m i j p l r z : ℕ, FiveSquareSys39 k n x w m i j p l r z := by
  constructor
  · intro hp
    obtain ⟨n, _, hnSquare⟩ := exists_U_square (2 * k) 0
    obtain ⟨x, _, hxSquare⟩ := exists_fiveSquareRadicand_square hnSquare 0
    obtain ⟨_, hn, hx⟩ := fiveSquareRadicand_growth hk hxSquare
    obtain ⟨w, m, i, j, p, l, r, z, M, A, B, C, D, E, F, G, H, I, K, L, R, S, hS⟩ :=
      theorem_3_9_necessity_of_growth hk hp hn hx
    exact ⟨n, x, w, m, i, j, p, l, r, z, (hS.reduced hk).toFiveSquareSys39 hxSquare⟩
  · rintro ⟨n, x, w, m, i, j, p, l, r, z, h⟩
    exact h.prime hk

end JSWW1976
