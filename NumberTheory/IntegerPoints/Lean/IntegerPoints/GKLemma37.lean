import IntegerPoints.GKStatements

/-!
# Graham–Kolesnik, Lemma 3.7

The book form of the differencing lemma follows from `AP.lemma37_sharp` after
translating between its output derivative count `P₀` and the book's input
count `P = P₀ + 1`.
-/

namespace LeanProofs.IntegerPoints

/-- **Graham–Kolesnik, Lemma 3.7** in the book's shift range
`h < 2εN/(s+P)`. -/
theorem gk_lemma37_holds : gk_lemma37 := by
  intro N P s y ε a b h f hP hs hy hε _hεhalf hf hh1 hhb hhN
  have hPsucc : P - 1 + 1 = P := Nat.sub_add_cancel hP
  have hf' : InGKClass N ((P - 1) + 1) s y ε a b f := by
    simpa only [hPsucc] using hf
  have hPcast : (((P - 1 : ℕ) : ℝ) + 1) = (P : ℝ) := by
    exact_mod_cast hPsucc
  have hden : s + ((P - 1 : ℕ) : ℝ) + 1 = s + (P : ℝ) := by
    calc
      s + ((P - 1 : ℕ) : ℝ) + 1 =
          s + (((P - 1 : ℕ) : ℝ) + 1) := by ring
      _ = s + (P : ℝ) := by rw [hPcast]
  apply AP.lemma37_sharp (P := P - 1) hs hy hε hf'
    (lt_of_lt_of_le zero_lt_one hh1) hhb.le
  rw [hden]
  exact hhN

end LeanProofs.IntegerPoints
