import IntegerPoints.GKBProcessTheorem

/-!
# Graham--Kolesnik process words

The trivial exponent pair is closed under every finite word in the `A`- and
`B`-processes.  The list is evaluated from right to left by
`gk_process_word`, so induction on its head applies the corresponding process
to the exponent pair supplied by the induction hypothesis.
-/

namespace LeanProofs.IntegerPoints

/-- **Graham--Kolesnik, Section 3.1.**  Every finite word in the `A`- and
`B`-processes sends the trivial pair `(0, 1)` to an exponent pair. -/
theorem gk_sec31_words_holds : gk_sec31_words := by
  intro w
  induction w with
  | nil =>
      simpa only [gk_process_word] using isExponentPair_zero_one
  | cons process w ih =>
      cases process with
      | false =>
          have hB :
              IsExponentPair
                ((gk_process_word w (0, 1)).2 - 1 / 2)
                ((gk_process_word w (0, 1)).1 + 1 / 2) :=
            gk_theorem310_holds _ _ ih
          simpa only [gk_process_word] using hB
      | true =>
          have hA :
              IsExponentPair
                ((gk_process_word w (0, 1)).1 /
                  (2 * (gk_process_word w (0, 1)).1 + 2))
                (((gk_process_word w (0, 1)).1 +
                    (gk_process_word w (0, 1)).2 + 1) /
                  (2 * (gk_process_word w (0, 1)).1 + 2)) :=
            AP.isExponentPair_A ih
          simpa only [gk_process_word] using hA

end LeanProofs.IntegerPoints
