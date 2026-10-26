import DiophantineConsistency.WangTiles942ResetRows

/-!
UNCOMPILED proposal for ProveIt 22e020937caa81d0cb72a4f63071d6c0bcc1eba9.
This changes only the proof of interval_propagate. The tile-specific clients,
strict boundary hypotheses and both local propagation premises are unchanged.
The Int.induction_on API is already used in WangTiles942SeamColumns.lean.
-/

namespace DiophantineConsistency.WangRowsRound3

theorem interval_propagate_candidate (P : ℤ → Prop) (l r x₀ : ℤ)
    (hl₀ : l < x₀) (hr₀ : x₀ < r) (h₀ : P x₀)
    (hnext : ∀ x, l < x → x+1 < r → P x → P (x+1))
    (hprev : ∀ x, l < x-1 → x < r → P x → P (x-1)) :
    ∀ x, l < x → x < r → P x := by
  have hshift (z : ℤ) : l < x₀+z → x₀+z < r → P (x₀+z) := by
    induction z using Int.induction_on with
    | zero =>
        intro hl hr
        simpa only [add_zero] using h₀
    | succ n ih =>
        intro hl hr
        have hs := hnext (x₀+(n : ℤ)) (by omega) (by omega)
          (ih (by omega) (by omega))
        convert hs using 1 <;> omega
    | pred n ih =>
        intro hl hr
        have hs := hprev (x₀+(-(n : ℤ))) (by omega) (by omega)
          (ih (by omega) (by omega))
        convert hs using 1 <;> omega
  intro x hl hr
  have he : x₀+(x-x₀) = x := by omega
  simpa only [he] using hshift (x-x₀) (by omega) (by omega)

end DiophantineConsistency.WangRowsRound3

#print axioms DiophantineConsistency.WangRowsRound3.interval_propagate_candidate
