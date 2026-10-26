import DiophantineConsistency.BoundedForallDepth

/-!
UNCOMPILED REVIEW CANDIDATES, not kernel-checked replacements.
Pinned source: b310142330df89e48413c8fce62e7de223e1c7d5.
These lemmas change no representation data or witness counts.
-/
namespace DiophantineConsistency.Round2Supplemental

/-- Pay the Fin-2 elimination cost once, not in every binary graph wrapper. -/
theorem compose_two_depth_le {σ : Type*}
    {f : (Fin 2 → ℕ) → ℕ} {g : Fin 2 → (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : ∀ i, GraphRep (g i)) {h : ℕ}
    (hh : 1 ≤ h) (hr : r.depth ≤ h)
    (h0 : (s 0).depth ≤ h) (h1 : (s 1).depth ≤ h) :
    (r.compose s).depth ≤ h + 8 := by
  refine (GraphRep.compose_depth_le r s hh hr ?_).trans (by omega)
  intro i
  fin_cases i <;> assumption

/-- Pilot replacement for the body of BoundedForallDepth.pow_depth_le. -/
theorem pow_depth_le_candidate {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) {h : ℕ} (hh : 512 ≤ h)
    (hr : r.depth ≤ h) (hs : s.depth ≤ h) : (r.pow s).depth ≤ h + 8 := by
  unfold GraphRep.pow
  exact compose_two_depth_le _ _ (by omega) (BoundedForallDepth.pow_depth.trans hh) hr hs

/-- Pilot for the binomial wrapper; sub/mod/div have the same proof shape. -/
theorem binomial_depth_le_candidate {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) {h : ℕ} (hh : 512 ≤ h)
    (hr : r.depth ≤ h) (hs : s.depth ≤ h) : (r.binomial s).depth ≤ h + 8 := by
  unfold GraphRep.binomial
  exact compose_two_depth_le _ _ (by omega) (BoundedForallDepth.binomial_depth.trans hh) hr hs

#print axioms DiophantineConsistency.Round2Supplemental.compose_two_depth_le
#print axioms DiophantineConsistency.Round2Supplemental.pow_depth_le_candidate
#print axioms DiophantineConsistency.Round2Supplemental.binomial_depth_le_candidate
end DiophantineConsistency.Round2Supplemental
