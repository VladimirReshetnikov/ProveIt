import GowersSzemeredi.Proofs16ColumnAnchorCounts

/-! Hereditary additive richness supplies a dense set of columns with
uniformly many exact quadruple representations. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

def popularColumnAnchors {N : Nat} [NeZero N] (B : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r lambda : Real) : Finset (ZMod N) :=
  B.filter (fun a => lambda*(N : Real)^2 ≤ (exactColumnAnchor B T L r a).card)

/-- Retain half the guaranteed vertex density. Every retained column
has at least `eta^2*b^3*N^2/16` exact quadruple representations. -/
theorem popular_column_anchors_dense {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) {b eta : Real}
    (hb : 0 < b) (heta : 0 < eta) (hB : b*N ≤ (B.card : Real))
    (hrich : ∀ C ⊆ B, eta^2*(C.card : Real)^4 ≤ N*((exactColumnQuadruples C T L r).card : Real)) :
    b*N/2 ≤ ((popularColumnAnchors B T L r (eta^2*b^3/16)).card : Real) := by
  let lambda := eta^2*b^3/16
  let P := popularColumnAnchors B T L r lambda
  let C := B \ P
  have hCB : C ⊆ B := Finset.sdiff_subset
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hlow : ∀ a ∈ C, ((exactColumnAnchor B T L r a).card : Real) ≤ lambda*(N : Real)^2 := by
    intro a ha
    obtain ⟨haB, haP⟩ := Finset.mem_sdiff.mp ha
    have hnot : ¬ lambda*(N : Real)^2 ≤ (exactColumnAnchor B T L r a).card := by
      intro h
      exact haP (Finset.mem_filter.mpr ⟨haB,h⟩)
    exact (lt_of_not_ge hnot).le
  have hupper : ((exactColumnQuadruples C T L r).card : Real) ≤ (C.card : Real)*lambda*(N : Real)^2 := by
    have hsum : ((exactColumnQuadruples C T L r).card : Real) ≤
        ∑ a ∈ C, ((exactColumnAnchor B T L r a).card : Real) := by
      exact_mod_cast exact_quadruples_le_anchor_sum hCB T L r
    calc _ ≤ ∑ a ∈ C, ((exactColumnAnchor B T L r a).card : Real) := hsum
      _ ≤ ∑ _a ∈ C, lambda*(N : Real)^2 := Finset.sum_le_sum fun a ha => hlow a ha
      _ = _ := by simp; ring
  have hCsmall : (C.card : Real) < b*N/2 := by
    by_contra h
    have hClower := le_of_not_gt h
    have hCpos : (0 : Real) < C.card := lt_of_lt_of_le (by positivity) hClower
    have hbound := (hrich C hCB).trans (mul_le_mul_of_nonneg_left hupper hn.le)
    have hcancel : eta^2*(C.card : Real)^3 ≤ lambda*(N : Real)^3 := by
      apply (mul_le_mul_iff_left₀ hCpos).mp
      nlinarith [hbound]
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ b*(N : Real)/2) hClower 3
    have hscaled := (mul_le_mul_of_nonneg_left hpow (sq_nonneg eta)).trans hcancel
    have hfinal : eta^2*b^3/8 ≤ lambda := by
      apply (mul_le_mul_iff_right₀ (pow_pos hn 3)).mp
      nlinarith [hscaled]
    have hpos : 0 < eta^2*b^3 := mul_pos (pow_pos heta 2) (pow_pos hb 3)
    dsimp only [lambda] at hfinal
    linarith
  have hpartition : (C.card : Real) + P.card = B.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (show P ⊆ B from Finset.filter_subset _ _)
  change b*N/2 ≤ (P.card : Real)
  linarith

end LeanProofs.GowersSzemeredi
