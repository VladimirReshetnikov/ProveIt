import GowersSzemeredi.Proofs16RobustCorrelation
import GowersSzemeredi.Proofs16PatternMissingRows

/-! Exact counting interpretation of the fourfold correlation, including
transport to the witness sets used in the pattern graph. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Correlation coordinates: displacement t and the two starting points x,y. -/
def fourDifferenceTriples {N : Nat} [NeZero N]
    (W : Finset (ZMod N)) (d : ZMod N) : Finset (ZMod N × ZMod N × ZMod N) :=
  Finset.univ.filter fun q => q.2.1 ∈ W ∧ q.2.1 - q.1 ∈ W ∧
    q.2.2 ∈ W ∧ q.2.2 - (q.1 - d) ∈ W

/-- The self-correlation is an actual nonnegative integer count. -/
theorem mixed_self_correlation_eq_card {N : Nat} [NeZero N]
    (W : Finset (ZMod N)) (d : ZMod N) :
    mixedDifferenceCorrelation W W d = ((fourDifferenceTriples W d).card : Complex) := by
  have hstar (x : ZMod N) : star (indicator W x) = indicator W x := by
    by_cases hx : x ∈ W <;> simp [indicator, hx]
  unfold mixedDifferenceCorrelation correlation
  simp only [star_sum, star_mul, hstar]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [show ((fourDifferenceTriples W d).card : Complex) =
      ∑ q : ZMod N × ZMod N × ZMod N,
        if q.2.1 ∈ W ∧ q.2.1 - q.1 ∈ W ∧ q.2.2 ∈ W ∧
          q.2.2 - (q.1 - d) ∈ W then 1 else 0 by simp [fourDifferenceTriples]]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : x ∈ W <;> by_cases hxt : x - t ∈ W <;>
    by_cases hy : y ∈ W <;> by_cases hyt : y - (t - d) ∈ W <;>
    simp [indicator, hx, hxt, hy, hyt]

/-- Changing to three points of a containing class preserves the exact
number of representations; there is no density or nonemptiness assumption. -/
theorem fourDifferenceTriples_card_eq_pattern {N : Nat} [NeZero N]
    (W C : Finset (ZMod N)) (hWC : W ⊆ C) (d : ZMod N) :
    (fourDifferenceTriples W d).card = (patternRepresentationTriples W C d).card := by
  let f : (q : ZMod N × ZMod N × ZMod N) → q ∈ fourDifferenceTriples W d →
      (Fin 3 → ↥C) := fun q hq =>
    ![⟨q.2.1, hWC (Finset.mem_filter.mp hq).2.1⟩,
      ⟨q.2.2 - (q.1 - d), hWC (Finset.mem_filter.mp hq).2.2.2.2⟩,
      ⟨q.2.2, hWC (Finset.mem_filter.mp hq).2.2.2.1⟩]
  apply Finset.card_bij f
  · intro q hq
    have h := (Finset.mem_filter.mp hq).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [f, h.1, h.2.2.1, h.2.2.2]
    · change q.2.1 + (q.2.2 - (q.1 - d)) - q.2.2 - d ∈ W
      rw [show q.2.1 + (q.2.2 - (q.1 - d)) - q.2.2 - d = q.2.1 - q.1 by ring]
      exact h.2.1
  · intro q hq r hr heq
    have h0 := congrArg (fun v : Fin 3 → ↥C => (v 0 : ZMod N)) heq
    have h1 := congrArg (fun v : Fin 3 → ↥C => (v 1 : ZMod N)) heq
    have h2 := congrArg (fun v : Fin 3 → ↥C => (v 2 : ZMod N)) heq
    change q.2.1 = r.2.1 at h0
    change q.2.2 - (q.1 - d) = r.2.2 - (r.1 - d) at h1
    change q.2.2 = r.2.2 at h2
    apply Prod.ext
    · linear_combination h2 - h1
    · exact Prod.ext h0 h2
  · intro v hv
    have h := (Finset.mem_filter.mp hv).2
    let q : ZMod N × ZMod N × ZMod N :=
      ((v 2 : ZMod N) + d - v 1, v 0, v 2)
    have hq : q ∈ fourDifferenceTriples W d := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, h.1 0, ?_, h.1 2, ?_⟩
      · change (v 0 : ZMod N) - ((v 2 : ZMod N) + d - v 1) ∈ W
        rw [show (v 0 : ZMod N) - ((v 2 : ZMod N) + d - v 1) =
          (v 0 : ZMod N) + v 1 - v 2 - d by ring]
        exact h.2
      · change (v 2 : ZMod N) - ((v 2 : ZMod N) + d - v 1 - d) ∈ W
        rw [show (v 2 : ZMod N) - ((v 2 : ZMod N) + d - v 1 - d) = v 1 by ring]
        exact h.1 1
    refine ⟨q, hq, ?_⟩
    funext i
    apply Subtype.ext
    fin_cases i <;> simp [f, q]
    ring

/-- Exact norm/count identity for the witness set used by row filling. -/
theorem mixed_self_correlation_norm_eq_pattern_card {N : Nat} [NeZero N]
    (W C : Finset (ZMod N)) (hWC : W ⊆ C) (d : ZMod N) :
    ‖mixedDifferenceCorrelation W W d‖ =
      ((patternRepresentationTriples W C d).card : Real) := by
  rw [mixed_self_correlation_eq_card, Complex.norm_natCast,
    fourDifferenceTriples_card_eq_pattern W C hWC]

end LeanProofs.GowersSzemeredi
