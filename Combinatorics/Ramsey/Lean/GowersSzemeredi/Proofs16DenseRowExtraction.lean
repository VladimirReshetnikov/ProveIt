import GowersSzemeredi.Proofs16BilinearBogolyubovRows

/-! Extract dense rows from an ambient set of pairs, retaining the sharp
averaging factor (alpha-theta)/(1-theta). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem rowOf_card_sum {N : Nat} [NeZero N] (A : Finset (ZMod N × ZMod N)) :
    (∑ y : ZMod N, (rowOf A y).card) = A.card := by
  have hrow (y : ZMod N) : (rowOf A y).card = (A.filter fun p => p.2 = y).card := by
    apply Finset.card_bij (fun x _ => (x, y))
    · intro x hx
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).2, rfl⟩
    · intro x hx z hz h
      exact congrArg Prod.fst h
    · intro p hp
      obtain ⟨hp, hpy⟩ := Finset.mem_filter.mp hp
      refine ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simpa only [← hpy] using hp
      · exact Prod.ext rfl hpy.symm
  simp_rw [hrow]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp

def denseRowSet {N : Nat} [NeZero N] (A : Finset (ZMod N × ZMod N))
    (theta : Real) : Finset (ZMod N) :=
  Finset.univ.filter fun y => theta ≤ (rowOf A y).card / (N : Real)

/-- The exact first-moment bound for rows above a specified density. -/
theorem denseRowSet_density {N : Nat} [NeZero N] (A : Finset (ZMod N × ZMod N))
    {alpha theta : Real} (htheta : theta < 1) (hA : alpha * (N : Real)^2 ≤ A.card) :
    ((alpha - theta) / (1 - theta)) * N ≤ ((denseRowSet A theta).card : Real) := by
  let Y := denseRowSet A theta
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hpoint (y : ZMod N) : ((rowOf A y).card : Real) ≤
      theta * N + if y ∈ Y then (1 - theta) * N else 0 := by
    by_cases hy : y ∈ Y
    · rw [if_pos hy]
      have hcard : ((rowOf A y).card : Real) ≤ N := by
        exact_mod_cast (show (rowOf A y).card ≤ N by
          simpa [rowOf] using Finset.card_le_card (Finset.filter_subset (fun x => (x, y) ∈ A) Finset.univ))
      nlinarith only [hcard]
    · rw [if_neg hy, add_zero]
      have hlow : ((rowOf A y).card : Real) / N < theta := by
        exact lt_of_not_ge (fun h => hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      exact (div_lt_iff₀ hN).mp hlow |>.le
  have hsum : (A.card : Real) ≤ theta * (N : Real)^2 +
      (Y.card : Real) * ((1 - theta) * N) := by
    calc
      (A.card : Real) = ∑ y : ZMod N, ((rowOf A y).card : Real) := by
        exact_mod_cast (rowOf_card_sum A).symm
      _ ≤ ∑ y : ZMod N, (theta * N + if y ∈ Y then (1 - theta) * N else 0) :=
        Finset.sum_le_sum fun y _ => hpoint y
      _ = _ := by
        simp [Finset.sum_add_distrib]
        ring
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (sub_pos.mpr htheta)).mpr
  have hraw : (alpha - theta) * N ≤ (Y.card : Real) * (1 - theta) := by
    nlinarith only [hsum, hA, hN]
  exact hraw

/-- At threshold alpha/2 the row-set density is at least alpha/(2-alpha),
which is stronger than the usual alpha/2 lower bound. -/
theorem exists_dense_rows {N : Nat} [NeZero N] (A : Finset (ZMod N × ZMod N))
    {alpha : Real} (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hA : alpha * (N : Real)^2 ≤ A.card) :
    ∃ Y : Finset (ZMod N), (alpha / (2 - alpha)) * N ≤ (Y.card : Real) ∧
      ∀ y ∈ Y, alpha / 2 ≤ (rowOf A y).card / (N : Real) := by
  refine ⟨denseRowSet A (alpha / 2), ?_, fun y hy => (Finset.mem_filter.mp hy).2⟩
  have h := denseRowSet_density A (show alpha / 2 < 1 by linarith) hA
  have heq : (alpha - alpha / 2) / (1 - alpha / 2) = alpha / (2 - alpha) := by
    field_simp
    ring
  simpa only [heq] using h

end LeanProofs.GowersSzemeredi
