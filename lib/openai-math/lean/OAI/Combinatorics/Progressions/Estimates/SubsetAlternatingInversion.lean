import OAI.Combinatorics.Progressions.Results.Basic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

noncomputable def subsetAlternatingTransform (F : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * F (S \ U)

theorem subsetAlternatingTransform_insert (F : Finset ι → ℝ) (S : Finset ι)
    {i : ι} (hi : i ∉ S) :
    subsetAlternatingTransform F (insert i S) =
      subsetAlternatingTransform (fun T => F (insert i T)) S - subsetAlternatingTransform F S := by
  unfold subsetAlternatingTransform
  rw [Finset.sum_powerset_insert hi]
  have he₁ (U : Finset ι) (hU : U ∈ S.powerset) : (insert i S) \ U = insert i (S \ U) := by
    have hn : i ∉ U := fun h => hi (Finset.mem_powerset.mp hU h)
    ext j
    by_cases hj : j = i <;> simp [hj, hn]
  have he₂ (U : Finset ι) (hU : U ∈ S.powerset) :
      (-1 : ℝ) ^ (insert i U).card * F ((insert i S) \ insert i U) =
        -((-1 : ℝ) ^ U.card * F (S \ U)) := by
    have hn : i ∉ U := fun h => hi (Finset.mem_powerset.mp hU h)
    have hs : (insert i S) \ insert i U = S \ U := by
      ext j
      by_cases hj : j = i <;> simp [hj, hi]
    rw [hs, Finset.card_insert_of_notMem hn, pow_succ]
    ring
  rw [Finset.sum_congr rfl (fun U hU => congrArg (fun z => (-1 : ℝ) ^ U.card * F z) (he₁ U hU)),
    Finset.sum_congr rfl he₂, Finset.sum_neg_distrib]
  rfl

theorem subsetAlternatingTransform_sum (S : Finset ι) (F : Finset ι → ℝ) :
    (∑ T ∈ S.powerset, subsetAlternatingTransform F T) = F S := by
  induction S using Finset.induction_on generalizing F with
  | empty => simp [subsetAlternatingTransform]
  | @insert i S hi ih =>
      rw [Finset.sum_powerset_insert hi]
      have he (T : Finset ι) (hT : T ∈ S.powerset) :
          subsetAlternatingTransform F (insert i T) =
            subsetAlternatingTransform (fun U => F (insert i U)) T - subsetAlternatingTransform F T :=
        subsetAlternatingTransform_insert F T (fun h => hi (Finset.mem_powerset.mp hT h))
      rw [Finset.sum_congr rfl he, Finset.sum_sub_distrib, ih F, ih (fun U => F (insert i U))]
      ring

end Erdos3

end

end OAI
