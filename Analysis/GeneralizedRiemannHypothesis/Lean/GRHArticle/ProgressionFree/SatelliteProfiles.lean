import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Single-coordinate changes to an all-ones exponent profile
-/

namespace GRHArticle.ProgressionFree

open scoped BigOperators

private noncomputable def raisedSatelliteProfile {ι : Type*} (e : ℕ) (i : ι) (j : ι) : ℕ := by
  classical
  exact if j = i then e else 1

/-- Profiles formed by setting one chosen satellite exponent to e. -/
noncomputable def raisedSatelliteProfiles {ι : Type*} [Fintype ι] (e : ℕ) : Finset (ι → ℕ) := by
  classical
  exact Finset.univ.image (raisedSatelliteProfile e)

theorem mem_raisedSatelliteProfiles_iff {ι : Type*} [Fintype ι] {e : ℕ} {v : ι → ℕ} :
    v ∈ raisedSatelliteProfiles e ↔ ∃ i, (∀ j, j ≠ i → v j = 1) ∧ v i = e := by
  classical
  rw [raisedSatelliteProfiles, Finset.mem_image]
  constructor
  · rintro ⟨i, _, rfl⟩
    exact ⟨i, fun j hj => by simp [raisedSatelliteProfile, hj], by simp [raisedSatelliteProfile]⟩
  · rintro ⟨i, h, hi⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    funext j
    by_cases hj : j = i
    · subst j
      simpa [raisedSatelliteProfile] using hi.symm
    · simpa [raisedSatelliteProfile, hj] using (h j hj).symm

private theorem raisedSatelliteProfile_injective {ι : Type*} {e : ℕ} (he : e ≠ 1) :
    Function.Injective (raisedSatelliteProfile (ι := ι) e) := by
  classical
  intro i j h
  by_contra hij
  exact he (by simpa [raisedSatelliteProfile, hij] using congrFun h i)

private theorem prod_raisedSatelliteProfile {ι R : Type*} [Fintype ι] [CommMonoid R]
    (u : ι → R) (i : ι) {e : ℕ} (he : 1 ≤ e) :
    (∏ j, u j ^ raisedSatelliteProfile e i j) = (∏ j, u j) * u i ^ (e - 1) := by
  classical
  have hfactor (j : ι) :
      u j ^ raisedSatelliteProfile e i j = u j * (if j = i then u j ^ (e - 1) else 1) := by
    by_cases hj : j = i
    · simp only [raisedSatelliteProfile, if_pos hj]
      rw [← pow_succ', Nat.sub_add_cancel he]
    · simp [raisedSatelliteProfile, hj]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']

/-- The weight of the raised profiles factors out the weight of the all-ones
profile, leaving the sum of the extra powers at the chosen coordinate. -/
theorem sum_raisedSatelliteProfiles_weight {ι R : Type*} [Fintype ι] [CommSemiring R]
    (u : ι → R) {e : ℕ} (he : 1 < e) :
    (∑ v ∈ raisedSatelliteProfiles e, ∏ j, u j ^ v j) =
      (∏ j, u j) * ∑ j, u j ^ (e - 1) := by
  classical
  rw [raisedSatelliteProfiles,
    Finset.sum_image (fun _ _ _ _ h => raisedSatelliteProfile_injective he.ne' h)]
  simp_rw [prod_raisedSatelliteProfile u _ he.le]
  rw [Finset.mul_sum]

theorem disjoint_raisedSatelliteProfiles_allOnes {ι : Type*} [Fintype ι]
    {e : ℕ} (he : e ≠ 1) :
    Disjoint (raisedSatelliteProfiles (ι := ι) e) ({(fun _ : ι => (1 : ℕ))} : Finset (ι → ℕ)) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro v hv hone
  obtain ⟨i, _, hi⟩ := mem_raisedSatelliteProfiles_iff.mp hv
  exact he (hi.symm.trans (congrFun (Finset.mem_singleton.mp hone) i))

theorem disjoint_raisedSatelliteProfiles_of_ne {ι : Type*} [Fintype ι]
    {e e' : ℕ} (he : e ≠ 1) (hee : e ≠ e') :
    Disjoint (raisedSatelliteProfiles (ι := ι) e) (raisedSatelliteProfiles e') := by
  refine Finset.disjoint_left.mpr ?_
  intro v hv hv'
  obtain ⟨i, _, hi⟩ := mem_raisedSatelliteProfiles_iff.mp hv
  obtain ⟨j, hrest, hj⟩ := mem_raisedSatelliteProfiles_iff.mp hv'
  by_cases hij : i = j
  · subst j
    exact hee (hi.symm.trans hj)
  · exact he (hi.symm.trans (hrest i hij))

end GRHArticle.ProgressionFree
