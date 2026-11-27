import GRHArticle.SingularModuli.PadicDiskRoots
import GRHArticle.SingularModuli.Support

/-!
# Sparse annihilators and conjugates in one p-adic disk

The number of distinct conjugate values in a disk is a lower bound on the
number of disk roots of every annihilating polynomial. This converts the local
fewnomial bound into an obstruction over the original coefficient field.
-/

namespace GRHArticle.SingularModuli

variable {p : ℕ} [Fact (Nat.Prime p)] {r : ℚ}

/-- Allowing more terms can only increase the factorial weight cutoff. -/
theorem sparseDiskRootBound_mono {s t : ℕ} (hs : 0 < s) (hst : s ≤ t)
    (hr : 1 / ((p : ℚ) - 1) < r) :
    sparseDiskRootBound p s r hs hr ≤ sparseDiskRootBound p t r (hs.trans_le hst) hr := by
  obtain ⟨i, hi⟩ := (isGreatest_sparseDiskRootBound hs hr).1
  exact (isGreatest_sparseDiskRootBound (hs.trans_le hst) hr).2 ⟨i.castLE hst, hi⟩

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra K ℂ_[p]]

/-- More than `B_p(t,r)` distinct conjugate images in a disk rule out every
annihilator over the base field with at most `t` terms. -/
theorem not_hasSparseAnnihilator_of_padic_conjugates {m t : ℕ} (ht : 0 < t)
    (hr : 1 / ((p : ℚ) - 1) < r) (x : L) (a : ℂ_[p]) (ha : a ≠ 0)
    (σ : Fin m → L →ₐ[K] ℂ_[p]) (hdistinct : Function.Injective (fun i => σ i x))
    (hdisk : ∀ i, ‖σ i x / a - 1‖ ≤ (p : ℝ) ^ (-(r : ℝ)))
    (hcount : sparseDiskRootBound p t r ht hr < m) :
    ¬ HasSparseAnnihilator K x t := by
  rintro ⟨P, hP, hterms, hzero⟩
  let f := algebraMap K ℂ_[p]
  have hmap := (Polynomial.map_ne_zero_iff f.injective).mpr hP
  have hcard := Polynomial.support_map_of_injective P f.injective
  have hroots := encard_polynomialDiskRoots_le (P.map f) hmap a ha hr
  let S := {y : ℂ_[p] | ‖y / a - 1‖ ≤ (p : ℝ) ^ (-(r : ℝ)) ∧ (P.map f).eval y = 0}
  have hsub : Set.range (fun i => σ i x) ⊆ S := by
    rintro _ ⟨i, rfl⟩
    refine ⟨hdisk i, ?_⟩
    simp [f, Polynomial.aeval_algHom_apply, hzero]
  have hm : (m : ℕ∞) ≤ S.encard := by
    simpa using hdistinct.encard_range.trans (Set.encard_mono hsub)
  have hs : 0 < (P.map f).support.card := Finset.card_pos.mpr (Polynomial.support_nonempty.mpr hmap)
  have hst : (P.map f).support.card ≤ t := hcard ▸ hterms
  have impossible := (hm.trans hroots).trans (Nat.cast_le.mpr (sparseDiskRootBound_mono hs hst hr))
  exact (Nat.not_le_of_lt hcount) (Nat.cast_le.mp impossible)

/-- Three conjugates in the depth-half disk at seven exclude a rational
trinomial, including polynomials with fewer than three nonzero coefficients. -/
theorem not_hasSparseAnnihilator_three_of_seven_half_conjugates
    [Fact (Nat.Prime 7)] {L : Type*} [Field L] [Algebra ℚ L]
    (x : L) (a : ℂ_[7]) (ha : a ≠ 0) (σ : Fin 3 → L →ₐ[ℚ] ℂ_[7])
    (hdistinct : Function.Injective (fun i => σ i x))
    (hdisk : ∀ i, ‖σ i x / a - 1‖ ≤ (7 : ℝ) ^ (-(1 / 2 : ℚ) : ℝ)) :
    ¬ HasSparseAnnihilator ℚ x 3 := by
  apply not_hasSparseAnnihilator_of_padic_conjugates (r := 1 / 2) (by decide)
    (by norm_num) x a ha σ hdistinct hdisk
  obtain ⟨i, hi⟩ := (isGreatest_sparseDiskRootBound (p := 7) (t := 3) (r := 1 / 2)
    (by decide) (by norm_num)).1
  exact Nat.lt_succ_of_le (seven_half_trinomial_cutoff.2 ⟨i, i.isLt, hi⟩)

end GRHArticle.SingularModuli
