import GRHArticle.SingularModuli.Support
import GRHArticle.SingularModuli.ThresholdDiskRoots
import Mathlib.FieldTheory.Separable

/-!
# Certifying maximal support from the roots of a minimal polynomial

An irreducible rational polynomial of degree `d` supplies `d` distinct
roots in an algebraically closed field of characteristic zero. If they
all belong to a region containing fewer than `d` roots of each nonzero
polynomial with at most `d` terms, every root has minimum support `d+1`.
-/

namespace GRHArticle.SingularModuli

open Polynomial

/-- Certify maximum support using a root-count bound on a region containing
all roots of the candidate minimal polynomial. -/
theorem minimumSupport_eq_of_rootSet_bound {E L : Type*} [Field E] [CharZero E]
    [IsAlgClosed E] [Field L] [Algebra ℚ L] (H : ℚ[X]) (hmonic : H.Monic)
    (hirr : Irreducible H) (x : L) (hx : aeval x H = 0) (D : Set E)
    (hD : ∀ y : E, aeval y H = 0 → y ∈ D)
    (hbound : ∀ Q : E[X], Q ≠ 0 → Q.support.card ≤ H.natDegree →
      {y : E | y ∈ D ∧ Q.eval y = 0}.encard ≤ ((H.natDegree - 1 : ℕ) : ℕ∞)) :
    minimumSupport (K := ℚ) (x := x) ⟨H, hmonic, hx⟩ = H.natDegree + 1 := by
  classical
  have hmin := minpoly.eq_of_irreducible_of_monic hirr hx hmonic
  have hpos := hirr.natDegree_pos
  have hint : IsIntegral ℚ x := ⟨H, hmonic, hx⟩
  have upper := minimumSupport_le_natDegree_add_one hint
  rw [← hmin] at upper
  have lower : ¬ minimumSupport hint ≤ H.natDegree := by
    rw [minimumSupport_le_iff]
    rintro ⟨P, hP, hsize, hzero⟩
    let f := algebraMap ℚ E
    have hsub : H.rootSet E ⊆ {y : E | y ∈ D ∧ (P.map f).eval y = 0} := by
      obtain ⟨G, hG⟩ := hmin ▸ minpoly.dvd ℚ x hzero
      intro y hy
      have hz := aeval_eq_zero_of_mem_rootSet hy
      refine ⟨hD y hz, ?_⟩
      simp only [f, eval_map_algebraMap, hG, map_mul, hz, zero_mul]
    have hc := (Set.encard_mono hsub).trans (hbound _ ((Polynomial.map_ne_zero_iff f.injective).2 hP)
      (by simpa only [support_map_of_injective P f.injective] using hsize))
    rw [Set.encard, ENat.card_eq_coe_fintype_card,
      card_rootSet_eq_natDegree hirr.separable (IsAlgClosed.splits _), Nat.cast_le] at hc
    omega
  change minimumSupport hint = _
  omega

/-- The open disk criterion for an irreducible rational polynomial and the
factorial threshold in `smd:cor:threshold`. -/
theorem minimumSupport_eq_of_threshold_disk {p : ℕ} [Fact p.Prime]
    {L : Type*} [Field L] [Algebra ℚ L] (H : ℚ[X]) (hmonic : H.Monic)
    (hirr : Irreducible H) (x : L) (hx : aeval x H = 0)
    (a : ℂ_[p]) (ha : a ≠ 0) {κ : ℚ} (hκ : 1 / ((p : ℚ) - 1) ≤ κ)
    (hval : ∀ i < H.natDegree, ∀ d > 0, (factorialIntervalValuation p i d : ℚ) ≤ (d : ℚ) * κ)
    (hdisk : ∀ y : ℂ_[p], aeval y H = 0 → ‖y / a - 1‖ < (p : ℝ) ^ (-(κ : ℝ))) :
    minimumSupport (K := ℚ) (x := x) ⟨H, hmonic, hx⟩ = H.natDegree + 1 := by
  apply minimumSupport_eq_of_rootSet_bound H hmonic hirr x hx _ hdisk
  exact fun Q hQ hs => encard_polynomialDiskRoots_lt_of_interval_bound Q hQ a ha hs hκ hval

end GRHArticle.SingularModuli
