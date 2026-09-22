import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.Data.Finsupp.Basic

/-!
# Arbitrary regrouping of jointly Hahn-summable families

This file proves the regrouping and interchange assertions immediately after
`a:def:summable` in `docs/surcomplex/analysis/article.tex`.

Starting with a `HahnSeries.SummableFamily`, an arbitrary function between
index types partitions the original indices into fibers. Each fiber is
summable, the family of its sums is summable, and its Hahn sum is the original
sum. Both levels inherit summability from the one jointly summable family;
no theorem here infers joint summability from two iterated sums.

At each exponent, regrouping is Mathlib's `Finsupp.mapDomain` on the finite
coefficient family. No topology or convergence operation is involved.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ R ι κ : Type*} [PartialOrder Γ] [AddCommMonoid R]

/-- Restricting a strongly summable family to any subset preserves both
summability conditions in `a:def:summable`. -/
def restrict (s : SummableFamily Γ R ι) (A : Set ι) : SummableFamily Γ R A where
  toFun i := s i.val
  isPWO_iUnion_support' := s.isPWO_iUnion_support.mono <|
    Set.iUnion_subset fun i _ hg => Set.mem_iUnion.mpr ⟨i.val, hg⟩
  finite_co_support' g :=
    (s.finite_co_support g).preimage fun _ _ _ _ h => Subtype.ext h

@[simp]
theorem restrict_apply (s : SummableFamily Γ R ι) (A : Set ι) (i : A) :
    restrict s A i = s i.val := rfl

/-- Grouping the finitely many coefficients at an exponent by an arbitrary
index map is precisely `Finsupp.mapDomain`. -/
theorem finsum_fiber_eq_mapDomain (d : ι →₀ R) (f : ι → κ) (b : κ) :
    (∑ᶠ i : {i // f i = b}, d i.val) = d.mapDomain f b := by
  classical
  simp only [finsum_subtype_eq_finsum_cond, finsum_eq_if, Finsupp.mapDomain,
    Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.single_apply]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  simp only [Finset.mem_coe, Finsupp.mem_support_iff]
  intro hid
  simp [hid] at hi

/-- The coefficient of a fiber's Hahn sum is the finite sum of the original
coefficients over that fiber, including when the fiber itself is infinite. -/
theorem coeff_hsum_fiber (s : SummableFamily Γ R ι) (f : ι → κ) (b : κ) (g : Γ) :
    (restrict s {i | f i = b}).hsum.coeff g = (s.coeff g).mapDomain f b := by
  exact finsum_fiber_eq_mapDomain (s.coeff g) f b

/-- Regroup a jointly strongly summable family by any index map. Its value
at `b` is the Hahn sum over the fiber above `b`. This is the arbitrary
regrouping construction stated after `a:def:summable`. -/
def regroup (s : SummableFamily Γ R ι) (f : ι → κ) : SummableFamily Γ R κ where
  toFun b := (restrict s {i | f i = b}).hsum
  isPWO_iUnion_support' := by
    refine s.isPWO_iUnion_support.mono ?_
    intro g hg
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hg
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (SummableFamily.support_hsum_subset hb)
    exact Set.mem_iUnion.mpr ⟨i.val, hi⟩
  finite_co_support' g := by
    refine ((s.coeff g).mapDomain f).support.finite_toSet.subset ?_
    intro b hb
    exact Finsupp.mem_support_iff.mpr ((coeff_hsum_fiber s f b g) ▸ hb)

@[simp]
theorem regroup_apply (s : SummableFamily Γ R ι) (f : ι → κ) (b : κ) :
    regroup s f b = (restrict s {i | f i = b}).hsum := rfl

/-- Regrouping acts on each finite coefficient family by `mapDomain`. -/
theorem coeff_regroup (s : SummableFamily Γ R ι) (f : ι → κ) (g : Γ) :
    (regroup s f).coeff g = (s.coeff g).mapDomain f := by
  ext b
  exact coeff_hsum_fiber s f b g

/-- Arbitrary regrouping preserves the Hahn sum, as asserted after
`a:def:summable`. The original joint summability witness supplies the finite
coefficient rearrangements required by the proof. -/
theorem hsum_regroup (s : SummableFamily Γ R ι) (f : ι → κ) :
    (regroup s f).hsum = s.hsum := by
  ext g
  rw [SummableFamily.coeff_hsum_eq_sum, SummableFamily.coeff_hsum_eq_sum]
  change ((regroup s f).coeff g).sum (fun _ r => r) = (s.coeff g).sum (fun _ r => r)
  rw [coeff_regroup]
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

/-- The two orders of summation agree for a jointly summable double family.
The inner fiber sums and both outer families are built by `regroup`, so this
is the interchange assertion after `a:def:summable` with its hypothesis intact. -/
theorem hsum_fubini (s : SummableFamily Γ R (ι × κ)) :
    (regroup s Prod.fst).hsum = (regroup s Prod.snd).hsum :=
  (hsum_regroup s Prod.fst).trans (hsum_regroup s Prod.snd).symm

end

end Surreal.HahnSeries
