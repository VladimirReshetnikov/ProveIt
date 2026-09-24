import Surreal.Foundations.SignSequenceStrongAlgebra
import Surreal.HahnSeries.Regroup

/-!
# Regrouping actual strong sums

Restriction and reindexing preserve strong summability. An arbitrary map
on a small index type partitions a jointly summable family into small
fibers; their strong sums are jointly summable and retain the original
sum. These are the regrouping assertions after `a:def:summable`.
-/

universe u v w

namespace Surreal.Foundations.SignSequence

noncomputable section

variable {ι : Type v} {κ : Type w} {f : ι → SignSequence.{u}}

/-- A restriction retains both native support certificates. -/
theorem StronglySummable.restrict (hf : StronglySummable f) (A : Set ι) :
    StronglySummable (fun i : A => f i.val) :=
  stronglySummable_of_hahnFamily (Surreal.HahnSeries.restrict hf.toHahnFamily A)
    (fun _ => rfl)

/-- Reindexing by an equivalence preserves strong summability. -/
theorem StronglySummable.reindex (hf : StronglySummable f) (e : κ ≃ ι) :
    StronglySummable (fun i => f (e i)) :=
  stronglySummable_of_hahnFamily
    (_root_.HahnSeries.SummableFamily.Equiv e.symm hf.toHahnFamily) (fun _ => rfl)

/-- Strong summability is invariant under a bijective reindexing. -/
theorem stronglySummable_reindex_iff (e : κ ≃ ι) :
    StronglySummable (fun i => f (e i)) ↔ StronglySummable f := by
  constructor
  · intro h
    simpa only [e.apply_symm_apply] using h.reindex e.symm
  · exact fun h => h.reindex e

/-- Injective reindexing retains both native support certificates. -/
theorem StronglySummable.comp_injective (hf : StronglySummable f) (k : κ → ι)
    (hk : Function.Injective k) : StronglySummable (fun n => f (k n)) := by
  constructor
  · apply hf.1.mono
    exact Set.iUnion_subset fun n => Set.subset_iUnion_of_subset (k n) (Set.Subset.refl _)
  · intro a
    exact (hf.2 a).preimage hk.injOn

section Small

variable [Small.{u} ι]

omit [Small.{u} ι] in
/-- The normal-form family of a restriction is the native Hahn restriction. -/
theorem toHahnFamily_restrict (hf : StronglySummable f) (A : Set ι) :
    (hf.restrict A).toHahnFamily = Surreal.HahnSeries.restrict hf.toHahnFamily A := by
  apply _root_.HahnSeries.SummableFamily.ext
  intro i
  rfl

/-- A jointly summable family licenses the family of all sums over fibers. -/
theorem StronglySummable.regroup (hf : StronglySummable f) (q : ι → κ) :
    StronglySummable
      (fun b => strongSum (fun i : {i // q i = b} => f i.val) (hf.restrict _)) := by
  apply stronglySummable_of_hahnFamily (Surreal.HahnSeries.regroup hf.toHahnFamily q)
  intro b
  rw [rawNormalForm_strongSum]
  rfl

/-- The extracted regrouped family agrees with native Hahn regrouping. -/
theorem toHahnFamily_regroup (hf : StronglySummable f) (q : ι → κ) :
    (hf.regroup q).toHahnFamily = Surreal.HahnSeries.regroup hf.toHahnFamily q := by
  apply _root_.HahnSeries.SummableFamily.ext
  intro b
  change rawNormalForm (strongSum _ _) = _
  rw [rawNormalForm_strongSum]
  rfl

/-- Arbitrary regrouping of a small jointly summable family preserves its actual sum. -/
theorem strongSum_regroup [Small.{u} κ] (hf : StronglySummable f) (q : ι → κ) :
    strongSum
      (fun b => strongSum (fun i : {i // q i = b} => f i.val) (hf.restrict _))
      (hf.regroup q) = strongSum f hf := by
  apply rawNormalForm_injective
  rw [rawNormalForm_strongSum, rawNormalForm_strongSum, toHahnFamily_regroup,
    Surreal.HahnSeries.hsum_regroup]

/-- A bijective change of the index type preserves the actual strong sum. -/
theorem strongSum_reindex [Small.{u} κ] (hf : StronglySummable f) (e : κ ≃ ι) :
    strongSum (fun i => f (e i)) (hf.reindex e) = strongSum f hf := by
  apply rawNormalForm_injective
  rw [rawNormalForm_strongSum, rawNormalForm_strongSum]
  have hs : (hf.reindex e).toHahnFamily =
      _root_.HahnSeries.SummableFamily.Equiv e.symm hf.toHahnFamily := by
    apply _root_.HahnSeries.SummableFamily.ext
    intro i
    rfl
  rw [hs, _root_.HahnSeries.SummableFamily.hsum_equiv]

/-- Omitting only zero terms by an injective reindexing preserves the actual strong sum. -/
theorem strongSum_comp_injective [Small.{u} κ] (hf : StronglySummable f) (k : κ → ι)
    (hk : Function.Injective k) (hzero : ∀ n, n ∉ Set.range k → f n = 0) :
    strongSum (fun n => f (k n)) (hf.comp_injective k hk) = strongSum f hf := by
  apply rawNormalForm_injective
  rw [rawNormalForm_strongSum, rawNormalForm_strongSum]
  have he : hf.toHahnFamily = (hf.comp_injective k hk).toHahnFamily.embDomain ⟨k, hk⟩ := by
    apply _root_.HahnSeries.SummableFamily.ext
    intro n
    by_cases hn : n ∈ Set.range k
    · obtain ⟨m, rfl⟩ := hn
      exact (_root_.HahnSeries.SummableFamily.embDomain_image
        (hf.comp_injective k hk).toHahnFamily ⟨k, hk⟩ (a := m)).symm
    · rw [_root_.HahnSeries.SummableFamily.embDomain_notin_range
        (hf.comp_injective k hk).toHahnFamily ⟨k, hk⟩ hn]
      change rawNormalForm (f n) = 0
      rw [hzero n hn, rawNormalForm_zero]
  rw [he, _root_.HahnSeries.SummableFamily.hsum_embDomain]

end Small

end

end Surreal.Foundations.SignSequence
