import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Set.Countable
import Surreal.HahnSeries.ScalarAtomicity
import Surreal.Algebra.NonvanishingSelection

/-!
# Atomicity of strong Hahn measures with automatic common support

This file proves the forward half of `meas:thm:atomic` and `meas:cor:coefficient-test` in
`docs/surreal/hahn-valued-measures-and-probability/article.tex`; the converse of
`meas:thm:atomic` and additivity on set-indexed families are in `StrongMeasure.lean`.

The key hypothesis is that each coefficient function `A ↦ coeff_γ μ(A)` is a
finite combination of point masses; no common support and no strong additivity
are assumed. On a countably separated space this already makes the global
support well ordered: otherwise a strictly decreasing sequence of exponents would
carry nonzero coefficient measures, and the deterministic selection lemma gives
a countable, hence measurable, set whose mass has infinitely many of those
exponents in its support. At each exponent only finitely many singleton masses
contribute. Hence the singleton masses form a strongly summable family, every
event mass is the strong sum of the masses of its points, and the global support
equals the union of the supports of the singleton masses.

Every strong Hahn measure has finitely atomic coefficients by `meas:prop:coefficients`,
and conversely finitely atomic coefficients give a strong Hahn measure, which is
`meas:cor:coefficient-test`.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {X Γ R : Type*} [MeasurableSpace X] [LinearOrder Γ] [AddCommGroup R]
  {μ : Set X → R⟦Γ⟧}

omit [MeasurableSpace X] in
/-- The finite atomic representation agrees with the finitely supported functionals
of the selection lemma. -/
theorem finiteAtomic_eq_supportedSum (F : Finset X) (c : X → R) (A : Set X) :
    finiteAtomic F c A = Selection.supportedSum F c A := by
  unfold finiteAtomic Selection.supportedSum
  congr

/-- The global support `S(μ)`: all exponents occurring in some event mass. -/
def globalSupport (μ : Set X → R⟦Γ⟧) : Set Γ :=
  {γ | ∃ A, MeasurableSet A ∧ (μ A).coeff γ ≠ 0}

/-- Every coefficient function is the finite combination of its singleton masses. -/
def HasAtomicCoefficients (μ : Set X → R⟦Γ⟧) : Prop :=
  ∀ γ, ∃ F : Finset X, ∀ A, MeasurableSet A →
    (μ A).coeff γ = finiteAtomic F (fun x => (μ {x}).coeff γ) A

/-- A representation with arbitrary coefficients can use the singleton masses. -/
theorem hasAtomicCoefficients_of_exists (hX : IsCountablySeparated X)
    (h : ∀ γ, ∃ (F : Finset X) (c : X → R), ∀ A, MeasurableSet A →
      (μ A).coeff γ = finiteAtomic F c A) : HasAtomicCoefficients μ := by
  classical
  obtain ⟨E, hE, hsep⟩ := hX
  have hsing := measurableSet_singleton_of_separated hE hsep
  intro γ
  obtain ⟨F, c, hrep⟩ := h γ
  refine ⟨F, fun A hA => ?_⟩
  rw [hrep A hA]
  unfold finiteAtomic
  refine Finset.sum_congr rfl fun x hx => ?_
  change c x = (μ {x}).coeff γ
  rw [hrep _ (hsing x), finiteAtomic_singleton, if_pos (Finset.mem_filter.mp hx).1]

/-- `meas:prop:coefficients` in the form used below. -/
theorem hasAtomicCoefficients_of_isStrongHahnMeasure (hμ : IsStrongHahnMeasure μ)
    (hX : IsCountablySeparated X) : HasAtomicCoefficients μ := fun γ => by
  obtain ⟨F, -, hrep⟩ := coeff_eq_finiteAtomic hμ hX γ
  exact ⟨F, hrep⟩

variable (hμ : HasAtomicCoefficients μ) (hX : IsCountablySeparated X)
include hμ hX

omit hX in
/-- Every exponent of the global support has a point of nonzero coefficient. -/
theorem exists_singleton_coeff_ne_zero {γ : Γ} (hγ : γ ∈ globalSupport μ) :
    ∃ x, (μ {x}).coeff γ ≠ 0 := by
  classical
  obtain ⟨A, hA, hne⟩ := hγ
  obtain ⟨F, hrep⟩ := hμ γ
  rw [hrep A hA, finiteAtomic] at hne
  obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact ⟨x, hx⟩

/-- `meas:thm:atomic`(iii): the global support is well ordered. -/
theorem isWF_globalSupport : (globalSupport μ).IsWF := by
  classical
  obtain ⟨E, hE, hsep⟩ := hX
  have hsing := measurableSet_singleton_of_separated hE hsep
  rw [Set.isWF_iff_no_descending_seq]
  intro γ hanti hmem
  choose F hrep using fun n => hμ (γ n)
  have hne : ∀ n, ∃ x ∈ F n, (μ {x}).coeff (γ n) ≠ 0 := by
    intro n
    obtain ⟨A, hA, hA0⟩ := hmem n
    rw [hrep n A hA, finiteAtomic] at hA0
    obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hA0
    exact ⟨x, (Finset.mem_filter.mp hx).1, hx0⟩
  obtain ⟨A, hAsub, hinf⟩ := Selection.exists_infinite_ne_zero F
    (fun n x => (μ {x}).coeff (γ n)) hne
  -- A countable set of points is measurable.
  have hAcount : A.Countable :=
    (Set.countable_iUnion fun n => (F n).countable_toSet).mono hAsub
  have hAmeas : MeasurableSet A := by
    rw [← Set.biUnion_of_singleton A]
    exact MeasurableSet.biUnion hAcount fun x _ => hsing x
  -- Infinitely many of the decreasing exponents lie in the support of `μ A`.
  let I := {n | Selection.supportedSum (F n) (fun x => (μ {x}).coeff (γ n)) A ≠ 0}
  haveI : Infinite I := hinf.to_subtype
  let e := Nat.orderEmbeddingOfSet I
  have heI : ∀ m, e m ∈ I := fun m => by
    rw [← Nat.orderEmbeddingOfSet_range I]
    exact ⟨m, rfl⟩
  have hwf := (μ A).isWF_support
  rw [Set.isWF_iff_no_descending_seq] at hwf
  refine hwf (γ ∘ e) (hanti.comp_strictMono e.strictMono) fun m => ?_
  change (μ A).coeff (γ (e m)) ≠ 0
  rw [hrep _ A hAmeas, finiteAtomic_eq_supportedSum]
  exact heI m

/-- `meas:thm:atomic`(i): the singleton masses form a strongly summable family. -/
def atomFamily : SummableFamily Γ R X where
  toFun x := μ {x}
  isPWO_iUnion_support' := by
    obtain ⟨E, hE, hsep⟩ := hX
    have hsing := measurableSet_singleton_of_separated hE hsep
    refine (isWF_globalSupport hμ ⟨E, hE, hsep⟩).isPWO.mono (Set.iUnion_subset fun x => ?_)
    intro γ hγ
    exact ⟨{x}, hsing x, (mem_support _ _).mp hγ⟩
  finite_co_support' γ := by
    classical
    obtain ⟨F, hrep⟩ := hμ γ
    obtain ⟨E, hE, hsep⟩ := hX
    have hsing := measurableSet_singleton_of_separated hE hsep
    refine F.finite_toSet.subset fun x hx => ?_
    by_contra hxF
    apply hx
    rw [hrep _ (hsing x), finiteAtomic_singleton, if_neg fun h => hxF (Finset.mem_coe.mpr h)]

@[simp]
theorem atomFamily_apply (x : X) : atomFamily hμ hX x = μ {x} := rfl

/-- `meas:thm:atomic`(ii): every event mass is the strong sum of its singleton masses. -/
theorem eq_atomicMeasure {A : Set X} (hA : MeasurableSet A) :
    μ A = atomicMeasure (atomFamily hμ hX) A := by
  classical
  ext γ
  obtain ⟨F, hrep⟩ := hμ γ
  obtain ⟨E, hE, hsep⟩ := hX
  have hsing := measurableSet_singleton_of_separated hE hsep
  rw [hrep A hA, coeff_atomicMeasure, finiteAtomic,
    finsum_mem_eq_sum_of_subset _ (s := A) (t := F.filter (· ∈ A)) ?_ ?_]
  · rfl
  · intro x hx
    obtain ⟨hxA, hx0⟩ := hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    refine ⟨?_, hxA⟩
    by_contra hxF
    apply hx0
    change (μ {x}).coeff γ = 0
    rw [hrep _ (hsing x), finiteAtomic_singleton, if_neg hxF]
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
    exact hx.2

/-- `meas:thm:atomic`(iii): the global support is the union of the supports of the
singleton masses. -/
theorem globalSupport_eq_iUnion :
    globalSupport μ = ⋃ x, (μ {x}).support := by
  obtain ⟨E, hE, hsep⟩ := hX
  have hsing := measurableSet_singleton_of_separated hE hsep
  ext γ
  simp only [Set.mem_iUnion, mem_support]
  exact ⟨fun hγ => exists_singleton_coeff_ne_zero hμ hγ,
    fun ⟨x, hx⟩ => ⟨{x}, hsing x, hx⟩⟩

/-- Finitely atomic coefficients make `μ` a strong Hahn measure. -/
theorem isStrongHahnMeasure_of_hasAtomicCoefficients : IsStrongHahnMeasure μ where
  empty := by rw [eq_atomicMeasure hμ hX MeasurableSet.empty, atomicMeasure_empty]
  iUnion A hA hdisj := by
    obtain ⟨s, hs, hsum⟩ := atomicMeasure_iUnion (atomFamily hμ hX) hdisj
    refine ⟨s, fun n => by rw [hs, ← eq_atomicMeasure hμ hX (hA n)], ?_⟩
    rw [eq_atomicMeasure hμ hX (MeasurableSet.iUnion hA), hsum]

omit hμ in
/-- `meas:cor:coefficient-test`: on a countably separated space, a set function is a
strong Hahn measure exactly when every coefficient function is a finite linear
combination of point masses. No common support or strong additivity is assumed in
the second condition. -/
theorem isStrongHahnMeasure_iff :
    IsStrongHahnMeasure μ ↔ ∀ γ, ∃ (F : Finset X) (c : X → R), ∀ A, MeasurableSet A →
      (μ A).coeff γ = finiteAtomic F c A := by
  constructor
  · intro h γ
    obtain ⟨F, hrep⟩ := hasAtomicCoefficients_of_isStrongHahnMeasure h hX γ
    exact ⟨F, _, hrep⟩
  · intro h
    exact isStrongHahnMeasure_of_hasAtomicCoefficients
      (hasAtomicCoefficients_of_exists hX h) hX

end

end Surreal.HahnSeries
