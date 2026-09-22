import Mathlib.RingTheory.HahnSeries.Lex
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Surreal.HahnSeries.Regroup

/-!
# Strong Hahn measures with an atomic representation

This file formalizes the converse half of `meas:thm:atomic` and its consequences in
`docs/surreal/hahn-valued-measures-and-probability/article.tex`.

`meas:lem:sumalgebra` is proved for Hahn series over any linearly ordered
cancellative coefficient monoid: a strong sum of nonnegative series is
nonnegative, and positive as soon as one summand is positive. No divisibility
or countability assumption on the exponents is used.

`IsStrongHahnMeasure` is `meas:def:strong`: the empty set has mass zero, and every
pairwise disjoint measurable sequence has a strongly summable family of masses
whose Hahn sum is the mass of the union. A strongly summable family `w`
defines the set function `A ↦ ∑ˢ_{x ∈ A} w x` of equation (2) on all subsets.
It is a strong Hahn measure for every measurable structure. It is additive on
arbitrary set-indexed disjoint families (`meas:thm:atomic`(iv)), with the family of
masses constructed as a regrouping of `w`. Over ordered coefficients it is
positive exactly when every singleton mass is nonnegative.

Pushforwards and coefficientwise scalar integration (`meas:prop:integration`) are
proved for these atomic measures, with no boundedness or measurability
condition on the integrand. The atomicity theorem for arbitrary strong measures
on countably separated spaces, which requires the scalar Boolean-algebra lemmas,
is a separate obligation.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

section Positivity

variable {Γ R α : Type*} [LinearOrder Γ] [AddCommMonoid R] [LinearOrder R]
  [IsOrderedCancelAddMonoid R]

omit [IsOrderedCancelAddMonoid R] in
/-- A positive Hahn series has a first nonzero coefficient, and it is positive. -/
theorem exists_coeff_pos_of_pos {x : R⟦Γ⟧} (hx : 0 < toLex x) :
    ∃ i, (∀ j < i, x.coeff j = 0) ∧ 0 < x.coeff i := by
  obtain ⟨i, hi, hpos⟩ := (lt_iff _ _).mp hx
  refine ⟨i, fun j hj => ?_, by simpa using hpos⟩
  simpa using (hi j hj).symm

omit [IsOrderedCancelAddMonoid R] in
/-- The converse coefficient test for positivity in the lexicographic order. -/
theorem pos_of_coeff {x : R⟦Γ⟧} {i : Γ} (hi : ∀ j < i, x.coeff j = 0)
    (hpos : 0 < x.coeff i) : 0 < toLex x :=
  (lt_iff _ _).mpr ⟨i, fun j hj => by simpa using (hi j hj).symm, by simpa using hpos⟩

/-- `meas:lem:sumalgebra`, strict part: a strong sum of nonnegative Hahn series is
positive when one summand is positive. At the least exponent of the common
support, the only contributions are positive leading coefficients. -/
theorem hsum_pos (s : SummableFamily Γ R α) (hs : ∀ a, 0 ≤ toLex (s a)) {a₀ : α}
    (ha₀ : 0 < toLex (s a₀)) : 0 < toLex s.hsum := by
  classical
  have hwf : (⋃ a, (s a).support).IsWF := s.isPWO_iUnion_support.isWF
  obtain ⟨i₀, -, hi₀⟩ := exists_coeff_pos_of_pos ha₀
  have hne : (⋃ a, (s a).support).Nonempty :=
    ⟨i₀, Set.mem_iUnion.mpr ⟨a₀, (mem_support _ _).mpr hi₀.ne'⟩⟩
  set g := hwf.min hne with hg
  have hmin : ∀ a, ∀ j ∈ (s a).support, g ≤ j := fun a j hj =>
    hwf.min_le hne (Set.mem_iUnion.mpr ⟨a, hj⟩)
  have hbelow : ∀ a, ∀ j < g, (s a).coeff j = 0 := fun a j hj => by
    by_contra h
    exact (not_le.mpr hj) (hmin a j ((mem_support _ _).mpr h))
  -- Every nonzero coefficient at the least exponent is a positive leading coefficient.
  have hcoeff : ∀ a, (s a).coeff g ≠ 0 → 0 < (s a).coeff g := by
    intro a ha
    have hpos : 0 < toLex (s a) := by
      refine lt_of_le_of_ne (hs a) fun h => ha ?_
      rw [show s a = ofLex (toLex (s a)) from rfl, ← h]
      simp
    obtain ⟨i, hi, hlt⟩ := exists_coeff_pos_of_pos hpos
    rcases (hmin a i ((mem_support _ _).mpr hlt.ne')).lt_or_eq with h | h
    · exact absurd (hi g h) ha
    · exact h ▸ hlt
  have hnonneg : ∀ a, 0 ≤ (s a).coeff g := fun a => by
    by_cases ha : (s a).coeff g = 0
    · exact ha.ge
    · exact (hcoeff a ha).le
  obtain ⟨a₁, ha₁⟩ := Set.mem_iUnion.mp (hwf.min_mem hne)
  have ha₁' : (s a₁).coeff g ≠ 0 := (mem_support _ _).mp ha₁
  refine pos_of_coeff (i := g) (fun j hj => ?_) ?_
  · rw [SummableFamily.coeff_hsum]
    simp [hbelow _ j hj]
  · rw [SummableFamily.coeff_hsum_eq_sum]
    refine Finset.sum_pos' (fun a _ => hnonneg a) ⟨a₁, ?_, hcoeff a₁ ha₁'⟩
    simpa [SummableFamily.coeff_def] using ha₁'

/-- `meas:lem:sumalgebra`: a strong sum of nonnegative Hahn series is nonnegative. -/
theorem hsum_nonneg (s : SummableFamily Γ R α) (hs : ∀ a, 0 ≤ toLex (s a)) :
    0 ≤ toLex s.hsum := by
  by_cases h : ∃ a, s a ≠ 0
  · obtain ⟨a, ha⟩ := h
    refine (hsum_pos s hs (a₀ := a) (lt_of_le_of_ne (hs a) fun h => ha ?_)).le
    rw [show s a = ofLex (toLex (s a)) from rfl, ← h]
    simp
  · push Not at h
    have : s.hsum = 0 := by
      ext g
      simp [SummableFamily.coeff_hsum, h]
    simp [this]

end Positivity

section Atomic

variable {Γ R X Y ι : Type*} [PartialOrder Γ] [AddCommMonoid R]

/-- `meas:def:strong`: a strong Hahn measure on a measurable space. Every pairwise
disjoint measurable sequence has strongly summable masses, summing to the mass of
the union. No common support or valuation-topological continuity is imposed. -/
structure IsStrongHahnMeasure [MeasurableSpace X] (μ : Set X → R⟦Γ⟧) : Prop where
  empty : μ ∅ = 0
  iUnion : ∀ A : ℕ → Set X, (∀ n, MeasurableSet (A n)) → Pairwise (Function.onFun Disjoint A) →
    ∃ s : SummableFamily Γ R ℕ, (∀ n, s n = μ (A n)) ∧ μ (⋃ n, A n) = s.hsum

/-- Equation (2) of `meas:thm:atomic`: the strong sum of the singleton weights over
an arbitrary subset. -/
def atomicMeasure (w : SummableFamily Γ R X) (A : Set X) : R⟦Γ⟧ :=
  (restrict w A).hsum

/-- Each coefficient of an atomic mass is a finite sum of weight coefficients. -/
theorem coeff_atomicMeasure (w : SummableFamily Γ R X) (A : Set X) (g : Γ) :
    (atomicMeasure w A).coeff g = ∑ᶠ x ∈ A, (w x).coeff g := by
  rw [atomicMeasure, SummableFamily.coeff_hsum]
  exact finsum_set_coe_eq_finsum_mem (f := fun x => (w x).coeff g) A

@[simp]
theorem atomicMeasure_empty (w : SummableFamily Γ R X) : atomicMeasure w ∅ = 0 := by
  ext g
  simp [coeff_atomicMeasure]

/-- A singleton carries exactly its weight: `w x = μ({x})`. -/
@[simp]
theorem atomicMeasure_singleton (w : SummableFamily Γ R X) (x : X) :
    atomicMeasure w {x} = w x := by
  ext g
  simp [coeff_atomicMeasure]

@[simp]
theorem atomicMeasure_univ (w : SummableFamily Γ R X) :
    atomicMeasure w Set.univ = w.hsum := by
  ext g
  simp [coeff_atomicMeasure, SummableFamily.coeff_hsum]

/-- The member of a family containing a chosen point of its union. -/
def unionIndex (A : ι → Set X) (u : ↥(⋃ i, A i)) : ι :=
  (Set.mem_iUnion.mp u.2).choose

theorem mem_unionIndex (A : ι → Set X) (u : ↥(⋃ i, A i)) : u.1 ∈ A (unionIndex A u) :=
  (Set.mem_iUnion.mp u.2).choose_spec

theorem unionIndex_eq_iff {A : ι → Set X} (hA : Pairwise (Function.onFun Disjoint A))
    (u : ↥(⋃ i, A i)) (i : ι) : unionIndex A u = i ↔ u.1 ∈ A i := by
  constructor
  · rintro rfl
    exact mem_unionIndex A u
  · intro h
    by_contra hne
    exact Set.disjoint_left.mp (hA hne) (mem_unionIndex A u) h

/-- A fiber of the union index is the corresponding member of a disjoint family. -/
def unionFiberEquiv {A : ι → Set X} (hA : Pairwise (Function.onFun Disjoint A)) (i : ι) :
    ↥{u : ↥(⋃ i, A i) | unionIndex A u = i} ≃ A i where
  toFun u := ⟨u.1.1, (unionIndex_eq_iff hA u.1 i).mp u.2⟩
  invFun x := ⟨⟨x.1, Set.mem_iUnion.mpr ⟨i, x.2⟩⟩, (unionIndex_eq_iff hA _ i).mpr x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The masses of an arbitrary indexed family of sets, regrouped from the weights
of their union. Its values are the atomic masses when the family is disjoint. -/
def disjointFamily (w : SummableFamily Γ R X) (A : ι → Set X) : SummableFamily Γ R ι :=
  regroup (restrict w (⋃ i, A i)) (unionIndex A)

theorem disjointFamily_apply (w : SummableFamily Γ R X) {A : ι → Set X}
    (hA : Pairwise (Function.onFun Disjoint A)) (i : ι) :
    disjointFamily w A i = atomicMeasure w (A i) := by
  rw [disjointFamily, regroup_apply, atomicMeasure,
    ← SummableFamily.hsum_equiv (unionFiberEquiv hA i)]
  rfl

theorem hsum_disjointFamily (w : SummableFamily Γ R X) (A : ι → Set X) :
    (disjointFamily w A).hsum = atomicMeasure w (⋃ i, A i) :=
  hsum_regroup _ _

/-- `meas:thm:atomic`(iv): an atomic measure is additive on every set-indexed disjoint
family, with the sum interpreted strongly. -/
theorem atomicMeasure_iUnion (w : SummableFamily Γ R X) {A : ι → Set X}
    (hA : Pairwise (Function.onFun Disjoint A)) :
    ∃ s : SummableFamily Γ R ι, (∀ i, s i = atomicMeasure w (A i)) ∧
      atomicMeasure w (⋃ i, A i) = s.hsum :=
  ⟨disjointFamily w A, disjointFamily_apply w hA, (hsum_disjointFamily w A).symm⟩

/-- Finite additivity for two disjoint sets. -/
theorem atomicMeasure_union (w : SummableFamily Γ R X) {A B : Set X} (h : Disjoint A B) :
    atomicMeasure w (A ∪ B) = atomicMeasure w A + atomicMeasure w B := by
  classical
  ext g
  simp only [coeff_atomicMeasure, coeff_add]
  exact finsum_mem_union' h ((w.finite_co_support g).subset fun x hx => hx.2)
    ((w.finite_co_support g).subset fun x hx => hx.2)

/-- The converse half of `meas:thm:atomic`: every strongly summable family defines a
strong Hahn measure on all subsets, whatever measurable structure is used. -/
theorem isStrongHahnMeasure_atomicMeasure [MeasurableSpace X] (w : SummableFamily Γ R X) :
    IsStrongHahnMeasure (atomicMeasure w) where
  empty := atomicMeasure_empty w
  iUnion _ _ hA := by
    obtain ⟨s, hs, hsum⟩ := atomicMeasure_iUnion w hA
    exact ⟨s, hs, hsum⟩

/-- `meas:prop:integration`(i): the pushforward of an atomic measure is atomic, with
the fiber masses as weights. -/
theorem atomicMeasure_regroup (w : SummableFamily Γ R X) (f : X → Y) (B : Set Y) :
    atomicMeasure (regroup w f) B = atomicMeasure w (f ⁻¹' B) := by
  have hA : Pairwise (Function.onFun Disjoint fun y : B => f ⁻¹' {y.1}) := by
    intro y z hyz
    refine Set.disjoint_left.mpr fun x hy hz => hyz (Subtype.ext ?_)
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy hz
    exact hy.symm.trans hz
  have hU : (⋃ y : B, f ⁻¹' {y.1}) = f ⁻¹' B := by
    ext x
    simp
  rw [← hU, ← hsum_disjointFamily w _, atomicMeasure]
  congr 1
  ext y
  rw [disjointFamily_apply w hA]
  rfl

/-- `meas:prop:integration`(i): pushforward along any map is a strong Hahn measure. -/
theorem isStrongHahnMeasure_pushforward [MeasurableSpace Y] (w : SummableFamily Γ R X)
    (f : X → Y) : IsStrongHahnMeasure fun B => atomicMeasure w (f ⁻¹' B) := by
  simpa only [← atomicMeasure_regroup] using isStrongHahnMeasure_atomicMeasure (regroup w f)

/-- `meas:cor:cardinality`: the atomic set is the union, over exponents, of the finite
sets of points with a nonzero coefficient there. -/
theorem setOf_ne_zero_eq_iUnion (w : SummableFamily Γ R X) :
    {x | w x ≠ 0} = ⋃ g, {x | (w x).coeff g ≠ 0} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hx
    by_contra h
    push Not at h
    exact hx (HahnSeries.ext (funext h))
  · rintro ⟨g, hg⟩ hx
    simp [hx] at hg

theorem finite_setOf_coeff_ne_zero (w : SummableFamily Γ R X) (g : Γ) :
    {x | (w x).coeff g ≠ 0}.Finite :=
  w.finite_co_support g

end Atomic

section Positive

variable {Γ R X : Type*} [LinearOrder Γ] [AddCommMonoid R] [LinearOrder R]
  [IsOrderedCancelAddMonoid R]

/-- The positivity clause of `meas:thm:atomic`: an atomic measure is positive on all
subsets exactly when every singleton weight is nonnegative. -/
theorem atomicMeasure_nonneg_iff (w : SummableFamily Γ R X) :
    (∀ A, 0 ≤ toLex (atomicMeasure w A)) ↔ ∀ x, 0 ≤ toLex (w x) := by
  constructor
  · intro h x
    simpa using h {x}
  · intro h A
    exact hsum_nonneg _ fun x => h x.1

/-- A positive atomic measure is monotone. -/
theorem atomicMeasure_mono (w : SummableFamily Γ R X) (hw : ∀ x, 0 ≤ toLex (w x))
    {A B : Set X} (hAB : A ⊆ B) : toLex (atomicMeasure w A) ≤ toLex (atomicMeasure w B) := by
  have hB : B = A ∪ (B \ A) := (Set.union_sdiff_cancel hAB).symm
  rw [hB, atomicMeasure_union w Set.disjoint_sdiff_right, toLex_add]
  exact le_add_of_nonneg_right ((atomicMeasure_nonneg_iff w).mpr hw _)

end Positive

section Integration

variable {Γ R X : Type*} [PartialOrder Γ] [Semiring R]

/-- `meas:prop:integration`(ii): the coefficientwise integral `∑ˢ_x g(x) w_x` of an
arbitrary scalar function, with no boundedness or measurability hypothesis. -/
def atomicIntegral (w : SummableFamily Γ R X) (g : X → R) : R⟦Γ⟧ :=
  (SummableFamily.smulFamily g w).hsum

theorem coeff_atomicIntegral (w : SummableFamily Γ R X) (g : X → R) (γ : Γ) :
    (atomicIntegral w g).coeff γ = ∑ᶠ x, g x * (w x).coeff γ :=
  SummableFamily.hsum_smulFamily g w γ

theorem finite_support_mul_coeff (w : SummableFamily Γ R X) (g : X → R) (γ : Γ) :
    (Function.support fun x => g x * (w x).coeff γ).Finite :=
  (w.finite_co_support γ).subset fun x hx h =>
    Function.mem_support.mp hx (by simp only at h; rw [h, mul_zero])

theorem atomicIntegral_add (w : SummableFamily Γ R X) (g₁ g₂ : X → R) :
    atomicIntegral w (g₁ + g₂) = atomicIntegral w g₁ + atomicIntegral w g₂ := by
  ext γ
  simp only [coeff_atomicIntegral, coeff_add, Pi.add_apply, add_mul]
  exact finsum_add_distrib (finite_support_mul_coeff w g₁ γ) (finite_support_mul_coeff w g₂ γ)

/-- The integral is linear over the coefficient ring. -/
theorem atomicIntegral_const_mul (w : SummableFamily Γ R X) (c : R) (g : X → R) :
    atomicIntegral w (fun x => c * g x) = c • atomicIntegral w g := by
  ext γ
  rw [coeff_atomicIntegral, coeff_smul, coeff_atomicIntegral, smul_eq_mul,
    mul_finsum' _ _ (finite_support_mul_coeff w g γ)]
  simp only [mul_assoc]

/-- Integration of an indicator function recovers the atomic mass. -/
theorem atomicIntegral_indicator (w : SummableFamily Γ R X) (A : Set X) :
    atomicIntegral w (A.indicator 1) = atomicMeasure w A := by
  classical
  ext γ
  rw [coeff_atomicIntegral, coeff_atomicMeasure, finsum_mem_def]
  refine finsum_congr fun x => ?_
  by_cases hx : x ∈ A <;> simp [hx]

end Integration

section IntegrationPositive

variable {Γ R X : Type*} [LinearOrder Γ] [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Nonnegative scalars preserve lexicographic nonnegativity. -/
theorem smul_nonneg_toLex {c : R} {x : R⟦Γ⟧} (hc : 0 ≤ c) (hx : 0 ≤ toLex x) :
    0 ≤ toLex (c • x) := by
  rcases hc.eq_or_lt with rfl | hc
  · simp
  rcases hx.eq_or_lt with h | h
  · have : x = 0 := by
      rw [show x = ofLex (toLex x) from rfl, ← h]
      simp
    simp [this]
  obtain ⟨i, hi, hpos⟩ := exists_coeff_pos_of_pos h
  refine (pos_of_coeff (i := i) (fun j hj => ?_) ?_).le
  · simp [hi j hj]
  · simpa using mul_pos hc hpos

/-- `meas:prop:integration`(iii): a nonnegative integrand has nonnegative integral
against a positive atomic measure. -/
theorem atomicIntegral_nonneg (w : SummableFamily Γ R X) (hw : ∀ x, 0 ≤ toLex (w x))
    {g : X → R} (hg : ∀ x, 0 ≤ g x) : 0 ≤ toLex (atomicIntegral w g) :=
  hsum_nonneg _ fun x => smul_nonneg_toLex (hg x) (hw x)

end IntegrationPositive

end

end Surreal.HahnSeries
