import GRHArticle.ProgressionFree.NumberFieldIdeals.ProductSets
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Extremal densities of progression-free sets of ideals

The supremum of natural densities ranges over admissible sets for which
the relative norm-ball count converges. For upper density the same
normalization is used, with the limit superior at infinity.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Filter Topology
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- Upper natural density among all nonzero integral ideals in norm order. -/
noncomputable def idealUpperDensity (A : Set (Ideal (𝓞 K))⁰) : ℝ :=
  limsup (densityUpTo A) atTop

/-- The article's natural-density extremum for a specified ratio convention. -/
noncomputable def idealNaturalDensitySupremum (K : Type*) [Field K] [NumberField K]
    (integral : Bool) : ℝ :=
  sSup {d : ℝ | ∃ A : Set (Ideal (𝓞 K))⁰, IdealAdmissible integral A ∧ HasNaturalDensity A d}

/-- The article's upper-density extremum for a specified ratio convention. -/
noncomputable def idealUpperDensitySupremum (K : Type*) [Field K] [NumberField K]
    (integral : Bool) : ℝ :=
  sSup {d : ℝ | ∃ A : Set (Ideal (𝓞 K))⁰, IdealAdmissible integral A ∧ d = idealUpperDensity A}

theorem densityUpTo_mem_unitInterval (A : Set (Ideal (𝓞 K))⁰) {X : ℝ} (hX : 0 ≤ X) :
    0 ≤ densityUpTo A X ∧ densityUpTo A X ≤ 1 := by
  unfold densityUpTo
  refine ⟨by positivity,?_⟩
  have hc := countUpTo_mono (Set.subset_univ A) (le_refl X) hX
  by_cases h : countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) X = 0
  · simp [h]
  · apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))).mpr
    simpa only [one_mul, Nat.cast_le] using hc

theorem idealUpperDensity_le_one (A : Set (Ideal (𝓞 K))⁰) : idealUpperDensity A ≤ 1 := by
  apply limsup_le_of_le _ ((eventually_ge_atTop 0).mono fun _ h ↦ (densityUpTo_mem_unitInterval A h).2)
  exact (isBoundedUnder_of_eventually_ge ((eventually_ge_atTop 0).mono
    fun _ h ↦ (densityUpTo_mem_unitInterval A h).1)).isCoboundedUnder_le

/-- A lower bound along any sequence of real norm cutoffs tending to
infinity is a lower bound on the upper natural density. -/
theorem le_idealUpperDensity_of_tendsto_le {A : Set (Ideal (𝓞 K))⁰}
    {X f : ℕ → ℝ} {d : ℝ} (hX : Tendsto X atTop atTop) (hf : Tendsto f atTop (𝓝 d))
    (hle : ∀ᶠ j in atTop, f j ≤ densityUpTo A (X j)) : d ≤ idealUpperDensity A := by
  apply le_limsup_of_le (isBoundedUnder_of_eventually_le
    ((eventually_ge_atTop 0).mono fun _ h ↦ (densityUpTo_mem_unitInterval A h).2))
  intro b hb
  apply le_of_tendsto hf
  filter_upwards [hle, hX.eventually hb] with j h₁ h₂
  exact h₁.trans h₂

theorem le_idealNaturalDensitySupremum {integral : Bool} {A : Set (Ideal (𝓞 K))⁰} {d : ℝ}
    (hA : IdealAdmissible integral A) (hd : HasNaturalDensity A d) :
    d ≤ idealNaturalDensitySupremum K integral := by
  unfold idealNaturalDensitySupremum
  apply le_csSup
  · refine ⟨1,?_⟩
    rintro x ⟨B,_,hB⟩
    exact le_of_tendsto hB ((eventually_ge_atTop 0).mono fun _ h ↦ (densityUpTo_mem_unitInterval B h).2)
  · exact ⟨A,hA,hd⟩

theorem le_idealUpperDensitySupremum {integral : Bool} {A : Set (Ideal (𝓞 K))⁰}
    (hA : IdealAdmissible integral A) : idealUpperDensity A ≤ idealUpperDensitySupremum K integral := by
  unfold idealUpperDensitySupremum
  apply le_csSup
  · refine ⟨1,?_⟩
    rintro x ⟨B,_,rfl⟩
    exact idealUpperDensity_le_one B
  · exact ⟨A,hA,rfl⟩

theorem idealNaturalDensitySupremum_le_upper (integral : Bool) :
    idealNaturalDensitySupremum K integral ≤ idealUpperDensitySupremum K integral := by
  apply csSup_le
  · refine ⟨0,∅,fun _ _ _ ha ↦ ha.elim,?_⟩
    have he : densityUpTo (∅ : Set (Ideal (𝓞 K))⁰) = fun _ ↦ 0 := by
      funext X
      simp [densityUpTo,countUpTo]
    simp [HasNaturalDensity,he]
  · rintro _ ⟨A,hA,hd⟩
    exact (Filter.Tendsto.limsup_eq hd) ▸ le_idealUpperDensitySupremum hA

/-- Any smooth admissible template and admissible exterior rules give a
lower bound on the true natural-density supremum. Finitely many exterior
primes may exclude exponent one. -/
theorem idealProductSet_density_le_supremum (S E : Finset (HeightOneSpectrum (𝓞 K)))
    (integral : Bool) (F : Set (Ideal (𝓞 K))⁰) (hF : F ⊆ Set.range (smoothMultiplier S))
    (hf : IdealAdmissible integral F) (A : HeightOneSpectrum (𝓞 K) → Set ℕ)
    (h0 : ∀ p ∉ S, 0 ∈ A p) (h1 : ∀ p ∉ S, p ∉ E → 1 ∈ A p)
    (hA : ∀ p ∉ S, ThreeAPFree (A p)) :
    (∏ p ∈ S, (1-primeWeight p)) * (∑' J : F, (absNorm J.val.val : ℝ)⁻¹) *
      (∏' p : {p // p ∉ S}, localRuleMass p.val (A p.val)) ≤ idealNaturalDensitySupremum K integral :=
  le_idealNaturalDensitySupremum (idealProductSet_admissible S integral F hF hf A hA)
    (idealProductSet_density_of_finite_exceptions S E F hF A h0 h1)

end GRHArticle.ProgressionFree.NumberFieldIdeals
