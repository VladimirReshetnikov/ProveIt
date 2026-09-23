import Mathlib.Data.Rat.Floor
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.Topology.Algebra.FilterBasis
import Surreal.Algebra.MultiquadraticSigns
import Surreal.HahnSeries.FiniteBaseChange

/-!
# Closure of the algebraic coefficient part

This module proves `tail:thm:closure` of
`docs/surreal/tail-spans-and-differential-transcendence/article.tex` (Section
`tail:sec:approx`), together with the examples that follow it in the source.

Setting: `M ⊆ E` is an arbitrary field extension and `Γ` an arbitrary linearly ordered exponent
set, nonempty whenever a topology is involved. The source takes `E = M̄`, an algebraic closure of
a field `M` of characteristic zero, and `Γ` an ordered abelian group; the argument is
coefficientwise and uses none of these hypotheses.

* `algebraicPart M Γ E` is the set `𝒜 = ⋃_{F/M finite, F ⊆ E} F((t^Γ))` of
  `tail:eq:relativeunion`: the union, over the finite intermediate fields `F` of `E / M`, of the
  coefficientwise images of `F((t^Γ))` in `E((t^Γ))`. By `mem_algebraicPart_iff`, a series lies
  in `𝒜` iff all of its coefficients lie in one finite intermediate field.
* `valuationTopology Γ R` is the valuation topology on `R((t^Γ))`, the group topology of the
  additive filter basis of balls `{x | v(x) > γ}` (`valuationBasis`,
  `isTopologicalAddGroup_valuationTopology`). The neighbourhoods of `f` are the sets
  `{g | v(f - g) > γ}` (`hasBasis_nhds`), so closure is described by `mem_valuationClosure_iff`.
* `prefixField M f γ = M(c_η : η ≤ γ)` is the field of `tail:eq:prefixcriterion`. By
  `prefixField_eq_adjoin`, zero coefficients may be omitted from its generators.
* `mem_closure_algebraicPart_iff` is `tail:thm:closure`: `f ∈ E((t^Γ))` lies in the valuation
  closure of `𝒜` iff `[M(c_η : η ≤ γ) : M] < ∞` for every `γ ∈ Γ`. Its neighbourhood form is
  `forall_exists_algebraicPart_iff`. `mem_closure_algebraicPart_iff'` omits zero coefficients,
  and `mem_closure_algebraicPart_iff_algebraicClosure` is the instance `E = AlgebraicClosure M`.
  Necessity is `prefixField_le`: an approximant with `v(f - g) > γ` shares the coefficients of
  `f` through `γ`. For sufficiency the approximants are the truncations `truncLE f γ = f_{≤γ}`
  (`truncLE_mem_algebraicPart`), with `v(f - f_{≤γ}) > γ` (`lt_orderTop_sub_truncLE`). Every
  series is the valuation limit of its truncations (`tendsto_truncLE`), so under the criterion
  `f` is the limit of the elements `f_{≤γ}` of `𝒜` (`truncLE_mem_algebraicPart_and_tendsto`).

The examples after the theorem:

* `finiteDimensional_prefixField_of_finite` and
  `mem_closure_algebraicPart_of_support_subset_natCast`: for `Γ = ℚ`, a series supported in `ℕ`
  with algebraic coefficients satisfies the criterion, so it lies in the closure of `𝒜`; its
  truncations have finite support (`finite_support_truncLE_of_support_subset_natCast`). In
  particular `∑_{n ≥ 1} √p_n t^n` lies in the closure (`ratPrimeRootSeries_mem_closure`).
* `not_finiteDimensional_prefixField_of_sq` and `not_lt_orderTop_sub_of_sq`: if the
  coefficients through `γ` include the square roots of an infinite family with independent square
  classes (`tail:lem:signs`, from `Surreal.TailSigns`), the criterion fails at `γ` and no element
  of `𝒜` approximates `f` with error valuation greater than `γ`. Distinct primes have independent
  square classes in `ℚ` (`independentSquareClasses_prime`). For `Γ = ℚ ×ₗ ℚ` and
  `f = ∑_{n ≥ 1} √p_n t^{(0, n)}` this gives the failure of the criterion at the cutoff `(1, 0)`
  (`not_finiteDimensional_prefixField_lexPrimeRootSeries`), the absence of approximants with
  error valuation greater than `(1, 0)` (`not_lt_orderTop_lexPrimeRootSeries_sub`), and
  `lexPrimeRootSeries_notMem_closure`. The square roots are chosen in
  `AlgebraicClosure ℚ` (`sqrtPrime`); the source's positive real roots are one such choice, and
  the argument does not depend on the signs.

Pending: `𝒜` is identified with the relative algebraic closure of `M((t^Γ))` in `M̄((t^Γ))` only
by `tail:thm:coefficient`, which is not formalized. One inclusion is proved here: for a linearly
ordered cancellative exponent monoid `Γ`, every element of `𝒜` is integral over the
coefficientwise image of `M((t^Γ))` (`isIntegralElem_of_mem_algebraicPart`, from
`tail:lem:basechange`). The reverse inclusion needs `tail:thm:coefficient`. The theorem is
therefore proved for `𝒜` as defined by `tail:eq:relativeunion`, and the source's "no element
algebraic over the enlarged base" is proved for the elements of `𝒜`. The closing remark on the
surreal embedding `(a, b) ↦ aω + b` of value groups is not formalized.
-/

namespace Surreal.AlgebraicClosurePart

open _root_.HahnSeries Topology Pointwise

noncomputable section

section Truncation

variable {Γ R : Type*} [LinearOrder Γ]

/-- The truncation `f_{≤γ} = ∑_{η ≤ γ} c_η t^η` used in `tail:thm:closure`. -/
def truncLE [Zero R] (f : HahnSeries Γ R) (γ : Γ) : HahnSeries Γ R where
  coeff η := if η ≤ γ then f.coeff η else 0
  isPWO_support' := f.isPWO_support.mono fun η hη => by
    rw [Function.mem_support] at hη
    rw [mem_support]
    split_ifs at hη
    · exact hη
    · exact absurd rfl hη

@[simp]
theorem coeff_truncLE [Zero R] (f : HahnSeries Γ R) (γ η : Γ) :
    (truncLE f γ).coeff η = if η ≤ γ then f.coeff η else 0 := rfl

/-- The truncation `f_{≤γ}` either equals `f` or differs from it only beyond `γ`:
`v(f - f_{≤γ}) > γ`. -/
theorem lt_orderTop_sub_truncLE [AddGroup R] (f : HahnSeries Γ R) (γ : Γ) :
    (γ : WithTop Γ) < (f - truncLE f γ).orderTop := by
  by_contra h
  rw [not_lt] at h
  obtain ⟨η, hη⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top h)
  have hηγ : η ≤ γ := WithTop.coe_le_coe.mp (hη ▸ h)
  apply coeff_orderTop_ne hη.symm
  rw [coeff_sub, coeff_truncLE, if_pos hηγ, sub_self]

end Truncation

section Topology

variable {Γ R : Type*} [LinearOrder Γ] [AddCommGroup R]

/-- The valuation ball `{x | γ < v(x)}` around zero. -/
def ball (γ : Γ) : Set (HahnSeries Γ R) := {x | (γ : WithTop Γ) < x.orderTop}

variable (Γ R) in
/-- The valuation neighbourhoods `{x | γ < v(x)}` of zero, `γ ∈ Γ`, form an additive group
filter basis. -/
@[implicit_reducible]
def valuationBasis [Nonempty Γ] : AddGroupFilterBasis (HahnSeries Γ R) :=
  addGroupFilterBasisOfComm (Set.range ball) (Set.range_nonempty _)
    (by
      rintro _ _ ⟨γ₁, rfl⟩ ⟨γ₂, rfl⟩
      refine ⟨ball (max γ₁ γ₂), ⟨_, rfl⟩, fun x hx => ⟨?_, ?_⟩⟩
      · exact (WithTop.coe_le_coe.mpr (le_max_left γ₁ γ₂)).trans_lt hx
      · exact (WithTop.coe_le_coe.mpr (le_max_right γ₁ γ₂)).trans_lt hx)
    (by
      rintro _ ⟨γ, rfl⟩
      show (γ : WithTop Γ) < (0 : HahnSeries Γ R).orderTop
      rw [orderTop_zero]
      exact WithTop.coe_lt_top γ)
    (by
      rintro _ ⟨γ, rfl⟩
      refine ⟨ball γ, ⟨γ, rfl⟩, ?_⟩
      rintro _ ⟨x, hx, y, hy, rfl⟩
      have hxy := min_orderTop_le_orderTop_add (x := x) (y := y)
      exact lt_of_lt_of_le (lt_min hx hy) hxy)
    (by
      rintro _ ⟨γ, rfl⟩
      refine ⟨ball γ, ⟨γ, rfl⟩, fun x hx => ?_⟩
      show (γ : WithTop Γ) < (-x).orderTop
      rw [orderTop_neg]
      exact hx)

variable (Γ R) in
/-- The valuation topology on `R((t^Γ))`: the group topology whose neighbourhoods of `f` are
the sets `{g | v(f - g) > γ}`. -/
@[implicit_reducible]
def valuationTopology [Nonempty Γ] : TopologicalSpace (HahnSeries Γ R) :=
  (valuationBasis Γ R).topology

/-- Addition and negation are continuous for the valuation topology. -/
theorem isTopologicalAddGroup_valuationTopology [Nonempty Γ] :
    @IsTopologicalAddGroup (HahnSeries Γ R) (valuationTopology Γ R) _ :=
  (valuationBasis Γ R).isTopologicalAddGroup

theorem image_add_ball (f : HahnSeries Γ R) (γ : Γ) :
    (fun y => f + y) '' ball γ = {g | (γ : WithTop Γ) < (f - g).orderTop} := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    show (γ : WithTop Γ) < (f - (f + x)).orderTop
    rw [sub_add_cancel_left, orderTop_neg]
    exact hx
  · intro hg
    refine ⟨g - f, ?_, add_sub_cancel f g⟩
    show (γ : WithTop Γ) < (g - f).orderTop
    rw [← neg_sub, orderTop_neg]
    exact hg

/-- The valuation neighbourhoods of `f` are the sets `{g | v(f - g) > γ}`, `γ ∈ Γ`. -/
theorem hasBasis_nhds [Nonempty Γ] (f : HahnSeries Γ R) :
    (@nhds _ (valuationTopology Γ R) f).HasBasis (fun _ : Γ => True)
      fun γ => {g | (γ : WithTop Γ) < (f - g).orderTop} := by
  refine ((valuationBasis Γ R).nhds_hasBasis f).to_hasBasis ?_ ?_
  · intro V hV
    obtain ⟨γ, rfl⟩ := hV
    exact ⟨γ, trivial, (image_add_ball f γ).symm.subset⟩
  · exact fun γ _ => ⟨ball γ, ⟨γ, rfl⟩, (image_add_ball f γ).subset⟩

/-- Closure in the valuation topology: `f` lies in the closure of `S` iff every valuation
neighbourhood `{g | v(f - g) > γ}` meets `S`. -/
theorem mem_valuationClosure_iff [Nonempty Γ] {S : Set (HahnSeries Γ R)}
    {f : HahnSeries Γ R} :
    f ∈ closure[valuationTopology Γ R] S ↔
      ∀ γ : Γ, ∃ g ∈ S, (γ : WithTop Γ) < (f - g).orderTop := by
  letI := valuationTopology Γ R
  rw [mem_closure_iff_nhds_basis (hasBasis_nhds f)]
  simp only [forall_const, Set.mem_setOf_eq]

/-- Every series is the valuation limit of its truncations: `f_{≤γ} → f` as `γ → ∞`. -/
theorem tendsto_truncLE [Nonempty Γ] (f : HahnSeries Γ R) :
    Filter.Tendsto (truncLE f) Filter.atTop (@nhds _ (valuationTopology Γ R) f) := by
  refine (hasBasis_nhds f).tendsto_right_iff.mpr fun γ _ => ?_
  refine Filter.eventually_atTop.mpr ⟨γ, fun δ hδ => ?_⟩
  exact (WithTop.coe_le_coe.mpr hδ).trans_lt (lt_orderTop_sub_truncLE f δ)

end Topology

section Closure

variable (M : Type*) {Γ E : Type*} [Field M] [LinearOrder Γ] [Field E] [Algebra M E]

variable (Γ E) in
/-- `tail:eq:relativeunion`: the union, over the finite intermediate fields `F` of `E / M`, of
the coefficientwise images of `F((t^Γ))` in `E((t^Γ))`. -/
def algebraicPart : Set (HahnSeries Γ E) :=
  ⋃ (F : IntermediateField M E) (_ : FiniteDimensional M F),
    Set.range fun h : HahnSeries Γ F => h.map F.val

/-- A series lies in the algebraic part iff all of its coefficients lie in one finite
intermediate field. -/
theorem mem_algebraicPart_iff {g : HahnSeries Γ E} :
    g ∈ algebraicPart M Γ E ↔
      ∃ F : IntermediateField M E, FiniteDimensional M F ∧ ∀ η, g.coeff η ∈ F := by
  simp only [algebraicPart, Set.mem_iUnion, Set.mem_range]
  constructor
  · rintro ⟨F, hF, h, rfl⟩
    exact ⟨F, hF, fun η => (h.coeff η).2⟩
  · rintro ⟨F, hF, hg⟩
    refine ⟨F, hF,
      { coeff := fun η => ⟨g.coeff η, hg η⟩
        isPWO_support' := g.isPWO_support.mono fun η hη h0 => hη (Subtype.ext h0) }, ?_⟩
    ext η
    rfl

/-- The prefix coefficient field `M(c_η : η ≤ γ)` of `tail:eq:prefixcriterion`. -/
def prefixField (f : HahnSeries Γ E) (γ : Γ) : IntermediateField M E :=
  IntermediateField.adjoin M (f.coeff '' Set.Iic γ)

theorem coeff_mem_prefixField (f : HahnSeries Γ E) {γ η : Γ} (hη : η ≤ γ) :
    f.coeff η ∈ prefixField M f γ :=
  IntermediateField.subset_adjoin M _ ⟨η, hη, rfl⟩

/-- `tail:thm:closure`, last sentence: zero coefficients may be omitted from the generated
field. -/
theorem prefixField_eq_adjoin (f : HahnSeries Γ E) (γ : Γ) :
    prefixField M f γ =
      IntermediateField.adjoin M (f.coeff '' {η | η ≤ γ ∧ f.coeff η ≠ 0}) := by
  refine le_antisymm ?_ (IntermediateField.adjoin.mono _ _ _ (Set.image_mono fun η hη => hη.1))
  rw [prefixField, IntermediateField.adjoin_le_iff]
  rintro _ ⟨η, hη, rfl⟩
  by_cases h0 : f.coeff η = 0
  · rw [h0]
    exact zero_mem _
  · exact IntermediateField.subset_adjoin M _ ⟨η, ⟨hη, h0⟩, rfl⟩

/-- Necessity step of `tail:thm:closure`: if `v(f - g) > γ` and every coefficient of `g` lies in
`F`, then the coefficients of `f` through exponent `γ` lie in `F`. -/
theorem prefixField_le {f g : HahnSeries Γ E} {γ : Γ} {F : IntermediateField M E}
    (hg : ∀ η, g.coeff η ∈ F) (hfg : (γ : WithTop Γ) < (f - g).orderTop) :
    prefixField M f γ ≤ F := by
  rw [prefixField, IntermediateField.adjoin_le_iff]
  rintro _ ⟨η, hη, rfl⟩
  have h0 : (f - g).coeff η = 0 :=
    coeff_eq_zero_of_lt_orderTop ((WithTop.coe_le_coe.mpr hη).trans_lt hfg)
  rw [coeff_sub, sub_eq_zero] at h0
  rw [SetLike.mem_coe, h0]
  exact hg η

/-- Sufficiency step of `tail:thm:closure`: under the prefix criterion at `γ`, the truncation
`f_{≤γ}` lies in the algebraic part. -/
theorem truncLE_mem_algebraicPart {f : HahnSeries Γ E} {γ : Γ}
    (h : FiniteDimensional M (prefixField M f γ)) : truncLE f γ ∈ algebraicPart M Γ E := by
  refine (mem_algebraicPart_iff M).mpr ⟨prefixField M f γ, h, fun η => ?_⟩
  rw [coeff_truncLE]
  split_ifs with hη
  · exact coeff_mem_prefixField M f hη
  · exact zero_mem _

/-- `tail:thm:closure`, neighbourhood form: `f` can be approximated by the algebraic part with
error valuation greater than every `γ` iff all prefix coefficient fields are finite over `M`. -/
theorem forall_exists_algebraicPart_iff (f : HahnSeries Γ E) :
    (∀ γ : Γ, ∃ g ∈ algebraicPart M Γ E, (γ : WithTop Γ) < (f - g).orderTop) ↔
      ∀ γ : Γ, FiniteDimensional M (prefixField M f γ) := by
  constructor
  · intro h γ
    obtain ⟨g, hg, hfg⟩ := h γ
    obtain ⟨F, hF, hgF⟩ := (mem_algebraicPart_iff M).mp hg
    have hle := prefixField_le M hgF hfg
    exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  · intro h γ
    exact ⟨truncLE f γ, truncLE_mem_algebraicPart M (h γ), lt_orderTop_sub_truncLE f γ⟩

/-- `tail:thm:closure`: a series `f ∈ E((t^Γ))` lies in the valuation-topological closure of
the algebraic part `⋃_{F/M finite} F((t^Γ))` iff `[M(c_η : η ≤ γ) : M] < ∞` for every `γ`. -/
theorem mem_closure_algebraicPart_iff [Nonempty Γ] (f : HahnSeries Γ E) :
    f ∈ closure[valuationTopology Γ E] (algebraicPart M Γ E) ↔
      ∀ γ : Γ, FiniteDimensional M (prefixField M f γ) :=
  mem_valuationClosure_iff.trans (forall_exists_algebraicPart_iff M f)

/-- Sufficiency in `tail:thm:closure` as a limit statement: under the prefix criterion, every
truncation `f_{≤γ}` lies in the algebraic part, and these truncations converge to `f` in the
valuation topology. -/
theorem truncLE_mem_algebraicPart_and_tendsto [Nonempty Γ] {f : HahnSeries Γ E}
    (h : ∀ γ : Γ, FiniteDimensional M (prefixField M f γ)) :
    (∀ γ : Γ, truncLE f γ ∈ algebraicPart M Γ E) ∧
      Filter.Tendsto (truncLE f) Filter.atTop (@nhds _ (valuationTopology Γ E) f) :=
  ⟨fun γ => truncLE_mem_algebraicPart M (h γ), tendsto_truncLE f⟩

/-- `tail:thm:closure` with zero coefficients omitted from the generated fields. -/
theorem mem_closure_algebraicPart_iff' [Nonempty Γ] (f : HahnSeries Γ E) :
    f ∈ closure[valuationTopology Γ E] (algebraicPart M Γ E) ↔
      ∀ γ : Γ, FiniteDimensional M
        (IntermediateField.adjoin M (f.coeff '' {η | η ≤ γ ∧ f.coeff η ≠ 0})) := by
  rw [mem_closure_algebraicPart_iff]
  refine forall_congr' fun γ => ?_
  rw [prefixField_eq_adjoin]

/-- `tail:thm:closure` in the source's setting, with coefficients in an algebraic closure `M̄`
of `M` (characteristic zero is not needed). -/
theorem mem_closure_algebraicPart_iff_algebraicClosure [Nonempty Γ]
    (f : HahnSeries Γ (AlgebraicClosure M)) :
    f ∈ closure[valuationTopology Γ (AlgebraicClosure M)]
        (algebraicPart M Γ (AlgebraicClosure M)) ↔
      ∀ γ : Γ, FiniteDimensional M (prefixField M f γ) :=
  mem_closure_algebraicPart_iff M f

end Closure

section BaseChange

open Surreal.HahnSeries (mapCoefficients)

variable (M : Type*) {Γ E : Type*} [Field M] [AddCommMonoid Γ] [LinearOrder Γ]
  [IsOrderedCancelAddMonoid Γ] [Field E] [Algebra M E]

/-- One inclusion in the identification of `𝒜` with the relative algebraic closure: every element
of the algebraic part is integral over the coefficientwise image of `M((t^Γ))` in `E((t^Γ))`,
because `F((t^Γ))` is finite over `M((t^Γ))` for each finite `F / M`
(`Surreal.FiniteBaseChange.finite_hahn`). -/
theorem isIntegralElem_of_mem_algebraicPart {g : HahnSeries Γ E}
    (hg : g ∈ algebraicPart M Γ E) :
    (mapCoefficients (Γ := Γ) (algebraMap M E)).IsIntegralElem g := by
  simp only [algebraicPart, Set.mem_iUnion, Set.mem_range] at hg
  obtain ⟨F, hF, h, rfl⟩ := hg
  letI := Surreal.FiniteBaseChange.hahnBaseChangeAlgebra (Γ := Γ) (M := M) (F := F)
  haveI := Surreal.FiniteBaseChange.finite_hahn Γ M F
  obtain ⟨p, hp, hpe⟩ := Algebra.IsIntegral.isIntegral (R := HahnSeries Γ M) h
  refine ⟨p, hp, ?_⟩
  have hcomp : (mapCoefficients (Γ := Γ) (algebraMap F E)).comp
      (mapCoefficients (algebraMap M F)) = mapCoefficients (algebraMap M E) := by
    ext x η
    simp only [RingHom.comp_apply, Surreal.HahnSeries.coeff_mapCoefficients]
    exact (IsScalarTower.algebraMap_apply M F E (x.coeff η)).symm
  have hmap : h.map F.val = mapCoefficients (algebraMap F E) h := by
    ext η
    rfl
  rw [hmap, ← hcomp, ← Polynomial.hom_eval₂]
  exact (congrArg (mapCoefficients (algebraMap F E)) hpe).trans (map_zero _)

end BaseChange

section Criteria

variable (M : Type*) {Γ E : Type*} [Field M] [LinearOrder Γ] [Field E] [Algebra M E]

/-- A prefix with finitely many nonzero coefficients, all algebraic over `M`, generates a finite
extension of `M`. -/
theorem finiteDimensional_prefixField_of_finite {f : HahnSeries Γ E} {γ : Γ}
    (hfin : {η | η ≤ γ ∧ f.coeff η ≠ 0}.Finite) (hint : ∀ η ≤ γ, IsIntegral M (f.coeff η)) :
    FiniteDimensional M (prefixField M f γ) := by
  rw [prefixField_eq_adjoin]
  have : Finite (f.coeff '' {η | η ≤ γ ∧ f.coeff η ≠ 0}) := (hfin.image _).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun _ ⟨η, hη, he⟩ => he ▸ hint η hη.1

/-- For `Γ = ℚ`, a series supported in the natural numbers has only finitely many nonzero
coefficients at exponents `η ≤ γ`. -/
theorem finite_setOf_le_of_support_subset_natCast {f : HahnSeries ℚ E}
    (hf : f.support ⊆ Set.range (Nat.cast : ℕ → ℚ)) (γ : ℚ) :
    {η | η ≤ γ ∧ f.coeff η ≠ 0}.Finite := by
  refine ((Set.finite_Iic ⌊γ⌋₊).image (Nat.cast : ℕ → ℚ)).subset ?_
  rintro η ⟨hηγ, hη⟩
  obtain ⟨n, rfl⟩ := hf hη
  exact ⟨n, Nat.le_floor hηγ, rfl⟩

/-- For `Γ = ℚ`, the truncations `f_{≤γ}` of a series supported in the natural numbers have
finite support. -/
theorem finite_support_truncLE_of_support_subset_natCast {f : HahnSeries ℚ E}
    (hf : f.support ⊆ Set.range (Nat.cast : ℕ → ℚ)) (γ : ℚ) : (truncLE f γ).support.Finite := by
  refine (finite_setOf_le_of_support_subset_natCast hf γ).subset fun η hη => ?_
  rw [mem_support, coeff_truncLE] at hη
  split_ifs at hη with hηγ
  · exact ⟨hηγ, hη⟩
  · exact absurd rfl hη

/-- The example after `tail:thm:closure` for `Γ = ℚ`: a series supported in the natural numbers
with algebraic coefficients satisfies the prefix criterion (below any rational cutoff there are
only finitely many exponents), so it lies in the valuation closure of the algebraic part. The
approximants are its truncations `f_{≤γ}`: they have finite support
(`finite_support_truncLE_of_support_subset_natCast`), lie in the algebraic part and converge
to `f` (`truncLE_mem_algebraicPart_and_tendsto`). -/
theorem mem_closure_algebraicPart_of_support_subset_natCast {f : HahnSeries ℚ E}
    (hf : f.support ⊆ Set.range (Nat.cast : ℕ → ℚ)) (hint : ∀ η, IsIntegral M (f.coeff η)) :
    f ∈ closure[valuationTopology ℚ E] (algebraicPart M ℚ E) :=
  (mem_closure_algebraicPart_iff M f).mpr fun γ =>
    finiteDimensional_prefixField_of_finite M (finite_setOf_le_of_support_subset_natCast hf γ)
      fun η _ => hint η

open Surreal.TailSigns in
/-- The obstruction behind the example after `tail:thm:closure`: if the coefficients of `f`
through exponent `γ` include square roots `r_i` of a family with independent square classes
indexed by an infinite set, then `M(c_η : η ≤ γ)` is an infinite extension of `M`. -/
theorem not_finiteDimensional_prefixField_of_sq {I : Type*} [Infinite I] {a : I → M}
    {r : I → E} (hr : ∀ i, r i ^ 2 = algebraMap M E (a i)) (ha : IndependentSquareClasses a)
    (h2 : (2 : M) ≠ 0) {f : HahnSeries Γ E} {γ : Γ}
    (hcoeff : ∀ i, ∃ η ≤ γ, f.coeff η = r i) :
    ¬ FiniteDimensional M (prefixField M f γ) := by
  intro hfin
  have hle : IntermediateField.adjoin M (r '' Set.univ) ≤ prefixField M f γ := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, -, rfl⟩
    obtain ⟨η, hη, he⟩ := hcoeff i
    rw [← he]
    exact coeff_mem_prefixField M f hη
  have hA : FiniteDimensional M (IntermediateField.adjoin M (r '' Set.univ)) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  have : Infinite {U : Finset I // (U : Set I) ⊆ Set.univ} :=
    Infinite.of_injective (fun i => ⟨{i}, Set.subset_univ _⟩) fun i j h => by
      simpa using congrArg Subtype.val h
  exact Module.not_finite_of_infinite_basis (adjoinBasis hr ha h2 Set.univ) hA

open Surreal.TailSigns in
/-- Under the hypotheses of `not_finiteDimensional_prefixField_of_sq`, no element of the
algebraic part approximates `f` with error valuation greater than `γ`. -/
theorem not_lt_orderTop_sub_of_sq {I : Type*} [Infinite I] {a : I → M}
    {r : I → E} (hr : ∀ i, r i ^ 2 = algebraMap M E (a i)) (ha : IndependentSquareClasses a)
    (h2 : (2 : M) ≠ 0) {f : HahnSeries Γ E} {γ : Γ}
    (hcoeff : ∀ i, ∃ η ≤ γ, f.coeff η = r i) {g : HahnSeries Γ E}
    (hg : g ∈ algebraicPart M Γ E) : ¬ (γ : WithTop Γ) < (f - g).orderTop := by
  intro hfg
  obtain ⟨F, hF, hgF⟩ := (mem_algebraicPart_iff M).mp hg
  have hle := prefixField_le M hgF hfg
  exact not_finiteDimensional_prefixField_of_sq M hr ha h2 hcoeff
    (FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle))

end Criteria

section PrimeExamples

/-- Distinct primes have independent square classes in `ℚ`: no product of finitely many
distinct primes is a rational square. -/
theorem independentSquareClasses_prime {I : Type*} {p : I → ℕ} (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) :
    Surreal.TailSigns.IndependentSquareClasses fun i => (p i : ℚ) := by
  intro J hJ hsq
  have hsq' : IsSquare (∏ i ∈ J, p i) := by
    rw [← Rat.isSquare_natCast_iff, Nat.cast_prod]
    exact hsq
  obtain ⟨m, hm⟩ := hsq'
  have hsf : Squarefree (∏ i ∈ J, p i) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun i _ j _ hij => ?_)
      fun i _ => Irreducible.squarefree (hp i)
    show IsRelPrime (p i) (p j)
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hp i) (hp j)).mpr (hinj.ne hij)
  have hm1 : m = 1 := Nat.isUnit_iff.mp (hsf m ⟨1, by rw [mul_one]; exact hm⟩)
  obtain ⟨i, hi⟩ := hJ
  have hdvd : p i ∣ ∏ j ∈ J, p j := Finset.dvd_prod_of_mem p hi
  rw [hm, hm1, mul_one] at hdvd
  exact (hp i).one_lt.ne' (Nat.dvd_one.mp hdvd)

/-- A chosen square root `√p_{n+1}` of the `(n + 1)`st prime `p_{n+1} = nth Prime n` in the
algebraic closure of `ℚ`. -/
def sqrtPrime (n : ℕ) : AlgebraicClosure ℚ :=
  Classical.choose
    (IsAlgClosed.exists_pow_nat_eq (algebraMap ℚ (AlgebraicClosure ℚ) (Nat.nth Nat.Prime n))
      two_pos)

theorem sqrtPrime_sq (n : ℕ) :
    sqrtPrime n ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) (Nat.nth Nat.Prime n) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq _ two_pos)

/-- The coefficient sequence `(√p_{n+1})_{n ∈ ℕ}` as a Hahn series over `ℕ`. -/
def primeRootSeries : HahnSeries ℕ (AlgebraicClosure ℚ) :=
  toPowerSeries.symm (PowerSeries.mk sqrtPrime)

theorem coeff_primeRootSeries (n : ℕ) : primeRootSeries.coeff n = sqrtPrime n := by
  rw [primeRootSeries, coeff_toPowerSeries_symm, PowerSeries.coeff_mk]

/-- The exponents `1, 2, 3, …` in `ℚ`. -/
def ratExponent : ℕ ↪o ℚ :=
  OrderEmbedding.ofStrictMono (fun n => (n : ℚ) + 1) fun a b h => by simpa using h

/-- The exponents `(0, 1), (0, 2), (0, 3), …` in the lexicographic group `ℚ ×ₗ ℚ`. -/
def lexExponent : ℕ ↪o Lex (ℚ × ℚ) :=
  OrderEmbedding.ofStrictMono (fun n => toLex ((0 : ℚ), (n : ℚ) + 1)) fun a b h =>
    Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, by simpa using h⟩)

/-- The series `∑_{n ≥ 1} √p_n t^n` over `ℚ`. -/
def ratPrimeRootSeries : HahnSeries ℚ (AlgebraicClosure ℚ) :=
  embDomain ratExponent primeRootSeries

/-- The series `∑_{n ≥ 1} √p_n t^{(0, n)}` over `ℚ ×ₗ ℚ`. -/
def lexPrimeRootSeries : HahnSeries (Lex (ℚ × ℚ)) (AlgebraicClosure ℚ) :=
  embDomain lexExponent primeRootSeries

theorem coeff_ratPrimeRootSeries (n : ℕ) :
    ratPrimeRootSeries.coeff ((n : ℚ) + 1) = sqrtPrime n := by
  rw [ratPrimeRootSeries, ← coeff_primeRootSeries n]
  exact embDomain_coeff (f := ratExponent)

theorem coeff_ratPrimeRootSeries_eq_zero {η : ℚ} (hη : ∀ n : ℕ, η ≠ (n : ℚ) + 1) :
    ratPrimeRootSeries.coeff η = 0 :=
  embDomain_notin_range fun ⟨n, hn⟩ => hη n hn.symm

theorem coeff_lexPrimeRootSeries (n : ℕ) :
    lexPrimeRootSeries.coeff (toLex ((0 : ℚ), (n : ℚ) + 1)) = sqrtPrime n := by
  rw [lexPrimeRootSeries, ← coeff_primeRootSeries n]
  exact embDomain_coeff (f := lexExponent)

theorem coeff_lexPrimeRootSeries_eq_zero {η : Lex (ℚ × ℚ)}
    (hη : ∀ n : ℕ, η ≠ toLex ((0 : ℚ), (n : ℚ) + 1)) : lexPrimeRootSeries.coeff η = 0 :=
  embDomain_notin_range fun ⟨n, hn⟩ => hη n hn.symm

/-- The example after `tail:thm:closure`: for `Γ = ℚ`, the series `∑_{n ≥ 1} √p_n t^n` lies in
the valuation closure of the algebraic part. -/
theorem ratPrimeRootSeries_mem_closure :
    ratPrimeRootSeries ∈ closure[valuationTopology ℚ (AlgebraicClosure ℚ)]
      (algebraicPart ℚ ℚ (AlgebraicClosure ℚ)) := by
  refine mem_closure_algebraicPart_of_support_subset_natCast ℚ ?_
    fun η => Algebra.IsIntegral.isIntegral _
  intro η hη
  obtain ⟨n, -, rfl⟩ := support_embDomain_subset hη
  exact ⟨n + 1, by simp [ratExponent]⟩

/-- The example after `tail:thm:closure` for the enlarged group `Γ = ℚ ×ₗ ℚ`: every exponent of
`∑_{n ≥ 1} √p_n t^{(0, n)}` lies below `(1, 0)`, so the prefix coefficient field at that cutoff
contains every `√p_n` and is an infinite extension of `ℚ`; the prefix criterion fails there. -/
theorem not_finiteDimensional_prefixField_lexPrimeRootSeries :
    ¬ FiniteDimensional ℚ (prefixField ℚ lexPrimeRootSeries (toLex ((1 : ℚ), (0 : ℚ)))) :=
  not_finiteDimensional_prefixField_of_sq ℚ (I := ℕ) sqrtPrime_sq
    (independentSquareClasses_prime Nat.prime_nth_prime
      (Nat.nth_injective Nat.infinite_setOf_prime)) two_ne_zero fun n =>
    ⟨lexExponent n, (Prod.Lex.toLex_lt_toLex.mpr (Or.inl zero_lt_one)).le, by
      rw [lexPrimeRootSeries, embDomain_coeff, coeff_primeRootSeries]⟩

/-- The example after `tail:thm:closure` for the enlarged group `Γ = ℚ ×ₗ ℚ`: no element of the
algebraic part approximates `∑_{n ≥ 1} √p_n t^{(0, n)}` with error valuation greater than
`(1, 0)`. -/
theorem not_lt_orderTop_lexPrimeRootSeries_sub {g : HahnSeries (Lex (ℚ × ℚ)) (AlgebraicClosure ℚ)}
    (hg : g ∈ algebraicPart ℚ (Lex (ℚ × ℚ)) (AlgebraicClosure ℚ)) :
    ¬ ((toLex ((1 : ℚ), (0 : ℚ)) : Lex (ℚ × ℚ)) : WithTop (Lex (ℚ × ℚ))) <
      (lexPrimeRootSeries - g).orderTop := by
  refine not_lt_orderTop_sub_of_sq ℚ (I := ℕ) sqrtPrime_sq
    (independentSquareClasses_prime Nat.prime_nth_prime
      (Nat.nth_injective Nat.infinite_setOf_prime)) two_ne_zero (fun n => ?_) hg
  refine ⟨lexExponent n, (Prod.Lex.toLex_lt_toLex.mpr (Or.inl zero_lt_one)).le, ?_⟩
  rw [lexPrimeRootSeries, embDomain_coeff, coeff_primeRootSeries]

/-- Consequently `∑_{n ≥ 1} √p_n t^{(0, n)}` does not lie in the valuation closure of the
algebraic part over `ℚ ×ₗ ℚ`, since the prefix criterion of `tail:thm:closure` fails at the
cutoff `(1, 0)` (`not_finiteDimensional_prefixField_lexPrimeRootSeries`). -/
theorem lexPrimeRootSeries_notMem_closure :
    lexPrimeRootSeries ∉ closure[valuationTopology (Lex (ℚ × ℚ)) (AlgebraicClosure ℚ)]
      (algebraicPart ℚ (Lex (ℚ × ℚ)) (AlgebraicClosure ℚ)) := fun h =>
  not_finiteDimensional_prefixField_lexPrimeRootSeries
    ((mem_closure_algebraicPart_iff ℚ lexPrimeRootSeries).mp h _)

end PrimeExamples

end

end Surreal.AlgebraicClosurePart
