import Mathlib.Algebra.Polynomial.BigOperators
import Surreal.HahnSeries.StrongMeasureShadow

/-!
# Finite visibility detects a negative atom

This file formalizes `meas:thm:visibility`, `meas:cor:hidden-necessary`,
`meas:cor:safesupport` and `meas:prop:integration`(iv) of
`docs/surreal/hahn-valued-measures-and-probability/article.tex`.

The ordinary real sample set `Ω ⊆ ℝ` is modelled by an index type `X` with an injective
position map `e : X → K` into a linearly ordered commutative ring `K` (for instance
`K = ℝ` and `e` the inclusion of a subset). A signed strong Hahn measure is represented
by its strongly summable family `w` of point weights, as in `meas:thm:atomic`; the
exponents `Γ` form any linearly ordered cancellative additive monoid, and only a linear
order on `Γ` is used for the detector itself.

* `meas:prop:integration`(iv): for a polynomial `P` with Hahn coefficients the family
  `(P(e x) w_x)_x` is strongly summable (`polyFamily`, `polyFamily_apply`), and
  `L(P) = ∫ P dμ` is the finite combination `∑_j b_j ∫ x^j dμ` (`polyIntegral_eq_sum`).
  On real polynomials it agrees with the scalar integral of `meas:prop:integration`(ii)
  (`polyIntegral_map_C`).
* `meas:eq:visible` and `meas:thm:visibility`: the visible atoms
  `D_γ = {x | w_x ≠ 0, v(w_x) ≤ γ}` (`visibleAtoms`). If `w_{x₀} < 0`, `γ = v(w_{x₀})`
  and `D_γ` is finite, then `p = ∏_{y ∈ D_γ \ {x₀}} (X - e y)`, of degree `|D_γ| - 1`,
  has `L(p²) < 0` (`exists_sq_atomicIntegral_neg`, `exists_sq_polyIntegral_neg`). When every
  `D_γ` is finite, positivity of the measure, positivity of `L` on real polynomial
  squares and positivity of `L` on squares of Hahn-coefficient polynomials are
  equivalent (`nonneg_tfae`).
* `meas:cor:hidden-necessary`: under positivity on real polynomial squares every negative
  atom has infinitely many atoms of strictly smaller valuation
  (`infinite_earlier_atoms`).
* `meas:cor:safesupport`: if every element of `S = ⋃_x supp w_x` has finitely many
  predecessors in `S`, positivity on real polynomial squares implies positivity of the
  measure (`nonneg_of_finite_predecessors`). The finite-predecessor condition is
  equivalent to an order embedding `S ↪o ℕ`, that is `ot(S) ≤ ω`
  (`finite_predecessors_iff_nonempty_orderEmbedding`, `nonneg_of_orderEmbedding_nat`),
  and a globally left-finite support has it (`nonneg_of_leftFinite`).

The hypotheses of the two corollaries are stated with the scalar integral
`∫ p² dμ = atomicIntegral w (fun x => p.eval (e x) ^ 2)` of `meas:prop:integration`(ii),
whereas clause 2 of `nonneg_tfae` uses `L(p²) = polyIntegral w e (p.map C ^ 2)`; the two
agree by `polyIntegral_map_C_sq`.

For an arbitrary strong Hahn measure on a countably separated space the point weights are
`strongWeights` (`meas:thm:atomic`); `measure_nonneg_tfae`, `measure_infinite_earlier_atoms`
and `measure_nonneg_of_finite_predecessors` restate the equivalence, `meas:cor:hidden-necessary`
and the finite-predecessor form of `meas:cor:safesupport` for the measure itself. The first
assertion of `meas:thm:visibility` and the `ot(S) ≤ ω` and left-finite forms of
`meas:cor:safesupport` have no separate measure-level statement; they follow by
instantiating `w := strongWeights hμ hX`.

All statements are proved at the stated generality; nothing in `meas:thm:visibility`,
`meas:cor:hidden-necessary`, `meas:cor:safesupport` or `meas:prop:integration`(iv) is
left pending. Of `meas:prop:integration` only part (iv) is proved here; the scalar integral
of part (ii) is `atomicIntegral` from `Surreal.HahnSeries.StrongMeasure`.
-/

namespace Surreal.FiniteVisibility

open _root_.HahnSeries Surreal.HahnSeries
open scoped Polynomial

noncomputable section

section Leading

variable {Γ R : Type*} [LinearOrder Γ] [Zero R] [LinearOrder R]

/-- A lexicographically negative Hahn series is nonzero. -/
theorem ne_zero_of_toLex_neg {x : R⟦Γ⟧} (h : toLex x < 0) : x ≠ 0 := by
  rintro rfl
  simp at h

omit [LinearOrder R] in
/-- A nonzero Hahn series has a valuation in `Γ`. -/
theorem exists_orderTop_eq_of_ne_zero {x : R⟦Γ⟧} (hx : x ≠ 0) :
    ∃ γ : Γ, x.orderTop = γ := by
  obtain ⟨γ, hγ⟩ := WithTop.ne_top_iff_exists.mp (orderTop_ne_top.mpr hx)
  exact ⟨γ, hγ.symm⟩

/-- The coefficient test for negativity in the lexicographic order. -/
theorem neg_of_coeff {x : R⟦Γ⟧} {i : Γ} (hi : ∀ j < i, x.coeff j = 0) (hneg : x.coeff i < 0) :
    toLex x < 0 :=
  (lt_iff _ _).mpr ⟨i, fun j hj => by simpa using hi j hj, by simpa using hneg⟩

/-- A negative Hahn series has a negative coefficient at its valuation. -/
theorem coeff_neg_of_toLex_neg {x : R⟦Γ⟧} (h : toLex x < 0) {γ : Γ} (hγ : x.orderTop = γ) :
    x.coeff γ < 0 := by
  obtain ⟨i, hi, hlt⟩ := (lt_iff _ _).mp h
  have hi' : ∀ j < i, x.coeff j = 0 := fun j hj => by simpa using hi j hj
  have hlt' : x.coeff i < 0 := by simpa using hlt
  have hle : x.orderTop ≤ i := orderTop_le_of_coeff_ne_zero hlt'.ne
  rw [hγ, WithTop.coe_le_coe] at hle
  rcases hle.lt_or_eq with h' | h'
  · exact absurd (hi' γ h') (coeff_orderTop_ne hγ)
  · rwa [h']

end Leading

section Visible

variable {Γ K X : Type*} [LinearOrder Γ] [CommRing K]

/-- `meas:eq:visible`: the atoms visible by scale `γ`,
`D_γ = {x | w_x ≠ 0, v(w_x) ≤ γ}`. -/
def visibleAtoms (w : SummableFamily Γ K X) (γ : Γ) : Set X :=
  {x | w x ≠ 0 ∧ (w x).orderTop ≤ (γ : WithTop Γ)}

theorem mem_visibleAtoms {w : SummableFamily Γ K X} {γ : Γ} {x : X} :
    x ∈ visibleAtoms w γ ↔ w x ≠ 0 ∧ (w x).orderTop ≤ (γ : WithTop Γ) :=
  Iff.rfl

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- `meas:thm:visibility`, first assertion, for the scalar integral of
`meas:prop:integration`(ii): if `w_{x₀} < 0`, `γ = v(w_{x₀})` and `D_γ` is finite, the
real polynomial `p = ∏_{y ∈ D_γ \ {x₀}} (X - e y)`, of degree `|D_γ| - 1`, satisfies
`∫ p² dμ < 0`. Below `γ` every contributing atom is visible and different from `x₀`, so
`p` kills it; at `γ` only `x₀` survives, with coefficient `p(e x₀)² c_{γ,x₀} < 0`. -/
theorem exists_sq_atomicIntegral_neg (w : SummableFamily Γ K X) {e : X → K}
    (he : Function.Injective e) {x₀ : X} (hneg : toLex (w x₀) < 0) {γ : Γ}
    (hγ : (w x₀).orderTop = γ) (hfin : (visibleAtoms w γ).Finite) :
    ∃ p : K[X], p.natDegree + 1 = hfin.toFinset.card ∧
      toLex (atomicIntegral w fun x => p.eval (e x) ^ 2) < 0 := by
  classical
  set D := hfin.toFinset with hD
  have hx₀ : x₀ ∈ D := by
    rw [hD, Set.Finite.mem_toFinset]
    exact ⟨ne_zero_of_toLex_neg hneg, hγ.le⟩
  set p : K[X] := ∏ y ∈ D.erase x₀, (Polynomial.X - Polynomial.C (e y)) with hp
  refine ⟨p, ?_, ?_⟩
  · rw [hp, Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_erase_add_one hx₀]
  have hzero : ∀ y ∈ D.erase x₀, p.eval (e y) = 0 := by
    intro y hy
    rw [hp, Polynomial.eval_prod]
    exact Finset.prod_eq_zero hy (by simp)
  have hne : p.eval (e x₀) ≠ 0 := by
    rw [hp, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
    intro y hy
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_ne_zero.mpr fun h => Finset.ne_of_mem_erase hy (he h).symm
  -- At every exponent up to `γ` only the atom `x₀` contributes.
  have hcoeff : ∀ δ : Γ, δ ≤ γ → (atomicIntegral w fun x => p.eval (e x) ^ 2).coeff δ =
      p.eval (e x₀) ^ 2 * (w x₀).coeff δ := by
    intro δ hδ
    rw [coeff_atomicIntegral]
    refine finsum_eq_single (fun x => p.eval (e x) ^ 2 * (w x).coeff δ) x₀ fun x hx => ?_
    by_cases hc : (w x).coeff δ = 0
    · simp only [hc, mul_zero]
    · have hxD : x ∈ D.erase x₀ := by
        refine Finset.mem_erase.mpr ⟨hx, ?_⟩
        rw [hD, Set.Finite.mem_toFinset]
        exact ⟨ne_zero_of_coeff_ne_zero hc,
          (orderTop_le_of_coeff_ne_zero hc).trans (WithTop.coe_le_coe.mpr hδ)⟩
      simp only [hzero x hxD, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        zero_mul]
  refine neg_of_coeff (i := γ) (fun j hj => ?_) ?_
  · rw [hcoeff j hj.le, coeff_eq_zero_of_lt_orderTop (by rw [hγ]; exact WithTop.coe_lt_coe.mpr hj),
      mul_zero]
  · rw [hcoeff γ le_rfl]
    exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hne) (coeff_neg_of_toLex_neg hneg hγ)

/-- `meas:cor:hidden-necessary`: if a signed strong measure is nonnegative on all real
polynomial squares, every negative atom has infinitely many distinct atoms of strictly
smaller valuation. Only finitely many atoms have valuation exactly `γ`, so finitely many
earlier atoms would make `D_γ` finite. -/
theorem infinite_earlier_atoms (w : SummableFamily Γ K X) {e : X → K}
    (he : Function.Injective e)
    (hsq : ∀ p : K[X], 0 ≤ toLex (atomicIntegral w fun x => p.eval (e x) ^ 2)) {x₀ : X}
    (hneg : toLex (w x₀) < 0) :
    {x | w x ≠ 0 ∧ (w x).orderTop < (w x₀).orderTop}.Infinite := by
  intro hE
  obtain ⟨γ, hγ⟩ := exists_orderTop_eq_of_ne_zero (ne_zero_of_toLex_neg hneg)
  have hfin : (visibleAtoms w γ).Finite := by
    refine (hE.union (finite_setOf_coeff_ne_zero w γ)).subset ?_
    rintro x ⟨hx, hle⟩
    rcases hle.lt_or_eq with h | h
    · exact Or.inl ⟨hx, by rw [hγ]; exact h⟩
    · exact Or.inr (coeff_orderTop_ne h)
  obtain ⟨p, -, hp⟩ := exists_sq_atomicIntegral_neg w he hneg hγ hfin
  exact (hsq p).not_gt hp

/-- `meas:cor:safesupport`: if every element of `S = ⋃_x supp w_x` has only finitely many
predecessors in `S`, positivity on real polynomial squares implies positivity of the
measure. For a negative atom of valuation `γ`, the visible set `D_γ` lies in the finite
union of the finite coefficient rows at the exponents of `S` up to `γ`. -/
theorem nonneg_of_finite_predecessors (w : SummableFamily Γ K X) {e : X → K}
    (he : Function.Injective e)
    (hS : ∀ γ ∈ ⋃ x, (w x).support, {δ | δ ∈ ⋃ x, (w x).support ∧ δ < γ}.Finite)
    (hsq : ∀ p : K[X], 0 ≤ toLex (atomicIntegral w fun x => p.eval (e x) ^ 2)) :
    ∀ A : Set X, 0 ≤ toLex (atomicMeasure w A) := by
  rw [atomicMeasure_nonneg_iff]
  intro x₀
  by_contra hx
  have hneg := not_le.mp hx
  obtain ⟨γ, hγ⟩ := exists_orderTop_eq_of_ne_zero (ne_zero_of_toLex_neg hneg)
  have hγS : γ ∈ ⋃ x, (w x).support :=
    Set.mem_iUnion.mpr ⟨x₀, (mem_support _ _).mpr (coeff_orderTop_ne hγ)⟩
  have hle : {δ | δ ∈ ⋃ x, (w x).support ∧ δ ≤ γ}.Finite := by
    refine ((hS γ hγS).union (Set.finite_singleton γ)).subset ?_
    rintro δ ⟨hδS, hδ⟩
    rcases hδ.lt_or_eq with h | h
    · exact Or.inl ⟨hδS, h⟩
    · exact Or.inr h
  have hfin : (visibleAtoms w γ).Finite := by
    refine (hle.biUnion fun δ _ => finite_setOf_coeff_ne_zero w δ).subset ?_
    rintro x ⟨hx, hxγ⟩
    obtain ⟨δ, hδ⟩ := exists_orderTop_eq_of_ne_zero hx
    have hc := coeff_orderTop_ne hδ
    rw [hδ, WithTop.coe_le_coe] at hxγ
    exact Set.mem_iUnion₂.mpr
      ⟨δ, ⟨Set.mem_iUnion.mpr ⟨x, (mem_support _ _).mpr hc⟩, hxγ⟩, hc⟩
  obtain ⟨p, -, hp⟩ := exists_sq_atomicIntegral_neg w he hneg hγ hfin
  exact (hsq p).not_gt hp

/-- `meas:cor:safesupport`, last sentence: for a globally left-finite support, with
`S ∩ (-∞, γ]` finite for every `γ ∈ Γ`, positivity on real polynomial squares implies
positivity of the measure, since such a support has the finite-predecessor property. -/
theorem nonneg_of_leftFinite (w : SummableFamily Γ K X) {e : X → K}
    (he : Function.Injective e)
    (hS : ∀ γ : Γ, {δ | δ ∈ ⋃ x, (w x).support ∧ δ ≤ γ}.Finite)
    (hsq : ∀ p : K[X], 0 ≤ toLex (atomicIntegral w fun x => p.eval (e x) ^ 2)) :
    ∀ A : Set X, 0 ≤ toLex (atomicMeasure w A) :=
  nonneg_of_finite_predecessors w he
    (fun γ _ => (hS γ).subset fun _ hδ => ⟨hδ.1, hδ.2.le⟩) hsq

end Visible

section OrderType

variable {Γ : Type*} [LinearOrder Γ]

/-- The finite-predecessor condition of `meas:cor:safesupport` says `ot(S) ≤ ω`: every
element of `S` has finitely many predecessors in `S` exactly when `S` order-embeds in `ℕ`.
The embedding counts predecessors. -/
theorem finite_predecessors_iff_nonempty_orderEmbedding {S : Set Γ} :
    (∀ γ ∈ S, {δ | δ ∈ S ∧ δ < γ}.Finite) ↔ Nonempty (S ↪o ℕ) := by
  constructor
  · intro h
    refine ⟨OrderEmbedding.ofStrictMono (fun γ : S => {δ | δ ∈ S ∧ δ < γ.1}.ncard) ?_⟩
    intro a b hab
    have hab' : a.1 < b.1 := Subtype.coe_lt_coe.mpr hab
    refine Set.ncard_lt_ncard ⟨fun δ hδ => ⟨hδ.1, hδ.2.trans hab'⟩, fun hsub => ?_⟩ (h b.1 b.2)
    exact lt_irrefl a.1 (hsub ⟨a.2, hab'⟩).2
  · rintro ⟨f⟩ γ hγ
    have hsub : {δ | δ ∈ S ∧ δ < γ} ⊆ Subtype.val '' (f ⁻¹' Set.Iio (f ⟨γ, hγ⟩)) := by
      rintro δ ⟨hδS, hδ⟩
      refine ⟨⟨δ, hδS⟩, ?_, rfl⟩
      exact f.lt_iff_lt.mpr (Subtype.mk_lt_mk.mpr hδ)
    exact (((Set.finite_Iio _).preimage f.injective.injOn).image _).subset hsub

variable {K X : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `meas:cor:safesupport` with the hypothesis `ot(S) ≤ ω`, stated as an order embedding
of the global support into `ℕ`. -/
theorem nonneg_of_orderEmbedding_nat (w : SummableFamily Γ K X) {e : X → K}
    (he : Function.Injective e) (hS : Nonempty ((⋃ x, (w x).support) ↪o ℕ))
    (hsq : ∀ p : K[X], 0 ≤ toLex (atomicIntegral w fun x => p.eval (e x) ^ 2)) :
    ∀ A : Set X, 0 ≤ toLex (atomicMeasure w A) :=
  nonneg_of_finite_predecessors w he (finite_predecessors_iff_nonempty_orderEmbedding.mpr hS)
    hsq

end OrderType

section Polynomial

variable {Γ K X : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing K]

/-- `meas:prop:integration`(iv): for a polynomial `P = ∑_j b_j X^j` with Hahn coefficients,
the family `(P(e x) w_x)_x`, built as the finite sum over `j` of the products of the
one-member family `(b_j)` with the strongly summable family `((e x)^j w_x)_x`. -/
def polyFamily (w : SummableFamily Γ K X) (e : X → K) (P : K⟦Γ⟧[X]) :
    SummableFamily Γ K X :=
  ∑ j ∈ P.support, P.coeff j • SummableFamily.smulFamily (fun x => e x ^ j) w

/-- The members of `polyFamily` are the products `P(e x) w_x`. -/
theorem polyFamily_apply (w : SummableFamily Γ K X) (e : X → K) (P : K⟦Γ⟧[X]) (x : X) :
    polyFamily w e P x = P.eval (HahnSeries.C (e x)) * w x := by
  have hev : ∀ (s : Finset ℕ) (F : ℕ → SummableFamily Γ K X),
      (∑ j ∈ s, F j) x = ∑ j ∈ s, F j x := by
    intro s F
    induction s using Finset.cons_induction with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, SummableFamily.zero_apply]
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, SummableFamily.add_apply, ih]
  rw [polyFamily, hev, Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsf : SummableFamily.smulFamily (fun x => e x ^ j) w x = (e x ^ j) • w x := rfl
  rw [SummableFamily.smul_apply, of_symm_smul_of_eq_mul, hsf, ← C_mul_eq_smul, map_pow,
    mul_assoc]

/-- `meas:prop:integration`(iv): the integral `L(P) = ∫ P dμ = ∑ˢ_x P(e x) w_x` of a
polynomial with Hahn coefficients. -/
def polyIntegral (w : SummableFamily Γ K X) (e : X → K) (P : K⟦Γ⟧[X]) : K⟦Γ⟧ :=
  (polyFamily w e P).hsum

theorem coeff_polyIntegral (w : SummableFamily Γ K X) (e : X → K) (P : K⟦Γ⟧[X]) (γ : Γ) :
    (polyIntegral w e P).coeff γ = ∑ᶠ x, (P.eval (HahnSeries.C (e x)) * w x).coeff γ := by
  rw [polyIntegral, SummableFamily.coeff_hsum]
  exact finsum_congr fun x => by rw [polyFamily_apply]

/-- `meas:prop:integration`(iv): `∫ P dμ` is obtained by expanding `P` into finitely many
coefficients times ordinary power moments, `∫ P dμ = ∑_j b_j ∫ x^j dμ`. -/
theorem polyIntegral_eq_sum (w : SummableFamily Γ K X) (e : X → K) (P : K⟦Γ⟧[X]) :
    polyIntegral w e P = ∑ j ∈ P.support, P.coeff j * atomicIntegral w fun x => e x ^ j := by
  rw [polyIntegral, polyFamily, ← SummableFamily.lsum_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [SummableFamily.lsum_apply, SummableFamily.hsum_smul]
  rfl

/-- On real polynomials `L` is the scalar integral of `meas:prop:integration`(ii). -/
theorem polyIntegral_map_C (w : SummableFamily Γ K X) (e : X → K) (p : K[X]) :
    polyIntegral w e (p.map HahnSeries.C) = atomicIntegral w fun x => p.eval (e x) := by
  rw [polyIntegral, atomicIntegral]
  refine congrArg _ (SummableFamily.ext fun x => ?_)
  rw [polyFamily_apply, Polynomial.eval_map_apply, C_mul_eq_smul]
  rfl

/-- `L(p²) = ∫ p² dμ` for a real polynomial `p`. -/
theorem polyIntegral_map_C_sq (w : SummableFamily Γ K X) (e : X → K) (p : K[X]) :
    polyIntegral w e (p.map HahnSeries.C ^ 2) = atomicIntegral w fun x => p.eval (e x) ^ 2 := by
  rw [← Polynomial.map_pow, polyIntegral_map_C]
  simp only [Polynomial.eval_pow]

end Polynomial

section Positivity

variable {Γ K X : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A measure with nonnegative point weights is nonnegative on squares of Hahn-coefficient
polynomials, by strong summation of the nonnegative values `P(e x)² w_x`. -/
theorem polyIntegral_sq_nonneg (w : SummableFamily Γ K X) (hw : ∀ x, 0 ≤ toLex (w x))
    (e : X → K) (P : K⟦Γ⟧[X]) : 0 ≤ toLex (polyIntegral w e (P ^ 2)) :=
  hsum_nonneg _ fun x => by
    rw [polyFamily_apply, Polynomial.eval_pow, toLex_mul, toLex_pow]
    exact mul_nonneg (sq_nonneg _) (hw x)

/-- `meas:thm:visibility`, first assertion, for the functional `L(P) = ∫ P dμ` on
Hahn-coefficient polynomials: if `w_{x₀} < 0`, `γ = v(w_{x₀})` and `D_γ` is finite, a real
polynomial `p` of degree `|D_γ| - 1` has `L(p²) < 0`. -/
theorem exists_sq_polyIntegral_neg (w : SummableFamily Γ K X) {e : X → K}
    (he : Function.Injective e) {x₀ : X} (hneg : toLex (w x₀) < 0) {γ : Γ}
    (hγ : (w x₀).orderTop = γ) (hfin : (visibleAtoms w γ).Finite) :
    ∃ p : K[X], p.natDegree + 1 = hfin.toFinset.card ∧
      toLex (polyIntegral w e (p.map HahnSeries.C ^ 2)) < 0 := by
  obtain ⟨p, hdeg, hp⟩ := exists_sq_atomicIntegral_neg w he hneg hγ hfin
  exact ⟨p, hdeg, by rwa [polyIntegral_map_C_sq]⟩

/-- `meas:thm:visibility`, second assertion: if every `D_γ` is finite, the following are
equivalent: the measure is positive; `L(p²) ≥ 0` for every real polynomial `p`;
`L(P²) ≥ 0` for every polynomial `P` with Hahn coefficients. -/
theorem nonneg_tfae (w : SummableFamily Γ K X) {e : X → K} (he : Function.Injective e)
    (hfin : ∀ γ, (visibleAtoms w γ).Finite) :
    List.TFAE [∀ A : Set X, 0 ≤ toLex (atomicMeasure w A),
      ∀ p : K[X], 0 ≤ toLex (polyIntegral w e (p.map HahnSeries.C ^ 2)),
      ∀ P : K⟦Γ⟧[X], 0 ≤ toLex (polyIntegral w e (P ^ 2))] := by
  tfae_have 1 → 3 := fun h P =>
    polyIntegral_sq_nonneg w ((atomicMeasure_nonneg_iff w).mp h) e P
  tfae_have 3 → 2 := fun h p => h _
  tfae_have 2 → 1 := by
    intro h
    rw [atomicMeasure_nonneg_iff]
    intro x₀
    by_contra hx
    have hneg := not_le.mp hx
    obtain ⟨γ, hγ⟩ := exists_orderTop_eq_of_ne_zero (ne_zero_of_toLex_neg hneg)
    obtain ⟨p, -, hp⟩ := exists_sq_polyIntegral_neg w he hneg hγ (hfin γ)
    exact (h p).not_gt hp
  tfae_finish

end Positivity

section Measure

variable {Γ K X : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] [MeasurableSpace X]
  {μ : Set X → K⟦Γ⟧}

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- The positivity clause of `meas:thm:atomic` for a strong Hahn measure on a countably
separated space: `μ` is positive exactly when every point weight is nonnegative. -/
theorem nonneg_iff_strongWeights (hμ : IsStrongHahnMeasure μ) (hX : IsCountablySeparated X) :
    (∀ A, MeasurableSet A → 0 ≤ toLex (μ A)) ↔ ∀ x, 0 ≤ toLex (strongWeights hμ hX x) := by
  constructor
  · intro h x
    rw [strongWeights_apply]
    exact h _ (hX.measurableSet_singleton x)
  · intro h A hA
    rw [eq_atomicMeasure_strongWeights hμ hX hA]
    exact (atomicMeasure_nonneg_iff _).mpr h A

/-- `meas:thm:visibility` for a signed strong Hahn measure `μ` on a countably separated
space with injective positions `e`: if every set `D_γ` of its point weights is finite,
positivity of `μ`, positivity of `L` on real polynomial squares and positivity of `L` on
squares of Hahn-coefficient polynomials are equivalent. -/
theorem measure_nonneg_tfae (hμ : IsStrongHahnMeasure μ) (hX : IsCountablySeparated X)
    {e : X → K} (he : Function.Injective e)
    (hfin : ∀ γ, (visibleAtoms (strongWeights hμ hX) γ).Finite) :
    List.TFAE [∀ A, MeasurableSet A → 0 ≤ toLex (μ A),
      ∀ p : K[X], 0 ≤ toLex (polyIntegral (strongWeights hμ hX) e (p.map HahnSeries.C ^ 2)),
      ∀ P : K⟦Γ⟧[X], 0 ≤ toLex (polyIntegral (strongWeights hμ hX) e (P ^ 2))] := by
  have h := nonneg_tfae (strongWeights hμ hX) he hfin
  rw [List.tfae_cons_cons] at h ⊢
  refine ⟨?_, h.2⟩
  rw [nonneg_iff_strongWeights, ← atomicMeasure_nonneg_iff]
  exact h.1

end Measure

section MeasureCorollaries

variable {Γ K X : Type*} [LinearOrder Γ] [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]
  [MeasurableSpace X] {μ : Set X → K⟦Γ⟧}

/-- `meas:cor:hidden-necessary` for a signed strong Hahn measure on a countably separated
space: if `∫ p² dμ ≥ 0` for every real polynomial `p`, every point `x₀` with
`μ({x₀}) < 0` has infinitely many atoms of strictly smaller valuation. -/
theorem measure_infinite_earlier_atoms (hμ : IsStrongHahnMeasure μ)
    (hX : IsCountablySeparated X) {e : X → K} (he : Function.Injective e)
    (hsq : ∀ p : K[X],
      0 ≤ toLex (atomicIntegral (strongWeights hμ hX) fun x => p.eval (e x) ^ 2))
    {x₀ : X} (hneg : toLex (μ {x₀}) < 0) :
    {x | μ {x} ≠ 0 ∧ (μ {x}).orderTop < (μ {x₀}).orderTop}.Infinite :=
  infinite_earlier_atoms (strongWeights hμ hX) he hsq hneg

/-- `meas:cor:safesupport` for a signed strong Hahn measure on a countably separated space:
if every element of `S = ⋃_x supp μ({x})` has finitely many predecessors in `S`, positivity
on real polynomial squares implies `μ(A) ≥ 0` for every event `A`. -/
theorem measure_nonneg_of_finite_predecessors (hμ : IsStrongHahnMeasure μ)
    (hX : IsCountablySeparated X) {e : X → K} (he : Function.Injective e)
    (hS : ∀ γ ∈ ⋃ x, (μ {x}).support, {δ | δ ∈ ⋃ x, (μ {x}).support ∧ δ < γ}.Finite)
    (hsq : ∀ p : K[X],
      0 ≤ toLex (atomicIntegral (strongWeights hμ hX) fun x => p.eval (e x) ^ 2)) :
    ∀ A, MeasurableSet A → 0 ≤ toLex (μ A) := by
  intro A hA
  rw [eq_atomicMeasure_strongWeights hμ hX hA]
  exact nonneg_of_finite_predecessors (strongWeights hμ hX) he hS hsq A

end MeasureCorollaries

end

end Surreal.FiniteVisibility
