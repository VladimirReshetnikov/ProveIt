import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Surreal.Foundations.SignSequenceReal
import Surreal.Foundations.SignSequenceTopology
import Surreal.HahnSeries.StrongMeasure

/-!
# Coefficientwise positivity, finite strong products and order-limit additivity

This file formalizes `meas:lem:coefpositive`, the finite-product clause of
`meas:lem:sumalgebra` and `meas:cw:cor:orderlimits` of
`docs/surreal/hahn-valued-measures-and-probability/article.tex`.

* `meas:lem:coefpositive`: for nonnegative real Hahn series `f n`, indexed by an arbitrary
  type, whose supports lie in one well-ordered set `W` of exponents and whose coefficients
  are absolutely summable at every `γ ∈ W`, the coefficientwise series
  `f = ∑_{γ ∈ W} (∑_n coef_γ(f n)) t^γ` (`coefficientwiseSum`) is nonnegative
  (`coefficientwiseSum_nonneg`). If some `f n` is nonzero then `f > 0`
  (`coefficientwiseSum_pos`) and `v(f) = min_{f n ≠ 0} v(f n)`
  (`isLeast_orderTop_coefficientwiseSum`). The exponents form any linear order. Finite
  families are the case of a finite index type, where the summability hypothesis is
  automatic and the coefficientwise series is the ordinary finite sum
  (`coefficientwiseSum_eq_sum`, `toLex_sum_nonneg`, `toLex_sum_pos`,
  `isLeast_orderTop_sum`). A strongly summable family with supports in `W` has its strong
  sum as coefficientwise series (`coefficientwiseSum_eq_hsum`).
* The unlabelled remark after `meas:lem:coefpositive`: the constant family
  `(2^{-n})_{n ≥ 1}` (`halfPowFamily`, indexed from `0` as `n ↦ 2^{-(n+1)}`) has
  coefficientwise sum `1` (`coefficientwiseSum_halfPowFamily`) but is not strongly summable
  (`not_exists_summableFamily_halfPowFamily`).
* `meas:lem:sumalgebra`, finite-product clause: for finitely many strongly summable
  families `(f^{(k)}_i)_{i ∈ I_k}`, `k < n`, with arbitrary index types, the family
  `(∏_k f^{(k)}_{i_k})_{(i_k)_k}` is strongly summable (`piFamily`, `piFamily_apply`) and
  its strong sum is `∏_k ∑ˢ_i f^{(k)}_i` (`hsum_piFamily`), over any commutative semiring of
  coefficients and any ordered cancellative commutative monoid of exponents. The other
  clauses of `meas:lem:sumalgebra` are proved elsewhere: subfamilies and regrouping are
  `Surreal.HahnSeries.restrict`, `regroup` and `hsum_regroup`, the binary product is
  Mathlib's `HahnSeries.SummableFamily.mul` with `hsum_mul`, positivity is
  `Surreal.HahnSeries.hsum_pos`, and the valuation formula is
  `Surreal.MeasureBarrier.isLeast_orderTop_hsum`.
* `meas:cw:cor:orderlimits`: a set function `μ` on a measurable space with values in the
  actual sign-sequence surreals is order-limit additive (`IsOrderLimitAdditive`) if the
  partial sums over every disjoint measurable sequence converge to the mass of the union in
  the native order topology. Then the masses of every disjoint measurable sequence are
  eventually zero (`IsOrderLimitAdditive.eventually_eq_zero`), so only finitely many are
  nonzero (`IsOrderLimitAdditive.finite_setOf_ne_zero`). The proof is the small-index
  convergence clause of `found:thm:discrete`
  (`Surreal.Foundations.SignSequence.tendsto_nhds_iff_eventually_eq`). Consequently no such
  `μ` extends Lebesgue measure on `[0, 1]`: neither on the Borel sets of `ℝ`, agreeing with
  `ofReal ∘ volume.real` on the measurable subsets of `[0, 1]`
  (`IsOrderLimitAdditive.not_extends_volume`), nor on the unit interval with its own Borel
  structure and Lebesgue measure (`IsOrderLimitAdditive.not_extends_volume_unitInterval`).
  The obstruction is the disjoint dyadic intervals `(2^{-(n+1)}, 2^{-n}]` (`dyadicInterval`).
  This part concerns set functions valued in `Surreal.Foundations.SignSequence`, not Hahn
  series; its declarations live in the namespace `Surreal.CoefficientwisePositivity`, for
  example `Surreal.CoefficientwisePositivity.IsOrderLimitAdditive.not_extends_volume`.

Nothing remains pending for these three statements or for the remark.
-/

namespace Surreal.CoefficientwisePositivity

open _root_.HahnSeries Surreal.HahnSeries

noncomputable section

section CoefficientwiseSum

variable {Γ α : Type*} [LinearOrder Γ]

open scoped Classical in
/-- The coefficientwise series `f = ∑_{γ ∈ W} (∑_n coef_γ(f n)) t^γ` of
`meas:lem:coefpositive`. Its coefficient at `γ ∈ W` is the ordinary real sum
`∑' n, coef_γ(f n)`, and it vanishes off `W`; the well-ordering of `W` makes it a Hahn
series. -/
def coefficientwiseSum (W : Set Γ) (hW : W.IsWF) (f : α → ℝ⟦Γ⟧) : ℝ⟦Γ⟧ where
  coeff γ := if γ ∈ W then ∑' n, (f n).coeff γ else 0
  isPWO_support' := hW.isPWO.mono fun γ hγ => by
    by_contra h
    exact hγ (if_neg h)

variable {W : Set Γ} (hW : W.IsWF) {f : α → ℝ⟦Γ⟧}

/-- When all supports lie in `W`, every coefficient of the coefficientwise series is the
ordinary sum of the corresponding coefficients. -/
theorem coeff_coefficientwiseSum (hsupp : ∀ n, (f n).support ⊆ W) (γ : Γ) :
    (coefficientwiseSum W hW f).coeff γ = ∑' n, (f n).coeff γ := by
  by_cases h : γ ∈ W
  · simp [coefficientwiseSum, h]
  · have h0 : ∀ n, (f n).coeff γ = 0 := fun n => by
      by_contra hn
      exact h (hsupp n ((mem_support _ _).mpr hn))
    simp [coefficientwiseSum, h, h0]

/-- The proof of `meas:lem:coefpositive`: the least leading exponent `g` of a nonzero member
bounds every valuation from below and is attained; the coefficientwise series vanishes below
`g`, and its coefficient at `g` is an absolutely convergent sum of nonnegative terms with a
positive term. -/
theorem exists_least_leading_exponent (hsupp : ∀ n, (f n).support ⊆ W)
    (habs : ∀ γ ∈ W, Summable fun n => |(f n).coeff γ|) (hf : ∀ n, 0 ≤ toLex (f n))
    (hne : ∃ n, f n ≠ 0) :
    ∃ g : Γ, (∀ n, (g : WithTop Γ) ≤ (f n).orderTop) ∧ (∃ n, (f n).orderTop = g) ∧
      (∀ j < g, (coefficientwiseSum W hW f).coeff j = 0) ∧
        0 < (coefficientwiseSum W hW f).coeff g := by
  have hUW : (⋃ n, (f n).support) ⊆ W := Set.iUnion_subset hsupp
  have hwf : (⋃ n, (f n).support).IsWF := hW.mono hUW
  obtain ⟨n₀, hn₀⟩ := hne
  have hne' : (⋃ n, (f n).support).Nonempty := by
    obtain ⟨i, hi⟩ := support_nonempty_iff.mpr hn₀
    exact ⟨i, Set.mem_iUnion.mpr ⟨n₀, hi⟩⟩
  set g := hwf.min hne'
  have hmin : ∀ n, ∀ j ∈ (f n).support, g ≤ j := fun n j hj =>
    hwf.min_le hne' (Set.mem_iUnion.mpr ⟨n, hj⟩)
  have hle : ∀ n, (g : WithTop Γ) ≤ (f n).orderTop := fun n =>
    le_orderTop_iff_forall.mpr fun j hj => by
      by_contra h
      exact (not_le.mpr (WithTop.coe_lt_coe.mp hj)) (hmin n j ((mem_support _ _).mpr h))
  -- At the least exponent a member contributes zero or its positive leading coefficient.
  have hcoeff : ∀ n, (f n).coeff g ≠ 0 → 0 < (f n).coeff g := by
    intro n hn
    have hpos : 0 < toLex (f n) := by
      refine lt_of_le_of_ne (hf n) fun h => hn ?_
      rw [show f n = ofLex (toLex (f n)) from rfl, ← h]
      simp
    obtain ⟨i, hi, hlt⟩ := exists_coeff_pos_of_pos hpos
    rcases (hmin n i ((mem_support _ _).mpr hlt.ne')).lt_or_eq with h | h
    · exact absurd (hi g h) hn
    · exact h ▸ hlt
  have hnonneg : ∀ n, 0 ≤ (f n).coeff g := fun n => by
    by_cases hn : (f n).coeff g = 0
    · exact hn.ge
    · exact (hcoeff n hn).le
  obtain ⟨n₁, hn₁⟩ := Set.mem_iUnion.mp (hwf.min_mem hne')
  refine ⟨g, hle, ⟨n₁, orderTop_eq_of_le hn₁ (hmin n₁)⟩, fun j hj => ?_, ?_⟩
  · rw [coeff_coefficientwiseSum hW hsupp]
    have h0 : ∀ n, (f n).coeff j = 0 := fun n =>
      coeff_eq_zero_of_lt_orderTop ((WithTop.coe_lt_coe.mpr hj).trans_le (hle n))
    simp [h0]
  · rw [coeff_coefficientwiseSum hW hsupp]
    have hs : Summable fun n => (f n).coeff g := (habs g (hUW (hwf.min_mem hne'))).of_abs
    exact hs.tsum_pos hnonneg n₁ (hcoeff n₁ ((mem_support _ _).mp hn₁))

/-- `meas:lem:coefpositive`, strict part: if some member is nonzero, the coefficientwise
series of nonnegative real Hahn series is positive. -/
theorem coefficientwiseSum_pos (hsupp : ∀ n, (f n).support ⊆ W)
    (habs : ∀ γ ∈ W, Summable fun n => |(f n).coeff γ|) (hf : ∀ n, 0 ≤ toLex (f n))
    (hne : ∃ n, f n ≠ 0) : 0 < toLex (coefficientwiseSum W hW f) := by
  obtain ⟨g, -, -, hbelow, hpos⟩ := exists_least_leading_exponent hW hsupp habs hf hne
  exact pos_of_coeff hbelow hpos

/-- `meas:lem:coefpositive`: the coefficientwise series of nonnegative real Hahn series with
supports in one well-ordered set and absolutely summable coefficients is nonnegative. -/
theorem coefficientwiseSum_nonneg (hsupp : ∀ n, (f n).support ⊆ W)
    (habs : ∀ γ ∈ W, Summable fun n => |(f n).coeff γ|) (hf : ∀ n, 0 ≤ toLex (f n)) :
    0 ≤ toLex (coefficientwiseSum W hW f) := by
  by_cases hne : ∃ n, f n ≠ 0
  · exact (coefficientwiseSum_pos hW hsupp habs hf hne).le
  · push Not at hne
    have h0 : coefficientwiseSum W hW f = 0 := by
      ext γ
      rw [coeff_coefficientwiseSum hW hsupp]
      simp [hne]
    simp [h0]

/-- `meas:lem:coefpositive`, valuation clause: if some member is nonzero, then
`v(f) = min_{f n ≠ 0} v(f n)` for the coefficientwise series `f`. -/
theorem isLeast_orderTop_coefficientwiseSum (hsupp : ∀ n, (f n).support ⊆ W)
    (habs : ∀ γ ∈ W, Summable fun n => |(f n).coeff γ|) (hf : ∀ n, 0 ≤ toLex (f n))
    (hne : ∃ n, f n ≠ 0) :
    IsLeast ((fun n => (f n).orderTop) '' {n | f n ≠ 0})
      (coefficientwiseSum W hW f).orderTop := by
  obtain ⟨g, hle, ⟨n₁, hn₁⟩, hbelow, hpos⟩ :=
    exists_least_leading_exponent hW hsupp habs hf hne
  have hg : (coefficientwiseSum W hW f).orderTop = g := by
    refine orderTop_eq_of_le ((mem_support _ _).mpr hpos.ne') fun j hj => ?_
    by_contra hlt
    push Not at hlt
    exact (mem_support _ _).mp hj (hbelow j hlt)
  refine ⟨⟨n₁, ne_zero_of_coeff_ne_zero (coeff_orderTop_ne hn₁), ?_⟩, ?_⟩
  · change (f n₁).orderTop = _
    rw [hn₁, hg]
  · rintro _ ⟨n, -, rfl⟩
    rw [hg]
    exact hle n

/-- For a finite family the coefficientwise series is the ordinary finite sum. -/
theorem coefficientwiseSum_eq_sum [Fintype α] (hsupp : ∀ n, (f n).support ⊆ W) :
    coefficientwiseSum W hW f = ∑ n, f n := by
  ext γ
  rw [coeff_coefficientwiseSum hW hsupp, tsum_fintype, coeff_sum]

/-- A strongly summable family whose supports lie in `W` has its strong sum as
coefficientwise series: coefficientwise sums extend strong sums. -/
theorem coefficientwiseSum_eq_hsum (s : SummableFamily Γ ℝ α)
    (hsupp : ∀ n, (s n).support ⊆ W) : coefficientwiseSum W hW s = s.hsum := by
  ext γ
  rw [coeff_coefficientwiseSum hW hsupp, SummableFamily.coeff_hsum,
    tsum_eq_finsum (s.finite_co_support γ)]

section Finite

variable [Fintype α] (f : α → ℝ⟦Γ⟧)

/-- The union of the supports of a finite family of Hahn series is well-founded; it serves as
the common well-ordered set `W` of `meas:lem:coefpositive` for finite families. -/
theorem isWF_iUnion_support : (⋃ n ∈ (Finset.univ : Finset α), (f n).support).IsWF :=
  (Finset.univ.isWF_bUnion).mpr fun n _ => (f n).isWF_support

/-- Every member's support lies in the union of the supports of the finite family. -/
theorem support_subset_iUnion (n : α) :
    (f n).support ⊆ ⋃ m ∈ (Finset.univ : Finset α), (f m).support :=
  fun _ hγ => Set.mem_iUnion₂.mpr ⟨n, Finset.mem_univ n, hγ⟩

/-- `meas:lem:coefpositive` for finite families: a finite sum of nonnegative real Hahn series
is nonnegative. -/
theorem toLex_sum_nonneg (hf : ∀ n, 0 ≤ toLex (f n)) : 0 ≤ toLex (∑ n, f n) := by
  rw [← coefficientwiseSum_eq_sum (isWF_iUnion_support f) (support_subset_iUnion f)]
  exact coefficientwiseSum_nonneg _ (support_subset_iUnion f)
    (fun _ _ => Summable.of_finite) hf

/-- `meas:lem:coefpositive` for finite families, strict part. -/
theorem toLex_sum_pos (hf : ∀ n, 0 ≤ toLex (f n)) (hne : ∃ n, f n ≠ 0) :
    0 < toLex (∑ n, f n) := by
  rw [← coefficientwiseSum_eq_sum (isWF_iUnion_support f) (support_subset_iUnion f)]
  exact coefficientwiseSum_pos _ (support_subset_iUnion f)
    (fun _ _ => Summable.of_finite) hf hne

/-- `meas:lem:coefpositive` for finite families, valuation clause:
`v(∑ n, f n) = min_{f n ≠ 0} v(f n)`. -/
theorem isLeast_orderTop_sum (hf : ∀ n, 0 ≤ toLex (f n)) (hne : ∃ n, f n ≠ 0) :
    IsLeast ((fun n => (f n).orderTop) '' {n | f n ≠ 0}) (∑ n, f n).orderTop := by
  rw [← coefficientwiseSum_eq_sum (isWF_iUnion_support f) (support_subset_iUnion f)]
  exact isLeast_orderTop_coefficientwiseSum _ (support_subset_iUnion f)
    (fun _ _ => Summable.of_finite) hf hne

end Finite

end CoefficientwiseSum

section HalfPowFamily

variable {Γ : Type*} [LinearOrder Γ] [Zero Γ]

/-- The constant family `(2^{-n})_{n ≥ 1}` of the remark after `meas:lem:coefpositive`, as
real Hahn series at exponent `0`, indexed from `0` as `n ↦ 2^{-(n+1)}`. -/
def halfPowFamily (n : ℕ) : ℝ⟦Γ⟧ :=
  single 0 ((2 : ℝ)⁻¹ ^ (n + 1))

/-- The remark after `meas:lem:coefpositive`, first half: the constant family
`(2^{-n})_{n ≥ 1}` has coefficientwise sum `1` over `W = {0}`. -/
theorem coefficientwiseSum_halfPowFamily :
    coefficientwiseSum {0} Set.isWF_singleton (halfPowFamily (Γ := Γ)) = 1 := by
  ext γ
  rw [coeff_coefficientwiseSum (f := halfPowFamily) _ fun _ => support_single_subset]
  by_cases h : γ = 0
  · subst h
    simp_rw [halfPowFamily, coeff_single_same, coeff_one, if_pos, pow_succ]
    rw [tsum_mul_right, tsum_geometric_inv_two]
    norm_num
  · simp [halfPowFamily, coeff_single_of_ne h, h]

/-- The remark after `meas:lem:coefpositive`, second half: the constant family
`(2^{-n})_{n ≥ 1}` is not strongly summable, since infinitely many members contribute at
exponent `0`. -/
theorem not_exists_summableFamily_halfPowFamily :
    ¬ ∃ s : SummableFamily Γ ℝ ℕ, ∀ n, s n = halfPowFamily n := by
  rintro ⟨s, hs⟩
  refine Set.infinite_univ ((s.finite_co_support 0).subset fun n _ => ?_)
  simp [hs, halfPowFamily]

end HalfPowFamily

section FiniteProducts

universe v

variable {Γ R : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommSemiring R]

/-- `meas:lem:sumalgebra`, finite-product clause: the strongly summable family of all
products `∏_k f^{(k)}_{i_k}` of finitely many strongly summable families, indexed by the
tuples `(i_k)_k`. It is built from the binary product family by induction on the number of
factors. -/
def piFamily : {n : ℕ} → {ι : Fin n → Type v} → ((k : Fin n) → SummableFamily Γ R (ι k)) →
    SummableFamily Γ R ((k : Fin n) → ι k)
  | 0, _, _ => SummableFamily.const _ 1
  | _ + 1, ι, s => SummableFamily.Equiv (Fin.consEquiv ι)
      (SummableFamily.mul (s 0) (piFamily fun k => s k.succ))

/-- The members of the finite product family are the products of the members. -/
theorem piFamily_apply : ∀ {n : ℕ} {ι : Fin n → Type v}
    (s : (k : Fin n) → SummableFamily Γ R (ι k)) (x : (k : Fin n) → ι k),
    piFamily s x = ∏ k, s k (x k)
  | 0, _, _, _ => by simp [piFamily]
  | _ + 1, _, s, x => by
    rw [Fin.prod_univ_succ, ← piFamily_apply (fun k => s k.succ) (fun k => x k.succ)]
    rfl

/-- `meas:lem:sumalgebra`, finite-product clause:
`∏_k ∑ˢ_i f^{(k)}_i = ∑ˢ_{(i_k)_k} ∏_k f^{(k)}_{i_k}`. -/
theorem hsum_piFamily : ∀ {n : ℕ} {ι : Fin n → Type v}
    (s : (k : Fin n) → SummableFamily Γ R (ι k)),
    (piFamily s).hsum = ∏ k, (s k).hsum
  | 0, _, _ => by simp [piFamily]
  | _ + 1, _, s => by
    rw [piFamily, SummableFamily.hsum_equiv, SummableFamily.hsum_mul, hsum_piFamily,
      Fin.prod_univ_succ]

end FiniteProducts

section OrderLimits

universe u

open Filter Topology MeasureTheory Surreal.Foundations

/-- The order-limit reading of countable additivity in `meas:cw:cor:orderlimits`: for every
pairwise disjoint measurable sequence, the finite partial sums of the masses converge to the
mass of the union in the native order topology of the actual sign-sequence surreals. -/
def IsOrderLimitAdditive {X : Type*} [MeasurableSpace X] (μ : Set X → SignSequence.{u}) :
    Prop :=
  ∀ A : ℕ → Set X, (∀ n, MeasurableSet (A n)) → Pairwise (Function.onFun Disjoint A) →
    Tendsto (fun N => ∑ n ∈ Finset.range N, μ (A n)) atTop (𝓝 (μ (⋃ n, A n)))

namespace IsOrderLimitAdditive

variable {X : Type*} [MeasurableSpace X] {μ : Set X → SignSequence.{u}}

/-- By `found:thm:discrete` the partial sums are eventually constant, so the masses of a
disjoint measurable sequence are eventually zero. -/
theorem eventually_eq_zero (hμ : IsOrderLimitAdditive μ) {A : ℕ → Set X}
    (hA : ∀ n, MeasurableSet (A n)) (hd : Pairwise (Function.onFun Disjoint A)) :
    ∀ᶠ n in atTop, μ (A n) = 0 := by
  have h := (SignSequence.tendsto_nhds_iff_eventually_eq _ atTop _).mp (hμ A hA hd)
  filter_upwards [h, (tendsto_add_atTop_nat 1).eventually h] with n hn hn1
  simp only [Finset.sum_range_succ, hn] at hn1
  simpa using hn1

/-- `meas:cw:cor:orderlimits`: in every disjoint measurable sequence only finitely many
masses are nonzero. -/
theorem finite_setOf_ne_zero (hμ : IsOrderLimitAdditive μ) {A : ℕ → Set X}
    (hA : ∀ n, MeasurableSet (A n)) (hd : Pairwise (Function.onFun Disjoint A)) :
    {n | μ (A n) ≠ 0}.Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hμ.eventually_eq_zero hA hd)
  refine (Set.finite_lt_nat N).subset fun n hn => ?_
  by_contra h
  exact hn (hN n (not_lt.mp h))

/-- No disjoint measurable sequence has only nonzero masses. -/
theorem not_forall_ne_zero (hμ : IsOrderLimitAdditive μ) {A : ℕ → Set X}
    (hA : ∀ n, MeasurableSet (A n)) (hd : Pairwise (Function.onFun Disjoint A)) :
    ¬ ∀ n, μ (A n) ≠ 0 := fun h =>
  Set.infinite_univ ((hμ.finite_setOf_ne_zero hA hd).subset fun n _ => h n)

end IsOrderLimitAdditive

/-- The disjoint dyadic intervals `(2^{-(n+1)}, 2^{-n}] ⊆ [0, 1]` of positive length. -/
def dyadicInterval (n : ℕ) : Set ℝ :=
  Set.Ioc ((2⁻¹ : ℝ) ^ (n + 1)) ((2⁻¹ : ℝ) ^ n)

/-- Each dyadic interval `(2^{-(n+1)}, 2^{-n}]` lies in `[0, 1]`. -/
theorem dyadicInterval_subset (n : ℕ) : dyadicInterval n ⊆ Set.Icc 0 1 := fun _ hx =>
  ⟨(pow_pos (by norm_num) _).le.trans hx.1.le, hx.2.trans (pow_le_one₀ (by norm_num) (by norm_num))⟩

/-- Each dyadic interval is a Borel set of `ℝ`. -/
theorem measurableSet_dyadicInterval (n : ℕ) : MeasurableSet (dyadicInterval n) :=
  measurableSet_Ioc

/-- Distinct dyadic intervals are disjoint. -/
theorem pairwise_disjoint_dyadicInterval : Pairwise (Function.onFun Disjoint dyadicInterval) := by
  intro m n hmn
  have h := Antitone.pairwise_disjoint_on_Ioc_succ (f := fun n : ℕ => (2⁻¹ : ℝ) ^ n)
    (pow_right_anti₀ (by norm_num) (by norm_num)) hmn
  simpa [Function.onFun, dyadicInterval, Order.succ_eq_add_one] using h

/-- Each dyadic interval has positive Lebesgue measure. -/
theorem volume_real_dyadicInterval_pos (n : ℕ) : 0 < volume.real (dyadicInterval n) := by
  have h : (2⁻¹ : ℝ) ^ (n + 1) < (2⁻¹ : ℝ) ^ n :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (Nat.lt_succ_self n)
  rw [dyadicInterval, Real.volume_real_Ioc_of_le h.le]
  exact sub_pos.mpr h

namespace IsOrderLimitAdditive

/-- `meas:cw:cor:orderlimits`, Lebesgue clause on the Borel sets of `ℝ`: no order-limit
additive surreal-valued set function agrees with Lebesgue measure on the measurable subsets
of `[0, 1]`. -/
theorem not_extends_volume {μ : Set ℝ → SignSequence.{u}} (hμ : IsOrderLimitAdditive μ)
    (hvol : ∀ A, MeasurableSet A → A ⊆ Set.Icc 0 1 →
      μ A = SignSequence.ofReal (volume.real A)) : False := by
  refine hμ.not_forall_ne_zero (A := dyadicInterval) measurableSet_dyadicInterval
    pairwise_disjoint_dyadicInterval fun n => ?_
  rw [hvol _ (measurableSet_dyadicInterval n) (dyadicInterval_subset n), Ne,
    ← SignSequence.ofReal_zero, SignSequence.ofReal_inj]
  exact (volume_real_dyadicInterval_pos n).ne'

/-- `meas:cw:cor:orderlimits`, Lebesgue clause on the unit interval itself: no order-limit
additive surreal-valued set function on the Borel sets of `[0, 1]` agrees with its Lebesgue
measure. -/
theorem not_extends_volume_unitInterval {μ : Set unitInterval → SignSequence.{u}}
    (hμ : IsOrderLimitAdditive μ)
    (hvol : ∀ A, MeasurableSet A → μ A = SignSequence.ofReal (volume.real A)) : False := by
  refine hμ.not_forall_ne_zero (A := fun n => Subtype.val ⁻¹' dyadicInterval n)
    (fun n => measurable_subtype_coe (measurableSet_dyadicInterval n))
    (fun _ _ hmn => (pairwise_disjoint_dyadicInterval hmn).preimage _) fun n => ?_
  have h : volume.real (Subtype.val ⁻¹' dyadicInterval n : Set unitInterval) =
      volume.real (dyadicInterval n) := by
    rw [measureReal_def, measureReal_def, unitInterval.volume_apply,
      Subtype.image_preimage_coe, Set.inter_eq_right.mpr (dyadicInterval_subset n)]
  rw [hvol _ (measurable_subtype_coe (measurableSet_dyadicInterval n)), h, Ne,
    ← SignSequence.ofReal_zero, SignSequence.ofReal_inj]
  exact (volume_real_dyadicInterval_pos n).ne'

end IsOrderLimitAdditive

end OrderLimits

end

end Surreal.CoefficientwisePositivity
