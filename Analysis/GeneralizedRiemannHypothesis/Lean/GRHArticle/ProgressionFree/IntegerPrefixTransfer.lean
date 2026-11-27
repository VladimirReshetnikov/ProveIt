import GRHArticle.ProgressionFree.IntegerPrefix
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Discrete smooth-prefix losses

The step-function integrals for the smooth optimizations are sums with
weight `1/(k*(k+1))`. Tonelli's theorem equates the fixed-set sum with
its reciprocal weight.
-/

namespace GRHArticle.ProgressionFree

open Filter Topology Finset
open scoped BigOperators Classical

/-- The integers in the set up to a positive prefix cutoff. -/
noncomputable def integerPrefixSlice (A : Set ℕ) (k : ℕ) : Finset ℕ :=
  (integerPrefix k).filter (· ∈ A)

private theorem mem_integerPrefixSlice {A : Set ℕ} {k a : ℕ} :
    a ∈ integerPrefixSlice A k ↔ a ∈ integerPrefix k ∧ a ∈ A := by
  simp only [integerPrefixSlice, mem_filter]

/-- The weight of the interval between consecutive cutoffs. -/
noncomputable def integerPrefixStepWeight (k : ℕ) : ℝ := 1 / ((k : ℝ) * ((k : ℝ)+1))

private theorem integerPrefixStepWeight_nonneg (k : ℕ) : 0 ≤ integerPrefixStepWeight k := by
  unfold integerPrefixStepWeight
  positivity

private theorem integerPrefixStepWeight_diff {k : ℕ} (hk : 0 < k) :
    integerPrefixStepWeight k = (k : ℝ)⁻¹ - ((k : ℝ)+1)⁻¹ := by
  have h₀ : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have h₁ : (k : ℝ)+1 ≠ 0 := by positivity
  unfold integerPrefixStepWeight
  field_simp
  ring

private noncomputable def prefixKernel (a k : ℕ) : ℝ :=
  if a ≤ k then integerPrefixStepWeight k else 0

private theorem hasSum_prefixKernel {a : ℕ} (ha : 0 < a) :
    HasSum (prefixKernel a) (a : ℝ)⁻¹ := by
  have hshift : HasSum (fun n : ℕ ↦ prefixKernel a (n+a)) (a : ℝ)⁻¹ := by
    apply (hasSum_iff_tendsto_nat_of_nonneg (fun _ ↦ by
      simp only [prefixKernel, if_pos (Nat.le_add_left _ _), integerPrefixStepWeight_nonneg]) _).mpr
    have ht : Tendsto (fun n : ℕ ↦ ((n:ℝ)+(a:ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    have hm := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ (a:ℝ)⁻¹) atTop (𝓝 ((a:ℝ)⁻¹))).sub ht
    simp only [sub_zero] at hm
    refine hm.congr fun n ↦ ?_
    have hs := sum_range_sub' (fun j : ℕ ↦ ((j:ℝ)+(a:ℝ))⁻¹) n
    simp only [Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one] at hs
    rw [← hs]
    apply sum_congr rfl
    intro j hj
    rw [prefixKernel, if_pos (Nat.le_add_left _ _), integerPrefixStepWeight_diff (by omega), Nat.cast_add,
      add_right_comm _ 1 _]
  have hs : Summable (prefixKernel a) := (summable_nat_add_iff a).mp hshift.summable
  have h := hs.sum_add_tsum_nat_add a
  have hzero : ∑ n ∈ range a, prefixKernel a n = 0 := by
    apply sum_eq_zero
    intro n hn
    exact if_neg (Nat.not_le_of_lt (mem_range.mp hn))
  rw [hzero, zero_add, hshift.tsum_eq] at h
  exact h ▸ hs.hasSum

private theorem prefixKernel_tsum_column (A : Set ℕ)
    (hpos : ∀ a ∈ A, 0 < a) (k : ℕ) :
    (∑' a : A, prefixKernel a.val k) = ((integerPrefixSlice A k).card : ℝ) * integerPrefixStepWeight k := by
  let T : Set A := {a | a.val ≤ k}
  let e : T ≃ ↥(integerPrefixSlice A k) := {
    toFun := fun a ↦ ⟨a.val.val, mem_integerPrefixSlice.mpr
      ⟨mem_Icc.mpr ⟨hpos _ a.val.property, a.property⟩, a.val.property⟩⟩
    invFun := fun a ↦ ⟨⟨a.val, (mem_integerPrefixSlice.mp a.property).2⟩,
      (mem_Icc.mp (mem_integerPrefixSlice.mp a.property).1).2⟩
    left_inv := by intro a; exact Subtype.ext (Subtype.ext rfl)
    right_inv := by intro a; exact Subtype.ext rfl }
  have hs := (e.tsum_eq (fun _ : ↥(integerPrefixSlice A k) ↦ integerPrefixStepWeight k)).symm
  rw [tsum_fintype, sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul] at hs
  rw [hs]
  calc
    _ = ∑' a : A, T.indicator (fun _ ↦ integerPrefixStepWeight k) a := by
      apply tsum_congr
      intro a
      by_cases h : a.val ≤ k <;> simp [prefixKernel, T, h]
    _ = _ := (_root_.tsum_subtype T (fun _ ↦ integerPrefixStepWeight k)).symm

/-- The count weighted by the prefix step widths sums to the reciprocal
weight of a fixed set of positive integers. -/
theorem integerPrefix_hasSum_stepWeight (A : Set ℕ)
    (hpos : ∀ a ∈ A, 0 < a) (hs : Summable (fun a : A ↦ (a.val : ℝ)⁻¹)) :
    HasSum (fun k ↦ ((integerPrefixSlice A k).card : ℝ) * integerPrefixStepWeight k)
      (∑' a : A, (a.val : ℝ)⁻¹) := by
  let f (a : A) (k : ℕ) := prefixKernel a.val k
  have hnonneg : 0 ≤ Function.uncurry f := by
    intro x
    unfold Function.uncurry f prefixKernel
    split
    · exact integerPrefixStepWeight_nonneg _
    · exact le_rfl
  have hrow (a : A) := hasSum_prefixKernel (hpos _ a.property)
  have hprod : Summable (Function.uncurry f) := by
    apply (summable_prod_of_nonneg hnonneg).mpr
    refine ⟨fun a ↦ (hrow a).summable, ?_⟩
    exact hs.congr fun a ↦ (hrow a).tsum_eq.symm
  have hswap := hprod.prod_symm
  have hlim : HasSum (fun k ↦ ∑' a : A, f a k) (∑' a : A, (a.val : ℝ)⁻¹) := by
    have hsouter : Summable (fun k ↦ ∑' a : A, f a k) :=
      ((summable_prod_of_nonneg (f := fun q : ℕ × A ↦ f q.2 q.1) (fun q ↦ hnonneg q.swap)).mp hswap).2
    have he := hprod.tsum_comm' (fun a ↦ (hrow a).summable) hswap.prod_factor
    rw [tsum_congr fun a ↦ (hrow a).tsum_eq] at he
    exact he ▸ hsouter.hasSum
  have he : (fun k ↦ ∑' a : A, f a k) =
      fun k ↦ ((integerPrefixSlice A k).card : ℝ) * integerPrefixStepWeight k :=
    funext (prefixKernel_tsum_column A hpos)
  rwa [he] at hlim

private noncomputable def reciprocalMonoidHom : ℕ →* ℝ where
  toFun n := (n:ℝ)⁻¹
  map_one' := by norm_num
  map_mul' a b := by
    rw [Nat.cast_mul, mul_inv_rev, mul_comm]

/-- The finite Euler factor for the density of rough numbers. -/
noncomputable def integerSmoothDensityFactor (Y : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE Y, (1 - (p:ℝ)⁻¹)

/-- The full reciprocal sum on the smooth numbers is the inverse rough-density
factor. -/
theorem hasSum_reciprocal_smoothNumbers (Y : ℕ) :
    HasSum (fun a : Nat.smoothNumbers (Y+1) ↦ (a.val:ℝ)⁻¹)
      (integerSmoothDensityFactor Y)⁻¹ := by
  have hnorm {p : ℕ} (hp : p.Prime) : ‖reciprocalMonoidHom p‖ < 1 := by
    change ‖(p:ℝ)⁻¹‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hprod :=
    (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hnorm (Y+1)).2
  simpa only [integerSmoothDensityFactor, Nat.primesLE, reciprocalMonoidHom, MonoidHom.coe_mk,
    OneHom.coe_mk, Finset.prod_inv_distrib] using hprod

theorem summable_reciprocal_smoothNumbers (Y : ℕ) :
    Summable (fun a : Nat.smoothNumbers (Y+1) ↦ (a.val:ℝ)⁻¹) :=
  (hasSum_reciprocal_smoothNumbers Y).summable

/-- The separately optimized cardinality after restricting to the smooth numbers. -/
noncomputable def integerSmoothPrefixMaximum (integral : Bool) (Y k : ℕ) : ℕ :=
  ((integerPrefixSlice (Nat.smoothNumbers (Y+1)) k).powerset.filter
    fun A : Finset ℕ ↦ IntegerPrefixAdmissible integral (A : Set ℕ)).sup Finset.card

private theorem integerSmoothPrefixMaximum_le (integral : Bool) (Y k : ℕ) :
    integerSmoothPrefixMaximum integral Y k ≤ (integerPrefixSlice (Nat.smoothNumbers (Y+1)) k).card :=
  Finset.sup_le (fun _ h ↦ card_le_card (mem_powerset.mp (mem_filter.mp h).1))

private theorem prefixSlice_card_le_smoothMaximum {A : Set ℕ} {integral : Bool} {Y : ℕ}
    (hS : A ⊆ Nat.smoothNumbers (Y+1)) (hadm : IntegerPrefixAdmissible integral A) (k : ℕ) :
    (integerPrefixSlice A k).card ≤ integerSmoothPrefixMaximum integral Y k := by
  unfold integerSmoothPrefixMaximum
  apply le_sup (f := Finset.card)
  refine mem_filter.mpr ⟨mem_powerset.mpr ?_, ?_⟩
  · intro n hn
    exact mem_integerPrefixSlice.mpr ⟨(mem_integerPrefixSlice.mp hn).1, hS (mem_integerPrefixSlice.mp hn).2⟩
  · intro a b c ha hb hc hab hbc he hd
    exact hadm (mem_integerPrefixSlice.mp ha).2 (mem_integerPrefixSlice.mp hb).2 (mem_integerPrefixSlice.mp hc).2 hab hbc he hd

private theorem integerSmoothPrefixMaximum_eq_cardMax (integral : Bool) (Y k : ℕ) (hk : k ≤ Y) :
    integerSmoothPrefixMaximum integral Y k = integerPrefixCardMax integral k := by
  have he : integerPrefixSlice (Nat.smoothNumbers (Y+1)) k = integerPrefix k := by
    ext n
    refine ⟨fun hn ↦ (mem_integerPrefixSlice.mp hn).1, fun hn ↦ mem_integerPrefixSlice.mpr ⟨hn, ?_⟩⟩
    obtain ⟨hnP, hnK⟩ := mem_Icc.mp hn
    exact Nat.mem_smoothNumbers_of_lt hnP (by omega)
  rw [integerSmoothPrefixMaximum, he, integerPrefixCardMax, integerPrefixWeightMax]
  simp only [sum_const, smul_eq_mul, mul_one]

private theorem summable_integerSmoothPrefixMaximum (integral : Bool) (Y : ℕ) :
    Summable (fun k ↦ (integerSmoothPrefixMaximum integral Y k : ℝ) * integerPrefixStepWeight k) := by
  have hs := (integerPrefix_hasSum_stepWeight (Nat.smoothNumbers (Y+1))
    (fun _ hn ↦ Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hn))
    (summable_reciprocal_smoothNumbers Y)).summable
  refine Summable.of_nonneg_of_le (fun _ ↦ by unfold integerPrefixStepWeight; positivity) ?_ hs
  intro k
  apply mul_le_mul_of_nonneg_right _ (integerPrefixStepWeight_nonneg k)
  exact_mod_cast integerSmoothPrefixMaximum_le integral Y k

theorem integerSmoothDensityFactor_pos (Y : ℕ) : 0 < integerSmoothDensityFactor Y := by
  apply Finset.prod_pos
  intro p hp
  apply sub_pos.mpr
  apply inv_lt_one_of_one_lt₀
  exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt

/-- The value `U` of the separately optimized smooth cutoff counts. -/
noncomputable def integerSmoothUpperOptimization (integral : Bool) (Y : ℕ) : ℝ :=
  integerSmoothDensityFactor Y *
    ∑' k, (integerSmoothPrefixMaximum integral Y k : ℝ) * integerPrefixStepWeight k

/-- The value `B` of the fixed smooth-set reciprocal optimization. -/
noncomputable def integerSmoothLowerOptimization (integral : Bool) (Y : ℕ) : ℝ :=
  integerSmoothDensityFactor Y * sSup
    {w : ℝ | ∃ A : Set ℕ, A ⊆ Nat.smoothNumbers (Y+1) ∧
      IntegerPrefixAdmissible integral A ∧ w = ∑' a : A, (a.val : ℝ)⁻¹}

private theorem integerPrefixSlice_filter (A : Set ℕ) {N k : ℕ} (hk : k ≤ N) :
    (integerPrefixSlice A N).filter (· ≤ k) = integerPrefixSlice A k := by
  ext a
  simp only [mem_filter, mem_integerPrefixSlice, integerPrefix, mem_Icc]
  constructor
  · rintro ⟨⟨⟨ha, _⟩, hA⟩, hka⟩
    exact ⟨⟨ha, hka⟩, hA⟩
  · rintro ⟨⟨ha, hka⟩, hA⟩
    exact ⟨⟨⟨ha,hka.trans hk⟩, hA⟩, hka⟩

private theorem weighted_deficit_ge_prefixLoss {integral : Bool} {N Y : ℕ} (hNY : N ≤ Y)
    {A : Set ℕ} (hS : A ⊆ Nat.smoothNumbers (Y+1))
    (hadm : IntegerPrefixAdmissible integral A) :
    (integerPrefixLoss integral N : ℝ) ≤
      (∑' k, (integerSmoothPrefixMaximum integral Y k : ℝ) * integerPrefixStepWeight k) -
        ∑' a : A, (a.val:ℝ)⁻¹ := by
  let f (k : ℕ) := (integerSmoothPrefixMaximum integral Y k : ℝ) * integerPrefixStepWeight k
  let g (k : ℕ) := ((integerPrefixSlice A k).card : ℝ) * integerPrefixStepWeight k
  have hf : Summable f := summable_integerSmoothPrefixMaximum integral Y
  have hgs : Summable (fun a : A ↦ (a.val:ℝ)⁻¹) := by
    let i : A → Nat.smoothNumbers (Y+1) := fun a ↦ ⟨a.val,hS a.property⟩
    have hi : Function.Injective i :=
      fun a b h ↦ Subtype.ext (congrArg (fun t : Nat.smoothNumbers (Y+1) ↦ t.val) h)
    simpa only [Function.comp_def, i] using
      (summable_reciprocal_smoothNumbers Y).comp_injective hi
  have hg : HasSum g (∑' a : A, (a.val:ℝ)⁻¹) :=
    integerPrefix_hasSum_stepWeight A
      (fun _ hn ↦ Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers (hS hn))) hgs
  have hnonneg (k : ℕ) : 0 ≤ f k - g k := by
    rw [sub_nonneg]
    apply mul_le_mul_of_nonneg_right _ (integerPrefixStepWeight_nonneg k)
    exact_mod_cast prefixSlice_card_le_smoothMaximum hS hadm k
  let A₀ := integerPrefixSlice A N
  have hA₀ : A₀ ⊆ integerPrefix N := filter_subset _ _
  have hAdm₀ : IntegerPrefixAdmissible integral (A₀ : Set ℕ) := by
    intro a b c ha hb hc hab hbc he hd
    exact hadm (mem_integerPrefixSlice.mp ha).2 (mem_integerPrefixSlice.mp hb).2 (mem_integerPrefixSlice.mp hc).2 hab hbc he hd
  have hq := integerPrefixLoss_le_deficit hA₀ hAdm₀
  have hfinite : (integerPrefixLoss integral N : ℝ) ≤ ∑ k ∈ integerPrefix N, (f k - g k) := by
    have hr := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hr
    refine hr.trans_eq (sum_congr rfl fun k hk ↦ ?_)
    have hkN := (mem_Icc.mp hk).2
    simp only [f, g, integerSmoothPrefixMaximum_eq_cardMax _ _ _ (hkN.trans hNY),
      A₀, integerPrefixSlice_filter A hkN, integerPrefixStepWeight]
    ring
  calc
    _ ≤ ∑ k ∈ integerPrefix N, (f k - g k) := hfinite
    _ ≤ ∑' k, (f k - g k) := (hf.sub hg.summable).sum_le_tsum _ (fun k _ ↦ hnonneg k)
    _ = _ := by
      rw [hf.tsum_sub hg.summable, hg.tsum_eq]

/-- The finite loss survives in the full smooth optimization for either
convention and every smoothness bound covering the prefix. -/
theorem integerSmoothOptimization_gap (integral : Bool) {N Y : ℕ} (hNY : N ≤ Y) :
    integerSmoothDensityFactor Y * (integerPrefixLoss integral N : ℝ) ≤
      integerSmoothUpperOptimization integral Y - integerSmoothLowerOptimization integral Y := by
  let U₀ := ∑' k, (integerSmoothPrefixMaximum integral Y k : ℝ) * integerPrefixStepWeight k
  let weights := {w : ℝ | ∃ A : Set ℕ, A ⊆ Nat.smoothNumbers (Y+1) ∧
    IntegerPrefixAdmissible integral A ∧ w = ∑' a : A, (a.val : ℝ)⁻¹}
  have hw : weights.Nonempty :=
    ⟨_, ∅, Set.empty_subset _, by intro a b c ha; exact ha.elim, rfl⟩
  have hbound : sSup weights ≤ U₀ - (integerPrefixLoss integral N : ℝ) := by
    apply csSup_le hw
    rintro _ ⟨A,hS,hA,rfl⟩
    have h := weighted_deficit_ge_prefixLoss hNY hS hA
    dsimp only [U₀]
    linarith
  have h := mul_le_mul_of_nonneg_left hbound (integerSmoothDensityFactor_pos Y).le
  rw [mul_sub] at h
  change _ ≤ integerSmoothDensityFactor Y * U₀ - integerSmoothDensityFactor Y * sSup weights
  linarith

/-- Even separately optimized smooth cutoff counts have normalized weight
at most the total smooth mass. -/
theorem integerSmoothUpperOptimization_le_one (integral : Bool) (Y : ℕ) :
    integerSmoothUpperOptimization integral Y ≤ 1 := by
  have hs := integerPrefix_hasSum_stepWeight (Nat.smoothNumbers (Y+1))
    (fun _ hn ↦ Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hn))
    (summable_reciprocal_smoothNumbers Y)
  have hcomp := (summable_integerSmoothPrefixMaximum integral Y).tsum_le_tsum
    (fun k ↦ mul_le_mul_of_nonneg_right (by
      exact_mod_cast integerSmoothPrefixMaximum_le integral Y k)
      (integerPrefixStepWeight_nonneg k)) hs.summable
  rw [hs.tsum_eq, (hasSum_reciprocal_smoothNumbers Y).tsum_eq] at hcomp
  unfold integerSmoothUpperOptimization
  have hc := integerSmoothDensityFactor_pos Y
  exact (mul_le_mul_of_nonneg_left hcomp hc.le).trans_eq (mul_inv_cancel₀ hc.ne')

/-- Combining the effective finite prefix loss with the smooth-factor bounds
gives the corresponding lower bound on the extremal density gap. -/
theorem integerDensityGap_of_smoothBounds (integral : Bool) {N Y : ℕ} (hNY : N ≤ Y)
    {b u v tail : ℝ}
    (hb : b ≤ integerSmoothLowerOptimization integral Y)
    (hu : v * integerSmoothUpperOptimization integral Y ≤ u)
    (hv : v ≤ 1) (htail : 1-v ≤ tail) :
    integerSmoothDensityFactor Y * (integerPrefixLoss integral N : ℝ) - tail ≤ u-b := by
  have hpenalty : (1-v) * integerSmoothUpperOptimization integral Y ≤ tail :=
    (mul_le_mul_of_nonneg_left (integerSmoothUpperOptimization_le_one integral Y)
      (sub_nonneg.mpr hv)).trans (by simpa using htail)
  have hgap := integerSmoothOptimization_gap integral hNY
  linarith only [hpenalty, hgap, hb, hu]

end GRHArticle.ProgressionFree
