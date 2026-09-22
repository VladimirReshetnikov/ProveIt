import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.Valuation.ValuationSubring
import Surreal.HahnSeries.StandardPart

/-!
# The convex scale subgroup and the unresolved error ideal

This file formalizes `epd:def:orderunit` and `epd:lem:ideal` of
`docs/surcomplex/expanding-polynomial-dynamics/article.tex`.

The source works in `K = k((t^Γ))` with `k ∈ {ℝ, ℂ}` and a nonzero ordered abelian group `Γ`.
Here `k` is an arbitrary field and `Γ` an arbitrary linearly ordered abelian group; neither
`Γ ≠ 0` nor divisibility is used. The valuation `v` is Mathlib's `HahnSeries.orderTop`, with
value `⊤` at zero, so `0 ∈ I_κ` is automatic, and `O` is `Surreal.HahnSeries.nonnegativeSubring`.

* `IsOrderUnit`, `scaleSubgroup` (`H_κ`), `errorSubgroup` (`I_κ` as an additive subgroup of
  `K`) and `errorIdeal` (`I_κ` as an ideal of `O`) are `epd:def:orderunit`.
  `image_errorIdeal` identifies the two versions of `I_κ`.
* `ordConnected_scaleSubgroup` is the convexity of `H_κ` in `epd:lem:ideal`;
  `scaleSubgroup_le` adds that `H_κ` lies in every convex subgroup containing `κ` (so for
  `0 ≤ κ` it is the smallest such subgroup), and
  `scaleSubgroup_eq_top_iff` that `H_κ = Γ` exactly for an order unit.
* `image_mul_errorSubgroup` and `span_singleton_mul_errorIdeal` are `q I_κ = I_κ`.
* `mem_errorSubgroup_iff_forall_pow`, `coe_errorSubgroup_eq_iInter` and
  `errorIdeal_eq_iInf_span_pow` are `I_κ = ⋂ₙ qⁿ O`.
* `errorSubgroup_eq_bot_iff` and `errorIdeal_eq_bot_iff` are `I_κ = 0 ↔ κ` is an order unit;
  `errorSubgroup_ne_bot` is the nonvanishing in the non-order-unit case.
* Mathlib has no topology on Hahn series, so clopenness is stated through the valuation balls
  `{y : v(y - x) > η}` that form the source's neighbourhood basis: `exists_ball_subset` is the
  ball `{v > η} ⊆ I_κ`, `exists_ball_mem_iff` shows that one radius works uniformly for `I_κ`
  and its complement, and `exists_ball_subset_of_mem` and `exists_ball_subset_compl_of_not_mem`
  are openness and closedness.
* The coarsened valuation `K^× → Γ/H_κ` is realized through its valuation ring
  `coarseValuationSubring`, the Mathlib `ValuationSubring` of all `h` with `v(h) ≥ γ` for some
  `γ ∈ H_κ`, since Mathlib has no ordered quotient of an ordered group by a convex subgroup.
  `coarseValuation_le_iff` and `coarseValuation_eq_iff` show that its valuation compares values
  of `v` modulo `H_κ`, which identifies its value group with `Γ/H_κ` informally (no quotient
  group is constructed). Finally
  `nonunits_coarseValuationSubring`, `image_maximalIdeal_coarseValuationSubring` and
  `mem_maximalIdeal_coarseValuationSubring_iff` identify `I_κ` with its maximal ideal, and
  `mem_errorSubgroup_iff_eq_zero_or` is the closing sentence of the proof: `h ∈ I_κ` iff
  `h = 0` or `v(h)` exceeds every element of `H_κ`.

Hypotheses are never stronger than the source's: `q I_κ = I_κ` and the maximal-ideal
description are stated with `0 ≤ κ`, while `I_κ = ⋂ₙ qⁿ O`, `I_κ = 0 ↔ κ` is an order unit
and the ball statements use the source's `0 < κ`.
-/

namespace Surreal.ScaleIdeal

open _root_.HahnSeries Surreal.HahnSeries

section Group

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- `epd:def:orderunit`: a positive `u` is an order unit if every element of `Γ` is at most
some ordinary multiple of `u`. -/
def IsOrderUnit (u : Γ) : Prop :=
  0 < u ∧ ∀ γ : Γ, ∃ n : ℕ, γ ≤ n • u

omit [IsOrderedAddMonoid Γ] in
/-- A positive scale fails to be an order unit exactly when some element exceeds all of its
multiples. -/
theorem not_isOrderUnit_iff {κ : Γ} (hκ : 0 < κ) :
    ¬ IsOrderUnit κ ↔ ∃ η : Γ, ∀ n : ℕ, n • κ < η := by
  simp only [IsOrderUnit, hκ, true_and, not_forall, not_exists, not_le]

/-- `epd:def:orderunit`: the scale subgroup `H_κ = {γ : |γ| ≤ n κ for some n}`. -/
def scaleSubgroup (κ : Γ) : AddSubgroup Γ where
  carrier := {γ | ∃ n : ℕ, |γ| ≤ n • κ}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨n, hn⟩ ⟨m, hm⟩
    exact ⟨n + m, (abs_add_le a b).trans (by rw [add_nsmul]; exact add_le_add hn hm)⟩
  neg_mem' := by
    rintro a ⟨n, hn⟩
    exact ⟨n, by rwa [abs_neg]⟩

theorem mem_scaleSubgroup {κ γ : Γ} : γ ∈ scaleSubgroup κ ↔ ∃ n : ℕ, |γ| ≤ n • κ :=
  Iff.rfl

/-- `epd:lem:ideal`: the scale subgroup `H_κ` is convex. -/
theorem ordConnected_scaleSubgroup (κ : Γ) : (scaleSubgroup κ : Set Γ).OrdConnected := by
  refine ⟨fun a ha b hb x hx => ?_⟩
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  refine ⟨n + m, ?_⟩
  rw [add_nsmul]
  calc |x| ≤ max |a| |b| := abs_le_max_abs_abs hx.1 hx.2
    _ ≤ |a| + |b| := max_le_add_of_nonneg (abs_nonneg a) (abs_nonneg b)
    _ ≤ n • κ + m • κ := add_le_add hn hm

theorem nsmul_mem_scaleSubgroup {κ : Γ} (hκ : 0 ≤ κ) (n : ℕ) : n • κ ∈ scaleSubgroup κ :=
  ⟨n, (abs_of_nonneg (nsmul_nonneg hκ n)).le⟩

theorem self_mem_scaleSubgroup {κ : Γ} (hκ : 0 ≤ κ) : κ ∈ scaleSubgroup κ := by
  simpa using nsmul_mem_scaleSubgroup hκ 1

/-- `H_κ` lies in every convex subgroup of `Γ` containing `κ`; with `self_mem_scaleSubgroup`
(for `0 ≤ κ`) it is the smallest such subgroup. -/
theorem scaleSubgroup_le {κ : Γ} {G : AddSubgroup Γ} (hG : (G : Set Γ).OrdConnected)
    (hκ : κ ∈ G) : scaleSubgroup κ ≤ G := by
  rintro γ ⟨n, hn⟩
  have h1 : n • κ ∈ G := nsmul_mem hκ n
  exact hG.out (neg_mem h1) h1 ⟨(abs_le.mp hn).1, (abs_le.mp hn).2⟩

/-- A positive scale is an order unit exactly when its scale subgroup is all of `Γ`. -/
theorem scaleSubgroup_eq_top_iff {κ : Γ} (hκ : 0 < κ) :
    scaleSubgroup κ = ⊤ ↔ IsOrderUnit κ := by
  rw [AddSubgroup.eq_top_iff']
  constructor
  · intro h
    refine ⟨hκ, fun γ => ?_⟩
    obtain ⟨n, hn⟩ := h γ
    exact ⟨n, (le_abs_self γ).trans hn⟩
  · rintro ⟨-, h⟩ γ
    exact h |γ|

end Group

section Hahn

variable {Γ k : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field k]

/-- The valuation of an inverse, with `⊤` retained at zero. -/
theorem orderTop_inv (x : k⟦Γ⟧) : x⁻¹.orderTop = -x.orderTop := by
  have h := (addVal Γ k).map_inv (x := x)
  rwa [addVal_apply, addVal_apply] at h

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem ne_zero_of_orderTop_eq {κ : Γ} {q : k⟦Γ⟧} (hq : q.orderTop = κ) : q ≠ 0 := by
  rintro rfl
  simp at hq

theorem orderTop_pow_eq {κ : Γ} {q : k⟦Γ⟧} (hq : q.orderTop = κ) (n : ℕ) :
    (q ^ n).orderTop = ((n • κ : Γ) : WithTop Γ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, orderTop_mul, ih, hq, succ_nsmul, WithTop.coe_add]

/-- `epd:def:orderunit`: the error set `I_κ = {h : v(h) > n κ for every n}`, as an additive
subgroup of `K`. The convention `v(0) = ⊤` puts `0` in it. -/
def errorSubgroup (κ : Γ) : AddSubgroup k⟦Γ⟧ where
  carrier := {h | ∀ n : ℕ, ((n • κ : Γ) : WithTop Γ) < h.orderTop}
  zero_mem' := fun n => by rw [orderTop_zero]; exact WithTop.coe_lt_top _
  add_mem' := fun ha hb n => (lt_min (ha n) (hb n)).trans_le min_orderTop_le_orderTop_add
  neg_mem' := fun ha n => by rw [orderTop_neg]; exact ha n

omit [IsOrderedAddMonoid Γ] in
theorem mem_errorSubgroup {κ : Γ} {h : k⟦Γ⟧} :
    h ∈ errorSubgroup κ ↔ ∀ n : ℕ, ((n • κ : Γ) : WithTop Γ) < h.orderTop :=
  Iff.rfl

omit [IsOrderedAddMonoid Γ] in
theorem orderTop_pos_of_mem_errorSubgroup {κ : Γ} {h : k⟦Γ⟧} (hh : h ∈ errorSubgroup κ) :
    0 < h.orderTop := by
  simpa using hh 0

/-- Every element of `I_κ` lies in `O`. -/
theorem mem_nonnegativeSubring_of_mem_errorSubgroup {κ : Γ} {h : k⟦Γ⟧}
    (hh : h ∈ errorSubgroup κ) : h ∈ nonnegativeSubring Γ k :=
  (mem_nonnegativeSubring h).mpr (orderTop_pos_of_mem_errorSubgroup hh).le

/-- `I_κ` is stable under multiplication by elements of nonnegative valuation. -/
theorem mul_mem_errorSubgroup {κ : Γ} {a h : k⟦Γ⟧} (ha : 0 ≤ a.orderTop)
    (hh : h ∈ errorSubgroup κ) : a * h ∈ errorSubgroup κ := fun n => by
  rw [orderTop_mul]
  exact (hh n).trans_le (le_add_of_nonneg_left ha)

/-- `epd:lem:ideal`: `I_κ` is an ideal of `O`. -/
def errorIdeal (κ : Γ) : Ideal (nonnegativeSubring Γ k) where
  carrier := {h | (h : k⟦Γ⟧) ∈ errorSubgroup κ}
  zero_mem' := (errorSubgroup κ).zero_mem
  add_mem' := fun ha hb => (errorSubgroup κ).add_mem ha hb
  smul_mem' := fun c _ hh => mul_mem_errorSubgroup ((mem_nonnegativeSubring _).mp c.2) hh

theorem mem_errorIdeal {κ : Γ} {h : nonnegativeSubring Γ k} :
    h ∈ errorIdeal κ ↔ (h : k⟦Γ⟧) ∈ errorSubgroup κ :=
  Iff.rfl

/-- The ideal `errorIdeal κ` of `O` and the subgroup `errorSubgroup κ` of `K` are the same set
`I_κ`. -/
theorem image_errorIdeal (κ : Γ) :
    ((↑) : nonnegativeSubring Γ k → k⟦Γ⟧) ''
        (errorIdeal (k := k) κ : Set (nonnegativeSubring Γ k)) =
      (errorSubgroup (k := k) κ : Set k⟦Γ⟧) := by
  ext h
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hh
    exact ⟨⟨h, mem_nonnegativeSubring_of_mem_errorSubgroup hh⟩, hh, rfl⟩

/-- Division by an element of valuation `κ` preserves `I_κ`. -/
theorem exists_mul_eq_of_mem {κ : Γ} {q h : k⟦Γ⟧} (hq : q.orderTop = κ)
    (hh : h ∈ errorSubgroup κ) : ∃ y ∈ errorSubgroup κ, q * y = h := by
  have hq0 := ne_zero_of_orderTop_eq hq
  refine ⟨q⁻¹ * h, fun n => ?_, mul_inv_cancel_left₀ hq0 h⟩
  have hv : h.orderTop = κ + (q⁻¹ * h).orderTop := by
    rw [← hq, ← orderTop_mul, mul_inv_cancel_left₀ hq0]
  have h1 := hh (n + 1)
  rw [hv, succ_nsmul', WithTop.coe_add] at h1
  exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp h1

/-- `epd:lem:ideal`: `q I_κ = I_κ` for every `q` with `v(q) = κ`, as sets of `K`. Only
`0 ≤ κ` is needed. -/
theorem image_mul_errorSubgroup {κ : Γ} (hκ : 0 ≤ κ) {q : k⟦Γ⟧} (hq : q.orderTop = κ) :
    (q * ·) '' (errorSubgroup (k := k) κ : Set k⟦Γ⟧) = errorSubgroup (k := k) κ := by
  ext h
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mul_mem_errorSubgroup (by rw [hq]; exact_mod_cast hκ) hy
  · intro hh
    obtain ⟨y, hy, rfl⟩ := exists_mul_eq_of_mem hq hh
    exact ⟨y, hy, rfl⟩

/-- `epd:lem:ideal`: `q I_κ = I_κ` as ideals of `O`, for `q ∈ O` with `v(q) = κ`. -/
theorem span_singleton_mul_errorIdeal {κ : Γ} {q : nonnegativeSubring Γ k}
    (hq : (q : k⟦Γ⟧).orderTop = κ) : Ideal.span {q} * errorIdeal κ = errorIdeal κ := by
  ext x
  rw [Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (errorIdeal κ).mul_mem_left q hz
  · intro hx
    obtain ⟨y, hy, hxy⟩ := exists_mul_eq_of_mem hq hx
    exact ⟨⟨y, mem_nonnegativeSubring_of_mem_errorSubgroup hy⟩, hy, Subtype.ext hxy⟩

/-- `epd:lem:ideal`: `I_κ = ⋂ₙ qⁿ O` for every `q` with `v(q) = κ > 0`. -/
theorem mem_errorSubgroup_iff_forall_pow {κ : Γ} (hκ : 0 < κ) {q : k⟦Γ⟧}
    (hq : q.orderTop = κ) (h : k⟦Γ⟧) :
    h ∈ errorSubgroup κ ↔ ∀ n : ℕ, ∃ y ∈ nonnegativeSubring Γ k, q ^ n * y = h := by
  have hq0 := ne_zero_of_orderTop_eq hq
  constructor
  · intro hh n
    have hqn : q ^ n ≠ 0 := pow_ne_zero n hq0
    refine ⟨(q ^ n)⁻¹ * h, ?_, mul_inv_cancel_left₀ hqn h⟩
    rw [mem_nonnegativeSubring]
    have hv : h.orderTop = ((n • κ : Γ) : WithTop Γ) + ((q ^ n)⁻¹ * h).orderTop := by
      rw [← orderTop_pow_eq hq n, ← orderTop_mul, mul_inv_cancel_left₀ hqn]
    have h1 := hh n
    rw [hv] at h1
    have h2 : ((n • κ : Γ) : WithTop Γ) + 0 <
        ((n • κ : Γ) : WithTop Γ) + ((q ^ n)⁻¹ * h).orderTop := by
      rwa [add_zero]
    exact ((WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp h2).le
  · intro hh n
    obtain ⟨y, hy, rfl⟩ := hh (n + 1)
    rw [orderTop_mul, orderTop_pow_eq hq]
    calc ((n • κ : Γ) : WithTop Γ) < (((n + 1) • κ : Γ) : WithTop Γ) := by
          rw [WithTop.coe_lt_coe, succ_nsmul]
          exact lt_add_of_pos_right _ hκ
      _ ≤ _ := le_add_of_nonneg_right ((mem_nonnegativeSubring _).mp hy)

/-- `epd:lem:ideal`: `I_κ = ⋂ₙ qⁿ O` as an equality of subsets of `K`. -/
theorem coe_errorSubgroup_eq_iInter {κ : Γ} (hκ : 0 < κ) {q : k⟦Γ⟧} (hq : q.orderTop = κ) :
    (errorSubgroup (k := k) κ : Set k⟦Γ⟧) =
      ⋂ n : ℕ, (q ^ n * ·) '' (nonnegativeSubring Γ k : Set k⟦Γ⟧) := by
  ext h
  simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_image]
  exact mem_errorSubgroup_iff_forall_pow hκ hq h

/-- `epd:lem:ideal`: `I_κ = ⋂ₙ qⁿ O` as ideals of `O`, for `q ∈ O` with `v(q) = κ > 0`. -/
theorem errorIdeal_eq_iInf_span_pow {κ : Γ} (hκ : 0 < κ) {q : nonnegativeSubring Γ k}
    (hq : (q : k⟦Γ⟧).orderTop = κ) : errorIdeal κ = ⨅ n : ℕ, Ideal.span {q ^ n} := by
  ext x
  rw [Submodule.mem_iInf, mem_errorIdeal, mem_errorSubgroup_iff_forall_pow hκ hq]
  refine forall_congr' fun n => ?_
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hxy.symm)⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, c.2, by simp⟩

omit [IsOrderedAddMonoid Γ] in
/-- A monomial beyond every multiple of `κ` lies in `I_κ`. -/
theorem single_mem_errorSubgroup {κ η : Γ} (hη : ∀ n : ℕ, n • κ < η) (c : k) :
    single η c ∈ errorSubgroup κ := fun n =>
  (WithTop.coe_lt_coe.mpr (hη n)).trans_le orderTop_single_le

omit [IsOrderedAddMonoid Γ] in
/-- The ball `{v > η}` lies in `I_κ` once `η` exceeds every multiple of `κ`. -/
theorem mem_errorSubgroup_of_lt_orderTop {κ η : Γ} (hη : ∀ n : ℕ, n • κ < η) {x : k⟦Γ⟧}
    (hx : (η : WithTop Γ) < x.orderTop) : x ∈ errorSubgroup κ := fun n =>
  (WithTop.coe_lt_coe.mpr (hη n)).trans hx

omit [IsOrderedAddMonoid Γ] in
/-- For an order unit, no finite valuation exceeds all multiples, so `I_κ = 0`. -/
theorem eq_zero_of_mem_errorSubgroup {κ : Γ} (hκ : IsOrderUnit κ) {h : k⟦Γ⟧}
    (hh : h ∈ errorSubgroup κ) : h = 0 := by
  by_contra h0
  obtain ⟨n, hn⟩ := hκ.2 h.order
  have h1 := hh n
  rw [← order_eq_orderTop_of_ne_zero h0, WithTop.coe_lt_coe] at h1
  exact absurd hn (not_le.mpr h1)

omit [IsOrderedAddMonoid Γ] in
/-- `epd:lem:ideal`: for `κ > 0`, `I_κ = 0` exactly when `κ` is an order unit. -/
theorem errorSubgroup_eq_bot_iff {κ : Γ} (hκ : 0 < κ) :
    errorSubgroup (k := k) κ = ⊥ ↔ IsOrderUnit κ := by
  constructor
  · intro h
    by_contra hu
    obtain ⟨η, hη⟩ := (not_isOrderUnit_iff hκ).mp hu
    have hmem := single_mem_errorSubgroup (k := k) hη 1
    rw [h, AddSubgroup.mem_bot] at hmem
    exact single_ne_zero one_ne_zero hmem
  · intro hu
    exact (AddSubgroup.eq_bot_iff_forall _).mpr fun h hh => eq_zero_of_mem_errorSubgroup hu hh

omit [IsOrderedAddMonoid Γ] in
/-- `epd:lem:ideal`: if `κ > 0` is not an order unit, then `I_κ` is nonzero. -/
theorem errorSubgroup_ne_bot {κ : Γ} (hκ : 0 < κ) (hu : ¬ IsOrderUnit κ) :
    errorSubgroup (k := k) κ ≠ ⊥ :=
  fun h => hu ((errorSubgroup_eq_bot_iff hκ).mp h)

/-- `epd:lem:ideal`: for `κ > 0`, the ideal `I_κ` of `O` is zero exactly when `κ` is an order
unit. -/
theorem errorIdeal_eq_bot_iff {κ : Γ} (hκ : 0 < κ) :
    errorIdeal (k := k) κ = ⊥ ↔ IsOrderUnit κ := by
  rw [← errorSubgroup_eq_bot_iff (k := k) hκ, Submodule.eq_bot_iff,
    AddSubgroup.eq_bot_iff_forall]
  constructor
  · intro h x hx
    exact congrArg Subtype.val (h ⟨x, mem_nonnegativeSubring_of_mem_errorSubgroup hx⟩ hx)
  · intro h x hx
    exact Subtype.ext (h x hx)

omit [IsOrderedAddMonoid Γ] in
/-- `epd:lem:ideal` (openness): if `κ > 0` is not an order unit, some ball `{v > η}` lies in
`I_κ`. -/
theorem exists_ball_subset {κ : Γ} (hκ : 0 < κ) (hu : ¬ IsOrderUnit κ) :
    ∃ η : Γ, ∀ x : k⟦Γ⟧, (η : WithTop Γ) < x.orderTop → x ∈ errorSubgroup κ := by
  obtain ⟨η, hη⟩ := (not_isOrderUnit_iff hκ).mp hu
  exact ⟨η, fun x hx => mem_errorSubgroup_of_lt_orderTop hη hx⟩

omit [IsOrderedAddMonoid Γ] in
/-- `epd:lem:ideal` (clopenness): if `κ > 0` is not an order unit, there is one radius `η`
such that membership in `I_κ` is constant on every ball `{y : v(y - x) > η}`. -/
theorem exists_ball_mem_iff {κ : Γ} (hκ : 0 < κ) (hu : ¬ IsOrderUnit κ) :
    ∃ η : Γ, ∀ x y : k⟦Γ⟧, (η : WithTop Γ) < (y - x).orderTop →
      (x ∈ errorSubgroup κ ↔ y ∈ errorSubgroup κ) := by
  obtain ⟨η, hη⟩ := exists_ball_subset (k := k) hκ hu
  refine ⟨η, fun x y hxy => ?_⟩
  have hd := hη _ hxy
  constructor
  · intro hx
    simpa using (errorSubgroup κ).add_mem hx hd
  · intro hy
    simpa using (errorSubgroup κ).sub_mem hy hd

omit [IsOrderedAddMonoid Γ] in
/-- `epd:lem:ideal`: `I_κ` is open in the valuation topology when `κ > 0` is not an order
unit. -/
theorem exists_ball_subset_of_mem {κ : Γ} (hκ : 0 < κ) (hu : ¬ IsOrderUnit κ) {x : k⟦Γ⟧}
    (hx : x ∈ errorSubgroup κ) :
    ∃ η : Γ, ∀ y : k⟦Γ⟧, (η : WithTop Γ) < (y - x).orderTop → y ∈ errorSubgroup κ := by
  obtain ⟨η, hη⟩ := exists_ball_mem_iff (k := k) hκ hu
  exact ⟨η, fun y hy => (hη x y hy).mp hx⟩

omit [IsOrderedAddMonoid Γ] in
/-- `epd:lem:ideal`: `I_κ` is closed in the valuation topology when `κ > 0` is not an order
unit. -/
theorem exists_ball_subset_compl_of_not_mem {κ : Γ} (hκ : 0 < κ) (hu : ¬ IsOrderUnit κ)
    {x : k⟦Γ⟧} (hx : x ∉ errorSubgroup κ) :
    ∃ η : Γ, ∀ y : k⟦Γ⟧, (η : WithTop Γ) < (y - x).orderTop → y ∉ errorSubgroup κ := by
  obtain ⟨η, hη⟩ := exists_ball_mem_iff (k := k) hκ hu
  exact ⟨η, fun y hy hy' => hx ((hη x y hy).mpr hy')⟩

/-- `epd:lem:ideal`: the valuation ring of the coarsened valuation `K^× → Γ/H_κ`, consisting
of the `h` whose value is at least some element of `H_κ`. -/
def coarseValuationSubring (κ : Γ) : ValuationSubring k⟦Γ⟧ where
  carrier := {h | ∃ γ ∈ scaleSubgroup κ, (γ : WithTop Γ) ≤ h.orderTop}
  zero_mem' := ⟨0, (scaleSubgroup κ).zero_mem, by simp⟩
  one_mem' := ⟨0, (scaleSubgroup κ).zero_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨γ, hγ, ha⟩ ⟨δ, hδ, hb⟩
    refine ⟨min γ δ, ?_, ?_⟩
    · rcases min_choice γ δ with h | h <;> rw [h] <;> assumption
    · rw [WithTop.coe_min]
      exact (min_le_min ha hb).trans min_orderTop_le_orderTop_add
  mul_mem' := by
    rintro a b ⟨γ, hγ, ha⟩ ⟨δ, hδ, hb⟩
    refine ⟨γ + δ, add_mem hγ hδ, ?_⟩
    rw [orderTop_mul, WithTop.coe_add]
    exact add_le_add ha hb
  neg_mem' := by
    rintro a ⟨γ, hγ, ha⟩
    exact ⟨γ, hγ, by rwa [orderTop_neg]⟩
  mem_or_inv_mem' := by
    intro x
    by_cases hx : 0 ≤ x.orderTop
    · exact Or.inl ⟨0, (scaleSubgroup κ).zero_mem, by simpa using hx⟩
    · refine Or.inr ⟨0, (scaleSubgroup κ).zero_mem, ?_⟩
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      rw [← order_eq_orderTop_of_ne_zero hx0] at hx
      have hneg : x.order < 0 := by simpa using hx
      rw [orderTop_inv, ← order_eq_orderTop_of_ne_zero hx0,
        ← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.coe_le_coe]
      exact neg_nonneg.mpr hneg.le

theorem mem_coarseValuationSubring {κ : Γ} {h : k⟦Γ⟧} :
    h ∈ coarseValuationSubring κ ↔ ∃ γ ∈ scaleSubgroup κ, (γ : WithTop Γ) ≤ h.orderTop :=
  Iff.rfl

/-- The coarsened valuation ring contains `O`. -/
theorem nonnegativeSubring_le_coarseValuationSubring (κ : Γ) :
    nonnegativeSubring Γ k ≤ (coarseValuationSubring κ).toSubring := fun h hh =>
  ⟨0, (scaleSubgroup κ).zero_mem, by
    rw [WithTop.coe_zero]
    exact (mem_nonnegativeSubring h).mp hh⟩

/-- The coarsened valuation compares values of `v` modulo `H_κ`: `w(x) ≤ w(y)` in Mathlib's
multiplicative convention means that the class of `v(y)` in `Γ/H_κ` is at most that of
`v(x)`. -/
theorem coarseValuation_le_iff {κ : Γ} {x y : k⟦Γ⟧} (hy : y ≠ 0) :
    (coarseValuationSubring κ).valuation x ≤ (coarseValuationSubring κ).valuation y ↔
      ∃ γ ∈ scaleSubgroup κ, ((y.order + γ : Γ) : WithTop Γ) ≤ x.orderTop := by
  rw [ValuationSubring.valuation_le_iff]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨γ, hγ, ha⟩ := mem_coarseValuationSubring.mp a.2
    refine ⟨γ, hγ, ?_⟩
    calc ((y.order + γ : Γ) : WithTop Γ) = (γ : WithTop Γ) + y.order := by
          rw [add_comm, WithTop.coe_add]
      _ ≤ (a : k⟦Γ⟧).orderTop + y.orderTop :=
          add_le_add ha (order_eq_orderTop_of_ne_zero hy).le
      _ = ((a : k⟦Γ⟧) * y).orderTop := (orderTop_mul _ _).symm
  · rintro ⟨γ, hγ, hle⟩
    refine ⟨⟨x * y⁻¹, mem_coarseValuationSubring.mpr ⟨γ, hγ, ?_⟩⟩,
      inv_mul_cancel_right₀ hy x⟩
    have hv : x.orderTop = (y.order : WithTop Γ) + (x * y⁻¹).orderTop := by
      conv_lhs => rw [← inv_mul_cancel_right₀ hy x]
      rw [orderTop_mul, ← order_eq_orderTop_of_ne_zero hy, add_comm]
    rw [hv, WithTop.coe_add] at hle
    exact (WithTop.add_le_add_iff_left WithTop.coe_ne_top).mp hle

/-- `epd:lem:ideal`: the coarsened valuation takes the same value at two nonzero elements
exactly when their values of `v` agree modulo `H_κ`; this identifies its value group with
`Γ/H_κ` through `v(x) ↦ w(x)`, without constructing the quotient group. -/
theorem coarseValuation_eq_iff {κ : Γ} {x y : k⟦Γ⟧} (hx : x ≠ 0) (hy : y ≠ 0) :
    (coarseValuationSubring κ).valuation x = (coarseValuationSubring κ).valuation y ↔
      x.order - y.order ∈ scaleSubgroup κ := by
  rw [le_antisymm_iff, coarseValuation_le_iff hy, coarseValuation_le_iff hx,
    ← order_eq_orderTop_of_ne_zero hx, ← order_eq_orderTop_of_ne_zero hy]
  simp only [WithTop.coe_le_coe]
  constructor
  · rintro ⟨⟨γ, hγ, h1⟩, ⟨δ, hδ, h2⟩⟩
    refine (ordConnected_scaleSubgroup κ).out hγ (neg_mem hδ) ⟨le_sub_iff_add_le'.mpr h1, ?_⟩
    rw [sub_le_iff_le_add, neg_add_eq_sub, le_sub_iff_add_le]
    exact h2
  · intro hd
    exact ⟨⟨x.order - y.order, hd, by simp⟩, ⟨-(x.order - y.order), neg_mem hd, by simp⟩⟩

/-- The nonunits of the coarsened valuation ring are the `h` whose value exceeds every
element of `H_κ`. -/
theorem mem_nonunits_coarseValuationSubring {κ : Γ} {h : k⟦Γ⟧} :
    h ∈ (coarseValuationSubring κ).nonunits ↔
      ∀ γ ∈ scaleSubgroup κ, (γ : WithTop Γ) < h.orderTop := by
  rw [ValuationSubring.mem_nonunits_iff_or]
  by_cases h0 : h = 0
  · simp [h0]
  simp only [h0, false_or, mem_coarseValuationSubring, not_exists, not_and, not_le]
  rw [orderTop_inv, ← order_eq_orderTop_of_ne_zero h0]
  simp_rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.coe_lt_coe]
  constructor
  · intro H γ hγ
    exact neg_lt_neg_iff.mp (H (-γ) (neg_mem hγ))
  · intro H γ hγ
    exact neg_lt.mp (H (-γ) (neg_mem hγ))

/-- `epd:lem:ideal`: `h ∈ I_κ` iff `v(h)` exceeds every element of `H_κ` (with `v(0) = ⊤`). -/
theorem mem_errorSubgroup_iff_forall_scaleSubgroup {κ : Γ} (hκ : 0 ≤ κ) {h : k⟦Γ⟧} :
    h ∈ errorSubgroup κ ↔ ∀ γ ∈ scaleSubgroup κ, (γ : WithTop Γ) < h.orderTop := by
  constructor
  · rintro hh γ ⟨n, hn⟩
    exact (WithTop.coe_le_coe.mpr ((le_abs_self γ).trans hn)).trans_lt (hh n)
  · intro hh n
    exact hh _ (nsmul_mem_scaleSubgroup hκ n)

/-- `epd:lem:ideal`, closing sentence of the proof: `h ∈ I_κ` iff `h = 0` or `v(h)` exceeds
every element of `H_κ`. -/
theorem mem_errorSubgroup_iff_eq_zero_or {κ : Γ} (hκ : 0 ≤ κ) {h : k⟦Γ⟧} :
    h ∈ errorSubgroup κ ↔ h = 0 ∨ ∀ γ ∈ scaleSubgroup κ, γ < h.order := by
  rw [mem_errorSubgroup_iff_forall_scaleSubgroup hκ]
  by_cases h0 : h = 0
  · simp [h0]
  · simp only [h0, false_or, ← order_eq_orderTop_of_ne_zero h0, WithTop.coe_lt_coe]

/-- `epd:lem:ideal`: `I_κ` is the set of nonunits of the coarsened valuation ring. -/
theorem nonunits_coarseValuationSubring {κ : Γ} (hκ : 0 ≤ κ) :
    ((coarseValuationSubring (k := k) κ).nonunits : Set k⟦Γ⟧) = errorSubgroup (k := k) κ := by
  ext h
  exact mem_nonunits_coarseValuationSubring.trans
    (mem_errorSubgroup_iff_forall_scaleSubgroup hκ).symm

/-- `epd:lem:ideal`: `I_κ` is the maximal ideal of the coarsened valuation ring. -/
theorem image_maximalIdeal_coarseValuationSubring {κ : Γ} (hκ : 0 ≤ κ) :
    ((↑) : coarseValuationSubring (k := k) κ → k⟦Γ⟧) ''
        (IsLocalRing.maximalIdeal (coarseValuationSubring (k := k) κ) :
          Set (coarseValuationSubring (k := k) κ)) =
      (errorSubgroup (k := k) κ : Set k⟦Γ⟧) := by
  rw [ValuationSubring.image_maximalIdeal]
  exact nonunits_coarseValuationSubring hκ

/-- `epd:lem:ideal`: an element of the coarsened valuation ring lies in its maximal ideal
exactly when it lies in `I_κ`. -/
theorem mem_maximalIdeal_coarseValuationSubring_iff {κ : Γ} (hκ : 0 ≤ κ)
    (x : coarseValuationSubring (k := k) κ) :
    x ∈ IsLocalRing.maximalIdeal (coarseValuationSubring κ) ↔ (x : k⟦Γ⟧) ∈ errorSubgroup κ := by
  rw [← ValuationSubring.coe_mem_nonunits_iff, ← SetLike.mem_coe,
    nonunits_coarseValuationSubring hκ, SetLike.mem_coe]

end Hahn

end Surreal.ScaleIdeal
