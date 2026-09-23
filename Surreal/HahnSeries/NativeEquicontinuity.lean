import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.TFAE
import Surreal.HahnSeries.ScaleIdeal

/-!
# Native equicontinuity of polynomial iterates without an order unit

This file formalizes `epd:prop:budget`, `epd:thm:general`, `epd:def:affine-julia` and
`epd:cor:empty-affine` of `docs/surcomplex/expanding-polynomial-dynamics/article.tex`.

The source works in `K = k((t^Γ))` with `k ∈ {ℝ, ℂ}`, a nonzero ordered abelian group `Γ`, the
valuation `v` (least exponent, `v(0) = +∞`) and the native uniformity whose entourages are
`{(x, y) : v(x - y) > γ}`. Mathlib has no uniform structure on Hahn series, so equicontinuity is
stated in this explicit valuation-ball form, which is the source's definition.

Generic part: `K` is any commutative ring, `Γ` any linearly ordered abelian group and `v` any
additive valuation `K → WithTop Γ`. The iterate `fⁿ` is `(fun z => f.eval z)^[n]`.
* `orbit_budget` is `epd:eq:orbitbudget`, `v(fⁿ(x)) ≥ -(d + 1)ⁿ A`, and `difference_budget`
  is `epd:eq:differencebudget`, `v(fⁿ(x) - fⁿ(y)) ≥ v(x - y) - ((d + 1)ⁿ - 1) A`, stated
  additively as `v(x - y) ≤ v(fⁿ(x) - fⁿ(y)) + ((d + 1)ⁿ - 1) A` in `WithTop Γ`;
  `budget` combines them (`epd:prop:budget`). The one-step estimates are `orbit_step` and
  `difference_step`, the latter through the divided difference of `geom_sum₂_mul`.
* `OrbitBounded`, `IterEquicontinuousAt` and `IterUniformEquicontinuousOn` are the notions (ii),
  (iii) and the uniform notion of `epd:thm:general`; `disk v A` is `D_A = {z : v(z) ≥ -A}`, and
  `mem_disk_of_le` says that `D_A` contains the ball `{y : v(y - x) ≥ -A}` around each of its
  points, and `isNativeOpen_disk` that `D_A` is native open.
* `uniformEquicontinuousOn_disk` is the closing sentence of `epd:thm:general`; `orbitBounded`
  and `iterEquicontinuousAt` are (i) ⇒ (ii) and (i) ⇒ (iii); `not_orbitBounded_of_isOrderUnit`
  and `not_iterEquicontinuousAt_of_isOrderUnit` are the converse counterexample `f = t^{-u} X`.
  `tfae_general` is the equivalence (i) ⇔ (ii) ⇔ (iii), under the hypothesis that `v` attains
  every value of `Γ` (used only for the converse, which needs elements `t^γ`). There (iii) is
  pointwise equicontinuity at every point; the source's local form, uniform equicontinuity on
  a native open disk around each point, is `exists_disk_iterUniformEquicontinuousOn` under
  (i), and the counterexample refutes even the pointwise form.
* `IsNativeOpen`, `IterEquicontinuousOn` and `affineJulia` are `epd:def:affine-julia`, and
  `affineJulia_eq_empty` is `epd:cor:empty-affine`. Beyond the source,
  `iterEquicontinuousAt_of_notMem_affineJulia` shows that points outside `J_aff,v(f)` are points
  of equicontinuity, so `affineJulia_eq_empty_iff` makes the corollary an equivalence when `v`
  attains every value.

Hahn part: `k` is any commutative domain (the source takes `ℝ` or `ℂ`) and `K = k⟦Γ⟧` with
`v = orderTop` (Mathlib's `HahnSeries.addVal`). `budget_hahn` is `epd:prop:budget`,
`general_hahn` is the three-way equivalence of `epd:thm:general`,
`uniformEquicontinuousOn_hahn` its closing sentence, `affineJulia_hahn_eq_empty` is
`epd:cor:empty-affine` and `affineJulia_hahn_eq_empty_iff` its converse. `exists_addVal_eq`
(`v(t^γ) = γ`) supplies the surjectivity used by the converses.

Generality: the budget assumes `f.natDegree ≤ d` and `0 ≤ A` instead of the source's
`deg f = d ≥ 1` and `A > 0`, so constant and zero polynomials are included; the coefficient
hypothesis is the source's, on nonzero coefficients only. `Γ ≠ 0` and divisibility are not
used. No clause of `epd:prop:budget`, `epd:thm:general` or `epd:cor:empty-affine` is pending.
-/

namespace Surreal.NativeEquicontinuity

open Polynomial Surreal.ScaleIdeal

section Group

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- Every value of `WithTop Γ` is at least `-A` for some `A ≥ 0`. -/
theorem exists_neg_le (w : WithTop Γ) : ∃ A : Γ, 0 ≤ A ∧ ((-A : Γ) : WithTop Γ) ≤ w := by
  induction w with
  | top => exact ⟨0, le_rfl, le_top⟩
  | coe g => exact ⟨|g|, abs_nonneg g, WithTop.coe_le_coe.mpr (neg_abs_le g)⟩

/-- For `A ≥ 0`, `A ≤ (d + 1)ⁿ A`. -/
theorem le_pow_nsmul {A : Γ} (hA : 0 ≤ A) (d n : ℕ) : A ≤ (d + 1) ^ n • A := by
  simpa using nsmul_le_nsmul_left hA (Nat.one_le_pow' n d)

omit [IsOrderedAddMonoid Γ] in
/-- If `Γ` has no order unit, the multiples of any `A ≥ 0` are bounded above. -/
theorem exists_nsmul_le (h : ¬ ∃ u : Γ, IsOrderUnit u) {A : Γ} (hA : 0 ≤ A) :
    ∃ η : Γ, ∀ r : ℕ, r • A ≤ η := by
  rcases hA.eq_or_lt with rfl | hA
  · exact ⟨0, fun r => (nsmul_zero r).le⟩
  · obtain ⟨η, hη⟩ := (not_isOrderUnit_iff hA).mp fun hu => h ⟨A, hu⟩
    exact ⟨η, fun r => (hη r).le⟩

end Group

section Generic

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
variable {K : Type*} [CommRing K] (v : AddValuation K (WithTop Γ))

/-- `v(zⁱ) ≥ -i M` whenever `v(z) ≥ -M`. -/
theorem neg_nsmul_le_map_pow {M : Γ} {z : K} (hz : ((-M : Γ) : WithTop Γ) ≤ v z) (i : ℕ) :
    ((-(i • M) : Γ) : WithTop Γ) ≤ v (z ^ i) := by
  rw [AddValuation.map_pow, ← neg_nsmul, WithTop.coe_nsmul]
  exact nsmul_le_nsmul_right hz i

/-- The source's bound on the nonzero coefficients bounds every coefficient, since
`v(0) = ⊤`. -/
theorem coeff_bound {f : K[X]} {A : Γ}
    (hf : ∀ j, f.coeff j ≠ 0 → ((-A : Γ) : WithTop Γ) ≤ v (f.coeff j)) (j : ℕ) :
    ((-A : Γ) : WithTop Γ) ≤ v (f.coeff j) := by
  by_cases h : f.coeff j = 0
  · rw [h, AddValuation.map_zero]
    exact le_top
  · exact hf j h

/-- One step of `epd:eq:orbitbudget`: if `v(aⱼ) ≥ -A`, `A ≤ M` and `v(z) ≥ -M`, then
`v(f(z)) ≥ -(d + 1) M`. -/
theorem orbit_step {f : K[X]} {d : ℕ} (hd : f.natDegree ≤ d) {A M : Γ} (hAM : A ≤ M)
    (hM : 0 ≤ M) (hf : ∀ j, ((-A : Γ) : WithTop Γ) ≤ v (f.coeff j)) {z : K}
    (hz : ((-M : Γ) : WithTop Γ) ≤ v z) :
    ((-((d + 1) • M) : Γ) : WithTop Γ) ≤ v (f.eval z) := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hd)]
  refine AddValuation.map_le_sum v fun j hj => ?_
  have hj' : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [AddValuation.map_mul]
  refine le_trans ?_ (add_le_add (hf j) (neg_nsmul_le_map_pow v hz j))
  rw [← WithTop.coe_add, WithTop.coe_le_coe, succ_nsmul, neg_add, add_comm]
  exact add_le_add (neg_le_neg hAM) (neg_le_neg (nsmul_le_nsmul_left hM hj'))

/-- One step of `epd:eq:differencebudget`: under the hypotheses of `orbit_step` for `z` and
`w`, the divided difference of `f` has valuation at least `-d M`, so
`v(z - w) ≤ v(f(z) - f(w)) + d M`. -/
theorem difference_step {f : K[X]} {d : ℕ} (hd : f.natDegree ≤ d) {A M : Γ} (hAM : A ≤ M)
    (hM : 0 ≤ M) (hf : ∀ j, ((-A : Γ) : WithTop Γ) ≤ v (f.coeff j)) {z w : K}
    (hz : ((-M : Γ) : WithTop Γ) ≤ v z) (hw : ((-M : Γ) : WithTop Γ) ≤ v w) :
    v (z - w) ≤ v (f.eval z - f.eval w) + ((d • M : Γ) : WithTop Γ) := by
  set S : K := ∑ j ∈ Finset.range (d + 1),
    f.coeff j * ∑ i ∈ Finset.range j, z ^ i * w ^ (j - 1 - i) with hS_def
  have key : f.eval z - f.eval w = S * (z - w) := by
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hd) z, eval_eq_sum_range' (Nat.lt_succ_of_le hd) w,
      ← Finset.sum_sub_distrib, hS_def, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, geom_sum₂_mul, mul_sub]
  have hS : ((-(d • M) : Γ) : WithTop Γ) ≤ v S := by
    refine AddValuation.map_le_sum v fun j hj => ?_
    have hj' : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [AddValuation.map_mul]
    rcases j with _ | j
    · simp
    · refine le_trans ?_ (add_le_add (hf (j + 1)) (AddValuation.map_le_sum v
        (g := ((-(j • M) : Γ) : WithTop Γ)) fun i hi => ?_))
      · rw [← WithTop.coe_add, WithTop.coe_le_coe, ← neg_add, neg_le_neg_iff]
        calc A + j • M ≤ M + j • M := add_le_add hAM le_rfl
          _ = (j + 1) • M := by rw [succ_nsmul, add_comm]
          _ ≤ d • M := nsmul_le_nsmul_left hM hj'
      · have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [AddValuation.map_mul, Nat.add_sub_cancel]
        refine le_trans ?_
          (add_le_add (neg_nsmul_le_map_pow v hz i) (neg_nsmul_le_map_pow v hw (j - i)))
        rw [← WithTop.coe_add, ← neg_add, ← add_nsmul, Nat.add_sub_of_le hi']
  rw [key, AddValuation.map_mul]
  calc v (z - w) = ((-(d • M) : Γ) : WithTop Γ) + v (z - w) + ((d • M : Γ) : WithTop Γ) := by
        rw [add_right_comm, ← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero, zero_add]
    _ ≤ v S + v (z - w) + ((d • M : Γ) : WithTop Γ) := by gcongr

/-- `epd:eq:orbitbudget`: if `deg f ≤ d`, `0 ≤ A`, every nonzero coefficient has
`v(aⱼ) ≥ -A` and `v(x) ≥ -A`, then `v(fⁿ(x)) ≥ -(d + 1)ⁿ A` for every `n`. -/
theorem orbit_budget {f : K[X]} {d : ℕ} (hd : f.natDegree ≤ d) {A : Γ} (hA : 0 ≤ A)
    (hf : ∀ j, f.coeff j ≠ 0 → ((-A : Γ) : WithTop Γ) ≤ v (f.coeff j)) {x : K}
    (hx : ((-A : Γ) : WithTop Γ) ≤ v x) (n : ℕ) :
    ((-((d + 1) ^ n • A) : Γ) : WithTop Γ) ≤ v ((fun z => f.eval z)^[n] x) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ', mul_nsmul']
    exact orbit_step v hd (le_pow_nsmul hA d n) (nsmul_nonneg hA _) (coeff_bound v hf) ih

/-- `epd:eq:differencebudget`: under the hypotheses of `orbit_budget` for `x` and `y`,
`v(fⁿ(x) - fⁿ(y)) ≥ v(x - y) - ((d + 1)ⁿ - 1) A`, stated additively in `WithTop Γ`. -/
theorem difference_budget {f : K[X]} {d : ℕ} (hd : f.natDegree ≤ d) {A : Γ} (hA : 0 ≤ A)
    (hf : ∀ j, f.coeff j ≠ 0 → ((-A : Γ) : WithTop Γ) ≤ v (f.coeff j)) {x y : K}
    (hx : ((-A : Γ) : WithTop Γ) ≤ v x) (hy : ((-A : Γ) : WithTop Γ) ≤ v y) (n : ℕ) :
    v (x - y) ≤ v ((fun z => f.eval z)^[n] x - (fun z => f.eval z)^[n] y) +
      ((((d + 1) ^ n - 1) • A : Γ) : WithTop Γ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have step := difference_step v hd (le_pow_nsmul hA d n) (nsmul_nonneg hA _)
      (coeff_bound v hf) (orbit_budget v hd hA hf hx n) (orbit_budget v hd hA hf hy n)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have harith : (d + 1) ^ (n + 1) - 1 = d * (d + 1) ^ n + ((d + 1) ^ n - 1) := by
      have hP := Nat.one_le_pow' n d
      rw [pow_succ', add_mul, one_mul]
      generalize (d + 1) ^ n = P at hP ⊢
      generalize d * P = Q
      omega
    refine ih.trans ((add_le_add step le_rfl).trans_eq ?_)
    rw [add_assoc, ← WithTop.coe_add, harith, add_nsmul, mul_nsmul']

/-- `epd:prop:budget`: both budgets, for `x, y ∈ D_A` and every `n`. The source's hypotheses
`deg f = d ≥ 1` and `A > 0` are weakened to `deg f ≤ d` and `A ≥ 0`. -/
theorem budget {f : K[X]} {d : ℕ} (hd : f.natDegree ≤ d) {A : Γ} (hA : 0 ≤ A)
    (hf : ∀ j, f.coeff j ≠ 0 → ((-A : Γ) : WithTop Γ) ≤ v (f.coeff j)) {x y : K}
    (hx : ((-A : Γ) : WithTop Γ) ≤ v x) (hy : ((-A : Γ) : WithTop Γ) ≤ v y) (n : ℕ) :
    ((-((d + 1) ^ n • A) : Γ) : WithTop Γ) ≤ v ((fun z => f.eval z)^[n] x) ∧
      v (x - y) ≤ v ((fun z => f.eval z)^[n] x - (fun z => f.eval z)^[n] y) +
        ((((d + 1) ^ n - 1) • A : Γ) : WithTop Γ) :=
  ⟨orbit_budget v hd hA hf hx n, difference_budget v hd hA hf hx hy n⟩

/-- `epd:thm:general` (ii): the orbit of `x` under `f` is valuation-bounded. -/
def OrbitBounded (f : K[X]) (x : K) : Prop :=
  ∃ β : Γ, ∀ n : ℕ, (β : WithTop Γ) ≤ v ((fun z => f.eval z)^[n] x)

/-- `epd:thm:general` (iii), pointwise form: the iterates of `f` are equicontinuous at `x` for
the native uniformity: every output threshold `γ` is met on some input ball
`{y : v(y - x) > δ}`. The source's local form (equicontinuity on a native open neighbourhood of
`x`) is `exists_disk_iterUniformEquicontinuousOn`. -/
def IterEquicontinuousAt (f : K[X]) (x : K) : Prop :=
  ∀ γ : Γ, ∃ δ : Γ, ∀ y : K, (δ : WithTop Γ) < v (y - x) →
    ∀ n : ℕ, (γ : WithTop Γ) < v ((fun z => f.eval z)^[n] y - (fun z => f.eval z)^[n] x)

/-- `epd:thm:general`: the iterates of `f` are uniformly equicontinuous on `S` for the native
uniformity. -/
def IterUniformEquicontinuousOn (f : K[X]) (S : Set K) : Prop :=
  ∀ γ : Γ, ∃ δ : Γ, ∀ x ∈ S, ∀ y ∈ S, (δ : WithTop Γ) < v (x - y) →
    ∀ n : ℕ, (γ : WithTop Γ) < v ((fun z => f.eval z)^[n] x - (fun z => f.eval z)^[n] y)

/-- `epd:prop:budget`: the disk `D_A = {z : v(z) ≥ -A}`. -/
def disk (A : Γ) : Set K :=
  {z | ((-A : Γ) : WithTop Γ) ≤ v z}

/-- `D_A` contains the ball `{y : v(y - x) ≥ -A}` around each of its points; hence it is native
open (`isNativeOpen_disk`). -/
theorem mem_disk_of_le {A : Γ} {x y : K} (hx : x ∈ disk v A)
    (hy : ((-A : Γ) : WithTop Γ) ≤ v (y - x)) : y ∈ disk v A := by
  have h := AddValuation.map_le_add v hy hx
  rwa [sub_add_cancel] at h

/-- For every polynomial and point there is an `A ≥ 0` bounding the nonzero coefficients and
the point, as required by `epd:prop:budget`. -/
theorem exists_budget_radius (f : K[X]) (x : K) :
    ∃ A : Γ, 0 ≤ A ∧ (∀ j, f.coeff j ≠ 0 → ((-A : Γ) : WithTop Γ) ≤ v (f.coeff j)) ∧
      ((-A : Γ) : WithTop Γ) ≤ v x := by
  classical
  have hfin : ∀ s : Finset K, ∃ A : Γ, 0 ≤ A ∧ ∀ a ∈ s, ((-A : Γ) : WithTop Γ) ≤ v a := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, le_rfl, by simp⟩
    | insert a s _ ih =>
      obtain ⟨A₁, h₁, ha⟩ := exists_neg_le (v a)
      obtain ⟨A₂, -, hs⟩ := ih
      refine ⟨max A₁ A₂, h₁.trans (le_max_left _ _), fun b hb => ?_⟩
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact (WithTop.coe_le_coe.mpr (neg_le_neg (le_max_left _ _))).trans ha
      · exact (WithTop.coe_le_coe.mpr (neg_le_neg (le_max_right _ _))).trans (hs b hb)
  obtain ⟨A, hA, hs⟩ := hfin (insert x ((Finset.range (f.natDegree + 1)).image f.coeff))
  refine ⟨A, hA, fun j hj => hs _ ?_, hs _ (Finset.mem_insert_self _ _)⟩
  exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
    (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_natDegree_of_ne_zero hj))))

/-- `epd:thm:general`, closing sentence: if `Γ` has no order unit, the iterates of `f` are
uniformly equicontinuous on every disk `D_A` for which the coefficient bounds of
`epd:prop:budget` hold. -/
theorem uniformEquicontinuousOn_disk (h : ¬ ∃ u : Γ, IsOrderUnit u) {f : K[X]} {A : Γ}
    (hA : 0 ≤ A) (hf : ∀ j, f.coeff j ≠ 0 → ((-A : Γ) : WithTop Γ) ≤ v (f.coeff j)) :
    IterUniformEquicontinuousOn v f (disk v A) := by
  obtain ⟨η, hη⟩ := exists_nsmul_le h hA
  refine fun γ => ⟨γ + η, fun x hx y hy hxy n => ?_⟩
  have hb := difference_budget v le_rfl hA hf hx hy n
  have h1 : (γ : WithTop Γ) + (η : WithTop Γ) <
      v ((fun z => f.eval z)^[n] x - (fun z => f.eval z)^[n] y) + (η : WithTop Γ) := by
    rw [← WithTop.coe_add]
    exact hxy.trans_le (hb.trans (add_le_add le_rfl (WithTop.coe_le_coe.mpr (hη _))))
  exact lt_of_add_lt_add_right h1

/-- `epd:thm:general`, (i) ⇒ (ii): without an order unit every orbit of every polynomial is
valuation-bounded. -/
theorem orbitBounded (h : ¬ ∃ u : Γ, IsOrderUnit u) (f : K[X]) (x : K) :
    OrbitBounded v f x := by
  obtain ⟨A, hA, hf, hx⟩ := exists_budget_radius v f x
  obtain ⟨η, hη⟩ := exists_nsmul_le h hA
  exact ⟨-η, fun n => (WithTop.coe_le_coe.mpr (neg_le_neg (hη _))).trans
    (orbit_budget v le_rfl hA hf hx n)⟩

/-- `epd:thm:general`, (i) ⇒ (iii): without an order unit the iterates of every polynomial are
equicontinuous at every point. -/
theorem iterEquicontinuousAt (h : ¬ ∃ u : Γ, IsOrderUnit u) (f : K[X]) (x : K) :
    IterEquicontinuousAt v f x := by
  obtain ⟨A, hA, hf, hx⟩ := exists_budget_radius v f x
  intro γ
  obtain ⟨δ, hδ⟩ := uniformEquicontinuousOn_disk v h hA hf γ
  refine ⟨max δ 0, fun y hy n => hδ y ?_ x hx
    ((WithTop.coe_le_coe.mpr (le_max_left δ 0)).trans_lt hy) n⟩
  exact mem_disk_of_le v hx
    ((WithTop.coe_le_coe.mpr ((neg_nonpos.mpr hA).trans (le_max_right δ 0))).trans hy.le)

/-- The iterates of `z ↦ t z` are `z ↦ tⁿ z`. -/
theorem iterate_eval_C_mul_X (t y : K) (n : ℕ) :
    (fun z => (C t * X).eval z)^[n] y = t ^ n * y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, eval_mul, eval_C, eval_X, pow_succ', mul_assoc]

/-- `epd:thm:general`, not (i) ⇒ not (ii): if `u` is an order unit and `v(t) = -u`, the orbit
of `1` under `z ↦ t z` is not valuation-bounded. -/
theorem not_orbitBounded_of_isOrderUnit {u : Γ} (hu : IsOrderUnit u) {t : K}
    (ht : v t = ((-u : Γ) : WithTop Γ)) : ¬ OrbitBounded v (C t * X) 1 := by
  rintro ⟨β, hβ⟩
  obtain ⟨m, hm⟩ := hu.2 (-β)
  have h := hβ (m + 1)
  rw [iterate_eval_C_mul_X, mul_one, AddValuation.map_pow, ht, ← WithTop.coe_nsmul,
    WithTop.coe_le_coe, neg_nsmul, le_neg] at h
  have hlt : m • u < (m + 1) • u := by
    rw [succ_nsmul]
    exact lt_add_of_pos_right _ hu.1
  exact absurd (h.trans hm) (not_le.mpr hlt)

/-- `epd:thm:general`, not (i) ⇒ not (iii): if `u` is an order unit, `v(t) = -u` and `v`
attains every value, the iterates of `z ↦ t z` are not equicontinuous at `0`; even the output
threshold `0` fails. -/
theorem not_iterEquicontinuousAt_of_isOrderUnit {u : Γ} (hu : IsOrderUnit u) {t : K}
    (ht : v t = ((-u : Γ) : WithTop Γ)) (hv : ∀ γ : Γ, ∃ h : K, v h = γ) :
    ¬ IterEquicontinuousAt v (C t * X) 0 := by
  intro heq
  obtain ⟨δ, hδ⟩ := heq 0
  obtain ⟨N, hN⟩ := hu.2 δ
  obtain ⟨h, hh⟩ := hv ((N + 1) • u)
  have hlt : δ < (N + 1) • u := hN.trans_lt (by
    rw [succ_nsmul]
    exact lt_add_of_pos_right _ hu.1)
  have key := hδ h (by rw [sub_zero, hh]; exact WithTop.coe_lt_coe.mpr hlt) (N + 1)
  rw [iterate_eval_C_mul_X, iterate_eval_C_mul_X, mul_zero, sub_zero, AddValuation.map_mul,
    AddValuation.map_pow, ht, hh, ← WithTop.coe_nsmul, ← WithTop.coe_add, neg_nsmul,
    neg_add_cancel] at key
  exact lt_irrefl _ key

/-- `epd:thm:general`: for an additive valuation attaining every value of `Γ`, the following
are equivalent: (i) `Γ` has no order unit; (ii) every orbit of every polynomial is
valuation-bounded; (iii) the iterates of every polynomial are equicontinuous at every point
in the native uniformity. The implications from (i) do not use the surjectivity hypothesis.
Clause (iii) is stated pointwise; under (i) the stronger local form, uniform equicontinuity on
a native open disk around each point, is `exists_disk_iterUniformEquicontinuousOn`, and the
counterexample for the converse refutes even the pointwise form. -/
theorem tfae_general (hv : ∀ γ : Γ, ∃ t : K, v t = γ) :
    List.TFAE [¬ ∃ u : Γ, IsOrderUnit u, ∀ (f : K[X]) (x : K), OrbitBounded v f x,
      ∀ (f : K[X]) (x : K), IterEquicontinuousAt v f x] := by
  tfae_have 1 → 2 := fun h => orbitBounded v h
  tfae_have 1 → 3 := fun h => iterEquicontinuousAt v h
  tfae_have 2 → 1 := by
    rintro h ⟨u, hu⟩
    obtain ⟨t, ht⟩ := hv (-u)
    exact not_orbitBounded_of_isOrderUnit v hu ht (h _ _)
  tfae_have 3 → 1 := by
    rintro h ⟨u, hu⟩
    obtain ⟨t, ht⟩ := hv (-u)
    exact not_iterEquicontinuousAt_of_isOrderUnit v hu ht hv (h _ _)
  tfae_finish

/-- `epd:def:affine-julia`: `U` is open in the native valuation topology. -/
def IsNativeOpen (U : Set K) : Prop :=
  ∀ x ∈ U, ∃ ρ : Γ, ∀ y : K, (ρ : WithTop Γ) < v (y - x) → y ∈ U

/-- Every disk `D_A` is native open: it contains the ball `{y : v(y - x) > -A}` around each of
its points, as in the proof of `epd:thm:general`. -/
theorem isNativeOpen_disk (A : Γ) : IsNativeOpen v (disk v A) :=
  fun _ hx => ⟨-A, fun _ hy => mem_disk_of_le v hx hy.le⟩

/-- `epd:thm:general`, (i) ⇒ (iii) in the source's local form: without an order unit, every
point `x` lies in a native open disk `D_A` on which the iterates of `f` are uniformly
equicontinuous. -/
theorem exists_disk_iterUniformEquicontinuousOn (h : ¬ ∃ u : Γ, IsOrderUnit u) (f : K[X])
    (x : K) :
    ∃ A : Γ, x ∈ disk v A ∧ IsNativeOpen v (disk v A) ∧
      IterUniformEquicontinuousOn v f (disk v A) := by
  obtain ⟨A, hA, hf, hx⟩ := exists_budget_radius v f x
  exact ⟨A, hx, isNativeOpen_disk v A, uniformEquicontinuousOn_disk v h hA hf⟩

/-- `epd:def:affine-julia`: the iterates of `f`, restricted to `U`, are equicontinuous at every
point of `U`, as maps to the additive valued field. -/
def IterEquicontinuousOn (f : K[X]) (U : Set K) : Prop :=
  ∀ x ∈ U, ∀ γ : Γ, ∃ δ : Γ, ∀ y ∈ U, (δ : WithTop Γ) < v (y - x) →
    ∀ n : ℕ, (γ : WithTop Γ) < v ((fun z => f.eval z)^[n] y - (fun z => f.eval z)^[n] x)

/-- `epd:def:affine-julia`: `J_aff,v(f)`, the points having no native open neighbourhood on
which all iterates of `f` are equicontinuous. -/
def affineJulia (f : K[X]) : Set K :=
  {x | ¬ ∃ U : Set K, x ∈ U ∧ IsNativeOpen v U ∧ IterEquicontinuousOn v f U}

/-- `epd:cor:empty-affine`: if `Γ` has no order unit, `J_aff,v(f) = ∅` for every polynomial. -/
theorem affineJulia_eq_empty (h : ¬ ∃ u : Γ, IsOrderUnit u) (f : K[X]) :
    affineJulia v f = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => hx ⟨Set.univ, Set.mem_univ x,
    fun _ _ => ⟨0, fun _ _ => Set.mem_univ _⟩, fun z _ γ => ?_⟩
  obtain ⟨δ, hδ⟩ := iterEquicontinuousAt v h f z γ
  exact ⟨δ, fun y _ => hδ y⟩

/-- A point outside `J_aff,v(f)` is a point of equicontinuity of the iterates, because the
neighbourhood in `epd:def:affine-julia` is open. -/
theorem iterEquicontinuousAt_of_notMem_affineJulia {f : K[X]} {x : K}
    (hx : x ∉ affineJulia v f) : IterEquicontinuousAt v f x := by
  simp only [affineJulia, Set.mem_setOf_eq, not_not] at hx
  obtain ⟨U, hxU, hU, heq⟩ := hx
  intro γ
  obtain ⟨ρ, hρ⟩ := hU x hxU
  obtain ⟨δ, hδ⟩ := heq x hxU γ
  exact ⟨max δ ρ, fun y hy =>
    hδ y (hρ y ((WithTop.coe_le_coe.mpr (le_max_right δ ρ)).trans_lt hy))
      ((WithTop.coe_le_coe.mpr (le_max_left δ ρ)).trans_lt hy)⟩

/-- `epd:cor:empty-affine` is an equivalence when `v` attains every value of `Γ`:
`J_aff,v(f) = ∅` for every polynomial exactly when `Γ` has no order unit. -/
theorem affineJulia_eq_empty_iff (hv : ∀ γ : Γ, ∃ t : K, v t = γ) :
    (∀ f : K[X], affineJulia v f = ∅) ↔ ¬ ∃ u : Γ, IsOrderUnit u := by
  refine ⟨fun h => ?_, fun h f => affineJulia_eq_empty v h f⟩
  rintro ⟨u, hu⟩
  obtain ⟨t, ht⟩ := hv (-u)
  refine not_iterEquicontinuousAt_of_isOrderUnit v hu ht hv
    (iterEquicontinuousAt_of_notMem_affineJulia v ?_)
  rw [h]
  exact Set.notMem_empty 0

end Generic

section Hahn

open _root_.HahnSeries

variable {Γ k : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [CommRing k] [IsDomain k]

/-- The Hahn valuation attains every value: `v(t^γ) = γ`. -/
theorem exists_addVal_eq (γ : Γ) : ∃ t : k⟦Γ⟧, addVal Γ k t = γ :=
  ⟨single γ 1, by rw [addVal_apply, orderTop_single one_ne_zero]⟩

/-- `epd:prop:budget` in `K = k⟦Γ⟧` with `v = orderTop`: for `deg f ≤ d`, `A ≥ 0` bounding the
nonzero coefficients, `x, y ∈ D_A` and every `n`, `v(fⁿ(x)) ≥ -(d + 1)ⁿ A` and
`v(fⁿ(x) - fⁿ(y)) ≥ v(x - y) - ((d + 1)ⁿ - 1) A`. -/
theorem budget_hahn {f : (k⟦Γ⟧)[X]} {d : ℕ} (hd : f.natDegree ≤ d) {A : Γ} (hA : 0 ≤ A)
    (hf : ∀ j, f.coeff j ≠ 0 → ((-A : Γ) : WithTop Γ) ≤ (f.coeff j).orderTop) {x y : k⟦Γ⟧}
    (hx : ((-A : Γ) : WithTop Γ) ≤ x.orderTop) (hy : ((-A : Γ) : WithTop Γ) ≤ y.orderTop)
    (n : ℕ) :
    ((-((d + 1) ^ n • A) : Γ) : WithTop Γ) ≤ ((fun z => f.eval z)^[n] x).orderTop ∧
      (x - y).orderTop ≤ ((fun z => f.eval z)^[n] x - (fun z => f.eval z)^[n] y).orderTop +
        ((((d + 1) ^ n - 1) • A : Γ) : WithTop Γ) := by
  have h := budget (addVal Γ k) hd hA (f := f) (x := x) (y := y)
    (by simpa only [addVal_apply] using hf) (by simpa only [addVal_apply] using hx)
    (by simpa only [addVal_apply] using hy) n
  simpa only [addVal_apply] using h

/-- `epd:thm:general` in `K = k⟦Γ⟧` with `v = orderTop`: (i) `Γ` has no order unit, (ii) every
orbit of every polynomial is valuation-bounded, and (iii) the iterates of every polynomial are
equicontinuous at every point of `K` in the native uniformity, are equivalent. Clause (iii) is
the pointwise form; the source's local form follows under (i) from
`exists_disk_iterUniformEquicontinuousOn` at `v = addVal Γ k`. -/
theorem general_hahn :
    List.TFAE [¬ ∃ u : Γ, IsOrderUnit u,
      ∀ (f : (k⟦Γ⟧)[X]) (x : k⟦Γ⟧), ∃ β : Γ, ∀ n : ℕ,
        (β : WithTop Γ) ≤ ((fun z => f.eval z)^[n] x).orderTop,
      ∀ (f : (k⟦Γ⟧)[X]) (x : k⟦Γ⟧) (γ : Γ), ∃ δ : Γ, ∀ y : k⟦Γ⟧,
        (δ : WithTop Γ) < (y - x).orderTop → ∀ n : ℕ,
          (γ : WithTop Γ) < ((fun z => f.eval z)^[n] y - (fun z => f.eval z)^[n] x).orderTop] := by
  simpa only [OrbitBounded, IterEquicontinuousAt, addVal_apply] using
    tfae_general (addVal Γ k) exists_addVal_eq

/-- `epd:thm:general`, closing sentence, in `K = k⟦Γ⟧`: without an order unit, the iterates of
`f` are uniformly equicontinuous on every `D_A` for which the coefficient bounds hold. -/
theorem uniformEquicontinuousOn_hahn (h : ¬ ∃ u : Γ, IsOrderUnit u) {f : (k⟦Γ⟧)[X]} {A : Γ}
    (hA : 0 ≤ A) (hf : ∀ j, f.coeff j ≠ 0 → ((-A : Γ) : WithTop Γ) ≤ (f.coeff j).orderTop)
    (γ : Γ) : ∃ δ : Γ, ∀ x y : k⟦Γ⟧, ((-A : Γ) : WithTop Γ) ≤ x.orderTop →
      ((-A : Γ) : WithTop Γ) ≤ y.orderTop → (δ : WithTop Γ) < (x - y).orderTop →
        ∀ n : ℕ,
          (γ : WithTop Γ) < ((fun z => f.eval z)^[n] x - (fun z => f.eval z)^[n] y).orderTop := by
  obtain ⟨δ, hδ⟩ := uniformEquicontinuousOn_disk (addVal Γ k) h hA
    (by simpa only [addVal_apply] using hf) γ
  refine ⟨δ, fun x y hx hy hxy n => ?_⟩
  have := hδ x (by simpa only [disk, Set.mem_setOf_eq, addVal_apply] using hx) y
    (by simpa only [disk, Set.mem_setOf_eq, addVal_apply] using hy)
    (by simpa only [addVal_apply] using hxy) n
  simpa only [addVal_apply] using this

/-- `epd:cor:empty-affine` in `K = k⟦Γ⟧`: without an order unit, `J_aff,v(f) = ∅`. -/
theorem affineJulia_hahn_eq_empty (h : ¬ ∃ u : Γ, IsOrderUnit u) (f : (k⟦Γ⟧)[X]) :
    affineJulia (addVal Γ k) f = ∅ :=
  affineJulia_eq_empty (addVal Γ k) h f

/-- In `K = k⟦Γ⟧`, `J_aff,v(f) = ∅` for every polynomial exactly when `Γ` has no order unit. -/
theorem affineJulia_hahn_eq_empty_iff :
    (∀ f : (k⟦Γ⟧)[X], affineJulia (addVal Γ k) f = ∅) ↔ ¬ ∃ u : Γ, IsOrderUnit u :=
  affineJulia_eq_empty_iff (addVal Γ k) exists_addVal_eq

end Hahn

end Surreal.NativeEquicontinuity
