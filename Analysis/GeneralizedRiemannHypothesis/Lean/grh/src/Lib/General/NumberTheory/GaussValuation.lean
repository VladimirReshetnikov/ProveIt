import Lib.General.NumberTheory.PadicLimitsValuation

/-!
# The Gauss valuation of a polynomial over the ring of integers of ℚ̄_ℓ

The function `New.ellVal` agrees with the valuation `v` only on integral elements of `ℚ̄_ℓ`, so
almost everything is stated over their ring `ℤ̄_ℓ`. The first sections collect the rules of `v`
there and show that monic polynomials split, that every nonnegative rational number is the valuation
of some element, and that the residue field is algebraically closed. For a rational number `ρ ≥ 0`,
called the radius, and `g = ∑ y_i Y ^ i` put `v_ρ(g) = min_i (v(y_i) + ρ i)`.

* `New.Selmer.gaussVal`, `New.Selmer.gaussVal_le_eval`: `v(g(y)) ≥ v_ρ(g)` if `v(y) ≥ ρ`.
* `New.Selmer.exists_forall_ellVal_eval_eq_gaussVal`: for finitely many polynomials equality holds
  at one such point.
* `New.Selmer.gaussVal_mul`, `New.Selmer.gaussVal_eq_add_sum_roots`: `v_ρ` is additive on products,
  and it is given by `v₀(g)` and the valuations of the integral roots.
* `New.Selmer.exists_one_add_pow_eq`: a solution of `(1 + x') ^ j = 1 + x` of large valuation.
* `New.Selmer.le_ellVal_geom_sum`, `New.Selmer.ellVal_pow_sub_one_le`: bounds for the valuations of
  geometric sums of elements near `1` and of `ζ ^ j - 1` for roots of unity `ζ` of `ℓ`-power order.

Notions from other files:
* `New.ellVal`: the valuation `v` on `ℚ̄_ℓ` with `v ℓ = 1`, cut off below at `0`; `New.intQpBar ℓ`
  is the ring `ℤ̄_ℓ` of integral elements, and `x.1` is `x` as an element of `ℚ̄_ℓ`.
* `New.ThePrime ℓ`: `ℓ` is prime.

## Relation to the literature

Known result: Gauss norms and Gauss's lemma for polynomials over the integral elements of ℚ̄_ℓ.
Source: Bosch, Güntzer, Remmert, Non-Archimedean Analysis.
-/

noncomputable section

namespace New.Selmer

open Polynomial Finset IsLocalRing

open scoped NNReal ENNReal NNRat

variable {ℓ : ℕ} [ThePrime ℓ] {ι : Type*} {ρ ρ' : ℚ≥0}

/-! ### The valuation on integral elements -/

lemma norm_coe_le_one (x : intQpBar ℓ) : ‖x.1‖ ≤ 1 := x.2

lemma ellVal_eq_top_iff {x : PadicAlgCl ℓ} : ellVal x = ⊤ ↔ x = 0 := by
  simp [ellVal]

lemma ellVal_zero : ellVal (0 : PadicAlgCl ℓ) = ⊤ := ellVal_eq_top_iff.2 rfl

lemma ellVal_congr_norm {x y : PadicAlgCl ℓ} (h_norm : ‖x‖ = ‖y‖) : ellVal x = ellVal y :=
  le_antisymm (ellVal_le_ellVal h_norm.ge) (ellVal_le_ellVal h_norm.le)

/-- The valuation `v = ellVal` is additive on products of elements of `ℤ̄_ℓ = intQpBar ℓ`. (Outside
this ring it is cut off at `0` and is not additive.) -/
lemma ellVal_val_mul (x y : intQpBar ℓ) : ellVal (x * y).1 = ellVal x.1 + ellVal y.1 := by
  obtain rfl | hx := eq_or_ne x 0
  · simp [ellVal_zero]
  obtain rfl | hy := eq_or_ne y 0
  · simp [ellVal_zero]
  have h_nonneg (z : intQpBar ℓ) : 0 ≤ -Real.logb ℓ ‖z.1‖ := neg_nonneg.2 <| Real.logb_nonpos
    (mod_cast (Fact.out : ℓ.Prime).one_lt) (norm_nonneg z.1) (norm_coe_le_one z)
  simp [ellVal, hx, hy, Real.logb_mul, add_comm, ENNReal.ofReal_add (h_nonneg x) (h_nonneg y)]

/-- The ultrametric inequality for `v = ellVal` on the integral elements `ℤ̄_ℓ = intQpBar ℓ`:
`min(v(x), v(y)) ≤ v(x + y)`. -/
lemma min_ellVal_le_ellVal_add (x y : intQpBar ℓ) :
    min (ellVal x.1) (ellVal y.1) ≤ ellVal (x + y).1 := by
  obtain h | h := le_total (ellVal x.1) (ellVal y.1)
  · have h_dvd : x ∣ x + y := dvd_add dvd_rfl (dvd_iff_ellVal_le.2 h)
    exact min_le_of_left_le (dvd_iff_ellVal_le.1 h_dvd)
  · have h_dvd : y ∣ x + y := dvd_add (dvd_iff_ellVal_le.2 h) dvd_rfl
    exact min_le_of_right_le (dvd_iff_ellVal_le.1 h_dvd)

/-- The valuation `v = ellVal`, with `v(ℓ) = 1`, as an additive valuation on `ℤ̄_ℓ = intQpBar ℓ`,
the ring of integral elements of `ℚ̄_ℓ`. -/
def ellAddVal : AddValuation (intQpBar ℓ) ℝ≥0∞ :=
  .of (fun x : intQpBar ℓ ↦ ellVal x.1) ellVal_zero (by simp [ellVal]) min_ellVal_le_ellVal_add
    ellVal_val_mul

lemma ellAddVal_apply (x : intQpBar ℓ) : ellAddVal x = ellVal x.1 := rfl

lemma ellVal_neg (x : intQpBar ℓ) : ellVal (-x).1 = ellVal x.1 := ellVal_congr_norm (norm_neg x.1)

lemma min_ellVal_le_ellVal_sub (x y : intQpBar ℓ) :
    min (ellVal x.1) (ellVal y.1) ≤ ellVal (x - y).1 := by
  simpa only [ellAddVal_apply] using ellAddVal.map_sub x y

/-- If two integral elements `x`, `y` of `ℚ̄_ℓ` have different valuations, then `v(x + y)` is the
smaller of these. -/
lemma ellVal_add_eq_min_of_ne {x y : intQpBar ℓ} (h_ne : ellVal x.1 ≠ ellVal y.1) :
    ellVal (x + y).1 = min (ellVal x.1) (ellVal y.1) := by
  simpa only [ellAddVal_apply] using ellAddVal.map_add_of_distinct_val h_ne

/-- If two integral elements `x`, `y` of `ℚ̄_ℓ` have different valuations, then `v(x - y)` is the
smaller of these. -/
lemma ellVal_sub_eq_min_of_ne {x y : intQpBar ℓ} (h_ne : ellVal x.1 ≠ ellVal y.1) :
    ellVal (x - y).1 = min (ellVal x.1) (ellVal y.1) := by
  rw [sub_eq_add_neg, ellVal_add_eq_min_of_ne (by rwa [ellVal_neg]), ellVal_neg]

/-- A sum of integral elements of `ℚ̄_ℓ` with valuations at least `c` has valuation at least `c`. -/
lemma le_ellVal_sum {s : Finset ι} {f : ι → intQpBar ℓ} {c : ℝ≥0∞}
    (h_le : ∀ i ∈ s, c ≤ ellVal (f i).1) : c ≤ ellVal (∑ i ∈ s, f i).1 := by
  simpa only [ellAddVal_apply] using ellAddVal.map_le_sum (f := f) h_le

lemma ellVal_eq_zero_iff_isUnit {x : intQpBar ℓ} : ellVal x.1 = 0 ↔ IsUnit x := by
  rw [isUnit_iff_dvd_one, dvd_iff_ellVal_le, ← ellAddVal_apply 1, AddValuation.map_one,
    nonpos_iff_eq_zero]

/-- The valuation `ellVal` of a product of integral elements of `ℚ̄_ℓ` is the sum of their
valuations. -/
lemma ellVal_multiset_prod (s : Multiset (intQpBar ℓ)) :
    ellVal s.prod.1 = (s.map fun x : intQpBar ℓ ↦ ellVal x.1).sum := by
  induction s using Multiset.induction_on with
  | empty => exact ellVal_eq_zero_iff_isUnit.2 isUnit_one
  | cons x s ih =>
    rw [Multiset.prod_cons, ellVal_val_mul, ih, Multiset.map_cons, Multiset.sum_cons]

lemma ellVal_prod (s : Finset ι) (f : ι → intQpBar ℓ) :
    ellVal (∏ i ∈ s, f i).1 = ∑ i ∈ s, ellVal (f i).1 := by
  simpa using ellVal_multiset_prod (s.val.map f)

/-! ### Roots of monic polynomials -/

/-- A monic polynomial over `ℤ̄_ℓ = intQpBar ℓ` splits: its roots in `ℚ̄_ℓ` are integral over this
valuation ring, which is integrally closed. -/
lemma splits_of_monic {g : (intQpBar ℓ)[X]} (hg : g.Monic) : g.Splits := by
  have h_splits : (g.map (algebraMap (intQpBar ℓ) (PadicAlgCl ℓ))).Splits := IsAlgClosed.splits _
  refine h_splits.of_splits_map_of_injective Subtype.val_injective fun α hα ↦ ?_
  exact IsIntegrallyClosed.algebraMap_eq_of_integral
    ⟨g, hg, (eval₂_eq_eval_map _).trans (isRoot_of_mem_roots hα)⟩

/-- A monic polynomial of nonzero degree over `ℤ̄_ℓ = intQpBar ℓ` has a root in this ring. -/
lemma exists_eval_eq_zero_of_monic {g : (intQpBar ℓ)[X]} (hg : g.Monic) (h_deg : g.degree ≠ 0) :
    ∃ α : intQpBar ℓ, g.eval α = 0 :=
  (splits_of_monic hg).exists_eval_eq_zero h_deg

/-- Every nonnegative rational number `ρ` is the valuation `v = ellVal`, normalised by `v(ℓ) = 1`,
of some element `π` of `ℤ̄_ℓ = intQpBar ℓ`. -/
lemma exists_ellVal_eq (ρ : ℚ≥0) : ∃ π : intQpBar ℓ, ellVal π.1 = (ρ : ℝ≥0) := by
  -- for `ρ = a / b` take a root of `Y ^ b - ℓ ^ a`
  obtain ⟨π, hπ⟩ := exists_eval_eq_zero_of_monic
    (monic_X_pow_sub_C ((ℓ : intQpBar ℓ) ^ ρ.num) ρ.den_ne_zero)
    ((degree_X_pow_sub_C ρ.den_pos _).trans_ne (mod_cast ρ.den_ne_zero))
  have h_pow : π.1 ^ ρ.den = (ℓ : PadicAlgCl ℓ) ^ ρ.num := by
    simpa [sub_eq_zero, Subtype.ext_iff] using hπ
  have h_val : (ρ.den : ℝ≥0∞) * ellVal π.1 = ρ.num := by
    rw [← ellVal_pow, h_pow, ellVal_pow, ellVal_ell, mul_one]
  have h_den : (ρ.den : ℝ≥0∞) * (ρ : ℝ≥0) = ρ.num :=
    mod_cast congrArg (NNRat.cast : ℚ≥0 → ℝ≥0) ρ.den_mul_eq_num
  exact ⟨π, (ENNReal.mul_right_inj (by simp) (by simp)).1 (h_val.trans h_den.symm)⟩

/-- The residue field of `ℤ̄_ℓ = intQpBar ℓ`, the ring of integral elements of `ℚ̄_ℓ`, is
algebraically closed. -/
instance isAlgClosed_residueField : IsAlgClosed (ResidueField (intQpBar ℓ)) := by
  refine .of_exists_root _ fun f hf h_irred ↦ ?_
  obtain ⟨g, rfl, h_deg, hg⟩ :=
    lifts_and_degree_eq_and_monic (mem_lifts_of_surjective residue_surjective f) hf
  obtain ⟨α, hα⟩ := exists_eval_eq_zero_of_monic hg
    (h_deg.trans_ne (degree_pos_of_irreducible h_irred).ne')
  exact ⟨residue _ α, by rw [eval_map_apply, hα, map_zero]⟩

/-! ### The Gauss valuation -/

/-- The Gauss valuation `v_ρ(g)` of radius `ρ` of a polynomial `g = ∑ y_i Y ^ i` over
`ℤ̄_ℓ = intQpBar ℓ`: the least of the numbers `v(y_i) + ρ i`, where `v = ellVal`. -/
def gaussVal (ρ : ℚ≥0) (g : (intQpBar ℓ)[X]) : ℝ≥0∞ :=
  ⨅ i : ℕ, ellVal (g.coeff i).1 + (ρ : ℝ≥0) * (i : ℝ≥0∞)

/-- The Gauss valuation `v_ρ(g)` is at most `v(y_i) + ρ i` for each coefficient `y_i` of `g`. -/
lemma gaussVal_le_coeff (g : (intQpBar ℓ)[X]) (i : ℕ) :
    gaussVal ρ g ≤ ellVal (g.coeff i).1 + (ρ : ℝ≥0) * (i : ℝ≥0∞) :=
  iInf_le _ i

lemma gaussVal_mono (h_le : ρ ≤ ρ') (g : (intQpBar ℓ)[X]) : gaussVal ρ g ≤ gaussVal ρ' g :=
  iInf_mono fun i ↦ by gcongr

/-- At the points `y` with `v(y) ≥ ρ` we have `v(g(y)) ≥ v_ρ(g)`: here `v = ellVal`, and
`v_ρ = gaussVal ρ` is the Gauss valuation of radius `ρ`. -/
lemma gaussVal_le_eval (g : (intQpBar ℓ)[X]) {y : intQpBar ℓ} (hy : (ρ : ℝ≥0) ≤ ellVal y.1) :
    gaussVal ρ g ≤ ellVal (g.eval y).1 := by
  rw [eval_eq_sum_range]
  refine le_ellVal_sum fun i _ ↦ (gaussVal_le_coeff g i).trans ?_
  grw [ellVal_val_mul, SubmonoidClass.coe_pow, ellVal_pow, mul_comm, hy]

/-- For a prime `ℓ`, a radius `ρ ≥ 0` and a polynomial `g` over the valuation ring `intQpBar ℓ` of
ℚ̄_ℓ, the Gauss valuation `gaussVal ρ g` is at most `v(g(0))`, the valuation of the constant term of
`g`. Here `gaussVal ρ g` is the least of `v(y_i) + ρ i` over the coefficients `y_i` of `g`, and
`v = ellVal` is the ℓ-adic valuation normalised by `v(ℓ) = 1`. -/
lemma gaussVal_le_eval_zero (g : (intQpBar ℓ)[X]) : gaussVal ρ g ≤ ellVal (g.eval 0).1 :=
  gaussVal_le_eval g (by simp [ellVal_zero])

/-- If the coefficient of `Y ^ d` in `g` is a unit, then the Gauss valuation `v_ρ(g) = gaussVal ρ g`
is at most `ρ d`. -/
lemma gaussVal_le_of_isUnit_coeff {g : (intQpBar ℓ)[X]} {d : ℕ} (hg : IsUnit (g.coeff d)) :
    gaussVal ρ g ≤ (ρ : ℝ≥0) * (d : ℝ≥0∞) := by
  simpa [ellVal_eq_zero_iff_isUnit.2 hg] using gaussVal_le_coeff (ρ := ρ) g d

/-- Putting `Y = π Y'`, where `π` in `ℤ̄_ℓ = intQpBar ℓ` has valuation `v(π) = ρ` (`v = ellVal`),
turns the Gauss valuation of radius `ρ` into that of radius `0`: `v₀(g(π Y')) = v_ρ(g)`. -/
lemma gaussVal_zero_comp_C_mul_X {π : intQpBar ℓ} (hπ : ellVal π.1 = (ρ : ℝ≥0))
    (g : (intQpBar ℓ)[X]) : gaussVal 0 (g.comp (C π * X)) = gaussVal ρ g := by
  refine iInf_congr fun i ↦ ?_
  rw [comp_C_mul_X_coeff, ellVal_val_mul, SubmonoidClass.coe_pow, ellVal_pow, hπ]
  simp [mul_comm]

/-- Scaling: a polynomial `g` over `ℤ̄_ℓ = intQpBar ℓ` is `c` times a polynomial `q` whose reduction
to the residue field is nonzero, and `v(c)`, where `v = ellVal`, is the Gauss valuation `v₀(g)` of
radius `0`. -/
lemma exists_eq_C_mul_map_residue_ne_zero (g : (intQpBar ℓ)[X]) :
    ∃ (c : intQpBar ℓ) (q : (intQpBar ℓ)[X]),
      g = C c * q ∧ q.map (residue (intQpBar ℓ)) ≠ 0 ∧ ellVal c.1 = gaussVal 0 g := by
  obtain rfl | hg := eq_or_ne g 0
  · exact ⟨0, 1, by simp, by simp, by simp [gaussVal, ellVal_zero]⟩
  -- take for `c` a coefficient of least valuation
  obtain ⟨k, hk, h_min⟩ :=
    g.support.exists_min_image (fun i ↦ ellVal (g.coeff i).1) (support_nonempty.2 hg)
  have h_dvd (i : ℕ) : g.coeff k ∣ g.coeff i := by
    by_cases hi : i ∈ g.support
    · exact dvd_iff_ellVal_le.2 (h_min i hi)
    · simp [notMem_support_iff.1 hi]
  obtain ⟨q, hq⟩ : C (g.coeff k) ∣ g := (C_dvd_iff_dvd_coeff (g.coeff k) g).2 h_dvd
  have h_one : q.coeff k = 1 :=
    mul_left_cancel₀ (mem_support_iff.1 hk) (by rw [← coeff_C_mul, ← hq, mul_one])
  refine ⟨g.coeff k, q, hq, support_nonempty.1 ⟨k, by simp [h_one]⟩, le_antisymm ?_ ?_⟩
  · exact le_iInf fun i ↦ (dvd_iff_ellVal_le.1 (h_dvd i)).trans le_self_add
  · simpa using gaussVal_le_coeff (ρ := 0) g k

/-- Finitely many polynomials over `ℤ̄_ℓ = intQpBar ℓ` with nonzero reductions take unit values at
one point: the reductions have finitely many roots, and the residue field is algebraically closed,
hence infinite. -/
lemma exists_forall_isUnit_eval [Finite ι] {q : ι → (intQpBar ℓ)[X]}
    (hq : ∀ i : ι, (q i).map (residue (intQpBar ℓ)) ≠ 0) :
    ∃ y : intQpBar ℓ, ∀ i : ι, IsUnit ((q i).eval y) := by
  have h_finite : (⋃ i, {z | ((q i).map (residue (intQpBar ℓ))).IsRoot z}).Finite :=
    Set.finite_iUnion fun i ↦ finite_setOfPred_isRoot (hq i)
  obtain ⟨y, hy⟩ := residue_surjective.exists.1 h_finite.exists_notMem
  refine ⟨y, fun i ↦ ?_⟩
  rw [← residue_ne_zero_iff_isUnit, ← eval_map_apply]
  exact fun h_root ↦ hy (Set.mem_iUnion.2 ⟨i, h_root⟩)

/-- Generic points: for finitely many polynomials over `ℤ̄_ℓ = intQpBar ℓ` there is one point `y`
with `v(y) ≥ ρ` at which `v(g(y)) = v_ρ(g)` for all of them; here `v = ellVal`, and
`v_ρ = gaussVal ρ` is the Gauss valuation of radius `ρ`. -/
lemma exists_forall_ellVal_eval_eq_gaussVal [Finite ι] (ρ : ℚ≥0) (g : ι → (intQpBar ℓ)[X]) :
    ∃ y : intQpBar ℓ,
      (ρ : ℝ≥0) ≤ ellVal y.1 ∧
      ∀ i : ι, ellVal ((g i).eval y).1 = gaussVal ρ (g i) := by
  -- Put `Y = π Y'` with `v(π) = ρ`, scale each polynomial, and avoid the roots of the reductions.
  obtain ⟨π, hπ⟩ := exists_ellVal_eq (ℓ := ℓ) ρ
  have h_scale (i : ι) : ∃ (c : intQpBar ℓ) (q : (intQpBar ℓ)[X]),
      (g i).comp (C π * X) = C c * q ∧ q.map (residue (intQpBar ℓ)) ≠ 0 ∧
        ellVal c.1 = gaussVal 0 ((g i).comp (C π * X)) :=
    exists_eq_C_mul_map_residue_ne_zero _
  choose c q h_eq hq hc using h_scale
  obtain ⟨y', hy'⟩ := exists_forall_isUnit_eval hq
  refine ⟨π * y', by simp only [ellVal_val_mul, hπ, le_self_add], fun i ↦ ?_⟩
  have h_eval : (g i).eval (π * y') = c i * (q i).eval y' :=
    calc (g i).eval (π * y') = ((g i).comp (C π * X)).eval y' := by simp
      _ = c i * (q i).eval y' := by rw [h_eq, eval_mul, eval_C]
  rw [h_eval, ellVal_val_mul, ellVal_eq_zero_iff_isUnit.2 (hy' i), add_zero, hc,
    gaussVal_zero_comp_C_mul_X hπ]

lemma gaussVal_one : gaussVal ρ (1 : (intQpBar ℓ)[X]) = 0 := by
  simpa using gaussVal_le_of_isUnit_coeff (ρ := ρ) (g := (1 : (intQpBar ℓ)[X])) (d := 0) (by simp)

/-- Gauss's lemma: the Gauss valuation `v_ρ` of a product of two integral polynomials is the sum of
their Gauss valuations. Evaluate at a point that is generic for `f`, `g` and `f g`. -/
lemma gaussVal_mul (f g : (intQpBar ℓ)[X]) :
    gaussVal ρ (f * g) = gaussVal ρ f + gaussVal ρ g := by
  obtain ⟨y, -, hy⟩ := exists_forall_ellVal_eval_eq_gaussVal ρ ![f, g, f * g]
  calc gaussVal ρ (f * g) = ellVal ((f * g).eval y).1 := (hy 2).symm
    _ = ellVal (f.eval y).1 + ellVal (g.eval y).1 := by rw [eval_mul, ellVal_val_mul]
    _ = gaussVal ρ f + gaussVal ρ g := congrArg₂ (· + ·) (hy 0) (hy 1)

lemma gaussVal_prod (s : Finset ι) (g : ι → (intQpBar ℓ)[X]) :
    gaussVal ρ (∏ i ∈ s, g i) = ∑ i ∈ s, gaussVal ρ (g i) := by
  induction s using Finset.cons_induction <;> simp [gaussVal_one, gaussVal_mul, *]

/-! ### The Gauss valuation and the roots -/

/-- For one integral polynomial `f` there is an integral point `y` with `v(y) ≥ ρ` at which
`v(f(y))` is the Gauss valuation `v_ρ(f)`. -/
lemma exists_ellVal_eval_eq_gaussVal (ρ : ℚ≥0) (f : (intQpBar ℓ)[X]) :
    ∃ y : intQpBar ℓ, (ρ : ℝ≥0) ≤ ellVal y.1 ∧ ellVal (f.eval y).1 = gaussVal ρ f := by
  simpa using exists_forall_ellVal_eval_eq_gaussVal ρ fun _ : Unit ↦ f

/-- For an integral element `α` the Gauss valuation of radius `ρ` of the linear polynomial `Y - α`
is `min(v(α), ρ)`, where `v = ellVal`: evaluation at `0` and the leading coefficient
give `≤`, and a generic point gives `≥`. -/
lemma gaussVal_X_sub_C (α : intQpBar ℓ) :
    gaussVal ρ (X - C α : (intQpBar ℓ)[X]) = min (ellVal α.1) (ρ : ℝ≥0) := by
  refine le_antisymm (le_min ?_ ?_) ?_
  · have h_eval : (X - C α : (intQpBar ℓ)[X]).eval 0 = -α := by simp
    rw [← ellVal_neg α, ← h_eval]
    exact gaussVal_le_eval_zero (X - C α)
  · simpa using gaussVal_le_of_isUnit_coeff (ρ := ρ) (g := X - C α) (d := 1) (by simp)
  · obtain ⟨y, hy, h_eq⟩ := exists_ellVal_eval_eq_gaussVal ρ (X - C α : (intQpBar ℓ)[X])
    calc min (ellVal α.1) (ρ : ℝ≥0) ≤ min (ellVal y.1) (ellVal α.1) :=
          (min_comm _ _).trans_le (min_le_min_right _ hy)
      _ ≤ ellVal (y - α).1 := min_ellVal_le_ellVal_sub y α
      _ = gaussVal ρ (X - C α) := by rw [← h_eq, eval_sub, eval_X, eval_C]

/-- For a prime `ℓ`, a radius `ρ ≥ 0` and a multiset `R` of integral elements (elements of the
valuation ring `intQpBar ℓ` of ℚ̄_ℓ), the Gauss valuation `gaussVal ρ` of `∏ (Y - α)` is
`∑ min(v(α), ρ)`, both over `α` in `R`. Here `v = ellVal` is the ℓ-adic valuation normalised by
`v(ℓ) = 1`, and `gaussVal ρ g` is the least of `v(y_i) + ρ i` over the coefficients `y_i` of `g`. -/
lemma gaussVal_prod_X_sub_C (R : Multiset (intQpBar ℓ)) :
    gaussVal ρ (R.map fun α : intQpBar ℓ ↦ X - C α).prod =
      (R.map fun α : intQpBar ℓ ↦ min (ellVal α.1) (ρ : ℝ≥0)).sum := by
  induction R using Multiset.induction_on with
  | empty => simp [gaussVal_one]
  | cons α R ih => simp [gaussVal_mul, ih, gaussVal_X_sub_C]

/-- An integral polynomial `q` without integral roots has the same valuation `ellVal` at all
integral points: if `q ≠ 0`, each root `β` in `ℚ̄_ℓ` has `‖β‖ > 1`, so `‖y - β‖ = ‖β‖` for integral
`y`. -/
lemma ellVal_eval_eq_of_roots_eq_zero {q : (intQpBar ℓ)[X]} (hq : q.roots = 0)
    (y y' : intQpBar ℓ) : ellVal (q.eval y).1 = ellVal (q.eval y').1 := by
  obtain rfl | hq₀ := eq_or_ne q 0
  · simp
  let Q : (PadicAlgCl ℓ)[X] := q.map (algebraMap (intQpBar ℓ) (PadicAlgCl ℓ))
  have h_eval (z : intQpBar ℓ) : (q.eval z).1 = Q.eval z.1 :=
    (eval_map_apply (algebraMap (intQpBar ℓ) (PadicAlgCl ℓ)) z).symm
  have h_large (β : PadicAlgCl ℓ) (hβ : β ∈ Q.roots) : 1 < ‖β‖ := by
    by_contra! h_int
    -- otherwise `β` is an integral root of `q`
    let b : intQpBar ℓ := ⟨β, h_int⟩
    have h_root : b ∈ q.roots :=
      (mem_roots hq₀).2 (Subtype.ext ((h_eval b).trans (isRoot_of_mem_roots hβ)))
    simp [hq] at h_root
  have h_sub (z : intQpBar ℓ) (β : PadicAlgCl ℓ) (hβ : β ∈ Q.roots) : ‖z.1 - β‖ = ‖β‖ := by
    have h_lt : ‖z.1‖ < ‖-β‖ := (norm_coe_le_one z).trans_lt (by simpa using h_large β hβ)
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_lt.ne,
      max_eq_right h_lt.le, norm_neg]
  have h_norm (z : intQpBar ℓ) : ‖(q.eval z).1‖ = ‖Q.leadingCoeff‖ * (Q.roots.map norm).prod :=
    calc ‖(q.eval z).1‖ = ‖Q.leadingCoeff * (Q.roots.map fun β ↦ z.1 - β).prod‖ := by
          rw [h_eval, (IsAlgClosed.splits Q).eval_eq_prod_roots]
      _ = ‖Q.leadingCoeff‖ * (Q.roots.map fun β ↦ ‖z.1 - β‖).prod := by
          simp [← normHom_apply (Multiset.prod _), map_multiset_prod]
      _ = ‖Q.leadingCoeff‖ * (Q.roots.map norm).prod := by rw [Multiset.map_congr rfl (h_sub z)]
  exact ellVal_congr_norm ((h_norm y).trans (h_norm y').symm)

/-- An integral polynomial `g` is `q ∏ (Y - α)` over its integral roots `α` with multiplicity,
where `v(q(y)) = v₀(g)` at all integral points `y`. Here `v` is the valuation `ellVal` and `v₀`
the Gauss valuation of radius `0`. -/
lemma exists_eq_mul_prod_roots (g : (intQpBar ℓ)[X]) :
    ∃ q : (intQpBar ℓ)[X],
      g = q * (g.roots.map fun α : intQpBar ℓ ↦ X - C α).prod ∧
      ∀ y : intQpBar ℓ, ellVal (q.eval y).1 = gaussVal 0 g := by
  obtain ⟨q, h_eq, -, hq⟩ := g.exists_prod_multiset_X_sub_C_mul
  refine ⟨q, by rw [mul_comm, h_eq], fun y ↦ ?_⟩
  obtain ⟨z, -, hz⟩ := exists_ellVal_eval_eq_gaussVal 0 q
  have h_prod : gaussVal 0 (g.roots.map fun α ↦ X - C α).prod = 0 := by
    simp [gaussVal_prod_X_sub_C, min_eq_right zero_le]
  rw [ellVal_eval_eq_of_roots_eq_zero hq y z, hz, ← h_eq, gaussVal_mul, h_prod, zero_add]

/-- The Gauss valuation `v_ρ(g)` of radius `ρ`, the least of the `v(y_i) + ρ i` for the coefficients
`y_i` of `g`, is `v₀(g) + ∑ min(v(α), ρ)`: the sum is over the integral roots `α` of `g` with
multiplicity, `v` is the valuation `ellVal` and `v₀` the Gauss valuation of radius `0`. -/
theorem gaussVal_eq_add_sum_roots (g : (intQpBar ℓ)[X]) :
    gaussVal ρ g =
      gaussVal 0 g + (g.roots.map fun α : intQpBar ℓ ↦ min (ellVal α.1) (ρ : ℝ≥0)).sum := by
  obtain ⟨q, h_eq, hq⟩ := exists_eq_mul_prod_roots g
  obtain ⟨y, -, hy⟩ := exists_ellVal_eval_eq_gaussVal ρ q
  have h_const : gaussVal ρ q = gaussVal 0 g := hy.symm.trans (hq y)
  conv_lhs => rw [h_eq, gaussVal_mul, gaussVal_prod_X_sub_C, h_const]

/-- At an integral point `y` an integral polynomial `g` has `v(g(y)) = v₀(g) + ∑ v(y - α)`, the sum
over the integral roots `α` of `g` with multiplicity; `v` is the valuation `ellVal` and `v₀` the
Gauss valuation of radius `0`. -/
theorem ellVal_eval_eq_add_sum_roots (g : (intQpBar ℓ)[X]) (y : intQpBar ℓ) :
    ellVal (g.eval y).1 =
      gaussVal 0 g + (g.roots.map fun α : intQpBar ℓ ↦ ellVal (y - α).1).sum := by
  obtain ⟨q, h_eq, hq⟩ := exists_eq_mul_prod_roots g
  have h_eval : g.eval y = q.eval y * (g.roots.map fun α : intQpBar ℓ ↦ y - α).prod := by
    simpa [eval_multiset_prod] using congrArg (eval y) h_eq
  rw [h_eval, ellVal_val_mul, hq, ellVal_multiset_prod, Multiset.map_map, Function.comp_def]

/-! ### Powers of elements near `1`, geometric sums and roots of unity -/

/-- Let `x` be integral with `v(x) ≥ ρ`, for the valuation `v` = `ellVal`, and let `1 ≤ j ≤ m`.
Then some integral `x'` with `(1 + x') ^ j = 1 + x` has `v(x') ≥ ρ / m`: the `j` solutions have
the product `± x`. -/
lemma exists_one_add_pow_eq {m j : ℕ} (hj : j ∈ Set.Icc 1 m) {x : intQpBar ℓ}
    (hx : (ρ : ℝ≥0) ≤ ellVal x.1) :
    ∃ x' : intQpBar ℓ, (1 + x') ^ j - 1 = x ∧ (↑(ρ / m) : ℝ≥0) ≤ ellVal x'.1 := by
  obtain ⟨hj_pos, hj_le⟩ := hj
  let g : (intQpBar ℓ)[X] := (X + C 1) ^ j - C (1 + x)
  have hg : g.IsMonicOfDegree j := by
    simpa [g] using ((isMonicOfDegree_X_add_one 1).pow j).sub (q := C (1 + x)) (by simpa)
  have h_splits : g.Splits := splits_of_monic hg.monic
  have h_card : g.roots.card = j := h_splits.natDegree_eq_card_roots.symm.trans hg.natDegree_eq
  have h_prod : -x = (g.roots.map fun α ↦ -α).prod := by
    simpa [g] using h_splits.eval_eq_prod_roots_of_monic hg.monic 0
  have h_sum : ellVal x.1 = (g.roots.map fun α ↦ ellVal α.1).sum := by
    simp only [← ellVal_neg x, h_prod, ellVal_multiset_prod, Multiset.map_map, Function.comp_def,
      ellVal_neg]
  -- take a root of largest valuation
  obtain ⟨x', hx', h_max⟩ := g.roots.exists_max_image (fun α : intQpBar ℓ ↦ ellVal α.1)
    (Multiset.card_pos.1 (hj_pos.trans_eq h_card.symm))
  have h_le : (ρ : ℝ≥0) ≤ ellVal x'.1 * m :=
    calc ((ρ : ℝ≥0) : ℝ≥0∞) ≤ (g.roots.map fun α ↦ ellVal α.1).sum := hx.trans_eq h_sum
      _ ≤ j * ellVal x'.1 := by
        simpa [h_card] using Multiset.sum_map_le_sum_map _ (fun _ ↦ ellVal x'.1) h_max
      _ ≤ ellVal x'.1 * m := by grw [mul_comm, hj_le]
  refine ⟨x', ?_, ?_⟩
  · simpa [g, sub_eq_zero, sub_eq_iff_eq_add', add_comm] using isRoot_of_mem_roots hx'
  · rw [NNRat.cast_div, NNRat.cast_natCast, ENNReal.coe_div (Nat.cast_ne_zero.2 (by omega))]
    exact ENNReal.div_le_of_le_mul h_le

/-- The geometric sum of length `a b` is the geometric sum of length `a` times the geometric sum of
length `b` in `α ^ a`. -/
lemma geom_sum_range_mul {R : Type*} [CommSemiring R] (α : R) (a b : ℕ) :
    ∑ i ∈ range (a * b), α ^ i = (∑ i ∈ range a, α ^ i) * ∑ k ∈ range b, (α ^ a) ^ k := by
  induction b with
  | zero => simp
  | succ b ih => simp [sum_range_add, ih, pow_add, ← sum_mul, pow_mul, mul_add,
      sum_range_succ, mul_comm]

/-- If `v(α - 1) ≥ ρ` with `ρ ≤ 1`, where `v` is the valuation `ellVal`, then `∑_{i < ℓ ^ n} α ^ i`
has valuation at least `n ρ`: it is the product of the factors `∑_{i < ℓ} α ^ (i ℓ ^ h)` for
`h < n`, each congruent to `ℓ` modulo `α - 1`, and `v(ℓ) = 1 ≥ ρ`. -/
lemma le_ellVal_geom_sum (hρ : ρ ≤ 1) {α : intQpBar ℓ} (hα : (ρ : ℝ≥0) ≤ ellVal (α - 1).1)
    (n : ℕ) : (n : ℝ≥0∞) * (ρ : ℝ≥0) ≤ ellVal (∑ i ∈ range (ℓ ^ n), α ^ i).1 := by
  have h_factor (h : ℕ) : (ρ : ℝ≥0) ≤ ellVal (∑ i ∈ range ℓ, (α ^ ℓ ^ h) ^ i).1 := by
    set β : intQpBar ℓ := α ^ ℓ ^ h
    have h_dvd : α - 1 ∣ ∑ i ∈ range ℓ, (β ^ i - 1) :=
      dvd_sum fun i _ ↦ (sub_one_dvd_pow_sub_one α _).trans (sub_one_dvd_pow_sub_one β i)
    have hℓ : (ρ : ℝ≥0) ≤ ellVal (ℓ : intQpBar ℓ).1 := by simpa [ellVal_ell] using hρ
    rw [show ∑ i ∈ range ℓ, β ^ i = ∑ i ∈ range ℓ, (β ^ i - 1) + ℓ by simp]
    exact (le_min (hα.trans (dvd_iff_ellVal_le.1 h_dvd)) hℓ).trans (min_ellVal_le_ellVal_add _ _)
  induction n with
  | zero => simp
  | succ n ih => grw [pow_succ, geom_sum_range_mul, ellVal_val_mul, Nat.cast_succ, add_one_mul,
      ih, h_factor n]

/-- A root of unity `ζ` of order `ℓ ^ (h + 1)` has `v(ζ - 1) = 1 / φ(ℓ ^ (h + 1))`, where `φ` is
Euler's function. -/
lemma ellVal_sub_one_of_isPrimitiveRoot {h : ℕ} {ζ : intQpBar ℓ}
    (hζ : IsPrimitiveRoot ζ (ℓ ^ (h + 1))) :
    ellVal (ζ - 1).1 = (Nat.totient (ℓ ^ (h + 1)) : ℝ≥0∞)⁻¹ := by
  have h_norm : ‖(ζ.1 - 1) ^ Nat.totient (ℓ ^ (h + 1))‖ = ‖(ℓ : PadicAlgCl ℓ)‖ := by
    rw [norm_pow, Period.norm_zeta_sub_one_pow (IsPrimitiveRoot.coe_submonoidClass_iff.2 hζ)]
  refine ENNReal.eq_inv_of_mul_eq_one_left ?_
  simpa [ellVal_pow, ellVal_ell, mul_comm] using ellVal_congr_norm h_norm

/-- If `ζ` has order `ℓ ^ (h + 1)`, `j ≠ 0` and the exponent `t = padicValNat ℓ j` of `ℓ` in `j`
is at most `h`, then `v(ζ ^ j - 1) = ℓ ^ t / φ(ℓ ^ (h + 1))`; here `v = ellVal` and `φ` is
Euler's function. -/
lemma ellVal_pow_sub_one_of_isPrimitiveRoot {h j : ℕ} {ζ : intQpBar ℓ}
    (hζ : IsPrimitiveRoot ζ (ℓ ^ (h + 1))) (hj : j ≠ 0) (hjh : padicValNat ℓ j ≤ h) :
    ellVal (ζ ^ j - 1).1 =
      (ℓ ^ padicValNat ℓ j : ℕ) * (Nat.totient (ℓ ^ (h + 1)) : ℝ≥0∞)⁻¹ := by
  -- write `j = ℓ ^ t j'` and `h = t + k`; then `ζ ^ j` has order `ℓ ^ (k + 1)`
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨t, j', hj', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hj ℓ hℓ.ne_one
  have ht : padicValNat ℓ (ℓ ^ t * j') = t := by
    simp [padicValNat.mul, hℓ.ne_zero, right_ne_zero_of_mul hj, hj']
  rw [ht] at hjh ⊢
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hjh
  have h_order : IsPrimitiveRoot ((ζ ^ ℓ ^ t) ^ j') (ℓ ^ (k + 1)) :=
    (hζ.pow (pow_pos hℓ.pos _) (by ring)).pow_of_coprime j'
      ((hℓ.coprime_iff_not_dvd.2 hj').pow_left _).symm
  have h_totient : Nat.totient (ℓ ^ (t + k + 1)) = ℓ ^ t * Nat.totient (ℓ ^ (k + 1)) := by
    simp only [Nat.totient_prime_pow_succ hℓ, pow_add ℓ t k, mul_assoc]
  rw [pow_mul, ellVal_sub_one_of_isPrimitiveRoot h_order, h_totient, Nat.cast_mul,
    ENNReal.mul_inv (by simp) (by simp), ENNReal.mul_inv_cancel_left (by simp [hℓ.ne_zero])]
  simp

/-- Let `ℓ` be a prime and `ζ` an element of the valuation ring of ℚ̄_ℓ with `ζ ^ ℓ ^ h = 1`. Let
`v = ellVal` be the valuation normalised by `v(ℓ) = 1`, which is `-log_ℓ |·|` on integral
elements. If `ρ < 1` and `v(ζ - 1) ≤ ρ / m`, then `v(ζ ^ j - 1) ≤ ρ` for every `j` with
`1 ≤ j ≤ m`. -/
lemma ellVal_pow_sub_one_le (hρ : ρ < 1) {m j h : ℕ} (hj : j ∈ Set.Icc 1 m) {ζ : intQpBar ℓ}
    (hζ : ζ ^ ℓ ^ h = 1) (hζρ : ellVal (ζ - 1).1 ≤ (↑(ρ / m) : ℝ≥0)) :
    ellVal (ζ ^ j - 1).1 ≤ (ρ : ℝ≥0) := by
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨hj_pos, hj_le⟩ := hj
  -- `ζ` has order `ℓ ^ k`, and `k ≠ 0` because `v(ζ - 1)` is finite
  obtain ⟨k, -, hk⟩ : ∃ k ≤ h, orderOf ζ = ℓ ^ k :=
    (Nat.dvd_prime_pow hℓ).1 (orderOf_dvd_of_pow_eq_one hζ)
  obtain - | k := k
  · simp [orderOf_eq_one_iff.1 (hk.trans (pow_zero ℓ)), ellVal_zero] at hζρ
  have h_order : IsPrimitiveRoot ζ (ℓ ^ (k + 1)) := by simpa [hk] using IsPrimitiveRoot.orderOf ζ
  have h_ratio : m * (Nat.totient (ℓ ^ (k + 1)) : ℝ≥0∞)⁻¹ ≤ (ρ : ℝ≥0) := by
    rw [ellVal_sub_one_of_isPrimitiveRoot h_order, NNRat.cast_div, NNRat.cast_natCast,
      ENNReal.coe_div (Nat.cast_ne_zero.2 (by omega))] at hζρ
    exact (mul_le_mul_right hζρ _).trans ENNReal.mul_div_le
  have h_lt : m < Nat.totient (ℓ ^ (k + 1)) := by
    have h_lt_one : m / (Nat.totient (ℓ ^ (k + 1)) : ℝ≥0∞) < 1 := h_ratio.trans_lt (mod_cast hρ)
    simpa [ENNReal.div_lt_iff, hℓ.ne_zero] using h_lt_one
  -- `ℓ ^ v(j) ≤ m < φ(ℓ ^ (k + 1)) ≤ ℓ ^ (k + 1)`, so `v(j) ≤ k`
  have h_pow_le : ℓ ^ padicValNat ℓ j ≤ m := (Nat.le_of_dvd hj_pos pow_padicValNat_dvd).trans hj_le
  have h_pow_lt : ℓ ^ padicValNat ℓ j < ℓ ^ (k + 1) :=
    h_pow_le.trans_lt (h_lt.trans_le (Nat.totient_le _))
  have h_val_le : padicValNat ℓ j ≤ k :=
    Nat.le_of_lt_succ ((Nat.pow_lt_pow_iff_right hℓ.one_lt).1 h_pow_lt)
  calc ellVal (ζ ^ j - 1).1
      = (ℓ ^ padicValNat ℓ j : ℕ) * (Nat.totient (ℓ ^ (k + 1)) : ℝ≥0∞)⁻¹ :=
        ellVal_pow_sub_one_of_isPrimitiveRoot h_order (Nat.ne_zero_of_lt hj_pos) h_val_le
    _ ≤ m * (Nat.totient (ℓ ^ (k + 1)) : ℝ≥0∞)⁻¹ := by gcongr
    _ ≤ (ρ : ℝ≥0) := h_ratio

end New.Selmer

end
