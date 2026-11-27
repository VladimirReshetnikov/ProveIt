import Lib.Adelic.TraceFormula.OrbitalUnfolding
import New.Appendix.DiscreteSeries.PositionGroup
import New.Determinant.AuxiliaryForms.DeepLevelPoincarePeriod
import New.Determinant.AuxiliaryForms.PathData
import New.UpperBound.Objects.RowChain

/-!
# Vanishing of forms on Y₀ orthogonal to the deep level on Ỹ^0_0

A form `y` of level `J_M = D.chosenLevel` on a hermitian space `V` is zero if it is orthogonal to
the restrictions of all forms of the deep level `J(𝔟)` on `V ⊕ ⟨1⟩`, translated by a suitable real
point `ω`. This requires size conditions on the level and a lower bound for the pairing of the
matrix coefficients for the parameter `l` of `V` and the parameter `l'` of `V ⊕ ⟨1⟩`.

Every bound `S` of `‖y‖` is halved. The smoothing of `y` is its convolution with the translated
coefficient for `l'`; the point `ω` with the lower bound for the pairing comes from steepness, in
the proof of `New.Data.exists_eq_zero_of_orthogonal_gridLevelForms`.

1. Decay: `New.Exchange.integral_typeKernelMajorant_le`.
2. The cusp: `New.Exchange.norm_le_half_of_firstMinimum_lt`.
3. A Poincaré series is a form, so its period is zero:
   `New.Exchange.poincare_period_translatedCoeff_eq_zero`.
4. Unfolding shows that the smoothing of `y` is small: `New.Exchange.norm_poincare_period_sub_le`
   and `New.Exchange.norm_realConv_translatedCoeff_le`.
5. Undoing the smoothing: `New.Exchange.norm_le_half_of_le_firstMinimum`.

## Main definitions and results

* `New.Exchange.HasDeepLevelSizes`: the size conditions. The real number `m` in them is at least a
  power of `β` that absorbs all constants in the estimates.
* `New.Exchange.eq_zero_of_petersson_translate_eq_zero`: the criterion at a given real point;
  `New.Exchange.exists_forall_eq_zero_of_petersson_restrict_eq_zero` chooses the point place by
  place.
* `New.Data.exists_eq_zero_of_orthogonal_gridLevelForms`: the forms of level `J(𝔟)` on `Ỹ^0_0`,
  restricted to `U(Y₀)` after translation by one real point, detect every nonzero form of level
  `J_M` on `Y₀`.

Notions from other files:
* `New.typeKernel`: `typeKernel l s` is the product over the infinite places `w` of the formal
  degree times the conjugate matrix coefficient `(l w).dsCoeff` of the parameter `l w`.
* `New.Space.IsForm`: `V.IsForm e F` says that `F` is automorphic, bounded, and fixed by the right
  convolution `New.realConv` with `e` over the real points (if `e` is integrable).
* `New.Space.firstMinimum`: the least norm of a nonzero vector of the lattice of a space, cut off at
  `1`; `V.move x` is the space `V` with its adelic frame multiplied by `x`.
* `New.Data.principalForms`, `New.Data.gridLevelForms`: the forms fixed by `D.chosenLevel`, and the
  forms on `Ỹ^i_0` fixed by the deep level, that is, the principal level of
  `D.gridLevelGen = D.piM ^ D.natB`, where `D.piM * star D.piM = D.M` is `M`.
* `New.Data.spaceY`: the hermitian space `Y_j` with its adelic frame, chosen as in
  `New.Data.exists_space_isStd_of_le_and_gram_eq_of_lt`.
* `(l w).HasLargeGap B`: the entries of `l w = 2λ` are distinct, of the parity of `card n - 1`, and
  entries of `λ` with different signs are at least `500 n³ + B` apart; `dsCoeff` is the matrix
  coefficient of the parameter and `dsKernel` its conjugate times the formal degree.

## Relation to the literature

Nonvanishing periods via Poincaré series of deep level and restriction results of Burger–Sarnak type
are known in the literature. Related work: Prasad–Schulze-Pillot, Generalised form of a conjecture
of Jacquet, 2008; Harris, Testing rationality of coherent cohomology of Shimura varieties, 2014;
Muić, Fourier coefficients of automorphic forms and integrable discrete series, 2015.
-/

/-!
## A vanishing criterion through restrictions of deep level forms

The parameter `l` of the forms on `V` has large gaps for `4 A`, and the parameter `l'` of the forms
on `V ⊕ ⟨1⟩` has large gaps for `2 A`, with `8 (card n + 1)² < A`.
-/

section DeepLevelTest

open New MeasureTheory Matrix Finset Fintype Norms.L2Operator ComplexConjugate Space DiscreteSeries
  U

variable {P : Parameters} {D : Data P} (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]
  {s : n → ℤˣ} {V : Space D.E n s} (A : ℕ) {L N : ℕ}

/-- A Lipschitz bound under left translation for the product over the infinite places `w` of the
conjugate matrix coefficients `(l w).dsCoeff`. The parameters `l w` are integer vectors with entries
bounded by `L` and large gaps: entries of `l w / 2` with different signs differ by at least
`500 n³ + 4 A`. If `β` bounds `2000 (card n + L + 1)⁶` and the number `D.f` of infinite places and
`u` is a real point within `δ` of `1`, the values at `u⁻¹ * z` and `z` differ by at most `β² δ`. -/
lemma New.Exchange.norm_prod_conj_dsCoeff_inv_mul_sub_le {β δ : ℝ}
    {l : NumberField.InfinitePlace D.E → HCParam s}
    (h_gap : ∀ w : NumberField.InfinitePlace D.E, (l w).HasLargeGap (4 * A))
    (hl : ∀ (w : NumberField.InfinitePlace D.E) (i : n), |l w i| ≤ L)
    (hβ : 2000 * (card n + L + 1) ^ 6 ≤ β) (hfβ : D.f ≤ β) {u : GInf D.E s} (hu : dist u 1 ≤ δ)
    (z : GInf D.E s) :
    ‖∏ w : NumberField.InfinitePlace D.E, conj ((l w).dsCoeff ((u⁻¹ * z) w)) -
      ∏ w : NumberField.InfinitePlace D.E, conj ((l w).dsCoeff (z w))‖ ≤ β * (β * δ) := by
  -- There are at most `β` factors, each of norm at most `1` and with Lipschitz constant `β`.
  have β_nonneg : 0 ≤ β := hβ.trans' (by positivity)
  have δ_nonneg : 0 ≤ δ := dist_nonneg.trans hu
  let c (g : GInf D.E s) (w : NumberField.InfinitePlace D.E) : ℂ := conj ((l w).dsCoeff (g w))
  have factor_le (w : NumberField.InfinitePlace D.E) : ‖c (u⁻¹ * z) w - c z w‖ ≤ β * δ := by
    have const_le : (100 * (card n + L + 1) ^ 5 : ℝ) ≤ β := hβ.trans' (mod_cast by lia)
    -- `conj (dsCoeff g) = dsCoeff g⁻¹`, and `dsCoeff` is Lipschitz under right translation.
    calc ‖c (u⁻¹ * z) w - c z w‖
      _ = ‖(l w).dsCoeff ((z w)⁻¹ * u w : USign s) - (l w).dsCoeff ((z w)⁻¹ : USign s)‖ := by
        simp_rw [c, ← dsCoeff_inv (h_gap w), Pi.mul_apply, Pi.inv_apply, _root_.mul_inv_rev,
          inv_inv]
      _ ≤ 100 * (card n + L + 1) ^ 5 * ‖(u w : Matrix n n ℂ) - 1‖ :=
        norm_dsCoeff_sub_le (hg := h_gap w) (hl w) _ _
      _ ≤ β * δ := by
        gcongr
        exact (dist_eq_norm _ _).symm.trans_le ((dist_le_pi_dist u 1 w).trans hu)
  have sub_le : ‖c (u⁻¹ * z) - c z‖ ≤ β * δ := (pi_norm_le_iff_of_nonempty _).2 factor_le
  have norm_le_one (g : GInf D.E s) : ‖c g‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonempty _).2 fun w ↦ by simp [c, norm_dsCoeff_le_one (h_gap w)]
  -- `prodMap` is the product map `c ↦ ∏ w, c w`, multilinear of norm `1`.
  let prodMap : ContinuousMultilinearMap ℂ (fun _ : NumberField.InfinitePlace D.E ↦ ℂ) ℂ :=
    .mkPiAlgebra ℂ (NumberField.InfinitePlace D.E) ℂ
  calc ‖prodMap (c (u⁻¹ * z)) - prodMap (c z)‖
    _ ≤ ‖prodMap‖ * D.f * max ‖c (u⁻¹ * z)‖ ‖c z‖ ^ (D.f - 1) * ‖c (u⁻¹ * z) - c z‖ :=
      prodMap.norm_image_sub_le _ _
    _ ≤ ‖prodMap‖ * β * 1 ^ (D.f - 1) * (β * δ) := by
      grw [norm_le_one, norm_le_one, max_self, hfβ, sub_le]
    _ = β * (β * δ) := by simp [prodMap]

variable {n A} {β m : ℝ}

/-- The size conditions of the vanishing criterion for a space of rank `card n` over the field `D.E`
of the data `D`. The exponent `A` dominates the rank, the exponent `N` of a lower bound
`v * β ^ (-N)`, with `v` a volume, for local pairings of matrix coefficients, and the real
dimension; `β` dominates the constants, among them the cusp constant
`cuspConst D.E n D.cyclotomicConductor` and the bound `L` of the parameters; `m` is at least a large
power of `β`; and the generator of the deep level is large against `m` at every infinite place `w`,
with embedding `Φ w`. The radius `m` is a real number, not the number `D.m` of lifts. -/
structure New.Exchange.HasDeepLevelSizes (D : Data P) (n : Type) [Fintype n] (A L N : ℕ)
    (β m : ℝ) : Prop where
  /-- `A` is large against the square of the rank. -/
  rank_sq_lt : 8 * (card n + 1) ^ 2 < A
  /-- `A` exceeds the exponent `N` of the lower bound for the local pairings. -/
  exponent_lt : N < A
  /-- `A` exceeds by `2` or more the real dimension of a space of rank `card n + 1` over `E ⊗ ℝ`. -/
  dim_le : 2 * D.f * (card n + 1) + 2 ≤ A
  /-- `β` bounds the constant of the cusp estimate: `D.M` is the level and `cuspConst` depends on
  the rank and on the number `D.cyclotomicConductor` in the different of `D.E`. -/
  cuspConst_sq_le : D.M * cuspConst D.E n D.cyclotomicConductor ^ 2 ≤ β
  /-- `β` bounds a polynomial in the rank and the bound `L` of the parameters. -/
  rank_pow_le : 2000 * (card n + L + 1) ^ 6 ≤ β
  /-- `β` bounds the number of infinite places. -/
  places_le : D.f ≤ β
  /-- `m` is at least a large power of `β`. -/
  pow_le : β ^ (20 * A * (D.f + 1)) ≤ m
  /-- The level is deep: its generator is large at every infinite place. -/
  pow_le_norm_gridLevelGen : ∀ w : NumberField.InfinitePlace D.E,
    m ^ (3 * card n + 2) ≤ ‖Φ w D.gridLevelGen.val‖

section Sizes
omit [Nonempty n]

section

omit [DecidableEq n]

lemma New.Exchange.HasDeepLevelSizes.sixteen_le
    (h_size : Exchange.HasDeepLevelSizes D n A L N β m) : 16 ≤ β :=
  h_size.rank_pow_le.trans' (mod_cast by lia)

/-- The size conditions for the deep level force the constant `β` to be at most the radius `m`,
which is at least a power of `β`. -/
lemma New.Exchange.HasDeepLevelSizes.beta_le_m (h_size : Exchange.HasDeepLevelSizes D n A L N β m) :
    β ≤ m := by
  have one_le : 1 ≤ β := by linarith [h_size.sixteen_le]
  have hA : N < A := h_size.exponent_lt
  exact (le_self_pow₀ one_le (by lia)).trans h_size.pow_le

/-- The comparison of constants behind `integral_typeKernelMajorant_le`. Of the size conditions for
the deep level it uses `8 (card n + 1)² < A`, `N < A`, `2000 (card n + L + 1)⁶ ≤ β` and
`β ^ (20 A (D.f + 1)) ≤ m`. The left side is the `D.f`-th power of the bound for the local
integrals; it is small against `m`. -/
lemma New.Exchange.HasDeepLevelSizes.pow_places_le_div
    (h_size : Exchange.HasDeepLevelSizes D n A L N β m) :
    (8 * (2000 * (card n + L + 1) ^ 6) ^ (2 * card n ^ 2) * 2 ^ (2 * A)) ^ D.f ≤
      m / (16 * β) / (β ^ N * (2 * β) ^ (3 * A)) ^ D.f := by
  have hA : 8 * (card n + 1) ^ 2 < A := h_size.rank_sq_lt
  have hN : N < A := h_size.exponent_lt
  have hβ₁₆ : 16 ≤ β := h_size.sixteen_le
  have exponent_le : 1 + 2 * card n ^ 2 + 2 * A + (N + 2 * (3 * A)) ≤ 20 * A := by nlinarith
  rw [le_div_iff₀ (by positivity), le_div_iff₀ (by positivity)]
  calc
    _ ≤ (β * β ^ (2 * card n ^ 2) * β ^ (2 * A)) ^ D.f * (β ^ N * (β * β) ^ (3 * A)) ^ D.f *
        (β * β) := by
      gcongr
      exacts [by linarith, h_size.rank_pow_le, by linarith, by linarith]
    _ = β ^ ((1 + 2 * card n ^ 2 + 2 * A + (N + 2 * (3 * A))) * D.f + 2) := by ring
    _ ≤ β ^ (20 * A * (D.f + 1)) :=
      pow_le_pow_right₀ (by linarith) (by nlinarith [Nat.mul_le_mul_right D.f exponent_le])
    _ ≤ m := h_size.pow_le

end

/-- Under the size conditions `HasDeepLevelSizes`, `D.M * κ²` is at most `β ≤ m`. Here
`κ = cuspConst D.E n D.cyclotomicConductor` is the constant of the cusp estimate
`IsForm.norm_le_of_firstMinimum_lt`. So where `V.firstMinimum` is at least the threshold
`(m⁻² / (D.M κ²)) ^ card n` of that estimate, `m² ≤ m ^ (3 card n + 2) * V.firstMinimum`. -/
lemma New.Exchange.HasDeepLevelSizes.sq_le_pow_mul_firstMinimum
    (h_size : Exchange.HasDeepLevelSizes D n A L N β m)
    (h_large : (m⁻¹ ^ 2 / (D.M * cuspConst D.E n D.cyclotomicConductor ^ 2)) ^ card n ≤
      V.firstMinimum) :
    m ^ 2 ≤ m ^ (3 * card n + 2) * V.firstMinimum := by
  have m_ge : 16 ≤ m := h_size.sixteen_le.trans h_size.beta_le_m
  have const_le : D.M * cuspConst D.E n D.cyclotomicConductor ^ 2 ≤ m :=
    h_size.cuspConst_sq_le.trans h_size.beta_le_m
  have const_pos : 0 < D.M * cuspConst D.E n D.cyclotomicConductor ^ 2 := by
    grw [← one_le_cuspConst]
    simp [NeZero.pos]
  calc m ^ 2
    _ = m ^ (3 * card n + 2) * (m⁻¹ ^ 2 / m) ^ card n := by
      rw [show m⁻¹ ^ 2 / m = (m ^ 3)⁻¹ by field, inv_pow, ← pow_mul, pow_add]
      field
    _ ≤ m ^ (3 * card n + 2) * V.firstMinimum := by grw [← h_large, const_le]

end Sizes

/-- The function `u ↦ ∏_w deg(l w) (2 / ‖u w‖) ^ (2 A)` on the real points, with `deg` the formal
degree. It is a majorant of `‖typeKernel l s‖` that keeps half of its decay when the parameters
`l w` have large gaps for `4 A`. -/
noncomputable def New.Exchange.typeKernelMajorant (l : NumberField.InfinitePlace D.E → HCParam s)
    (A : ℕ) (u : GInf D.E s) : ℝ :=
  ∏ w : NumberField.InfinitePlace D.E, (l w).formalDegree * (2 / ‖(u w).val.val‖) ^ (2 * A)

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let the parameters `l w` have large gaps for `4 A` and entries bounded by `L`. Then
`typeKernelMajorant l A`, the product over the infinite places `w` of the formal degree of `l w`
times `(2 / ‖u w‖) ^ (2 A)`, is integrable over the real points `u`. Under the size conditions for
the deep level, where `β` dominates the constants, `β ^ N` is the loss in the local pairings and
`m` is at least a large power of `β`, its integral is at most
`m / (16 β) / (β ^ N (2 β) ^ (3 A)) ^ D.f`, with `D.f` the number of infinite places. -/
lemma New.Exchange.integral_typeKernelMajorant_le {l : NumberField.InfinitePlace D.E → HCParam s}
    (h_size : HasDeepLevelSizes D n A L N β m)
    (h_gap : ∀ w : NumberField.InfinitePlace D.E, (l w).HasLargeGap (4 * A))
    (hl : ∀ (w : NumberField.InfinitePlace D.E) (i : n), |l w i| ≤ L) :
    Integrable (typeKernelMajorant l A) ∧
    ∫ u : GInf D.E s, typeKernelMajorant l A u ≤
      m / (16 * β) / (β ^ N * (2 * β) ^ (3 * A)) ^ D.f := by
  have hA : 8 * (card n + 1) ^ 2 < A := h_size.rank_sq_lt
  let factor (w : NumberField.InfinitePlace D.E) (g : USign s) : ℝ :=
    (l w).formalDegree * (2 / ‖(g : Matrix n n ℂ)‖) ^ (2 * A)
  let C : ℝ := 8 * (2000 * (card n + L + 1) ^ 6) ^ (2 * card n ^ 2) * 2 ^ (2 * A)
  have tail (w : NumberField.InfinitePlace D.E) :
      Integrable (factor w) ∧ ∫ g : USign s, factor w g ≤ C :=
    integral_tail_le (hg := h_gap w) (hl w) (2 * A) (by lia)
  refine ⟨.fintype_prod fun w ↦ (tail w).left, ?_⟩
  calc ∫ u : GInf D.E s, ∏ w, factor w (u w)
    _ = ∏ w, ∫ g : USign s, factor w g := integral_fintype_prod_volume_eq_prod factor
    _ ≤ C ^ D.f := (prod_le_prod₀ (fun w _ ↦ by positivity [formalDegree_pos (h_gap w)])
      fun w _ ↦ (tail w).right).trans_eq (by rw [prod_const, card_univ])
    _ ≤ m / (16 * β) / (β ^ N * (2 * β) ^ (3 * A)) ^ D.f := h_size.pow_places_le_div

/-- The kernel `typeKernel l s` varies slowly. Let the parameters `l w` have large gaps for `4 A`
and entries bounded by `L`, and assume the size conditions `HasDeepLevelSizes D n A L N β m`: `β`
dominates the constants and `m` is at least a large power of `β`. For a real point `u` within
`m⁻¹ ^ 2` of `1`, the values of the kernel at `u⁻¹ * z` and `z` differ by at most `β / m` times the
sum of the values at these points of `typeKernelMajorant l A`, the function
`u ↦ ∏ w, deg(l w) (2 / ‖u w‖) ^ (2 A)` with `deg` the formal degree. -/
lemma New.Exchange.norm_typeKernel_inv_mul_sub_le {l : NumberField.InfinitePlace D.E → HCParam s}
    (h_size : HasDeepLevelSizes D n A L N β m)
    (h_gap : ∀ w : NumberField.InfinitePlace D.E, (l w).HasLargeGap (4 * A))
    (hl : ∀ (w : NumberField.InfinitePlace D.E) (i : n), |l w i| ≤ L)
    {u : GInf D.E s} (hu : dist u 1 ≤ m⁻¹ ^ 2) (z : GInf D.E s) :
    ‖typeKernel l s (u⁻¹ * z) - typeKernel l s z‖ ≤
      (typeKernelMajorant l A (u⁻¹ * z) + typeKernelMajorant l A z) * (β / m) := by
  have hβ₁₆ : 16 ≤ β := h_size.sixteen_le
  have m_ge : 16 ≤ m := hβ₁₆.trans h_size.beta_le_m
  let deg : ℝ := ∏ w, (l w).formalDegree
  let ψ (g : GInf D.E s) : ℂ := ∏ w, conj ((l w).dsCoeff (g w))
  let decay (g : GInf D.E s) : ℝ := ∏ w, (2 / ‖(g w : Matrix n n ℂ)‖) ^ (2 * A)
  have deg_pos : 0 < deg := prod_pos fun w _ ↦ formalDegree_pos (h_gap w)
  have kernel_eq (g : GInf D.E s) : typeKernel l s g = deg * ψ g := by
    simp [typeKernel, dsKernel, deg, ψ, prod_mul_distrib]
  have majorant_eq (g : GInf D.E s) : typeKernelMajorant l A g = deg * decay g := prod_mul_distrib
  have ψ_le (g : GInf D.E s) : ‖ψ g‖ ≤ decay g ^ 2 :=
    calc ‖ψ g‖
      _ = ∏ w, ‖(l w).dsCoeff (g w)‖ := by simp only [ψ, norm_prod, RCLike.norm_conj]
      _ ≤ ∏ w, (2 / ‖(g w : Matrix n n ℂ)‖) ^ (4 * A) := by
        gcongr with w
        exact norm_dsCoeff_le_pow (h_gap w) le_add_self (g w)
      _ = decay g ^ 2 := by simp only [decay, ← prod_pow, ← pow_mul]; ring_nf
  have lipschitz : ‖ψ (u⁻¹ * z) - ψ z‖ ≤ β * (β * m⁻¹ ^ 2) :=
    norm_prod_conj_dsCoeff_inv_mul_sub_le n A h_gap hl h_size.rank_pow_le h_size.places_le hu z
  have ψ_sub_le : ‖ψ (u⁻¹ * z) - ψ z‖ ≤ (decay (u⁻¹ * z) + decay z) * (β / m) := by
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
    calc ‖ψ (u⁻¹ * z) - ψ z‖ ^ 2
      _ ≤ β * (β * m⁻¹ ^ 2) * (decay (u⁻¹ * z) ^ 2 + decay z ^ 2) := by
        rw [sq ‖_‖]
        nth_grw 1 [lipschitz, norm_sub_le, ψ_le, ψ_le]
      _ ≤ β * (β * m⁻¹ ^ 2) * (decay (u⁻¹ * z) + decay z) ^ 2 := by
        gcongr
        exact pow_add_pow_le (by positivity) (by positivity) two_ne_zero
      _ = ((decay (u⁻¹ * z) + decay z) * (β / m)) ^ 2 := by ring
  calc ‖typeKernel l s (u⁻¹ * z) - typeKernel l s z‖
    _ = deg * ‖ψ (u⁻¹ * z) - ψ z‖ := by
      rw [kernel_eq, kernel_eq, ← mul_sub, norm_mul, Complex.norm_of_nonneg deg_pos.le]
    _ ≤ deg * ((decay (u⁻¹ * z) + decay z) * (β / m)) := by gcongr
    _ = _ := by rw [majorant_eq, majorant_eq, ← mul_add, mul_assoc]

/-- High in a cusp a form is at most half of its bound. Assume the size conditions
`HasDeepLevelSizes D n A L N β m`, and let the parameters `l w` have large gaps for `4 A` and
entries bounded by `L`. Let `y` be a form on `V` of type `l`, right invariant under the principal
congruence subgroup of level `D.M` (`HasLevel`) and bounded by `S`. Where the first minimum of the
lattice of `V.move x` is below the threshold of the cusp estimate, whose constant is
`cuspConst D.E n D.cyclotomicConductor`, we have `‖y x‖ ≤ S / 2`. -/
lemma New.Exchange.norm_le_half_of_firstMinimum_lt {l : NumberField.InfinitePlace D.E → HCParam s}
    (h_size : HasDeepLevelSizes D n A L N β m)
    (h_gap : ∀ w : NumberField.InfinitePlace D.E, (l w).HasLargeGap (4 * A))
    (hl : ∀ (w : NumberField.InfinitePlace D.E) (i : n), |l w i| ≤ L)
    {y : G D.E s → ℂ} (hy : V.IsForm (typeKernel l s) y)
    (hy_level : HasLevel y (principalLevel n D.M))
    {S : ℝ} (hS : ∀ g : G D.E s, ‖y g‖ ≤ S) {x : G D.E s}
    (h_small : (V.move x).firstMinimum <
      (m⁻¹ ^ 2 / (D.M * cuspConst D.E n D.cyclotomicConductor ^ 2)) ^ card n) :
    ‖y x‖ ≤ S / 2 := by
  -- By cuspidality (`IsForm.norm_le_of_firstMinimum_lt`) it is enough to bound
  -- `‖y (x * (u, 1)) - y x‖` by `S / 2` for real points `u` within `m⁻¹ ^ 2` of `1`.
  have hβ₁₆ : 16 ≤ β := h_size.sixteen_le
  have m_ge : 16 ≤ m := hβ₁₆.trans h_size.beta_le_m
  have S_nonneg : 0 ≤ S := (norm_nonneg (y x)).trans (hS x)
  have cusp : IsCuspKernel (4 * A) (typeKernel l s) := isCuspKernel_typeKernel h_gap
  let major : GInf D.E s → ℝ := typeKernelMajorant l A
  obtain ⟨major_int, integral_major⟩ := integral_typeKernelMajorant_le h_size h_gap hl
  have integral_le : ∫ u, major u ≤ m / (16 * β) :=
    integral_major.trans (div_le_self (by positivity) (by bound))
  refine hy.norm_le_of_firstMinimum_lt cusp P.conductor_mem_differentIdeal NeZero.out hy_level
    (δ := m⁻¹ ^ 2) (by positivity) (by bound) h_small fun u hu ↦ ?_
  have integrand_le (z : GInf D.E s) :
      ‖typeKernel l s (u⁻¹ * z) * y (x * (u, 1) * (u⁻¹ * z, 1)) -
        typeKernel l s z * y (x * (z, 1))‖ ≤ (major (u⁻¹ * z) + major z) * (β / m) * S := by
    rw [show x * (u, 1) * (u⁻¹ * z, 1) = x * (z, 1) by simp [mul_assoc], ← sub_mul]
    exact norm_mul_le_of_le (norm_typeKernel_inv_mul_sub_le h_size h_gap hl hu z) (hS _)
  -- Write both values of `y` as convolutions with its kernel, and integrate.
  have conv_int (g : G D.E s) : Integrable fun z ↦ typeKernel l s z * y (g * (z, 1)) :=
    hy.isBoundedMeasurable.integrable_mul_comp cusp.integrable _
  have shift_int : Integrable fun z ↦ major (u⁻¹ * z) := major_int.comp_mul_left u⁻¹
  calc ‖y (x * (u, 1)) - y x‖
    _ = ‖∫ z, typeKernel l s (u⁻¹ * z) * y (x * (u, 1) * (u⁻¹ * z, 1)) -
        typeKernel l s z * y (x * (z, 1))‖ := by
      nth_rw 1 2 [← hy.realConv_eq cusp.integrable]
      rw [realConv, realConv, ← integral_mul_left_eq_self _ u⁻¹,
        ← integral_sub ((conv_int _).comp_mul_left _) (conv_int _)]
    _ ≤ ∫ z, (major (u⁻¹ * z) + major z) * (β / m) * S :=
      norm_integral_le_of_norm_le (((shift_int.add major_int).mul_const _).mul_const _)
        (.of_forall integrand_le)
    _ = 2 * (∫ z, major z) * (β / m) * S := by
      rw [integral_mul_const, integral_mul_const, integral_add shift_int major_int,
        integral_mul_left_eq_self major, two_mul]
    _ ≤ 2 * (m / (16 * β)) * (β / m) * S := by gcongr
    _ = S / 8 := by field
    _ ≤ S / 2 := by linarith

omit [Nonempty n] in
/-- Let `y` be a function on the group of `V` whose Petersson product with `x ↦ φ ((x ⊕ 1) ω)` is
zero for all forms `φ` on `Z = V ⊕ ⟨1⟩` of type `l'` and level `K`, where the parameters `l' w` have
large gaps for `2 A` and `8 (card n + 1)² < A`. Fix a real point `α` and put `c g = ∏ w, conj ((l'
w).dsCoeff ((α w)⁻¹ * g w * ω w))`, the translated coefficient for `l'`. Then the Poincaré series
over the rational points `γ` of `Z` of `c` times the indicator of `K` at the finite part
(`poincareKernel`), centred at `x ⊕ 1`, has zero period against `y` over the quotient of the group
of `V` by its rational points (`quotMeasure`). -/
lemma New.Exchange.poincare_period_translatedCoeff_eq_zero
    {l' : NumberField.InfinitePlace D.E → HCParam (s ⊕ᵥ (1 : Unit → ℤˣ))}
    (hA : 8 * (card n + 1) ^ 2 < A)
    (h_gap' : ∀ w : NumberField.InfinitePlace D.E, (l' w).HasLargeGap (2 * A))
    {ω : GInf D.E (s ⊕ᵥ (1 : Unit → ℤˣ))} {y : G D.E s → ℂ}
    {K : Subgroup (Gf D.E (n ⊕ Unit))} [IsLevel K]
    (h_orth : ∀ φ ∈ levelSpace
        ((V.sum (signedSpace D.E (1 : Unit → ℤˣ))).formRep (typeKernel l' (s ⊕ᵥ 1))) K,
      V.petersson y (fun x : G D.E s ↦ φ (G.sum (x, 1) * (ω, 1))) = 0)
    (x : G D.E s) (α : GInf D.E (s ⊕ᵥ (1 : Unit → ℤˣ))) :
    ∫ h : G D.E s, ∑' γ : (V.sum (signedSpace D.E (1 : Unit → ℤˣ))).Γ,
      poincareKernel (translatedCoeff l' α ω) K
        ((G.inlLine D.E s x)⁻¹ * γ * G.inlLine D.E s h) * y h ∂V.quotMeasure = 0 := by
  -- The Poincaré series is, up to the nonzero formal degrees, the conjugate of the value at
  -- `G.sum (h, 1) * (ω, 1)` of a form `Q` of type `l'` and level `K` on `Z`; the series converges
  -- to a form by the decay of the coefficient.
  let Z : Space D.E (n ⊕ Unit) (s ⊕ᵥ 1) := V.sum (signedSpace D.E 1)
  let term (γ : Z.Γ) (h : G D.E s) : ℂ :=
    poincareKernel (translatedCoeff l' α ω) K ((G.inlLine D.E s x)⁻¹ * γ.val * G.inlLine D.E s h)
  let deg : ℂ := ∏ w, (l' w).formalDegree
  have deg_ne : deg ≠ 0 := by simp [deg, prod_ne_zero_iff, (formalDegree_pos (h_gap' _)).ne']
  have h_order : 8 * card (n ⊕ Unit) ^ 2 < 2 * A := by grind [card_sum, card_unit]
  let centreInv : G D.E (s ⊕ᵥ 1) := (G.sum (x, 1) * (α, 1))⁻¹
  obtain ⟨Q, hQ⟩ : ∃ Q : levelSpace (Z.formRep (typeKernel l' (s ⊕ᵥ 1))) K,
      ∀ g : G D.E (s ⊕ᵥ 1), conj (Q.val g) = ∑' γ : Z.Γ,
        typeKernel l' (s ⊕ᵥ 1) (centreInv * γ * g).1 * Set.indicator K 1 (centreInv * γ * g).2 :=
    Z.exists_kernel_form h_order (isCuspKernel_typeKernel h_gap') centreInv K
  have conj_Q (h : G D.E s) :
      conj (Q.val (G.sum (h, 1) * (ω, 1))) = deg * ∑' γ : Z.Γ, term γ h := by
    rw [hQ, ← tsum_mul_left]
    congr! 2 with γ
    simp [term, deg, centreInv, poincareKernel, G.inlLine, translatedCoeff, typeKernel, dsKernel,
      prod_mul_distrib, mul_assoc]
  refine (mul_eq_zero_iff_left deg_ne).1 ?_
  calc deg * ∫ h : G D.E s, ∑' γ : Z.Γ, term γ h * y h ∂V.quotMeasure
    _ = V.petersson (fun h : G D.E s ↦ Q.val (G.sum (h, 1) * (ω, 1))) y := by
      simp_rw [petersson, conj_Q, tsum_mul_right, ← integral_const_mul, mul_assoc]
    _ = 0 := by rw [← conj_petersson, h_orth Q.val Q.prop, map_zero]

omit [Nonempty n] in
/-- Assume the size conditions `HasDeepLevelSizes D n A L N β m` and large gaps for `2 A` of the
parameters `l' w`. Let `y` be automorphic on `V`, of the deep level
`principalLevel n D.gridLevelGen`, and bounded by `S`. Let it also be orthogonal to
`x ↦ φ ((x ⊕ 1) ω)` for all forms `φ` on `V ⊕ ⟨1⟩` of type `l'` and deep level. For a real point
`α`, the translated coefficient `translatedCoeff l' α ω g` is
`∏ w, conj ((l' w).dsCoeff ((α w)⁻¹ * g w * ω w))`. Where
`m² ≤ m ^ (3 card n + 2) * (V.move x).firstMinimum`, its restriction along the block embedding
`inl s 1` is integrable. The convolution of this restriction with `y` at `x` is then at most
`10 S / m` times `sliceConst A α ω = ∏ w, (2 (‖α w‖ ‖ω w‖)²) ^ A * 16 ^ A * v`, with `v` the volume
of the unit ball around `1` in `U(s)`. -/
lemma New.Exchange.norm_realConv_translatedCoeff_le
    {l' : NumberField.InfinitePlace D.E → HCParam (s ⊕ᵥ (1 : Unit → ℤˣ))}
    (h_size : HasDeepLevelSizes D n A L N β m)
    (h_gap' : ∀ w : NumberField.InfinitePlace D.E, (l' w).HasLargeGap (2 * A))
    {ω : GInf D.E (s ⊕ᵥ (1 : Unit → ℤˣ))} {y : G D.E s → ℂ} (hy : V.IsAutomorphic y)
    (hy_level : HasLevel y (principalLevel n D.gridLevelGen))
    (h_orth : ∀ φ ∈ levelSpace
        ((V.sum (signedSpace D.E (1 : Unit → ℤˣ))).formRep (typeKernel l' (s ⊕ᵥ 1)))
        (principalLevel (n ⊕ Unit) D.gridLevelGen),
      V.petersson y (fun x : G D.E s ↦ φ (G.sum (x, 1) * (ω, 1))) = 0)
    {S : ℝ} (hS : ∀ g : G D.E s, ‖y g‖ ≤ S) {x : G D.E s}
    (h_large : m ^ 2 ≤ m ^ (3 * card n + 2) * (V.move x).firstMinimum)
    (α : GInf D.E (s ⊕ᵥ (1 : Unit → ℤˣ))) :
    Integrable (fun r : GInf D.E s ↦ translatedCoeff l' α ω (inl s 1 ∘ r)) ∧
    ‖realConv (fun r : GInf D.E s ↦ translatedCoeff l' α ω (inl s 1 ∘ r)) y x‖ ≤
      sliceConst A α ω * S * (10 / m) := by
  -- The period of the Poincaré series of the coefficient against `y` is `0` by `h_orth`, so its
  -- identity term is as small as the error in `norm_poincare_period_sub_le`.
  have m_ge : 16 ≤ m := h_size.sixteen_le.trans h_size.beta_le_m
  let vol : ℝ := volume.real (principalLevel n D.gridLevelGen : Set (Gf D.E n))
  let slice (r : GInf D.E s) : ℂ := translatedCoeff l' α ω (inl s 1 ∘ r)
  have key : Integrable slice ∧
      ‖0 - vol • realConv slice y x‖ ≤ vol * sliceConst A α ω * S * (10 / m) := by
    rw [← poincare_period_translatedCoeff_eq_zero h_size.rank_sq_lt h_gap' h_orth x α]
    exact norm_poincare_period_sub_le hy hS Fact.out hy_level h_size.pow_le_norm_gridLevelGen
      h_size.dim_le
      h_size.rank_sq_lt h_gap' (by positivity) x h_large (h_size.places_le.trans h_size.beta_le_m)
      (by linarith) ω α
  -- The positive volume `vol` of the level cancels.
  simpa [slice, vol, measureReal_pos_of_isLevel, abs_of_pos, mul_assoc] using key

/-- Let the parameter `l` have large gaps for `4 * A` (`HasLargeGap`), let `16 ≤ β` and
`‖ω‖ ^ 2 ≤ β`. Then the norm of the kernel `dsKernel l r`, times
`(2 (‖inl s 1 r * ω‖ ‖ω‖)²) ^ A * 16 ^ A`, is at most
`l.formalDegree * (2 / ‖r‖) ^ (2 A) * (2 β) ^ (3 A)`. Here `inl s 1 r = diag(r, 1)`. -/
lemma New.Exchange.norm_dsKernel_mul_pow_le {l : HCParam s} (h_gap : l.HasLargeGap (4 * A))
    (hβ : 16 ≤ β) {ω : USign (s ⊕ᵥ (1 : Unit → ℤˣ))}
    (hω : ‖(ω : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ^ 2 ≤ β) (r : USign s) :
    ‖dsKernel l r‖ *
      ((2 * (‖((inl s 1 r * ω : USign (s ⊕ᵥ 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ *
        ‖(ω : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖) ^ 2) ^ A * 16 ^ A) ≤
      l.formalDegree * (2 / ‖(r : Matrix n n ℂ)‖) ^ (2 * A) * (2 * β) ^ (3 * A) := by
  set ρ : ℝ := ‖(r : Matrix n n ℂ)‖
  set σ : ℝ := ‖(ω : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖
  have ρ_pos : 0 < ρ := one_pos.trans_le (one_le_norm r)
  have hdeg : 0 < l.formalDegree := formalDegree_pos h_gap
  have kernel_le : ‖dsKernel l r‖ ≤ l.formalDegree * (2 / ρ) ^ (4 * A) := by
    grw [← norm_dsCoeff_le_pow h_gap le_add_self r]
    simp [dsKernel, abs_of_pos hdeg]
  have norm_le :
      ‖((inl s 1 r * ω : USign (s ⊕ᵥ 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ≤ ρ * σ :=
    (norm_mul_le _ _).trans_eq (by simp [ρ, σ, one_le_norm])
  calc
    _ ≤ l.formalDegree * (2 / ρ) ^ (4 * A) * ((2 * (ρ * β) ^ 2) ^ A * β ^ A) := by
      grw [kernel_le, norm_le, mul_assoc ρ, ← sq, hω, hβ]
    _ = l.formalDegree * (2 / ρ) ^ (2 * A) * (2 * β) ^ (3 * A) := by
      simp only [pow_mul, mul_assoc, ← mul_pow]
      congr 2
      field

/-- Let the parameters `l w` have large gaps for `4 A`, so that their formal degrees are positive,
and let `ω` be a real point, with a component `ω w` in `U(s ⊕ᵥ 1)` at each infinite place `w`. Pair
the conjugate of the kernel `typeKernel l s`, divided by the value of the kernel at `1`, with the
restriction along `inl s 1 : r ↦ r ⊕ 1` of
`translatedCoeff l' ω ω g = ∏ w, conj ((l' w).dsCoeff ((ω w)⁻¹ * g w * ω w))`. This integral over
the real points is the product over `w` of the local pairings of the matrix coefficients. -/
lemma New.Exchange.integral_translatedCoeff_mul_eq_prod
    {l : NumberField.InfinitePlace D.E → HCParam s}
    {l' : NumberField.InfinitePlace D.E → HCParam (s ⊕ᵥ (1 : Unit → ℤˣ))}
    (h_gap : ∀ w : NumberField.InfinitePlace D.E, (l w).HasLargeGap (4 * A))
    (ω : GInf D.E (s ⊕ᵥ (1 : Unit → ℤˣ))) :
    ∫ z : GInf D.E s,
        translatedCoeff l' ω ω (inl s 1 ∘ z) * (conj (typeKernel l s z) / typeKernel l s 1) =
      ∏ w : NumberField.InfinitePlace D.E, ∫ r : USign s, (l w).dsCoeff r *
        conj ((l' w).dsCoeff ((ω w)⁻¹ * inl s 1 r * ω w : USign (s ⊕ᵥ 1))) := by
  rw [← integral_fintype_prod_volume_eq_prod]
  refine integral_congr_ae (.of_forall fun z ↦ ?_)
  -- The formal degrees in `dsKernel` are positive and cancel in the quotient.
  simp [translatedCoeff, field, typeKernel, dsKernel, prod_mul_distrib, prod_eq_zero_iff, ne_of_gt,
    formalDegree_pos (h_gap _)]

omit [Nonempty n] in
/-- Right translation of the point by the real point `u` moves `u ⊕ 1` into the left argument of
the translated coefficient. -/
lemma New.Exchange.realConv_translatedCoeff_mul
    (l' : NumberField.InfinitePlace D.E → HCParam (s ⊕ᵥ (1 : Unit → ℤˣ)))
    (α ω : GInf D.E (s ⊕ᵥ (1 : Unit → ℤˣ))) (y : G D.E s → ℂ) (x : G D.E s) (u : GInf D.E s) :
    realConv (fun r : GInf D.E s ↦ translatedCoeff l' α ω (inl s 1 ∘ r)) y (x * (u, 1)) =
      realConv (fun r : GInf D.E s ↦ translatedCoeff l' (inl s 1 ∘ u * α) ω (inl s 1 ∘ r)) y x := by
  rw [realConv, realConv, ← integral_mul_left_eq_self (fun z ↦ _ * y (x * (z, 1))) u]
  -- The products stay in the group, where `(inl u)⁻¹ * inl u` cancels.
  simp [translatedCoeff, mul_assoc, -Subgroup.coe_mul, -MulMemClass.coe_mul]

/-- Let `y` be a form on `V` of type `l` and of the deep level `D.gridLevelGen`, bounded by `S` and
orthogonal to `x ↦ φ ((x ⊕ 1) ω)` for all forms `φ` on `V ⊕ ⟨1⟩` of type `l'` and deep level. Assume
the size conditions for the deep level, large gaps of the parameters, bounded entries of `l`, that
`ω` is not large (`hω`) and that the local pairings of the coefficients for `l` and `l'` are bounded
from below (`h_pair`). Where the first minimum of `V.move x` is at least the threshold of the cusp
estimate, whose constant `cuspConst D.E n D.cyclotomicConductor` depends on the rank and on a number
in the different of `D.E`, we have `‖y x‖ ≤ S / 2`. -/
lemma New.Exchange.norm_le_half_of_le_firstMinimum {l : NumberField.InfinitePlace D.E → HCParam s}
    {l' : NumberField.InfinitePlace D.E → HCParam (s ⊕ᵥ (1 : Unit → ℤˣ))}
    (h_size : HasDeepLevelSizes D n A L N β m)
    (h_gap : ∀ w : NumberField.InfinitePlace D.E, (l w).HasLargeGap (4 * A))
    (h_gap' : ∀ w : NumberField.InfinitePlace D.E, (l' w).HasLargeGap (2 * A))
    (hl : ∀ (w : NumberField.InfinitePlace D.E) (i : n), |l w i| ≤ L)
    {ω : GInf D.E (s ⊕ᵥ (1 : Unit → ℤˣ))}
    (hω : ∀ w : NumberField.InfinitePlace D.E,
      ‖(ω w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ^ 2 ≤ β)
    (h_pair : ∀ w : NumberField.InfinitePlace D.E,
      volume.real {r : USign s | ‖(r : Matrix n n ℂ) - 1‖ ≤ 1} ≤ β ^ N *
        ‖∫ r : USign s, (l w).dsCoeff r *
          conj ((l' w).dsCoeff ((ω w)⁻¹ * inl s 1 r * ω w : USign (s ⊕ᵥ 1)))‖)
    {y : G D.E s → ℂ} (hy : V.IsForm (typeKernel l s) y)
    (hy_level : HasLevel y (principalLevel n D.gridLevelGen))
    (h_orth : ∀ φ ∈ levelSpace
        ((V.sum (signedSpace D.E (1 : Unit → ℤˣ))).formRep (typeKernel l' (s ⊕ᵥ 1)))
        (principalLevel (n ⊕ Unit) D.gridLevelGen),
      V.petersson y (fun x : G D.E s ↦ φ (G.sum (x, 1) * (ω, 1))) = 0)
    {S : ℝ} (hS : ∀ g : G D.E s, ‖y g‖ ≤ S) {x : G D.E s}
    (h_large : (m⁻¹ ^ 2 / (D.M * cuspConst D.E n D.cyclotomicConductor ^ 2)) ^ card n ≤
      (V.move x).firstMinimum) :
    ‖y x‖ ≤ S / 2 := by
  -- Average the small convolution of `norm_realConv_translatedCoeff_le` over the kernel of `y`.
  -- The result is `η * y x`, where `η` is the product of the local pairings of `h_pair`.
  set v : ℝ := volume.real {r : USign s | ‖(r : Matrix n n ℂ) - 1‖ ≤ 1}
  have hβ₁₆ : 16 ≤ β := h_size.sixteen_le
  have m_ge : 16 ≤ m := hβ₁₆.trans h_size.beta_le_m
  have S_nonneg : 0 ≤ S := (norm_nonneg (y x)).trans (hS x)
  have v_pos : 0 < v := ENNReal.toReal_pos (measure_sublevel_ne_zero volume (by simp))
    (measure_ball_ne_top_of_isProperMap volume .monoidHom_id 1)
  have cusp : IsCuspKernel (4 * A) (typeKernel l s) := isCuspKernel_typeKernel h_gap
  obtain ⟨major_int, integral_major⟩ := integral_typeKernelMajorant_le h_size h_gap hl
  let ψ (α : GInf D.E (s ⊕ᵥ 1)) (r : GInf D.E s) : ℂ := translatedCoeff l' α ω (inl s 1 ∘ r)
  let growth (α : GInf D.E (s ⊕ᵥ (1 : Unit → ℤˣ))) (w : NumberField.InfinitePlace D.E) : ℝ :=
    (2 * (‖(α w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ *
      ‖(ω w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖) ^ 2) ^ A
  have conv_bound (α : GInf D.E (s ⊕ᵥ 1)) : Integrable (ψ α) ∧
      ‖realConv (ψ α) y x‖ ≤ (∏ w, growth α w * (16 ^ A * v)) * S * (10 / m) :=
    norm_realConv_translatedCoeff_le h_size h_gap' hy.toIsAutomorphic hy_level h_orth hS
      (h_size.sq_le_pow_mul_firstMinimum h_large) α
  -- Fubini, then the rank one formula `realConv_translate`.
  let η : ℂ := ∫ z, ψ ω z * (conj (typeKernel l s z) / typeKernel l s 1)
  have average : ∫ u, typeKernel l s u * realConv (ψ ω) y (x * (u, 1)) = η * y x := by
    rw [integral_mul_realConv hy.isBoundedMeasurable (conv_bound ω).1 cusp.integrable _]
    simp_rw [hy.realConv_translate cusp, ← mul_assoc, integral_mul_const, η]
  have η_ge : (v / β ^ N) ^ D.f ≤ ‖η‖ := by
    simp only [η, ψ, integral_translatedCoeff_mul_eq_prod h_gap, norm_prod]
    grw [← fun w ↦ (div_le_iff₀' (by bound)).2 (h_pair w)]
    simp [div_pow]
  have integrand_le (u : GInf D.E s) : ‖typeKernel l s u * realConv (ψ ω) y (x * (u, 1))‖ ≤
      typeKernelMajorant l A u * (((2 * β) ^ (3 * A) * v) ^ D.f * S * 10 / m) := by
    calc ‖typeKernel l s u * realConv (ψ ω) y (x * (u, 1))‖
      _ ≤ (∏ w, ‖dsKernel (l w) (u w)‖ * (growth (inl s 1 ∘ u * ω) w * 16 ^ A) * v) *
          (S * (10 / m)) := by
        grw [norm_mul, realConv_translatedCoeff_mul, (conv_bound (inl s 1 ∘ u * ω)).2]
        simp [typeKernel, prod_mul_distrib, mul_assoc]
      _ ≤ (∏ w, (l w).formalDegree * (2 / ‖(u w : Matrix n n ℂ)‖) ^ (2 * A) *
          (2 * β) ^ (3 * A) * v) * (S * (10 / m)) := by
        gcongr (∏ w, ?_ * _) * _ with w
        exact norm_dsKernel_mul_pow_le (h_gap w) hβ₁₆ (hω w) (u w)
      _ = typeKernelMajorant l A u * (((2 * β) ^ (3 * A) * v) ^ D.f * S * 10 / m) := by
        simp only [typeKernelMajorant, prod_mul_distrib, prod_const, card_univ]
        ring
  -- Integrate: the constants of `η_ge`, `integrand_le` and `integral_major` cancel.
  have average_le : (v / β ^ N) ^ D.f * ‖y x‖ ≤
      m / (16 * β) / (β ^ N * (2 * β) ^ (3 * A)) ^ D.f *
        (((2 * β) ^ (3 * A) * v) ^ D.f * S * 10 / m) := by
    grw [η_ge, ← norm_mul, ← average, ← integral_major, ← integral_mul_const]
    exact norm_integral_le_of_norm_le (major_int.mul_const _) (.of_forall integrand_le)
  have norm_le : ‖y x‖ * 16 * β ≤ S * 10 := by simpa [field, mul_pow, div_pow] using average_le
  grw [← hβ₁₆] at norm_le
  linarith

/-- The vanishing criterion at a real point `ω` of `GInf D.E (s ⊕ᵥ 1)`. Assume the following. First,
the size conditions `HasDeepLevelSizes D n A L N β m`. Second, large gaps of the parameters: entries
of `l w / 2` with different signs differ by at least `500 n³ + 4 A`, and likewise for `l'` with
`n + 1` and `2 A`. Third, entries of `l` bounded by `L`. Fourth, `ω` is not large (`hω`). Fifth, at
each infinite place the coefficient for `l` pairs nontrivially with the restriction of the
coefficient for `l'` conjugated by `ω`, with the explicit lower bound `h_pair`. Then a form `y` on
`V` of type `l` and level `D.chosenLevel` vanishes if it is orthogonal to `x ↦ φ ((x ⊕ 1) ω)` for
every form `φ` on `V ⊕ ⟨1⟩` of type `l'` and of the deep level
`principalLevel (n ⊕ Unit) D.gridLevelGen`. -/
theorem New.Exchange.eq_zero_of_petersson_translate_eq_zero
    {l : NumberField.InfinitePlace D.E → HCParam s}
    {l' : NumberField.InfinitePlace D.E → HCParam (s ⊕ᵥ (1 : Unit → ℤˣ))}
    (h_size : HasDeepLevelSizes D n A L N β m)
    (h_gap : ∀ w : NumberField.InfinitePlace D.E, (l w).HasLargeGap (4 * A))
    (h_gap' : ∀ w : NumberField.InfinitePlace D.E, (l' w).HasLargeGap (2 * A))
    (hl : ∀ (w : NumberField.InfinitePlace D.E) (i : n), |l w i| ≤ L)
    {ω : GInf D.E (s ⊕ᵥ (1 : Unit → ℤˣ))}
    (hω : ∀ w : NumberField.InfinitePlace D.E,
      ‖(ω w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ^ 2 ≤ β)
    (h_pair : ∀ w : NumberField.InfinitePlace D.E,
      volume.real {r : USign s | ‖(r : Matrix n n ℂ) - 1‖ ≤ 1} ≤ β ^ N *
        ‖∫ r : USign s, (l w).dsCoeff r *
          conj ((l' w).dsCoeff ((ω w)⁻¹ * inl s 1 r * ω w : USign (s ⊕ᵥ 1)))‖)
    {y : G D.E s → ℂ} (hy : V.IsForm (typeKernel l s) y) (hy_level : HasLevel y D.chosenLevel)
    (h_orth : ∀ φ ∈ levelSpace
        ((V.sum (signedSpace D.E (1 : Unit → ℤˣ))).formRep (typeKernel l' (s ⊕ᵥ 1)))
        (principalLevel (n ⊕ Unit) D.gridLevelGen),
      V.petersson y (fun x : G D.E s ↦ φ (G.sum (x, 1) * (ω, 1))) = 0) :
    y = 0 := by
  -- By `le_of_halving` it is enough to halve every bound `S` of `‖y‖`.
  -- Where `(V.move x).firstMinimum` is large this follows from the orthogonality, by unfolding a
  -- Poincaré series; where it is small, from cuspidality and the fact that `y` varies slowly.
  have level (a : NumberField.RingOfIntegers D.E) (ha : D.piM ∣ a) :
      HasLevel y (principalLevel n a) :=
    fun k hk ↦ hy_level k (D.principalLevel_le_chosenLevel ha hk)
  have half (S : ℝ) (hS : ∀ g : G D.E s, ‖y g‖ ≤ S) (x : G D.E s) : ‖y x‖ ≤ S / 2 := by
    obtain h_large | h_small := le_or_gt
      ((m⁻¹ ^ 2 / (D.M * cuspConst D.E n D.cyclotomicConductor ^ 2)) ^ card n)
      (V.move x).firstMinimum
    · exact norm_le_half_of_le_firstMinimum h_size h_gap h_gap' hl hω h_pair hy
        (level D.gridLevelGen D.piM_dvd_gridLevelGen) h_orth hS h_large
    · exact norm_le_half_of_firstMinimum_lt h_size h_gap hl hy
        (level D.M (Dvd.intro _ D.piM_mul_star)) hS h_small
  obtain ⟨C, hC⟩ := hy.bounded
  exact funext fun x ↦
    norm_le_zero_iff.1 (le_of_halving hC le_rfl (fun S _ hS x ↦ .inl (half S hS x)) x)

variable (n A β) in
/-- Let `l` be the parameters of the forms on `V` and `l'` those of the forms on `V ⊕ ⟨1⟩`, whose
signs `t` are `s ⊕ᵥ 1`. Assume large gaps for `4 A` of `l w` and for `2 A` of `l' w`, `|l w i| ≤ L`,
the size conditions of `HasDeepLevelSizes`, and that at each infinite place some point `ω` with
`‖ω‖ ^ 2 ≤ β` makes the pairing for `l` and `l'` not small (`h_place`). Then there is a real point
`g` such that a form `y` on `V` of type `l` and level `D.chosenLevel` vanishes if it is orthogonal
to `x ↦ φ ((x ⊕ 1) g)` for all forms `φ` on `V ⊕ ⟨1⟩` of type `l'` and of the deep level
`D.gridLevelGen`. -/
lemma New.Exchange.exists_forall_eq_zero_of_petersson_restrict_eq_zero {t : n ⊕ Unit → ℤˣ}
    {l : NumberField.InfinitePlace D.E → HCParam s}
    {l' : NumberField.InfinitePlace D.E → HCParam t} {h_signs : s ⊕ᵥ 1 = t}
    (h_gap : ∀ w : NumberField.InfinitePlace D.E, (l w).HasLargeGap (4 * A))
    (h_gap' : ∀ w : NumberField.InfinitePlace D.E, (l' w).HasLargeGap (2 * A))
    (h_entry : ∀ (w : NumberField.InfinitePlace D.E) (i : n), |l w i| ≤ L)
    (h_rank : 8 * (card n + 1) ^ 2 < A) (h_exponent : N < A)
    (h_dim : 2 * D.f * (card n + 1) + 2 ≤ A)
    (h_cusp : D.M * cuspConst D.E n D.cyclotomicConductor ^ 2 ≤ β)
    (h_rank_pow : 2000 * (card n + L + 1) ^ 6 ≤ β) (h_places : D.f ≤ β)
    (h_pow_le : β ^ (20 * A * (D.f + 1)) ≤ m)
    (h_level : ∀ w : NumberField.InfinitePlace D.E,
      m ^ (3 * card n + 2) ≤ ‖Φ w D.gridLevelGen.val‖)
    (h_place : ∀ w : NumberField.InfinitePlace D.E, ∃ ω : USign (s ⊕ᵥ (1 : Unit → ℤˣ)),
      ‖(ω : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ^ 2 ≤ β ∧
      volume.real {r : USign s | ‖(r : Matrix n n ℂ) - 1‖ ≤ 1} ≤ β ^ N *
        ‖∫ r : USign s, (l w).dsCoeff r *
          conj ((toHCParam (s ⊕ᵥ 1) (l' w)).dsCoeff
            (ω⁻¹ * inl s 1 r * ω : USign (s ⊕ᵥ (1 : Unit → ℤˣ))))‖) :
    ∃ g : GInf D.E t, ∀ y ∈ levelSpace (V.formRep (typeKernel l s)) D.chosenLevel,
      (∀ φ ∈ levelSpace
          (((V.sum (signedSpace D.E 1)).reindex (.refl (n ⊕ Unit)) h_signs).formRep
            (typeKernel l' t))
          (principalLevel (n ⊕ Unit) D.gridLevelGen),
        V.petersson y
          (fun x : G D.E s ↦ φ (G.reindex (.refl (n ⊕ Unit)) h_signs (.sum (x, 1)) * (g, 1))) = 0) →
      y.val = 0 := by
  subst h_signs
  choose ω hω_norm h_pair using h_place
  exact ⟨ω, fun y hy_level h_orth ↦ eq_zero_of_petersson_translate_eq_zero
    ⟨h_rank, h_exponent, h_dim, h_cusp, h_rank_pow, h_places, h_pow_le, h_level⟩ h_gap h_gap'
    h_entry hω_norm h_pair y.prop (mem_levelSpace_formRep_iff.1 hy_level) h_orth⟩

end DeepLevelTest

/-! ## Forms of level `J_M` on Y₀ -/

section RowsReached

open Matrix.Norms.L2Operator

/-- At every infinite place the generator `D.gridLevelGen = D.piM ^ D.natB` of the deep level
has modulus `√D.M ^ D.natB`. -/
lemma New.Data.norm_gridLevelGen {P : Parameters} (D : Data P)
    (w : NumberField.InfinitePlace D.E) : ‖Φ w D.gridLevelGen.val‖ = √D.M ^ D.natB := by
  have h_sq : ‖Φ w D.piM‖ ^ 2 = D.M := by
    simpa [sq] using congrArg (fun a : NumberField.RingOfIntegers D.E ↦ ‖Φ w a‖) D.piM_mul_star
  simp [← h_sq]

/-- There is a real point `g` of `GInf D.E (D.gridSigns true 0 0 0)`, the archimedean unitary group
on the index type `D.Y 0 ⊕ Unit`, the index type of `Ỹ^0_0 = Y₀ ⊕ ⟨1⟩`, with the following property.
Let `y` lie in `D.principalForms`, so it is a form on `Y₀ = D.spaceY 0` of type `D.paramW` and level
`J_M = D.chosenLevel`. Then `y` vanishes if it is Petersson orthogonal to `x ↦ φ ((x ⊕ 1) g)` for
all `φ` in `D.gridLevelForms 0`, the forms on `Ỹ^0_0` of type `D.gridKernel true 0 0 true` and of
the principal level of `D.gridLevelGen`. -/
lemma New.Data.exists_eq_zero_of_orthogonal_gridLevelForms {P : Parameters} (D : Data P) :
    ∃ g : GInf (n := D.Y 0 ⊕ Unit) D.E (D.gridSigns true 0 0 0),
      ∀ y ∈ D.principalForms (D.spaceY 0),
      (∀ φ ∈ D.gridLevelForms 0, (D.spaceY 0).petersson y.val
        (fun x : New.G D.E (D.signsY 0) ↦
          φ (G.reindex (.refl (D.Y 0 ⊕ Unit)) D.gridSigns_true_zero.symm (.sum (x, 1)) * (g, 1))) =
            0) →
      y.val = 0 := by
  -- At each infinite place `IsSteep.exists_volume_le_mul_norm_integral_dsCoeff` gives a point at
  -- which the pairing of the matrix coefficients of the two types is bounded from below. Then
  -- `Exchange.exists_forall_eq_zero_of_petersson_restrict_eq_zero` applies with the sizes `h_sizes`
  -- below.
  obtain ⟨e, h_steep⟩ : ∃ e : D.InitIndex 0 ⊕ Fin (2 * D.ϱ + 2) ≃ D.GridIndex false 0 0,
      ∀ w : D.Φ, DiscreteSeries.IsSteep (D.gridParam false 0 0 0 w) (D.liftWeight 0 w) e :=
    D.exists_isSteep false
  obtain ⟨e', h_steep'⟩ : ∃ e' : D.InitIndex 0 ⊕ Fin (2 * D.ϱ + 2 + 1) ≃ D.GridIndex true 0 0,
      ∀ w : D.Φ, DiscreteSeries.IsSteep (D.gridParam true 0 0 0 w) (D.liftWeight 0 w) e' :=
    D.exists_isSteep true
  have h_mono : Monotone fun k : ℕ ↦ √D.M ^ k := pow_right_mono₀ D.le_of_hasLogBound
  have abs_param_le (z : Bool) (w : D.Φ) (x : D.GridIndex z 0 0) :
      |D.gridParam z 0 0 0 w x| ≤ ⌈20 * D.b⌉₊ :=
    D.abs_gridParam_le (z := z) w bot_le bot_le x
  -- These bounds for `β` and for the two ranks are found as instances by `D.le_of_hasLogBound` and
  -- its versions for natural numbers, which compare quantities by their logarithmic bounds.
  have β_lb : D.HasLogLower (√D.M ^ ⌈D.x⌉₊) (3 * (20 * D.logB / 2)) :=
    D.hasLogLower_of_le (G := √D.M ^ 3) (h_mono D.nat_le_of_hasLogBound)
  have rank_ub : D.HasLogUpper (Fintype.card (D.Y 0)) (5 * D.logX + 3) :=
    D.hasLogUpper_of_le_of_nonneg (F := D.r) (by simp [D.card_rowIndex]) (Nat.cast_nonneg _)
  have rank_ub' : D.HasLogUpper (Fintype.card (D.Y 0 ⊕ Unit)) (max (5 * D.logX + 3) 0 + 1) :=
    D.hasLogUpper_of_le_of_nonneg (F := D.r + 1) (by simp [D.card_rowIndex]) (Nat.cast_nonneg _)
  let β : ℝ := √D.M ^ ⌈D.x⌉₊
  let A : ℕ := D.r ^ 4
  let N : ℕ := 20 * (Fintype.card (D.Y 0 ⊕ Unit) + Fintype.card (D.Y 0)) ^ 2
  have h_sizes : Exchange.HasDeepLevelSizes D (D.Y 0) A ⌈20 * D.b⌉₊ N β
      (β ^ (20 * A * (D.f + 1))) :=
    { rank_sq_lt := D.nat_lt_of_hasLogBound
      exponent_lt := D.nat_lt_of_hasLogBound
      dim_le := D.nat_le_of_hasLogBound
      cuspConst_sq_le := by rw [cuspConst]; exact D.le_of_hasLogBound
      rank_pow_le := D.le_of_hasLogBound
      places_le := D.le_of_hasLogBound
      pow_le := le_rfl
      pow_le_norm_gridLevelGen := fun w ↦ by
        rw [D.norm_gridLevelGen w, ← pow_mul, ← pow_mul]
        exact h_mono D.nat_le_of_hasLogBound }
  refine Exchange.exists_forall_eq_zero_of_petersson_restrict_eq_zero (D.Y 0) A β
    (h_gap := fun w ↦ (D.hasGap_signsY_paramW w).mono D.nat_le_of_hasLogBound)
    (h_gap' := fun w ↦ (D.hasGap_gridParam w true 0 0 0).neg.mono D.nat_le_of_hasLogBound)
    (h_entry := abs_param_le false) h_sizes.rank_sq_lt h_sizes.exponent_lt h_sizes.dim_le
      h_sizes.cuspConst_sq_le
    h_sizes.rank_pow_le h_sizes.places_le h_sizes.pow_le h_sizes.pow_le_norm_gridLevelGen fun w ↦ ?_
  -- `gridSigns_true_zero` writes the signs of `Ỹ^0_0` as those of `Y₀` followed by `1`; along this
  -- equality the facts on `D.gridParam true 0 0 0 w` are facts on `l'`.
  let l' : HCParam (Sum.elim (D.signsY 0) (1 : Unit → ℤˣ)) := D.gridParam true 0 0 0 w
  obtain ⟨h_steep_l', h_gap'⟩ : DiscreteSeries.IsSteep l' (D.liftWeight 0 w) e' ∧ l'.HasGap D.gap :=
    D.gridSigns_true_zero ▸ ⟨h_steep' w, D.hasGap_gridParam w true 0 0 0⟩
  have h_steep_neg : DiscreteSeries.IsSteep (-(-l')) (D.liftWeight 0 w) e' := by rwa [neg_neg]
  have h_card_bound : (Fintype.card (D.Y 0 ⊕ Unit) : ℝ) ^ 4 *
      (6 * D.liftWeight 0 w) ^ (2 * (2 * D.ϱ + 2) + 2) ≤ β := by
    grw [show (Fintype.card (D.Y 0 ⊕ Unit) : ℝ) ≤ √D.M from D.le_of_hasLogBound,
      show (6 * D.liftWeight 0 w : ℝ) ≤ √D.M from D.le_of_hasLogBound, ← pow_add]
    exact h_mono D.nat_le_of_hasLogBound
  have h_log : 10 ^ 30 * (((Fintype.card (D.Y 0 ⊕ Unit) : ℝ) + Fintype.card (D.Y 0)) ^ 2 *
      Real.log β) ^ 3 ≤ (D.r ^ 7 : ℕ) := by
    rw [Real.log_pow]
    exact D.le_of_hasLogBound
  have h_even : Even (2 * D.ϱ + 2) := by grind
  exact (h_steep w).exists_volume_le_mul_norm_integral_dsCoeff h_even h_steep_neg
    (hB := D.le_of_hasLogBound)
    (hl := (D.hasGap_signsY_paramW w).mono D.nat_le_of_hasLogBound)
    (hl' := h_gap'.neg.mono D.nat_le_of_hasLogBound)
    (hL := abs_param_le false w) (hL' := fun x ↦ (abs_neg _).trans_le (abs_param_le true w x))
    (hβ := D.le_of_hasLogBound) (hn := D.le_of_hasLogBound) h_card_bound h_log

end RowsReached
