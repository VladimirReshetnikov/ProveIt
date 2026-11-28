import Lib.Adelic.AutomorphicForms.RealConvolution
import Lib.Adelic.TraceFormula.Stretch
import Lib.Adelic.TraceFormula.TestFunction

/-!
# The sum of a majorant over the rational points

For a test function `φ` on the finite points, the sum of `|φ(y_fin)| ‖y_∞‖ ^ (-8 n² - 1)` over all
`y = g⁻¹ γ x`, `γ` rational, is bounded by a constant times `Ht(x) ^ (4 f n²)`, uniformly in `g`.
Here `‖y_∞‖` is the product of the operator norms at the infinite places, `Ht(x)` is `V.height x`,
`f` is the number of infinite places, and in such exponents `n` stands for the dimension `card n`.
The translates `g⁻¹ γ x B` of a small box `B` are disjoint, the majorant at the base point of each
is at most a bounded multiple of its values there, and it is integrable.

* `New.tsum_mul_measure_le_lintegral`: a sum over disjoint translates against an integral.
* `New.Space.exists_levelBox_disjoint`: the translates of the box `New.levelBox` are disjoint.
* `New.Space.exists_tsum_majorant_le`: the bound for the sum of `New.Space.majorant`.

Notions from other files:
* `G E s = GInf E s × Gf E n` is the adelic unitary group: one copy of the real unitary group
  `USign s` of the signs `s` at each infinite place, times the finite adelic group `Gf E n`.
* `stdLevel E n` is the subgroup of integral points of `Gf E n`; a level is an open subgroup of it.
* For `V : Space E n s`, a hermitian space on `Eⁿ` with a base lattice `V.baseLattice`, `U V.J` is
  the group of rational points and `V.ratEmbed` its embedding into `G E s`.
* `V.height x` is the inverse of the first minimum, cut off at `1`, of the lattice of `V` at `x`,
  that is, of the base lattice of the translate `V.move x`.
* `TestFunction (Gf E n)` is the Schwartz–Bruhat space of `Gf E n` (locally constant functions of
  compact support).

## Relation to the literature

Known result: Sum over the rational points of a majorant of a test function, bounded by a power of
the height. This is the standard estimate for the kernel of a trace formula.
-/

open NumberField MeasureTheory Matrix Fintype Norms.L2Operator ENNReal

noncomputable section

namespace New

/-- If the translates `y i * B` are disjoint and `f x ≤ c * f (x * z)` for `z ∈ B`, then the sum of
the values `f (y i)`, times the measure of `B`, is at most `c` times the integral of `f`. -/
lemma tsum_mul_measure_le_lintegral {G I : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [Countable I] {y : I → G} {B : Set G}
    (hB : MeasurableSet B) (h_disjoint : ∀ i j : I, ∀ z ∈ B, ∀ z' ∈ B, y i * z = y j * z' → i = j)
    {f : G → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ⊤) (h_le : ∀ x : G, ∀ z ∈ B, f x ≤ c * f (x * z)) :
    (∑' i : I, f (y i)) * μ B ≤ c * ∫⁻ x : G, f x ∂μ := by
  let S (i : I) : Set G := (fun x ↦ (y i)⁻¹ * x) ⁻¹' B
  have hS (i : I) : MeasurableSet (S i) := measurable_const_mul _ hB
  have hS_disjoint : Pairwise (Function.onFun Disjoint S) := fun i j hij ↦
    Set.disjoint_left.2 fun x hi hj ↦ hij (h_disjoint i j _ hi _ hj (by simp))
  have h_term (i : I) : f (y i) * μ B ≤ ∫⁻ x in S i, c * f x ∂μ := by
    rw [← measure_preimage_mul μ (y i)⁻¹ B, ← setLIntegral_const]
    exact setLIntegral_mono' (hS i) fun x hx ↦ by simpa using h_le (y i) _ hx
  calc (∑' i : I, f (y i)) * μ B ≤ ∑' i : I, ∫⁻ x in S i, c * f x ∂μ :=
        ENNReal.tsum_mul_right.ge.trans (ENNReal.tsum_le_tsum h_term)
    _ = ∫⁻ x in ⋃ i : I, S i, c * f x ∂μ := (lintegral_iUnion hS hS_disjoint _).symm
    _ ≤ ∫⁻ x, c * f x ∂μ := setLIntegral_le_lintegral _ _
    _ = c * ∫⁻ x, f x ∂μ := lintegral_const_mul' _ _ hc

/-- A test function `φ` on the finite adelic unitary group is invariant on both sides under some
level `J`, that is, under some open subgroup of the integral points. -/
lemma TestFunction.exists_isLevel_invariant {E n : Type} [Field E] [NumberField E] [IsCMField E]
    [Fintype n] [DecidableEq n] (φ : TestFunction (Gf E n)) : ∃ J : Subgroup (Gf E n), IsLevel J ∧
      (∀ u ∈ J, ∀ y : Gf E n, φ.1 (u⁻¹ * y) = φ.1 y) ∧
      ∀ u ∈ J, ∀ y : Gf E n, φ.1 (y * u) = φ.1 y := by
  have h_fixed : ∀ᶠ p in nhds (1 : Gf E n × Gf E n), TestFunction.translate p φ = φ :=
    IsSmoothRep.eventually_fixed φ
  have h_left : ∀ᶠ u in nhds (1 : Gf E n), TestFunction.translate (u, 1) φ = φ :=
    ((Continuous.prodMk_left 1).tendsto 1).eventually h_fixed
  have h_right : ∀ᶠ u in nhds (1 : Gf E n), TestFunction.translate (1, u) φ = φ :=
    ((Continuous.prodMk_right 1).tendsto 1).eventually h_fixed
  obtain ⟨M, hM, h_sub⟩ : ∃ M : ℕ, M ≠ 0 ∧ (principalLevel n (M : 𝓞 E) : Set (Gf E n)) ⊆
      {u : Gf E n | TestFunction.translate (u, 1) φ = φ ∧ TestFunction.translate (1, u) φ = φ} :=
    exists_principalLevel_subset (h_left.and h_right)
  refine ⟨principalLevel n M,
    ⟨principalLevel_le_stdLevel, isOpen_principalLevel (Nat.cast_ne_zero.2 hM)⟩,
    fun u hu y ↦ ?_, fun u hu y ↦ ?_⟩
  · obtain ⟨hu_left, -⟩ := h_sub hu
    conv_rhs => rw [← hu_left, TestFunction.translate_apply, mul_one]
  · obtain ⟨-, hu_right⟩ := h_sub hu
    conv_rhs => rw [← hu_right, TestFunction.translate_apply, inv_one, one_mul]

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] [Nonempty n] {s : n → ℤˣ}

/-- An element of a real unitary group within distance `1` of the identity has norm at most `2`. -/
lemma norm_le_two_of_norm_sub_one_le {z : USign s} (hz : ‖z.val.val - 1‖ ≤ 1) : ‖z.val.val‖ ≤ 2 :=
  calc ‖z.val.val‖ ≤ ‖(1 : Matrix n n ℂ)‖ + ‖z.val.val - 1‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ 1 + 1 := add_le_add norm_one.le hz
    _ = 2 := one_add_one_eq_two

/-- The quotient of two elements of a real unitary group within distance `δ ≤ 1` of the identity is
within distance `4 δ` of it. -/
lemma norm_mul_inv_sub_one_le {z z' : USign s} {δ : ℝ} (hδ : δ ≤ 1) (hz : ‖z.val.val - 1‖ ≤ δ)
    (hz' : ‖z'.val.val - 1‖ ≤ δ) : ‖(z' * z⁻¹).val.val - 1‖ ≤ 4 * δ := by
  have h_factor : (z' * z⁻¹).val.val - 1 =
      ((z'.val.val - 1) - (z.val.val - 1)) * z⁻¹.val.val := by simp [sub_mul]
  have h_inv : ‖z⁻¹.val.val‖ ≤ 2 :=
    (U.norm_inv z).trans_le (norm_le_two_of_norm_sub_one_le (hz.trans hδ))
  calc ‖(z' * z⁻¹).val.val - 1‖ ≤ (δ + δ) * 2 := by
        rw [h_factor]
        exact norm_mul_le_of_le (norm_sub_le_of_le hz' hz) h_inv
    _ = 4 * δ := by ring

variable (E s) in
/-- The box of the points whose real components are within distance `δ` of the identity and whose
finite component lies in `J`. -/
def levelBox (δ : ℝ) (J : Subgroup (Gf E n)) : Set (G E s) :=
  (Set.univ.pi fun _ : InfinitePlace E ↦ {z : USign s | ‖z.val.val - 1‖ ≤ δ}) ×ˢ
    (J : Set (Gf E n))

omit [Nonempty n] in
/-- A point lies in the box `levelBox E s δ J` if and only if each real component is within
distance `δ` of the identity and the finite component lies in `J`. -/
lemma mem_levelBox {δ : ℝ} {J : Subgroup (Gf E n)} {z : G E s} :
    z ∈ levelBox E s δ J ↔ (∀ w : InfinitePlace E, ‖(z.1 w).val.val - 1‖ ≤ δ) ∧ z.2 ∈ J := by
  simp only [levelBox, Set.mem_prod, Set.mem_univ_pi, Set.mem_ofPred_eq, SetLike.mem_coe]

omit [Nonempty n] in
/-- The box `levelBox E s δ J` is measurable if the subgroup `J` is open. -/
lemma measurableSet_levelBox (δ : ℝ) {J : Subgroup (Gf E n)} (hJ : IsOpen (J : Set (Gf E n))) :
    MeasurableSet (levelBox E s δ J) :=
  (MeasurableSet.univ_pi fun _ ↦
    (isClosed_le (by fun_prop) continuous_const).measurableSet).prod hJ.measurableSet

variable (s) in
/-- For an open subgroup `J` of the finite points there is a positive constant `v` such that, for
every `D ≥ 1`, the volume of the box `levelBox E s D⁻¹ J` is at least `v (12 D) ^ (-2 n² f)`, with
`f` the number of infinite places. -/
lemma exists_le_mul_volume_levelBox {J : Subgroup (Gf E n)} (hJ : IsOpen (J : Set (Gf E n))) :
    ∃ v ≠ (0 : ℝ≥0∞), ∀ D ≥ (1 : ℝ), v ≤ ENNReal.ofReal
      ((12 * D) ^ (2 * card n ^ 2 * Core.numInfPlaces E)) * volume (levelBox E s D⁻¹ J) := by
  -- The set `‖z‖ ≤ 2` is covered by `(12 D) ^ (2 n²)` translates of the set `‖z - 1‖ ≤ D⁻¹`.
  let bigVol : ℝ≥0∞ := volume {z : USign s | ‖z.val.val‖ ≤ 2}
  have h_bigVol : bigVol ≠ 0 :=
    measure_sublevel_ne_zero volume (norm_one.trans_lt one_lt_two) (by fun_prop)
  refine ⟨bigVol ^ Core.numInfPlaces E * volume (J : Set (Gf E n)),
    mul_ne_zero (pow_ne_zero _ h_bigVol) (hJ.measure_ne_zero _ ⟨1, J.one_mem⟩), fun D hD ↦ ?_⟩
  set count : ℝ≥0∞ := .ofReal ((12 * D) ^ (2 * card n ^ 2))
  set smallVol : ℝ≥0∞ := volume {z : USign s | ‖z.val.val - 1‖ ≤ D⁻¹}
  have h_cover : bigVol ≤ count * smallVol := by
    simpa using DiscreteSeries.measure_ball_le_covering volume
      (MonoidHom.id (USign s)) 1 hD one_le_two (K := 12 * D) (by linarith)
  have h_box : volume (levelBox E s D⁻¹ J) =
      smallVol ^ Core.numInfPlaces E * volume (J : Set (Gf E n)) := by
    simp [levelBox, Measure.volume_eq_prod, volume_pi_pi, smallVol]
  calc bigVol ^ Core.numInfPlaces E * volume (J : Set (Gf E n))
      ≤ (count * smallVol) ^ Core.numInfPlaces E * volume (J : Set (Gf E n)) := by gcongr
    _ = ENNReal.ofReal ((12 * D) ^ (2 * card n ^ 2 * Core.numInfPlaces E)) *
          volume (levelBox E s D⁻¹ J) := by
      rw [h_box, pow_mul, ENNReal.ofReal_pow (by positivity), mul_pow, mul_assoc]

namespace Space

variable (V : Space E n s)

instance : Countable (GL n E) := Units.val_injective.countable

omit [Nonempty n] in
/-- If, for a natural number `b`, the element `x⁻¹ γ x` is integral at the finite places and within
distance `((b + 1) Ht(x)²)⁻¹` of the identity at the infinite places, then the rational point `γ`
fixes every vector of length at most `b Ht(x)` of the lattice of `V.move x`, the translate of `V`
by `x`. Here `Ht(x) = V.height x` is the inverse of the first minimum of that lattice, this minimum
being cut off at `1` from above, so that `Ht(x) ≥ 1`. -/
lemma mulVec_eq_self_of_norm_sub_one_le {x : G E s} {γ : U V.J} {b : ℕ}
    (h_int : (x⁻¹ * V.ratEmbed γ * x).2 ∈ stdLevel E n)
    (h_close : ∀ w : InfinitePlace E,
      ‖((x⁻¹ * V.ratEmbed γ * x).1 w).val.val - 1‖ ≤ ((b + 1) * V.height x ^ 2)⁻¹)
    {y : n → E} (hy : y ∈ (V.move x).latticeBall (b * V.height x)) :
    γ.val.val *ᵥ y = y := by
  -- Otherwise `γ y - y` would be a nonzero lattice vector shorter than the first minimum.
  obtain ⟨hy_mem, hy_norm⟩ := hy
  set t : G E s := x⁻¹ * V.ratEmbed γ * x
  have h_arch (w : InfinitePlace E) :
      ‖(t.adeleMatrix - 1).map fun a : 𝔸 E ↦ a.1 w‖ ≤ ((b + 1) * V.height x ^ 2)⁻¹ := by
    convert h_close w
    ext i j
    rcases eq_or_ne i j with rfl | hij <;> simp [*]
  -- The factor `1` here and below is the common denominator that `mem_and_norm_le_of_vecAtPoint`
  -- allows for the entries of the matrix.
  have h_fin (i j : n) : ((1 : ℕ) : 𝔸f E) * ((t.adeleMatrix - 1) i j).2 ∈ Ô E := by
    rw [Nat.cast_one, one_mul]
    refine sub_mem (mem_stdLevel.1 h_int i j) ?_
    rcases eq_or_ne i j with rfl | hij <;> simp [one_mem, zero_mem, *]
  have h_coords : (V.move x).vecAtPoint (γ.val.val *ᵥ y - y) =
      1 • (t.adeleMatrix - 1) *ᵥ (V.move x).vecAtPoint y := by
    rw [one_smul, sub_mulVec, one_mulVec, map_sub, vecAtPoint_move_mulVec]
  obtain ⟨h_mem_of_integral, h_norm⟩ :=
    (V.move x).mem_and_norm_le_of_vecAtPoint _ (V.move x) y (t.adeleMatrix - 1) 1 h_arch h_coords
  have h_mem : γ.val.val *ᵥ y - y ∈ (V.move x).baseLattice := h_mem_of_integral h_fin hy_mem
  by_contra h_ne
  refine (firstMinimum_le h_mem (sub_ne_zero.2 h_ne)).not_gt ?_
  have h_height : 0 < V.height x := V.height_pos x
  rw [Nat.cast_one, one_mul] at h_norm
  calc ‖(V.move x).archCoords (γ.val.val *ᵥ y - y)‖
      ≤ ((b + 1) * V.height x ^ 2)⁻¹ * (b * V.height x) := h_norm.trans (by gcongr)
    _ < (V.height x)⁻¹ := by field_simp; exact lt_add_one _
    _ = (V.move x).firstMinimum := by rw [Space.height, inv_inv]

omit [Nonempty n] in
/-- There is a constant `c ≥ 1` such that a rational point `γ` is trivial if `x⁻¹ γ x` is integral
at the finite places (lies in `stdLevel E n`) and within distance `(c Ht(x)²)⁻¹` of the identity at
the infinite places. Here `Ht(x) = V.height x ≥ 1` is the inverse of the first minimum, cut off at
`1` from above, of the lattice of `V` at `x`. -/
theorem exists_eq_one_of_norm_sub_one_le : ∃ c ≥ (1 : ℝ), ∀ (x : G E s) (γ : U V.J),
    (x⁻¹ * V.ratEmbed γ * x).2 ∈ stdLevel E n →
    (∀ w : InfinitePlace E,
      ‖((x⁻¹ * V.ratEmbed γ * x).1 w).val.val - 1‖ ≤ (c * V.height x ^ 2)⁻¹) → γ = 1 := by
  -- `γ` fixes a basis of `Eⁿ` consisting of short lattice vectors at `x`.
  obtain ⟨b, h_short⟩ := V.exists_short_basis_matrix
  refine ⟨b + 1, le_add_of_nonneg_left b.cast_nonneg, fun x γ h_int h_close ↦ ?_⟩
  obtain ⟨Y, hY⟩ : ∃ Y : GL n E, ∀ j : n,
      Y.val.col j ∈ (V.move x).latticeBall (b * V.height x) := h_short x
  have h_mul : γ.val.val * Y.val = 1 * Y.val := ext_col fun j ↦ by
    rw [one_mul]
    exact V.mulVec_eq_self_of_norm_sub_one_le h_int h_close (hY j)
  exact Subtype.ext (Units.ext (Y.mul_left_inj.1 h_mul))

/-- Let `J` be a subgroup of the integral finite points. There is `c ≥ 1` such that, for all adelic
points `g`, `x` and for the box `B` of points within distance `δ = (c Ht(x)²)⁻¹` of the identity at
the infinite places and in `J` at the finite ones (`levelBox E s δ J`, with `Ht(x) = V.height x`),
the translates `g⁻¹ γ x B` by the rational points `γ` are disjoint. -/
theorem exists_levelBox_disjoint {J : Subgroup (Gf E n)} (hJ : J ≤ stdLevel E n) :
    ∃ c ≥ (1 : ℝ), ∀ (g x : G E s) (γ γ' : U V.J),
      ∀ z ∈ levelBox E s (c * V.height x ^ 2)⁻¹ J, ∀ z' ∈ levelBox E s (c * V.height x ^ 2)⁻¹ J,
      g⁻¹ * V.ratEmbed γ * x * z = g⁻¹ * V.ratEmbed γ' * x * z' → γ = γ' := by
  -- The quotient `γ'⁻¹ γ` is conjugate to `z' z⁻¹`, which is integral and close to the identity.
  obtain ⟨c, hc, h_one⟩ := V.exists_eq_one_of_norm_sub_one_le
  refine ⟨4 * c, by linarith, fun g x γ γ' z hz z' hz' h_eq ↦ ?_⟩
  obtain ⟨hz_inf, hz_fin⟩ := mem_levelBox.1 hz
  obtain ⟨hz'_inf, hz'_fin⟩ := mem_levelBox.1 hz'
  have h_quot : x⁻¹ * V.ratEmbed (γ'⁻¹ * γ) * x = z' * z⁻¹ :=
    calc x⁻¹ * V.ratEmbed (γ'⁻¹ * γ) * x
        = (g⁻¹ * V.ratEmbed γ' * x)⁻¹ * (g⁻¹ * V.ratEmbed γ * x * z) * z⁻¹ := by
          simp [mul_assoc]
      _ = z' * z⁻¹ := by rw [h_eq, inv_mul_cancel_left]
  have h_radius : (4 * c * V.height x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀
    (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (V.one_le_height x)))
  have h_int : (z' * z⁻¹).2 ∈ stdLevel E n := hJ (J.mul_mem hz'_fin (J.inv_mem hz_fin))
  have h_close (w : InfinitePlace E) :
      ‖((z' * z⁻¹).1 w).val.val - 1‖ ≤ (c * V.height x ^ 2)⁻¹ :=
    (norm_mul_inv_sub_one_le h_radius (hz_inf w) (hz'_inf w)).trans_eq (by ring)
  rw [← h_quot] at h_int h_close
  exact (inv_mul_eq_one.1 (h_one x (γ'⁻¹ * γ) h_int h_close)).symm

/-- The majorant `|φ(y_fin)| ‖y_∞‖ ^ (-A)`, where `‖y_∞‖` is the product of the operator norms at
the infinite places. -/
def majorant (φ : Gf E n → ℂ) (A : ℕ) (y : G E s) : ℝ :=
  ‖φ y.2‖ * ((∏ w : InfinitePlace E, ‖(y.1 w).val.val‖) ^ A)⁻¹

-- Keeps definitional checks from unfolding the finite products.
seal Finset.prod in
/-- If `φ` is invariant on the right under `J`, then the majorant of exponent `A` grows at most by
the factor `2 ^ (f A)`, with `f` the number of infinite places, when it is evaluated at `y` instead
of `y * z`, for `z` in a box `levelBox E s δ J` with `δ ≤ 1` (real components within distance `δ` of
the identity, finite component in `J`). -/
lemma majorant_le_mul_majorant_mul {φ : Gf E n → ℂ} {J : Subgroup (Gf E n)}
    (h_invariant : ∀ u ∈ J, ∀ y : Gf E n, φ (y * u) = φ y) (A : ℕ) {δ : ℝ} (hδ : δ ≤ 1) (y : G E s)
    {z : G E s} (hz : z ∈ levelBox E s δ J) :
    majorant φ A y ≤ (2 ^ Core.numInfPlaces E) ^ A * majorant φ A (y * z) := by
  obtain ⟨hz_inf, hz_fin⟩ := mem_levelBox.1 hz
  set p : ℝ := ∏ w : InfinitePlace E, ‖(y.1 w).val.val‖
  set q : ℝ := ∏ w : InfinitePlace E, ‖((y * z).1 w).val.val‖
  have h_norm : q ≤ 2 ^ Core.numInfPlaces E * p :=
    calc q ≤ ∏ w : InfinitePlace E, ‖(y.1 w).val.val‖ * 2 :=
          Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun w _ ↦
            norm_mul_le_of_le le_rfl (norm_le_two_of_norm_sub_one_le ((hz_inf w).trans hδ))
      _ = 2 ^ Core.numInfPlaces E * p := by simp [Finset.prod_mul_distrib, mul_comm, p]
  have hq_pos : 0 < q := one_pos.trans_le (le_prod_opNorm _).1
  have hp_pos : 0 < p := one_pos.trans_le (le_prod_opNorm _).1
  have h_inv : (p ^ A)⁻¹ ≤ (2 ^ Core.numInfPlaces E) ^ A * (q ^ A)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity), ← mul_pow, mul_comm]
    gcongr
  calc majorant φ A y ≤ ‖φ y.2‖ * ((2 ^ Core.numInfPlaces E) ^ A * (q ^ A)⁻¹) :=
        mul_le_mul_of_nonneg_left h_inv (norm_nonneg _)
    _ = (2 ^ Core.numInfPlaces E) ^ A * majorant φ A (y * z) := by
        rw [majorant, Prod.snd_mul, h_invariant _ hz_fin, mul_left_comm]

-- Sealed so that definitional checks do not unfold the products over the infinite places.
seal Finset.univ in
/-- The majorant `|φ(y_fin)| ‖y_∞‖ ^ (-A)` of a test function `φ` is integrable for the volume on
the adelic group as soon as its exponent `A` exceeds `8 n²`. -/
lemma integrable_majorant (φ : TestFunction (Gf E n)) {A : ℕ} (hA : 8 * card n ^ 2 < A) :
    Integrable fun y : G E s ↦ majorant φ A y := by
  have h_place : Integrable fun z : USign s ↦ (‖z.val.val‖ ^ A)⁻¹ := by
    have h_decay : Integrable fun z : USign s ↦ (2 / ‖z.val.val‖) ^ A := by
      obtain ⟨h_integrable, -⟩ :=
        DiscreteSeries.integral_decay_le volume IsProperMap.monoidHom_id hA (1 : USign s)
      simpa using h_integrable
    exact (h_decay.const_mul (2 ^ A)⁻¹).congr (.of_forall fun z ↦ by simp [div_eq_mul_inv, mul_pow])
  have h_inf : Integrable fun z : GInf E s ↦ ∏ w : InfinitePlace E, (‖(z w).val.val‖ ^ A)⁻¹ :=
    .fintype_prod fun _ ↦ h_place
  obtain ⟨h_const, h_compact, -⟩ := φ.property
  have h_fin : Integrable φ.1 := h_const.continuous.integrable_of_hasCompactSupport h_compact
  have h_eq (y : G E s) :
      (∏ w : InfinitePlace E, (‖(y.1 w).val.val‖ ^ A)⁻¹) * ‖φ.1 y.2‖ = majorant φ.1 A y := by
    simp [majorant, Finset.prod_pow, mul_comm]
  exact (h_inf.mul_prod h_fin.norm).congr (.of_forall h_eq)

/-- Let `E` be a CM field and `V` a hermitian space with a point. Let `φ` be a test function on the
finite unitary group, a locally constant, compactly supported complex function. Then there is a
constant `C ≥ 0` such that, for all adelic points `g` and `x`, the following holds with `f` the
number of infinite places and `V.height x` equal to `1/λ`, where `λ` is the first minimum, capped at
1, of the space `V` moved by `x`: the sum of the majorant `|φ(y_fin)| ‖y_∞‖ ^ (-8 n² - 1)` over all
`y = g⁻¹ · V.ratEmbed γ · x`, with `γ` running over the rational unitary group `U(V.J)` and `‖y_∞‖`
the product of the operator norms at the infinite places, is at most `C * V.height x ^ (4 f n²)`. -/
theorem exists_tsum_majorant_le (φ : TestFunction (Gf E n)) : ∃ C ≥ (0 : ℝ), ∀ g x : G E s,
    ∑' γ : U V.J, ENNReal.ofReal (majorant φ (8 * card n ^ 2 + 1) (g⁻¹ * V.ratEmbed γ * x)) ≤
      .ofReal (C * V.height x ^ (4 * Core.numInfPlaces E * card n ^ 2)) := by
  -- Compare the sum, times the volume of a box of radius `(c Ht(x)²)⁻¹`, with the integral.
  obtain ⟨J, hJ, -, hJ_fix⟩ := TestFunction.exists_isLevel_invariant φ
  obtain ⟨c, hc, h_disjoint⟩ := V.exists_levelBox_disjoint hJ.le
  -- `v` is a lower bound for `(12 D) ^ d` times the volume of the box of radius `D⁻¹`.
  obtain ⟨v, hv, h_volume⟩ := exists_le_mul_volume_levelBox s hJ.isOpen
  set A : ℕ := 8 * card n ^ 2 + 1
  set d : ℕ := 2 * card n ^ 2 * Core.numInfPlaces E with hd
  let factor : ℝ := (2 ^ Core.numInfPlaces E) ^ A
  let bound : ℝ≥0∞ := .ofReal factor * ∫⁻ y : G E s, .ofReal (majorant φ A y)
  have h_bound_ne_top : bound ≠ ⊤ :=
    mul_ne_top ofReal_ne_top (integrable_majorant φ (Nat.lt_succ_self _)).lintegral_lt_top.ne
  refine ⟨(12 * c) ^ d * (bound / v).toReal, by positivity, fun g x ↦ ?_⟩
  have hD : 1 ≤ c * V.height x ^ 2 :=
    one_le_mul_of_one_le_of_one_le hc (one_le_pow₀ (V.one_le_height x))
  set S : ℝ≥0∞ := ∑' γ : U V.J, ENNReal.ofReal (majorant φ A (g⁻¹ * V.ratEmbed γ * x))
  set B : Set (G E s) := levelBox E s (c * V.height x ^ 2)⁻¹ J
  set cover : ℝ := (12 * (c * V.height x ^ 2)) ^ d
  have h_sum : S * volume B ≤ bound := by
    refine tsum_mul_measure_le_lintegral volume (measurableSet_levelBox _ hJ.isOpen)
      (h_disjoint g x) (f := fun y ↦ .ofReal (majorant φ A y)) ofReal_ne_top fun y z hz ↦ ?_
    rw [← ofReal_mul (by positivity)]
    exact ofReal_le_ofReal (majorant_le_mul_majorant_mul hJ_fix A (inv_le_one_of_one_le₀ hD) y hz)
  have h_le : S * v ≤ .ofReal cover * bound :=
    calc S * v ≤ S * (.ofReal cover * volume B) := by gcongr; exact h_volume _ hD
      _ = .ofReal cover * (S * volume B) := mul_left_comm _ _ _
      _ ≤ .ofReal cover * bound := by gcongr
  calc S ≤ .ofReal cover * bound / v :=
        (ENNReal.le_div_iff_mul_le (.inl hv)
          (.inr (mul_ne_top ofReal_ne_top h_bound_ne_top))).2 h_le
    _ = .ofReal (cover * (bound / v).toReal) := by
        rw [mul_div_assoc, ofReal_mul (by positivity), ofReal_toReal (div_ne_top h_bound_ne_top hv)]
    _ = .ofReal ((12 * c) ^ d * (bound / v).toReal *
          V.height x ^ (4 * Core.numInfPlaces E * card n ^ 2)) := by
        simp only [cover, hd]
        ring_nf

end Space

end New

end
