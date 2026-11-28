import Lib.Adelic.Witt.SmoothWitt
import Lib.SiegelWeil.Tower.LargeSideConstantTerm
import Lib.Weil.MixedModel.TargetZeroTerm

/-!
# The image of the cone integral

Let `W' = W ⊕ H` and `V' = V ⊕ H`, with adapted splittings and isotropic lines `A` and `B` in the
hyperbolic planes, and let the rank of `W` be even. For `0 < z`, every Schwartz vector `v` for
`(W, V)` has a Schwartz vector `v'` for `(W', V')` such that the cone integral of `v'` and `v` have
the same theta integrals on standard data (`exists_thetaLarge_cone_eq`). Up to a positive factor
that is analytic in `z`, one `v'` serves for all `z > 0` (`exists_thetaLarge_cone_eq_mul`). The
slices of this `v'` along `A` (its values in the mixed model attached to `A`, as a function of a
vector of `V'` at the infinite places) are `β x • k x v^B`, where `v` is the zero term of `v^B`
along `Hom(W, B)`, `β` is a bump function near the vector `x_B` that spans `B`, and the smooth
family `k x` carries `x_B` to `x` for isotropic `x` in the support of `β`.

In the code `A` and `X` are the splittings of `W'` and `V'` that define the two lines, the adelic
vector `x_B` that spans `B` is `X.kAdelic`, and `lineVector X w` is its component at the infinite
place `w`. The word real refers to the components at the infinite places of `E`.

* `PairFock E s t` is the Fock space of the pair with signs `s` and `t`; a vector is Schwartz
  (`IsSchwartzVector`) if all its weighted norms are finite.
* `realPairWeil γ γ'` is the Weil representation of the real points `GInf` of the two unitary groups
  on this space, with `(x, y)` twisted by `det y ^ γ * det x ^ (-γ')`.
* A splitting is adapted (`IsBaseAdapted`) if its adelic frames are orthonormal at the infinite
  places and integral at the finite places.
* `cone A X μ z v'` is the integral of `coneIntegrand A X μ true z v'` over the pairs `(κ, a)` of a
  point of the maximal compact subgroup `maxCompact E t'` of `U(V')` and a family of non-zero
  complex numbers indexed by the infinite places.
* `thetaLarge W V 𝔠 v Φ` is the theta integral over `[U(V)]` of the datum with real part `v` and
  component `Φ` at the ramified places of `𝔠`, as a function on `U(W)`.
* A `SplitTameChar E μ` is a tamely ramified character of weight `μ`, all `μ w > 0`, of the norm-one
  adeles, with a non-empty set of ramified places that contains no conjugate of one of its places;
  so the ramified places are split over the totally real subfield.

## Relation to the literature

See `New.Determinant.Exchange.TheoremForPartners` for related work.
-/

noncomputable section

namespace New.Exchange

open Matrix NumberField MeasureTheory Measure Fintype Fock Space Splitting WeilData ContDiff
  Norms.Elementwise
variable {E : Type} [Field E] [CMType E] {n n' r r' : Type} [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n'] [Fintype r] [DecidableEq r] [Fintype r'] [DecidableEq r']
  {s : n → ℤˣ} {s' : n' → ℤˣ} {t : r → ℤˣ} {t' : r' → ℤˣ} {W : Space E n s} {W' : Space E n' s'}
  {V : Space E r t} {V' : Space E r' t'} (A : W'.Splitting W Unit) (X : V'.Splitting V Unit)

/-- The component `lineVector X w` at an infinite place `w` of the vector `x_B` that spans the
isotropic line of the splitting `X` is non-zero. -/
lemma lineVector_ne_zero (w : InfinitePlace E) : lineVector X w ≠ 0 := by
  intro h_zero
  have h_dual : ((X.kCoord * X.kAdelic) () ()).1 w = 1 := by simp [X.coord_mul_frame]
  have h_entry (i : r') : (X.kAdelic i ()).1 w = 0 := congrFun h_zero i
  simp [mul_apply, Prod.fst_sum, h_entry] at h_dual

lemma sum_norm_sq_lineVector_pos (w : InfinitePlace E) : 0 < ∑ i : r', ‖lineVector X w i‖ ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, lineVector X w i ≠ 0 := Function.ne_iff.1 (lineVector_ne_zero X w)
  exact Finset.sum_pos' (fun _ _ ↦ sq_nonneg _) ⟨i, Finset.mem_univ i, by positivity⟩

/-- Let `X.kAdelic` be the adelic vector `x_B` that spans the isotropic line of the splitting `X`,
and `lineVector X w` its component at the infinite place `w`. This component is isotropic for the
Hermitian form with signs `t'`. -/
lemma lineVector_isotropic (w : InfinitePlace E) :
    star (lineVector X w) ⬝ᵥ signMatrix t' *ᵥ lineVector X w = 0 := by
  have h_gram : X.kAdelicᴴ * stdForm E t' * X.kAdelic = 0 := by
    simp [← lCoord.eq_1, X.coord_mul_frame]
  have h_real : (atRealPlace X.kAdelic w)ᴴ * signMatrix t' * atRealPlace X.kAdelic w = 0 := by
    simp [gram_atRealPlace, h_gram]
  simpa [mul_apply, dotProduct, mulVec, lineVector, signMatrix, diagonal, mul_assoc] using
    congrFun₂ h_real () ()

variable [WeilData E]

/-- The component at the infinite places of a point `κ` of the maximal compact subgroup of the
adelic unitary group for the signs `t'`. -/
abbrev maxCompactInf (κ : maxCompact E t') : GInf E t' := (κ : G E t').1

/-- The isotropic vector `κ⁻¹ x_B a` of `p = (κ, a)`, where `x_B` is the vector that spans the
isotropic line of `X`, with components `lineVector X w` at the infinite places `w`. It is written in
the coordinates of the slices along a line of the source: its entry at `(w, i, ())` is the `i`-th
entry at the infinite place `w`. -/
def conePoint (p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ) : InfinitePlace E × r' × Unit → ℂ :=
  fun q ↦ ((↑(maxCompactInf p.1 q.1)⁻¹ : Matrix r' r' ℂ) *ᵥ p.2.val q.1 • lineVector X q.1) q.2.1

omit [WeilData E] in
/-- Let `lineVector X w` be the component at the infinite place `w` of the vector `x_B` that spans
the isotropic line of `X`. The coordinates of `conePoint X (κ, a)` at `w` are those of
`κ⁻¹ x_B a`, that is of `a w • lineVector X w` multiplied by the inverse of `κ` at `w`. -/
lemma conePoint_apply (κ : maxCompact E t') (a : (InfinitePlace E → ℂ)ˣ) (w : InfinitePlace E)
    (i : r') : conePoint X (κ, a) (w, i, ()) =
      ((↑(maxCompactInf κ w)⁻¹ : Matrix r' r' ℂ) *ᵥ a.val w • lineVector X w) i := rfl

omit [WeilData E] in
lemma continuous_conePoint : Continuous (conePoint X) := by
  refine continuous_pi fun q ↦ ?_
  have h_coord : Continuous fun p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ ↦ p.2.val q.1 :=
    (continuous_apply q.1).comp Units.continuous_val.snd'
  simp only [conePoint, mulVec, dotProduct, Pi.smul_apply]
  fun_prop

omit [WeilData E] in
/-- A point of the adelic maximal compact subgroup is a unitary matrix at each infinite place. -/
lemma maxCompact_fst_mem_maxCompactU (κ : maxCompact E t') (w : InfinitePlace E) :
    maxCompactInf κ w ∈ maxCompactU t' := (Subgroup.mem_prod.1 κ.property).1 w (Set.mem_univ w)

omit [WeilData E] in
/-- Let `x_B` be the vector that spans the isotropic line of the splitting `X` of `V'`, with
components `lineVector X w`, so that `conePoint X (κ, a)` is `κ⁻¹ x_B a`. A point `κ` of the
maximal compact subgroup of `U(V')` keeps lengths: at each infinite place `w`, the squared length
of `κ⁻¹ x_B a` is `‖a w‖ ^ 2` times that of `x_B`. -/
lemma sum_norm_sq_conePoint (κ : maxCompact E t') (a : (InfinitePlace E → ℂ)ˣ)
    (w : InfinitePlace E) : ∑ i : r', ‖conePoint X (κ, a) (w, i, ())‖ ^ 2 =
      ‖a.val w‖ ^ 2 * ∑ i : r', ‖lineVector X w i‖ ^ 2 := by
  let K : Matrix r' r' ℂ := ↑(maxCompactInf κ w)⁻¹
  let y : r' → ℂ := a.val w • lineVector X w
  have h_unitary : Kᴴ * K = 1 := by
    simpa [K] using mem_U.1 (inv_mem (maxCompact_fst_mem_maxCompactU κ w))
  have h_dot : star (K *ᵥ y) ⬝ᵥ K *ᵥ y = star y ⬝ᵥ y := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, h_unitary, one_mulVec]
  calc ∑ i, ‖(K *ᵥ y) i‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
        rwa [star_dotProduct_self_eq_sum, star_dotProduct_self_eq_sum, Complex.ofReal_inj] at h_dot
    _ = ‖a.val w‖ ^ 2 * ∑ i, ‖lineVector X w i‖ ^ 2 := by simp [y, Finset.mul_sum, mul_pow]

/-- Let `A` be an adapted splitting and `x_B = X.kAdelic` the adelic vector that spans the isotropic
line of `X`, with components `lineVector X w` at the infinite places. Here `realSlice A V'` sends a
vector for `(W', V')` to its value, a vector for `(W, V')`, at a given adelic vector of `V'` in the
mixed model attached to `A`. For `κ⁻¹ x_B a`, with `κ` replaced by its infinite component and `a`
extended by `0` at the finite places, this is the slice of that mixed model at the point
`conePoint X (κ, a)`, the coordinates of `κ⁻¹ x_B a` at the infinite places. -/
lemma realSlice_eq_slice_conePoint [IsBaseAdapted A] (κ : maxCompact E t')
    (a : (InfinitePlace E → ℂ)ˣ) :
    realSlice A V'
        (G.adeleMatrix ((maxCompactInf κ, 1) : G E t')⁻¹ * (((a.val, 0) : 𝔸 E) • X.kAdelic)) =
      (isAdapted_homSource A V').mixedModel.slice (conePoint X (κ, a)) := by
  rw [realSlice]
  congr with q
  simp [conePoint, matrixToVec, mul_apply, mulVec, dotProduct, lineVector, Prod.fst_sum,
    G.adeleMatrix_fst]

omit [WeilData E] in
/-- A function `ρ` of `(κ, a)`, with `κ` in `maxCompact E t'`, that vanishes unless
`1 / 2 ≤ ‖a w‖ ^ 2 ≤ 2` at every infinite place `w`, has compact support. -/
lemma hasCompactSupport_of_norm_sq_mem_Icc {ρ : maxCompact E t' × (InfinitePlace E → ℂ)ˣ → ℝ}
    (hρ : ∀ (κ : maxCompact E t') (a : (InfinitePlace E → ℂ)ˣ), ρ (κ, a) ≠ 0 →
      ∀ w : InfinitePlace E, ‖a.val w‖ ^ 2 ∈ Set.Icc (2⁻¹ : ℝ) 2) :
    HasCompactSupport ρ := by
  let annulus : Set ℂ := {c | ‖c‖ ^ 2 ∈ Set.Icc (2⁻¹ : ℝ) 2}
  have h_annulus : IsCompact annulus :=
    (isCompact_closedBall 0 2).of_isClosed_subset (isClosed_Icc.preimage (by fun_prop))
      fun c hc ↦ mem_closedBall_zero_iff.2 (by nlinarith [norm_nonneg c, hc.2])
  have h_zero : 0 ∉ annulus := by norm_num [annulus]
  have h_units : Set.univ.pi (fun _ : InfinitePlace E ↦ annulus) ⊆ Set.range Units.val :=
    fun a ha ↦ Pi.isUnit_iff.2 fun w ↦ (ne_of_mem_of_not_mem (ha w trivial) h_zero).isUnit
  have h_compact : IsCompact (Units.val ⁻¹' Set.univ.pi fun _ : InfinitePlace E ↦ annulus) :=
    Units.isOpenEmbedding_val.isCompact_preimage' (isCompact_univ_pi fun _ ↦ h_annulus) h_units
  exact .of_support_subset_isCompact (isCompact_univ.prod h_compact)
    fun ⟨κ, a⟩ h_ne ↦ ⟨Set.mem_univ κ, fun w _ ↦ hρ κ a h_ne w⟩

/-- A real function `ρ` of the pairs `p = (κ, a)` has a positive Mellin transform if for all real
`z` the integral of `ρ (κ, a) |a| ^ z` converges and is positive. Here `|a|` is the module of the
idele that is `a` at the infinite places and `1` elsewhere. -/
structure HasPosMellinTransform (ρ : maxCompact E t' × (InfinitePlace E → ℂ)ˣ → ℝ) : Prop where
  /-- The integral of `ρ (κ, a) |a| ^ z` converges. -/
  integrable (z : ℝ) : Integrable (fun p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ ↦
    ρ p * ideleAbs (realIdele p.2) ^ z) (haar.prod haar)
  /-- The integral of `ρ (κ, a) |a| ^ z` is positive. -/
  integral_pos (z : ℝ) : 0 < ∫ p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ,
    ρ p * ideleAbs (realIdele p.2) ^ z ∂haar.prod haar

omit [WeilData E] in
/-- Let `ρ` have a positive Mellin transform: for all real `z` the integral of `ρ (κ, a) |a| ^ z`
converges and is positive. Then `(κ, a) ↦ ρ (κ, a) |a| ^ (m / 2)` has one too: the factor shifts the
exponent by `m / 2`. -/
lemma HasPosMellinTransform.mul_sqrt_pow {ρ : maxCompact E t' × (InfinitePlace E → ℂ)ˣ → ℝ}
    (hρ : HasPosMellinTransform ρ) (m : ℕ) :
    HasPosMellinTransform fun p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ ↦
      ρ p * √(ideleAbs (realIdele p.2)) ^ m := by
  have h_shift (z : ℝ) (p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ) :
      ρ p * √(ideleAbs (realIdele p.2)) ^ m * ideleAbs (realIdele p.2) ^ z =
        ρ p * ideleAbs (realIdele p.2) ^ (m / 2 + z : ℝ) := by
    rw [Real.rpow_add ideleAbs_pos, Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ideleAbs_pos.le,
      mul_assoc, one_div_mul_eq_div]
  exact ⟨fun z ↦ by simpa only [h_shift] using hρ.integrable (m / 2 + z),
    fun z ↦ by simpa only [h_shift] using hρ.integral_pos (m / 2 + z)⟩

omit [WeilData E] in
/-- Let `x_B` be the vector that spans the isotropic line of the splitting `X`, with components
`lineVector X w`, so that `conePoint X (κ, a)` is `κ⁻¹ x_B a` for `κ` in the maximal compact
subgroup `maxCompact E t'` of `U(V')`. Let `β ≥ 0` be continuous, non-zero at `x_B`, and zero unless
the squared length at each infinite place is within a factor `2` of that of `x_B`. Then for all real
`z` the integral of `β (κ⁻¹ x_B a) |a| ^ z` over the pairs `(κ, a)` converges and is positive. -/
lemma hasPosMellinTransform_comp_conePoint {β : (InfinitePlace E × r' × Unit → ℂ) → ℝ}
    (hβ : Continuous β) (hβ_nonneg : ∀ x : InfinitePlace E × r' × Unit → ℂ, 0 ≤ β x)
    (hβ_ne_zero : β (conePoint X 1) ≠ 0)
    (hβ_shell : ∀ x : InfinitePlace E × r' × Unit → ℂ, β x ≠ 0 → ∀ w : InfinitePlace E,
      ∑ i : r', ‖x (w, i, ())‖ ^ 2 ∈ Set.Icc (2⁻¹ * ∑ i : r', ‖lineVector X w i‖ ^ 2)
        (2 * ∑ i : r', ‖lineVector X w i‖ ^ 2)) :
    HasPosMellinTransform (β ∘ conePoint X) := by
  let ρ (z : ℝ) (p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ) : ℝ :=
    β (conePoint X p) * ideleAbs (realIdele p.2) ^ z
  have hρ_cont (z : ℝ) : Continuous (ρ z) := (hβ.comp (continuous_conePoint X)).mul
    (continuous_ideleAbs_realIdele.snd'.rpow_const fun _ ↦ .inl ideleAbs_pos.ne')
  have hρ_supp (z : ℝ) : HasCompactSupport (ρ z) := by
    refine hasCompactSupport_of_norm_sq_mem_Icc fun κ a h_ne w ↦ ?_
    simpa only [sum_norm_sq_conePoint, Set.mem_Icc,
      mul_le_mul_iff_left₀ (sum_norm_sq_lineVector_pos X w)] using
      hβ_shell (conePoint X (κ, a)) (left_ne_zero_of_mul h_ne) w
  refine ⟨fun z ↦ (hρ_cont z).integrable_of_hasCompactSupport (hρ_supp z), fun z ↦ ?_⟩
  exact (hρ_cont z).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (hρ_supp z)
    (fun _ ↦ mul_nonneg (hβ_nonneg _) (Real.rpow_nonneg ideleAbs_pos.le z))
    (by simpa [ρ] using hβ_ne_zero)

omit [WeilData E] in
/-- Let the splitting `X` of `V'` define the isotropic line spanned by `x_B`, with components
`lineVector X w`, and write `conePoint X (κ, a) = κ⁻¹ x_B a` for `κ` in the maximal compact subgroup
of the unitary group `U(V')`. There are a smooth compactly supported function `β` and a smooth
family `k x` of real points of `U(V')` such that `ρ (κ, a) = β (κ⁻¹ x_B a)` has a positive Mellin
transform and, for `x = κ⁻¹ x_B a` with `β x ≠ 0`, the point `κ * k x` multiplies `x_B` by `a` at
each infinite place. -/
lemma exists_hasPosMellinTransform_mulVec_eq_smul :
    ∃ (β : (InfinitePlace E × r' × Unit → ℂ) → ℝ)
      (k : (InfinitePlace E × r' × Unit → ℂ) → GInf E t'),
      ContDiff ℝ ∞ β ∧
      HasCompactSupport β ∧
      (∀ w : InfinitePlace E,
        ContDiff ℝ ∞ fun x : InfinitePlace E × r' × Unit → ℂ ↦ (k x w : Matrix r' r' ℂ)) ∧
      HasPosMellinTransform (β ∘ conePoint X) ∧
      ∀ (κ : maxCompact E t') (a : (InfinitePlace E → ℂ)ˣ), β (conePoint X (κ, a)) ≠ 0 →
        ∀ w : InfinitePlace E,
          (↑(maxCompactInf κ w * k (conePoint X (κ, a)) w) : Matrix r' r' ℂ) *ᵥ lineVector X w =
            a.val w • lineVector X w := by
  -- Take the family place by place, and `β ≥ 0` supported where it carries `x_B` to `x` wherever
  -- `x` is isotropic and where the squared length at each place is within a factor `2` of that of
  -- `x_B`.
  let Carries (w : InfinitePlace E) (g : USign t') (y : r' → ℂ) : Prop :=
    star y ⬝ᵥ signMatrix t' *ᵥ y = 0 → (g : Matrix r' r' ℂ) *ᵥ lineVector X w = y
  have h_family (w : InfinitePlace E) : ∃ k : (r' → ℂ) → USign t',
      ContDiff ℝ ∞ (fun y ↦ (k y : Matrix r' r' ℂ)) ∧
        ∀ᶠ y in nhds (lineVector X w), Carries w (k y) y :=
    exists_contDiff_eventually_mulVec_eq (lineVector_ne_zero X w) (lineVector_isotropic X w)
  choose k hk h_near using h_family
  let x₀ (q : InfinitePlace E × r' × Unit) : ℂ := lineVector X q.1 q.2.1
  let col (w : InfinitePlace E) (x : InfinitePlace E × r' × Unit → ℂ) (i : r') : ℂ := x (w, i, ())
  let len (y : r' → ℂ) : ℝ := ∑ i, ‖y i‖ ^ 2
  let shell (w : InfinitePlace E) : Set ℝ :=
    Set.Icc (2⁻¹ * len (lineVector X w)) (2 * len (lineVector X w))
  have h_shell (w : InfinitePlace E) : ∀ᶠ y in nhds (lineVector X w), len y ∈ shell w :=
    have h_len : 0 < len (lineVector X w) := sum_norm_sq_lineVector_pos X w
    (by fun_prop : ContinuousAt len _) (Icc_mem_nhds (by linarith) (by linarith))
  let good : Set (InfinitePlace E × r' × Unit → ℂ) :=
    {x | ∀ w, Carries w (k w (col w x)) (col w x) ∧ len (col w x) ∈ shell w}
  have h_good : good ∈ nhds x₀ := Filter.eventually_all.2 fun w ↦
    (by fun_prop : ContinuousAt (col w) x₀).eventually ((h_near w).and (h_shell w))
  obtain ⟨β, hβ_good, hβ_supp, hβ, hβ_range, hβ_one⟩ :
      ∃ β : (InfinitePlace E × r' × Unit → ℂ) → ℝ, tsupport β ⊆ good ∧ HasCompactSupport β ∧
        ContDiff ℝ ∞ β ∧ Set.range β ⊆ Set.Icc 0 1 ∧ β x₀ = 1 :=
    exists_contDiff_tsupport_subset h_good
  have h_carry (x : InfinitePlace E × r' × Unit → ℂ) (hx : β x ≠ 0) (w : InfinitePlace E) :
      Carries w (k w (col w x)) (col w x) := (hβ_good (subset_closure hx) w).1
  have h_len (x : InfinitePlace E × r' × Unit → ℂ) (hx : β x ≠ 0) (w : InfinitePlace E) :
      len (col w x) ∈ shell w := (hβ_good (subset_closure hx) w).2
  have h_base : conePoint X 1 = x₀ := funext fun q ↦ by simp [conePoint, maxCompactInf, x₀]
  have h_mellin : HasPosMellinTransform (β ∘ conePoint X) :=
    hasPosMellinTransform_comp_conePoint X hβ.continuous (fun x ↦ (hβ_range ⟨x, rfl⟩).1)
      (by simp [h_base, hβ_one]) h_len
  refine ⟨β, fun x w ↦ k w (col w x), hβ, hβ_supp, fun w ↦ (hk w).comp (by fun_prop), h_mellin,
    fun κ a h_ne w ↦ ?_⟩
  -- The point `x = κ⁻¹ x_B a` is isotropic, so `k x` carries `x_B` to it.
  let κw : USign t' := maxCompactInf κ w
  let y : r' → ℂ := col w (conePoint X (κ, a))
  have hy : y = (↑κw⁻¹ : Matrix r' r' ℂ) *ᵥ a.val w • lineVector X w :=
    funext (conePoint_apply X κ a w)
  have h_back : (κw : Matrix r' r' ℂ) *ᵥ y = a.val w • lineVector X w := by
    rw [hy, mulVec_mulVec, Subgroup.coe_inv, Units.mul_inv, one_mulVec]
  have h_iso : star y ⬝ᵥ signMatrix t' *ᵥ y = 0 := by
    rw [← mem_U.1 κw.prop, ← mulVec_mulVec, ← mulVec_mulVec, ← star_mulVec_dotProduct, h_back]
    simp [mulVec_smul, lineVector_isotropic X w]
  have h_image : (k w y : Matrix r' r' ℂ) *ᵥ lineVector X w = y := h_carry _ h_ne w h_iso
  rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, h_image, h_back]

/-- Slices along an adapted splitting `A` can be prescribed: for `β` smooth of compact support, a
smooth family `k x` of real points of `U(V')` and a Schwartz vector `v` for `(W, V')`, some Schwartz
vector `v'` for `(W', V')` has the slice `β x • k x v` at every `x`. -/
lemma exists_slice_eq_smul_realPairWeil [IsBaseAdapted A] (γ : InfinitePlace E → ℤ)
    {β : (InfinitePlace E × r' × Unit → ℂ) → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ_supp : HasCompactSupport β) {k : (InfinitePlace E × r' × Unit → ℂ) → GInf E t'}
    (hk : ∀ w : InfinitePlace E,
      ContDiff ℝ ∞ fun x : InfinitePlace E × r' × Unit → ℂ ↦ (k x w : Matrix r' r' ℂ))
    {v : PairFock E s t'} (hv : IsSchwartzVector v) :
    ∃ v' : PairFock E s' t', IsSchwartzVector v' ∧ ∀ x : InfinitePlace E × r' × Unit → ℂ,
      (isAdapted_homSource A V').mixedModel.slice x v' = β x • realPairWeil γ 0 (1, k x) v := by
  -- `realPairWeil` is `realWeil` times powers of the determinants, which are absorbed into `β`.
  have h_entry (w : InfinitePlace E) (i j : r') :
      ContDiff ℝ ∞ fun x ↦ (k x w : Matrix r' r' ℂ) i j := contDiff_pi.1 (contDiff_pi.1 (hk w) i) j
  have h_zpow (w : InfinitePlace E) :
      ContDiff ℝ ∞ fun x ↦ (k x w : Matrix r' r' ℂ).det ^ γ w := by
    have h_det : ContDiff ℝ ∞ fun x ↦ (k x w : Matrix r' r' ℂ).det := by
      simp only [det_apply]
      fun_prop
    cases γ w with
    | ofNat m => simpa using h_det.pow m
    | negSucc m =>
      simp only [zpow_negSucc]
      exact (h_det.pow (m + 1)).inv fun x ↦ pow_ne_zero _ (GeneralLinearGroup.det_ne_zero _)
  have h_scalar : ContDiff ℝ ∞ fun x ↦ β x • ∏ w, (k x w : Matrix r' r' ℂ).det ^ γ w :=
    hβ.smul (contDiff_prod fun w _ ↦ h_zpow w)
  have h_family : ContDiff ℝ ∞ fun x ↦ (pairHomInf ((1 : GInf E s), k x) :
      Matrix (InfinitePlace E × r' × n) (InfinitePlace E × r' × n) ℂ) := by
    refine contDiff_pi' fun ⟨w, i, a⟩ ↦ contDiff_pi' fun ⟨w', j, b⟩ ↦ ?_
    obtain rfl | h_ne := eq_or_ne w w'
    · simpa [pairHomInf, blockDiagonal_apply, pairHom, one_apply] using
        (h_entry w i j).mul (contDiff_const (c := (1 : Matrix n n ℂ) a b))
    · simp [pairHomInf, blockDiagonal_apply, h_ne, contDiff_const]
  obtain ⟨v', hv', h_slice⟩ :=
    (isAdapted_homSource A V').mixedModel.exists_isSchwartzVector_slice_eq h_scalar
      hβ_supp.smul_right h_family hv
  exact ⟨v', hv', fun x ↦ by simp [h_slice, realPairWeil_apply_apply, mul_smul]⟩

/-- Let the splittings `A` and `X` be adapted and the rank of `W` even. There is a function `ρ` of
`(κ, a)` such that `ρ (κ, a) |a| ^ z` has a positive integral for all real `z`, with the following
property. Each Schwartz vector `v` for `(W, V)` has a Schwartz vector `v'` for `(W', V')` such that
the integrand `coneIntegrand A X μ true z v'` of the cone integral of `v'`, with weight `μ` and
exponent `z`, is at each `(κ, a)` the multiple `ρ (κ, a) |a| ^ z` of a translate of `v` by a real
point `h` of `U(V)`. -/
theorem exists_coneIntegrand_eq_smul [IsBaseAdapted A] [IsBaseAdapted X] (μ : InfinitePlace E → ℤ)
    (hn : 2 ∣ card n) :
    ∃ ρ : maxCompact E t' × (InfinitePlace E → ℂ)ˣ → ℝ,
      HasPosMellinTransform ρ ∧
      ∀ v : PairFock E s t, IsSchwartzVector v → ∃ v' : PairFock E s' t', IsSchwartzVector v' ∧
        ∀ (z : ℝ) (κ : maxCompact E t') (a : (InfinitePlace E → ℂ)ˣ), ∃ h : GInf E t,
          coneIntegrand A X μ true z v' (κ, a) =
            (ρ (κ, a) * ideleAbs (realIdele a) ^ z) •
              realPairWeil (targetWeight n μ) 0 (1, h) v := by
  -- Write `v` as the zero term of `vB` and prescribe the slices `β x • k x vB` of `v'`.
  let γ : InfinitePlace E → ℤ := targetWeight n μ
  obtain ⟨β, k, hβ, hβ_supp, hk, h_mellin, h_line⟩ := exists_hasPosMellinTransform_mulVec_eq_smul X
  refine ⟨fun p ↦ β (conePoint X p) * √(ideleAbs (realIdele p.2)) ^ card n,
    h_mellin.mul_sqrt_pow (card n), fun v hv ↦ ?_⟩
  obtain ⟨vB, hvB, rfl⟩ := exists_realTargetZeroTerm_eq (W := W) X hv
  obtain ⟨v', hv', h_slice⟩ := exists_slice_eq_smul_realPairWeil A γ hβ hβ_supp hk hvB
  refine ⟨v', hv', fun z κ a ↦ ?_⟩
  let κInf : GInf E t' := maxCompactInf κ
  let x : InfinitePlace E × r' × Unit → ℂ := conePoint X (κ, a)
  let N : ℝ := ideleAbs (realIdele a)
  let u (w : InfinitePlace E) : ℂ := a.val w / ‖a.val w‖
  have h_weight : targetWeight n' μ = fun w ↦ γ w + 1 := by grind [A.card_eq, card_unit]
  -- For `x = κ⁻¹ x_B a`, the line term is the zero term along `Hom(W, B)` of the slice of `κ v'`
  -- at `x_B a`, and this slice is `β x • κ k x vB`.
  have h_term : lineTermReal A X true a (realPairWeil (fun w ↦ γ w + 1) 0 (1, κInf) v') =
      β x • realTargetZeroTerm W X (realPairWeil γ 0 (1, κInf * k x) vB) := by
    rw [lineTermReal_true_eq_realTargetZeroTerm, realSlice_realPairWeil,
      realSlice_eq_slice_conePoint,
      h_slice]
    simp only [ContinuousLinearMap.map_smul_of_tower, rep_apply_apply, Prod.mk_mul_mk, one_mul, x]
  rw [coneIntegrand, h_weight, h_term]
  by_cases h_zero : β x = 0
  · exact ⟨1, by simp [x, h_zero]⟩
  -- The point `κ k x` multiplies `x_B` by `a`, so under the zero term it acts through `U(V)`, with
  -- a power of `|a|` and a phase that cancels the one in the integrand.
  obtain ⟨h, h_levi⟩ : ∃ h : GInf E t, ∀ v : PairFock E s t',
      realTargetZeroTerm W X (realPairWeil γ 0 (1, κInf * k x) v) =
        ((∏ w, u w ^ (-2 * μ w)) * √N ^ card n) •
          realPairWeil γ 0 (1, h) (realTargetZeroTerm W X v) :=
    exists_realTargetZeroTerm_realPairWeil X hn μ (h_line κ a h_zero)
  have h_phase : (∏ w, u w ^ (2 * μ w)) * ∏ w, u w ^ (-2 * μ w) = 1 := by
    simp [u, Finset.prod_ne_zero_iff, zpow_ne_zero, piUnits_val_apply_ne_zero]
  have h_scalar : (∏ w, u w ^ (2 * μ w)) * (N ^ z : ℝ) * β x *
      ((∏ w, u w ^ (-2 * μ w)) * √N ^ card n) = (β x * √N ^ card n * N ^ z : ℝ) := by
    push_cast
    linear_combination (N ^ z : ℝ) * β x * √N ^ card n * h_phase
  exact ⟨h, by rw [h_levi, ← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul, h_scalar]⟩

/-- The theta integral `thetaLarge W V 𝔠 v Φ`, a function of a point `g` of `U(W)`, is the integral
over `[U(V)]` for the datum with real part `v` and component `Φ` at the ramified places of `𝔠`. It
does not change when a real point `h` of `U(V)` acts on `v` by the Weil representation twisted by
`det ^ targetWeight n μ`, where `targetWeight n μ w = ⌊#n / 2⌋ - μ w`. Here `𝔠` is a split tame
character: a tamely ramified character of weight `μ`, with all `μ w > 0`, of the norm-one adeles,
whose non-empty set `𝔠.ramifiedPlaces` of ramified places contains no conjugate of one of its
places, so that these places are split. `Φ` is a function on the matrices over the product of the
completions at these places. -/
lemma thetaLarge_realPairWeil (μ : InfinitePlace E → ℤ) (𝔠 : SplitTameChar E μ) (h : GInf E t)
    (v : PairFock E s t) (Φ : Matrix r n (LocProd 𝔠.ramifiedPlaces) → ℂ) (g : G E s) :
    thetaLarge W V 𝔠 (realPairWeil (targetWeight n μ) 0 (1, h) v) Φ g = thetaLarge W V 𝔠 v Φ g := by
  let a : AutChar E := rankTwist 𝔠.character⁻¹ n
  let f : 𝒮 (W.hom V) := localDatum W V v Φ 𝔠.readsAt
  have h_move : thetaIntegral W V a a (pairWeil W V a a (1, h, 1) f) g =
      thetaIntegral W V a a f (g * 1) := thetaIntegral_pairWeil (1, h, 1) g
  simpa +unfoldPartialApp only [pairWeil_integrated_right, mul_one, thetaLarge, localDatum, a, f,
    targetWeight, Pi.neg_apply, sub_eq_add_neg] using h_move

/-- Let `A` and `X` be adapted splittings `W' = W ⊕ H` and `V' = V ⊕ H` with `H` a hyperbolic plane,
let the rank of `W` be even, and let `σ` identify `b ⊕ r` with the index set of `W`. There is a
positive analytic function `B` on the real line such that each Schwartz vector `v` for `(W, V)` has
a Schwartz vector `v'` for `(W', V')` with this property: for all `z > 0`, the theta integrals over
`[U(V)]` of `cone A X μ z v'` are `B z` times those of `v`. This holds at every adelic point `g` of
`U(W)`, for every character `𝔠` of weight `μ` (all `μ w > 0`) of the norm-one adeles that is tamely
ramified exactly at a non-empty set of split places, containing no place together with its
conjugate, and for every standard datum `stdRowDatum σ 𝔠.semilocalChar y` at these places. -/
theorem exists_thetaLarge_cone_eq_mul [IsBaseAdapted A] [IsBaseAdapted X]
    (μ : InfinitePlace E → ℤ) {b : Type} [Fintype b] [DecidableEq b] (σ : b ⊕ r ≃ n)
    (hn : 2 ∣ card n) :
    ∃ B : ℝ → ℝ, (∀ z : ℝ, 0 < B z) ∧ AnalyticOnNhd ℝ (fun z : ℝ ↦ (B z : ℂ)) Set.univ ∧
      ∀ v : PairFock E s t, IsSchwartzVector v → ∃ v' : PairFock E s' t', IsSchwartzVector v' ∧
        ∀ z > (0 : ℝ), ∀ (𝔠 : SplitTameChar E μ) (y : Matrix b n (LocProd 𝔠.ramifiedPlaces))
          (g : G E s),
          thetaLarge W V 𝔠 (cone A X μ z v') (stdRowDatum σ 𝔠.semilocalChar y) g =
            B z * thetaLarge W V 𝔠 v (stdRowDatum σ 𝔠.semilocalChar y) g := by
  obtain ⟨ρ, hρ, h_image⟩ := exists_coneIntegrand_eq_smul A X μ hn
  refine ⟨fun z ↦ ∫ p, ρ p * ideleAbs (realIdele p.2) ^ z ∂haar.prod haar, hρ.integral_pos,
    fun z _ ↦ ?_, fun v hv ↦ ?_⟩
  · -- A Mellin transform that converges for every exponent is analytic.
    have h_complex (x : ℝ) : Integrable
        (fun p ↦ (ρ p : ℂ) * (ideleAbs (realIdele p.2) ^ x : ℝ)) (haar.prod haar) :=
      mod_cast (hρ.integrable x).ofReal (𝕜 := ℂ)
    obtain ⟨-, -, h_strip⟩ := analyticOnNhd_integral_mul_rpow (fun _ ↦ ideleAbs_pos)
      (continuous_ideleAbs_realIdele.measurable.comp measurable_snd)
      (h_complex (z - 1)).hasFiniteIntegral (h_complex (z + 1))
    simpa only [← integral_complex_ofReal, Complex.ofReal_mul] using h_strip z (by simp)
  -- Exchange the cone integral with the integral over `[U(V)]`, which takes the same value at
  -- `v` and at its translates.
  obtain ⟨v', hv', h_integrand⟩ := h_image v hv
  refine ⟨v', hv', fun z hz 𝔠 y g ↦ ?_⟩
  let Φ : Matrix r n (LocProd 𝔠.ramifiedPlaces) → ℂ := stdRowDatum σ 𝔠.semilocalChar y
  have h_inner (p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ) :
      ∫ h, coneKernel 𝔠 A X σ v' y g true z (h, p) ∂V.quotMeasure =
        (ρ p * ideleAbs (realIdele p.2) ^ z) • thetaLarge W V 𝔠 v Φ g := by
    obtain ⟨h, h_eq⟩ : ∃ h : GInf E t, coneIntegrand A X μ true z v' p =
        (ρ p * ideleAbs (realIdele p.2) ^ z) • realPairWeil (targetWeight n μ) 0 (1, h) v :=
      h_integrand z p.1 p.2
    simp only [coneKernel, h_eq, ContinuousLinearMap.map_smul_of_tower, integral_smul,
      integral_stdKernelForm, thetaLarge_realPairWeil, Φ]
  calc _ = ∫ p, coneKernel 𝔠 A X σ v' y g true z p ∂V.quotMeasure.prod (haar.prod haar) :=
      (integral_coneKernel A X y g true hv' hz).symm
    _ = ∫ p, (ρ p * ideleAbs (realIdele p.2) ^ z) • thetaLarge W V 𝔠 v Φ g ∂haar.prod haar := by
      rw [integral_prod_symm _ (integrable_coneKernel A X y g true hv' hz), funext h_inner]
    _ = (∫ p, ρ p * ideleAbs (realIdele p.2) ^ z ∂haar.prod haar : ℝ) * thetaLarge W V 𝔠 v Φ g := by
      rw [integral_smul_const, Complex.real_smul]

/-- Let the splittings `A` and `X` be adapted, the rank of `W` even and `0 < z`, and let `σ`
identify `b ⊕ r` with the index set of `W`. Each Schwartz vector `v` for `(W, V)` has a Schwartz
vector `v'` for `(W', V')` such that the cone integral `cone A X μ z v'` and `v` have the same theta
integrals over `[U(V)]`, at every adelic point `g` of `U(W)`. This holds for every split tame
character `𝔠` of weight `μ`, that is a character of the norm-one adeles, tamely ramified exactly at
a non-empty set of split places that contains no place together with its conjugate, and for every
standard datum `stdRowDatum σ 𝔠.semilocalChar y` at these places: the function that sends `x` to
`𝔠.semilocalChar⁻¹` of the determinant of the matrix with rows `y` and `x`, ordered by `σ`, if that
matrix is integrally invertible, and to zero otherwise. -/
theorem exists_thetaLarge_cone_eq [IsBaseAdapted A] [IsBaseAdapted X] (μ : InfinitePlace E → ℤ)
    {b : Type} [Fintype b] [DecidableEq b] (σ : b ⊕ r ≃ n) (hn : 2 ∣ card n) {z : ℝ} (hz : 0 < z)
    {v : PairFock E s t} (hv : IsSchwartzVector v) :
    ∃ v' : PairFock E s' t', IsSchwartzVector v' ∧
      ∀ (𝔠 : SplitTameChar E μ) (y : Matrix b n (LocProd 𝔠.ramifiedPlaces)) (g : G E s),
        thetaLarge W V 𝔠 (cone A X μ z v') (stdRowDatum σ 𝔠.semilocalChar y) g =
          thetaLarge W V 𝔠 v (stdRowDatum σ 𝔠.semilocalChar y) g := by
  -- Apply `exists_thetaLarge_cone_eq_mul` to `(B z)⁻¹ • v`.
  obtain ⟨B, hB, -, h_image⟩ := exists_thetaLarge_cone_eq_mul A X μ σ hn
  have hB_ne : (B z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hB z).ne'
  have h_schwartz : IsSchwartzVector ((B z : ℂ)⁻¹ • v) := fun N ↦ by
    simpa only [fockMoment_smul] using ENNReal.mul_ne_top enorm_ne_top (hv N)
  obtain ⟨v', hv', h_cone⟩ := h_image ((B z : ℂ)⁻¹ • v) h_schwartz
  refine ⟨v', hv', fun 𝔠 y g ↦ ?_⟩
  calc _ = B z * thetaLarge W V 𝔠 ((B z : ℂ)⁻¹ • v) (stdRowDatum σ 𝔠.semilocalChar y) g :=
         h_cone z hz 𝔠 y g
    _ = thetaLarge W V 𝔠 v (stdRowDatum σ 𝔠.semilocalChar y) g := by
      simp only [← integral_stdKernelForm, map_smul, smul_eq_mul, integral_const_mul,
        mul_inv_cancel_left₀ hB_ne]

end New.Exchange

end
