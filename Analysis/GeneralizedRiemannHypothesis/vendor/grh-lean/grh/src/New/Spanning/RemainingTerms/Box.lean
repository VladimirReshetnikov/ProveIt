import Lib.Adelic.Adeles.SemilocalProducts
import New.Spanning.Unfolding.Setup

/-!
# The box

Let `S : Filling E 𝔰` be admissible data for a CM field `E` and a shape `𝔰`, with `M = S.M` the
level and `b = S.b`. Consider the tuples of complex numbers, one for each infinite place, modulo
`M 𝓞_E`, and fix a measurable set `D` of representatives, each coordinate of each point of `D`
having modulus at most `b ^ 26`.

An archimedean point `y` is reduced if the entries above the diagonal of its triangular matrix
`S.ratTriangle y` lie in `D`. It is boxed if it is reduced and lies in the cut at every place `v`,
that is, `besselLength (y v) ≤ b ^ (6 n + 2)`, where `n = 𝔰.n = 𝔰.ϱ + 1`.

Notions from other files:
* `frameVector z a`: for `z` in `𝔰.G₁`, the image of the `a`-th frame vector under `z⁻¹`;
  `orthoFrame z` is the result of the Gram–Schmidt process on these vectors.
* `gramSchmidtMatrix z`: the unitriangular matrix of the coefficients of `frameVector z` in
  `orthoFrame z`; `S.ratTriangle` reads it in the rational frame.
* `besselLength z`: the infimum of `‖s * z‖ + 1` over `s` in the Bessel subgroup.
* `frameBox r`: the points at which all frame vectors have length at most `r`.

## Main definitions and results

* `New.Filling.exists_isResidueDomain`: such a set `D` exists.
* `New.Filling.boxedPoints`: the boxed points.
* `New.Filling.mul_mem_boxedPoints_iff`: invariance under the unipotent elements fixing the frame.
* `New.Filling.mem_frameBox_of_mem_boxedPoints`: at a boxed point the frame vectors have length at
  most `b ^ (37 n)`.
-/

open NumberField Matrix Set ENNReal

namespace New.Filling

/-- Let `V` be an abelian group and a standard Borel space with measurable translations. Let `L` be
a countable subgroup and `B` a measurable set that meets every coset of `L` in a finite nonempty
set. Then `B` contains a measurable set of representatives of the cosets. -/
lemma _root_.New.exists_measurableSet_existsUnique_add_mem {V : Type*} [AddCommGroup V]
    [MeasurableSpace V] [StandardBorelSpace V] [MeasurableAdd V] (L : AddSubgroup V) [Countable L]
    {B : Set V} (hB : MeasurableSet B) (h_nonempty : ∀ w : V, ∃ l : L, l.val + w ∈ B)
    (h_finite : ∀ w : V, {l : L | l.val + w ∈ B}.Finite) :
    ∃ D ⊆ B, MeasurableSet D ∧ ∀ w : V, ∃! l : L, l.val + w ∈ D := by
  -- In each coset take the point of `B` at which a measurable injection `f` to `ℝ` is least.
  let f : V → ℝ := MeasureTheory.embeddingReal V
  have hf : MeasurableEmbedding f := MeasureTheory.measurableEmbedding_embeddingReal V
  let least (l : L) : Set V := {w : V | l.val + w ∈ B → f w ≤ f (l.val + w)}
  have h_meas (l : L) : MeasurableSet (least l) :=
    .imp (measurable_const_add _ hB)
      (measurableSet_le hf.measurable (hf.measurable.comp (measurable_const_add _)))
  refine ⟨B ∩ ⋂ l : L, least l, inter_subset_left, hB.inter (.iInter h_meas), fun w ↦ ?_⟩
  obtain ⟨l₀, hl₀, h_least⟩ : ∃ l₀ : L, l₀.val + w ∈ B ∧
      ∀ l : L, l.val + w ∈ B → f (l₀.val + w) ≤ f (l.val + w) :=
    exists_min_image {l : L | l.val + w ∈ B} (fun l : L ↦ f (l.val + w)) (h_finite w)
      (h_nonempty w)
  refine ⟨l₀, ⟨hl₀, mem_iInter.2 fun l hl ↦ ?_⟩, ?_⟩
  · -- `l₀ + w` is least in its coset.
    show f (l₀.val + w) ≤ f (l.val + (l₀.val + w))
    rw [← add_assoc, ← AddSubgroup.coe_add] at hl ⊢
    exact h_least (l + l₀) hl
  · -- Any least point of the coset has the same value of `f`.
    rintro l ⟨hl, hl_least⟩
    have h_least_l : (l₀ - l).val + (l.val + w) ∈ B →
        f (l.val + w) ≤ f ((l₀ - l).val + (l.val + w)) :=
      mem_iInter.1 hl_least (l₀ - l)
    rw [AddSubgroup.coe_sub, ← add_assoc, sub_add_cancel] at h_least_l
    have h_eq : l.val + w = l₀.val + w :=
      hf.injective ((h_least_l hl₀).antisymm (h_least l hl))
    exact Subtype.ext (add_right_cancel h_eq)

/-- Few integral vectors have bounded conjugates. If `f` maps `A` injectively to vectors in `E^ι`
whose entries are algebraic integers of absolute value at most `r` under the embedding `Φ v` of
every infinite place `v` (chosen by the instance `PlaceEmbedding E`), then `A` has at most
`(1 + 2 r) ^ (2 |ι| m)` elements, where `m = Core.numInfPlaces E` is the number of infinite
places. -/
lemma encard_le_of_isIntegral_norm_le {α ι E : Type*} [Fintype ι] {A : Set α} [Field E]
    [NumberField E] [PlaceEmbedding E] {r : ℝ} (f : α → ι → E) (hr : 0 ≤ r)
    (hf : ∀ a ∈ A, ∀ i : ι, IsIntegral ℤ (f a i) ∧ ∀ v : InfinitePlace E, ‖Φ v (f a i)‖ ≤ r)
    (h_inj : InjOn f A) :
    A.encard ≤ ENNReal.ofReal ((1 + 2 * r) ^ (Fintype.card ι * Core.numInfPlaces E * 2)) := by
  -- Embed `A` in `ℂ ^ (ι × places)`, a real space of dimension `card ι * Core.numInfPlaces E * 2`.
  -- The image lies in the ball of radius `r` and its points are at distance at least `1`.
  let F (a : α) (p : ι × InfinitePlace E) : ℂ := Φ p.2 (f a p.1)
  have h_separated : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → 1 ≤ ‖F a - F b‖ := by
    -- An algebraic integer whose conjugates all have absolute value below `1` is zero.
    intro a ha b hb hab
    by_contra! h_close
    have h_ne : f a ≠ f b := fun h_eq ↦ hab (h_inj ha hb h_eq)
    refine h_ne (funext fun i ↦ eq_of_sub_eq_zero ?_)
    have h_integral : IsIntegral ℤ (f a i - f b i) := (hf a ha i).left.sub (hf b hb i).left
    refine eq_zero_of_forall_norm_lt_one h_integral fun v ↦ ?_
    have h_lt : ‖(F a - F b) (i, v)‖ < 1 := (norm_le_pi_norm _ (i, v)).trans_lt h_close
    simpa [F] using h_lt
  have h_bounded : ∀ a ∈ A, ‖F a‖ ≤ r := fun a ha ↦
    (pi_norm_le_iff_of_nonneg hr).2 fun p ↦ (hf a ha p.1).right p.2
  -- The packing bound: `1`-separated points in a ball of radius `r` number at most
  -- `(1 + 2 r) ^ dim`.
  grw [encard_le_of_separated one_pos hr h_separated h_bounded]
  simp [Module.finrank_pi_fintype]

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
  {D : Set (InfinitePlace E → ℂ)}

/-- A tuple of complex numbers, one for each infinite place, lies in `S.levelMultiples`, the
multiples of the level `M = S.M`, if and only if it consists of the images of `M x` for an integer
`x` of `E`. -/
lemma mem_levelMultiples {w : InfinitePlace E → ℂ} :
    w ∈ S.levelMultiples ↔ ∃ x : 𝓞 E, (fun v : InfinitePlace E ↦ Φ v (S.M * (x : E))) = w :=
  .rfl

/-- Let `S : Filling E 𝔰`, the data of the filling theorem, satisfy the standing hypotheses
`S.IsAdmissible`. For `r ≥ 0` and a tuple `w` over the infinite places, only finitely many `l` in
`S.levelMultiples` make all coordinates of `l + w` have modulus at most `r`. Here `S.levelMultiples`
is the set of tuples `M x`, where `x` is an integer of `E` and `M = S.M` is the level. -/
lemma finite_setOf_levelMultiples_add_le [S.IsAdmissible] {r : ℝ} (hr : 0 ≤ r)
    (w : InfinitePlace E → ℂ) :
    {l : S.levelMultiples | ∀ v : InfinitePlace E, ‖(l.val + w) v‖ ≤ r}.Finite := by
  have h_integer (l : S.levelMultiples) :
      ∃ x : 𝓞 E, (fun v : InfinitePlace E ↦ Φ v (S.M * (x : E))) = l.val :=
    mem_levelMultiples.1 l.property
  choose x hx using h_integer
  let A : Set S.levelMultiples := {l | ∀ v : InfinitePlace E, ‖(l.val + w) v‖ ≤ r}
  let f (l : S.levelMultiples) (_ : Unit) : E := S.M * (x l : E)
  have h_bound : ∀ l ∈ A, ∀ i : Unit,
      IsIntegral ℤ (f l i) ∧ ∀ v : InfinitePlace E, ‖Φ v (f l i)‖ ≤ r + ‖w‖ := by
    refine fun l hl i ↦ ⟨(isIntegral_natCast _).mul (x l).isIntegral_coe, fun v ↦ ?_⟩
    change ‖Φ v (S.M * (x l : E))‖ ≤ r + ‖w‖
    rw [congrFun (hx l) v, ← add_sub_cancel_right (l.val v) (w v)]
    exact norm_sub_le_of_le (hl v) (norm_le_pi_norm w v)
  have h_inj : InjOn f A := by
    intro l _ l' _ h_eq
    have h_mul : S.M * (x l : E) = S.M * (x l' : E) := congrFun h_eq ()
    ext1
    rw [← hx l, ← hx l', h_mul]
  have h_lt_top : (A.encard : ℝ≥0∞) < ⊤ :=
    (encard_le_of_isIntegral_norm_le f (by positivity) h_bound h_inj).trans_lt ofReal_lt_top
  exact encard_lt_top_iff.1 (mod_cast h_lt_top)

variable (S) in
/-- Let `S : Filling E 𝔰`, the data of the filling theorem over `E`, satisfy the standing hypotheses
`S.IsAdmissible`, which bound the data by powers of `b = S.b`. Then there is a set `D` with
`S.IsResidueDomain D`: a measurable set of representatives for the tuples of complex numbers, one
for each infinite place, modulo `M 𝓞_E`. -/
lemma exists_isResidueDomain [S.IsAdmissible] :
    ∃ D : Set (InfinitePlace E → ℂ), S.IsResidueDomain D := by
  have hb : 1000 ≤ S.b := S.thousand_le_b
  have : Countable (𝓞 E) := RingOfIntegers.coe_injective.countable
  have : Countable S.levelMultiples := (countable_range _).to_subtype
  let B : Set (InfinitePlace E → ℂ) :=
    {w : InfinitePlace E → ℂ | ∀ v : InfinitePlace E, ‖w v‖ ≤ S.b ^ 26}
  -- Every tuple is within `M (2 f) ^ 2 |ϖ| ≤ b ^ 26` of a tuple in `S.levelMultiples`, where
  -- `M = S.M` is the level, `ϖ = S.deltaE` and `f = numInfPlaces E`.
  have h_nonempty (w : InfinitePlace E → ℂ) : ∃ l : S.levelMultiples, l.val + w ∈ B := by
    have h_ne : S.deltaE ≠ 0 := mod_cast S.deltaE_ne_zero
    have h_different : S.deltaE ∈ differentIdeal ℤ (𝓞 E) := by simp [S.span_deltaE]
    obtain ⟨a, ha_int, ha_near⟩ : ∃ a : E, 0 - algebraMap E (𝔸f E) a ∈ Ô E ∧
        ∀ v : InfinitePlace E, ‖-w v / S.M - Φ v a‖ ≤ (2 * numInfPlaces E) ^ 2 * ‖Φ v S.deltaE‖ :=
      exists_principal_near_of_mem_differentIdeal h_ne h_different (fun v ↦ -w v / S.M) 0
    rw [zero_sub, neg_mem_iff, algebraMap_mem_Ô] at ha_int
    let l : S.levelMultiples :=
      ⟨fun v ↦ Φ v (S.M * a), mem_levelMultiples.2 ⟨⟨a, ha_int⟩, rfl⟩⟩
    refine ⟨l, fun v ↦ ?_⟩
    have hM_ne : (S.M : ℂ) ≠ 0 := by simp [Nat.Prime.ne_zero]
    have h_places : 2 * (numInfPlaces E : ℝ) ≤ S.b := by linarith [S.numInfPlaces_le_div]
    calc ‖Φ v (S.M * a) + w v‖ = ‖(S.M : ℂ)‖ * ‖-w v / S.M - Φ v a‖ := by
          rw [← norm_mul, ← norm_neg, map_mul, map_natCast]
          congr 1
          field
      _ ≤ S.b ^ 23 * (S.b ^ 2 * S.b) := by
          grw [ha_near, RCLike.norm_natCast, M_le_b_pow, IsAdmissible.norm_deltaE_le, h_places]
      _ = S.b ^ 26 := by ring
  -- Only finitely many integers have bounded conjugates.
  have h_finite (w : InfinitePlace E → ℂ) : {l : S.levelMultiples | l.val + w ∈ B}.Finite :=
    finite_setOf_levelMultiples_add_le (by positivity) w
  have hB : MeasurableSet B := by measurability
  obtain ⟨D, hDB, hD_meas, hD⟩ : ∃ D ⊆ B, MeasurableSet D ∧
      ∀ w : InfinitePlace E → ℂ, ∃! l : S.levelMultiples, l.val + w ∈ D :=
    exists_measurableSet_existsUnique_add_mem S.levelMultiples hB h_nonempty h_finite
  exact ⟨D, { measurableSet := hD_meas, norm_le := fun w v hw ↦ hDB hw v,
              existsUnique_add_mem := hD }⟩

/-- For any set `D` of tuples over the infinite places, let `S.reducedPoints D` be the set of points
whose matrix has all its entries above the diagonal in `D`. This set is left invariant by the fixer
`besselFixer` of the frame, the elements fixing each frame vector: if every `s v` lies in
`besselFixer`, then `s * y` is in `S.reducedPoints D` if and only if `y` is. -/
lemma mul_mem_reducedPoints_iff {s y : InfinitePlace E → 𝔰.G₁}
    (hs : ∀ v : InfinitePlace E, s v ∈ besselFixer) :
    s * y ∈ S.reducedPoints D ↔ y ∈ S.reducedPoints D := by
  have h_triangle : S.ratTriangle (s * y) = S.ratTriangle y := by
    funext a b v
    simp only [ratTriangle, gramSchmidtMatrix, orthoFrame, Pi.mul_apply,
      frameVector_mul_of_mem_besselFixer (hs v)]
  simp only [reducedPoints, mem_ofPred_eq, h_triangle]

variable (S) in
/-- The boxed points: the archimedean points `y` that are reduced for a chosen set satisfying
`New.Filling.IsResidueDomain` (one exists for admissible data) and lie in the cut at every infinite
place `v`, that is, `besselLength (y v) ≤ S.b ^ (6 * 𝔰.n + 2)`. -/
def boxedPoints : Set (InfinitePlace E → 𝔰.G₁) :=
  {y ∈ S.reducedPoints (Classical.epsilon S.IsResidueDomain) |
    ∀ v : InfinitePlace E, InCut (y v) S.b}

/-- A boxed point `y` lies in the cut at every infinite place `v`, that is,
`besselLength (y v) ≤ S.b ^ (6 * 𝔰.n + 2)`. -/
lemma inCut_of_mem_boxedPoints {y : InfinitePlace E → 𝔰.G₁} (hy : y ∈ S.boxedPoints)
    (v : InfinitePlace E) : InCut (y v) S.b :=
  hy.2 v

/-- If `S.reducedIndicator`, the indicator of the reduced points for the chosen set of
representatives, is nonzero at `y` and `y` lies in the cut at every infinite place
(`besselLength (y v) ≤ S.b ^ (6 * 𝔰.n + 2)`), then `y` is boxed. -/
lemma mem_boxedPoints_of_reducedIndicator_ne_zero {y : InfinitePlace E → 𝔰.G₁}
    (hy : S.reducedIndicator y ≠ 0) (h_cut : ∀ v : InfinitePlace E, InCut (y v) S.b) :
    y ∈ S.boxedPoints :=
  ⟨mem_of_indicator_ne_zero hy, h_cut⟩

/-- The group `New.Shape.Form.besselU0` consists of the elements of the Bessel unipotent group
`besselU` that fix each frame vector. If every component of `u` lies in `besselU0`, then `u * y` is
boxed if and only if `y` is. -/
lemma mul_mem_boxedPoints_iff {y u : InfinitePlace E → 𝔰.G₁}
    (hu : ∀ v : InfinitePlace E, u v ∈ besselU0) :
    u * y ∈ S.boxedPoints ↔ y ∈ S.boxedPoints := by
  have h_besselLength (v : InfinitePlace E) : besselLength (u v * y v) = besselLength (y v) := by
    obtain ⟨hu_unipotent, -⟩ := Subgroup.mem_inf.1 (hu v)
    exact besselLength_besselS_mul (mem_partialUnitriangularGroup_of_mem_besselU hu_unipotent)
  simp [boxedPoints, mul_mem_reducedPoints_iff fun v ↦ mem_besselFixer_of_mem_besselU0 (hu v),
    h_besselLength]

/-- On and below the diagonal, at every infinite place, the matrix `S.ratTriangle y` (the triangular
matrix of the frame at `y`, read in the rational frame) agrees with the identity matrix. -/
lemma ratTriangle_eq_one_apply_of_le (y : InfinitePlace E → 𝔰.G₁) {row col : Fin (𝔰.ϱ + 1)}
    (h_col_le_row : col ≤ row) (v : InfinitePlace E) :
    S.ratTriangle y row col v = (1 : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) ℂ) row col := by
  rw [ratTriangle, gramSchmidtMatrix, RealPlace.unitriangularMatrix, of_apply,
    dite_eq_right h_col_le_row.not_gt, one_apply]
  split_ifs with h_diagonal
  · rw [h_diagonal, div_self (S.basisScale_ne_zero v _), mul_one]
  · rw [zero_mul]

/-- If `D` is a set of representatives modulo `S.M 𝓞_E` as in `New.Filling.IsResidueDomain`, in
particular measurable, then the set of points whose triangular matrix has its entries above the
diagonal in `D` is measurable. -/
lemma IsResidueDomain.measurableSet_reducedPoints (hD : S.IsResidueDomain D) :
    MeasurableSet (S.reducedPoints D) := by
  have h_entry (a b : Fin (𝔰.ϱ + 1)) :
      Measurable fun y : InfinitePlace E → 𝔰.G₁ ↦ S.ratTriangle y a b :=
    measurable_pi_iff.2 fun v ↦
      ((measurable_gramSchmidtMatrix a b).comp (measurable_pi_apply v)).mul_const _
  simp only [reducedPoints, ofPred_forall]
  exact .iInter fun a ↦ .iInter fun b ↦ .iInter fun _ ↦ h_entry a b hD.measurableSet

/-- At an infinite place `v` the scale `S.basisScale v` of the normalised basis is
`κ_v ^ (ϱ - a) / √N` at the `a`-th frame vector `𝔰.besselFrame a`. Here `ϱ = 𝔰.ϱ` is the number of
hyperbolic planes, `N = S.N` is the prime of the data, and `κ_v = S.realM v` is the real number
`S.M * Φ v S.deltaE / (2 π i)`. For admissible `S` one has `1 ≤ |κ_v|`, so the scale does not grow
along the frame: for `a ≤ b` the scale at `b` divided by the scale at `a` has modulus at most
one. -/
lemma norm_basisScale_div_le_one [S.IsAdmissible] (v : InfinitePlace E) {a b : Fin (𝔰.ϱ + 1)}
    (hab : a ≤ b) :
    ‖S.basisScale v (𝔰.besselFrame b) / S.basisScale v (𝔰.besselFrame a)‖ ≤ 1 := by
  simp only [basisScale_besselFrame, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have h_pow : |S.realM v| ^ (𝔰.ϱ - (b : ℕ)) ≤ |S.realM v| ^ (𝔰.ϱ - (a : ℕ)) :=
    pow_le_pow_right₀ (IsAdmissible.one_le_abs_realM v) (Nat.sub_le_sub_left hab 𝔰.ϱ)
  refine div_le_one_of_le₀ ?_ (by positivity)
  gcongr

/-- Let `S` be admissible and `D` a measurable set of representatives modulo `S.M 𝓞_E` whose points
have modulus at most `S.b ^ 26` at every place. If `y` is reduced for `D`, that is, the entries
above the diagonal of `S.ratTriangle y` lie in `D`, then all entries of `gramSchmidtMatrix (y v)`
have modulus at most `S.b ^ 26`. -/
lemma IsResidueDomain.norm_gramSchmidtMatrix_le [S.IsAdmissible] (hD : S.IsResidueDomain D)
    {y : InfinitePlace E → 𝔰.G₁} (hy : y ∈ S.reducedPoints D) (v : InfinitePlace E)
    (a b : Fin (𝔰.ϱ + 1)) : ‖gramSchmidtMatrix (y v) a b‖ ≤ S.b ^ 26 := by
  have h_scale : gramSchmidtMatrix (y v) a b = S.ratTriangle y a b v *
      (S.basisScale v (𝔰.besselFrame b) / S.basisScale v (𝔰.besselFrame a)) := by
    rw [ratTriangle, mul_assoc, div_mul_div_cancel₀ (S.basisScale_ne_zero v _),
      div_self (S.basisScale_ne_zero v _), mul_one]
  rw [h_scale]
  obtain hab | rfl | hba : a < b ∨ a = b ∨ b < a := lt_trichotomy a b
  · grw [norm_mul, norm_basisScale_div_le_one v hab.le, mul_one, hD.norm_le _ v (hy a b hab)]
  · simp [ratTriangle_eq_one_apply_of_le y le_rfl, one_le_pow₀ S.one_le_b]
  · simp [ratTriangle_eq_one_apply_of_le y hba.le, hba.ne',
    pow_nonneg (zero_le_one.trans S.one_le_b)]

/-- Let `S` be admissible, let `D` be a measurable set of representatives modulo `S.M 𝓞_E`, the
points of `D` having modulus at most `S.b ^ 26` at every place, and let `y` be reduced for `D`: the
entries of the triangular matrix `S.ratTriangle y` above the diagonal lie in `D`. Then at every
infinite place `v` the point `y v` is in the `frameBox` of radius
`S.b ^ 27 * besselLength (y v)`. -/
lemma IsResidueDomain.mem_frameBox [S.IsAdmissible] (hD : S.IsResidueDomain D)
    {y : InfinitePlace E → 𝔰.G₁} (hy : y ∈ S.reducedPoints D) (v : InfinitePlace E) :
    y v ∈ frameBox (S.b ^ 27 * besselLength (y v)) := by
  -- A frame vector is a sum of `ϱ + 1 ≤ b` orthogonal vectors, each no longer than the Bessel
  -- length, with coefficients of modulus at most `b ^ 26`.
  intro (l : Fin (𝔰.ϱ + 1))
  show ‖frameVector (y v) l‖ ≤ S.b ^ 27 * besselLength (y v)
  have hb_pos : 0 < S.b := zero_lt_one.trans_le S.one_le_b
  have h_besselLength_nonneg : 0 ≤ besselLength (y v) := besselLength_nonneg (y v)
  have h_term (a : Fin (𝔰.ϱ + 1)) :
      ‖gramSchmidtMatrix (y v) a l • orthoFrame (y v) a‖ ≤ S.b ^ 26 * besselLength (y v) := by
    have h_ortho : ‖orthoFrame (y v) a‖ ≤ besselLength (y v) :=
      (norm_orthoFrame_mem_Icc (y v) a le_rfl).right
    grw [norm_smul, hD.norm_gramSchmidtMatrix_le hy, h_ortho]
  calc ‖frameVector (y v) l‖
    _ = ‖∑ a : Fin (𝔰.ϱ + 1), gramSchmidtMatrix (y v) a l • orthoFrame (y v) a‖ := by
      rw [← frameVector_eq_sum_orthoFrame]
    _ ≤ ∑ _ : Fin (𝔰.ϱ + 1), S.b ^ 26 * besselLength (y v) :=
      norm_sum_le_of_le _ fun a _ ↦ h_term a
    _ = ↑(𝔰.ϱ + 1) * (S.b ^ 26 * besselLength (y v)) := by simp
    _ ≤ S.b * (S.b ^ 26 * besselLength (y v)) := by grw [S.succ_le_b]
    _ = S.b ^ 27 * besselLength (y v) := by ring

/-- Let `S` be admissible, that is, satisfy the standing hypotheses `New.Filling.IsAdmissible`,
`n = 𝔰.n`, and let `y` be boxed: the entries above the diagonal of `S.ratTriangle y` lie in the set
of representatives modulo `S.M 𝓞_E` chosen in `S.boxedPoints`, and
`besselLength (y v) ≤ S.b ^ (6 n + 2)` at every infinite place `v`, where `besselLength g` is the
infimum of `‖s * g‖ + 1` over `s` in the Bessel subgroup `besselS` of `𝔰.G₁`. Then `y v` lies in the
`frameBox` of radius `S.frameBoxRadius = S.b ^ (37 n)`. -/
lemma mem_frameBox_of_mem_boxedPoints [S.IsAdmissible] {y : InfinitePlace E → 𝔰.G₁}
    (hy : y ∈ S.boxedPoints) (v : InfinitePlace E) : y v ∈ frameBox S.frameBoxRadius := by
  have hy_reduced : y ∈ S.reducedPoints (Classical.epsilon S.IsResidueDomain) := hy.left
  have hy_cut : besselLength (y v) ≤ S.b ^ (6 * 𝔰.n + 2) := inCut_of_mem_boxedPoints hy v
  intro (a : Fin (𝔰.ϱ + 1))
  show ‖frameVector (y v) a‖ ≤ S.frameBoxRadius
  have hb : 1 ≤ S.b := S.one_le_b
  have hD : S.IsResidueDomain (Classical.epsilon S.IsResidueDomain) :=
    Classical.epsilon_spec S.exists_isResidueDomain
  -- The norm is at most `b ^ 27 * b ^ (6 n + 2) ≤ b ^ (37 n)`.
  grw [hD.mem_frameBox hy_reduced v a, hy_cut, frameBoxRadius, ← pow_add]
  exact pow_le_pow_right₀ hb (by lia)

/-- For admissible data the set of boxed points is measurable. -/
lemma measurableSet_boxedPoints [S.IsAdmissible] : MeasurableSet S.boxedPoints := by
  have hD : S.IsResidueDomain (Classical.epsilon S.IsResidueDomain) :=
    Classical.epsilon_spec S.exists_isResidueDomain
  refine hD.measurableSet_reducedPoints.inter ?_
  change MeasurableSet {y : InfinitePlace E → 𝔰.G₁ | ∀ v, besselLength (y v) ≤ S.b ^ (6 * 𝔰.n + 2)}
  measurability

end New.Filling
