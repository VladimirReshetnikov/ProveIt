import Lib.Adelic.Reduction.FiniteVolume
import Lib.Adelic.Reduction.FirstMinimumShortBases

/-!
# Mahler's criterion for hermitian spaces and class sums for definite spaces

For a hermitian space `V : New.Space E n s`, the rational unitary group embeds in the adelic unitary
group `New.G E s` with image `V.Γ`, and in its finite part with image `V.Γf`. Mahler's criterion
follows from short bases, whose Gram matrices take finitely many values. It gives compactness modulo
the rational points when all signs agree. For the signs `1`, it also gives finiteness of classes.
For such a space, the integral over `Γ \ G` of a suitable invariant function is then a class
sum. Here `K₀` is `New.stdLevel`, and `New.classSum` sums over the double cosets `Γf \ G_f / K` with
weights `1 / #(Γf ∩ g K g⁻¹)`.

## Main definitions and results

* `New.Space.mahler_criterion`: Mahler's criterion; the `g` of bounded height lie in `V.Γ * C` for
  one compact set `C`.
* `New.Space.isCocompact_of_definite`: if all signs agree, the adelic group is compact modulo
  `V.Γ`. `New.Space.isCocompact_Gamma` is the case of the signs `1`.
* `New.Space.isCocompact_finitePart`: for the signs `1`, the finite part of the group is
  compact modulo `V.Γf`.
* `New.Space.hasFiniteType_of_isLevel`: for the signs `1`, finitely many classes with finite
  stabilisers.
* `New.Space.integral_quotMeasure_eq_classSum`: take a space with signs `1` and a continuous, left
  `Γ`-invariant function on `G`. Suppose that its average over the infinite places is fixed under
  right translation by an open `K ≤ K₀`. Then its integral over `Γ \ G` is `[K₀ : K]⁻¹` times the
  class sum of this average. `New.Space.classIntegral_eq_integral` is the case of functions of the
  finite part.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to diag(s), with s the signs, at the infinite places and 1 at the finite places.
* `New.Space.move`: the space `V.move g` is the space with the same J and the point x g; its lattice
  `baseLattice` is the lattice at `g`, and the norm of `archCoords u` is the length of u at `g`.
* `New.Space.height`: the height ht(g) = 1/λ, with λ the first minimum cut off at 1
  (`New.Space.firstMinimum`) of the moved space `V.move g`.
* `New.IsLevel`: an open subgroup of `K₀`, with index `New.stdLevelIndex` in `K₀`.

## Relation to the literature

Known; see `Lib.Adelic.Reduction.FiniteVolume` and `Lib.Adelic.QuotientMeasure.Basic` for sources.
-/

/-!
## Mahler compactness, and finiteness of classes in the definite case

`V` is a matrix `J` over `E` with an adelic point `x`. `New.G E s` is the unitary group of the
standard form. `V.ratEmbed γ = x⁻¹ γ x` embeds `U(J)(E)` in it with image `V.Γ` (finite parts:
`V.Γf`), and `V.toRatCoords g = x g x⁻¹`.
-/

section MahlerSpace

open Matrix NumberField QuotientGroup PiLp ConjAct
open scoped Pointwise

namespace New.Space

variable {E : Type*} [Field E] [CMType E]
  {n : Type*} [Fintype n] [DecidableEq n] {s : n → ℤˣ} (V : Space E n s)

/-- For a hermitian space `V` with a point, there is a constant `c` such that for every `g` in
`G E s` some basis of `Eⁿ`, the columns of `Y`, lies in `(V.move g).latticeBall (c * V.height g)`.
That is, each column is a vector of the base lattice of the moved space `V.move g` (the same form
with the point `V.x * g`) whose length `‖archCoords y‖` in that space is at most `c * V.height g`.
Here `V.height g = 1 / λ`, where `λ` is the first minimum of `V.move g` cut off at `1`. -/
lemma exists_short_basis_matrix :
    ∃ c : ℕ, ∀ g : G E s, ∃ Y : GL n E, ∀ j : n,
      Y.val.col j ∈ (V.move g).latticeBall (c * V.height g) :=
  ⟨shortBasisConst E n (Ideal.absNorm (differentIdeal ℤ (𝓞 E))),
    fun g ↦ (V.move g).exists_short_basis (Ideal.absNorm_mem (differentIdeal ℤ (𝓞 E)))⟩

/-- Points with a bounded rational frame from `H` are compact modulo the rational isometries in `H`:
for a compact set `C` of adelic matrices and a subgroup `H` of `GL n E` there is a compact
`K ⊆ G E s` such that, whenever `x g⁻¹ x⁻¹ r ∈ C` for some `r ∈ H` (`x` the point of `V`,
`V.toRatCoords g = x g x⁻¹`, `toAdele` embeds `E` in its adeles), some element `γ` of the group
`U V.J` of rational isometries lies in `H` and has `V.ratEmbed γ * g ∈ K`. -/
lemma exists_isCompact_of_bounded_frame {C : Set (Matrix n n (𝔸 E))} (hC : IsCompact C)
    (H : Subgroup (GL n E)) :
    ∃ K : Set (G E s), IsCompact K ∧
      ∀ (g : G E s) (r : H),
        (V.toRatCoords g⁻¹ : GL n (𝔸 E)).val * (r : GL n E).val.map toAdele ∈ C →
        ∃ γ : U V.J, V.ratEmbed γ * g ∈ K ∧ γ.val ∈ H := by
  -- The Gram matrix `gram r` takes finitely many values on the `r` with `x g⁻¹ x⁻¹ r ∈ C`. For
  -- each value `T` fix one `rep T ∈ H`; then `γ = rep (gram r) r⁻¹` is a rational isometry and
  -- `(γ g)⁻¹` lies in `x⁻¹ C (rep T)⁻¹ x`.
  let gram (r : H) : Matrix n n E := r.val.valᴴ * V.J * r.val
  let rep : Matrix n n E → H := gram.invFun
  let gramValues : Set (Matrix n n E) :=
    {T | T.map toAdele ∈ (fun c ↦ cᴴ * V.J.map toAdele * c) '' C}
  -- a compact set of adelic matrices contains finitely many rational ones
  have h_finite : gramValues.Finite :=
    finite_setOf_map_toAdele_mem (hC.image_of_continuous fun c ↦ cᴴ * V.J.map toAdele * c)
  let rightFactor (T : Matrix n n E) : Matrix n n (𝔸 E) :=
    ((rep T : GL n E).val.map toAdele)⁻¹ * V.x.val
  refine ⟨(G.adeleMatrix ⁻¹' ((V.x⁻¹.val • C) * rightFactor '' gramValues))⁻¹,
    (G.isClosedEmbedding_adeleMatrix.isCompact_preimage
      ((hC.smul V.x⁻¹.val).mul (h_finite.image rightFactor).isCompact)).inv, fun g r hr ↦ ?_⟩
  let c : Matrix n n (𝔸 E) := (V.toRatCoords g⁻¹ : GL n (𝔸 E)).val * r.val.val.map toAdele
  -- `x g⁻¹ x⁻¹` is an isometry of the adelic form, so `c` and `r` have one Gram matrix
  have h_gram_map : cᴴ * V.J.map toAdele * c = (gram r).map toAdele := by
    unfold c
    rw [U.gram_invariant]
    simp [gram]
  let γ : U V.J := ⟨(rep (gram r)).val * r.val⁻¹,
    gram_mul_of_gram_eq (gram.invFun_eq ⟨r, rfl⟩) (gram_inv_of_gram_eq rfl)⟩
  refine ⟨γ, ?_, (rep (gram r) * r⁻¹).prop⟩
  have h_mat : (V.x⁻¹.val • c) * rightFactor (gram r) = (V.ratEmbed γ * g)⁻¹.adeleMatrix := by
    simp [c, γ, rep, rightFactor, ratEmbed, toRatCoords, G.adeleMatrix, mul_assoc, U.map]
  show (V.ratEmbed γ * g)⁻¹.adeleMatrix ∈ (V.x⁻¹.val • C) * rightFactor '' gramValues
  rw [← h_mat]
  exact Set.mul_mem_mul (Set.smul_mem_smul_set hr) (Set.mem_image_of_mem _ ⟨c, hr, h_gram_map⟩)

/-- One half of the Mahler–Godement compactness criterion, for the unitary group of a hermitian
space: for each real `R` there is a compact subset `C` of the adelic unitary group `G E s` such that
every `g` with `V.height g ≤ R` has `γ * g ∈ C` for some `γ` in the group `V.Γ` of rational points
(the elements `x⁻¹γx`, with `x` the point of `V` and `γ` in the rational unitary group of `V.J`).
Here `V.height g = 1/λ`, where `λ` is the first minimum of the moved space `V.move g` cut off at `1`
(`firstMinimum`). -/
lemma mahler_criterion (R : ℝ) :
    ∃ C : Set (G E s), IsCompact C ∧ ∀ g : G E s, V.height g ≤ R → ∃ γ ∈ V.Γ, γ * g ∈ C := by
  -- At a point `g` of height at most `R` the lattice holds a basis `Y` of length at most `c * R`.
  -- So `(x g)⁻¹ Y`, with `x` the point of `V`, lies in a compact box, and `Y` is a bounded rational
  -- frame in the sense of `exists_isCompact_of_bounded_frame`.
  obtain ⟨c, h_short⟩ := V.exists_short_basis_matrix
  let box : Set (Matrix n n (𝔸 E)) := Set.matrix (Metric.closedBall 0 (c * R) ×ˢ Ô E)
  obtain ⟨K, hK, h_frame⟩ := V.exists_isCompact_of_bounded_frame
    ((Core.isCompact_closedBall_prod_integral (c * R)).matrix.smul V.x) ⊤
  refine ⟨K, hK, fun g hg ↦ ?_⟩
  obtain ⟨Y, hY⟩ := h_short g
  have h_box : (V.move g).x⁻¹.val * Y.val.map toAdele ∈ box := fun i j ↦ by
    -- the finite part is integral as the column lies in the lattice; `w` is an infinite place
    refine ⟨?_, (hY j).1 i⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonempty]
    exact fun w ↦ (norm_apply_le ((V.move g).archCoords (Y.val.col j)) (w, i)).trans
      (by grw [(hY j).2, hg])
  have h_frame_eq : V.x • ((V.move g).x⁻¹.val * Y.val.map toAdele) =
      (V.toRatCoords g⁻¹).val.val * Y.val.map toAdele := by
    simp [move, toRatCoords, mul_assoc, Units.smul_def]
  obtain ⟨γ, hγ, -⟩ := h_frame g ⟨Y, Subgroup.mem_top Y⟩ ⟨_, h_box, h_frame_eq⟩
  exact ⟨V.ratEmbed γ, ⟨γ, rfl⟩, hγ⟩

/-- If all signs `s i` are equal (the space is definite), then the adelic unitary group `G E s` is
compact modulo the group `V.Γ` of rational points: there is a compact `C` such that every `g` has
`γ * g ∈ C` for some `γ ∈ V.Γ`. The hypothesis `h_definite` may be omitted when `simp` proves it,
as for constant `s`.

A special case of the compactness theorem for anisotropic groups (Borel–Harish-Chandra,
Mostow–Tamagawa), part of the reduction theory. -/
lemma isCocompact_of_definite (h_definite : ∀ i j : n, s i = s j := by simp) :
    V.Γ.IsCocompact := by
  obtain ⟨C, hC, h_cover⟩ := V.mahler_criterion 1
  -- In a definite space all heights are `1`.
  refine ⟨C, hC, fun g ↦ h_cover g ?_⟩
  simp [height, firstMinimum_move_eq_one h_definite]

/-- If all the signs of `V` are `1`, then `G E 1` is compact modulo the group `V.Γ` of rational
points: some compact set meets every coset `V.Γ g`. -/
lemma isCocompact_Gamma (V : Space E n 1) : V.Γ.IsCocompact :=
  V.isCocompact_of_definite fun _ _ ↦ rfl

variable (V : Space E n 1)

/-- For a space with all signs `1`, the subgroup `V.Γf` of finite parts of the rational points is
cocompact in the finite adelic unitary group: some compact set meets every coset `V.Γf g`. -/
lemma isCocompact_finitePart : V.Γf.IsCocompact := by
  -- Project the compact set of `isCocompact_Gamma` to the finite places.
  obtain ⟨C, hC, h_cover⟩ := V.isCocompact_Gamma
  refine ⟨Prod.snd '' C, hC.image continuous_snd, fun g ↦ ?_⟩
  obtain ⟨-, ⟨(γ : U V.J), rfl⟩, hγ⟩ := h_cover (1, g)
  exact ⟨V.embFin γ, ⟨γ, rfl⟩, V.ratEmbed γ * (1, g), hγ, rfl⟩

/-- For a space with all signs `1` and a level `K` (an open subgroup of `stdLevel E n`), the pair
`(Γf, K)` has finite type (`HasFiniteType`): there are finitely many double cosets `Γf \ Gf / K`,
the stabilisers `Γf ∩ g K g⁻¹` are finite, and `K` is open and compact.

A special case of Borel's finiteness of class numbers. Only forms with an adelic orthonormal frame
are covered, at open subgroups of the standard level. -/
instance hasFiniteType_of_isLevel {K : Subgroup (Gf E n)} [hK : IsLevel K] :
    HasFiniteType V.Γf K := by
  refine ⟨?_, fun g ↦ ?_, hK.isOpen, hK.isCompact⟩
  · -- A compact set `C` with `Γf C = Gf` meets finitely many cosets of the open group `K`.
    obtain ⟨C, hC, hcover⟩ := V.isCocompact_finitePart
    refine (finite_quotient_image_of_isCompact hK.isOpen hC).of_surjective
      (fun c ↦ ⟦c.val.out⟧) (Quot.ind fun g ↦ ?_)
    -- the class of `g` comes from the coset of `γ * g ∈ C`
    obtain ⟨γ, hγ, (hγg : γ * g ∈ C)⟩ := hcover g
    obtain ⟨k, hk⟩ := mk_out_eq_mul K (γ * g)
    have h_class : DoubleCoset.mk V.Γf K g = DoubleCoset.mk V.Γf K (⟦γ * g⟧ : Gf E n ⧸ K).out :=
      (DoubleCoset.eq ..).mpr ⟨γ, hγ, k, k.prop, hk⟩
    exact ⟨⟨γ * g, γ * g, hγg, rfl⟩, h_class.symm⟩
  · -- The discrete closed group `Γf` meets the compact set `g K g⁻¹` in a finite set.
    exact ((hK.isCompact.preimage_smul (toConjAct g⁻¹)).inter_left
      V.Γf.isClosed_of_discreteTopology).finite (IsDiscrete.mono ⟨mod_cast inferInstance⟩
        inf_le_left)

end New.Space

end MahlerSpace

/-!
## Unimodularity and the integral over [G] as a class sum

The Haar measures of `New.Gf` (finite points) and `New.G` (all adelic points) are right invariant.
-/

namespace New

open MeasureTheory Measure Set DoubleCoset Subgroup HasFiniteType

section FinitePart

variable {E n : Type*} [Field E] [CMType E] [Fintype n] [DecidableEq n]

/-- `Gf E n` is unimodular: the rational points of the standard space are a lattice in it. -/
instance : (volume : Measure (Gf E n)).IsMulRightInvariant :=
  isMulRightInvariant_of_finite_covolume
    (isFiniteMeasure_quotMeasure_of_cocompact _ (stdSpace E n).isCocompact_finitePart)

/-- A level `K` (an open subgroup of `stdLevel E n`) has volume `1 / [stdLevel E n : K]`, as
`vol (stdLevel E n) = 1`. -/
lemma measureReal_eq_inv_stdLevelIndex (K : Subgroup (Gf E n)) [hK : IsLevel K] :
    volume.real (K : Set (Gf E n)) = (stdLevelIndex K : ℝ)⁻¹ := by
  rw [measureReal_def, ← inter_eq_left.2 (SetLike.coe_subset_coe.2 hK.le),
    measure_inter_eq_inv_relIndex isCompact_stdLevel hK.isOpen volume volume_stdLevel,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]

lemma measureReal_pos_of_isLevel (K : Subgroup (Gf E n)) [hK : IsLevel K] :
    0 < volume.real (K : Set (Gf E n)) :=
  ENNReal.toReal_pos (hK.isOpen.measure_ne_zero _ ⟨1, K.one_mem⟩) hK.isCompact.measure_ne_top

/-- The group `Gf E Unit` of `1 × 1` matrices is commutative. -/
instance : IsMulCommutative (Gf E Unit) where
  -- `1 × 1` matrices over a commutative ring commute
  is_comm := ⟨by aesop (add simp [Matrix.mul_apply, mul_comm])⟩

end FinitePart

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  {W : Type*} [RCLike W]

/-- `G` is unimodular, as a product of unimodular groups. -/
instance : (volume : Measure (G E s)).IsMulRightInvariant := by
  apply_rules [prod.instIsMulRightInvariant, pi.isMulRightInvariant]

namespace Space

/-- Unfolding on a space with all signs `1`: for `Φ` integrable on `G`, the sum
`g ↦ ∑ γ ∈ Γ, Φ (γ g)` over the rational points `Γ = V.Γ`, written as an integral for the counting
measure, is integrable on `[G]`, with the same integral as `Φ`. Integration on `[G] = Γ \ G` is by
`V.quotMeasure`. -/
lemma integral_quotMeasure_integral {V : Space E n 1} {Φ : G E (1 : n → ℤˣ) → W}
    (hΦ : Integrable Φ) :
    Integrable (fun g : G E (1 : n → ℤˣ) ↦ ∫ γ : V.Γ, Φ (γ • g) ∂count) V.quotMeasure ∧
      ∫ g : G E (1 : n → ℤˣ), ∫ γ : V.Γ, Φ (γ • g) ∂count ∂V.quotMeasure =
        ∫ g : G E (1 : n → ℤˣ), Φ g := by
  obtain ⟨h_prod, h_eq⟩ := (measurePreserving_orbitMeasure (ν := count (α := V.Γ))).fubini hΦ
  exact ⟨h_prod.integral_prod_left, h_eq⟩

/-- Let `f g` be the integral of `F` over `G_∞ × {g}` (`G_∞ = GInf E 1` is the group at the
infinite places), let the level `K` fix `f` under right translation (`rightStabilizer f`), and let
`u` be a finite point such that the indicator of `G_∞ × u K` times `F` is integrable. Then the
integral of `F` over `G_∞ × u K` is `[stdLevel E n : K]⁻¹ * f u`. -/
lemma integral_indicator_univ_prod_coset {F : G E (1 : n → ℤˣ) → W} {f : Gf E n → W}
    (hF_avg : ∀ g : Gf E n, ∫ x : GInf E (1 : n → ℤˣ), F (x, g) = f g)
    (K : Subgroup (Gf E n)) [hK : IsLevel K] (hf_stab : K ≤ rightStabilizer f) (u : Gf E n)
    (h_int : Integrable ((univ ×ˢ ((u * ·) '' (K : Set (Gf E n)))).indicator F)) :
    ∫ g : GInf E (1 : n → ℤˣ) × Gf E n, (univ ×ˢ ((u * ·) '' (K : Set (Gf E n)))).indicator F g =
      (stdLevelIndex K : W)⁻¹ * f u := by
  classical
  let Φ : G E (1 : n → ℤˣ) → W := (univ ×ˢ ((u * ·) '' K)).indicator F
  -- As `f` is constant on `u K`, the integral is `vol K * f u`.
  have h_slice (k : Gf E n) :
      ∫ x, Φ (x, u * k) = (K : Set (Gf E n)).indicator (fun _ ↦ f u) k := by
    by_cases hk : k ∈ K
    · simp [Φ, hk, hF_avg, hf_stab hk u]
    · simp [Φ, hk]
  calc ∫ g, Φ g = ∫ k, ∫ x, Φ (x, k) := integral_prod_symm _ h_int
    _ = ∫ k, ∫ x, Φ (x, u * k) := (integral_mul_left_eq_self _ u).symm
    _ = (stdLevelIndex K : W)⁻¹ * f u := by
      simp [h_slice, integral_indicator_const _ hK.isOpen.measurableSet,
        measureReal_eq_inv_stdLevelIndex, RCLike.real_smul_eq_coe_mul]

/-- Let `V` be a space with all signs `1`: a hermitian matrix `J` over `E` and a point `x`. Write
`V.Γ` for its rational points `x⁻¹γx` (`γ ∈ U(J)(E)`) in `G = G_∞ × G_f`, and `V.Γf` for their
finite parts in `Gf E n`. Let `F` be a continuous left `V.Γ`-invariant function on `G` whose
integral over `G_∞` at `(·, g)` is `f g`, and let `K` be a level (an open subgroup of
`K₀ = stdLevel E n = G_f ∩ GL_n(Ô)`) that fixes `f` under right translation. Then the integral of
`F` over `V.Γ \ G` against `V.quotMeasure` (with `vol G_∞ = vol K₀ = 1`) is `[K₀ : K]⁻¹` times the
class sum of `f`, which is the sum over the double cosets `V.Γf g K` of
`f g / #(V.Γf ∩ g K g⁻¹)`. -/
lemma integral_quotMeasure_eq_classSum {V : Space E n 1} {F : G E (1 : n → ℤˣ) → W}
    {f : Gf E n → W} (hF_left : V.Γ.FixesLeft F)
    (hF_avg : ∀ g : Gf E n, ∫ x : GInf E (1 : n → ℤˣ), F (x, g) = f g)
    (K : Subgroup (Gf E n)) [hK : IsLevel K] (hf_stab : K ≤ rightStabilizer f)
    (hF_cont : Continuous F) :
    ∫ g : G E (1 : n → ℤˣ), F g ∂V.quotMeasure = (stdLevelIndex K : W)⁻¹ * classSum V.Γf K f := by
  classical
  -- Cut `F` into the pieces `Φ u` on the cosets `G_∞ × u K`, `u` a class representative, and unfold
  -- each piece. The projection to `Gf E n` maps `V.Γ` bijectively onto `V.Γf`.
  let finPart (γ : V.Γ) : Gf E n := (γ : G E (1 : n → ℤˣ)).2
  have h_inj : Function.Injective finPart :=
    (V.fact_embFin_injective.out.injOn_range (g := Prod.snd)).injective
  have h_surj : ∀ a ∈ V.Γf, ∃ γ : V.Γ, finPart γ = a :=
    forall_mem_range.2 fun γ ↦ ⟨⟨V.ratEmbed γ, γ, rfl⟩, rfl⟩
  -- `T g h : Finset V.Γ` is the set of `γ` with `g⁻¹ * finPart γ * h ∈ K`; it has
  -- `#(classAut V.Γf K g)` elements if `g` and `h` lie in one class, and none otherwise.
  have h_transporter : ∀ g h : Gf E n, ∃ T : Finset V.Γ,
      (∀ γ : V.Γ, γ ∈ T ↔ finPart γ ∈ V.Γf ∧ g⁻¹ * finPart γ * h ∈ K) ∧
      T.card = if DoubleCoset.mk V.Γf K g = DoubleCoset.mk V.Γf K h
        then Nat.card (classAut V.Γf K g) else 0 :=
    exists_transporter V.Γf h_inj h_surj K
  choose T hT card_T using h_transporter
  let Φ (u : Gf E n) : G E (1 : n → ℤˣ) → W := (univ ×ˢ ((u * ·) '' K)).indicator F
  have h_int (u : Gf E n) : Integrable (Φ u) := by
    have h_compact :
        IsCompact (univ ×ˢ ((u * ·) '' (K : Set (Gf E n))) : Set (G E (1 : n → ℤˣ))) :=
      isCompact_univ.prod (hK.isCompact.image (continuous_const_mul u))
    exact (hF_cont.continuousOn.integrableOn_compact h_compact).integrable_indicator
      h_compact.measurableSet
  -- The `γ` that move `g` into `G_∞ × u K` form the finite set `T u g.2`, and `F (γ * g) = F g`.
  have h_orbit (u : Gf E n) (g : G E (1 : n → ℤˣ)) :
      ∫ γ : V.Γ, Φ u (γ • g) ∂count = ((T u g.2).card : ℝ) • F g := by
    have h_ind : (fun γ : V.Γ ↦ Φ u (γ • g)) = (T u g.2 : Set V.Γ).indicator fun _ ↦ F g := by
      ext ⟨_, δ, rfl⟩
      have hγ : (V.ratEmbed δ).2 ∈ V.Γf := ⟨δ, rfl⟩
      simp [Φ, finPart, indicator, hT, hγ, Subgroup.smul_def, hF_left _ ⟨δ, rfl⟩, mul_assoc]
    rw [h_ind, integral_indicator_const _ (T u g.2).measurableSet, measureReal_def,
      count_apply_finset, ENNReal.toReal_natCast]
  -- Only the class `c` of `g.2` contributes, with as many terms as `c.out` has automorphisms.
  let weight (c : DoubleCosets V.Γf K) : ℝ := (Nat.card (classAut V.Γf K c.out) : ℝ)⁻¹
  have h_weight (c : DoubleCosets V.Γf K) : weight c * Nat.card (classAut V.Γf K c.out) = 1 :=
    have h_finite : Finite (classAut V.Γf K c.out) := finite_aut c.out
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  have h_term (g : G E (1 : n → ℤˣ)) (c : DoubleCosets V.Γf K) :
      weight c • ∫ γ : V.Γ, Φ c.out (γ • g) ∂count =
        if c = DoubleCoset.mk V.Γf K g.2 then F g else 0 := by
    rw [h_orbit, card_T, out_eq', smul_smul]
    split_ifs
    · rw [h_weight, one_smul]
    · rw [Nat.cast_zero, mul_zero, zero_smul]
  have h_sum (g : G E (1 : n → ℤˣ)) : F g = ∑ c, weight c • ∫ γ : V.Γ, Φ c.out (γ • g) ∂count := by
    simp only [h_term, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h_unfold (c : DoubleCosets V.Γf K) :
      Integrable (fun g : G E (1 : n → ℤˣ) ↦ ∫ γ : V.Γ, Φ c.out (γ • g) ∂count) V.quotMeasure ∧
        ∫ g, ∫ γ : V.Γ, Φ c.out (γ • g) ∂count ∂V.quotMeasure = ∫ g, Φ c.out g :=
    integral_quotMeasure_integral (h_int c.out)
  have h_vol (u : Gf E n) : ∫ g, Φ u g = (stdLevelIndex K : W)⁻¹ * f u :=
    integral_indicator_univ_prod_coset hF_avg K hf_stab u (h_int u)
  calc ∫ g, F g ∂V.quotMeasure
      = ∑ c, ∫ g, weight c • ∫ γ : V.Γ, Φ c.out (γ • g) ∂count ∂V.quotMeasure := by
        rw [funext h_sum]
        exact integral_finsetSum _ fun c _ ↦ (h_unfold c).left.smul (weight c)
    _ = ∑ c, weight c • ((stdLevelIndex K : W)⁻¹ * f c.out) := by
        simp only [integral_smul, (h_unfold _).right, h_vol]
    _ = (stdLevelIndex K : W)⁻¹ * classSum V.Γf K f := by
        rw [classSum, finsum_eq_sum_of_fintype, Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ ↦ by rw [mul_smul_comm, inv_natCast_smul_eq ℝ ℚ]

/-- Let `V` be a space with all signs `1`. Write `V.Γ` for its rational points `x⁻¹γx`
(`γ ∈ U(J)(E)`) in `G = G_∞ × G_f` and `V.Γf` for their finite parts, and let `K` be a level, an
open subgroup of `K₀ = stdLevel E n = G_f ∩ GL_n(Ô)`. Let `y` on `G_f` be left `V.Γf`-invariant with
open right stabiliser. Then `classIntegral V.Γf K y` equals `[K₀ : K]` times the integral of
`g ↦ y g_fin` over `V.Γ \ G` against `V.quotMeasure` (with `vol G_∞ = vol K₀ = 1`), where
`classIntegral V.Γf K y` is the sum over the double cosets `V.Γf g K'` of
`y g / #(V.Γf ∩ g K' g⁻¹)`, with `K' = rightStabilizer y ⊓ K`, divided by `[K : K']`. -/
theorem classIntegral_eq_integral {V : Space E n 1} {y : Gf E n → W}
    (hy : y ∈ smoothInvariants V.Γf) (K : Subgroup (Gf E n)) [hK : IsLevel K] :
    classIntegral V.Γf K y =
      (stdLevelIndex K : W) * ∫ g : G E (1 : n → ℤˣ), y g.2 ∂V.quotMeasure := by
  -- The integral is `[stdLevel : S]⁻¹` times the class sum at the level `S = Stab y ∩ K`.
  obtain ⟨(hy_left : V.Γf.FixesLeft y), (hy_open : IsOpen (rightStabilizer y : Set (Gf E n)))⟩ := hy
  have hS : IsLevel (rightStabilizer y ⊓ K) := ⟨inf_le_of_right_le hK.le, hy_open.inter hK.isOpen⟩
  have h_left : V.Γ.FixesLeft fun g ↦ y g.2 :=
    forall_mem_range.2 fun γ g ↦ hy_left _ ⟨γ, rfl⟩ g.2
  have h_index : (stdLevelIndex (rightStabilizer y ⊓ K) : W) =
      (rightStabilizer y).relIndex K * stdLevelIndex K := by
    rw [← inf_relIndex_right, ← Nat.cast_mul, relIndex_mul_relIndex _ _ _ inf_le_right hK.le]
  have h_integral : ∫ g : G E (1 : n → ℤˣ), y g.2 ∂V.quotMeasure =
      (stdLevelIndex (rightStabilizer y ⊓ K) : W)⁻¹ * classSum V.Γf (rightStabilizer y ⊓ K) y :=
    integral_quotMeasure_eq_classSum h_left (fun g ↦ by simp) _ inf_le_left
      (isLocallyConstant_of_eventually_mul <| hy_open.mem_nhds (one_mem _)).continuous.snd'
  rw [h_integral, h_index, mul_inv_rev, mul_assoc,
    mul_inv_cancel_left₀ (Nat.cast_ne_zero.2 (isCompact_stdLevel.relIndex_ne_zero hK.isOpen)),
    classIntegral, inv_natCast_smul_eq ℚ W, smul_eq_mul]

end Space

end New
