import New.Spanning.Frames.StandardLevel
import New.Spanning.MainTerm.GlobalSieve

/-!
# The place and level of a set of primes, orbit sums and the set of entries

This file sets up the local theory at a finite set `T` of finite places, stable under conjugation.
It defines the projection `New.Filling.toPlaces` of the finite adelic unitary group to `T` and the
condition `New.Filling.IsIntegralOff` of being integral off `T`. It also defines the orbit sums
`New.Filling.cosetAmplitude`, the finite set `New.Filling.entrySet` of entries and the condition
`New.Filling.IsFillingData`. It shows that the product `New.LocProd T` of the completions at `T` is
a finite place that carries such a datum.

## Main definitions and results

* `New.Filling.exists_isIntegralOff_toPlaces_eq`: every point of the unitary group at `T` is the
  projection of a finite adelic point that is integral off `T`.
* `New.Filling.exists_isFillingData`: `New.LocProd T` is a finite place (`New.Floors.IntegralPlace`)
  with a place datum satisfying `New.Filling.IsFillingData`.

Notions from other files:
* `New.Filling.latticeStabilizer`, `New.Filling.principalLevel`: The group `K` of integral points of
  the finite adelic unitary group, and the kernel `K(M)` of its reduction modulo `M`;
  `New.Floors.PlaceData.congruenceSubgroup` is the group `K(M)` at `T`.
* `New.Filling.amplitude`: The integral of β_c(y) β_c'(γ⁻¹y) W(y) ⊗ W(γ⁻¹y)^* over the infinite
  points y, with β_c the cutoff `New.Filling.classCutoff` and W the full or the cut Bessel function
  at infinity, according to the argument `side`.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

namespace New.Filling

open NumberField MeasureTheory Matrix ENNReal Fintype Floors FloorGroups Function
  ComplexOrder SemilocalField Measure Filter Complex Set

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape}

/-! ### Orbit sums, the set of entries and the projection to `T` -/

section

variable (S : Filling E 𝔰) (T : Finset (FinPlace E)) [T.StarStable]

/-- The element `x` of the finite adelic unitary group and its inverse have entries integral at
every place outside `T`. -/
abbrev IsIntegralOff (x : S.GFin) : Prop := x.val ∈ intGL 𝔰.BesselIndex (integralOff T)

/-- The sum of the amplitudes of `u γ u'⁻¹`, for the Bessel function named by `side` (full or cut),
over the pairs `(u, u')` of rational points of the unipotent group 𝖴 for which `u γ u'⁻¹` lies over
the block `(c, s, c')`. -/
noncomputable def cosetAmplitude (side : FullOrCut) (c : S.Classes) (s : S.ResidueGL)
    (c' : S.Classes) (γ : S.G E) : EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord) :=
  ∑' x : (S.ratMiddle E).besselU × (S.ratMiddle E).besselU,
    (S.termsOver c s c').indicator (S.amplitude side c c') (x.1.val * γ * x.2.val⁻¹)

/-- The nonzero integers `δ` of `E` with `‖δ‖ ^ 2 ≤ b ^ (270 n ^ 2)` at every infinite place. The
nonzero leading minors of a term with nonzero cut amplitude are such integers
(`New.Filling.leadingMinor_mem_boundedNonzeroIntegers`). -/
def boundedNonzeroIntegers : Set E :=
  {δ : E | δ ≠ 0 ∧ IsIntegral ℤ δ ∧ ∀ v : InfinitePlace E, ‖Φ v δ‖ ^ 2 ≤ S.b ^ (270 * 𝔰.n ^ 2)}

/-- The set `S.boundedNonzeroIntegers` is finite. It consists of the nonzero integers `δ` of `E`
with `‖δ‖ ^ 2 ≤ b ^ (270 n ^ 2)` at every infinite place of `E`. -/
lemma finite_boundedNonzeroIntegers : S.boundedNonzeroIntegers.Finite := by
  refine (Embeddings.finite_of_norm_le E ℂ √(S.b ^ (270 * 𝔰.n ^ 2))).subset ?_
  rintro δ ⟨-, h_int, h_le⟩
  refine ⟨h_int, fun φ ↦ Real.le_sqrt_of_sq_le ?_⟩
  rw [← InfinitePlace.apply, ← mk_Φ (InfinitePlace.mk φ), InfinitePlace.apply]
  exact h_le _

/-- There are finitely many quotients of two elements of `boundedNonzeroIntegers`. -/
lemma finite_quotient_boundedNonzeroIntegers :
    {t : Eˣ | ∃ δ ∈ S.boundedNonzeroIntegers, ∃ δ' ∈ S.boundedNonzeroIntegers, δ / δ' = t}.Finite :=
  Finite.preimage (f := Units.val) Units.val_injective.injOn
    (S.finite_boundedNonzeroIntegers.image2 (fun δ δ' : E ↦ δ / δ') S.finite_boundedNonzeroIntegers)

/-- The finite set 𝒯 of entries: the quotients of two elements of `boundedNonzeroIntegers`. -/
noncomputable def entrySet : Finset Eˣ := S.finite_quotient_boundedNonzeroIntegers.toFinset

/-- The homomorphism from the finite adelic unitary group (lattice basis) to the unitary group
over the product of the completions at T, taking components at T. -/
noncomputable def toPlaces :
    U (S.latticeMiddle (𝔸f E)).splitGram →* U (S.latticeMiddle (LocProd T)).splitGram :=
  U.map (evalPlaces T) (fun x ↦ (star_evalPlaces T x).symm)
    (S.map_splitGram_latticeMiddle (evalPlaces T))

/-- The place datum `F` on the product of the completions at `T` is built on the Gram matrix
`New.Filling.latticeMiddle`, with 3ϱ + 6 further hyperbolic pairs and an orthonormal part of size
`k - (6ϱ + 13)`. It is a large lattice datum for the chosen place structure, its modulus is the
component of `M` at `T`, and the character of the place is `New.Filling.charOnPlaces`. -/
class IsFillingData [P : IntegralPlace (LocProd T)]
    (F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T))
      (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5)) :
    Prop extends P.IsLargeLatticeData F where
  /-- The character of the place is the character of `S` at `T`. -/
  psi_eq : P.ψ = S.charOnPlaces T
  /-- The modulus of `F` is the component of `M` at `T`. -/
  levelUnit_eq : F.levelUnit = S.ideleM.map (evalPlaces T)

/-- A finite adele is integral off T for all sufficiently large finite sets T of finite places. -/
lemma eventually_mem_integralOff (a : 𝔸f E) :
    ∀ᶠ T : Finset (FinPlace E) in Filter.atTop, a ∈ integralOff T := by
  -- It suffices that `T` contain the finitely many places where `a` is not integral.
  have h_fin : {w : FinPlace E | a w ∉ LocInt w}.Finite := a.2
  filter_upwards [eventually_ge_atTop h_fin.toFinset] with T hT
  have h_int (w : FinPlace E) (hw : w ∉ T) : a w ∈ LocInt w :=
    by_contra fun h_not ↦ hw (hT (h_fin.mem_toFinset.2 h_not))
  simpa [integralOff] using h_int

/-- For a finite set `T₀` of nonzero elements of `E` there is a finite set `T` of places, stable
under conjugation, off which the elements of `T₀` are units and the following are integral: the
inverse of the modulus `M`, the lattice basis with its inverse, and the inverse of the natural
number `S.N`. Here `ratIntegralOff T` is the ring of `T`-integers of `E`. -/
theorem exists_places_integralOff (T₀ : Finset Eˣ) :
    ∃ T : Finset (FinPlace E),
      T.StarStable ∧
      (∀ t ∈ T₀, t.val ∈ ratIntegralOff T ∧ t⁻¹.val ∈ ratIntegralOff T) ∧
      Fact (S.ideleM⁻¹.val ∈ integralOff T) ∧
      S.latticeBasis ∈ intGL 𝔰.BesselIndex (integralOff T) ∧
      (S.N : E)⁻¹ ∈ ratIntegralOff T := by
  classical
  -- Every `T` lies in the stable set `T ∪ star T`.
  have h_star : ∃ᶠ T : Finset (FinPlace E) in .atTop, T.StarStable := by
    refine frequently_atTop.2 fun T ↦ ⟨T ∪ T.image star, Finset.subset_union_left, ⟨?_⟩⟩
    intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem star hw)
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
      rw [star_star]
      exact Finset.mem_union_left _ hv
  -- The other conditions ask finitely many adeles to be integral off `T`.
  refine (h_star.and_eventually ?_).exists
  simp [mem_intGL, eventually_mem_integralOff, fact_iff, -eventually_atTop, -Sum.forall]

end

variable [WeilData E] {S : Filling E 𝔰} {T : Finset (FinPlace E)} [T.StarStable] {x : S.GFin}

section

omit [WeilData E]

/-- Let `w_p = weylElem 𝔰.ϱ p` be the Weyl element with `e_a ↦ p_a e*_a` and `e*_a ↦ e_a / p̄_a` on
the `𝔰.ϱ` hyperbolic pairs of the hermitian space of `S`. At an infinite place `v` with chosen
embedding `Φ v`, its rescaled image `ratToInf` is `w_q`, where `q i` is `Φ v (p i)` times the square
`frameScaleSq v i` of the scale of the `i`-th frame vector, read as a unit by `unitOrOne`. -/
lemma ratToInf_weylElem (p : ℕ → Eˣ) (v : InfinitePlace E) :
    S.ratToInf (weylElem 𝔰.ϱ p) v =
      weylElem 𝔰.ϱ (fun i : ℕ ↦ unitOrOne (S.frameScaleSq v i * Φ v (p i))) := by
  -- Compare entries column by column; each column has one nonzero entry. Conjugating by the scales
  -- `basisScale` multiplies the entries on the pair of floor `a` by `S.frameScaleSq v a` or by its
  -- inverse, and keeps the others.
  ext i j
  rcases j with a | (a | a) | a
  all_goals
    simp [weylElem, weylOn, BesselIndex.level, basisScale, frameScaleSq, unitOrOne, two_mul,
      pow_add, Nat.add_sub_assoc, Nat.Prime.ne_zero]
    split_ifs with hi
    · simp [field, ← Complex.ofReal_pow, hi, Nat.Prime.ne_zero]
    · simp

/-- At an infinite place `v`, the rescaled image of `w_p σ` is `w_q` times the rescaled image of
`σ`, where `q i` is `Φ v (p i)` times the squared scale `frameScaleSq v i`. -/
lemma ratToInf_weylElem_mul {σ : S.G E} {p : ℕ → Eˣ} (v : InfinitePlace E) :
    S.ratToInf (weylElem 𝔰.ϱ p * σ) v =
      weylElem 𝔰.ϱ (fun i : ℕ ↦ unitOrOne (S.frameScaleSq v i * Φ v (p i))) * S.ratToInf σ v := by
  rw [map_mul, Pi.mul_apply, ratToInf_weylElem]

/-- Every element `y` of the unitary group over the completions at `T` is the projection of a finite
adelic element `x` that is integral off `T`. Moreover, `x` lies in the unipotent group
`New.Shape.Form.besselU` if `y` does. It lies in `New.Shape.Form.besselH` if `y` does. -/
theorem exists_isIntegralOff_toPlaces_eq (y : U (S.latticeMiddle (LocProd T)).splitGram) :
    ∃ x : U (S.latticeMiddle (𝔸f E)).splitGram,
      S.toPlaces T x = y ∧ S.IsIntegralOff T x ∧
      (y ∈ besselU → x ∈ besselU) ∧
      (y ∈ besselH → x ∈ besselH) := by
  -- The lift of `y` is `1 + φ (y - 1)`, where `φ` extends each entry by zero.
  let φ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd T) →ₙ+*
      Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) :=
    { toFun M := M.map (adeleOfLocal T)
      map_mul' := by simp
      map_zero' := by simp
      map_add' := Matrix.map_add _ (map_add _) }
  have hφ (M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd T)) (i j : 𝔰.BesselIndex) :
      φ M i j = adeleOfLocal T (M i j) := rfl
  let f : GL 𝔰.BesselIndex (LocProd T) →* GL 𝔰.BesselIndex (𝔸f E) := unitsMapNonUnital φ
  have hf (g : GL 𝔰.BesselIndex (LocProd T)) (i j : 𝔰.BesselIndex) :
      (f g).val i j = (1 : Matrix _ _ (𝔸f E)) i j +
        adeleOfLocal T (g.val i j - (1 : Matrix _ _ (LocProd T)) i j) := rfl
  have h_unitary : f y ∈ S.GFin := by
    let J : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) := (S.latticeMiddle (𝔸f E)).splitGram
    have h_left (M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd T)) :
        φ (J.map (evalPlaces T) * M) = J * φ M := by
      ext i j : 1
      simp only [hφ, mul_apply, _root_.map_sum, Matrix.map_apply, adeleOfLocal_evalPlaces_mul]
    have h_right (M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd T)) :
        φ (M * J.map (evalPlaces T)) = φ M * J := by
      ext i j : 1
      simp only [hφ, mul_apply, _root_.map_sum, Matrix.map_apply, mul_comm (M _ _),
        mul_comm (adeleOfLocal T _), adeleOfLocal_evalPlaces_mul]
    have h_star (M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd T)) : φ Mᴴ = (φ M)ᴴ := by
      ext i j : 1
      simp only [hφ, conjTranspose_apply, adeleOfLocal_star]
    -- For `y = 1 + z` the condition on `y` reads `zᴴ J z + zᴴ J + J z = 0`; apply `φ` to it.
    obtain ⟨z, hz⟩ : ∃ z : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd T), 1 + z = y.val.val :=
      add_left_surjective 1 y.val.val
    have hy : (1 + z)ᴴ * J.map (evalPlaces T) * (1 + z) = J.map (evalPlaces T) := by
      rw [hz, S.map_splitGram_latticeMiddle (evalPlaces T)]
      exact mem_U.1 y.prop
    have h_zero : zᴴ * (J.map (evalPlaces T) * z) + zᴴ * J.map (evalPlaces T) +
        J.map (evalPlaces T) * z = 0 := by
      rw [conjTranspose_add, conjTranspose_one] at hy
      linear_combination (norm := noncomm_ring) hy
    have h_map : (φ z)ᴴ * (J * φ z) + (φ z)ᴴ * J + J * φ z = 0 := by
      rw [← h_star, ← h_left, ← h_right, ← map_mul, ← map_add, ← map_add, h_zero, map_zero]
    have hfy : (f y).val = 1 + φ z := by simp [f, ← hz]
    change (f y).valᴴ * J * (f y).val = J
    rw [hfy, conjTranspose_add, conjTranspose_one]
    linear_combination (norm := noncomm_ring) h_map
  have h_int (g : GL 𝔰.BesselIndex (LocProd T)) : IsIntMatrix (integralOff T) (f g).val :=
    IsIntMatrix.one.add fun _ _ ↦ adeleOfLocal_mem_integralOff T _
  refine ⟨⟨f y, h_unitary⟩, ?_, mem_intGL.2 ⟨h_int y, h_int y⁻¹⟩, ?_⟩
  · ext i j : 3
    change evalPlaces T ((f y).val i j) = y.val.val i j
    simp [hf, Matrix.one_apply]
  · -- Both subgroups ask certain entries to be those of `1`, and `f` keeps this.
    have h_entry (i j : 𝔰.BesselIndex) (h : y.val.val i j = (1 : Matrix _ _ (LocProd T)) i j) :
        (f y).val i j = (1 : Matrix _ _ (𝔸f E)) i j := by
      rw [hf, h, sub_self, map_zero, add_zero]
    exact ⟨fun hy ↦ mem_besselU.2 fun i j h ↦ h_entry i j (mem_besselU.1 hy i j h),
      fun hy ↦ mem_floorGroup.2 fun i j h ↦ h_entry i j (mem_floorGroup.1 hy i j h)⟩

/-- Let `u` be a finite idele with `u⁻¹` integral off `T`. A finite adelic point `x` is integral and
congruent to `1` modulo `u` if and only if it is integral off `T` and its projection to `T` is
integral and congruent to `1` modulo the projection of `u`. -/
theorem mem_unitaryLevel_iff {u : (𝔸f E)ˣ} (hu : u⁻¹.val ∈ integralOff T) :
    x ∈ unitaryLevel (Ô E) u (S.latticeMiddle (𝔸f E)).splitGram ↔
      S.IsIntegralOff T x ∧
      S.toPlaces T x ∈
        unitaryLevel O (u.map (evalPlaces T)) (S.latticeMiddle (LocProd T)).splitGram := by
  have h_entry (i j : 𝔰.BesselIndex) :
      (S.toPlaces T x).val.val i j = evalPlaces T (x.val.val i j) := rfl
  have h_inv_entry (i j : 𝔰.BesselIndex) :
      (S.toPlaces T x).val⁻¹.val i j = evalPlaces T (x.val⁻¹.val i j) := rfl
  -- By `mem_Ô_iff` each condition splits into one at `T` and one off `T`.
  have h_split : x ∈ unitaryLevel (Ô E) u (S.latticeMiddle (𝔸f E)).splitGram ↔
      (S.IsIntegralOff T x ∧ IsIntMatrix (integralOff T) (u⁻¹.val • (x.val.val - 1))) ∧
      S.toPlaces T x ∈
        unitaryLevel O (u.map (evalPlaces T)) (S.latticeMiddle (LocProd T)).splitGram := by
    simp [unitaryLevel, mem_intGL, IsIntMatrix, mem_Ô_iff T, Units.smul_def, forall_and,
      Matrix.one_apply, Subgroup.copy, h_entry, h_inv_entry, -Sum.forall, -coe_units_inv]
    -- The two sides are now the same conditions on entries, in another order.
    tauto
  -- Off `T` the congruence modulo `u` follows from integrality, as `u⁻¹` is integral there.
  have h_cong (hx : S.IsIntegralOff T x) :
      IsIntMatrix (integralOff T) (u⁻¹.val • (x.val.val - 1)) :=
    (hx.isIntMatrix.sub .one).smul hu
  rw [h_split, and_iff_left_of_imp h_cong]

/-- A finite adelic point `x` lies in the group `K` of integral points if and only if it is integral
off `T` and its projection to `T` is integral. -/
lemma mem_latticeStabilizer_iff :
    x ∈ S.latticeStabilizer ↔
      S.IsIntegralOff T x ∧
      S.toPlaces T x ∈ unitaryLevel O 1 (S.latticeMiddle (LocProd T)).splitGram := by
  simp [latticeStabilizer, ← unitaryLevel_one, mem_unitaryLevel_iff (T := T)]

end

/-! ### The product of the completions at `T` as a finite place -/

/-- Let `i` and `τ` be integral at `T`, with `i² = -1`, `star i = -i` and `τ + star τ = 1`. There is
a Haar measure `ν` on the skew elements, of mass one on the integral ones, such that
`(a, b) ↦ τ i a + b` takes `ν.prod ν` to the volume. -/
lemma exists_isAddHaarMeasure_skewAdjoint {i τ : LocProd T} (hi : i ∈ O) (hτ : τ ∈ O)
    (h_sq : -i * i = 1) (h_skew : star i = -i) (h_tr : τ + star τ = 1) :
    ∃ ν : Measure (skewAdjoint (LocProd T)),
      ν.IsAddHaarMeasure ∧
      ν {b : skewAdjoint (LocProd T) | b.val ∈ O} = 1 ∧
      MeasurePreserving
        (fun p : skewAdjoint (LocProd T) × skewAdjoint (LocProd T) ↦ τ * i * p.1.val + p.2.val)
        (ν.prod ν) := by
  -- The map `π` is onto and `π ⁻¹' O = B ×ˢ B`, for `B` the set of integral skew elements. So it
  -- takes `ν.prod ν` to the Haar measure that gives `O` mass one.
  let B : Set (skewAdjoint (LocProd T)) := {b : skewAdjoint (LocProd T) | b.val ∈ O}
  let ν : Measure (skewAdjoint (LocProd T)) :=
    addHaarMeasure ⟨⟨B, isCompact_O.preimage_val isClosed_skewAdjoint⟩, 0,
      isOpen_O.preimage_val.interior_eq.ge O.zero_mem⟩
  have hν : ν B = 1 := addHaarMeasure_self
  let π : skewAdjoint (LocProd T) × skewAdjoint (LocProd T) →+ LocProd T :=
    .mk' (fun p ↦ τ * i * p.1.val + p.2.val) fun p q ↦ by simp [mul_add, add_add_add_comm]
  have h_lift : HasAddStableLifts π univ := by
    refine fun x ↦ ⟨(skewPart (-i * x), skewPart (star τ * x)), ?_, by simp⟩
    change τ * i * (-i * x - star (-i * x)) + (star τ * x - star (star τ * x)) = x
    simp only [star_mul', star_neg, star_star, h_skew]
    linear_combination τ * (x + star x) * h_sq + x * h_tr
  have h_pre : π ⁻¹' (O : Subring (LocProd T)) = B ×ˢ B := by
    ext ⟨a, b⟩
    let x : LocProd T := τ * i * a + b
    change x ∈ O ↔ a.val ∈ O ∧ b.val ∈ O
    refine ⟨fun hx ↦ ?_, fun ⟨ha, hb⟩ ↦ add_mem (mul_mem (mul_mem hτ hi) ha) hb⟩
    -- The trace of `x = π (a, b)` gives back `a`, so `x ∈ O` forces `a ∈ O`, then `b ∈ O`.
    have h_trace : a = -i * (x + star x) := by
      simp only [x, star_add, star_mul', h_skew, skewAdjoint.star_val_eq]
      linear_combination -(τ + star τ) * a.val * h_sq - a.val * h_tr
    have ha : a.val ∈ O :=
      mem_of_eq_of_mem h_trace (mul_mem (neg_mem hi) (add_mem hx (IsStarStable.star_mem hx)))
    exact ⟨ha, (add_mem_cancel_left (mul_mem (mul_mem hτ hi) ha)).1 hx⟩
  have h_map : (ν.prod ν).map π = volume := by
    simpa [h_pre, SemilocalField.volume_O, hν] using measure_smul_map_restrict_eq_smul_neg
      (ν.prod ν) volume (by measurability) .univ h_lift isCompact_O.measurableSet
  exact ⟨ν, inferInstance, hν, by fun_prop, h_map⟩

/-- If the integers at `T` are self-dual for the character `ψ`, then there is a kernel `G` for
Plancherel's inequality. It is continuous, integrable and nonnegative, with `G 0 = 1`, and its
transform has mass at most one. -/
lemma exists_plancherel_kernel {ψ : AddChar (LocProd T) ℂ}
    (h_dual : ∀ a : LocProd T, (∀ r ∈ O, ψ (r * a) = 1) ↔ a ∈ O) :
    ∃ G : LocProd T → ℝ,
      Continuous G ∧ Integrable G ∧ 0 ≤ G ∧ G 0 = 1 ∧
      ∫⁻ z : LocProd T, ‖∫ v : LocProd T, G v * ψ (star v * z)‖ₑ ≤ 1 := by
  classical
  let G : LocProd T → ℝ := (O : Subring (LocProd T)).carrier.indicator 1
  -- Orthogonality of characters and self-duality: `G` is its own transform.
  have h_transform (z : LocProd T) : ∫ v : LocProd T, G v * ψ (star v * z) = G z := by
    have h_star : (∀ v ∈ O, ψ (star v * z) = 1) ↔ z ∈ O :=
      ⟨fun h ↦ (h_dual z).1 fun r hr ↦ by simpa using h _ (IsStarStable.star_mem hr),
        fun h v hv ↦ (h_dual z).2 h _ (IsStarStable.star_mem hv)⟩
    calc
      _ = ∫ v in (O : Subring (LocProd T)), ψ (star v * z) := by
        simp [G, ← integral_indicator isCompact_O.measurableSet, indicator_apply,
          apply_ite Complex.ofReal]
      _ = if ∀ v ∈ O, ψ (star v * z) = 1 then 1 else 0 := by
        simpa [real_def, volume_O] using setIntegral_char (ν := volume) (M := O.toAddSubgroup)
          isOpen_O (χ := fun v ↦ ψ (star v * z)) (by simp [add_mul, AddChar.map_add_eq_mul])
      _ = G z := by simp [G, h_star, indicator_apply, apply_ite Complex.ofReal]
  refine ⟨G, IsClopen.continuous_indicator ⟨isCompact_O.isClosed, isOpen_O⟩ continuous_one, ?_,
    fun _ ↦ indicator_nonneg (by simp) _, by simp [G], ?_⟩
  · simp [G, integrable_indicator_iff, isCompact_O.measurableSet, Pi.one_def, volume_O]
  · calc
      _ = ∫⁻ z : LocProd T, (O : Subring (LocProd T)).carrier.indicator 1 z := by
        simp_rw [h_transform]
        simp [G, indicator_apply, apply_ite enorm, apply_ite Complex.ofReal]
      _ ≤ 1 := (lintegral_indicator_one_le _).trans_eq volume_O

section

omit [WeilData E] [T.StarStable]

/-- The integers at `T` are self-dual for the character `charOnPlaces`: `a` is integral if and only
if the character is trivial on the integral multiples of `a`. -/
lemma forall_charOnPlaces_mul_eq_one_iff (a : LocProd T) :
    (∀ r ∈ O, S.charOnPlaces T (r * a) = 1) ↔ a ∈ O :=
  -- Extension by zero reduces this to the self-duality of `Ô E`.
  calc
    _ ↔ ∀ r : Ô E, S.selfDualChar (r * adeleOfLocal T a) = 1 := by
      simp [locProd_O_eq_map_evalPlaces, charOnPlaces, adeleOfLocal_evalPlaces_mul, -map_mul]
    _ ↔ adeleOfLocal T a ∈ Ô E := S.forall_selfDualChar_mul_eq_one_iff _
    _ ↔ a ∈ O := by simp [mem_Ô_iff T]

open Valued in
/-- The product over the places `w` of `T` of the functions `1 + √(‖x w‖⁻¹ - 1)` is locally
integrable. -/
lemma locallyIntegrable_prod_one_add_sqrt :
    LocallyIntegrable fun x : LocProd T ↦ ∏ w : T, (1 + √(‖x w‖⁻¹ - 1)) := fun x ↦ by
  have h_loc (w : T) :
      ∃ C ∈ nhds (x w), IntegrableOn (fun y : LocField w.val ↦ 1 + √(‖y‖⁻¹ - 1)) C :=
    locallyIntegrable_one_add_sqrt_inv_norm_sub_one w.val (x w)
  choose C hC hC_int using h_loc
  exact ⟨Set.univ.pi C, set_pi_mem_nhds finite_univ fun w _ ↦ hC w,
    (Integrable.fintype_prod_dep hC_int).mono_measure (restrict_pi_pi _ C).le⟩

open Valued in
/-- Let `x` lie in the product `LocProd T` of the completions of `E` at the places `w` of `T`. The
generalized index of `x`, the inverse of `∏ w, ‖x w‖`, is at most the square of the product over
`w ∈ T` of the numbers `1 + √(‖x w‖⁻¹ - 1)`. -/
lemma ofReal_genIndex_le_enorm_prod_sq (x : LocProd T) :
    ENNReal.ofReal (genIndex x) ≤ ‖∏ w : T, (1 + √(‖x w‖⁻¹ - 1))‖ₑ ^ 2 := by
  have h_real (r : ℝ) : r ≤ (1 + √(r - 1)) ^ 2 := by grind [Real.sqrt_nonneg]
  calc
    _ = ENNReal.ofReal (∏ w : T, ‖x w‖⁻¹) := by
      rw [genIndex_eq_inv_prod_norm, Finset.prod_inv_distrib]
    _ ≤ ENNReal.ofReal (∏ w : T, (1 + √(‖x w‖⁻¹ - 1)) ^ 2) := by
      gcongr with w
      exact h_real _
    _ ≤ ‖∏ w : T, (1 + √(‖x w‖⁻¹ - 1)) ^ 2‖ₑ := Real.ofReal_le_enorm _
    _ = _ := by rw [Finset.prod_pow, enorm_pow]

end

variable (S T) in
open Valued Finset in
/-- The product of the completions of `E` at `T` carries the structure of a finite place whose
additive character is `S.charOnPlaces T`. This is `x ↦ ψ_f(-x / ϖ)` read at `T` through extension by
zero, where `ψ_f = ψf E` is the standard character of the finite adeles and `ϖ = S.deltaE` is the
generator of the different of `E` in the data `S`. -/
theorem exists_integralPlace : ∃ P : IntegralPlace (LocProd T), P.ψ = S.charOnPlaces T := by
  obtain ⟨i, hi, τ, hτ, h_sq, h_skew, h_tr⟩ :
      ∃ i ∈ O, ∃ τ ∈ O, -i * i = 1 ∧ star i = -i ∧ τ + star τ = 1 :=
    IsAdelic.exists_skew_unit (A := LocProd T)
  obtain ⟨ν, _, hν, h_split⟩ := exists_isAddHaarMeasure_skewAdjoint hi hτ h_sq h_skew h_tr
  let : TraceOne (LocProd T) := TraceOne.mk τ h_tr
  have h_dual (a : LocProd T) : (∀ r ∈ O, S.charOnPlaces T (r * a) = 1) ↔ a ∈ O :=
    forall_charOnPlaces_mul_eq_one_iff a
  -- The modulus is the inverse of the index, that is `∏ w, ‖x w‖` for a unit `x`.
  let modulus : LocProd T →* ℝ≥0∞ :=
    { toFun x := (ENNReal.ofReal (genIndex x))⁻¹
      map_one' := by simp
      map_mul' x y := by
        rw [map_mul]
        simp [ENNReal.mul_inv, genIndex_eq_inv_prod_norm, prod_nonneg] }
  have h_det (n : Type) [Fintype n] [DecidableEq n] (M : Matrix n n (LocProd T))
      (hM : IsUnit M.det) :
      volume.map (M *ᵥ ·) = (modulus M.det)⁻¹ • volume := by
    refine (map_smul_eq_inv_distribHaarChar_smul (GeneralLinearGroup.mk'' M hM)).trans ?_
    simp [modulus, inv_distribHaarChar_GL_eq_genIndex_det isOpen_O isCompact_O
      SemilocalField.isValuationPair]
  -- A locally integrable majorant of `modulus⁻¹ᐟ²`, as a product over the places.
  have h_le (u : (LocProd T)ˣ) : (modulus u)⁻¹ ≤ ‖∏ w : T, (1 + √(‖u.val w‖⁻¹ - 1))‖ₑ ^ 2 :=
    (inv_inv _).trans_le (ofReal_genIndex_le_enorm_prod_sq u.val)
  let P₀ : Floors.Place (LocProd T) :=
    { skewUnit := .mkOfMulEqOne _ _ h_sq
      skewMeasure := ν
      modulus := modulus
      ψ := S.charOnPlaces T
      kernelBound := 1
      continuous_psi := continuous_ψf.subtype_val.comp ((continuous_adeleOfLocal T).const_mul _)
      measurable_modulus := by
        simp [modulus, genIndex_eq_inv_prod_norm]
        fun_prop
      star_skewUnit := by simp [h_skew]
      measurePreserving_split := h_split
      modulus_star_and_neg := by
        simp [modulus]
        simp [genIndex_eq_inv_prod_norm]
      map_mulVec_volume := h_det
      ae_isUnit := by simpa [Pi.isUnit_iff, -Subtype.forall] using! fun w ↦ ae_eval_ne _ w 0
      exists_locallyIntegrable_bound := ⟨_, locallyIntegrable_prod_one_add_sqrt, h_le⟩
      norm_psi := by simp [charOnPlaces]
      exists_plancherel_kernel := exists_plancherel_kernel h_dual }
  exact ⟨{
      toPlace := P₀
      element_mem := hτ
      skewUnit_mem := neg_mem hi
      skewUnit_inv_mem := hi
      kernelBound_eq_one := rfl
      skewMeasure_setOf_mem := hν
      self_dual := h_dual
      modulus_eq_inv_genIndex := fun _ ↦ rfl }, rfl⟩

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
variable (S T) in
/-- Let `(S.latticeMiddle (LocProd T)).G` be the unitary group, over the product of the completions
at `T`, of `ϱ` hyperbolic planes plus the space `X₀ ⊕ E z` with its Gram matrix `S.latticeMiddle` in
the lattice basis. This group is unimodular: the inverse of a left Haar measure is left invariant.
Here `P` is any structure of a finite place on that product; its character plays no part. -/
theorem isMulLeftInvariant_haar_inv [P : IntegralPlace (LocProd T)] :
    (haar (G := (S.latticeMiddle (LocProd T)).G)).inv.IsMulLeftInvariant := by
  -- An orthonormal basis `k` over `Ô E` identifies the adelic group with `Gf E _`, whose measure is
  -- bi-invariant; push this measure forward from the points integral off `T`
  -- (`isMulLeftInvariant_measure_smul_inv`).
  obtain ⟨k, hk, hkJ⟩ :
      ∃ k ∈ intGL 𝔰.BesselIndex (Ô E), k.valᴴ * (S.latticeMiddle (𝔸f E)).splitGram * k.val = 1 :=
    exists_orthonormal_Ô (E := E) S.isUnimodular_latticeMiddle.splitGram
  let c : Gf E 𝔰.BesselIndex ≃* S.GFin := U.conj k hkJ
  have hc : Continuous c := .subtype_mk (by fun_prop) _
  have h_pr : Continuous (S.toPlaces T) := U.continuous_map
  let π : Gf E 𝔰.BesselIndex →* (S.latticeMiddle (LocProd T)).G := (S.toPlaces T).comp c.toMonoidHom
  let X : Set (Gf E 𝔰.BesselIndex) := {g | S.IsIntegralOff T (c g)}
  have hX : IsOpen X := (isOpen_intGL (isOpen_integralOff T)).preimage_val.preimage hc
  -- Each point at `T` has a lift that is integral off `T`.
  have h_lift : HasStableLifts π X := by
    intro y
    obtain ⟨x, hx, hx_off, -⟩ := exists_isIntegralOff_toPlaces_eq y
    refine ⟨c.symm x, ?_⟩
    simp [X, π, IsIntegralOff, mul_mem_cancel_left, mul_mem_cancel_right, hx, hx_off]
  -- Integral at `T` and off `T` means integral, and `k` normalizes the integral points.
  have h_int : π ⁻¹' unitaryLevel O 1 (S.latticeMiddle (LocProd T)).splitGram ∩ X =
      stdLevel E 𝔰.BesselIndex := by
    ext g
    exact (and_comm.trans mem_latticeStabilizer_iff.symm).trans (Subgroup.le_normalizer hk _).symm
  -- The measure `volume (stdLevel E _) • haar.inv` is left invariant, and `stdLevel E _` has volume
  -- one.
  have h_inv :
      (volume (stdLevel E 𝔰.BesselIndex : Set (Gf E 𝔰.BesselIndex)) •
        (haar (G := (S.latticeMiddle (LocProd T)).G)).inv).IsMulLeftInvariant := by
    rw [← h_int]
    exact isMulLeftInvariant_measure_smul_inv volume haar (h_pr.comp hc).measurable
      hX.measurableSet h_lift P.measurableSet_unitaryLevel
  simpa using h_inv

section

omit [WeilData E]

/-- The image in the finite adeles `𝔸f E` of `-ϖ⁻¹`, where `ϖ = S.deltaE`, is skew: its conjugate
under `star` is its negative. -/
lemma star_neg_inv_deltaE :
    star ((-S.deltaE.val⁻¹ : E) : 𝔸f E) = -((-S.deltaE.val⁻¹ : E) : 𝔸f E) := by
  simp [← coe_star_ringOfIntegers, S.star_deltaE]

omit [T.StarStable] in
/-- The character `S.charOnPlaces T` at `x` is `ψf E`, the standard character of the finite adeles,
at `-ϖ⁻¹` times `adeleOfLocal T x`, the extension of `x` by zero. Here `ϖ = S.deltaE`. -/
lemma charOnPlaces_apply_eq_ψf (x : LocProd T) :
    S.charOnPlaces T x = (ψf E ((-S.deltaE.val⁻¹ : E) * adeleOfLocal T x) : ℂ) := rfl

/-- The character `S.charOnPlaces T` is trivial on the traces `x + star x` for `x` in `LocProd T`.
This is because it reads a fixed character of the finite adeles through multiplication by the skew
element -ϖ⁻¹. -/
lemma charOnPlaces_add_star (x : LocProd T) : S.charOnPlaces T (x + star x) = 1 := by
  -- ϖ is skew and `ψf` takes the same value at conjugate adeles.
  have h_neg : ψf E ((-S.deltaE.val⁻¹ : E) * star (adeleOfLocal T x)) =
      ψf E (-((-S.deltaE.val⁻¹ : E) * adeleOfLocal T x)) := by
    rw [← ψf_star, star_mul', star_star, star_neg_inv_deltaE, neg_mul]
  rw [charOnPlaces_apply_eq_ψf, map_add, adeleOfLocal_star, mul_add, AddChar.map_add_eq_mul, h_neg,
    ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, Circle.coe_one]

end

variable (T) in
open Valued Finset in
/-- Let `ϱ = 𝔰.ϱ` be the number of hyperbolic planes, `k = 𝔰.k` the dimension of the definite
summand `X₀`, and `S.latticeMiddle` the Gram matrix of `X₀ ⊕ E z` in the lattice basis. The product
of the completions at a conjugation-stable finite set `T` is a finite place `P` with a place datum
`F`, with 3ϱ + 6 further hyperbolic pairs and an orthonormal part of size `k - (6ϱ + 13)`, that
satisfies `New.Filling.IsFillingData`. -/
theorem exists_isFillingData :
    ∃ _ : IntegralPlace (LocProd T),
      ∃ F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T))
        (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5),
      S.IsFillingData T F := by
  obtain ⟨P, hψ⟩ := S.exists_integralPlace T
  -- The lower bound on `𝔰.k` makes the subtraction of natural numbers exact.
  have h_k : 1000 * (2 * 𝔰.ϱ + 2) ≤ 𝔰.k := S.thousand_mul_le_k
  have h_card : 𝔰.k =
      Fintype.card (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) + 2 * (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5) + 1 := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨F, hF, hg⟩ :
      ∃ F : PlaceData _ (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5),
        P.IsLatticeData F ∧ F.levelUnit = S.ideleM.map (evalPlaces T) :=
    P.exists_isLatticeData (by simp) (by simp [ideleM_val, -Nat.cast_mul]) h_card
  -- The zeta value at `T` is at most the global one.
  have h_zeta : idealZeta P.integers (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 4) ^ 𝔰.n ≤ .ofReal (1 + 2⁻¹ ^ 𝔰.n) := by
    grw [idealZeta_locProd_le, idealZeta_intAdeles_pow_le _ S.mul_finrank_le_pow]
  have : P.IsLargeLatticeData F := by
    refine ⟨hF, ⟨h_zeta, ?_⟩, hψ ▸ charOnPlaces_add_star, haar.inv, ?_, inferInstance⟩
    · simp
      lia
    · exact { toIsMulLeftInvariant := S.isMulLeftInvariant_haar_inv T }
  exact ⟨P, F, { psi_eq := hψ, levelUnit_eq := hg }⟩

end New.Filling
