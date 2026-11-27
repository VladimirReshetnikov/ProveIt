import New.Spanning.RemainingTerms.FramesOverLattice
import New.Spanning.Unfolding.Climbing

/-!
# Sums over lattices of given corank and small discriminant

This file bounds the sum of `(disc L) ^ (-k)` over all classes and all lattices `L ⊂ Λ ∩ X₀` of
given corank and small discriminant (`sum_discriminant_inv_le`).

Notions from other files:
* `X₀ = E ^ κ` is the hermitian space with the standard form, `k` is the cardinality of `κ`, and
  `k₀ = 𝔰.k₀` is a distinguished element of `κ`. `Gf E κ` is the finite adelic unitary group of
  `X₀`, and `stdLevel E κ` is the stabiliser of the standard lattice `Ô ^ κ` in it.
* `S.piN` is the finite idele `π̄` with `π π̄ = N`, and in the bounds `f = numInfPlaces E`.
* `S.Classes` is the set of double cosets of `Gf E κ` under the rational points and the level
  `S.sourceLevel`. If `g` is the chosen representative of the class `c`, then the lattice
  `S.classLatticeX₀ c`, also written `Λ ∩ X₀`, consists of the vectors `v` for which `g⁻¹ v` is
  integral with entry `k₀` divisible by `π̄`.
* `discriminant r L` is the square root of the generalised index `genIndex` of the Gram determinant
  of a basis of the lattice `L` of rank `r`.
-/

noncomputable section

namespace New.Filling

/-! ## Means over the classes, and cosets told apart by one row -/

section ClassesAndCosets

open Matrix ENNReal Finset Fintype DoubleCoset Subgroup

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}

/-- Let `A` be finite and nonempty with elements mapped by `a` into the finite adelic unitary group
`Gf E κ`, and let `f` be a function on `S.Classes`, the double cosets of this group under the
rational points and the level. If for every `u` the sum of `f` over the classes of the translates
`u * a φ`, `φ ∈ A`, is at most `card A * b`, then the sum of `f` over all classes is at most
`card S.Classes * b` (for `b ≥ 0`). -/
lemma sum_classes_le_of_sum_translates_le {A : Type} [Fintype A] [Nonempty A] (a : A → Gf E 𝔰.κ)
    (f : S.Classes → ℝ≥0∞) {b : ℝ} (hb : 0 ≤ b)
    (h_translates : ∀ u : Gf E 𝔰.κ, ∑ φ : A, f ⟦u * a φ⟧ ≤ .ofReal (card A * b)) :
    ∑ c : S.Classes, f c ≤ .ofReal (card S.Classes * b) := by
  -- `f` is finite, since every class is a term of one of the sums.
  have f_ne_top : ∀ c : S.Classes, f c ≠ ∞ := Quotient.ind fun g ↦ by
    obtain ⟨φ⟩ : Nonempty A := inferInstance
    simpa using
      sum_ne_top.mp (ne_top_of_le_ne_top ofReal_ne_top (h_translates (g / a φ))) φ (mem_univ φ)
  lift f to S.Classes → NNReal using f_ne_top
  -- The defect `δ = b - f` is a function on the double cosets.
  let δ (g : Gf E 𝔰.κ) : ℝ := b - f ⟦g⟧
  have δ_inv : ∀ γ ∈ stdRatPoints, ∀ k ∈ S.sourceLevel, ∀ g : Gf E 𝔰.κ, δ (γ * g * k) = δ g := by
    intro γ hγ k hk g
    have same_class : (⟦g⟧ : S.Classes) = ⟦γ * g * k⟧ :=
      Quotient.sound (DoubleCoset.rel_iff.mpr ⟨γ, hγ, k, hk, rfl⟩)
    simp only [δ, same_class]
  have δ_fixed : S.sourceLevel ≤ rightStabilizer δ := fun k hk g ↦ by
    simpa using δ_inv 1 (one_mem _) k hk g
  have δ_smooth : δ ∈ smoothInvariants stdRatPoints :=
    ⟨fun γ hγ g ↦ by simpa using δ_inv γ hγ 1 (one_mem _) g,
      isOpen_mono δ_fixed S.isLevel_sourceLevel.isOpen⟩
  -- The sum of the translates of `δ` is nonnegative, and the integral is translation invariant.
  have translates_nonneg (g : Gf E 𝔰.κ) : 0 ≤ ∑ φ : A, δ (g * a φ) := by
    have h_real : ((∑ φ : A, f ⟦g * a φ⟧ : NNReal) : ℝ) ≤ card A * b :=
      (le_ofReal_iff_toReal_le coe_ne_top (by positivity)).mp
        ((ofNNReal_finsetSum _ _).trans_le (h_translates g))
    simpa [δ] using h_real
  have integral_nonneg : 0 ≤ ∑ _φ : A, classIntegral stdRatPoints S.sourceLevel δ :=
    calc 0 ≤ classIntegral stdRatPoints S.sourceLevel fun g ↦ ∑ φ : A, δ (g * a φ) := by
          -- The integral is a weighted sum of values with nonnegative weights.
          refine mul_nonneg (by simp) (finsum_nonneg fun q ↦ mul_nonneg (by simp) ?_)
          exact translates_nonneg q.out
      _ = ∑ _φ : A, classIntegral stdRatPoints S.sourceLevel δ :=
          classIntegral_sum univ (fun _ ↦ AddMonoidHom.id ℝ) a (fun _ ↦ δ_smooth) fun _ ↦ rfl
  -- As `S.sourceLevel` fixes `δ`, its integral is the sum of `b - f c` over the classes `c`.
  have integral_eq :
      classIntegral stdRatPoints S.sourceLevel δ = ∑ c : S.Classes, (b - f c : ℝ) := by
    rw [classIntegral_eq_classSum δ_fixed, classSum_sourceLevel_eq_sum]
    exact sum_congr rfl fun c _ ↦ congrArg (fun d : S.Classes ↦ b - (f d : ℝ)) c.out_eq
  have h_real : ((∑ c : S.Classes, f c : NNReal) : ℝ) ≤ card S.Classes * b := by
    simpa [integral_eq, Fintype.card_pos] using integral_nonneg
  rw [← ofNNReal_finsetSum]
  exact (le_ofReal_iff_toReal_le coe_ne_top (by positivity)).mpr h_real

variable (S) in
/-- The rows `𝔰.k₀` of the matrices of `y⁻¹` and `y'⁻¹` are congruent modulo `S.piN`: their
difference maps every integral vector into `Ô π̄`. -/
abbrev InverseRowsCongruent (y y' : stdLevel E 𝔰.κ) : Prop :=
  let Y : Matrix 𝔰.κ 𝔰.κ (𝔸f E) := (y⁻¹ : Gf E 𝔰.κ)
  let Y' : Matrix 𝔰.κ 𝔰.κ (𝔸f E) := (y'⁻¹ : Gf E 𝔰.κ)
  colLattice (Ô E) (replicateRow Unit (Y 𝔰.k₀) - replicateRow Unit (Y' 𝔰.k₀)) ≤
    .comap (.proj ()) (Ô E ∙ S.piN.1)

/-- Let `y`, `y'` be integral unitary matrices whose inverses have congruent rows `𝔰.k₀` modulo the
idele `S.piN` of the filling `S` (`InverseRowsCongruent`). Then `y` and `y'` lie in the same coset
of the subgroup of elements that the inclusion `S.inclHFin` of `Gf E κ` in the unitary group of the
large space maps into the subgroup `S.latticeStabilizer` of integral matrices in the lattice
basis. -/
lemma inv_mul_mem_of_inverseRowsCongruent {y y' : stdLevel E 𝔰.κ}
    (h_congr : S.InverseRowsCongruent y y') :
    y⁻¹ * y' ∈ (S.latticeStabilizer.comap S.inclHFin).subgroupOf (stdLevel E 𝔰.κ) := by
  -- It is enough that row `k₀` of `y⁻¹ y'` is congruent to that of `1`.
  refine S.inclHFin_mem_latticeStabilizer_iff.2 ⟨(y⁻¹ * y').2, fun _ j ↦ ?_⟩
  -- Apply the difference of the rows to the integral column `j` of `y'`.
  let Y : Matrix 𝔰.κ 𝔰.κ (𝔸f E) := ((y⁻¹ : stdLevel E 𝔰.κ) : Gf E 𝔰.κ)
  let Y' : Matrix 𝔰.κ 𝔰.κ (𝔸f E) := ((y'⁻¹ : stdLevel E 𝔰.κ) : Gf E 𝔰.κ)
  let M : Matrix 𝔰.κ 𝔰.κ (𝔸f E) := (y' : Gf E 𝔰.κ)
  let row : Matrix Unit 𝔰.κ (𝔸f E) := replicateRow Unit (Y 𝔰.k₀) - replicateRow Unit (Y' 𝔰.k₀)
  have h_image : row *ᵥ Mᵀ j ∈ colLattice (Ô E) row :=
    ⟨Mᵀ j, y'.2.isIntMatrix.transpose j, rfl⟩
  have h_entry : ((Y - Y') * M) 𝔰.k₀ j ∈ Ô E ∙ S.piN.1 := h_congr h_image
  simpa [M, Y, Y', Matrix.sub_mul] using h_entry

end ClassesAndCosets

/-!
## Lattices of given corank

The lattice of a class is the kernel of a row modulo `piN` on a unimodular lattice. One averages
over the rows and counts the rows that vanish modulo `piN` on a given lattice. One then sums over
the sublattices of finite index of a primitive lattice, and finally over the primitive lattices.
-/

section CrudeLattices

open NumberField Matrix Module Fintype ENNReal Pointwise

variable {E : Type} [Field E] [CMType E] [HasPrimitiveRoot5040 E] {𝔰 : Shape}

section Forms

variable {S : Filling E 𝔰}

variable (S) in
/-- The lattices of rank `r` in `L₀` with discriminant at most `S.discriminantBound`. -/
abbrev BoundedDiscSublattice (r : ℕ) (L₀ : Submodule (Ô E) (𝔰.κ → 𝔸f E)) : Type :=
  {L : Submodule (Ô E) (𝔰.κ → 𝔸f E) //
    IsLatticeOfRank r L ∧ L ≤ L₀ ∧ discriminant r L ≤ S.discriminantBound}

/-- The unimodular lattice `u Ô ^ κ`: the vectors `v` with `u⁻¹ v` integral. -/
abbrev unimodularLattice (u : Gf E 𝔰.κ) : Submodule (Ô E) (𝔰.κ → 𝔸f E) :=
  preimageLattice (Ô E) u.1.inv

variable (S) in
/-- The linear form "row `k₀` of `y⁻¹ u⁻¹`" on `u Ô ^ κ`, called the form of `y`, vanishes on `L`
modulo `piN`. -/
def RowVanishesModPiN (u : Gf E 𝔰.κ) (y : stdLevel E 𝔰.κ) (L : Submodule (Ô E) (𝔰.κ → 𝔸f E)) :
    Prop :=
  ∀ v ∈ L,
    (((y⁻¹ : Gf E 𝔰.κ) : Matrix 𝔰.κ 𝔰.κ (𝔸f E)) *ᵥ u.1.inv *ᵥ v) 𝔰.k₀ ∈ Ô E ∙ S.piN.1

variable (S) in
/-- The term `(disc L) ^ (-k)`, for the discriminant in rank `r`, if the form of `y` on `u Ô ^ κ`
vanishes on `L` modulo `piN`, and `0` otherwise. -/
def discWeightIfRowVanishes (u : Gf E 𝔰.κ) (y : stdLevel E 𝔰.κ) (r : ℕ) :
    Submodule (Ô E) (𝔰.κ → 𝔸f E) → ℝ≥0∞ :=
  {L : Submodule (Ô E) (𝔰.κ → 𝔸f E) | S.RowVanishesModPiN u y L}.indicator
    fun L ↦ ENNReal.ofReal (discriminant r L ^ 𝔰.k)⁻¹

variable (S) in
/-- The cosets in `stdLevel E κ` of the subgroup of elements that `inclHFin` maps into
`latticeStabilizer`: those whose row `k₀` is congruent to that of `1` modulo `piN`. They
parametrise the positions of the form modulo `piN`. -/
abbrev LatticeStabilizerCoset : Type :=
  stdLevel E 𝔰.κ ⧸ (S.latticeStabilizer.comap S.inclHFin).subgroupOf (stdLevel E 𝔰.κ)

/-! ### Unimodular lattices -/

omit [HasPrimitiveRoot5040 E] in
/-- Let the chosen representative of the class `c` be `η u y` with `η` rational and `y` integral,
and let `L` lie in the lattice `Λ ∩ X₀` of `c`, which consists of the vectors `v` for which
`(η u y)⁻¹ v` is integral with entry `k₀` divisible by `π̄ = S.piN`. Then `η⁻¹ L` lies in `u Ô ^ κ`,
and the form of `y` vanishes on it modulo `π̄`. -/
lemma map_le_and_rowVanishesModPiN_of_out_eq {c : S.Classes} {η : U (stdSpace E 𝔰.κ).J}
    {u : Gf E 𝔰.κ} {y : stdLevel E 𝔰.κ} (hc : c.out = (stdSpace E 𝔰.κ).embFin η * u * y)
    {L : Submodule (Ô E) (𝔰.κ → 𝔸f E)} (h_le : L ≤ S.classLatticeX₀ c) :
    L.map ((finAdeleMatrix (η⁻¹ : GL 𝔰.κ E).val).mulVecLin.restrictScalars (Ô E)) ≤
      unimodularLattice u ∧
    S.RowVanishesModPiN u y
      (L.map ((finAdeleMatrix (η⁻¹ : GL 𝔰.κ E).val).mulVecLin.restrictScalars (Ô E))) := by
  let Y : Matrix 𝔰.κ 𝔰.κ (𝔸f E) := ((y⁻¹ : stdLevel E 𝔰.κ) : Gf E 𝔰.κ)
  let H : Matrix 𝔰.κ 𝔰.κ (𝔸f E) := finAdeleMatrix (η⁻¹ : GL 𝔰.κ E).val
  have hH : H = ((stdSpace E 𝔰.κ).embFin η⁻¹ : Gf E 𝔰.κ) := by simp [H, -map_inv]
  have h_coord : S.classCoordX₀ c = middleInclusionMatrix 𝔰 S.piN * (Y * (u.1.inv * H)) := by
    rw [classCoordX₀, hc, _root_.mul_inv_rev, _root_.mul_inv_rev, ← map_inv, hH]
    -- The coercion to matrices respects products, and turns `u⁻¹` into `u.1.inv`.
    rfl
  -- For `v ∈ L` the vector `y⁻¹ u⁻¹ η⁻¹ v` is integral, with entry `k₀` divisible by `piN`.
  have h_vector (v : 𝔰.κ → 𝔸f E) (hv : v ∈ L) :
      Y *ᵥ u.1.inv *ᵥ H *ᵥ v ∈ intVectors (Ô E) 𝔰.κ ∧
      (Y *ᵥ u.1.inv *ᵥ H *ᵥ v) 𝔰.k₀ ∈ Ô E ∙ S.piN.1 := by
    have h_int : IsIntMatrix (Ô E)
        (middleInclusionMatrix 𝔰 S.piN * replicateCol Unit (Y *ᵥ u.1.inv *ᵥ H *ᵥ v)) := fun i j ↦ by
      -- `classLatticeX₀` consists of the vectors that `classCoordX₀` makes integral.
      have h_entry : (S.classCoordX₀ c *ᵥ v) i ∈ Ô E := h_le hv i
      rwa [h_coord, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec] at h_entry
    obtain ⟨h_all, h_row⟩ := S.isIntMatrix_middleInclusionMatrix_mul_iff.1 h_int
    exact ⟨fun i ↦ h_all i (), h_row ()⟩
  constructor
  · rintro _ ⟨v, hv, rfl⟩
    exact (mulVec_mem_intVectors_iff (inv_mem y.2)).1 (h_vector v hv).left
  · rintro _ ⟨v, hv, rfl⟩
    exact (h_vector v hv).right

/-- Let `E` contain a primitive 5040th root of unity, let `S` be filling data over `E`, and let the
chosen representative of the class `c` be `η u y` with `η` rational and `y` integral. The sum of
`(disc L) ^ (-k)`, `k = #κ`, over the lattices `L` of rank `r` and discriminant at most
`S.discriminantBound` in `Λ ∩ X₀` is at most the same sum over those in `u Ô ^ κ` on which the form
"row `𝔰.k₀` of `y⁻¹ u⁻¹`" vanishes modulo `S.piN`. -/
lemma tsum_discriminant_inv_le_of_out_eq {c : S.Classes} {η : U (stdSpace E 𝔰.κ).J} {u : Gf E 𝔰.κ}
    {y : stdLevel E 𝔰.κ} (hc : c.out = (stdSpace E 𝔰.κ).embFin η * u * y) (r : ℕ) :
    ∑' L : S.BoundedDiscSublattice r (S.classLatticeX₀ c),
      ENNReal.ofReal (discriminant r L.val ^ 𝔰.k)⁻¹ ≤
      ∑' L : S.BoundedDiscSublattice r (unimodularLattice u),
        S.discWeightIfRowVanishes u y r L.val := by
  -- The rational isometry `η⁻¹` moves the lattices injectively and preserves the discriminant.
  let H : Matrix 𝔰.κ 𝔰.κ E := (η⁻¹ : GL 𝔰.κ E).val
  let P : (𝔰.κ → 𝔸f E) →ₗ[Ô E] 𝔰.κ → 𝔸f E := (finAdeleMatrix H).mulVecLin.restrictScalars (Ô E)
  have hH : Hᴴ * H = 1 := by simpa [H] using mem_U.1 η⁻¹.2
  have h_inv : finAdeleMatrix Hᴴ * finAdeleMatrix H = 1 := by
    simpa only [Matrix.map_mul, Matrix.map_one, map_zero, map_one] using congrArg finAdeleMatrix hH
  have hP : Function.Injective P := injective_restrictScalars_mulVecLin h_inv
  have h_map (L : S.BoundedDiscSublattice r (S.classLatticeX₀ c)) :
      (IsLatticeOfRank r (L.1.map P) ∧ L.1.map P ≤ unimodularLattice u ∧
        discriminant r (L.1.map P) ≤ S.discriminantBound) ∧
      S.RowVanishesModPiN u y (L.1.map P) ∧ discriminant r (L.1.map P) = discriminant r L.1 := by
    obtain ⟨L, hL, h_le, h_small⟩ := L
    obtain ⟨h_rank, h_disc⟩ := hL.map_of_unitary hH
    obtain ⟨h_map_le, h_kills⟩ := map_le_and_rowVanishesModPiN_of_out_eq hc h_le
    exact ⟨⟨h_rank, h_map_le, h_disc.trans_le h_small⟩, h_kills, h_disc⟩
  let move (L : S.BoundedDiscSublattice r (S.classLatticeX₀ c)) :
    S.BoundedDiscSublattice r (unimodularLattice u) :=
    ⟨L.1.map P, (h_map L).1⟩
  have h_move : Function.Injective move := fun L L' h ↦
    Subtype.ext (Submodule.map_injective_of_injective hP (congrArg Subtype.val h))
  calc _ = ∑' L : S.BoundedDiscSublattice r (S.classLatticeX₀ c),
         S.discWeightIfRowVanishes u y r (move L).1 := by
        refine tsum_congr fun L ↦ ?_
        obtain ⟨-, h_kills, h_disc⟩ := h_map L
        rw [discWeightIfRowVanishes, Set.indicator_of_mem h_kills, h_disc]
    _ ≤ _ := tsum_comp_le_tsum_of_injective h_move fun L ↦ S.discWeightIfRowVanishes u y r L.1

omit [HasPrimitiveRoot5040 E] in
/-- Let `u` be in `Gf E 𝔰.κ`, and let `φ` be a coset in `stdLevel E 𝔰.κ` of the preimage under
`inclHFin` of `latticeStabilizer`, with chosen element `φ.out`. Then the chosen representative of
the class of `u * φ.out` in the double cosets `S.Classes` equals `embFin η * u * y`. Here `η` is
some rational point of the unitary group `U` of the standard form on `𝔰.κ`, and `y` is some element
of `stdLevel E 𝔰.κ` lying in the coset `φ`. Of the standing hypotheses `S.IsAdmissible`, only one is
used: the level `sourceLevel` of `S`, which defines the double cosets `S.Classes`, is the preimage
of K(M). -/
lemma exists_mk_out_eq_embFin_mul [S.IsAdmissible] (u : Gf E 𝔰.κ) (φ : S.LatticeStabilizerCoset) :
    ∃ (η : U (stdSpace E 𝔰.κ).J) (y : stdLevel E 𝔰.κ),
      (y : S.LatticeStabilizerCoset) = φ ∧
      (⟦u * φ.out⟧ : S.Classes).out = (stdSpace E 𝔰.κ).embFin η * u * y := by
  obtain ⟨_, ⟨η, rfl⟩, g, hg, h_out⟩ : ∃ γ ∈ stdRatPoints (E := E), ∃ g ∈ S.sourceLevel,
      (⟦u * φ.out⟧ : S.Classes).out = γ * (u * φ.out : Gf E 𝔰.κ) * g :=
    (DoubleCoset.eq ..).1 (DoubleCoset.out_eq' ..).symm
  have hg_level : S.inclHFin g ∈ S.principalLevel := IsAdmissible.sourceLevel_eq.le hg
  have hg_stab : S.inclHFin g ∈ S.latticeStabilizer :=
    (S.principalLevel_eq_unitaryLevel.le hg_level).1
  refine ⟨η, φ.out * ⟨g, S.isLevel_sourceLevel.le hg⟩, ?_, h_out.trans (by simp [mul_assoc])⟩
  exact (QuotientGroup.mk_mul_of_mem φ.out hg_stab).trans φ.out_eq

/-! ### Forms and sublattices -/

variable (S) in
/-- The generalised index of `S.piN` is `N ^ f`, where `N = π π̄` and `f` is the number of
infinite places of `E`. -/
lemma genIndex_piN_eq_pow : genIndex S.piN.val = S.N ^ numInfPlaces E := by
  have h_sq : genIndex S.piN.1 ^ 2 = (S.N ^ numInfPlaces E) ^ 2 := by
    rw [← genIndex_natCast, ← S.piN_mul_star, map_mul, genIndex_star, sq]
  exact (pow_left_inj₀ (genIndex_pos _).le (by positivity) two_ne_zero).1 h_sq

omit [HasPrimitiveRoot5040 E] in
/-- A vector lies in `d Ô ^ ι` if and only if its multiple by `d⁻¹` is integral. -/
lemma mem_smul_intVectors_iff {ι : Type} {d : (𝔸f E)ˣ} {v : ι → 𝔸f E} :
    v ∈ d • intVectors (Ô E) ι ↔ d⁻¹ • v ∈ intVectors (Ô E) ι := by
  refine ⟨?_, fun hv ↦ ⟨d⁻¹ • v, hv, smul_inv_smul d v⟩⟩
  rintro ⟨w, hw : w ∈ intVectors (Ô E) ι, rfl⟩
  simpa [inv_smul_smul, ← Units.smul_def] using hw

omit [HasPrimitiveRoot5040 E] in
/-- Let `U` be invertible with `U` and `U⁻¹` integral, and let `m` be its first `r` columns
`firstCols e U`. Two forms `v`, `w` are congruent modulo `d` if their values on the other columns
of `U` are, and if their values on `m A`, divided by `d`, differ by a combination of the rows of
`A` with integral coefficients. -/
lemma sub_mem_smul_intVectors_of_values {π : Type} [Fintype π] [DecidableEq π] {r l : ℕ}
    {e : Fin r ⊕ Fin l ≃ π} {U : GL π (𝔸f E)} (hU : U ∈ intGL π (Ô E))
    {A : GL (Fin r) (𝔸f E)} {d : (𝔸f E)ˣ} {v w : π → 𝔸f E}
    (h_rows : d⁻¹ • v ᵥ* (firstCols e U * A.val) - d⁻¹ • w ᵥ* (firstCols e U * A.val) ∈
      colLattice (Ô E) A.valᵀ)
    (h_rest : (fun i : Fin l ↦ (v ᵥ* U.val) (e (.inr i)) - (w ᵥ* U.val) (e (.inr i))) ∈
      d • intVectors (Ô E) (Fin l)) :
    v - w ∈ d • intVectors (Ô E) π := by
  obtain ⟨s, hs_int, hs : A.valᵀ *ᵥ s =
    d⁻¹ • v ᵥ* (firstCols e U * A.val) - d⁻¹ • w ᵥ* (firstCols e U * A.val)⟩ := h_rows
  let z : π → 𝔸f E := d⁻¹ • (v - w)
  have h_first : z ᵥ* firstCols e U = s := by
    refine vecMul_injective_of_isUnit A.isUnit ?_
    show (z ᵥ* firstCols e U) ᵥ* A.val = s ᵥ* A.val
    rw [← mulVec_transpose A.val s, hs, vecMul_vecMul, smul_vecMul, sub_vecMul, smul_sub]
  have h_values : z ᵥ* U.val ∈ intVectors (Ô E) π := by
    intro p
    obtain ⟨i | i, rfl⟩ := e.surjective p
    · rw [show (z ᵥ* U.val) (e (.inl i)) = s i from congrFun h_first i]
      exact hs_int i
    · simpa only [z, smul_vecMul, sub_vecMul, Pi.smul_apply, Pi.sub_apply] using
        mem_smul_intVectors_iff.1 h_rest i
  refine mem_smul_intVectors_iff.2 ?_
  simpa only [mulVec_transpose, vecMul_vecMul, U.mul_inv, vecMul_one] using
    hU.isIntMatrix_inv.transpose.mulVec h_values

/-- **Few forms vanish on a sublattice.** Let the CM field `E` contain a primitive 5040th root of
unity. Let `m` be a basis of a primitive sublattice of rank `r` and corank `l` in `Ô ^ π`, and let
`L` be its sublattice with the basis `m A`. For `a` in a set `B` let `Y a` be integral linear forms
whose values on `L` are divisible by the integral idele `d` and which are pairwise incongruent
modulo `d`. Then `B` has at most `[det A] [d] ^ l` elements, where `[·]` is the generalised index
and `[det A]` is the index of `L` in the primitive sublattice. -/
lemma encard_le_of_vecMul_mem_smul {α π : Type} [Fintype π] {r l : ℕ} {B : Set α}
    (Y : α → π → 𝔸f E) {m : Matrix π (Fin r) (𝔸f E)} {A : GL (Fin r) (𝔸f E)} {d : (𝔸f E)ˣ}
    (hY : ∀ a ∈ B, Y a ∈ intVectors (Ô E) π) (hm : IsPrimitiveMatrix (Ô E) m)
    (h_rank : r + l = card π) (hA : IsIntMatrix (Ô E) A.val) (hd : d.val ∈ Ô E)
    (h_kills : ∀ a ∈ B, Y a ᵥ* (m * A.val) ∈ d • intVectors (Ô E) (Fin r))
    (h_incongruent : ∀ a ∈ B, ∀ b ∈ B, Y a - Y b ∈ d • intVectors (Ô E) π → a = b) :
    B.encard ≤ ENNReal.ofReal (genIndex A.val.det * genIndex d.val ^ l) := by
  classical
  -- Extend `m` to a basis `U` of `Ô ^ π`, and write the values of `Y a` on `m A` as `d W a`. The
  -- class of `W a` modulo the rows of `A` fixes the values on `m` modulo `d`, and the values on the
  -- other `l` basis vectors have `[d] ^ l` classes modulo `d`.
  let e : Fin r ⊕ Fin l ≃ π := equivOfCardEq (by simpa using h_rank)
  obtain ⟨U, hU, rfl⟩ : ∃ U ∈ intGL π (Ô E), m = firstCols e U :=
    (isValuationPair_Ô.exists_firstCols_iff e).2 hm
  let W (a : α) : Fin r → 𝔸f E := d⁻¹ • Y a ᵥ* (firstCols e U * A.val)
  let rest (a : α) (i : Fin l) : 𝔸f E := (Y a ᵥ* U.val) (e (.inr i))
  have h_rest_int (a : α) (ha : a ∈ B) : rest a ∈ intVectors (Ô E) (Fin l) := fun i ↦ by
    simpa only [mulVec_transpose] using hU.isIntMatrix.transpose.mulVec (hY a ha) (e (.inr i))
  have hW_int (a : α) (ha : a ∈ B) : W a ∈ intVectors (Ô E) (Fin r) :=
    mem_smul_intVectors_iff.1 (h_kills a ha)
  have hA_pos : 0 < genIndex A.val.det := genIndex_pos A.det
  have h_index : (submoduleIndex (colLattice (Ô E) A.valᵀ) (intVectors (Ô E) (Fin r)) : ℝ) =
      genIndex A.val.det := by
    rw [← det_transpose]
    exact submoduleIndex_colLattice_intVectors (M := transposeGL A) hA.transpose
  have h_unique (a : α) (ha : a ∈ B) (b : α) (hb : b ∈ B)
      (h_rows : W a - W b ∈ colLattice (Ô E) A.valᵀ)
      (h_rest : rest a - rest b ∈ d • intVectors (Ô E) (Fin l)) : a = b :=
    h_incongruent a ha b hb (sub_mem_smul_intVectors_of_values hU h_rows h_rest)
  -- Sort the forms by the class of `W a`, and those in one such class by the class of `rest a`.
  have h_class (C : Set α) (hC : C ⊆ B)
      (h_rows : ∀ a ∈ C, ∀ b ∈ C, W a - W b ∈ colLattice (Ô E) A.valᵀ) :
      C.encard ≤ ENNReal.ofReal (genIndex d.val ^ l) := by
    refine (encard_le_of_colouring (fun a (_ : Unit) ↦ rest a) (submoduleIndex_smul_ne_zero hd)
      (fun a ha _ ↦ h_rest_int a (hC ha)) (x := 1) fun D hD _ _ h_rest ↦ ?_).trans_eq ?_
    · have h_single : D.encard ≤ 1 := Set.encard_le_one_iff.2 fun a b ha hb ↦
        h_unique a (hC (hD ha)) b (hC (hD hb)) (h_rows a (hD ha) b (hD hb)) (h_rest a ha b hb ())
      exact_mod_cast h_single
    · rw [submoduleIndex_smul_intVectors hd, card_unit, pow_one, mul_one, Fintype.card_fin]
  have h_finite : submoduleIndex (colLattice (Ô E) A.valᵀ) (intVectors (Ô E) (Fin r)) ≠ 0 :=
    mod_cast h_index.trans_ne hA_pos.ne'
  refine (encard_le_of_colouring (fun a (_ : Unit) ↦ W a) h_finite (fun a ha _ ↦ hW_int a ha)
    fun C hC _ _ h_rows ↦ h_class C hC fun a ha b hb ↦ h_rows a ha b hb ()).trans_eq ?_
  rw [h_index, card_unit, pow_one, ofReal_mul hA_pos.le]

/-- Let `E` contain a primitive 5040th root of unity, and let `S` be filling data over `E` with
prime `N = π π̄` and `π̄ = S.piN`. The set `S.LatticeStabilizerCoset` is the quotient of `stdLevel`,
the group of integral unitary matrices on `κ`, by its subgroup of matrices whose row `𝔰.k₀` is
congruent to that of `1` modulo `π̄`. Let `y φ` be an element of each such coset `φ`,
let `V` have codimension `l`, and let `A` be invertible over the finite adeles, with integral
entries. Let `m = sublatticeBasis u.val.val_inv V` be the basis of the adelic points of `V` in
`u Ô ^ κ`. Then for at most `[det A] (N ^ f) ^ l` cosets `φ` the form "row `𝔰.k₀` of
`(y φ)⁻¹ u⁻¹`" vanishes modulo `π̄` on the lattice with basis `m A`. Here `[·]` is the generalised
index and `f` is the number of infinite places. -/
lemma encard_rowVanishesModPiN_le (u : Gf E 𝔰.κ) {y : S.LatticeStabilizerCoset → stdLevel E 𝔰.κ}
    (hy : ∀ φ : S.LatticeStabilizerCoset, (y φ : S.LatticeStabilizerCoset) = φ)
    {V : Submodule E (𝔰.κ → E)} {l : ℕ}
    (h_rank : finrank E V + l = 𝔰.k) {A : GL (Fin (finrank E V)) (𝔸f E)}
    (hA : IsIntMatrix (Ô E) A.val) :
    {φ : S.LatticeStabilizerCoset | S.RowVanishesModPiN u (y φ)
        (colLattice (Ô E) ((sublatticeBasis u.val.val_inv V).val * A.val))}.encard ≤
      ENNReal.ofReal (genIndex A.val.det * (S.N ^ numInfPlaces E) ^ l) := by
  -- Count the rows `k₀` of the `(y φ)⁻¹` modulo `piN`; congruent rows belong to one coset.
  let m : Matrix 𝔰.κ (Fin (finrank E V)) (𝔸f E) := (sublatticeBasis u.1.val_inv V).1
  let B : Set S.LatticeStabilizerCoset :=
    {φ | S.RowVanishesModPiN u (y φ) (colLattice (Ô E) (m * A.1))}
  let row (φ : S.LatticeStabilizerCoset) : 𝔰.κ → 𝔸f E :=
    (((y φ)⁻¹ : stdLevel E 𝔰.κ) : Gf E 𝔰.κ).val.val 𝔰.k₀
  have h_kills (φ : S.LatticeStabilizerCoset) (hφ : φ ∈ B) : row φ ᵥ* (u.1.inv * m * A.1) ∈
      S.piN • intVectors (Ô E) (Fin (finrank E V)) := by
    have h_entry (i : Fin (finrank E V)) : ∃ a ∈ Ô E,
        S.piN * a = (row φ ᵥ* (u.1.inv * m * A.1)) i := by
      rw [Matrix.mul_assoc]
      obtain ⟨a, ha, h_value⟩ := mem_span_singleton_iff_exists_mul.1 (hφ _ (col_mem_colLattice i))
      exact ⟨a, ha, h_value.symm⟩
    choose a ha h_value using h_entry
    exact ⟨a, ha, funext h_value⟩
  have h_apart (φ : S.LatticeStabilizerCoset) (_ : φ ∈ B) (φ' : S.LatticeStabilizerCoset)
    (_ : φ' ∈ B)
      (h_congr : row φ - row φ' ∈ S.piN • intVectors (Ô E) 𝔰.κ) : φ = φ' := by
    obtain ⟨a, ha, h_value⟩ := h_congr
    rw [← hy φ, ← hy φ']
    refine QuotientGroup.eq.2 (inv_mul_mem_of_inverseRowsCongruent (colLattice_le fun i ↦ ?_))
    -- Entry `i` of the difference of the two rows is `π̄ a i`.
    exact mem_span_singleton_iff_exists_mul.2 ⟨a i, ha i, (congrFun h_value i).symm⟩
  rw [← S.genIndex_piN_eq_pow]
  exact encard_le_of_vecMul_mem_smul row (fun φ _ ↦ (y φ).2.isIntMatrix_inv 𝔰.k₀)
    (isPrimitiveMatrix_mul_sublatticeBasis u.1.val_inv V) h_rank hA S.piN_mem h_kills h_apart

/-- Let `E` contain a primitive 5040th root of unity, and let `S` be filling data over `E` with
prime `N = π π̄` and `π̄ = S.piN`. The set `S.LatticeStabilizerCoset` is the quotient of `stdLevel`,
the group of integral unitary matrices on `κ`, by its subgroup of matrices whose row `𝔰.k₀` is
congruent to that of `1` modulo `π̄`. Let `y φ` be an element of each such coset `φ`, and let
`L ⊂ u Ô ^ κ` be a lattice of rank `r` and corank `l`. There is a subspace `V` of dimension `r` such
that `L` has a finite index `i` in the lattice `saturatedLattice` of adelic points of `V` in
`u Ô ^ κ`, `disc L` is `i` times the discriminant of that lattice, and for at most `i (N ^ f) ^ l`
of the `φ` the form "row `𝔰.k₀` of `(y φ)⁻¹ u⁻¹`" takes values divisible by `π̄` on `L`
(`RowVanishesModPiN`). -/
lemma exists_saturatedLattice_encard_rowVanishesModPiN_le (u : Gf E 𝔰.κ)
    {y : S.LatticeStabilizerCoset → stdLevel E 𝔰.κ}
    (hy : ∀ φ : S.LatticeStabilizerCoset, (y φ : S.LatticeStabilizerCoset) = φ) {r l : ℕ}
    (h_rank : r + l = 𝔰.k)
    {L : Submodule (Ô E) (𝔰.κ → 𝔸f E)} (hL : IsLatticeOfRank r L) (h_le : L ≤ unimodularLattice u) :
    ∃ V : Submodule E (𝔰.κ → E),
      finrank E V = r ∧
      L ≤ saturatedLattice u.val.val_inv V ∧
      submoduleIndex L (saturatedLattice u.val.val_inv V) ≠ 0 ∧
      discriminant r L = sublatticeDiscriminant u.val.val_inv V *
        submoduleIndex L (saturatedLattice u.val.val_inv V) ∧
      {φ : S.LatticeStabilizerCoset | S.RowVanishesModPiN u (y φ) L}.encard ≤ ENNReal.ofReal
        (submoduleIndex L (saturatedLattice u.val.val_inv V) * (S.N ^ numInfPlaces E) ^ l) := by
  -- `L` has a basis `m A`, with `m` a basis of the saturated lattice; the index is `[det A]`.
  obtain ⟨V, A, rfl, hA, rfl, h_disc⟩ :
      ∃ (V : Submodule E (𝔰.κ → E)) (A : GL (Fin (finrank E V)) (𝔸f E)),
        finrank E V = r ∧ IsIntMatrix (Ô E) A.1 ∧
        colLattice (Ô E) ((sublatticeBasis u.1.val_inv V).1 * A.1) = L ∧
        discriminant r L = sublatticeDiscriminant u.1.val_inv V * genIndex A.1.det :=
    hL.exists_eq_colLattice_sublatticeBasis_mul u.1.val_inv h_le
  let m : Matrix 𝔰.κ (Fin (finrank E V)) (𝔸f E) := (sublatticeBasis u.1.val_inv V).1
  have hm : IsPrimitiveMatrix (Ô E) (u.1.inv * m) :=
    isPrimitiveMatrix_mul_sublatticeBasis u.1.val_inv V
  have h_inv : HasLeftInv m := by
    obtain ⟨p, -, hp⟩ := hm.right
    exact ⟨p * u.1.inv, by rw [Matrix.mul_assoc, hp]⟩
  have h_index : submoduleIndex (colLattice (Ô E) (m * A.1)) (saturatedLattice u.1.val_inv V) =
      genIndex A.1.det := submoduleIndex_colLattice_mul h_inv hA
  refine ⟨V, rfl, colLattice_mul_le m hA, ?_, by rw [h_index, h_disc], ?_⟩
  · exact Nat.cast_ne_zero.1 (h_index.trans_ne (genIndex_pos A.det).ne')
  · rw [h_index]
    exact encard_rowVanishesModPiN_le u hy h_rank hA

/-- Let `d, i ≥ 1` be real numbers with `d i ≤ H`, and let `r ≤ k`. Then `i (d i) ^ (-k)` is at most
`H ^ (μ + 2) d ^ (-k-1) i ^ (-r-μ)` for every `μ`. -/
lemma mul_inv_pow_le_of_mul_le {d i H : ℝ} (hd : 1 ≤ d) (hi : 1 ≤ i) (hH : d * i ≤ H) {r k : ℕ}
    (hr : r ≤ k) (μ : ℕ) :
    i * ((d * i) ^ k)⁻¹ ≤ H ^ (μ + 2) * ((d ^ (k + 1))⁻¹ * i⁻¹ ^ (r + μ)) := by
  have hi_le : i ≤ H := (le_mul_of_one_le_left (by positivity) hd).trans hH
  have hH_pos : 0 < H := by linarith
  calc i * ((d * i) ^ k)⁻¹
    _ = i * (d * i) ^ (μ + 1) * (d ^ (k + μ + 1) * i ^ (k + μ + 1))⁻¹ := by
      field_simp
      ring
    _ ≤ H * H ^ (μ + 1) * (d ^ (k + 1) * i ^ (r + μ))⁻¹ := by
      have hd_pow : d ^ (k + 1) ≤ d ^ (k + μ + 1) := pow_le_pow_right₀ hd (by lia)
      have hi_pow : i ^ (r + μ) ≤ i ^ (k + μ + 1) := pow_le_pow_right₀ hi (by lia)
      gcongr
    _ = H ^ (μ + 2) * ((d ^ (k + 1))⁻¹ * i⁻¹ ^ (r + μ)) := by ring

/-- For a finite adelic unitary `u` and a subspace `V` of `E ^ κ`, the lattice of the adelic points
of `V` in `u Ô ^ κ` has discriminant at least `1`. -/
lemma one_le_sublatticeDiscriminant_unimodular (u : Gf E 𝔰.κ) (V : Submodule E (𝔰.κ → E)) :
    1 ≤ sublatticeDiscriminant u.val.val_inv V := by
  refine one_le_sublatticeDiscriminant u.1.val_inv V fun m hm ↦ ?_
  -- As `u⁻¹` is unitary, the Gram matrix of `m` is that of the integral matrix `u⁻¹ m`.
  have h_unitary : (u.1.inv)ᴴ * u.1.inv = 1 := by simpa using mem_U.1 u⁻¹.2
  have h_gram : (u.1.inv * m)ᴴ * (u.1.inv * m) = mᴴ * m := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ u.1.inv, h_unitary,
      Matrix.one_mul]
  rw [← h_gram]
  exact hm.conjTranspose.mul hm

/-- The weight of the subspace `V` of `E ^ κ`: it is `d ^ (-k-1)` if `V` has codimension `l`, with
`d` the discriminant of the lattice of the adelic points of `V` in `u Ô ^ κ`, and `0` otherwise. -/
abbrev subspaceDiscWeight (u : Gf E 𝔰.κ) (l : ℕ) (V : Submodule E (𝔰.κ → E)) : ℝ≥0∞ :=
  if finrank E V + l = 𝔰.k then ENNReal.ofReal (sublatticeDiscriminant u.1.val_inv V ^ (𝔰.k + 1))⁻¹
    else 0

omit [HasPrimitiveRoot5040 E] in
/-- Let `u` be in `Gf E 𝔰.κ`, let `y` assign an element `y φ` of `stdLevel E 𝔰.κ` to each coset `φ`
in `S.LatticeStabilizerCoset`, and let `L` be an `Ô`-submodule of `𝔸f E ^ 𝔰.κ`. The sum over these
cosets `φ` of the weights `S.discWeightIfRowVanishes u (y φ) r L` equals the number of cosets `φ`
for which the form of `y φ` vanishes on `L` modulo `piN`, times `(discriminant r L ^ 𝔰.k)⁻¹`. -/
lemma sum_discWeightIfRowVanishes_eq_encard_mul [Fintype S.LatticeStabilizerCoset] (u : Gf E 𝔰.κ)
    (y : S.LatticeStabilizerCoset → stdLevel E 𝔰.κ) (r : ℕ) (L : Submodule (Ô E) (𝔰.κ → 𝔸f E)) :
    ∑ φ : S.LatticeStabilizerCoset, S.discWeightIfRowVanishes u (y φ) r L =
      {φ : S.LatticeStabilizerCoset | S.RowVanishesModPiN u (y φ) L}.encard *
        ENNReal.ofReal (discriminant r L ^ 𝔰.k)⁻¹ := by
  rw [← tsum_set_const,
    _root_.tsum_subtype _ fun _ : S.LatticeStabilizerCoset ↦
      ENNReal.ofReal (discriminant r L ^ 𝔰.k)⁻¹,
    tsum_fintype]
  refine Finset.sum_congr rfl fun φ _ ↦ ?_
  by_cases h_kills : S.RowVanishesModPiN u (y φ) L <;> simp [discWeightIfRowVanishes, h_kills]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let `S` be filling data over `E` with shape `𝔰`, and let `u` be in `Gf E 𝔰.κ`. The set
`S.LatticeStabilizerCoset` is the quotient of `stdLevel`, the group of integral unitary matrices on
`κ`, by its subgroup of matrices whose row `k₀` is congruent to that of `1` modulo `S.piN`. Let
`y φ` be an element of each such coset `φ`, and call row `k₀` of `(y φ)⁻¹ u⁻¹` the form of `φ`. Let
`k = #κ`, let `r + l = k`, and let `L` be a lattice of rank `r` in `u Ô ^ κ` with discriminant at
most `H`. Then `L` has a finite index `i` in the lattice of the adelic points in `u Ô ^ κ` of some
subspace `V`. Moreover, the sum of `(disc L) ^ (-k)` over the `φ` whose form vanishes on `L` modulo
`S.piN` is at most `(N ^ f) ^ l H ^ (μ + 2) * subspaceDiscWeight u l V * i ^ (-dim V - μ)`, for any
natural number `μ`. Here `subspaceDiscWeight u l V` is `d ^ (-k-1)` if `V` has codimension `l`, with
`d` the discriminant of that lattice of `V`, and `0` otherwise. `N` is the prime of `S`, `H` is
`discriminantBound` and `f` is the number of infinite places. -/
lemma exists_sum_discWeightIfRowVanishes_le [Fintype S.LatticeStabilizerCoset] (u : Gf E 𝔰.κ)
    {y : S.LatticeStabilizerCoset → stdLevel E 𝔰.κ}
    (hy : ∀ φ : S.LatticeStabilizerCoset, (y φ : S.LatticeStabilizerCoset) = φ)
    {r l : ℕ} (h_rank : r + l = 𝔰.k) (μ : ℕ) (L : S.BoundedDiscSublattice r (unimodularLattice u)) :
    ∃ V : Submodule E (𝔰.κ → E),
      (L.val ≤ saturatedLattice u.val.val_inv V ∧
        submoduleIndex L.val (saturatedLattice u.val.val_inv V) ≠ 0) ∧
      ∑ φ : S.LatticeStabilizerCoset, S.discWeightIfRowVanishes u (y φ) r L.val ≤
        ENNReal.ofReal ((S.N ^ numInfPlaces E) ^ l * S.discriminantBound ^ (μ + 2)) *
          (subspaceDiscWeight u l V *
            (submoduleIndex L.val (saturatedLattice u.val.val_inv V) : ℝ≥0∞)⁻¹ ^
              (finrank E V + μ)) := by
  obtain ⟨L, hL, h_le, h_small⟩ := L
  -- At most `i (N ^ f) ^ l` forms vanish on `L`, and each of them contributes `(d i) ^ (-k)`.
  obtain ⟨V, rfl, h_sat, h_index, h_disc, h_forms⟩ :=
    exists_saturatedLattice_encard_rowVanishesModPiN_le u hy h_rank hL h_le
  refine ⟨V, ⟨h_sat, h_index⟩, ?_⟩
  set d : ℝ := sublatticeDiscriminant u.1.val_inv V
  set i : ℕ := submoduleIndex L (saturatedLattice u.1.val_inv V)
  have hd : 1 ≤ d := one_le_sublatticeDiscriminant_unimodular u V
  have hi : (1 : ℝ) ≤ i := Nat.one_le_cast.2 h_index.pos
  have hi_pos : (0 : ℝ) < i := one_pos.trans_le hi
  have h_di : d * i ≤ S.discriminantBound := h_disc.ge.trans h_small
  have h_exponents : i * ((d * i) ^ 𝔰.k)⁻¹ ≤
      S.discriminantBound ^ (μ + 2) * ((d ^ (𝔰.k + 1))⁻¹ * (i : ℝ)⁻¹ ^ (finrank E V + μ)) :=
    mul_inv_pow_le_of_mul_le hd hi h_di (Nat.le.intro h_rank) μ
  have discriminantBound_nonneg : 0 ≤ S.discriminantBound :=
    (hL.discriminant_pos.trans_le h_small).le
  calc ∑ φ : S.LatticeStabilizerCoset, S.discWeightIfRowVanishes u (y φ) (finrank E V) L
    _ = {φ : S.LatticeStabilizerCoset | S.RowVanishesModPiN u (y φ) L}.encard *
          ENNReal.ofReal ((d * i) ^ 𝔰.k)⁻¹ := by
      rw [sum_discWeightIfRowVanishes_eq_encard_mul, h_disc]
    _ ≤ ENNReal.ofReal (i * (S.N ^ numInfPlaces E) ^ l) * ENNReal.ofReal ((d * i) ^ 𝔰.k)⁻¹ := by
      gcongr
    _ = ENNReal.ofReal ((S.N ^ numInfPlaces E) ^ l * (i * ((d * i) ^ 𝔰.k)⁻¹)) := by
      rw [← ENNReal.ofReal_mul (by positivity), mul_comm (i : ℝ), mul_assoc]
    _ ≤ ENNReal.ofReal ((S.N ^ numInfPlaces E) ^ l * S.discriminantBound ^ (μ + 2) *
          ((d ^ (𝔰.k + 1))⁻¹ * (i : ℝ)⁻¹ ^ (finrank E V + μ))) := by
      grw [h_exponents, mul_assoc]
    _ = ENNReal.ofReal ((S.N ^ numInfPlaces E) ^ l * S.discriminantBound ^ (μ + 2)) *
          (ENNReal.ofReal (d ^ (𝔰.k + 1))⁻¹ * ENNReal.ofReal (i : ℝ)⁻¹ ^ (finrank E V + μ)) := by
      rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (inv_pos.2 hi_pos).le,
        ← ENNReal.ofReal_mul (p := (d ^ (𝔰.k + 1))⁻¹) (by positivity)]
    _ = ENNReal.ofReal ((S.N ^ numInfPlaces E) ^ l * S.discriminantBound ^ (μ + 2)) *
          (subspaceDiscWeight u l V * (i : ℝ≥0∞)⁻¹ ^ (finrank E V + μ)) := by
      rw [subspaceDiscWeight, ite_eq_left h_rank, ENNReal.ofReal_inv_of_pos hi_pos,
        ENNReal.ofReal_natCast]

/-- Let `u` be in the finite adelic unitary group `Gf E 𝔰.κ`, let `V` be a subspace of `E ^ 𝔰.κ`,
and let `Λ = saturatedLattice u.1.val_inv V` be the lattice of adelic points of `V` in `u Ô ^ 𝔰.κ`.
Here `𝔰.k = #𝔰.κ` is the size of the index set of the shape `𝔰`, and `𝔰.ϱ` is its number of
hyperbolic planes. The sum of `[Λ : M] ^ (-dim V - 2 𝔰.ϱ - 4)` over the sublattices `M` of finite
index in `Λ` is at most `2 ^ 𝔰.k`. The filling data `S : Filling E 𝔰` are used only for a bound on
the degree of `E` in terms of `𝔰.ϱ`. -/
lemma tsum_index_saturatedLattice_le (S : Filling E 𝔰) (u : Gf E 𝔰.κ) (V : Submodule E (𝔰.κ → E)) :
    ∑' M : {M : Submodule (Ô E) (𝔰.κ → 𝔸f E) // M ≤ saturatedLattice u.val.val_inv V ∧
        submoduleIndex M (saturatedLattice u.val.val_inv V) ≠ 0},
      (submoduleIndex M.val (saturatedLattice u.val.val_inv V) : ℝ≥0∞)⁻¹ ^
        (finrank E V + (2 * 𝔰.ϱ + 4)) ≤ 2 ^ 𝔰.k := by
  -- The sum is bounded by a power of the ideal zeta sum at `2 ϱ + 4`, which is at most `2`.
  have h_zeta_pow : idealZeta (Ô E) (2 * 𝔰.ϱ + 4) ^ (𝔰.ϱ + 1) ≤ ENNReal.ofReal (1 + 2⁻¹ ^ 0) := by
    simpa only [zero_add] using idealZeta_intAdeles_pow_le 0 S.mul_finrank_le_pow
  have h_zeta : idealZeta (Ô E) (2 * 𝔰.ϱ + 4) ≤ 2 := le_two_of_pow_le_ofReal h_zeta_pow
  have h_rank : finrank E V ≤ 𝔰.k := V.finrank_le.trans_eq (finrank_fintype_fun_eq_card E)
  calc _ ≤ idealZeta (Ô E) (2 * 𝔰.ϱ + 4) ^ finrank E V :=
      (isLatticeOfRank_saturatedLattice u.1.val_inv V).tsum_submoduleIndex_inv_pow_le _
    _ ≤ 2 ^ finrank E V := by gcongr
    _ ≤ 2 ^ 𝔰.k := pow_le_pow_right₀ one_le_two h_rank

/-! ### The sum over the forms and the lattices in a unimodular lattice -/

/-- Let `S` be filling data over the CM field `E` with shape `𝔰`, and let `u` be in the finite
adelic unitary group `Gf E 𝔰.κ`. The set `S.LatticeStabilizerCoset` is the quotient of `stdLevel`,
the group of integral unitary matrices on `κ`, by its subgroup of matrices whose row `k₀` is
congruent to that of `1` modulo `S.piN`. Let `y φ` be an element of each such coset `φ`, and call
row `k₀` of `(y φ)⁻¹ u⁻¹` the form of `φ`. Let `r + l = k = #κ`. Take the sum of `(disc L) ^ (-k)`
over the pairs of a coset `φ` and a lattice `L` of rank `r` in `u Ô ^ κ` with discriminant at most
`H` on which the form of `φ` vanishes modulo `S.piN`. This sum is at most `(N ^ f) ^ l H ^ (2 ϱ + 6)
(200 f k rd) ^ (f (k + 1) l) 2 ^ k`. Here `N` is the prime of `S`, `H` is `discriminantBound`, `ϱ`
is the number of hyperbolic planes of `𝔰`, `f` is the number of infinite places and `rd` is the root
discriminant of `E`. -/
lemma sum_tsum_discWeightIfRowVanishes_le [Fintype S.LatticeStabilizerCoset] (u : Gf E 𝔰.κ)
    {y : S.LatticeStabilizerCoset → stdLevel E 𝔰.κ}
    (hy : ∀ φ : S.LatticeStabilizerCoset, (y φ : S.LatticeStabilizerCoset) = φ)
    {r l : ℕ} (h_rank : r + l = 𝔰.k) :
    ∑ φ : S.LatticeStabilizerCoset, ∑' L : S.BoundedDiscSublattice r (unimodularLattice u),
        S.discWeightIfRowVanishes u (y φ) r L.val ≤
      ENNReal.ofReal ((S.N ^ numInfPlaces E) ^ l * S.discriminantBound ^ (2 * 𝔰.ϱ + 4 + 2)) *
        (ENNReal.ofReal ((200 * (numInfPlaces E * 𝔰.k) * rootDiscr E) ^
          (numInfPlaces E * (𝔰.k + 1) * l)) * 2 ^ 𝔰.k) := by
  -- Each `L` is a sublattice of finite index in the saturated lattice of some subspace `V`. Sort
  -- the `L` by `V`, and sum first over the sublattices and then over the subspaces.
  set C : ℝ≥0∞ :=
    ENNReal.ofReal ((S.N ^ numInfPlaces E) ^ l * S.discriminantBound ^ (2 * 𝔰.ϱ + 4 + 2))
  let Sub (V : Submodule E (𝔰.κ → E)) : Type :=
    {M : Submodule (Ô E) (𝔰.κ → 𝔸f E) // M ≤ saturatedLattice u.1.val_inv V ∧
      submoduleIndex M (saturatedLattice u.1.val_inv V) ≠ 0}
  let w (V : Submodule E (𝔰.κ → E)) (M : Sub V) : ℝ≥0∞ :=
    (submoduleIndex M.1 (saturatedLattice u.1.val_inv V) : ℝ≥0∞)⁻¹ ^ (finrank E V + (2 * 𝔰.ϱ + 4))
  have h_span (L : S.BoundedDiscSublattice r (unimodularLattice u)) :
      ∃ (V : Submodule E (𝔰.κ → E)) (M : Sub V), M.1 = L.1 ∧
        ∑ φ : S.LatticeStabilizerCoset, S.discWeightIfRowVanishes u (y φ) r L.1 ≤ C *
          (subspaceDiscWeight u l V * w V M) := by
    obtain ⟨V, h_sub, h_term⟩ := exists_sum_discWeightIfRowVanishes_le u hy h_rank (2 * 𝔰.ϱ + 4) L
    exact ⟨V, ⟨L.1, h_sub⟩, rfl, h_term⟩
  choose span M hM h_term using h_span
  let sort (L : S.BoundedDiscSublattice r (unimodularLattice u)) : Σ V : Submodule E (𝔰.κ → E),
    Sub V :=
    ⟨span L, M L⟩
  have h_sort : Function.Injective sort := by
    intro L L' h
    have h_eq : (sort L).snd.val = (sort L').snd.val := by rw [h]
    exact Subtype.ext (by rwa [← hM L, ← hM L'])
  calc _ = ∑' L : S.BoundedDiscSublattice r (unimodularLattice u), ∑ φ : S.LatticeStabilizerCoset,
          S.discWeightIfRowVanishes u (y φ) r L.1 :=
      (Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable).symm
    _ ≤ ∑' L : S.BoundedDiscSublattice r (unimodularLattice u),
          C * (subspaceDiscWeight u l (span L) * w (span L) (M L)) := ENNReal.tsum_le_tsum h_term
    _ ≤ ∑' p : Σ V : Submodule E (𝔰.κ → E), Sub V, C * (subspaceDiscWeight u l p.1 * w p.1 p.2) :=
      tsum_comp_le_tsum_of_injective h_sort fun p ↦ C * (subspaceDiscWeight u l p.1 * w p.1 p.2)
    _ = C * ∑' V : Submodule E (𝔰.κ → E), subspaceDiscWeight u l V * ∑' M : Sub V, w V M := by
      simp only [ENNReal.tsum_sigma', ENNReal.tsum_mul_left]
    _ ≤ C * ((∑' V : Submodule E (𝔰.κ → E), subspaceDiscWeight u l V) * 2 ^ 𝔰.k) := by
      rw [← ENNReal.tsum_mul_right]
      gcongr with V
      exact S.tsum_index_saturatedLattice_le u V
    _ ≤ _ := by
      gcongr
      -- The weight vanishes off the subspaces of codimension `l`.
      have h_support : Function.support (subspaceDiscWeight u l) ⊆
          {V : Submodule E (𝔰.κ → E) | finrank E V + l = Fintype.card 𝔰.κ} :=
        fun V hV ↦ of_not_not fun h_codim ↦ hV (ite_eq_right h_codim)
      have h_weight (V : {V : Submodule E (𝔰.κ → E) // finrank E V + l = Fintype.card 𝔰.κ}) :
          subspaceDiscWeight u l V.val = ENNReal.ofReal
            (sublatticeDiscriminant u.1.val_inv V.val ^ (𝔰.k + 1))⁻¹ :=
        ite_eq_left V.property
      rw [← tsum_subtype_eq_of_support_subset h_support]
      exact (tsum_congr h_weight).trans_le (tsum_sublatticeDiscriminant_inv_le u l)

end Forms

/-! ### The constants and the sum over all classes -/

omit [HasPrimitiveRoot5040 E] in
/-- The number `S.tailScale = b ^ (k f / 4)` is nonnegative, as the size parameter `b` is. Here
`k = |κ|` and `f` is the number of infinite places of `E`. -/
lemma tailScale_nonneg (S : Filling E 𝔰) [S.IsAdmissible] : 0 ≤ S.tailScale := by
  have hb : 0 < S.b := by linarith [S.thousand_le_b]
  rw [tailScale]
  positivity

/-- For every natural number `ϱ`, with `n = ϱ + 1`, the number `1 + n ^ 3 (2 ϱ + 6) + 1` is at
most `10 ^ 5 n ^ 9`. This bounds an exponent of the size parameter in
`pow_mul_discriminantBound_pow_le`. -/
lemma add_mul_succ_pow_three_le (ϱ : ℕ) :
    1 + (ϱ + 1) ^ 3 * (2 * ϱ + 4 + 2) + 1 ≤ 10 ^ 5 * (ϱ + 1) ^ 9 := by
  have h_one : 1 ≤ (ϱ + 1) ^ 9 := Nat.one_le_pow _ _ ϱ.succ_pos
  have h_linear : 2 * ϱ + 4 + 2 ≤ 6 * (ϱ + 1) := by lia
  have h_cube : (ϱ + 1) ^ 3 ≤ (ϱ + 1) ^ 8 := by gcongr; lia
  calc 1 + (ϱ + 1) ^ 3 * (2 * ϱ + 4 + 2) + 1
    _ ≤ (ϱ + 1) ^ 9 + (ϱ + 1) ^ 8 * (6 * (ϱ + 1)) + (ϱ + 1) ^ 9 := by gcongr
    _ = 8 * (ϱ + 1) ^ 9 := by ring
    _ ≤ 10 ^ 5 * (ϱ + 1) ^ 9 := Nat.mul_le_mul_right _ (by norm_num)

section

omit [HasPrimitiveRoot5040 E]

/-- Let `S` be filling data that satisfy the standing hypotheses `IsAdmissible`. The product
`b ^ f H ^ (2 ϱ + 6) 2 ^ k` is at most `tailScale = b ^ (k f / 4)`. Here `b` is the size parameter
of `S`, `k = #κ`, `f` is the number of infinite places of `E`, and
`H = discriminantBound = b ^ (n ^ 3 f)` with `n = ϱ + 1`. -/
lemma pow_mul_discriminantBound_pow_le (S : Filling E 𝔰) [S.IsAdmissible] :
    S.b ^ numInfPlaces E * S.discriminantBound ^ (2 * 𝔰.ϱ + 4 + 2) * 2 ^ 𝔰.k ≤ S.tailScale := by
  have hb : 2 ≤ S.b := by linarith [S.thousand_le_b]
  have discriminantBound_nonneg : 0 ≤ S.discriminantBound := pow_nonneg (zero_le_two.trans hb) _
  have h_two : (2 : ℝ) ^ 𝔰.k ≤ S.b ^ numInfPlaces E :=
    (by gcongr : (2 : ℝ) ^ 𝔰.k ≤ S.b ^ 𝔰.k).trans (pow_le_pow_right₀ S.one_le_b S.k_le_f)
  have h_exponent : 1 + 𝔰.n ^ 3 * (2 * 𝔰.ϱ + 4 + 2) + 1 ≤ 10 ^ 5 * 𝔰.n ^ 9 :=
    add_mul_succ_pow_three_le 𝔰.ϱ
  calc S.b ^ numInfPlaces E * S.discriminantBound ^ (2 * 𝔰.ϱ + 4 + 2) * 2 ^ 𝔰.k
    _ ≤ S.b ^ numInfPlaces E * S.discriminantBound ^ (2 * 𝔰.ϱ + 4 + 2) * S.b ^ numInfPlaces E := by
      gcongr
    _ = S.b ^ ((1 + 𝔰.n ^ 3 * (2 * 𝔰.ϱ + 4 + 2) + 1) * numInfPlaces E) := by
      rw [discriminantBound]
      ring
    _ ≤ S.tailScale := pow_le_tailScale (Nat.mul_le_mul_right _ h_exponent)

/-- Let `S` be filling data that satisfy the standing hypotheses `IsAdmissible`, among them
`N ≤ b ^ (60 (ϱ + 1))`. The product `N ^ f (200 f k rd) ^ (f (k + 1))` is at most
`tailScale = b ^ (k f / 4)`. Here `N` is the prime and `b` the size parameter of `S`, `k = #κ`, `f`
is the number of infinite places and `rd` the root discriminant of `E`. -/
lemma pow_mul_mul_rootDiscr_pow_le_tailScale (S : Filling E 𝔰) [S.IsAdmissible] :
    S.N ^ numInfPlaces E *
      (200 * (numInfPlaces E * 𝔰.k) * rootDiscr E) ^ (numInfPlaces E * (𝔰.k + 1)) ≤
      S.tailScale := by
  -- Compare the thousandth powers, which are bounded by powers of `b`.
  have hb : 0 < S.b := by linarith [S.thousand_le_b]
  have h_rd : 0 < rootDiscr E := rootDiscr_pos E
  have h_exponent : 60 * 𝔰.n * 1000 + (𝔰.k + 1) ≤ 250 * 𝔰.k := by
    have hk : 1000 * (2 * 𝔰.ϱ + 2) ≤ 𝔰.k := S.thousand_mul_le_k
    have hn : 𝔰.n = 𝔰.ϱ + 1 := rfl
    lia
  refine le_of_pow_le_pow_left₀ (n := 1000) (by norm_num) S.tailScale_nonneg ?_
  set X : ℝ := 200 * (numInfPlaces E * 𝔰.k) * rootDiscr E
  have hX : 0 ≤ X := by positivity
  calc (S.N ^ numInfPlaces E * X ^ (numInfPlaces E * (𝔰.k + 1))) ^ 1000
    _ = (S.N ^ 1000 * (X ^ 1000) ^ (𝔰.k + 1)) ^ numInfPlaces E := by
      simp only [mul_pow, ← pow_mul]
      ring_nf
    _ ≤ ((S.b ^ (60 * 𝔰.n)) ^ 1000 * S.b ^ (𝔰.k + 1)) ^ numInfPlaces E := by
      gcongr
      exacts [IsAdmissible.N_le, S.mul_rootDiscr_pow_le]
    _ ≤ (S.b ^ (250 * 𝔰.k)) ^ numInfPlaces E := by
      rw [← pow_mul, ← pow_add]
      gcongr
      exact S.one_le_b
    _ = (S.b ^ (𝔰.k * numInfPlaces E)) ^ 250 := by ring
    _ = S.tailScale ^ 1000 := by rw [← tailScale_pow_four, ← pow_mul]

/-- Let `S` be filling data that satisfy the standing hypotheses `IsAdmissible`, among them
`N ≤ b ^ (60 (ϱ + 1))`. For every `l`, the constant `(N ^ f) ^ l H ^ (2 ϱ + 6) (200 f
k rd) ^ (f (k + 1) l) 2 ^ k` of `sum_tsum_discWeightIfRowVanishes_le` is at most
`tailScale ^ (l + 1) / b ^ f`. Here `N` is the prime and `b` the size parameter of `S`, `k = #κ`,
`f` is the number of infinite places and `rd` the root discriminant of `E`,
`H = discriminantBound = b ^ ((ϱ + 1) ^ 3 f)` and `tailScale = b ^ (k f / 4)`. -/
lemma mul_rootDiscr_pow_le_tailScale_pow_div (S : Filling E 𝔰) [S.IsAdmissible] (l : ℕ) :
    (S.N ^ numInfPlaces E) ^ l * S.discriminantBound ^ (2 * 𝔰.ϱ + 4 + 2) *
        ((200 * (numInfPlaces E * 𝔰.k) * rootDiscr E) ^ (numInfPlaces E * (𝔰.k + 1) * l) *
          2 ^ 𝔰.k) ≤
      S.tailScale ^ (l + 1) / S.b ^ numInfPlaces E := by
  have hb : 0 < S.b := by linarith [S.thousand_le_b]
  have h_rd : 0 < rootDiscr E := rootDiscr_pos E
  have discriminantBound_nonneg : 0 ≤ S.discriminantBound := pow_nonneg hb.le _
  have hτ : 0 ≤ S.tailScale := S.tailScale_nonneg
  rw [le_div_iff₀ (by positivity)]
  calc _ = S.b ^ numInfPlaces E * S.discriminantBound ^ (2 * 𝔰.ϱ + 4 + 2) * 2 ^ 𝔰.k *
        (S.N ^ numInfPlaces E *
          (200 * (numInfPlaces E * 𝔰.k) * rootDiscr E) ^ (numInfPlaces E * (𝔰.k + 1))) ^ l := by
        rw [pow_mul _ _ l]
        ring
    _ ≤ S.tailScale * S.tailScale ^ l := by
      gcongr
      · exact S.pow_mul_discriminantBound_pow_le
      · exact S.pow_mul_mul_rootDiscr_pow_le_tailScale
    _ = S.tailScale ^ (l + 1) := by ring

end

/-- **Lattices of given corank.** Let `S` be filling data, with prime `N = π π̄` and size parameter
`b`, that satisfy the standing hypotheses `IsAdmissible`; those used are the form of the level,
`N ≤ b ^ (60 (ϱ + 1))`, the lower bounds `1000 ≤ b` and `5 ≤ N`, and a lower bound for an index. Let
`k₀ = 𝔰.k₀` be the distinguished index in `κ` given by the shape `𝔰`, and let `r + l = k = #κ`. For
a class `c` in the double coset space `S.Classes` of `U(X₀)`, with chosen representative `g`, the
lattice `classLatticeX₀ c` consists of the adelic vectors `v` such that `g⁻¹ v` is integral with
entry `k₀` divisible by `π̄`. Take the sum of `(disc L) ^ (-k)` over all `c` and all lattices `L` of
rank `r` in that lattice with `disc L ≤ discriminantBound = b ^ ((ϱ + 1) ^ 3 f)`. This sum is at
most `tailScale ^ (l + 1)` times the number of classes divided by `N ^ (k f)`. -/
theorem sum_discriminant_inv_le {S : Filling E 𝔰} [S.IsAdmissible] {r l : ℕ}
    (h_rank : r + l = 𝔰.k) :
    ∑ c : S.Classes, ∑' L : {L : Submodule (Ô E) (𝔰.κ → 𝔸f E) // IsLatticeOfRank r L ∧
        L ≤ S.classLatticeX₀ c ∧ discriminant r L ≤ S.discriminantBound},
      ENNReal.ofReal (discriminant r L.val ^ 𝔰.k)⁻¹ ≤
      .ofReal (card S.Classes / S.N ^ (𝔰.k * numInfPlaces E) * S.tailScale ^ (l + 1)) := by
  -- The mean over the classes is a mean over `u` of the mean over the lattice stabilizer cosets
  -- `φ`, of which there are at least `(N ^ k / b) ^ f`.
  have hb : 0 < S.b := by linarith [S.thousand_le_b]
  have hN : (0 : ℝ) < S.N := by linarith [S.five_le_N]
  have hτ : 0 ≤ S.tailScale := S.tailScale_nonneg
  have discriminantBound_nonneg : 0 ≤ S.discriminantBound := pow_nonneg hb.le _
  have h_rd : 0 < rootDiscr E := rootDiscr_pos E
  have h_card : (S.N ^ 𝔰.k / S.b) ^ numInfPlaces E ≤ (Nat.card S.LatticeStabilizerCoset : ℝ) :=
    IsAdmissible.le_relIndex
  have h_card_pos : (0 : ℝ) < Nat.card S.LatticeStabilizerCoset := h_card.trans_lt' (by positivity)
  have : Fintype S.LatticeStabilizerCoset :=
    Subgroup.fintypeOfIndexNeZero (Nat.cast_pos.1 h_card_pos).ne'
  rw [mul_comm_div]
  refine sum_classes_le_of_sum_translates_le (fun φ : S.LatticeStabilizerCoset ↦ φ.out.1) _
    (by positivity) fun u ↦ ?_
  have h_rep : ∀ φ : S.LatticeStabilizerCoset, ∃ (η : U (stdSpace E 𝔰.κ).J) (y : stdLevel E 𝔰.κ),
      (y : S.LatticeStabilizerCoset) = φ ∧
        (⟦u * φ.out⟧ : S.Classes).out = (stdSpace E 𝔰.κ).embFin η * u * y :=
    exists_mk_out_eq_embFin_mul u
  choose η y hy h_out using h_rep
  calc ∑ φ : S.LatticeStabilizerCoset, ∑' L :
         S.BoundedDiscSublattice r (S.classLatticeX₀ ⟦u * φ.out⟧),
        ENNReal.ofReal (discriminant r L.1 ^ 𝔰.k)⁻¹
    _ ≤ ∑ φ : S.LatticeStabilizerCoset, ∑' L : S.BoundedDiscSublattice r (unimodularLattice u),
          S.discWeightIfRowVanishes u (y φ) r L.1 :=
      Finset.sum_le_sum fun φ _ ↦ tsum_discriminant_inv_le_of_out_eq (h_out φ) r
    _ ≤ ENNReal.ofReal ((S.N ^ numInfPlaces E) ^ l * S.discriminantBound ^ (2 * 𝔰.ϱ + 4 + 2) *
          ((200 * (numInfPlaces E * 𝔰.k) * rootDiscr E) ^ (numInfPlaces E * (𝔰.k + 1) * l) *
            2 ^ 𝔰.k)) := by
      refine (sum_tsum_discWeightIfRowVanishes_le u hy h_rank).trans_eq ?_
      simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow two_pos.le,
        ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (S.tailScale ^ (l + 1) / S.b ^ numInfPlaces E) :=
      ENNReal.ofReal_le_ofReal (S.mul_rootDiscr_pow_le_tailScale_pow_div l)
    _ = ENNReal.ofReal ((S.N ^ 𝔰.k / S.b) ^ numInfPlaces E *
          (S.tailScale ^ (l + 1) / S.N ^ (𝔰.k * numInfPlaces E))) := by
      congr 1
      rw [div_pow, ← pow_mul]
      field_simp
    _ ≤ ENNReal.ofReal
          (card S.LatticeStabilizerCoset *
            (S.tailScale ^ (l + 1) / S.N ^ (𝔰.k * numInfPlaces E))) := by
      grw [h_card, Nat.card_eq_fintype_card]

end CrudeLattices

end New.Filling

end
