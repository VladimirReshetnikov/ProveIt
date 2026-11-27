import New.Spanning.Bessel.LargeFunction
import New.Spanning.Unfolding.AmplitudeSums
import New.UpperBound.Objects.Rows

/-!
# Poincaré series of fitting spaces, unfolding, Petersson products and source form coordinates

This file builds Poincaré series from the Bessel functions of filling data S (`New.Filling`) on a
hermitian space V that fits S, and computes their Petersson products.

K = `New.Filling.latticeStabilizer` and K(M) = `New.Filling.principalLevel` are levels in the
lattice basis of S. Here K(M) is the kernel of reduction at the chosen places, and M in this
notation is the product of the two level primes, not an adelic point. For a graded space Y on V that
fits S, the groups attached to Y correspond to those of S under `New.Filling.Fits.adelicEquiv` and
`New.Filling.Fits.finiteEquiv`, and algebraic forms of level `S.sourceLevel` get coordinates indexed
by classes and indices.

## Main definitions and results

* `New.Filling.Fits`: V matches S; this gives the identifications `New.Filling.Fits.ratEquiv`
  (rational points), `New.Filling.Fits.realHomeomorph` (infinite places) and
  `New.Filling.Fits.finiteEquiv` (finite places).
* `New.Filling.Fits.cutBessel`, `New.Filling.Fits.poincareSeries`: a coordinate i of the Bessel
  function, cut off and supported on the coset of a class c, and the series ∑_a φ_a ∑_γ of these,
  a = (c, i).
* `New.Filling.Fits.petersson_poincare`: the Petersson products of translated series are the
  amplitude sums `New.Filling.amplitudeSum` times the volume of the level.
* `New.Filling.Fits.poincareMap`, `New.Filling.Fits.coe_poincareMap`: the series are forms of level
  `New.Filling.stdPrincipalLevel`, linear in φ.
* `New.Filling.Fits.sourceFormCoords`: algebraic forms of level `S.sourceLevel` as vectors of the
  Euclidean space on classes times indices.
* `New.Filling.Fits.finrank_levelSpace_eq_sourceDim`: the dimension of the space of these forms is
  the number of classes times the dimension of the weight, and it is positive.

Notions from other files:
* `New.Filling.besselFn`: W_i(y), the product over the infinite places v of the i_v-th coordinate of
  the local Bessel function W_v at y_v. Only the full (not the cut) function is used: `.full`.
* `New.Filling.classRep`, `New.Filling.classUnipotent`, `New.Filling.classCutoff`: for a class c,
  its representative h_c, the group 𝖴_c(M) of rational unipotent u with h_c⁻¹ u h_c ∈ K(M), and a
  cutoff β_c at the infinite places whose translates under 𝖴_c(M) sum to 1.
* `New.Filling.termsOver`: the rational γ such that h_c⁻¹ γ h_c' lies in K and has reduction s.
* `New.Shape.Form.besselU`: the Bessel unipotent group 𝖴: the isometries of
  `New.Shape.Form.splitGram` T that are block upper unitriangular for the levels
  `New.BesselIndex.level`, so trivial on the middle block.
* X₀ is the hermitian space on κ with the standard form, all signs +1; U(X₀) is its unitary group.

## Relation to the literature

The file also contains known results stated on this proof's data: Poincaré series along a Bessel
subgroup and their unfolding. See `Lib.DiscreteSeries.Bruhat.FloorGroups`.
-/

noncomputable section

section PoincareSeries

open MeasureTheory Matrix Complex Subgroup Finset PiLp

namespace New.Filling

variable {E : Type} {𝔰 : Shape} {ε : 𝔰.BesselIndex → ℤˣ}
  [Field E] [CMType E] [HasPrimitiveRoot5040 E] [p : DiscreteSeries.UnitarySignFrame 𝔰 ε]

/-- The hermitian space V, with grading Y, fits the filling data S: the Bessel system of S at each
infinite place v has type (l v, kw v), Y is standardly indexed, and `typeKernel l ε` is an
idempotent kernel. The finite part of the point of V is a finite idele times `toBesselH 𝔰 ↑S.N η`
times `S.latticeBasis` times an integral matrix that reduces to 1 at the chosen places. The element
η is central. -/
structure Fits (S : Filling E 𝔰) (V : Space E 𝔰.BesselIndex ε)
    (l : NumberField.InfinitePlace E → HCParam ε)
    (kw : NumberField.InfinitePlace E → ℕ → ℕ) (Y : Grading V S.N 𝔰.κ (2 * 𝔰.ϱ + 1))
    (η : Gf E 𝔰.κ) : Prop where
  /-- The Bessel system at each infinite place `v` has type `(l v, kw v)`. -/
  isDiscreteSeriesBessel (v : NumberField.InfinitePlace E) :
    IsDiscreteSeriesBessel (S.besselSystem v) (l v) (kw v)
  /-- The grading `Y` labels the basis of `V` in the standard way, by `besselIndexEquiv`. -/
  index_eq : Y.indexEquiv = 𝔰.besselIndexEquiv
  /-- The kernel `typeKernel l ε` is idempotent. -/
  isIdempotentKernel : IsIdempotentKernel (typeKernel l ε)
  /-- The finite part of the point of `V` is a finite idele times `toBesselH _ ↑S.N η` times
  `S.latticeBasis` times an integral matrix that reduces to 1 at the chosen places. -/
  exists_point_eq : ∃ k : intGL 𝔰.BesselIndex (Ô E),
    (∀ (i : Fin 2) (w : S.chosenPlaces i), intGL.map (reduceAt w) k = 1) ∧
    ∃ u : (𝔸f E)ˣ, V.xFin = u • (toBesselH 𝔰 ↑S.N η).1 * S.latticeBasis * k.1
  /-- The element η commutes with every element of the finite adelic unitary group on κ. -/
  central (a : Gf E 𝔰.κ) : Commute η a

/-- The principal level at the chosen places of S (integral matrices that reduce to 1 there), as an
open subgroup of the finite adelic unitary group in orthonormal local bases. -/
def stdPrincipalLevel (S : Filling E 𝔰) : OpenSubgroup (Gf E 𝔰.BesselIndex) :=
  ⟨levelOf (fun w : Σ i : Fin 2, S.chosenPlaces i ↦ (w.2 : FinPlace E)) ⊥, isOpen_levelOf⟩

namespace Fits

section Series

variable {S : Filling E 𝔰} {V : Space E 𝔰.BesselIndex ε}
  {l : NumberField.InfinitePlace E → HCParam ε} {kw : NumberField.InfinitePlace E → ℕ → ℕ}
  {Y : Grading V S.N 𝔰.κ (2 * 𝔰.ϱ + 1)} {η : Gf E 𝔰.κ}

variable (X : S.Fits V l kw Y η) (a : S.Classes × S.BesselCoord)
  (φ : EuclideanSpace ℂ (S.Classes × S.BesselCoord)) (g : New.G E ε)

/-! ### Identifying the groups of `V` and of `S` -/

section

omit [HasPrimitiveRoot5040 E]

/-- If V fits S, the Gram matrix of V is the rational Gram matrix of S. -/
theorem J_eq_ratGram (X : S.Fits V l kw Y η) : V.J = S.ratGram := by
  -- Compare the two block matrices entry by entry; what is left is arithmetic of the indices.
  simp [Y.gram_eq, X.index_eq, ← ext_iff, gradedGram, Shape.besselIndexEquiv, splitGram, middleGram,
    Fin.rev, Matrix.one_apply, Nat.Prime.ne_zero]
  lia

/-- The isomorphism from the rational points of the unitary group of S onto the discrete
subgroup Γ of V, given by `New.Space.ratEmbed`. -/
def ratEquiv : S.G E ≃* V.Γ :=
  MulEquiv.trans (MulEquiv.subgroupCongr (congrArg U X.J_eq_ratGram.symm))
    (V.ratEmbed.ofInjective V.ratEmbed_injective)

/-- The isomorphism, given by the point of V, from the standard adelic group of signs ε onto the
adelic points of the unitary group of S. -/
def adelicEquiv : New.G E ε ≃* S.G (𝔸 E) :=
  V.toRatCoords.trans (MulEquiv.subgroupCongr (by simp [X.J_eq_ratGram, map_splitGram_ratMiddle]))

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- For γ a rational point of the unitary group of S, `X.adelicEquiv` applied to the image
`X.ratEquiv γ` of γ in Γ equals `S.ratToAdelic γ`, the diagonal embedding of γ into the adelic
group. -/
theorem adelicEquiv_ratEquiv (γ : S.G E) : X.adelicEquiv (X.ratEquiv γ) = S.ratToAdelic γ := by
  -- The conjugations by the point of `V` in `X.adelicEquiv` and in `X.ratEquiv` cancel.
  erw [V.toRatCoords.trans_apply, V.toRatCoords.apply_symm_apply]
  rfl

/-- Let the hermitian space V fit the filling data S, and let x_v be the component of the point
`V.x` at an infinite place v. Then x_vᴴ J x_v is the diagonal matrix of the signs ε, where J is the
Gram matrix of S over ℂ: ϱ hyperbolic pairs around the middle block `S.ratMiddle ℂ`. -/
theorem gram_map_evalInf_point (X : S.Fits V l kw Y η) (v : NumberField.InfinitePlace E) :
    (GeneralLinearGroup.map (evalInf v) V.x).valᴴ * (S.ratMiddle ℂ).splitGram *
      (GeneralLinearGroup.map (evalInf v) V.x).val = signMatrix ε := by
  have h_map : (V.x.valᴴ * V.J.map toAdele * V.x.val).map (evalInf v) =
      (stdForm E ε).map (evalInf v) := by rw [V.gram_point]
  have h_star : V.x.valᴴ.map (evalInf v) = (V.x.val.map (evalInf v))ᴴ :=
    conjTranspose_map _ (by simp [Function.Semiconj])
  simpa [X.J_eq_ratGram, stdForm, signMatrix, mul_assoc, map_splitGram_ratMiddle, h_star]
    using h_map

/-- The homeomorphism from G_∞ onto ∏_v G₁, g_v ↦ d_v⁻¹x_v g_v p⁻¹, with x the point of V,
d_v = `New.Filling.basisScaleGL` and p the chosen unitary sign frame. -/
def realHomeomorph : (NumberField.InfinitePlace E → USign ε) ≃ₜ
    (NumberField.InfinitePlace E → U (𝔰.middleGram (1 : ℂ)).splitGram) :=
  -- At each place `v`, pass to `𝔰.G₁` by the frame `p`, then multiply on the left by
  -- `(S.basisScaleGL v)⁻¹ * V.x * p⁻¹`. Its three factors carry the form of `𝔰.G₁` in turn to that
  -- of `S`, to the diagonal form of signs `ε`, and back.
  Homeomorph.piCongrRight fun v ↦ DiscreteSeries.frameEquiv.symm.toHomeomorph.trans <|
    Homeomorph.mulLeft ⟨(S.basisScaleGL v)⁻¹ * GeneralLinearGroup.map (evalInf v) V.x * p.matrix⁻¹,
      gram_mul_of_gram_eq
        (gram_mul_of_gram_eq (gram_inv_of_gram_eq
          (S.conjTranspose_basisScaleGL_mul_splitGram_mul v))
          (X.gram_map_evalInf_point v))
        (gram_inv_of_gram_eq p.gram_eq)⟩

/-- The homeomorphism `X.realHomeomorph` turns left translation by g into left translation by the
infinite part of `X.adelicEquiv g`. -/
theorem realHomeomorph_mul (g' : New.G E ε) :
    X.realHomeomorph (g * g').1 = S.adelicToInf (X.adelicEquiv g) * X.realHomeomorph g'.1 := by
  -- At each place both sides are products of the same change-of-basis matrices.
  ext v : 2
  have h_comp : (g.1 v).val = GeneralLinearGroup.map (evalInf v) (G.toUnitary g).val := rfl
  -- `X.adelicEquiv` is conjugation by the point of `V`, and `X.realHomeomorph` multiplies by `x`.
  let x : GL 𝔰.BesselIndex ℂ := (S.basisScaleGL v)⁻¹ * GeneralLinearGroup.map (evalInf v) V.x
  change x * p.matrix⁻¹ * (p.matrix * (g * g').1 v * p.matrix⁻¹) =
    S.adelicToInf (X.adelicEquiv g) v * (x * p.matrix⁻¹ * (p.matrix * g'.1 v * p.matrix⁻¹))
  simp [x, adelicToInf, adelicEquiv, U.map, U.conj, Space.toRatCoords, mul_assoc, h_comp]

/-- The isomorphism from the standard finite adelic unitary group onto that of S in the lattice
basis: conjugate by the finite point of V, change to the lattice basis, then conjugate by the
inverse of the image `New.Filling.inclHFin` of η, that is x ↦ ι(η)⁻¹ x ι(η). -/
def finiteEquiv : Gf E 𝔰.BesselIndex ≃* S.GFin :=
  (U.conj V.xFin (by simpa [X.J_eq_ratGram, mul_assoc, map_splitGram_ratMiddle] using
    V.gram_xFin)).trans (S.toLatticeBasis.trans (MulAut.conj (S.inclHFin η)⁻¹))

/-- On finite parts, `X.finiteEquiv` is the finite part of `X.adelicEquiv` in the lattice basis,
conjugated by the inverse of `S.inclHFin η`. -/
theorem finiteEquiv_eq_conj_adelicToFin :
    X.finiteEquiv g.2 = (S.inclHFin η)⁻¹ * S.adelicToFin (X.adelicEquiv g) * S.inclHFin η := by
  simp only [finiteEquiv, adelicToFin, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv,
    MonoidHom.comp_apply, MonoidHom.coe_ofClass]
  congr 3
  ext : 2
  -- It remains to compare the matrices of the finite part in rational coordinates.
  show V.ratCoordMatrixFin g.2 = (V.ratCoordMatrix g).map Prod.snd
  exact V.ratCoordMatrixFin_snd g

/-- The isomorphism `New.Filling.Fits.finiteEquiv` is conjugation by an integral matrix x that
reduces to 1 at the chosen places. -/
theorem exists_coe_finiteEquiv_eq_conj :
    ∃ x : intGL 𝔰.BesselIndex (Ô E),
      (∀ (i : Fin 2) (w : S.chosenPlaces i), intGL.map (reduceAt w) x = 1) ∧
      ∀ k : Gf E 𝔰.BesselIndex, (X.finiteEquiv k).val = x * k * x⁻¹ := by
  obtain ⟨x, hx_red, u, hu⟩ := X.exists_point_eq
  refine ⟨x, hx_red, fun k ↦ ?_⟩
  simp [finiteEquiv, inclHFin, Filling.toLatticeBasis, U.conj, hu, Units.ext_iff, mul_assoc]

/-- The image of k under `New.Filling.Fits.finiteEquiv` preserves the lattice of S if and only if k
is integral in the orthonormal local bases of V. -/
theorem finiteEquiv_mem_latticeStabilizer_iff {k : Gf E 𝔰.BesselIndex} :
    X.finiteEquiv k ∈ S.latticeStabilizer ↔ k ∈ stdLevel E 𝔰.BesselIndex := by
  obtain ⟨x, -, h_conj⟩ := X.exists_coe_finiteEquiv_eq_conj
  change (X.finiteEquiv k).val ∈ intGL 𝔰.BesselIndex (Ô E) ↔ k.val ∈ intGL 𝔰.BesselIndex (Ô E)
  simp [h_conj, mul_mem_cancel_left, mul_mem_cancel_right]

/-- The image of k under `New.Filling.Fits.finiteEquiv` lies in the lattice stabilizer
`New.Filling.latticeStabilizer` with reduction s if and only if k lies in the integral subgroup
`New.stdLevel` with reduction s at the chosen places. Here s is a family of matrices over the
residue fields of these places. -/
theorem reduction_finiteEquiv_iff (k : Gf E 𝔰.BesselIndex) (s : S.ResidueGL) :
    (∃ h : X.finiteEquiv k ∈ S.latticeStabilizer, S.reduction ⟨X.finiteEquiv k, h⟩ = s) ↔
      ∃ h : k ∈ stdLevel E 𝔰.BesselIndex,
        stdLevel.reduceFamily (fun w : Σ i : Fin 2, S.chosenPlaces i ↦ (w.2 : FinPlace E)) ⟨k, h⟩ =
          Sigma.uncurry s := by
  obtain ⟨x, hx_red, h_conj⟩ := X.exists_coe_finiteEquiv_eq_conj
  -- Conjugation by `x` does not change the reduction at a chosen place.
  have h_red (h : X.finiteEquiv k ∈ S.latticeStabilizer) (h' : k ∈ stdLevel E 𝔰.BesselIndex)
      (i : Fin 2) (w : S.chosenPlaces i) :
      S.reduction ⟨X.finiteEquiv k, h⟩ i w =
        stdLevel.reduceFamily (fun w : Σ i, S.chosenPlaces i ↦ (w.2 : FinPlace E)) ⟨k, h'⟩
          ⟨i, w⟩ := by
    have h_int : (⟨X.finiteEquiv k, h⟩ : intGL 𝔰.BesselIndex (Ô E)) = x * ⟨k, h'⟩ * x⁻¹ :=
      Subtype.ext (h_conj k)
    -- Both reductions unfold to `intGL.map (reduceAt w)`, which sends `x` to 1.
    simpa [hx_red, mul_assoc] using! congrArg (intGL.map (reduceAt w)) h_int
  refine ⟨fun ⟨h, hs⟩ ↦ ⟨X.finiteEquiv_mem_latticeStabilizer_iff.1 h, ?_⟩,
    fun ⟨h, hs⟩ ↦ ⟨X.finiteEquiv_mem_latticeStabilizer_iff.2 h, ?_⟩⟩
  · exact funext fun ⟨i, w⟩ ↦ (h_red h _ i w).symm.trans (congrFun₂ hs i w)
  · exact funext₂ fun i w ↦ (h_red _ h i w).trans (congrFun hs ⟨i, w⟩)

/-- An element k lies in the principal level `S.stdPrincipalLevel`, taken in orthonormal local
bases, if and only if its image under `New.Filling.Fits.finiteEquiv` lies in the principal level
`S.principalLevel`, taken in the lattice basis of S. -/
theorem mem_stdPrincipalLevel_iff {k : Gf E 𝔰.BesselIndex} :
    k ∈ S.stdPrincipalLevel ↔ X.finiteEquiv k ∈ S.principalLevel :=
  mem_levelOf.trans (by simp [principalLevel, reduction_finiteEquiv_iff])

/-! ### The Poincaré series -/

open scoped Classical in
/-- For a = (c, i), the function of adelic g equal to β_c(y) W_i(y), y the image of g_∞ under
`New.Filling.Fits.realHomeomorph`, if ψ⁻¹(h_c⁻¹ ι(η)) g_f lies in `New.Filling.stdPrincipalLevel`,
and 0 otherwise; here ψ = `New.Filling.Fits.finiteEquiv`, ι = `New.Filling.inclHFin`, and β_c is the
cutoff of c. -/
def cutBessel (a : S.Classes × S.BesselCoord) (g : New.G E ε) : ℂ :=
  if X.finiteEquiv.symm ((S.classRep a.1)⁻¹ * S.inclHFin η) * g.2 ∈ S.stdPrincipalLevel then
    (S.classCutoff a.1 (X.realHomeomorph g.1)).toReal • S.besselFn .full (X.realHomeomorph g.1) a.2
  else 0

open scoped Classical in
/-- For a = (c, i) and a rational point γ of the unitary group of S, `New.Filling.Fits.cutBessel` a
evaluated at (image of γ under `New.Filling.Fits.ratEquiv`)·g equals β_c(y) W_i(y) if h_c⁻¹ γ_f ι(η)
ψ(g_f) lies in `New.Filling.principalLevel`, and 0 otherwise. Here y is γ_∞ times the image of g_∞
under `New.Filling.Fits.realHomeomorph`. Also ψ = `New.Filling.Fits.finiteEquiv`,
ι = `New.Filling.inclHFin`, h_c = `New.Filling.classRep` of c and β_c is the cutoff of c. The
element η is the central finite adelic point of U(X₀) in the fit `X : S.Fits V l kw Y η`. -/
theorem cutBessel_ratEquiv_mul (γ : S.G E) :
    X.cutBessel a (X.ratEquiv γ * g) =
      let y : NumberField.InfinitePlace E → 𝔰.G₁ := S.ratToInf γ * X.realHomeomorph g.1
      if (S.classRep a.1)⁻¹ * (S.ratToFin γ * (S.inclHFin η * X.finiteEquiv g.2)) ∈
          S.principalLevel then
        (S.classCutoff a.1 y).toReal • S.besselFn .full y a.2
      else 0 := by
  have h_inf : X.realHomeomorph (X.ratEquiv γ * g).1 = S.ratToInf γ * X.realHomeomorph g.1 := by
    rw [realHomeomorph_mul, adelicEquiv_ratEquiv, ratToInf, MonoidHom.comp_apply]
  have h_fin : X.finiteEquiv (X.ratEquiv γ : New.G E ε).2 =
      (S.inclHFin η)⁻¹ * S.ratToFin γ * S.inclHFin η := by
    rw [finiteEquiv_eq_conj_adelicToFin, adelicEquiv_ratEquiv, ratToFin, MonoidHom.comp_apply]
  rw [cutBessel, h_inf]
  simp [X.mem_stdPrincipalLevel_iff, h_fin, mul_assoc]

/-- The cut-off function of a = (c, i) at γ·g is bounded by β_c(y) ∏_v ‖W_v(y_v)‖, where y is γ_∞
times the image of g_∞ under `New.Filling.Fits.realHomeomorph`, β_c is the cutoff of c and W_v is
the local Bessel function. -/
theorem enorm_cutBessel_ratEquiv_mul_le (γ : S.G E) :
    ‖X.cutBessel a (X.ratEquiv γ * g)‖ₑ ≤
      S.classCutoff a.1 (S.ratToInf γ * X.realHomeomorph g.1) *
        ∏ v : NumberField.InfinitePlace E,
          ‖(S.besselSystem v).besselFn .full ((S.ratToInf γ * X.realHomeomorph g.1) v)‖ₑ := by
  -- A coordinate of a vector is bounded by its norm.
  have h_coord (y : NumberField.InfinitePlace E → 𝔰.G₁) :
      ‖S.besselFn .full y a.2‖ₑ ≤ ∏ v, ‖(S.besselSystem v).besselFn .full (y v)‖ₑ := by
    simp only [besselFn, enorm_eq_nnnorm, nnnorm_prod]
    norm_cast
    gcongr
    exact nnnorm_apply_le _ _
  simp only [cutBessel_ratEquiv_mul]
  split
  · grw [enorm_toReal_smul_le, h_coord]
  · simp

end

/-- The Poincaré series of φ: g ↦ ∑_a φ_a ∑_{γ∈Γ} `New.Filling.Fits.cutBessel` a (γg), where
Γ = `V.Γ` is the group of rational points and a runs over pairs (class, coordinate). -/
@[local simp]
def poincareSeries (φ : EuclideanSpace ℂ (S.Classes × S.BesselCoord)) (g : New.G E ε) : ℂ :=
  ∑ a : S.Classes × S.BesselCoord, φ a * ∑' γ : V.Γ, X.cutBessel a (γ * g)

variable {X} [S.IsAdmissible]

/-- For admissible filling data, the cut-off Bessel function of a is measurable on the adelic
group. -/
@[fun_prop]
theorem measurable_cutBessel : Measurable (X.cutBessel a) :=
  .indicator (by fun_prop) S.stdPrincipalLevel.isOpen'.preimage_of_continuous.measurableSet

open scoped Classical in
/-- Assume `S.IsAdmissible`. For a = (c, i) and adelic g, sum `X.cutBessel a` at u·g over u in the
rational unipotent group `S.classUnipotent c`, with u embedded by `X.ratEquiv`. The sum is W_i(y),
the i-th coordinate of the full Bessel function `S.besselFn` at the image y of g_∞ under
`X.realHomeomorph`, if h_c⁻¹ ι(η) ψ(g_f) lies in `S.principalLevel`, and 0 otherwise. Here
h_c = `S.classRep c`, η is the central element in `X : S.Fits V l kw Y η`, ι = `S.inclHFin` and
ψ = `X.finiteEquiv`. -/
theorem tsum_cutBessel_classUnipotent :
    ∑' u : S.classUnipotent a.1, X.cutBessel a (X.ratEquiv u * g) =
      if (S.classRep a.1)⁻¹ * (S.inclHFin η * X.finiteEquiv g.2) ∈ S.principalLevel then
        S.besselFn .full (X.realHomeomorph g.1) a.2
      else 0 := by
  -- `S.besselFn` and the condition at the finite places are invariant under `S.classUnipotent a.1`,
  -- and the cutoffs `S.classCutoff` sum to `1` over this group.
  let x : S.GFin := S.inclHFin η * X.finiteEquiv g.2
  have h_level (u : S.classUnipotent a.1) :
      (S.classRep a.1)⁻¹ * (S.ratToFin u * x) ∈ S.principalLevel ↔
        (S.classRep a.1)⁻¹ * x ∈ S.principalLevel := by
    have hu : (S.classRep a.1)⁻¹ * S.ratToFin u * S.classRep a.1 ∈ S.principalLevel := by
      simpa using (Subgroup.mem_inf.1 u.2).2
    simp [← S.principalLevel.mul_mem_cancel_left hu (y := (S.classRep a.1)⁻¹ * x), mul_assoc]
  simp only [cutBessel_ratEquiv_mul, besselFn_mul_of_mem_classUnipotent, h_level, x]
  split
  · exact tsum_toReal_smul_of_tsum_eq_one (S.tsum_classCutoff_eq_one a.1 (X.realHomeomorph g.1)) _
  · exact tsum_zero

/-- Let V fit the admissible filling data S (the hypothesis X) and let a = (class, coordinate). The
sums over γ in the group `V.Γ` of rational points of the norms of the cut-off Bessel function
`X.cutBessel a` at γg are bounded uniformly in the adelic point g.

Known result: a step in the convergence of Poincaré series along a Bessel subgroup. -/
theorem exists_tsum_enorm_cutBessel_le :
    ∃ M : NNReal, ∀ g : New.G E ε, ∑' γ : V.Γ, ‖X.cutBessel a (γ * g)‖ₑ ≤ M := by
  -- `M` bounds the sum of the norms over the set `T` of terms over `(c, 1, c)` with `c = a.1`.
  let T : Set (S.G E) := Set.univ ∩ S.termsOver a.1 1 a.1
  obtain ⟨M, hM⟩ : ∃ M : NNReal, ∀ y : NumberField.InfinitePlace E → 𝔰.G₁,
      ∑' γ : T, S.classCutoff a.1 ((S.ratToInf γ)⁻¹ * y) *
        ∏ v, ‖(S.besselSystem v).besselFn .full (((S.ratToInf γ)⁻¹ * y) v)‖ₑ ≤ M :=
    (exists_tsum_classCutoff_mul_prod_enorm_le .univ a.1 1).imp fun _ hM y ↦
      (ENNReal.le_tsum a.1).trans (hM y)
  refine ⟨M, fun g ↦ ?_⟩
  -- All terms vanish unless some `δ` satisfies the level condition `InLevel δ` at the finite
  -- places. Then write the terms as `γ⁻¹ * δ` and compare with `hM` at the point
  -- `S.ratToInf δ * X.realHomeomorph g.1`.
  let InLevel (δ : S.G E) : Prop :=
    (S.classRep a.1)⁻¹ * (S.ratToFin δ * (S.inclHFin η * X.finiteEquiv g.2)) ∈ S.principalLevel
  have h_zero (δ : S.G E) (hδ : ¬InLevel δ) : X.cutBessel a (X.ratEquiv δ * g) = 0 :=
    (X.cutBessel_ratEquiv_mul a g δ).trans (ite_eq_right hδ)
  rw [← X.ratEquiv.tsum_eq]
  obtain h_none | ⟨δ, hδ⟩ : (∀ δ, ¬InLevel δ) ∨ ∃ δ, InLevel δ := by grind
  · simp [h_zero _ (h_none _)]
  -- If `γ⁻¹ * δ` satisfies the condition too, then `γ` lies in `T`.
  have h_over (γ : S.G E) (hγ : InLevel (γ⁻¹ * δ)) : γ ∈ T := by
    simpa [T, principalLevel, termsOver, translateByClassReps, mul_assoc] using mul_mem hδ
      (inv_mem hγ)
  calc ∑' γ : S.G E, ‖X.cutBessel a (X.ratEquiv γ * g)‖ₑ
      = ∑' γ : S.G E, ‖X.cutBessel a (X.ratEquiv (γ⁻¹ * δ) * g)‖ₑ :=
        ((Equiv.divLeft δ).symm.tsum_eq _).symm
    _ = ∑' γ : T, ‖X.cutBessel a (X.ratEquiv (γ.val⁻¹ * δ) * g)‖ₑ := by
        refine (tsum_subtype_eq_of_support_subset fun γ hγ ↦ h_over γ (by_contra fun h ↦ ?_)).symm
        exact hγ (by simp only [h_zero _ h, enorm_zero])
    _ ≤ M := by
        refine le_trans (ENNReal.tsum_le_tsum fun γ ↦ ?_) (hM (S.ratToInf δ * X.realHomeomorph g.1))
        simpa only [map_mul S.ratToInf, map_inv, mul_assoc] using
          X.enorm_cutBessel_ratEquiv_mul_le a g (γ.val⁻¹ * δ)

/-! ### Unfolding and Petersson products -/

/-- If the filling data are admissible, each cut-off Bessel function `X.cutBessel a` is integrable
on the adelic group. -/
theorem integrable_cutBessel : Integrable (X.cutBessel a) := by
  -- The sum of its norms over `V.Γ` is bounded and the quotient by `V.Γ` has finite volume.
  refine ⟨by fun_prop, ?_⟩
  calc ∫⁻ g, ‖X.cutBessel a g‖ₑ
    _ = ∫⁻ g, ∫⁻ γ : V.Γ, ‖X.cutBessel a (γ • g)‖ₑ ∂.count ∂V.quotMeasure :=
      (lintegral_orbitMeasure_lintegral (by fun_prop)).symm
    _ < ⊤ := by
      simp_rw [lintegral_count]
      exact IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal _
        (X.exists_tsum_enorm_cutBessel_le a)

omit [S.IsAdmissible] [HasPrimitiveRoot5040 E] in
/-- A function y invariant under Γ = `V.Γ` moves into the sum over Γ of the translates of
`X.cutBessel a`. -/
private theorem mul_tsum_cutBessel {y : New.G E ε → ℂ}
    (hy_inv : ∀ (γ : V.Γ) (g : New.G E ε), y (γ * g) = y g) :
    y g * ∑' γ : V.Γ, X.cutBessel a (γ * g) = ∑' γ : V.Γ, y (γ * g) * X.cutBessel a (γ * g) := by
  simp only [hy_inv, tsum_mul_left]

/-- For admissible filling data and a form y on V of any type e (a bounded automorphic function),
the product y·`X.cutBessel a` is integrable on the adelic group. -/
theorem integrable_mul_cutBessel {e : GInf E ε → ℂ} {y : New.G E ε → ℂ} (hy : V.IsForm e y) :
    Integrable fun g : New.G E ε ↦ y g * X.cutBessel a g := by
  simpa only [mul_comm, id] using
    hy.isBoundedMeasurable.integrable_mul_comp (X.integrable_cutBessel a) id

/-- For admissible filling data and a form y on V of any type e, the product of y with the sum over
Γ = `V.Γ` of the translates of `X.cutBessel a` is integrable on Γ∖G. -/
theorem integrable_mul_tsum_cutBessel {e : GInf E ε → ℂ} {y : New.G E ε → ℂ} (hy : V.IsForm e y) :
    Integrable (fun g : New.G E ε ↦ y g * ∑' γ : V.Γ, X.cutBessel a (γ * g)) V.Γ.quotMeasure := by
  have hy_inv (γ : V.Γ) (g : New.G E ε) : y (γ * g) = y g := hy.rat_mul _ γ.property g
  simpa only [mul_tsum_cutBessel a _ hy_inv] using
    integrable_quotMeasure_tsum V.Γ (integrable_mul_cutBessel a hy)

/-- Unfolding of one term, for admissible filling data and a form y on V of any type e: the
integral over Γ∖G of y times the sum over Γ = `V.Γ` of the translates of `X.cutBessel a` is
∫_G y·`X.cutBessel a`. -/
theorem integral_mul_tsum_cutBessel {e : GInf E ε → ℂ} {y : New.G E ε → ℂ} (hy : V.IsForm e y) :
    ∫ g : New.G E ε, y g * ∑' γ : V.Γ, X.cutBessel a (γ * g) ∂V.Γ.quotMeasure =
      ∫ g : New.G E ε, y g * X.cutBessel a g := by
  have hy_inv (γ : V.Γ) (g : New.G E ε) : y (γ * g) = y g := hy.rat_mul _ γ.property g
  simpa only [mul_tsum_cutBessel a _ hy_inv] using
    integral_quotMeasure_tsum_eq V.Γ (integrable_mul_cutBessel a hy)

omit [S.IsAdmissible] [HasPrimitiveRoot5040 E] in
/-- The product of y with the Poincaré series of φ, expanded over the pairs a. -/
private theorem mul_poincareSeries_eq_sum (y : New.G E ε → ℂ) :
    y g * X.poincareSeries φ g =
      ∑ a : S.Classes × S.BesselCoord, φ a * (y g * ∑' γ : V.Γ, X.cutBessel a (γ * g)) := by
  simp only [poincareSeries, Finset.mul_sum, mul_left_comm]

/-- For admissible filling data and a form y on V of any type e (a bounded automorphic function),
the product of y with the Poincaré series of φ is integrable on Γ∖G. -/
theorem integrable_mul_poincareSeries {e : GInf E ε → ℂ} {y : New.G E ε → ℂ} (hy : V.IsForm e y) :
    Integrable (fun g : New.G E ε ↦ y g * X.poincareSeries φ g) V.Γ.quotMeasure := by
  simp only [mul_poincareSeries_eq_sum]
  exact integrable_finsetSum _ fun a _ ↦ (integrable_mul_tsum_cutBessel a hy).const_mul (φ a)

/-- Unfolding, for admissible filling data and a form y on V of any type e (a bounded automorphic
function): the integral over Γ∖G of y times the Poincaré series of φ is
∑_a φ_a ∫_G y·`X.cutBessel a`. -/
theorem integral_mul_poincareSeries {e : GInf E ε → ℂ} {y : New.G E ε → ℂ} (hy : V.IsForm e y) :
    ∫ g : New.G E ε, y g * X.poincareSeries φ g ∂V.Γ.quotMeasure =
      ∑ a : S.Classes × S.BesselCoord, φ a * ∫ g : New.G E ε, y g * X.cutBessel a g := by
  simp only [mul_poincareSeries_eq_sum]
  rw [integral_finsetSum _ fun a _ ↦ (integrable_mul_tsum_cutBessel a hy).const_mul (φ a)]
  simp only [integral_const_mul, integral_mul_tsum_cutBessel _ hy]

/-- Unfolding, for admissible filling data S. Let y be a form on V of any type e (a bounded
automorphic function). Then y times the Poincaré series of φ is integrable on Γ∖G, with integral ∑_a
φ_a ∫_G y·`X.cutBessel a`.

Known result: the unfolding of Poincaré series along a Bessel subgroup. -/
theorem integrable_and_integral_mul_poincareSeries {e : GInf E ε → ℂ} {y : New.G E ε → ℂ}
    (hy : V.IsForm e y) :
    Integrable (fun g : New.G E ε ↦ y g * X.poincareSeries φ g) V.Γ.quotMeasure ∧
    ∫ g : New.G E ε, y g * X.poincareSeries φ g ∂V.Γ.quotMeasure =
      ∑ a : S.Classes × S.BesselCoord, φ a * ∫ g : New.G E ε, y g * X.cutBessel a g :=
  ⟨integrable_mul_poincareSeries φ hy, integral_mul_poincareSeries φ hy⟩

omit [S.IsAdmissible] [HasPrimitiveRoot5040 E] in
/-- Right convolution over the real points with `typeKernel l ε` fixes each coordinate of the full
Bessel function, read on G_∞ through `X.realHomeomorph`. -/
theorem integral_typeKernel_mul_besselFn (x : GInf E ε) (i : S.BesselCoord) :
    ∫ z : GInf E ε, typeKernel l ε z * S.besselFn .full (X.realHomeomorph (x * z)) i =
      S.besselFn .full (X.realHomeomorph x) i := by
  -- `X.realHomeomorph` is `frameEquiv.symm` at each place, followed by a left translation.
  have h_homeo (z : GInf E ε) (v : NumberField.InfinitePlace E) :
      X.realHomeomorph (x * z) v = X.realHomeomorph x v * DiscreteSeries.frameEquiv.symm (z v) := by
    simp [realHomeomorph, mul_assoc]
    rfl
  -- The integrand is a product over the places, and the kernel at `v` fixes the local function.
  let F (v : NumberField.InfinitePlace E) (z : USign ε) : ℂ := (l v).dsKernel z *
    (S.besselSystem v).besselFn .full (X.realHomeomorph x v * DiscreteSeries.frameEquiv.symm z)
      (i v)
  calc ∫ z : GInf E ε, typeKernel l ε z * S.besselFn .full (X.realHomeomorph (x * z)) i
      = ∫ z : GInf E ε, ∏ v, F v (z v) := by simp only [F, besselFn, h_homeo, prod_mul_distrib]
    _ = ∏ v, ∫ z : USign ε, F v z := integral_fintype_prod_volume_eq_prod F
    _ = S.besselFn .full (X.realHomeomorph x) i :=
        prod_congr rfl fun v _ ↦ (X.isDiscreteSeriesBessel v).integral_dsKernel_mul
          (X.realHomeomorph x v) (i v)

/-- Assume `S.IsAdmissible`. Let a = (c, i) and δ be in the adelic group. Consider the function
x ↦ sum over u in `S.classUnipotent c` of `X.cutBessel a` (u δ x). This function is fixed by right
convolution with `typeKernel l ε`: its convolution at each g equals its value at g. -/
theorem realConv_tsum_cutBessel_classUnipotent (δ : New.G E ε) :
    realConv (typeKernel l ε)
        (fun x : New.G E ε ↦ ∑' u : S.classUnipotent a.1, X.cutBessel a (X.ratEquiv u * (δ * x))) g
          =
      ∑' u : S.classUnipotent a.1, X.cutBessel a (X.ratEquiv u * (δ * g)) := by
  classical
  -- The sum is a translate of `S.besselFn` times an indicator at the finite places.
  have h_sum (x : GInf E ε) :
      ∑' u : S.classUnipotent a.1, X.cutBessel a ((X.ratEquiv u : New.G E ε) * (δ * (g * (x, 1)))) =
        if (S.classRep a.1)⁻¹ * (S.inclHFin η * X.finiteEquiv (δ * g).2) ∈ S.principalLevel then
          S.besselFn .full (X.realHomeomorph ((δ * g).1 * x)) a.2
        else 0 := by
    simp [tsum_cutBessel_classUnipotent, mul_assoc]
  simp only [realConv, h_sum, tsum_cutBessel_classUnipotent]
  split
  · exact X.integral_typeKernel_mul_besselFn _ _
  · simp only [mul_zero, integral_zero]

/-- Let V fit the admissible filling data S (the hypothesis X) and let a = (class, coordinate). The
series g ↦ ∑_γ `X.cutBessel a` (γg) over the rational points γ ∈ `V.Γ` is a form on V of type
`typeKernel l ε` (the discrete series kernel of parameter l) and level `S.stdPrincipalLevel`. -/
theorem exists_levelSpace_tsum_cutBessel_eq :
    ∃ y : levelSpace (V.formRep (typeKernel l ε)) S.stdPrincipalLevel, ∀ g : New.G E ε,
      ∑' γ : V.Γ, X.cutBessel a (γ * g) = (y : V.Form (typeKernel l ε)) g := by
  obtain ⟨M, hM⟩ := X.exists_tsum_enorm_cutBessel_le a
  -- Group the series by cosets of `S.classUnipotent a.1`; `F q` is the part of the coset `q`.
  let cosetEquiv : (S.G E ⧸ S.classUnipotent a.1) × S.classUnipotent a.1 ≃ V.Γ :=
    (cosetProdEquiv (S.classUnipotent a.1)).trans X.ratEquiv.toEquiv
  let F (q : S.G E ⧸ S.classUnipotent a.1) (g : New.G E ε) : ℂ :=
    ∑' u : S.classUnipotent a.1, X.cutBessel a (cosetEquiv (q, u) * g)
  have h_group (g : New.G E ε) :
      ∑' γ : V.Γ, X.cutBessel a (γ * g) = ∑' q : S.G E ⧸ S.classUnipotent a.1, F q g := by
    rw [← cosetEquiv.tsum_eq]
    exact (cosetEquiv.summable_iff.2 (.of_enorm ((hM g).trans_lt ENNReal.coe_lt_top).ne)).tsum_prod
  have h_bound (g : New.G E ε) : ∑' q : S.G E ⧸ S.classUnipotent a.1, ‖F q g‖ₑ ≤ M := by
    grw [← hM g, ← cosetEquiv.tsum_eq, ENNReal.tsum_prod', ← enorm_tsum_le_tsum_enorm]
  have h_fix (q : S.G E ⧸ S.classUnipotent a.1) (g : New.G E ε) :
      realConv (typeKernel l ε) (F q) g = F q g := by
    simpa [F, cosetEquiv, mul_assoc] using
      X.realConv_tsum_cutBessel_classUnipotent a g (X.ratEquiv q.out⁻¹)
  have h_level : HasLevel (X.cutBessel a) S.stdPrincipalLevel := fun k hk g ↦ by
    classical
    rw [cutBessel, cutBessel, show (g * ((1 : GInf E ε), k)).1 = g.1 from mul_one g.1]
    exact if_congr (by rw [Prod.snd_mul, ← mul_assoc, mul_mem_cancel_right hk]) rfl rfl
  have : Countable (S.G E ⧸ S.classUnipotent a.1) := inferInstanceAs (Countable (Quotient _))
  obtain ⟨y, hy⟩ :
      ∃ y : levelSpace (V.formRep (typeKernel l ε)) S.stdPrincipalLevel.toSubgroup,
        (y.val : New.G E ε → ℂ) = fun g : New.G E ε ↦
          ∑' q : S.G E ⧸ S.classUnipotent a.1, realConv (typeKernel l ε) (F q) g :=
    V.exists_form_eq_tsum X.isIdempotentKernel S.stdPrincipalLevel (by fun_prop) h_level h_group
      ENNReal.coe_ne_top h_bound
  exact ⟨y, fun g ↦ by simp only [hy, h_fix, h_group]⟩

variable (X) in
open scoped Classical in
/-- For admissible filling data, the linear map from source forms φ to forms of type
`typeKernel l ε` and level `S.stdPrincipalLevel` that sends the basis vector at a to the form
g ↦ ∑_{γ∈Γ} `X.cutBessel a` (γg). It sends φ to the Poincaré series of φ, by
`New.Filling.Fits.coe_poincareMap`. -/
def poincareMap :
    EuclideanSpace ℂ (S.Classes × S.BesselCoord) →ₗ[ℂ]
      levelSpace (V.formRep (typeKernel l ε)) S.stdPrincipalLevel :=
  (basisFun 2 ℂ (S.Classes × S.BesselCoord)).constr ℂ fun a : S.Classes × S.BesselCoord ↦
    (X.exists_levelSpace_tsum_cutBessel_eq a).choose

omit [S.IsAdmissible] in
/-- Let the hermitian space V fit the admissible filling data S (the hypothesis X), and let φ be a
vector with coordinates φ_a indexed by pairs a = (class, Bessel coordinate). The form
`X.poincareMap φ` on V, of type `typeKernel l ε` and level `S.stdPrincipalLevel`, is as a function
on the adelic group the Poincaré series `X.poincareSeries φ`. -/
theorem coe_poincareMap (X : S.Fits V l kw Y η) [S.IsAdmissible]
    (φ : EuclideanSpace ℂ (S.Classes × S.BesselCoord)) :
    ⇑(X.poincareMap φ : V.Form (typeKernel l ε)) = X.poincareSeries φ := by
  -- The series of each `X.cutBessel a` is a form `y a`, and `X.poincareMap φ = ∑_a φ_a y a`.
  let y (a : S.Classes × S.BesselCoord) :
      levelSpace (V.formRep (typeKernel l ε)) S.stdPrincipalLevel :=
    (X.exists_levelSpace_tsum_cutBessel_eq a).choose
  have hy (a : S.Classes × S.BesselCoord) (g : New.G E ε) :
      ∑' γ : V.Γ, X.cutBessel a (γ * g) = (y a : V.Form (typeKernel l ε)) g :=
    (X.exists_levelSpace_tsum_cutBessel_eq a).choose_spec g
  have h_sum : X.poincareMap φ = ∑ a : S.Classes × S.BesselCoord, φ a • y a := by
    simp [poincareMap, y]
  funext g
  -- Evaluation at `g` is linear.
  let ev : levelSpace (V.formRep (typeKernel l ε)) S.stdPrincipalLevel →ₗ[ℂ] ℂ :=
    { toFun z := (z : V.Form (typeKernel l ε)) g
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  calc ev (X.poincareMap φ)
      = ∑ a : S.Classes × S.BesselCoord, φ a * ev (y a) := by
        simp only [h_sum, map_sum, map_smul, smul_eq_mul]
    _ = X.poincareSeries φ g := sum_congr rfl fun a _ ↦ congrArg (φ a * ·) (hy a g).symm

omit [S.IsAdmissible] [HasPrimitiveRoot5040 E] in
/-- The homeomorphism `X.realHomeomorph` from G_∞ onto ∏_v `𝔰.G₁` preserves the volumes. -/
theorem measurePreserving_realHomeomorph : MeasurePreserving X.realHomeomorph.toMeasurableEquiv :=
  .symm X.realHomeomorph.symm.toMeasurableEquiv <| volume_preserving_pi fun _ ↦
    DiscreteSeries.measurePreserving_frameEquiv.comp (measurePreserving_mul_left _ _)

variable (X) in
/-- The point ψ⁻¹(ι(η)⁻¹ h_c) of the finite adelic group of V that represents the class c. Here
h_c = `S.classRep c`, ψ = `New.Filling.Fits.finiteEquiv`, ι = `New.Filling.inclHFin`, and η is the
central element of the fit. -/
def classPoint (c : S.Classes) : Gf E 𝔰.BesselIndex :=
  X.finiteEquiv.symm ((S.inclHFin η)⁻¹ * S.classRep c)

open scoped Classical in
omit [S.IsAdmissible] [HasPrimitiveRoot5040 E] in
/-- The function `X.cutBessel a g` equals `S.classCutoff a.1` times the `a.2`-th coordinate of
`S.besselFn .full`, both evaluated at `X.realHomeomorph g.1`, times the indicator of
`S.stdPrincipalLevel` evaluated at `(X.classPoint a.1)⁻¹ * g.2`. -/
theorem cutBessel_eq_mul_indicator (g : New.G E ε) :
    X.cutBessel a g =
      ((S.classCutoff a.1 (X.realHomeomorph g.1)).toReal • S.besselFn .full (X.realHomeomorph g.1)
        a.2) *
        S.stdPrincipalLevel.carrier.indicator 1 ((X.classPoint a.1)⁻¹ * g.2) := by
  have h_point : (X.classPoint a.1)⁻¹ = X.finiteEquiv.symm ((S.classRep a.1)⁻¹ * S.inclHFin η) := by
    simp [classPoint]
  simp [cutBessel, h_point, Set.indicator]

/-- **Folding.** Let V fit the admissible filling data S (the hypothesis X), and let z be a form on
V of type e and principal level J = `S.stdPrincipalLevel`. The integral over Γ∖G, Γ = `V.Γ`, of z
times the Poincaré series of φ is the volume of J times the sum over the classes c of ∫_{G_∞} β_c(y)
(∑_i φ_{(c, i)} W_i(y)) z(x, x_c) dx. Here y is the image of x under `X.realHomeomorph`,
x_c = `X.classPoint c`, W_i is the i-th coordinate of the Bessel function, and
β_c = `S.classCutoff c` is the cutoff for the quotient by `S.classUnipotent c`. -/
theorem integral_mul_poincareSeries_eq_sum_classes {e : GInf E ε → ℂ} {z : New.G E ε → ℂ}
    (hz : V.IsForm e z) (hz_level : HasLevel z S.stdPrincipalLevel.toSubgroup) :
    ∫ g : New.G E ε, z g * X.poincareSeries φ g ∂V.Γ.quotMeasure =
      volume.real S.stdPrincipalLevel.carrier * ∑ c : S.Classes, ∫ x : GInf E ε,
        (S.classCutoff c (X.realHomeomorph x)).toReal •
          (∑ i : S.BesselCoord, φ (c, i) * S.besselFn .full (X.realHomeomorph x) i) *
            z (x, X.classPoint c) := by
  rw [X.integral_mul_poincareSeries φ hz, Fintype.sum_prod_type, mul_sum]
  refine sum_congr rfl fun c _ ↦ ?_
  -- On the coset of `x_c` the form `z` does not depend on the finite part, so the integrand splits.
  set A : GInf E ε → ℂ := fun x ↦ (S.classCutoff c (X.realHomeomorph x)).toReal •
    (∑ i : S.BesselCoord, φ (c, i) * S.besselFn .full (X.realHomeomorph x) i) * z
      (x, X.classPoint c)
  let χ (x : Gf E 𝔰.BesselIndex) : ℂ :=
    S.stdPrincipalLevel.carrier.indicator 1 ((X.classPoint c)⁻¹ * x)
  have h_split (g : New.G E ε) :
      ∑ i : S.BesselCoord, φ (c, i) * (z g * X.cutBessel (c, i) g) = A g.1 * χ g.2 := by
    simp only [cutBessel_eq_mul_indicator]
    by_cases hg : (X.classPoint c)⁻¹ * g.2 ∈ S.stdPrincipalLevel.carrier
    · have h_value : z g = z (g.1, X.classPoint c) := by
        simpa using hz_level _ hg (g.1, X.classPoint c)
      simp only [A, χ, h_value, real_smul, mul_sum, sum_mul]
      exact sum_congr rfl fun i _ ↦ by ring
    · simp [χ, Set.indicator_of_notMem hg]
  have h_vol : ∫ x : Gf E 𝔰.BesselIndex, χ x = volume.real S.stdPrincipalLevel.carrier := by
    rw [integral_mul_left_eq_self (Set.indicator _ 1), Pi.one_def,
      integral_indicator_const _ S.stdPrincipalLevel.isOpen'.measurableSet, real_smul, mul_one]
  calc
    ∑ i : S.BesselCoord, φ (c, i) * ∫ g : New.G E ε, z g * X.cutBessel (c, i) g
      = ∫ g : New.G E ε, A g.1 * χ g.2 := by
        simp only [← h_split, ← integral_const_mul]
        exact (integral_finsetSum _ fun i _ ↦ (integrable_mul_cutBessel (c, i) hz).const_mul _).symm
    _ = (∫ x : GInf E ε, A x) * ∫ x : Gf E 𝔰.BesselIndex, χ x := integral_prod_mul A χ
    _ = _ := by rw [h_vol, mul_comm]

end Series

omit [HasPrimitiveRoot5040 E] p in
/-- The principal level `S.stdPrincipalLevel` is normalised by the integral group `New.stdLevel`, so
the translate by an integral k of a function of principal level has principal level. -/
theorem hasLevel_mul_right {S : Filling E 𝔰} {z : New.G E ε → ℂ}
    (hz : HasLevel z S.stdPrincipalLevel.toSubgroup) (k : stdLevel E 𝔰.BesselIndex) :
    HasLevel (fun g : New.G E ε ↦ z (g * (1, k.1))) S.stdPrincipalLevel.toSubgroup := by
  rintro _ ⟨u, hu, rfl⟩ g
  have h_conj : ((k⁻¹ * u * k : stdLevel E 𝔰.BesselIndex) : Gf E 𝔰.BesselIndex) ∈
      S.stdPrincipalLevel.toSubgroup :=
    ⟨k⁻¹ * u * k, Normal.conj_mem' inferInstance u hu k, rfl⟩
  have h_swap : g * (1, u.1) * (1, k.1) = g * (1, k.1) * (1, (k⁻¹ * u * k).1) := by
    simp [mul_assoc]
  exact (congrArg z h_swap).trans (hz _ h_conj (g * (1, k.1)))

omit [HasPrimitiveRoot5040 E] in
/-- Let S be filling data, K = `S.latticeStabilizer` the integral points of its finite adelic
unitary group, and K(M) = `S.principalLevel` the elements of K whose reduction at the chosen places
is 1. Let c, c' be classes with representatives h_c = `S.classRep c` and h_c', let x be a finite
adelic point with h_c⁻¹ x ∈ K(M), and let k ∈ K have reduction s. For a rational point γ with finite
part γ_f = `S.ratToFin γ`, the element h_c'⁻¹ γ_f⁻¹ x k lies in K(M) if and only if γ is a term over
(c, s, c'). -/
theorem mem_principalLevel_iff_mem_termsOver {S : Filling E 𝔰} {c : S.Classes} (c' : S.Classes)
    {s : S.ResidueGL} {x : S.GFin} (hx : (S.classRep c)⁻¹ * x ∈ S.principalLevel)
    {k : S.latticeStabilizer} (hk : S.reduction k = s) (γ : S.G E) :
    (S.classRep c')⁻¹ * ((S.ratToFin γ)⁻¹ * (x * (k : S.GFin))) ∈ S.principalLevel ↔
      γ ∈ S.termsOver c s c' := by
  -- With `m = h_c⁻¹ x` in K of reduction 1, the element in question is `(h_c⁻¹ γ_f h_c')⁻¹ m k`.
  obtain ⟨m, hm_red, hm⟩ : ∃ m : S.latticeStabilizer,
      S.reduction m = 1 ∧ (m : S.GFin) = (S.classRep c)⁻¹ * x := mem_map.1 hx
  have h_elem : (S.classRep c')⁻¹ * ((S.ratToFin γ)⁻¹ * (x * (k : S.GFin))) =
      (S.translateByClassReps c c' γ)⁻¹ * (m * k : S.latticeStabilizer) := by
    simp [hm, translateByClassReps, mul_assoc]
  have h_red : S.reduction (m * k) = s := by rw [map_mul, hm_red, hk, one_mul]
  rw [h_elem]
  constructor
  · intro h_mem
    obtain ⟨n, hn_red, hn⟩ : ∃ n : S.latticeStabilizer, S.reduction n = 1 ∧
        (n : S.GFin) = (S.translateByClassReps c c' γ)⁻¹ * (m * k : S.latticeStabilizer) :=
          mem_map.1 h_mem
    have h_term : S.reduction (m * k * n⁻¹) = s := by
      rw [map_mul, map_inv, hn_red, h_red, inv_one, mul_one]
    exact ⟨m * k * n⁻¹, h_term, by simp [hn, mul_assoc]⟩
  · rintro ⟨n, hn_red, hn⟩
    have h_one : S.reduction (n⁻¹ * (m * k)) = 1 := by
      rw [map_mul, map_inv, hn_red, h_red, inv_mul_cancel]
    exact mem_map.2 ⟨n⁻¹ * (m * k), h_one, by simp [hn]⟩

/-- Let the filling data S be admissible, let T be a set of rational points, c and c' classes with
representatives h_c and h_c', and s a family of matrices over the residue fields of the chosen
places. The terms over (c, s, c') are the rational γ such that h_c⁻¹ γ h_c' lies in
`S.latticeStabilizer` and has reduction s. The amplitude sum is the sum, over the terms γ in T, of
the integrals over y ∈ ∏_v `𝔰.G₁` of β_c(y) β_c'(γ⁻¹y) `S.besselKernel .full γ y`. In its entry
i = (i₁, i₂) sum and integral can be exchanged. Here `𝔰.G₁` is the complex unitary group of the
hermitian form of the shape 𝔰, β_c is the cutoff `S.classCutoff c`, and the entry i of the kernel is
W_{i₁}(y) conj(W_{i₂}(γ⁻¹y)), with W the full Bessel function. -/
theorem amplitudeSum_apply_eq_integral_tsum {S : Filling E 𝔰} [S.IsAdmissible] (T : Set (S.G E))
    (c : S.Classes) (s : S.ResidueGL) (c' : S.Classes) (i : S.BesselCoord × S.BesselCoord) :
    S.amplitudeSum .full T c s c' i =
      ∫ y : NumberField.InfinitePlace E → 𝔰.G₁, ∑' γ : ↥(T ∩ S.termsOver c s c'),
        (S.classCutoff c y * S.classCutoff c' ((S.ratToInf γ)⁻¹ * y)).toReal •
          S.besselKernel .full γ y i := by
  have h_fin : ∑' γ : ↥(T ∩ S.termsOver c s c'), ∫⁻ y,
      ‖(S.classCutoff c y * S.classCutoff c' ((S.ratToInf γ)⁻¹ * y)).toReal •
        S.besselKernel .full γ y‖ₑ < ⊤ := by
    grw [enorm_toReal_smul_le]
    exact (ENNReal.le_tsum c').trans_lt (tsum_amplitudeMajorant_lt_top T c s)
  simpa only [amplitudeSum, amplitude, PiLp.smul_apply] using
    tsum_integral_apply (by fun_prop) h_fin i

open scoped Classical in
/-- Let the hermitian space V fit the admissible filling data S, and let 𝒫a be the Poincaré series
(`X.poincareMap`) of the basis vector at a, as a form on V of type `typeKernel l ε`. For a = (c, i),
a' = (c', i') and k in `New.stdLevel` with reduction s at the chosen places, the Petersson product
⟨k𝒫a', 𝒫a⟩ is the volume of `S.stdPrincipalLevel` times the (i, i') entry of the amplitude sum, ∑_γ
∫ β_c(y) β_c'(γ⁻¹y) W_i(y) conj(W_i'(γ⁻¹y)) dy. Here γ runs over the rational points such that h_c⁻¹
γ h_c' lies in `S.latticeStabilizer` and has reduction s, y runs over ∏_v `𝔰.G₁`,
h_c = `S.classRep c`, β_c = `S.classCutoff c`, and W is the full Bessel function
`S.besselFn .full`. -/
theorem petersson_poincare {S : Filling E 𝔰} {V : Space E 𝔰.BesselIndex ε}
    {l : NumberField.InfinitePlace E → HCParam ε} {kw : NumberField.InfinitePlace E → ℕ → ℕ}
    {Y : Grading V S.N 𝔰.κ (2 * 𝔰.ϱ + 1)} {η : Gf E 𝔰.κ} {X : S.Fits V l kw Y η} [S.IsAdmissible]
    (c c' : S.Classes) (i i' : S.BesselCoord) {k : stdLevel E 𝔰.BesselIndex} {s : S.ResidueGL}
    (hs : stdLevel.reduceFamily (fun w : Σ j : Fin 2, S.chosenPlaces j ↦ (w.snd : FinPlace E)) k =
      Sigma.uncurry s) :
    inner ℂ
        (V.formRep (typeKernel l ε) (k : Gf E 𝔰.BesselIndex)
          (X.poincareMap (EuclideanSpace.single (c', i') 1) : V.Form (typeKernel l ε)))
        (X.poincareMap (EuclideanSpace.single (c, i) 1)) =
      volume.real S.stdPrincipalLevel.carrier *
        S.amplitudeSum .full Set.univ c s c' (i, i') := by
  -- Fold the series of `(c, i)` against the translate `z` of that of `(c', i')`, which stays a sum.
  set z : V.Form (typeKernel l ε) := V.formRep (typeKernel l ε) (k : Gf E 𝔰.BesselIndex)
    (X.poincareMap (EuclideanSpace.single (c', i') 1) : V.Form (typeKernel l ε))
  have hz_level : HasLevel (star ⇑z) S.stdPrincipalLevel.toSubgroup := fun u hu g ↦
    congrArg star (hasLevel_mul_right
      (V.mem_levelSpace_formRep_iff.1 (X.poincareMap (.single (c', i') 1)).property) k u hu g)
  -- At `(x, x_c)` the term `γ⁻¹` of the series survives exactly when `γ` lies over `(c, s, c')`.
  have h_value (x : GInf E ε) : z (x, X.classPoint c) =
      ∑' γ : ↥(Set.univ ∩ S.termsOver c s c'),
        (S.classCutoff c' ((S.ratToInf γ)⁻¹ * X.realHomeomorph x)).toReal •
          S.besselFn .full ((S.ratToInf γ)⁻¹ * X.realHomeomorph x) i' := by
    obtain ⟨hk_mem, hk_red⟩ := (X.reduction_finiteEquiv_iff k s).2 ⟨k.property, hs⟩
    have h_one : (S.classRep c)⁻¹ * S.classRep c ∈ S.principalLevel := by simp
    have h_term (γ : S.G E) :
        X.cutBessel (c', i') ((X.ratEquiv γ⁻¹ : New.G E ε) * ((x, X.classPoint c) * (1, k.1))) =
          if γ ∈ S.termsOver c s c' then
            (S.classCutoff c' ((S.ratToInf γ)⁻¹ * X.realHomeomorph x)).toReal •
              S.besselFn .full ((S.ratToInf γ)⁻¹ * X.realHomeomorph x) i' else 0 := by
      rw [cutBessel_ratEquiv_mul]
      simp [← mem_principalLevel_iff_mem_termsOver c' h_one hk_red γ, classPoint, mul_assoc]
    calc
      _ = ∑' γ : S.G E,
          X.cutBessel (c', i')
            ((X.ratEquiv γ⁻¹ : New.G E ε) * ((x, X.classPoint c) * (1, k.1))) := by
        change (X.poincareMap (.single (c', i') 1)).val ((x, X.classPoint c) * (1, k.1)) = _
        rw [X.coe_poincareMap]
        simp [poincareSeries, ← ((Equiv.inv (S.G E)).trans X.ratEquiv.toEquiv).tsum_eq]
      _ = _ := by
        rw [← tsum_subtype_eq_of_support_subset (s := Set.univ ∩ S.termsOver c s c')]
        · exact tsum_congr fun γ ↦ by rw [h_term, ite_eq_left γ.property.2]
        · exact fun γ hγ ↦ ⟨trivial, by_contra fun h ↦ hγ ((h_term γ).trans (ite_eq_right h))⟩
  calc
    _ = ∫ g : New.G E ε, star (z g) * X.poincareSeries (.single (c, i) 1) g ∂V.Γ.quotMeasure := by
      rw [← X.coe_poincareMap]
      rfl
    _ = volume.real S.stdPrincipalLevel.carrier * ∫ x : GInf E ε,
        (S.classCutoff c (X.realHomeomorph x)).toReal • S.besselFn .full (X.realHomeomorph x) i *
          star (z (x, X.classPoint c)) := by
      refine (integral_mul_poincareSeries_eq_sum_classes _ (z.property : V.IsForm _ z).conj
        hz_level).trans ?_
      rw [Fintype.sum_eq_single c fun d hd ↦ by simp [Prod.ext_iff, hd]]
      simp [Prod.ext_iff]
    _ = _ := by
      rw [amplitudeSum_apply_eq_integral_tsum, ← X.measurePreserving_realHomeomorph.integral_comp']
      refine congrArg _ (integral_congr_ae (.of_forall fun x ↦ ?_))
      simp only [h_value, tsum_star, ← tsum_mul_left, besselKernel, ENNReal.toReal_mul, real_smul,
        ofReal_mul, star_mul', Homeomorph.toMeasurableEquiv_coe, RCLike.star_def, conj_ofReal]
      exact tsum_congr fun γ ↦ by ring

end Fits

end New.Filling

end PoincareSeries

/-!
## Groups of a graded fitting space and source forms in Bessel coordinates

* `New.Filling.Fits.adelicToFin_adelicEquiv_inclX`, `New.Filling.Fits.finiteEquiv_inclX`,
  `New.Filling.Fits.adelicToInf_inclX`: the embeddings of U(X₀) agree.
-/

open Matrix in
/-- In the labelling `𝔰.besselIndexEquiv`, the matrix acting by m on κ and trivially on the string
of length 2ϱ + 1 is the block matrix with m in the κ-block and the identity elsewhere. -/
lemma New.Shape.submatrix_fromBlocks_besselIndexEquiv (𝔰 : Shape) {R : Type*} [Zero R] [One R]
    (m : Matrix 𝔰.κ 𝔰.κ R) :
    (fromBlocks m 0 0 1).submatrix 𝔰.besselIndexEquiv.symm 𝔰.besselIndexEquiv.symm =
      fromBlocks 1 0 0 (fromBlocks (fromBlocks m 0 0 1) 0 0 1) := by
  -- Compare entries block by block; what is left is arithmetic of the string indices.
  ext (i | (i | i) | i) (j | (j | j) | j) <;>
    simp [besselIndexEquiv, one_apply, Fin.ext_iff] <;> lia

open Matrix in
/-- A Kronecker product acts on a product vector factor by factor. -/
lemma New.kroneckerPi_mulVec_prod {T : Type} [Fintype T] [DecidableEq T] {I : T → Type}
    [∀ v : T, Fintype (I v)] (M : ∀ v : T, Matrix (I v) (I v) ℂ) (z : ∀ v : T, I v → ℂ)
    (i : ∀ v : T, I v) :
    (kroneckerPi M *ᵥ fun j : ∀ v : T, I v ↦ ∏ v : T, z v (j v)) i =
      ∏ v : T, (M v *ᵥ z v) (i v) := by
  simp [kroneckerPi, mulVec, dotProduct, Finset.prod_univ_sum, Finset.prod_mul_distrib]

namespace New.Filling.Fits

open Matrix Equiv Grading

variable {E : Type} {𝔰 : Shape} [Field E] [CMType E] {S : Filling E 𝔰}
variable {ε : 𝔰.BesselIndex → ℤˣ} {l : NumberField.InfinitePlace E → HCParam ε}
  {kw : NumberField.InfinitePlace E → ℕ → ℕ}
variable {V : Space E 𝔰.BesselIndex ε} {Y : Grading V S.N 𝔰.κ (2 * 𝔰.ϱ + 1)} {η : Gf E 𝔰.κ}
  [DiscreteSeries.UnitarySignFrame 𝔰 ε]

/-- The grade of an index in the grading Y is twice the difference of ϱ and its level. -/
lemma gradeOf_eq_two_mul_sub_level (X : S.Fits V l kw Y η) (i : 𝔰.BesselIndex) :
    Y.gradeOf i = 2 * (𝔰.ϱ - BesselIndex.level i) := by
  rcases i with i | (i | i) | i <;>
    simp [X.index_eq, gradeOf, BesselIndex.level, Shape.besselIndexEquiv] <;> lia

/-- Under `X.adelicEquiv`, the unipotent group of the grading Y corresponds to the Bessel unipotent
group `besselU` of the adelic group of S. -/
lemma mem_unipotent_iff_mem_besselU (X : S.Fits V l kw Y η) {g : New.G E ε} :
    g ∈ Y.unipotent ↔ X.adelicEquiv g ∈ besselU := by
  -- Both groups prescribe some entries `(i, j)` of the same matrix to be those of the identity,
  -- and the prescribed entries are the same.
  have h_entry (i j : 𝔰.BesselIndex) :
      -Y.gradeOf j ≤ -Y.gradeOf i ↔ BesselIndex.level j ≤ BesselIndex.level i := by
    simp only [X.gradeOf_eq_two_mul_sub_level]
    lia
  exact forall₂_congr fun i j ↦ imp_congr_left (h_entry i j)

/-- Under `X.adelicEquiv`, the Bessel group of the grading Y corresponds to the Bessel group
`besselS` of the adelic group of S. -/
lemma mem_besselGroup_iff_mem_besselS (X : S.Fits V l kw Y η) {g : New.G E ε} :
    g ∈ Y.besselGroup ↔ X.adelicEquiv g ∈ besselS := by
  -- Both groups prescribe entries `(i, j)` of the same matrix, in the columns `j` of the string
  -- vectors of grade `≥ 0`, to be those of the identity; check each block of columns.
  have h_entry (i j : 𝔰.BesselIndex) :
      (Y.indexEquiv.symm j).isRight ∧ 0 ≤ Y.gradeOf j ∧ Y.gradeOf i ≤ Y.gradeOf j ↔
        BesselIndex.level j ≤ BesselIndex.level i ∧
          (Floors.FloorGroups.floorOf j < 𝔰.n ∧ BesselIndex.level j < 𝔰.n ∨ 𝔰.n < 𝔰.n) := by
    simp only [X.gradeOf_eq_two_mul_sub_level]
    rcases j with j | (j | j) | j <;>
      simp [X.index_eq, BesselIndex.level, Shape.besselIndexEquiv] <;> grind
  exact forall₂_congr fun i j ↦ imp_congr_left (h_entry i j)

/-- The image of `Y.inclX a` under `X.adelicEquiv` is, as a matrix over the adeles, the block matrix
that acts by `G.toUnitary a` on the κ block and fixes all other basis vectors. -/
lemma coe_adelicEquiv_inclX (X : S.Fits V l kw Y η) (a : New.G E (1 : 𝔰.κ → ℤˣ)) :
    ((X.adelicEquiv (Y.inclX a)).val : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸 E)) =
      fromBlocks 1 0 0 (fromBlocks (fromBlocks (G.toUnitary a).val 0 0 1) 0 0 1) := by
  rw [← Shape.submatrix_fromBlocks_besselIndexEquiv, ← X.index_eq]
  simp [adelicEquiv, inclX, U.reindex, U.sum]

/-- For `a` in the adelic unitary group of U(X₀) on κ: map `Y.inclX a` by `X.adelicEquiv`, then take
the finite part in the lattice basis (`S.adelicToFin`). The result is `S.inclHFin a.2`. -/
lemma adelicToFin_adelicEquiv_inclX (X : S.Fits V l kw Y η) (a : New.G E (1 : 𝔰.κ → ℤˣ)) :
    S.adelicToFin (X.adelicEquiv (Y.inclX a)) = S.inclHFin a.2 := by
  have h_snd : ((G.toUnitary a).val : Matrix 𝔰.κ 𝔰.κ (𝔸 E)).map Prod.snd = a.2.val := rfl
  simp [adelicToFin, U.map, inclHFin, toBesselH, Units.ext_iff, coe_adelicEquiv_inclX,
    fromBlocks_map, h_snd]

/-- The isomorphism `X.finiteEquiv` takes the finite part of `Y.inclX a` to `S.inclHFin a.2`. -/
lemma finiteEquiv_inclX (X : S.Fits V l kw Y η) (a : New.G E (1 : 𝔰.κ → ℤˣ)) :
    X.finiteEquiv (Y.inclX a).2 = S.inclHFin a.2 := by
  -- `X.finiteEquiv` is `S.adelicToFin ∘ X.adelicEquiv` conjugated by `S.inclHFin η`, which commutes
  -- with `S.inclHFin a.2` because η is central in `Gf E 𝔰.κ`.
  rw [finiteEquiv_eq_conj_adelicToFin, adelicToFin_adelicEquiv_inclX,
    ((X.central _).map _).inv_mul_cancel]

/-- The isomorphism `X.finiteEquiv` takes the embedding `Y.inclXFin` of the finite adelic points of
U(X₀) to `S.inclHFin`. -/
lemma finiteEquiv_inclXFin (X : S.Fits V l kw Y η) (a : Gf E 𝔰.κ) :
    X.finiteEquiv (Y.inclXFin a) = S.inclHFin a :=
  -- `Y.inclXFin a` is by definition the finite component of `Y.inclX (1, a)`.
  X.finiteEquiv_inclX (1, a)

/-- If `X` says that `V` with grading `Y` fits `S`, then for `a` in `Gf E 𝔰.κ` (finite adelic
U(X₀)), `Y.inclXFin a` lies in `stdLevel`, the stabiliser of the standard lattice, if and only if
`S.inclHFin a` lies in `S.latticeStabilizer`. -/
lemma inclXFin_mem_stdLevel_iff (X : S.Fits V l kw Y η) (a : Gf E 𝔰.κ) :
    Y.inclXFin a ∈ stdLevel E 𝔰.BesselIndex ↔ S.inclHFin a ∈ S.latticeStabilizer := by
  rw [← X.finiteEquiv_mem_latticeStabilizer_iff, finiteEquiv_inclXFin]

/-- A finite adelic point of U(X₀), embedded by the grading Y, lies in the principal level of V at
the chosen places if and only if its image `S.inclHFin a` lies in the principal level of S. -/
lemma inclXFin_mem_stdPrincipalLevel_iff (X : S.Fits V l kw Y η) (a : Gf E 𝔰.κ) :
    Y.inclXFin a ∈ S.stdPrincipalLevel ↔ S.inclHFin a ∈ S.principalLevel := by
  rw [X.mem_stdPrincipalLevel_iff, finiteEquiv_inclXFin]

/-- At each infinite place v, the embedding `Y.inclX` of the adelic unitary group U(X₀) on κ,
rescaled into `𝔰.G₁`, is the embedding `toBesselH` applied to the component at v. -/
lemma adelicToInf_inclX (X : S.Fits V l kw Y η) (a : New.G E (1 : 𝔰.κ → ℤˣ)) :
    S.adelicToInf (X.adelicEquiv (Y.inclX a)) =
      fun v : NumberField.InfinitePlace E ↦ toBesselH 𝔰 1
        ⟨a.1 v, signMatrix_one (n := 𝔰.κ) ▸ (a.1 v).property⟩ := by
  -- The diagonal rescaling `basisScale` is 1 on κ, so conjugating by it fixes this block matrix.
  have h_fst (v : NumberField.InfinitePlace E) (i j : 𝔰.κ) :
      ((G.toUnitary a).val i j).1 v = (a.1 v).val i j := rfl
  ext v (i | (i | i) | i) (j | (j | j) | j) <;>
    simp +contextual [adelicToInf_apply, coe_adelicEquiv_inclX, basisScale, toBesselH, h_fst,
      Matrix.one_apply, Nat.Prime.ne_zero, apply_ite Prod.fst, ite_apply]

/-- If the graded hermitian space V fits the filling data S, there is a linear isomorphism A from
functions on `WeylIndex 𝔰.κ kw` to functions on `S.BesselCoord` with this property. For every family
g of unitary κ×κ matrices g v, one per infinite place v, and every x, the vector A x times
`kroneckerPi` of the matrices `(S.besselSystem v).rep (g v)` equals A applied to `schur kw` of the
transposes (g v)ᵀ times x. -/
lemma exists_weylBesselEquiv (X : S.Fits V l kw Y η) :
    ∃ A : (WeylIndex 𝔰.κ kw → ℂ) ≃ₗ[ℂ] (S.BesselCoord → ℂ),
      ∀ (g : NumberField.InfinitePlace E → U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) (x : WeylIndex 𝔰.κ kw → ℂ),
        A x ᵥ* kroneckerPi (fun v : NumberField.InfinitePlace E ↦
            ((S.besselSystem v).rep (g v) :
              Matrix (S.besselSystem v).Index (S.besselSystem v).Index ℂ)) =
          A (schur kw (fun v : NumberField.InfinitePlace E ↦ (g v : Matrix 𝔰.κ 𝔰.κ ℂ)ᵀ) *ᵥ x) := by
  -- Multiply on the right by the Kronecker product `M` over the infinite places of the local
  -- matrices `A v`, with inverses `A' v`, that `IsDiscreteSeriesBessel.exists_conj_rep_eq_schur`
  -- gives.
  let I (v : NumberField.InfinitePlace E) : Type := WeylIndex 𝔰.κ fun _ : Unit ↦ kw v
  have h_local (v : NumberField.InfinitePlace E) :
      ∃ (A : Matrix (I v) (S.besselSystem v).Index ℂ)
        (A' : Matrix (S.besselSystem v).Index (I v) ℂ),
        A * A' = 1 ∧ A' * A = 1 ∧ ∀ g : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ),
          A * ((S.besselSystem v).rep g).val =
            (schur (fun _ ↦ kw v) fun _ : Unit ↦ (g : Matrix 𝔰.κ 𝔰.κ ℂ)ᵀ)ᵀ * A :=
    (X.isDiscreteSeriesBessel v).exists_conj_rep_eq_schur
  choose A A' hAA' hA'A hA using h_local
  -- `e` reads a global index as a tuple of local indices.
  let e : WeylIndex 𝔰.κ kw ≃ ∀ v, I v := (funUnique Unit (WeylIndex 𝔰.κ kw)).symm.trans (piComm _)
  let M : Matrix (WeylIndex 𝔰.κ kw) S.BesselCoord ℂ := (kroneckerPi A).submatrix e id
  have h_schur (g : NumberField.InfinitePlace E → U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) :
      (schur kw fun v ↦ (g v : Matrix 𝔰.κ 𝔰.κ ℂ)ᵀ)ᵀ =
        (kroneckerPi fun v ↦
          (schur (fun _ ↦ kw v) fun _ : Unit ↦ (g v : Matrix 𝔰.κ 𝔰.κ ℂ)ᵀ)ᵀ).submatrix e e := by
    ext i j
    rw [transpose_apply, schur_apply_eq_prod .refl]
    rfl
  have h_law (g : NumberField.InfinitePlace E → U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) :
      M * kroneckerPi (fun v ↦ ((S.besselSystem v).rep (g v)).val) =
        (schur kw fun v ↦ (g v : Matrix 𝔰.κ 𝔰.κ ℂ)ᵀ)ᵀ * M := by
    rw [h_schur, submatrix_mul_equiv, ← kroneckerPi_mul]
    simp only [← hA, kroneckerPi_mul]
    rfl
  refine ⟨toLinearEquivRight'OfInv (M := (kroneckerPi A').submatrix id e) (M' := M)
    (by simp [M, ← coe_refl, ← kroneckerPi_mul, hA'A])
    (by simp [M, ← coe_refl, ← kroneckerPi_mul, hAA']), fun g x ↦ ?_⟩
  change x ᵥ* M ᵥ* kroneckerPi (fun v ↦ ((S.besselSystem v).rep (g v)).val) =
    (schur kw (fun v ↦ (g v : Matrix 𝔰.κ 𝔰.κ ℂ)ᵀ) *ᵥ x) ᵥ* M
  rw [vecMul_vecMul, h_law, ← vecMul_vecMul, vecMul_transpose]

/-- A fixed change of coordinates as in `exists_weylBesselEquiv`, from the values of forms to the
dual of the values of the Bessel function. -/
def weylBesselEquiv (h : S.Fits V l kw Y η) : (WeylIndex 𝔰.κ kw → ℂ) ≃ₗ[ℂ] (S.BesselCoord → ℂ) :=
  h.exists_weylBesselEquiv.choose

/-- The change of coordinates `X.weylBesselEquiv` turns the Schur matrix of the transposes of the
g v into right multiplication by the Kronecker product of the local representations. -/
lemma weylBesselEquiv_vecMul (X : S.Fits V l kw Y η)
    (g : NumberField.InfinitePlace E → U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) (x : WeylIndex 𝔰.κ kw → ℂ) :
    X.weylBesselEquiv x ᵥ* kroneckerPi (fun v : NumberField.InfinitePlace E ↦
        ((S.besselSystem v).rep (g v) : Matrix (S.besselSystem v).Index (S.besselSystem v).Index ℂ))
          =
      X.weylBesselEquiv
        (schur kw (fun v : NumberField.InfinitePlace E ↦ (g v : Matrix 𝔰.κ 𝔰.κ ℂ)ᵀ) *ᵥ x) :=
  X.exists_weylBesselEquiv.choose_spec g x

/-- The linear isomorphism that sends an algebraic form of weight kw and level `S.sourceLevel` to
its values at the class representatives, in the coordinates `weylBesselEquiv`. -/
def sourceFormCoords (h : S.Fits V l kw Y η) :
    levelSpace (algFormRep kw 0) S.sourceLevel ≃ₗ[ℂ] EuclideanSpace ℂ (S.Classes × S.BesselCoord) :=
  -- Evaluate at the class representatives, change coordinates in each class, then uncurry.
  freeLevelEquiv (stdSpace E 𝔰.κ).embFin (Space.weightRep kw 0 (stdSpace E 𝔰.κ)) 1
    S.classAut_eq_bot Quot.out_eq ≪≫ₗ LinearEquiv.piCongrRight
    (fun _ ↦ h.weylBesselEquiv) ≪≫ₗ LinearEquiv.symm
      (WithLp.linearEquiv .. ≪≫ₗ LinearEquiv.curry ..)

/-- If V fits the filling data S with weight kw, then `S.sourceDim` is the number of classes times
the dimension of the representation of weight kw. -/
lemma sourceDim_eq_card_mul_finrank (X : S.Fits V l kw Y η) :
    S.sourceDim = Fintype.card S.Classes * Module.finrank ℂ (WeylIndex 𝔰.κ kw → ℂ) := by
  rw [X.weylBesselEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card, sourceDim]

/-- Let E be a CM field, and let V, with grading Y, fit the filling data S: among other conditions,
the Bessel system of S at each infinite place v has type (l v, kw v), and η is central. Let X₀ be
the hermitian space on `𝔰.κ` with the standard definite form. The space of algebraic forms on U(X₀)
of weight (kw, 0) and level `S.sourceLevel` has dimension `S.sourceDim`. This equals the number of
double cosets `S.Classes` of U(X₀) at that level times the dimension of `WeylIndex 𝔰.κ kw → ℂ`, the
representation of weight kw, and it is positive. -/
theorem finrank_levelSpace_eq_sourceDim {ε : 𝔰.BesselIndex → ℤˣ}
    {l : NumberField.InfinitePlace E → HCParam ε} {kw : NumberField.InfinitePlace E → ℕ → ℕ}
    {V : Space E 𝔰.BesselIndex ε} {Y : Grading V S.N 𝔰.κ (2 * 𝔰.ϱ + 1)} {η : Gf E 𝔰.κ}
    [DiscreteSeries.UnitarySignFrame 𝔰 ε] (X : S.Fits V l kw Y η) :
    Module.finrank ℂ (levelSpace (algFormRep kw 0) S.sourceLevel) = S.sourceDim ∧
    S.sourceDim = Fintype.card S.Classes * Module.finrank ℂ (WeylIndex 𝔰.κ kw → ℂ) ∧
    0 < S.sourceDim := by
  refine ⟨?_, X.sourceDim_eq_card_mul_finrank, Nat.mul_pos Fintype.card_pos Fintype.card_pos⟩
  -- The level is free, so a form has one arbitrary value at each class.
  rw [X.sourceDim_eq_card_mul_finrank, Fintype.card_eq_nat_card]
  exact finrank_levelSpace_smoothFormRep S.classAut_eq_bot

end New.Filling.Fits

end
