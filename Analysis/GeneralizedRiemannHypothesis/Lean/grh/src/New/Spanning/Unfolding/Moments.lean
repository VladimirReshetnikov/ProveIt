import New.Spanning.SecondMoment.FewTranslates
import New.Spanning.Unfolding.MomentBounds

/-!
# The second moments of the operators `P* s P`, and good forms

Let `S` be admissible filling data, with size parameter `b = S.b`. The finite group
`Ḡ = S.ResidueGL` has one factor for each of the two level primes `p_i = S.levelPrime i`, and
`R̄₀ = S.reducedImage besselS` is the image of the Bessel subgroup in it. The source is the space of
dimension `D_X = S.sourceDim` with coordinates indexed by the classes and the coordinates of the
Bessel function. For a map `P` from the source to a representation `ρ` of `Ḡ` put `P_s = P* ρ(s) P`;
all norms of operators are Hilbert–Schmidt norms. The file proves the two moment bounds for the
`P_s`, and deduces that `e₀ P` is almost an isometry for the projection `e₀` onto the target forms.
We write `𝒟_id = S.identitySecondMoment` and `𝒟_main = S.mainSecondMoment`.

## Main definitions and results

* `New.Filling.HasAmplitudeBlocks`: the blocks of `P_s` are the conjugates of the amplitude sums,
  divided by the covolume.
* `New.Filling.besselTranslate`: the unitary representation `r_ψ` of `R̄₀` on the source, extended
  by `0`.
* `New.Filling.HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sub_besselTranslate_sq_le`: over `R̄₀`
  times one factor of `Ḡ`, `∑ ‖P_s - r_ψ(s)‖² ≤ b⁻¹² 𝒟_id`.
* `New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_sub_one_sq_le`: `‖P* P - 1‖² ≤ b⁻¹² D_X`.
* `New.Filling.HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sq_le`: `∑ ‖P_s‖² ≤ (1 + 9 b⁻⁴) 𝒟_main`
  over `Ḡ`.
* `New.Filling.HasAmplitudeBlocks.isNearIsometry_piTensorElem_comp`: `e₀ P` is almost an isometry in
  mean square, with the error `5 b⁻⁴`.

Notions from other files:
* `New.Filling.reduction`: the homomorphism from the stabilizer `K = S.latticeStabilizer` of the
  lattice to `Ḡ` that reduces matrix entries modulo the chosen places above `p₀` and `p₁`.
* `New.Filling.termsOver`: the terms over a block `(c, s, c')`, the rational `γ` such that
  `h_c⁻¹ γ h_c'` lies in `K` and has reduction `s`.
* `New.Filling.amplitudeSum`: the sum of the amplitudes of the terms of a set over a block.
* `New.Filling.identitySecondMoment`, `New.Filling.mainSecondMoment`: the numbers `#R̄₀ · D_X` and
  `D_X² / (deg · mass)`, with `deg = S.besselDegree` and the mass `New.mass` of the genus of the
  standard lattice of rank `r`.

## Relation to the literature

For the normalised Poincaré map `P`, the mean over level translates `s` of `‖P* s P‖²` is at most
nearly `D_X² / D₀`, with `D₀` the expected dimension of the target, and bad types carry little of
`P`. In rank one, Poisson summation on a product of two Kloosterman sides with a sharp diagonal term
is known in the literature. Related work: Herman, Beyond endoscopy for the Rankin–Selberg
L-function, 2011; Iwaniec–Li, The orthogonality of Hecke eigenvalues, 2007;
Michel–Ramakrishnan–Yang, Bessel periods on U(2,1)×U(1,1), 2023.

See `New.Spanning.SecondMoment.SpanningTheorem` and `New.Spanning.RemainingTerms.Sum` for related
work.
-/

namespace New.Filling

/-!
## The operators `P_s` and `r_ψ(s)`, and the second moments

In statements about `P`, `ρ` is a representation of `Ḡ`, unitary where stated, on a space of finite
dimension.
-/

section Moments

open Matrix Complex Module InnerProductSpace EuclideanSpace Finset Fintype

attribute [local instance low] Fintype.ofFinite

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰} [ok : S.IsAdmissible]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- In a unitary representation `ρ` of a finite group, a central idempotent `z` of the group algebra
(an idempotent whose coefficients form a class function) acts as an orthogonal projection. -/
lemma _root_.New.IsCentralProj.isSymmetricProjection {H : Type} [Group H] [Fintype H]
    {ρ : Representation ℂ H V} (hρ : ∀ (s : H) (x y : V), ⟪ρ s x, ρ s y⟫_ℂ = ⟪x, y⟫_ℂ)
    {z : MonoidAlgebra ℂ H} (hz : IsCentralProj z) :
    (ρ.asAlgebraHom z).IsSymmetricProjection :=
  have h_idem : IsIdempotentElem z := hz.1
  ⟨h_idem.map ρ.asAlgebraHom, hz.self_adjoint ρ 1 (innerₛₗ ℂ) hρ⟩

open scoped Classical in
variable (S) in
/-- Let `Ḡ = S.ResidueGL` be the product of the general linear groups over the residue fields at the
chosen places of `S`. The source is the Euclidean space with coordinates `(c, i)`, where `c` is a
class (a double coset of the definite unitary group `U(X₀)` for the level) and `i` is a coordinate
of the Bessel function `W` at the infinite places. For a representation `ρ` of `Ḡ` on `V` and a
linear map `P` from the source to `V`, this says that the block `(c, c')` of `P_s = P* ρ(s) P` is
the complex conjugate of `A(c, s, c') / ν`. Here `ν = unipotentCovolume`, and
`A(c, s, c') = amplitudeSum .full .univ c s c'` is the sum of the amplitudes
`∫ β_c(y) β_c'(γ⁻¹ y) W(y) ⊗ W(γ⁻¹ y)^* dy` over all terms, the rational `γ` such that
`h_c⁻¹ γ h_c'` is integral with reduction `s`; `h_c` represents the class `c` and
`β_c = classCutoff c`. This holds for the Poincaré map after scaling. -/
def HasAmplitudeBlocks (ρ : Representation ℂ S.ResidueGL V)
    (P : EuclideanSpace ℂ (S.Classes × S.BesselCoord) →ₗ[ℂ] V) : Prop :=
  ∀ (s : S.ResidueGL) (x y : S.Classes × S.BesselCoord), ⟪ρ s (P (.single y 1)),
    P (.single x 1)⟫_ℂ =
    S.amplitudeSum .full .univ x.1 s y.1 (x.2, y.2) / S.unipotentCovolume

variable [FiniteDimensional ℂ V] {ρ : Representation ℂ S.ResidueGL V}
  {P : EuclideanSpace ℂ (S.Classes × S.BesselCoord) →ₗ[ℂ] V}

open scoped Classical in
omit ok [FiniteDimensional ℂ V] in
/-- Let `S` be filling data for a unitary group over the CM field `E`, and `Ḡ = S.ResidueGL` the
product of the general linear groups over the residue fields at the chosen places. Let `ρ` be a
representation of `Ḡ` on `V` and `P` a linear map to `V` from the Euclidean space with basis `e_x`,
where `x` is a pair of a class (a double coset of the definite unitary group `U(X₀)` for the level)
and a coordinate of the Bessel function `W` at the infinite places. Suppose that
`⟪ρ(s) P e_y, P e_x⟫` is `c > 0` times the entry of `amplitudeSum .full .univ`, the sum over all
rational terms of the amplitude integrals of the uncut function `W`. Then `(c ν) ^ (-1/2) P`
satisfies `HasAmplitudeBlocks`, the same identity with `ν⁻¹` in place of `c`, where
`ν = S.unipotentCovolume > 0`. -/
lemma hasAmplitudeBlocks_smul_of_inner_eq {c : ℝ} (hc : 0 < c)
    (hP : ∀ (s : S.ResidueGL) (x y : S.Classes × S.BesselCoord),
      ⟪ρ s (P (.single y 1)), P (.single x 1)⟫_ℂ =
        ofReal c * S.amplitudeSum .full .univ x.1 s y.1 (x.2, y.2)) :
    S.HasAmplitudeBlocks ρ (ofReal √(c * S.unipotentCovolume)⁻¹ • P) := by
  intro s x y
  have hν : 0 < S.unipotentCovolume := S.unipotentCovolume_pos
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, inner_smul_left, inner_smul_right,
    hP, conj_ofReal, ← mul_assoc, ← ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast
  field [ofReal_ne_zero.2 hc.ne']

omit ok in
/-- Let `S` be filling data (`Filling`) for a unitary group `G` over the CM field `E`, and let
`Ḡ = S.ResidueGL` be the product of the general linear groups over the residue fields at the chosen
places above the two level primes `p₀`, `p₁`. The source is the Euclidean space with coordinates
`(c, i)`, where `c` is a class (a double coset of the definite unitary group `U(X₀)` for the level)
and `i` is a coordinate of the Bessel function `W` at the infinite places. Let `ρ` be a
representation of `Ḡ` on `V` and `P` a linear map from the source to `V`. Suppose
`HasAmplitudeBlocks`: the block `(c, c')` of `P_s = P* ρ(s) P` is the conjugate of
`A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and `A(c, s, c')` is the sum, over the
rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with reduction `s`, of an integral of
`W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class `c`). Then the squared
Hilbert–Schmidt norm of `P_s` is `∑ ‖A(c, s, c')‖² / ν²` over pairs of classes, the second moment at
`s` of all terms (`.univ`) for the uncut function `W` (`.full`). -/
lemma HasAmplitudeBlocks.hilbertSchmidtNorm_sq_eq_secondMoment (hP : S.HasAmplitudeBlocks ρ P)
    (s : S.ResidueGL) :
    hilbertSchmidtNorm (P.adjoint ∘ₗ ρ s ∘ₗ P) ^ 2 =
      secondMoment (S.amplitudeSum .full .univ) {s} := by
  classical
  have h_entry (x y : S.Classes × S.BesselCoord) :
      ⟪(P.adjoint ∘ₗ ρ s ∘ₗ P) (.single y 1), .single x 1⟫_ℂ =
        S.amplitudeSum .full .univ x.1 s y.1 (x.2, y.2) / S.unipotentCovolume := by
    simpa [LinearMap.adjoint_inner_left] using hP s x y
  rw [hilbertSchmidtNorm_sq_eq_sum_entries (basisFun _ ℂ) (basisFun _ ℂ)]
  simp only [basisFun_apply, h_entry]
  simp [secondMoment, sum_filter, norm_sq_eq, sum_prod_type, sum_div, div_pow,
    sum_comm (α := S.Classes) (γ := S.BesselCoord)]

open scoped Classical in
variable (S) in
/-- The operator `r_ψ(s)` on the source: its blocks are the complex conjugates of the sums of
amplitudes (`amplitudeSum`) of the terms in the Bessel subgroup, divided by `unipotentCovolume`. For
`s` in the image `R̄₀` of the Bessel subgroup it is the translation by `s`, twisted by the
character: each class `c` has a term of the Bessel subgroup over some block `(c, s, c')`
(`exists_besselS_mem_termsOver`), its matrix is given by `besselFn_mul_of_eq_embedH`, and
`besselTranslate_apply` gives the value of the operator. -/
noncomputable def besselTranslate (s : S.ResidueGL) :
    EuclideanSpace ℂ (S.Classes × S.BesselCoord) →ₗ[ℂ]
      EuclideanSpace ℂ (S.Classes × S.BesselCoord) :=
  toEuclideanLin <| of fun x y ↦
    star (S.amplitudeSum .full (S.ratMiddle E).besselS x.1 s y.1 (x.2, y.2) / S.unipotentCovolume)

omit ok in
/-- The operator `r_ψ(s) = besselTranslate s`, whose blocks are sums over rational elements of the
Bessel subgroup with reduction `s`, vanishes for `s` off the image of that subgroup in
`S.ResidueGL`. -/
lemma besselTranslate_eq_zero {s : S.ResidueGL} (hs : s ∉ S.reducedImage besselS) :
    S.besselTranslate s = 0 := by
  ext φ x
  simp [besselTranslate, amplitudeSum_besselS_eq_zero hs, mulVec, dotProduct]

/-- Let `S` be admissible filling data for a unitary group `G` over the CM field `E`, which contains
a primitive `5040`-th root of unity, and let `Ḡ = S.ResidueGL` be the product of the general linear
groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`. Let
`r_ψ(s) = S.besselTranslate s` be the operator on the source `ℂ^(classes × Bessel coordinates)`
whose blocks are the complex conjugates of the normalised amplitude sums of the rational elements of
the Bessel subgroup `besselS`. Let `γ` be a rational element of that subgroup over the block
`(c, s, c')`: `h_c⁻¹ γ h_c'` is integral with reduction `s`, where `h_c` represents the class `c`.
Suppose `W(γ y) = M W(y)` for all points `y` of `G` at the infinite places, where
`W = S.besselFn .full` is the vector of Bessel functions. Then the value of `r_ψ(s) φ` at the class
`c` is the entrywise conjugate of `M` applied to the value of `φ` at `c'`. -/
lemma besselTranslate_apply [HasPrimitiveRoot5040 E] {γ : S.G E} {c c' : S.Classes}
    {s : S.ResidueGL} (hγ : γ ∈ besselS) (hγ_over : γ ∈ S.termsOver c s c')
    {M : Matrix S.BesselCoord S.BesselCoord ℂ}
    (hM : ∀ y : NumberField.InfinitePlace E → 𝔰.G₁,
      S.besselFn .full (S.ratToInf γ * y) = M *ᵥ S.besselFn .full y)
    (φ : EuclideanSpace ℂ (S.Classes × S.BesselCoord)) (i : S.BesselCoord) :
    S.besselTranslate s φ (c, i) = ∑ j : S.BesselCoord, star (M i j) * φ (c', j) := by
  classical
  simp [besselTranslate, mulVec, dotProduct, sum_prod_type,
    amplitudeSum_besselS_apply hγ hγ_over hM, apply_ite, ite_div, S.unipotentCovolume_pos.ne']

/-- For admissible filling data `S` over a CM field `E` with a primitive `5040`-th root of unity,
the operator `r_ψ(1) = besselTranslate 1` is the identity. -/
lemma besselTranslate_one [HasPrimitiveRoot5040 E] : S.besselTranslate 1 = 1 := by
  ext φ ⟨c, i⟩
  have h_over : (1 : S.G E) ∈ S.termsOver c 1 c := (S.classUnipotent c).one_mem.2
  rw [besselTranslate_apply (one_mem _) h_over (M := 1) (by simp)]
  simp [Matrix.one_apply, apply_ite]

/-- Let `S` be admissible filling data for a unitary group `G` over the CM field `E`, which contains
a primitive `5040`-th root of unity, and let `Ḡ = S.ResidueGL` be the product of the general linear
groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`. Then
`r_ψ(s t) = r_ψ(s) r_ψ(t)` for `s` and `t` in `R̄₀`. -/
lemma besselTranslate_mul [HasPrimitiveRoot5040 E] {s t : S.ResidueGL}
    (hs : s ∈ S.reducedImage besselS) (ht : t ∈ S.reducedImage besselS) :
    S.besselTranslate (s * t) = S.besselTranslate s * S.besselTranslate t := by
  -- If `γ` lies over `(c, s, c')` and `δ` over `(c', t, c'')`, then `γ δ` is over `(c, s t, c'')`.
  ext φ ⟨c, i⟩
  obtain ⟨c', γ, hγ, hγ_over⟩ := exists_besselS_mem_termsOver c hs
  obtain ⟨c'', δ, hδ, hδ_over⟩ := exists_besselS_mem_termsOver c' ht
  obtain ⟨M, -, hM⟩ := exists_unitary_besselFn_mul (side := .full) hγ
  obtain ⟨N, -, hN⟩ := exists_unitary_besselFn_mul (side := .full) hδ
  have hMN (y : NumberField.InfinitePlace E → 𝔰.G₁) :
      S.besselFn .full (S.ratToInf (γ * δ) * y) = (M * N) *ᵥ S.besselFn .full y := by
    rw [map_mul, mul_assoc, hM, hN, mulVec_mulVec]
  have h_matrix : S.besselTranslate (s * t) φ (c, i) =
      ∑ k : S.BesselCoord, star ((M * N) i k) * φ (c'', k) :=
    besselTranslate_apply (mul_mem hγ hδ) (termsOver.mul hγ_over hδ_over) hMN φ i
  rw [h_matrix, End.mul_apply, besselTranslate_apply hγ hγ_over hM]
  simp only [besselTranslate_apply hδ hδ_over hN, Matrix.mul_apply, star_sum, star_mul', sum_mul,
    mul_sum, mul_assoc]
  exact sum_comm

/-- Let `S` be admissible filling data for a unitary group `G` over the CM field `E`, which contains
a primitive `5040`-th root of unity, and let `Ḡ = S.ResidueGL` be the product of the general linear
groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`. Then
`r_ψ(t s) = r_ψ(t) r_ψ(s)` for `t` in `R̄₀` and every `s` in `Ḡ`. -/
lemma besselTranslate_mul_left [HasPrimitiveRoot5040 E] {t : S.ResidueGL}
    (ht : t ∈ S.reducedImage besselS) (s : S.ResidueGL) :
    S.besselTranslate (t * s) = S.besselTranslate t * S.besselTranslate s := by
  by_cases hs : s ∈ S.reducedImage besselS
  · exact besselTranslate_mul ht hs
  · rw [besselTranslate_eq_zero hs, mul_zero,
      besselTranslate_eq_zero (mt (mul_mem_cancel_left ht).1 hs)]

/-- Let `S` be admissible filling data over a CM field `E` with a primitive `5040`-th root of unity.
The adjoint of `r_ψ(s) = besselTranslate s` is `r_ψ(s⁻¹)`. So, by `besselTranslate_mul` and
`besselTranslate_one`, `r_ψ` is a unitary representation of the image of the Bessel subgroup. -/
lemma adjoint_besselTranslate [HasPrimitiveRoot5040 E] (s : S.ResidueGL) :
    (S.besselTranslate s).adjoint = S.besselTranslate s⁻¹ := by
  classical
  rw [besselTranslate, besselTranslate, ← toEuclideanLin_conjTranspose_eq_adjoint]
  congr 1
  ext x y
  -- The block at `(c', s⁻¹, c)` is the adjoint of that at `(c, s, c')`.
  simp [amplitudeSum_besselS_inv y.1 x.1 s]

/-- Let `S` be admissible filling data for a unitary group `G` over the CM field `E`, which contains
a primitive `5040`-th root of unity, and let `Ḡ = S.ResidueGL` be the product of the general linear
groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`. For `t`
in `R̄₀` the operator `r_ψ(t)` is unitary, so composing an operator `A` of the source on the left
with it does not change the Hilbert–Schmidt norm. -/
lemma hilbertSchmidtNorm_besselTranslate_comp [HasPrimitiveRoot5040 E] {t : S.ResidueGL}
    (ht : t ∈ S.reducedImage besselS)
    (A : EuclideanSpace ℂ (S.Classes × S.BesselCoord) →ₗ[ℂ]
      EuclideanSpace ℂ (S.Classes × S.BesselCoord)) :
    hilbertSchmidtNorm (S.besselTranslate t ∘ₗ A) = hilbertSchmidtNorm A := by
  have h_adjoint : (S.besselTranslate t).adjoint * S.besselTranslate t = 1 := by
    rw [adjoint_besselTranslate, ← besselTranslate_mul (inv_mem ht) ht, inv_mul_cancel,
      besselTranslate_one]
  have h_norm (x : EuclideanSpace ℂ (S.Classes × S.BesselCoord)) :
      ‖S.besselTranslate t x‖ = ‖x‖ := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), ← LinearMap.adjoint_inner_right, ← End.mul_apply,
      h_adjoint, End.one_apply, ← norm_eq_sqrt_re_inner]
  exact le_antisymm (hilbertSchmidtNorm_le_of_norm_le fun x ↦ (h_norm (A x)).le)
    (hilbertSchmidtNorm_le_of_norm_le fun x ↦ (h_norm (A x)).ge)

/-- Let `S` be admissible filling data over a CM field `E` with a primitive `5040`-th root of unity.
The trace of `r_ψ(s) = besselTranslate s` is a sum over classes `c` and Bessel coordinates `i`. Each
summand is the `(i, i)` entry of the full amplitude sum `amplitudeSum` of the terms in the Bessel
subgroup `besselS` over the block `(c, s⁻¹, c)`, divided by `unipotentCovolume`. -/
lemma trace_besselTranslate [HasPrimitiveRoot5040 E] (s : S.ResidueGL) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord)) (S.besselTranslate s) =
      ∑ y : S.Classes × S.BesselCoord,
        S.amplitudeSum .full (S.ratMiddle E).besselS y.1 s⁻¹ y.1 (y.2, y.2) /
          S.unipotentCovolume := by
  classical
  rw [LinearMap.trace_eq_sum_inner _ (basisFun _ ℂ)]
  simp [besselTranslate, inner_single_left, amplitudeSum_besselS_inv]

/-- Equivariance on the right. Let `S` be admissible filling data for a unitary group `G` over the
CM field `E`, which contains a primitive `5040`-th root of unity, and let `Ḡ = S.ResidueGL` be the
product of the general linear groups over the residue fields at the chosen places above the two
level primes `p₀`, `p₁`. The source is the Euclidean space with coordinates `(c, i)`, where `c` is a
class (a double coset of the definite unitary group `U(X₀)` for the level) and `i` is a coordinate
of the Bessel function `W` at the infinite places. Let `ρ` be a representation of `Ḡ` on `V` and `P`
a linear map from the source to `V`. Suppose `HasAmplitudeBlocks`: the block `(c, c')` of
`P_s = P* ρ(s) P` is the conjugate of `A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and
`A(c, s, c')` is the sum, over the rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with
reduction `s`, of an integral of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class
`c`). Let `r_ψ(s) = S.besselTranslate s` be the operator on the source with the same blocks, but
summed only over the `γ` in the Bessel subgroup `besselS` (block unitriangular elements times
`U(X₀)`), and let `R̄₀` be the image of that subgroup in `Ḡ`. Then `P_(s t) = P_s r_ψ(t)` for `t` in
`R̄₀`. -/
lemma HasAmplitudeBlocks.adjoint_comp_rep_mul_right [HasPrimitiveRoot5040 E]
    (hP : S.HasAmplitudeBlocks ρ P) (s : S.ResidueGL) {t : S.ResidueGL}
      (ht : t ∈ S.reducedImage besselS) :
    P.adjoint ∘ₗ ρ (s * t) ∘ₗ P = (P.adjoint ∘ₗ ρ s ∘ₗ P) ∘ₗ S.besselTranslate t := by
  classical
  refine (basisFun _ ℂ).toBasis.ext fun ⟨d, j⟩ ↦ ext_inner_right_basis (basisFun _ ℂ).toBasis ?_
  rintro ⟨c, i⟩
  -- A term `δ` of the Bessel subgroup over `(d, t⁻¹, d')` gives column `(d, j)` of `r_ψ(t)`.
  obtain ⟨d', δ, hδ, hδ_over⟩ := exists_besselS_mem_termsOver d (inv_mem ht)
  obtain ⟨N, -, hN⟩ := exists_unitary_besselFn_mul (side := .full) hδ
  have h_col : S.besselTranslate t (.single (d, j) 1) =
      ∑ k : S.BesselCoord, N j k • EuclideanSpace.single (d', k) 1 := by
    ext ⟨e, k⟩
    have h_block : starRingEnd ℂ (S.amplitudeSum .full (S.ratMiddle E).besselS e t d (k, j)) =
        if d' = e then S.unipotentCovolume * N j k else 0 := by
      rw [← Complex.star_def, ← amplitudeSum_besselS_inv, amplitudeSum_besselS_apply hδ hδ_over hN]
    by_cases h : d' = e
    · simp [besselTranslate, h_block, h, S.unipotentCovolume_pos.ne', Pi.single_apply]
    · simp [besselTranslate, h_block, h, Ne.symm h]
  -- The blocks of all terms transform in the same way, as the set of all terms is stable.
  have h_move : S.amplitudeSum .full .univ c (s * t) d (i, j) =
      ∑ k : S.BesselCoord, star (N j k) * S.amplitudeSum .full .univ c s d' (i, k) := by
    simpa using amplitudeSum_mul_inv_apply (by simp [IsStable] : S.IsStable Set.univ) hδ hδ_over
      (fun γ ↦ by simp) hN c s i j
  simp only [OrthonormalBasis.coe_toBasis, basisFun_apply]
  calc ⟪(P.adjoint ∘ₗ ρ (s * t) ∘ₗ P) (.single (d, j) 1), .single (c, i) 1⟫_ℂ
      = ∑ k : S.BesselCoord,
          star (N j k) * (S.amplitudeSum .full .univ c s d' (i, k) / S.unipotentCovolume) := by
        rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.comp_apply,
          hP (s * t) (c, i) (d, j), h_move, sum_div]
        simp only [mul_div_assoc]
    _ = ⟪((P.adjoint ∘ₗ ρ s ∘ₗ P) ∘ₗ S.besselTranslate t) (.single (d, j) 1),
          .single (c, i) 1⟫_ℂ := by
        simp only [LinearMap.comp_apply, h_col, map_sum, map_smul, sum_inner, inner_smul_left,
          LinearMap.adjoint_inner_left, hP s (c, i), Complex.star_def]

/-- Let `S` be admissible filling data for a unitary group `G` over the CM field `E`, which contains
a primitive `5040`-th root of unity, and let `Ḡ = S.ResidueGL` be the product of the general linear
groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`. The
source is the Euclidean space with coordinates `(c, i)`, where `c` is a class (a double coset of the
definite unitary group `U(X₀)` for the level) and `i` is a coordinate of the Bessel function `W` at
the infinite places. Let `ρ` be a unitary representation of `Ḡ` on `V` and `P` a linear map from the
source to `V`. Suppose `HasAmplitudeBlocks`: the block `(c, c')` of `P_s = P* ρ(s) P` is the
conjugate of `A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and `A(c, s, c')` is the sum,
over the rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with reduction `s`, of an integral
of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class `c`). Let
`r_ψ(s) = S.besselTranslate s` be the operator on the source with the same blocks, but summed only
over the `γ` in the Bessel subgroup `besselS` (block unitriangular elements times `U(X₀)`), and let
`R̄₀` be the image of that subgroup in `Ḡ`. Then `ρ(t) P = P r_ψ(t)` for `t` in `R̄₀`. -/
lemma HasAmplitudeBlocks.rep_comp_eq_comp_besselTranslate [HasPrimitiveRoot5040 E]
    (hP : S.HasAmplitudeBlocks ρ P)
    (hρ : ∀ (s : S.ResidueGL) (x y : V), ⟪ρ s x, ρ s y⟫_ℂ = ⟪x, y⟫_ℂ) {t : S.ResidueGL}
    (ht : t ∈ S.reducedImage besselS) :
    ρ t ∘ₗ P = P ∘ₗ S.besselTranslate t := by
  -- The difference `d` is orthogonal to all translates of the image of `P`, hence to itself.
  ext1 φ
  set d : V := ρ t (P φ) - P (S.besselTranslate t φ) with hd
  have h_orth (s : S.ResidueGL) (φ' : EuclideanSpace ℂ (S.Classes × S.BesselCoord)) :
      ⟪ρ s (P φ'), d⟫_ℂ = 0 := by
    have h_apply : P.adjoint (ρ (s⁻¹ * t) (P φ)) =
        P.adjoint (ρ s⁻¹ (P (S.besselTranslate t φ))) :=
      LinearMap.congr_fun (hP.adjoint_comp_rep_mul_right s⁻¹ ht) φ
    have h_zero : P.adjoint (ρ s⁻¹ d) = 0 := by
      rw [hd, map_sub, map_sub, ← h_apply, map_mul, End.mul_apply, sub_self]
    rw [← hρ s⁻¹, ρ.inv_self_apply, ← LinearMap.adjoint_inner_right, h_zero, inner_zero_right]
  have h_self : ⟪d, d⟫_ℂ = 0 := by
    calc ⟪d, d⟫_ℂ = ⟪ρ t (P φ), d⟫_ℂ - ⟪P (S.besselTranslate t φ), d⟫_ℂ := inner_sub_left ..
      _ = 0 := by simpa [h_orth t φ] using h_orth 1 (S.besselTranslate t φ)
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h_self)

/-- Equivariance on the left. Let `S` be admissible filling data for a unitary group `G` over the CM
field `E`, which contains a primitive `5040`-th root of unity, and let `Ḡ = S.ResidueGL` be the
product of the general linear groups over the residue fields at the chosen places above the two
level primes `p₀`, `p₁`. The source is the Euclidean space with coordinates `(c, i)`, where `c` is a
class (a double coset of the definite unitary group `U(X₀)` for the level) and `i` is a coordinate
of the Bessel function `W` at the infinite places. Let `ρ` be a unitary representation of `Ḡ` on `V`
and `P` a linear map from the source to `V`. Suppose `HasAmplitudeBlocks`: the block `(c, c')` of
`P_s = P* ρ(s) P` is the conjugate of `A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and
`A(c, s, c')` is the sum, over the rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with
reduction `s`, of an integral of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class
`c`). Let `r_ψ(s) = S.besselTranslate s` be the operator on the source with the same blocks, but
summed only over the `γ` in the Bessel subgroup `besselS` (block unitriangular elements times
`U(X₀)`), and let `R̄₀` be the image of that subgroup in `Ḡ`. Then `P_(t s) = r_ψ(t) P_s` for `t` in
`R̄₀`. -/
lemma HasAmplitudeBlocks.adjoint_comp_rep_mul_left [HasPrimitiveRoot5040 E]
    (hP : S.HasAmplitudeBlocks ρ P)
    (hρ : ∀ (s : S.ResidueGL) (x y : V), ⟪ρ s x, ρ s y⟫_ℂ = ⟪x, y⟫_ℂ) (s : S.ResidueGL)
    {t : S.ResidueGL} (ht : t ∈ S.reducedImage besselS) :
    P.adjoint ∘ₗ ρ (t * s) ∘ₗ P = S.besselTranslate t ∘ₗ (P.adjoint ∘ₗ ρ s ∘ₗ P) := by
  -- The adjoint of `t⁻¹ P = P r_ψ(t⁻¹)` is `P* t = r_ψ(t) P*`.
  have h_adjoint : P.adjoint ∘ₗ ρ t = S.besselTranslate t ∘ₗ P.adjoint := by
    simpa [LinearMap.adjoint_comp, adjoint_rep_of_unitary hρ, adjoint_besselTranslate] using
      congrArg LinearMap.adjoint (hP.rep_comp_eq_comp_besselTranslate hρ (inv_mem ht))
  rw [map_mul, End.mul_eq_comp, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc, h_adjoint]
  simp only [LinearMap.comp_assoc]

/-- Let `S` be admissible filling data for a unitary group `G` over the CM field `E`, which contains
a primitive `5040`-th root of unity, and let `Ḡ = S.ResidueGL` be the product of the general linear
groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`. The
source is the Euclidean space with coordinates `(c, i)`. Suppose `HasAmplitudeBlocks`: the block
`(c, c')` of `P_s = P* ρ(s) P` is the conjugate of `A(c, s, c') / ν`, where
`ν = S.unipotentCovolume > 0` and `A(c, s, c')` is the sum, over the rational `γ` in `G` such that
`h_c⁻¹ γ h_c'` is integral with reduction `s`, of an integral of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs
(`h_c` represents the class `c`). Then the squared Hilbert–Schmidt norm of `P_s - r_ψ(s)` is the
second moment `∑ ‖A'(c, s, c')‖² / ν²` over pairs of classes, where `A'` is summed over the `γ`
outside the Bessel subgroup and `‖·‖` is the Euclidean norm of the entries. -/
lemma HasAmplitudeBlocks.hilbertSchmidtNorm_sub_besselTranslate_sq [HasPrimitiveRoot5040 E]
    (hP : S.HasAmplitudeBlocks ρ P) (s : S.ResidueGL) :
    hilbertSchmidtNorm (P.adjoint ∘ₗ ρ s ∘ₗ P - S.besselTranslate s) ^ 2 =
      secondMoment (S.amplitudeSum .full (S.ratMiddle E).besselSᶜ) {s} := by
  classical
  have h_entry (x y : S.Classes × S.BesselCoord) :
      ⟪(P.adjoint ∘ₗ ρ s ∘ₗ P - S.besselTranslate s) (.single y 1), .single x 1⟫_ℂ =
        S.amplitudeSum .full (S.ratMiddle E).besselSᶜ x.1 s y.1 (x.2, y.2) /
          S.unipotentCovolume := by
    rw [LinearMap.sub_apply, inner_sub_left, LinearMap.comp_apply, LinearMap.adjoint_inner_left,
      LinearMap.comp_apply, hP s x y, amplitudeSum_eq_inter_compl_add_inter Set.univ
        (S.ratMiddle E).besselS]
    simp [besselTranslate, inner_single_right, add_div]
  calc hilbertSchmidtNorm (P.adjoint ∘ₗ ρ s ∘ₗ P - S.besselTranslate s) ^ 2
    _ = ∑ x : S.Classes × S.BesselCoord, ∑ y : S.Classes × S.BesselCoord,
        ‖S.amplitudeSum .full (S.ratMiddle E).besselSᶜ x.1 s y.1 (x.2, y.2) / S.unipotentCovolume‖ ^
          2 :=
      by
        simp only [hilbertSchmidtNorm_sq_eq_sum_entries (basisFun _ ℂ) (basisFun _ ℂ),
          basisFun_apply, h_entry]
    _ = secondMoment (S.amplitudeSum .full (S.ratMiddle E).besselSᶜ) {s} := by
      simp [secondMoment, sum_filter, norm_sq_eq, sum_prod_type, sum_div, div_pow,
        sum_comm (α := S.Classes) (γ := S.BesselCoord)]

open scoped Classical in
/-- **Second moment near the Bessel subgroup.** Let `S` be admissible filling data for a unitary
group `G` over the CM field `E`, which contains a primitive `5040`-th root of unity, and let
`Ḡ = S.ResidueGL` be the product of the general linear groups over the residue fields at the chosen
places above the two level primes `p₀`, `p₁`. The source is the Euclidean space with coordinates
`(c, i)`, where `c` is a class (a double coset of the definite unitary group `U(X₀)` for the level)
and `i` is a coordinate of the Bessel function `W` at the infinite places. Let `ρ` be a
representation of `Ḡ` on `V` and `P` a linear map from the source to `V`. Suppose
`HasAmplitudeBlocks`: the block `(c, c')` of `P_s = P* ρ(s) P` is the conjugate of
`A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and `A(c, s, c')` is the sum, over the
rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with reduction `s`, of an integral of
`W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class `c`). Let
`r_ψ(s) = S.besselTranslate s` be the operator on the source with the same blocks, but summed only
over the `γ` in the Bessel subgroup `besselS` (block unitriangular elements times `U(X₀)`), and let
`R̄₀` be the image of that subgroup in `Ḡ`. Then `∑ ‖P_s - r_ψ(s)‖² ≤ b⁻¹² 𝒟_id` in Hilbert–Schmidt
norm, the sum being over the `s` that coincide with an element of `R̄₀` above the prime `p_(i+1)`
other than `p_i`. Here `b = S.b ≥ 1000` is the size parameter of `S`, and
`𝒟_id = S.identitySecondMoment` is `#R̄₀` times the dimension of the source. -/
theorem HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sub_besselTranslate_sq_le [HasPrimitiveRoot5040 E]
    (hP : S.HasAmplitudeBlocks ρ P) (i : Fin 2) :
    ∑ s : S.ResidueGL with ∃ t ∈ S.reducedImage besselS, s (i + 1) = t (i + 1),
      hilbertSchmidtNorm (P.adjoint ∘ₗ ρ s ∘ₗ P - S.besselTranslate s) ^ 2 ≤
      (S.b ^ 12)⁻¹ * S.identitySecondMoment := by
  simp only [hP.hilbertSchmidtNorm_sub_besselTranslate_sq]
  exact (secondMoment_eq_sum_secondMoment_singleton _
    {s | ∃ t ∈ S.reducedImage besselS, s (i + 1) = t (i + 1)}).symm.trans_le
      (secondMoment_compl_besselS_le (i + 1))

omit ok in
open scoped Classical in
/-- If `#R̄₀ · y ≤ b⁻¹² 𝒟_id`, then `y ≤ b⁻¹² D_X`. Here `R̄₀` is the image of the Bessel subgroup
in `S.ResidueGL`, `b = S.b`, `D_X = sourceDim` and `𝒟_id = identitySecondMoment = #R̄₀ · D_X`. -/
lemma le_sourceDim_div_of_card_nsmul_le {y : ℝ}
    (h_le : #{s : S.ResidueGL | s ∈ S.reducedImage besselS} • y ≤
      (S.b ^ 12)⁻¹ * S.identitySecondMoment) :
    y ≤ S.sourceDim / S.b ^ 12 := by
  rw [identitySecondMoment, nsmul_eq_mul, ← Fintype.card_subtype, card_eq_nat_card, mul_left_comm,
    ← div_eq_inv_mul] at h_le
  exact le_of_mul_le_mul_left h_le (Nat.cast_pos.2 Nat.card_pos)

/-- **Near isometry.** Let `S` be admissible filling data for a unitary group `G` over the CM field
`E`, which contains a primitive `5040`-th root of unity, and let `Ḡ = S.ResidueGL` be the product of
the general linear groups over the residue fields at the chosen places above the two level primes
`p₀`, `p₁`. The source is the Euclidean space with coordinates `(c, i)`, where `c` is a class (a
double coset of the definite unitary group `U(X₀)` for the level) and `i` is a coordinate of the
Bessel function `W` at the infinite places. Let `ρ` be a representation of `Ḡ` on `V` and `P` a
linear map from the source to `V`. Suppose `HasAmplitudeBlocks`: the block `(c, c')` of
`P_s = P* ρ(s) P` is the conjugate of `A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and
`A(c, s, c')` is the sum, over the rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with
reduction `s`, of an integral of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class
`c`). Then `‖P* P - 1‖² ≤ b⁻¹² D_X` in Hilbert–Schmidt norm, where `D_X = S.sourceDim` is the
dimension of the source and `b = S.b ≥ 1000` is the size parameter of `S`. -/
theorem HasAmplitudeBlocks.hilbertSchmidtNorm_sub_one_sq_le [HasPrimitiveRoot5040 E]
    (hP : S.HasAmplitudeBlocks ρ P) :
    hilbertSchmidtNorm (P.adjoint ∘ₗ P - 1) ^ 2 ≤ S.sourceDim / S.b ^ 12 := by
  classical
  -- For `s ∈ R̄₀` we have `P_s - r_ψ(s) = (P* P - 1) r_ψ(s)`, which has the norm of `P* P - 1`.
  set D : End ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord)) := P.adjoint ∘ₗ P - 1 with hD
  have h_eq (s : S.ResidueGL) (hs : s ∈ S.reducedImage besselS) :
      hilbertSchmidtNorm D = hilbertSchmidtNorm (P.adjoint ∘ₗ ρ s ∘ₗ P - S.besselTranslate s) := by
    have h_right : P.adjoint ∘ₗ ρ s ∘ₗ P = (P.adjoint ∘ₗ P) ∘ₗ S.besselTranslate s := by
      simpa [End.one_eq_id] using hP.adjoint_comp_rep_mul_right 1 hs
    calc hilbertSchmidtNorm D
      _ = hilbertSchmidtNorm (S.besselTranslate s⁻¹ ∘ₗ D.adjoint) := by
        rw [hilbertSchmidtNorm_besselTranslate_comp (inv_mem hs), hilbertSchmidtNorm_adjoint]
      _ = hilbertSchmidtNorm (D ∘ₗ S.besselTranslate s) := by
        rw [← adjoint_besselTranslate, ← LinearMap.adjoint_comp, hilbertSchmidtNorm_adjoint]
      _ = hilbertSchmidtNorm (P.adjoint ∘ₗ ρ s ∘ₗ P - S.besselTranslate s) := by
        rw [h_right, hD, LinearMap.sub_comp, End.one_eq_id, LinearMap.id_comp]
  refine le_sourceDim_div_of_card_nsmul_le ?_
  calc #{s : S.ResidueGL | s ∈ S.reducedImage besselS} • hilbertSchmidtNorm D ^ 2
    _ ≤ ∑ s with s ∈ S.reducedImage besselS,
        hilbertSchmidtNorm (P.adjoint ∘ₗ ρ s ∘ₗ P - S.besselTranslate s) ^ 2 :=
      card_nsmul_le_sum _ _ _ fun s hs ↦ by rw [h_eq s (mem_filter.1 hs).2]
    _ ≤ ∑ s with ∃ t ∈ S.reducedImage besselS, s (0 + 1) = t (0 + 1),
        hilbertSchmidtNorm (P.adjoint ∘ₗ ρ s ∘ₗ P - S.besselTranslate s) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (monotone_filter_right _ fun s _ hs ↦ ⟨s, hs, rfl⟩)
        fun s _ _ ↦ sq_nonneg _
    _ ≤ (S.b ^ 12)⁻¹ * S.identitySecondMoment :=
      hP.sum_hilbertSchmidtNorm_sub_besselTranslate_sq_le 0

omit ok in
/-- The identity of the source has squared Hilbert–Schmidt norm `D_X = sourceDim`. -/
lemma hilbertSchmidtNorm_one_sq_eq_sourceDim :
    hilbertSchmidtNorm (1 : End ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord))) ^ 2 =
      S.sourceDim := by
  classical
  simp [hilbertSchmidtNorm_sq_eq_sum (basisFun _ ℂ), sourceDim]

/-- Let `S` be admissible filling data (`Filling`, `IsAdmissible`) for a unitary group `G` over the
CM field `E`, which contains a primitive `5040`-th root of unity, and let `Ḡ = S.ResidueGL` be the
product of the general linear groups over the residue fields at the chosen places above the two
level primes `p₀`, `p₁`. The source is the Euclidean space with coordinates `(c, i)`, where `c` is a
class (a double coset of the definite unitary group `U(X₀)` for the level) and `i` is a coordinate
of the Bessel function `W` at the infinite places. Let `ρ` be a representation of `Ḡ` on `V` and `P`
a linear map from the source to `V`. Suppose `HasAmplitudeBlocks`: the block `(c, c')` of
`P_s = P* ρ(s) P` is the conjugate of `A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and
`A(c, s, c')` is the sum, over the rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with
reduction `s`, of an integral of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class
`c`). Then `‖P* P‖² ≤ 2 D_X` in Hilbert–Schmidt norm, where `D_X = S.sourceDim` is the dimension of
the source. -/
lemma HasAmplitudeBlocks.hilbertSchmidtNorm_adjoint_comp_sq_le [HasPrimitiveRoot5040 E]
    (hP : S.HasAmplitudeBlocks ρ P) :
    hilbertSchmidtNorm (P.adjoint ∘ₗ P) ^ 2 ≤ 2 * S.sourceDim := by
  -- `‖P* P‖ ≤ ‖P* P - 1‖ + ‖1‖ ≤ (1/3 + 1) ‖1‖`
  have hb : 1000 ≤ S.b := S.thousand_le_b
  set one : End ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord)) := 1
  have h_triangle : hilbertSchmidtNorm (P.adjoint ∘ₗ P) ≤ hilbertSchmidtNorm (P.adjoint ∘ₗ P - one)
    + hilbertSchmidtNorm one := by
    simpa [hilbertSchmidtNorm] using norm_add_le (hilbertSchmidtVector (P.adjoint ∘ₗ P - one))
      (hilbertSchmidtVector one)
  have h_near : hilbertSchmidtNorm (P.adjoint ∘ₗ P - one) ≤ hilbertSchmidtNorm one / 3 := by
    have h_sq : hilbertSchmidtNorm (P.adjoint ∘ₗ P - one) ^ 2 ≤ (hilbertSchmidtNorm one / 3) ^
      2 := by
      grw [hP.hilbertSchmidtNorm_sub_one_sq_le, div_pow, hilbertSchmidtNorm_one_sq_eq_sourceDim,
        ← hb]
      gcongr
      norm_num
    exact (abs_le_of_sq_le_sq' h_sq (div_nonneg (hilbertSchmidtNorm_nonneg _) zero_le_three)).2
  have h_le : hilbertSchmidtNorm (P.adjoint ∘ₗ P) ≤ 4 / 3 * hilbertSchmidtNorm one := by linarith
  rw [← hilbertSchmidtNorm_one_sq_eq_sourceDim]
  nlinarith [hilbertSchmidtNorm_nonneg (P.adjoint ∘ₗ P), hilbertSchmidtNorm_nonneg one]

/-- **Second moment.** Let `S` be admissible filling data (`Filling`, `IsAdmissible`) for a unitary
group `G` over the CM field `E`, which carries Weil data (a primitive `5040`-th root of unity and a
splitting character, see `WeilData`), and let `Ḡ = S.ResidueGL` be the product of the general linear
groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`. The
source is the Euclidean space with coordinates `(c, i)`, where `c` is a class (a double coset of the
definite unitary group `U(X₀)` for the level) and `i` is a coordinate of the Bessel function `W` at
the infinite places. Let `ρ` be a unitary representation of `Ḡ` on `V` and `P` a linear map from the
source to `V`. Suppose `HasAmplitudeBlocks`: the block `(c, c')` of `P_s = P* ρ(s) P` is the
conjugate of `A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and `A(c, s, c')` is the sum,
over the rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with reduction `s`, of an integral
of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class `c`). Then
`∑ ‖P_s‖² ≤ (1 + 9 b⁻⁴) 𝒟_main` in Hilbert–Schmidt norm, the sum being over all `s` in `Ḡ`. Here
`b = S.b ≥ 1000` is the size parameter of `S`, and `𝒟_main = S.mainSecondMoment` is the square of
the dimension of the source divided by the product of `S.besselDegree` (the product of the degree
constants of the local Bessel systems) and `New.mass` (the sum of `1 / #Aut` over the genus of the
standard lattice). -/
theorem HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sq_le [WeilData E] (hP : S.HasAmplitudeBlocks ρ P)
    (hρ : ∀ (s : S.ResidueGL) (x y : V), ⟪ρ s x, ρ s y⟫_ℂ = ⟪x, y⟫_ℂ) :
    ∑ s : S.ResidueGL, hilbertSchmidtNorm (P.adjoint ∘ₗ ρ s ∘ₗ P) ^ 2 ≤
      (1 + 9 / S.b ^ 4) * S.mainSecondMoment := by
  -- `s ↦ ‖P_s‖²` has positive type and `‖P_1‖² ≤ 2 D_X`, so `sum_secondMoment_le` applies.
  have h_gram (s t : S.ResidueGL) : ⟪hilbertSchmidtVector ((ρ s ∘ₗ P) ∘ₗ (ρ s ∘ₗ P).adjoint),
      hilbertSchmidtVector ((ρ t ∘ₗ P) ∘ₗ (ρ t ∘ₗ P).adjoint)⟫_ℂ =
        (secondMoment (S.amplitudeSum .full .univ) {s⁻¹ * t} : ℝ) := by
    rw [inner_hilbertSchmidtVector_translate hρ, hP.hilbertSchmidtNorm_sq_eq_secondMoment]
  have h_one : secondMoment (S.amplitudeSum .full .univ) {1} ≤ 2 * S.sourceDim := by
    rw [← hP.hilbertSchmidtNorm_sq_eq_secondMoment, map_one, End.one_eq_id (M := V),
      LinearMap.id_comp]
    exact hP.hilbertSchmidtNorm_adjoint_comp_sq_le
  simpa [hP.hilbertSchmidtNorm_sq_eq_secondMoment] using sum_secondMoment_le _ h_gram h_one

/-! ## Good forms: the remainder -/

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
open scoped Classical in
omit ok in
/-- **The remainder.** Let `S` be admissible filling data (`Filling`, `IsAdmissible`) for a unitary
group `G` over the CM field `E`, which contains a primitive `5040`-th root of unity, and let
`Ḡ = S.ResidueGL` be the product of the general linear groups over the residue fields at the chosen
places above the two level primes `p₀`, `p₁`. The source is the Euclidean space with coordinates
`(c, i)`, where `c` is a class (a double coset of the definite unitary group `U(X₀)` for the level)
and `i` is a coordinate of the Bessel function `W` at the infinite places. Let `ρ` be a unitary
representation of `Ḡ` on `V` and `P` a linear map from the source to `V`. Suppose
`HasAmplitudeBlocks`: the block `(c, c')` of `P_s = P* ρ(s) P` is the conjugate of
`A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and `A(c, s, c')` is the sum, over the
rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with reduction `s`, of an integral of
`W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class `c`). Let
`r_ψ(s) = S.besselTranslate s` be the operator on the source with the same blocks, but summed only
over the `γ` in the Bessel subgroup `besselS` (block unitriangular elements times `U(X₀)`). Write
`Ḡ = G_0 × G_1`, where `G_i` is the factor above `p_i`, made of matrices indexed by the basis
`𝔰.BesselIndex` of the hermitian space of shape `𝔰`, and embedded by `Pi.mulSingle i`. Then for a
central idempotent `x = ∑ x(t) t` of `ℂ[G_i]` (an idempotent whose coefficients form a class
function; it is then self-adjoint) we have `‖∑ x(t) (P_t - r_ψ(t))‖² ≤ b⁻¹² D_X` in Hilbert–Schmidt
norm, the sum being over `t` in `G_i`. Here `b = S.b ≥ 1000` is the size parameter of `S` and
`D_X = S.sourceDim` is the dimension of the source. -/
lemma HasAmplitudeBlocks.hilbertSchmidtNorm_sum_smul_sub_besselTranslate_sq_le [S.IsAdmissible]
    [HasPrimitiveRoot5040 E] {ρ : Representation ℂ S.ResidueGL V}
    {P : EuclideanSpace ℂ (S.Classes × S.BesselCoord) →ₗ[ℂ] V} (hP : S.HasAmplitudeBlocks ρ P)
    (hρ : ∀ (s : S.ResidueGL) (v v' : V), ⟪ρ s v, ρ s v'⟫_ℂ = ⟪v, v'⟫_ℂ) (i : Fin 2)
    {x : MonoidAlgebra ℂ (∀ w : S.chosenPlaces i, GL 𝔰.BesselIndex (ResField w.val))}
    (hx : IsCentralProj x) :
    hilbertSchmidtNorm (∑ t : ∀ w : S.chosenPlaces i, GL 𝔰.BesselIndex (ResField w.val),
        x.coeff t •
          (P.adjoint ∘ₗ ρ (Pi.mulSingle i t) ∘ₗ P - S.besselTranslate (Pi.mulSingle i t))) ^ 2 ≤
      S.sourceDim / S.b ^ 12 := by
  -- Put `P'_s = P_s - r_ψ(s)` and `P'_x = ∑ x(t) P'_t`. The map `f ↦ ∑ x(t) f(· t)` is a
  -- contraction on functions on the group. Apply it to `P'` cut down to `Ω = R̄₀ G_i`, where `R̄₀`
  -- is the image of the Bessel subgroup; the value at `s ∈ R̄₀` is `r_ψ(s) P'_x`, which has the
  -- norm of `P'_x`.
  let G (j : Fin 2) : Type := ∀ w : S.chosenPlaces j, GL 𝔰.BesselIndex (ResField w.val)
  let φ : G i →* S.ResidueGL := MonoidHom.mulSingle G i
  let P' (s : S.ResidueGL) : End ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord)) :=
    P.adjoint ∘ₗ ρ s ∘ₗ P - S.besselTranslate s
  let Ω : Set S.ResidueGL := {s | ∃ r ∈ S.reducedImage besselS, s (i + 1) = r (i + 1)}
  -- `f` is `P'` cut down to `Ω`, with values in the Hilbert space of operators.
  let f (s : S.ResidueGL) :
      PiLp 2 fun _ : Fin (finrank ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord))) ↦
        EuclideanSpace ℂ (S.Classes × S.BesselCoord) :=
    if s ∈ Ω then hilbertSchmidtVector (P' s) else 0
  have h_left {s : S.ResidueGL} (hs : s ∈ S.reducedImage besselS) (u : S.ResidueGL) :
      P' (s * u) = S.besselTranslate s ∘ₗ P' u := by
    simp only [P', hP.adjoint_comp_rep_mul_left hρ u hs, besselTranslate_mul_left hs,
      LinearMap.comp_sub, End.mul_eq_comp]
  have h_value {s : S.ResidueGL} (hs : s ∈ S.reducedImage besselS) :
      ‖∑ t : G i, x.coeff t • f (s * φ t)‖ = hilbertSchmidtNorm
        (∑ t : G i, x.coeff t • P' (φ t)) := by
    -- `φ t` is trivial above the other prime, so `s * φ t` lies in `Ω`.
    have h_mem (t : G i) : s * φ t ∈ Ω := ⟨s, hs, by simp [φ]⟩
    have h_sum : ∑ t : G i, x.coeff t • f (s * φ t) =
        hilbertSchmidtVector (S.besselTranslate s ∘ₗ ∑ t : G i, x.coeff t • P' (φ t)) := by
      simp only [f, h_mem, ite_true, h_left hs, ← End.mul_eq_comp, mul_sum, mul_smul_comm, map_sum,
        map_smul]
    rw [h_sum, ← hilbertSchmidtNorm, hilbertSchmidtNorm_besselTranslate_comp hs]
  have h_conv : ∑ s : S.ResidueGL, ‖∑ t : G i, x.coeff t • f (s * φ t)‖ ^ 2 ≤
      ∑ s : S.ResidueGL, ‖f s‖ ^ 2 := by
    calc ∑ s : S.ResidueGL, ‖∑ t : G i, x.coeff t • f (s * φ t)‖ ^ 2
      _ = ∑ s : S.ResidueGL, ‖∑ t : G i, x.coeff t • f ((φ t)⁻¹ * s)⁻¹‖ ^ 2 := by
        rw [← Equiv.sum_comp (Equiv.inv S.ResidueGL)]
        simp
      _ ≤ ∑ s : S.ResidueGL, ‖f s⁻¹‖ ^ 2 := hx.sum_norm_sq_conv_le φ fun s ↦ f s⁻¹
      _ = ∑ s : S.ResidueGL, ‖f s‖ ^ 2 := Equiv.sum_comp (Equiv.inv S.ResidueGL) fun s ↦ ‖f s‖ ^ 2
  refine le_sourceDim_div_of_card_nsmul_le ?_
  calc #{s : S.ResidueGL | s ∈ S.reducedImage besselS} • hilbertSchmidtNorm
         (∑ t : G i, x.coeff t • P' (φ t)) ^ 2
    _ ≤ ∑ s : S.ResidueGL with s ∈ S.reducedImage besselS, ‖∑ t : G i,
      x.coeff t • f (s * φ t)‖ ^ 2 :=
      card_nsmul_le_sum _ _ _ fun s hs ↦ by rw [h_value (mem_filter.1 hs).2]
    _ ≤ ∑ s : S.ResidueGL, ‖∑ t : G i, x.coeff t • f (s * φ t)‖ ^ 2 := by grw [← subset_univ]
    _ ≤ ∑ s : S.ResidueGL, ‖f s‖ ^ 2 := h_conv
    _ = ∑ s : S.ResidueGL with s ∈ Ω, hilbertSchmidtNorm (P' s) ^ 2 := by
      simp [f, sum_filter, apply_ite (‖·‖), ite_pow, hilbertSchmidtNorm]
    _ ≤ (S.b ^ 12)⁻¹ * S.identitySecondMoment :=
      hP.sum_hilbertSchmidtNorm_sub_besselTranslate_sq_le i

end Moments

/-! ## Good forms: the trace of `r_ψ` against a central idempotent of one factor -/

section BesselTrace

open NumberField Pi MeasureTheory Floors IntegralPlace Finset ENNReal Complex
open scoped Classical

open scoped BigOperators

variable {E : Type} [Field E] [CMType E] [WeilData E] {𝔰 : Shape}
  (S : Filling E 𝔰) [ok : S.IsAdmissible]

/-- For a finite group `G` and a central idempotent `x` of the complex group algebra
`MonoidAlgebra ℂ G` (`IsCentralProj x`), `∑ s, ‖x.coeff s‖² = (x.coeff 1).re`. -/
lemma sum_norm_sq_coeff_of_isCentralProj {G : Type*} [Group G] [Fintype G] {x : MonoidAlgebra ℂ G}
    (hx : IsCentralProj x) :
    ∑ s : G, ‖x.coeff s‖ ^ 2 = (x.coeff 1).re := by
  -- `x s⁻¹ = conj (x s)` as `|G| x` is a character; compare the coefficients of `1` in `x * x = x`.
  have h_inv (s : G) : x.coeff s⁻¹ = starRingEnd ℂ (x.coeff s) := by
    simpa using hx.isChar_card_mul_coeff.apply_inv s
  simpa [h_inv, x.coeff_mul_apply_left, Complex.sq_norm, Finsupp.sum_fintype, mul_conj] using
    congr_arg (fun y ↦ (y.coeff 1).re) hx.1

/-- Let `S` be admissible filling data over a CM field `E` with Weil data. Let `γ` be in the Bessel
subgroup and `k = translateByClassReps c c γ`, that is `h_c⁻¹ γ h_c` for the representative `h_c` of
the class `c`. If `k` lies in the stabilizer `latticeStabilizer` of the lattice and reduces to `1`
at the chosen places above the level prime `p_j`, then `k` lies in the unipotent subgroup
`besselU`. -/
lemma mem_besselU_of_reduction_eq_one {c : S.Classes} {γ : S.G E} {j : Fin 2}
    {k : S.latticeStabilizer}
    (hγ : γ ∈ (S.ratMiddle E).besselS) (hk : k.val = S.translateByClassReps c c γ)
    (hk_red : S.reduction k j = 1) :
    k.val ∈ (S.latticeMiddle (𝔸f E)).besselU := by
  -- Write `γ = u δ` with `u` unipotent and `δ` in `U(X₀)`; then `k = u' y` with `y = h_c⁻¹ δ h_c`
  -- and `u'` unipotent. It remains to see that `δ = 1`.
  obtain ⟨u, hu, δ, rfl⟩ : ∃ u ∈ besselU, ∃ g : U 1, γ = u * toBesselH 𝔰 (S.N : E) g :=
    exists_besselU_mul_toBesselH hγ S.isUnit_natCast_N
  let y : Gf E 𝔰.κ := c.out⁻¹ * stdEmbFin δ * c.out
  have hy : k * (S.inclHFin y)⁻¹ ∈ besselU := by
    simpa [y, hk, translateByClassReps, ratToFin_toBesselH, mul_assoc] using
      hu.translateByClassReps_mem_besselU c
  -- The `H`-part of an integral element of `𝖴 H` is integral.
  have hyK : S.inclHFin y ∈ S.latticeStabilizer :=
    (mem_unitaryLevel_of_besselU_mul hy (inclHFin_mem_besselH y)
      (unitaryLevel_one.ge (by simpa [latticeStabilizer] using k.prop))).1
  -- Each entry of `y` is the entry of `k` or of `1`, so `y` reduces to `1` where `k` does.
  have h_red (w : S.chosenPlaces j) : S.reduction ⟨S.inclHFin y, hyK⟩ j w = 1 := by
    ext a b
    rcases besselH_apply_eq_or hy (inclHFin_mem_besselH y) a b with h_entry | h_entry
    · rw [reduction_apply_congr k j w (by simpa using h_entry), hk_red, one_apply]
    · rw [reduction_apply_congr 1 j w h_entry, map_one, one_apply, one_apply]
  -- Freeness: a rational `δ` whose conjugate `y` is integral and reduces to `1` is `1`.
  obtain rfl := eq_one_of_reduceAt_eq_one le_rfl j _ fun w ↦
    (S.reduction_inclHFin_eq_one_iff hyK j w).mp (h_red w)
  -- Now `δ = 1`, hence `y = 1` and `k = k y⁻¹`.
  simpa [y] using hy

/-- The character `ψ_U` on the image `Ū₀` of the integral unipotent elements in the finite group
`S.ResidueGL`, extended by `0`. Its value at `s` is `S.unipotentChar k` for a unipotent `k` that
reduces to `s`; the choice does not matter (`extendedBesselChar_toPlaces_eq_reducedChar`). -/
noncomputable def reducedChar (s : S.ResidueGL) : ℂ :=
  if h : ∃ k : S.latticeStabilizer, k.val ∈ (S.latticeMiddle (𝔸f E)).besselU ∧ S.reduction k = s
    then
    S.unipotentChar h.choose
  else
    0

/-- The mean `ψ_U^♮(s)` of `ψ_U = reducedChar`, extended by `0`, over the conjugates of `s` in the
finite group `S.ResidueGL`. -/
noncomputable def reducedCharMean (s : S.ResidueGL) : ℂ := 𝔼 g : S.ResidueGL,
  S.reducedChar (g * s * g⁻¹)

omit ok [WeilData E] in
/-- The mean `ψ_U^♮` of `ψ_U` over conjugates is a class function. -/
lemma reducedCharMean_conj (g s : S.ResidueGL) :
    S.reducedCharMean (g * s * g⁻¹) = S.reducedCharMean s :=
  expect_equiv (.mulRight g) (by simp) fun t _ ↦ by simp [mul_assoc]

/-- Let `S` be admissible filling data over a CM field `E` with Weil data, and let `s` in
`S.ResidueGL` be `1` above the level prime `p_j`. The trace of `r_ψ(s) = S.besselTranslate s`, the
translation of the source by `s` twisted by the Bessel character, is `D_X ψ_U(s)`. Here
`D_X = S.sourceDim` and `ψ_U = S.reducedChar` is the character of the integral unipotent group, read
on reductions and extended by `0` off its image. -/
lemma trace_besselTranslate_eq_mul_reducedChar {j : Fin 2} {s : S.ResidueGL} (hs : s j = 1) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord)) (S.besselTranslate s) =
      S.sourceDim * S.reducedChar s := by
  rw [trace_besselTranslate, reducedChar]
  split_ifs with h
  · -- If `s` is the reduction of a unipotent `k`, the block at `s⁻¹` is `ψ_U(k)` times the block at
    -- `1`, which is the covolume times the identity.
    obtain ⟨hk_unip, hk_red⟩ :
        h.choose.val ∈ (S.latticeMiddle (𝔸f E)).besselU ∧ S.reduction h.choose = s := h.choose_spec
    have h_move (c : S.Classes) :
        S.amplitudeSum .full (S.ratMiddle E).besselS c s⁻¹ c =
          S.unipotentChar h.choose • S.amplitudeSum .full (S.ratMiddle E).besselS c 1 c := by
      simpa [hk_red] using
        amplitudeSum_besselU_mul isStable_besselS (u := 1) (one_mem _) hk_unip c 1 c
    simp [h_move, amplitudeSum_besselS_one_eq_ite, S.unipotentCovolume_pos.ne', sourceDim]
  · -- Otherwise there is no term: its translate `k` by the class representatives would be unipotent
    -- with the reduction `s⁻¹`.
    have h_empty (c : S.Classes) :
        IsEmpty ↥(↑(S.ratMiddle E).besselS ∩ S.termsOver c s⁻¹ c) := by
      refine ⟨fun ⟨γ, hγ, k, hk_red, hk⟩ ↦ ?_⟩
      have hk_unip : k.val ∈ (S.latticeMiddle (𝔸f E)).besselU :=
        S.mem_besselU_of_reduction_eq_one (j := j) hγ hk (by simp [hk_red, hs])
      exact h ⟨k⁻¹, inv_mem hk_unip, by simp [hk_red]⟩
    simp [amplitudeSum, tsum_empty]

omit ok [WeilData E] in
/-- Let `S` be filling data for a unitary group `G` over the CM field `E`, with level primes `p₀`,
`p₁`, and let `Ḡ = S.ResidueGL` be the product of the general linear groups over the residue fields
at the chosen places above them. Let `M = p₀ p₁`, and let `T` be a finite conjugation-stable set of
finite places off which `M⁻¹` is integral, so that `T` contains the places above `M`. Over the
product `LocProd T` of the completions at `T`, let `K` be the group of integral points of `G` and
`K(M)` its principal congruence subgroup of level `M`. Let `F` be a filling datum (`IsFillingData`):
a large lattice datum with `3ϱ + 6` hyperbolic pairs and `k - (6ϱ + 13)` orthonormal vectors, for
the ranks `ϱ = 𝔰.ϱ` and `k = 𝔰.k` of the shape, with modulus `F.levelUnit = M` and local character
`ψ(x) = ψ_f(-x / ϖ)`, where `ϖ` generates the different. The function
`χ_M = extendedBesselChar F.levelUnit` is `ψ(σ(u) / M)` on `u K(M)` for `u` in the block
unitriangular group `𝖴 = besselU`, with `σ(u)` the sum of the entries at the simple roots, and `0`
off `𝖴 K(M)`. Then for `l` in the stabilizer of the lattice, `χ_M` at the component of `l` at `T` is
`ψ_U` at the reduction of `l`, where `ψ_U = S.reducedChar` is the character `u ↦ ψ_f(-σ(u) / (M ϖ))`
of the integral points of `𝖴`, read on their reductions in `Ḡ` and extended by `0`. -/
lemma extendedBesselChar_toPlaces_eq_reducedChar {T : Finset (FinPlace E)} [T.StarStable]
    [Fact (S.ideleM⁻¹.val ∈ integralOff T)] [hInt : IntegralPlace (LocProd T)]
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) (l : S.latticeStabilizer) :
    extendedBesselChar F.levelUnit (S.toPlaces T l) = S.reducedChar (S.reduction l) := by
  rw [reducedChar]
  split_ifs with h
  · obtain ⟨hk_unip, hk_red⟩ :
        h.choose.val ∈ (S.latticeMiddle (𝔸f E)).besselU ∧ S.reduction h.choose = S.reduction l :=
      h.choose_spec
    have h_local : S.toPlaces T h.choose ∈ (S.latticeMiddle (LocProd T)).besselU :=
      hk_unip.map_mem_agreeWithOneOn _
    have h_cong : (S.toPlaces T h.choose)⁻¹ * S.toPlaces T l ∈
        unitaryLevel hInt.integers F.levelUnit (S.latticeMiddle (LocProd T)).splitGram :=
      (hF.reduction_eq_iff _ l).mp hk_red
    rw [extendedBesselChar_eq h_local h_cong,
      hF.psi_simpleRootSum_eq_unipotentChar (mem_latticeStabilizer_iff.mp h.choose.prop).1]
  · -- If `l ∈ u K(M)` at `T` with `u` unipotent, lift `u` to an integral unipotent element.
    by_contra h_ne
    obtain ⟨u, hu, hul⟩ : ∃ u ∈ (S.latticeMiddle (LocProd T)).besselU,
        u⁻¹ * S.toPlaces T l ∈ unitaryLevel hInt.integers F.levelUnit
          (S.latticeMiddle (LocProd T)).splitGram :=
      exists_besselU_of_extendedBesselChar_ne_zero h_ne
    obtain ⟨k, rfl, hk_off, hk_unip, -⟩ := S.exists_isIntegralOff_toPlaces_eq u
    have hk_int : k ∈ S.latticeStabilizer := by
      refine mem_latticeStabilizer_iff.mpr ⟨hk_off, ?_⟩
      -- `k = l (k⁻¹ l)⁻¹`, and both factors are integral at `T`.
      simpa using
        div_mem (mem_latticeStabilizer_iff.mp l.prop).2 (unitaryLevel_le_unitaryLevel_one hul)
    exact h ⟨⟨k, hk_int⟩, hk_unip hu, (hF.reduction_eq_iff ⟨k, hk_int⟩ l).mpr hul⟩

omit [WeilData E] in
/-- Let `S` be admissible filling data for a unitary group `G` over the CM field `E`, and let
`Ḡ = S.ResidueGL` be the product of the general linear groups over the residue fields at the chosen
places above the two level primes `p₀`, `p₁`. Let `M = p₀ p₁`, and let `T` be a finite
conjugation-stable set of finite places off which `M⁻¹` is integral, so that `T` contains the places
above `M`. Over the product `LocProd T` of the completions at `T`, let `K` be the group of integral
points of `G` and `K(M)` its principal congruence subgroup of level `M`. Let `F` be a filling datum
(`IsFillingData`): a large lattice datum with `3ϱ + 6` hyperbolic pairs and `k - (6ϱ + 13)`
orthonormal vectors, for the ranks `ϱ = 𝔰.ϱ` and `k = 𝔰.k` of the shape, with modulus
`F.levelUnit = M` and local character `ψ(x) = ψ_f(-x / ϖ)`, where `ϖ` generates the different. The
function `χ_M = extendedBesselChar F.levelUnit` is `ψ(σ(u) / M)` on `u K(M)` for `u` in the block
unitriangular group `𝖴 = besselU`, with `σ(u)` the sum of the entries at the simple roots, and `0`
off `𝖴 K(M)`. Then for `l` in the stabilizer of the lattice, `∫_K χ_M(y l y⁻¹) dy` for the measure
`dy = F.groupMeasure` is `vol(K)` times the value at the reduction of `l` of `S.reducedCharMean`,
the mean of `ψ_U` over conjugates. Here `ψ_U = S.reducedChar` is the character
`u ↦ ψ_f(-σ(u) / (M ϖ))` of the integral points of `𝖴`, read on their reductions in `Ḡ` and extended
by `0`. -/
lemma integral_extendedBesselChar_conj_eq {T : Finset (FinPlace E)} [T.StarStable]
    [Fact (S.ideleM⁻¹.val ∈ integralOff T)] [hInt : IntegralPlace (LocProd T)]
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) (l : S.latticeStabilizer) :
    ∫ y : (S.latticeMiddle (LocProd T)).G
        in unitaryLevel hInt.integers 1 (S.latticeMiddle (LocProd T)).splitGram,
        extendedBesselChar F.levelUnit (y * S.toPlaces T l * y⁻¹) ∂F.groupMeasure =
      F.groupMeasure.real (unitaryLevel hInt.integers 1 (S.latticeMiddle (LocProd T)).splitGram) •
        S.reducedCharMean (S.reduction l) := by
  -- Translate `y` by a lift `σ s` of each `s` in `S.ResidueGL` and sum; the integrand becomes
  -- constant.
  set K : Subgroup (U (S.latticeMiddle (LocProd T)).splitGram) :=
    unitaryLevel hInt.integers 1 (S.latticeMiddle (LocProd T)).splitGram
  let φ (y : (S.latticeMiddle (LocProd T)).G) : ℂ :=
    extendedBesselChar F.levelUnit (y * S.toPlaces T l * y⁻¹)
  choose σ hσ using ok.reduction_surjective
  have h_translate (g : S.ResidueGL) :
      ∫ y in K, φ (S.toPlaces T (σ g) * y) ∂F.groupMeasure = ∫ y in K, φ y ∂F.groupMeasure := by
    have h_mem : S.toPlaces T (σ g) ∈ K := (mem_latticeStabilizer_iff.mp (σ g).prop).2
    rw [← (measurePreserving_mul_left F.groupMeasure _).setIntegral_image_emb
      (measurableEmbedding_mulLeft _)]
    simp [Set.preimage, mul_mem_cancel_left, h_mem]
  have h_const (y : (S.latticeMiddle (LocProd T)).G) (hy : y ∈ K) :
      ∑ g : S.ResidueGL, φ (S.toPlaces T (σ g) * y) =
        Fintype.card S.ResidueGL * S.reducedCharMean (S.reduction l) := by
    obtain ⟨k, rfl, hk_off, -⟩ := S.exists_isIntegralOff_toPlaces_eq y
    lift k to S.latticeStabilizer using mem_latticeStabilizer_iff.2 ⟨hk_off, hy⟩
    rw [← S.reducedCharMean_conj (S.reduction k), reducedCharMean, Fintype.card_mul_expect]
    refine sum_congr rfl fun g _ ↦ ?_
    -- The integrand is `extendedBesselChar F.levelUnit` at the integral element
    -- `(σ g k) l (σ g k)⁻¹`.
    simpa [φ, hσ, mul_assoc] using
      S.extendedBesselChar_toPlaces_eq_reducedChar hF (σ g * k * l * (σ g * k)⁻¹)
  refine mul_left_cancel₀ (a := (Fintype.card S.ResidueGL : ℂ)) (by simp) ?_
  calc Fintype.card S.ResidueGL * ∫ y in K, φ y ∂F.groupMeasure
      = ∑ g : S.ResidueGL, ∫ y in K, φ (S.toPlaces T (σ g) * y) ∂F.groupMeasure := by
        simp only [h_translate, sum_const, card_univ, nsmul_eq_mul]
    _ = ∫ y in K, ∑ g : S.ResidueGL, φ (S.toPlaces T (σ g) * y) ∂F.groupMeasure :=
        (integral_finsetSum _ fun g _ ↦
          ContinuousOn.integrableOn_compact unitaryLevel_open_compact.2 (by fun_prop)).symm
    _ = Fintype.card S.ResidueGL * F.groupMeasure.real K • S.reducedCharMean (S.reduction l) := by
        rw [setIntegral_congr_fun measurableSet_unitaryLevel h_const, setIntegral_const,
          mul_smul_comm]

/-- Let `S` be admissible filling data for a unitary group `G` over the CM field `E`, which carries
Weil data, and let `Ḡ = S.ResidueGL` be the product of the general linear groups over the residue
fields at the chosen places above the two level primes `p₀`, `p₁`. Let `M = p₀ p₁`, and let `T` be a
finite conjugation-stable set of finite places off which `M⁻¹` is integral, so that `T` contains the
places above `M`. Over the product `LocProd T` of the completions at `T`, let `K` be the group of
integral points of `G` and `K(M)` its principal congruence subgroup of level `M`. Let `F` be a
filling datum (`IsFillingData`): a large lattice datum with `3ϱ + 6` hyperbolic pairs and
`k - (6ϱ + 13)` orthonormal vectors, for the ranks `ϱ = 𝔰.ϱ` and `k = 𝔰.k` of the shape, with
modulus `F.levelUnit = M` and local character `ψ(x) = ψ_f(-x / ϖ)`, where `ϖ` generates the
different. The function `χ_M = extendedBesselChar F.levelUnit` is `ψ(τ(u) / M)` on `u K(M)` for `u`
in the block unitriangular group `𝖴 = besselU`, with `τ(u)` the sum of the entries at the simple
roots, and `0` off `𝖴 K(M)`. Suppose that `T` consists of chosen places and their conjugates, and
put `a z = ∫_K χ_M(y z y⁻¹) dy` for the measure `dy = F.groupMeasure`. For a finite family `σ` in
the stabilizer of the lattice whose members have different reductions in `Ḡ` we have
`∑ |a (σ s)|² ≤ 2 vol(K)²`, where `a` is evaluated at the component of `σ s` at `T`. -/
lemma sum_sq_norm_integral_extendedBesselChar_conjugate_le {T : Finset (FinPlace E)} [T.StarStable]
    [Fact (S.ideleM⁻¹.val ∈ integralOff T)] (hT : T ⊆ S.chosenPlacesAndConj)
    [hInt : IntegralPlace (LocProd T)]
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) {ι : Type*} [Fintype ι] {σ : ι → S.latticeStabilizer}
    (hσ : Function.Injective fun s : ι ↦ S.reduction (σ s)) :
    ∑ s : ι,
        ‖∫ y : (S.latticeMiddle (LocProd T)).G
            in unitaryLevel hInt.integers 1 (S.latticeMiddle (LocProd T)).splitGram,
          extendedBesselChar F.levelUnit (y * S.toPlaces T (σ s) * y⁻¹) ∂F.groupMeasure‖ ^ 2 ≤
      2 * F.groupMeasure.real
        (unitaryLevel hInt.integers 1 (S.latticeMiddle (LocProd T)).splitGram) ^ 2 := by
  set K : Subgroup (U (S.latticeMiddle (LocProd T)).splitGram) :=
    unitaryLevel hInt.integers 1 (S.latticeMiddle (LocProd T)).splitGram
  let a (z : (S.latticeMiddle (LocProd T)).G) : ℂ := ∫ y in K,
    extendedBesselChar F.levelUnit (y * z * y⁻¹) ∂F.groupMeasure
  -- `a` is constant on the cosets `C s = σ(s) K(M)`: `K` normalises `K(M)`, and `χ_M` is right
  -- invariant under `K(M)`.
  let C (s : ι) : Set (U (S.latticeMiddle (LocProd T)).splitGram) :=
    ((S.toPlaces T (σ s))⁻¹ * ·) ⁻¹' F.congruenceSubgroup
  have hC_meas (s : ι) : MeasurableSet (C s) := measurable_const_mul _ measurableSet_unitaryLevel
  have ha_const (s : ι) : ∀ z ∈ C s, a z = a (S.toPlaces T (σ s)) := fun z hz ↦
    setIntegral_congr_fun measurableSet_unitaryLevel fun y hy ↦ by
      simpa using extendedBesselChar_mul_of_mem_unitaryLevel (y := y * S.toPlaces T (σ s) * y⁻¹)
        (conj_mem_unitaryLevel hy hz)
  -- The cosets are disjoint, since the `σ s` have different reductions.
  have hC_disj : Pairwise (Function.onFun Disjoint C) := by
    intro s t hst
    refine Set.disjoint_left.mpr fun z hs ht ↦ hst <| hσ <| ?_
    simpa [← hF.reduction_eq_iff, eq_comm] using div_mem hs.out ht.out
  -- The integral of `|a|²` over these cosets is at most `massIntegral K = ∫ |a|²`; bound this by
  -- `IsLargeLatticeData.massIntegral_le_main_add_error` with `Q = 2`, and by
  -- `2⁻¹ ^ n ≤ groupMeasure(K)`.
  have h_lintegral :
      (∑ s : ι, ‖a (S.toPlaces T (σ s))‖ₑ ^ 2) * F.groupMeasure F.congruenceSubgroup ≤
        2 * F.groupMeasure K ^ 2 * F.groupMeasure F.congruenceSubgroup := by
    have h_coset (s : ι) : ∫⁻ z in C s, ‖a z‖ₑ ^ 2 ∂F.groupMeasure =
        ‖a (S.toPlaces T (σ s))‖ₑ ^ 2 * F.groupMeasure F.congruenceSubgroup := by
      rw [setLIntegral_congr_fun (hC_meas s) fun z hz ↦ by rw [ha_const s z hz]]
      simp [C]
    have h_rank : 𝔰.n + 2 * 10 ^ 9 * 𝔰.n ^ 4 ≤ 𝔰.k := by
      grind [S.pow_chain, Nat.le_self_pow (n := 4) (by norm_num) 𝔰.n]
    calc (∑ s : ι, ‖a (S.toPlaces T (σ s))‖ₑ ^ 2) * F.groupMeasure F.congruenceSubgroup
        = ∑' s : ι, ∫⁻ z in C s, ‖a z‖ₑ ^ 2 ∂F.groupMeasure := by
          simp only [h_coset, sum_mul, tsum_fintype]
      _ = ∫⁻ z in ⋃ s, C s, ‖a z‖ₑ ^ 2 ∂F.groupMeasure := (lintegral_iUnion hC_meas hC_disj _).symm
      _ ≤ F.massIntegral K := setLIntegral_le_lintegral ..
      _ ≤ F.groupMeasure K * F.groupMeasure F.congruenceSubgroup * (F.groupMeasure K + 2⁻¹ ^ 𝔰.n) :=
          hF.massIntegral_le_main_add_error ⟨_, unitaryLevel_le_unitaryLevel_one, le_rfl⟩ le_rfl
            IsLargeLatticeData.modulus_le_half h_rank
      _ ≤ 2 * F.groupMeasure K ^ 2 * F.groupMeasure F.congruenceSubgroup := by
          grw [hF.inv_two_pow_le_groupMeasure (volume_integers_diff_intUnits_le hT)]
          exact le_of_eq (by ring)
  -- Pass to real numbers and cancel `groupMeasure(K(M)) > 0`.
  have h_pos : 0 < F.groupMeasure.real F.congruenceSubgroup :=
    toReal_pos ((unitaryLevel_open_compact.1 (g := F.levelUnit)).measure_ne_zero _ (by simp))
      (hF.groupMeasure_ne_top unitaryLevel_le_unitaryLevel_one)
  refine le_of_mul_le_mul_right ?_ h_pos
  simpa [toReal_sum, Measure.real] using
    toReal_mono (by simp [mul_eq_top, K, hF.groupMeasure_ne_top unitaryLevel_le_unitaryLevel_one])
      h_lintegral

omit ok [WeilData E] in
/-- Let `S` be filling data over the CM field `E`, with level primes `p₀`, `p₁` and, for each `p_i`,
a chosen set `S.chosenPlaces i` of places of norm `p_i`, such that the chosen places and their
conjugates have product `M = p₀ p₁`. If a finite set `T` of finite places contains all of these,
then the inverse of the finite idele `S.ideleM` of `M` is integral off `T`. -/
lemma inv_ideleM_mem_integralOff {T : Finset (FinPlace E)}
    (hT_mem : ∀ (i : Fin 2) (w : S.chosenPlaces i), w.val ∈ T ∧ star w.val ∈ T) :
    S.ideleM⁻¹.val ∈ integralOff T := by
  -- `M` divides the idempotent of the places off `T`, as it vanishes at the places of `T`.
  let r : Ô E := ⟨idem (↑T : Set (FinPlace E))ᶜ, idem_mem_Ô _⟩
  have h_vanish (i : Fin 2) (w : S.chosenPlaces i) :
      reduceAt w.val r = 0 ∧ reduceAt w.val (star r) = 0 := by
    grind [reduceAt_idem, star_idem, coe_star_Ô]
  have h_idem : S.ideleM⁻¹ • idem Tᶜ ∈ Ô E := by
    refine (S.inv_ideleM_smul_mem_iff r).2 ?_
    rintro ⟨⟨i, w⟩, _ | _⟩
    · rw [reduceAboveM_false, (h_vanish i w).1]
    · rw [reduceAboveM_true, RingHom.comp_apply, starRingEnd_apply, (h_vanish i w).2]
  exact (mem_integralOff T).2 (idem_mul_mem_Ô.1 (by rwa [mul_comm]))

omit ok in
/-- **The induced character.** Let `S` be admissible filling data for a unitary group `G` over the
CM field `E`, which carries Weil data, and let `Ḡ = S.ResidueGL` be the product of the general
linear groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`.
Let `ψ_U = S.reducedChar` be the additive character (`unipotentChar`) of the integral block
unitriangular elements of `G`, read on their reductions in `Ḡ` and extended by `0`, and let
`ψ_U^♮(s) = S.reducedCharMean s` be its mean over the conjugates of `s`. Then `∑ |ψ_U^♮(s)|² ≤ 2`,
the sum being over all `s` in `Ḡ`. -/
theorem sum_norm_reducedCharMean_sq_le [ok : S.IsAdmissible] :
    ∑ s : S.ResidueGL, ‖S.reducedCharMean s‖ ^ 2 ≤ 2 := by
  -- Work at the set `T` of the chosen places and their conjugates, with a lift `σ s` of each `s`.
  choose σ hσ using ok.reduction_surjective
  let T : Finset (FinPlace E) := S.chosenPlacesAndConj
  have : T.StarStable := by
    refine ⟨fun w hw ↦ ?_⟩
    obtain ⟨i, s, hs, rfl | rfl⟩ := mem_chosenPlacesAndConj.1 hw
    · exact mem_chosenPlacesAndConj.2 ⟨i, w, hs, .inr rfl⟩
    · exact mem_chosenPlacesAndConj.2 ⟨i, s, hs, .inl (star_star s)⟩
  have hT_mem (i : Fin 2) (w : S.chosenPlaces i) : w.val ∈ T ∧ star w.val ∈ T :=
    ⟨mem_chosenPlacesAndConj.2 ⟨i, w, w.prop, .inl rfl⟩,
      mem_chosenPlacesAndConj.2 ⟨i, w, w.prop, .inr rfl⟩⟩
  have : Fact (S.ideleM⁻¹.val ∈ integralOff T) := ⟨S.inv_ideleM_mem_integralOff hT_mem⟩
  -- The product of the completions at `T` has a large lattice datum `F` of modulus `M`.
  obtain ⟨hInt, F, hF⟩ := S.exists_isFillingData T
  set K : Subgroup (U (S.latticeMiddle (LocProd T)).splitGram) :=
    unitaryLevel hInt.integers 1 (S.latticeMiddle (LocProd T)).splitGram
  have hK_pos : 0 < F.groupMeasure.real K :=
    toReal_pos ((unitaryLevel_open_compact.1 (g := 1)).measure_ne_zero _ (by simp))
      (hF.groupMeasure_ne_top unitaryLevel_le_unitaryLevel_one)
  -- The integrals in `sum_sq_norm_integral_extendedBesselChar_conjugate_le` are the measure of `K`
  -- times `ψ_U^♮(s)`.
  have h_sq : F.groupMeasure.real K ^ 2 * ∑ s, ‖S.reducedCharMean s‖ ^ 2 ≤
      F.groupMeasure.real K ^ 2 * 2 := by
    have h_inj : Function.Injective fun s : S.ResidueGL ↦ S.reduction (σ s) := fun s t hst ↦ by
      simpa [hσ] using hst
    simpa only [S.integral_extendedBesselChar_conj_eq hF, hσ,
      norm_smul_of_nonneg measureReal_nonneg, mul_pow,
      ← mul_sum, mul_comm (2 : ℝ)] using S.sum_sq_norm_integral_extendedBesselChar_conjugate_le
        (T := T) subset_rfl hF h_inj
  exact le_of_mul_le_mul_left h_sq (pow_pos hK_pos 2)

attribute [local instance low] Fintype.ofFinite in
/-- **The trace.** Let `S` be admissible filling data for a unitary group `G` over the CM field `E`,
which carries Weil data, and let `Ḡ = S.ResidueGL` be the product of the general linear groups over
the residue fields at the chosen places above the two level primes `p₀`, `p₁`. Let
`r_ψ(s) = S.besselTranslate s` be the operator on the source `ℂ^(classes × Bessel coordinates)`
whose blocks are the complex conjugates of the normalised amplitude sums of the rational elements of
the Bessel subgroup `besselS`. Let `x` be a central idempotent of the group algebra of the factor of
`Ḡ` above `p_i`, made of matrices indexed by the basis `𝔰.BesselIndex` of the hermitian space, with
`Re x(1) ≤ b⁻⁸ / 2`. Then the trace of `r_ψ(x) = ∑ x(s) r_ψ(s)` has real part at most `b⁻⁴ D_X`. -/
lemma re_sum_coeff_mul_trace_besselTranslate_le {i : Fin 2}
    {x : MonoidAlgebra ℂ (∀ w : S.chosenPlaces i, GL 𝔰.BesselIndex (ResField w.val))}
    (hx : IsCentralProj x) (hx_small : (x.coeff 1).re ≤ (S.b ^ 8)⁻¹ / 2) :
    (∑ s : ∀ w : S.chosenPlaces i, GL 𝔰.BesselIndex (ResField w.val), x.coeff s *
        LinearMap.trace ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord))
          (S.besselTranslate (mulSingle i s))).re ≤
      (S.b ^ 4)⁻¹ * S.sourceDim := by
  -- The element `mulSingle i s` is `1` above the other prime, so the trace is `D_X ψ_U(s)`.
  have h_trace (s : ∀ w : S.chosenPlaces i, GL 𝔰.BesselIndex (ResField w.val)) :
      LinearMap.trace ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord))
        (S.besselTranslate (mulSingle i s)) = S.sourceDim * S.reducedChar (mulSingle i s) :=
    S.trace_besselTranslate_eq_mul_reducedChar (j := i + 1) (by simp)
  -- As `x` is a class function, `ψ_U` may be replaced by its mean over conjugates.
  have h_mean : ∑ s, x.coeff s * S.reducedChar (mulSingle i s) =
      ∑ s, x.coeff s * S.reducedCharMean (mulSingle i s) := by
    have h_conj (g : S.ResidueGL) : ∑ s, x.coeff s * S.reducedChar (g * mulSingle i s * g⁻¹) =
        ∑ s, x.coeff s * S.reducedChar (mulSingle i s) := by
      refine Fintype.sum_equiv (MulAut.conj (g i)) _ _ fun s ↦ ?_
      have h_single : g * mulSingle i s * g⁻¹ = mulSingle i (g i * s * (g i)⁻¹) :=
        Function.eq_update_iff.2 (by simp +contextual)
      rw [h_single, EquivLike.coe_coe, MulAut.conj_apply, hx.2]
    simp only [reducedCharMean, mul_expect, ← expect_sum_comm, h_conj, Fintype.expect_const]
  have h_sq : ∑ s, ‖S.reducedCharMean (mulSingle i s)‖ ^ 2 ≤ 2 := by
    refine .trans ?_ S.sum_norm_reducedCharMean_sq_le
    rw [← sum_image (f := fun s ↦ ‖S.reducedCharMean s‖ ^ 2) (mulSingle_injective i).injOn]
    exact sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
  -- Cauchy–Schwarz, with `∑ |x s|² = Re x(1) ≤ b⁻⁸ / 2` and `∑ |ψ_U^♮|² ≤ 2`.
  have h_bound : ‖∑ s, x.coeff s * S.reducedCharMean (mulSingle i s)‖ ≤ (S.b ^ 4)⁻¹ := by
    refine (abs_le_of_sq_le_sq' ?_ (by positivity)).2
    calc ‖∑ s, x.coeff s * S.reducedCharMean (mulSingle i s)‖ ^ 2
        ≤ (∑ s, ‖x.coeff s‖ * ‖S.reducedCharMean (mulSingle i s)‖) ^ 2 := by
          grw [norm_sum_le, norm_mul_le]
      _ ≤ (S.b ^ 8)⁻¹ / 2 * 2 := by
          grw [sum_mul_sq_le_sq_mul_sq, sum_norm_sq_coeff_of_isCentralProj hx, hx_small, h_sq]
      _ = (S.b ^ 4)⁻¹ ^ 2 := by ring
  calc (∑ s, x.coeff s * LinearMap.trace ℂ _ (S.besselTranslate (mulSingle i s))).re
      = (S.sourceDim * ∑ s, x.coeff s * S.reducedCharMean (mulSingle i s)).re := by
        simp only [← h_mean, h_trace, mul_left_comm (x.coeff _), mul_sum]
    _ ≤ S.sourceDim * ‖∑ s, x.coeff s * S.reducedCharMean (mulSingle i s)‖ := by
        grw [re_le_norm, norm_mul, norm_natCast]
    _ ≤ (S.b ^ 4)⁻¹ * S.sourceDim := by
        grw [h_bound, mul_comm]

end BesselTrace

/-! ## Good forms: one prime and both primes -/

section GoodForms

open Matrix Complex Module InnerProductSpace EuclideanSpace Finset Fintype

attribute [local instance low] Fintype.ofFinite

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰} [ok : S.IsAdmissible]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ S.ResidueGL V} {P : EuclideanSpace ℂ (S.Classes × S.BesselCoord) →ₗ[ℂ] V}

open scoped Classical in
/-- **One prime.** Let `S` be admissible filling data (`Filling`, `IsAdmissible`) for a unitary
group `G` over the CM field `E`, which carries Weil data (a primitive `5040`-th root of unity and a
splitting character, see `WeilData`), and let `Ḡ = S.ResidueGL` be the product of the general linear
groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`. The
source is the Euclidean space with coordinates `(c, i)`, where `c` is a class (a double coset of the
definite unitary group `U(X₀)` for the level) and `i` is a coordinate of the Bessel function `W` at
the infinite places. Let `ρ` be a unitary representation of `Ḡ` on `V` and `P` a linear map from the
source to `V`. Suppose `HasAmplitudeBlocks`: the block `(c, c')` of `P_s = P* ρ(s) P` is the
conjugate of `A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and `A(c, s, c')` is the sum,
over the rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with reduction `s`, of an integral
of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class `c`). Let `x` be a central
idempotent (an idempotent whose coefficients form a class function; it is then self-adjoint) of the
group algebra of the factor of `Ḡ` above `p_i`, made of matrices indexed by the basis
`𝔰.BesselIndex` of the hermitian space, with `Re x(1) ≤ b⁻⁸ / 2`, where `b = S.b ≥ 1000` is the size
parameter of `S`. Then `‖x P‖² ≤ 2 b⁻⁴ D_X` in Hilbert–Schmidt norm, where `x` acts on `V` through
`ρ` and `D_X = S.sourceDim` is the dimension of the source. -/
lemma HasAmplitudeBlocks.hilbertSchmidtNorm_asAlgebraHom_comp_sq_le [WeilData E]
    (hP : S.HasAmplitudeBlocks ρ P)
    (hρ : ∀ (s : S.ResidueGL) (v v' : V), ⟪ρ s v, ρ s v'⟫_ℂ = ⟪v, v'⟫_ℂ) (i : Fin 2)
    {x : MonoidAlgebra ℂ (∀ w : S.chosenPlaces i, GL 𝔰.BesselIndex (ResField w.val))}
    (hx : IsCentralProj x) (hx_small : (x.coeff 1).re ≤ (S.b ^ 8)⁻¹ / 2) :
    hilbertSchmidtNorm
        (Representation.asAlgebraHom (ρ.comp (MonoidHom.mulSingle
          (fun j : Fin 2 ↦ ∀ w : S.chosenPlaces j, GL 𝔰.BesselIndex (ResField w.val)) i)) x ∘ₗ
          P) ^ 2 ≤
      2 * (S.b ^ 4)⁻¹ * S.sourceDim := by
  have hb : 1000 ≤ S.b := S.thousand_le_b
  set e : End ℂ V := Representation.asAlgebraHom (ρ.comp (.mulSingle _ i)) x with he_def
  have he : e.IsSymmetricProjection :=
    hx.isSymmetricProjection (ρ := ρ.comp (.mulSingle _ i)) fun _ ↦ hρ _
  set P' : End ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord)) := ∑ t, x.coeff t •
    (P.adjoint ∘ₗ ρ (Pi.mulSingle i t) ∘ₗ P - S.besselTranslate (Pi.mulSingle i t)) with hP'
  -- `‖x P‖² = tr (P* x P) = tr r_ψ(x) + tr P'_x`, with `r_ψ(x) = ∑ x(t) r_ψ(t)`, `P'_x = P'`.
  have h_trace : hilbertSchmidtNorm (e ∘ₗ P) ^ 2 =
      (∑ t, x.coeff t * LinearMap.trace ℂ _ (S.besselTranslate (Pi.mulSingle i t))).re +
        (LinearMap.trace ℂ _ P').re := by
    have h_proj : (e ∘ₗ P).adjoint ∘ₗ e ∘ₗ P = P.adjoint ∘ₗ e ∘ₗ P := by
      rw [LinearMap.adjoint_comp, he.isSymmetric.adjoint_eq, LinearMap.comp_assoc,
        ← LinearMap.comp_assoc P e e, ← End.mul_eq_comp, he.isIdempotentElem.eq]
    have h_sum : P.adjoint ∘ₗ e ∘ₗ P =
        ∑ t, x.coeff t • (P.adjoint ∘ₗ ρ (Pi.mulSingle i t) ∘ₗ P) := by
      ext1 v
      simp [he_def, asAlgebraHom_eq_sum]
    rw [← ofReal_re (_ ^ 2), hilbertSchmidtNorm_sq_eq_trace, h_proj, h_sum, ← add_re, hP']
    simp [mul_sub]
  have h_bessel :
      (∑ t, x.coeff t * LinearMap.trace ℂ _ (S.besselTranslate (Pi.mulSingle i t))).re ≤
        (S.b ^ 4)⁻¹ * S.sourceDim :=
    S.re_sum_coeff_mul_trace_besselTranslate_le hx hx_small
  -- `|tr P'_x| ≤ ‖1‖ ‖P'_x‖`
  have h_rest : (LinearMap.trace ℂ _ P').re ≤ (S.b ^ 4)⁻¹ * S.sourceDim := by
    have h_inner : LinearMap.trace ℂ _ P' = ⟪hilbertSchmidtVector 1,
      hilbertSchmidtVector P'⟫_ℂ := by
      rw [inner_hilbertSchmidtVector, End.one_eq_id, LinearMap.adjoint_id, LinearMap.id_comp]
    rw [h_inner]
    refine (re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    suffices h_sq : (‖hilbertSchmidtVector
      (1 : End ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord)))‖ *
        ‖hilbertSchmidtVector P'‖) ^ 2 ≤ ((S.b ^ 4)⁻¹ * S.sourceDim) ^ 2 from
      (abs_le_of_sq_le_sq' h_sq (by positivity)).2
    calc
      _ = S.sourceDim * hilbertSchmidtNorm P' ^ 2 := by
        rw [mul_pow, ← hilbertSchmidtNorm_one_sq_eq_sourceDim, hilbertSchmidtNorm,
          hilbertSchmidtNorm]
      _ ≤ S.sourceDim * (S.sourceDim / S.b ^ 12) := by
        grw [hP.hilbertSchmidtNorm_sum_smul_sub_besselTranslate_sq_le hρ i hx]
      _ ≤ S.sourceDim * (S.sourceDim / S.b ^ 8) := by gcongr <;> linarith
      _ = ((S.b ^ 4)⁻¹ * S.sourceDim) ^ 2 := by ring
  linarith

variable {g : ∀ i : Fin 2,
  MonoidAlgebra ℂ (∀ w : S.chosenPlaces i, GL 𝔰.BesselIndex (ResField w.val))}

omit ok [FiniteDimensional ℂ V] in
/-- The source has dimension `D_X = S.sourceDim`. -/
lemma finrank_source_eq_sourceDim :
    (finrank ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord)) : ℝ) = S.sourceDim := by
  simp [sourceDim]

/-- **Both primes.** Let `S` be admissible filling data (`Filling`, `IsAdmissible`) for a unitary
group `G` over the CM field `E`, which carries Weil data (a primitive `5040`-th root of unity and a
splitting character, see `WeilData`), and let `Ḡ = S.ResidueGL` be the product of the general linear
groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`. The
source is the Euclidean space with coordinates `(c, i)`, where `c` is a class (a double coset of the
definite unitary group `U(X₀)` for the level) and `i` is a coordinate of the Bessel function `W` at
the infinite places. Let `ρ` be a unitary representation of `Ḡ` on `V` and `P` a linear map from the
source to `V`. Suppose `HasAmplitudeBlocks`: the block `(c, c')` of `P_s = P* ρ(s) P` is the
conjugate of `A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and `A(c, s, c')` is the sum,
over the rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with reduction `s`, of an integral
of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class `c`). Let `g_i` be a central
idempotent (an idempotent whose coefficients form a class function; it is then self-adjoint) of the
group algebra of the factor of `Ḡ` above `p_i`, such that the coefficient of `1 - g_i` at `1` has
real part at most `b⁻⁸ / 2`, where `b = S.b ≥ 1000` is the size parameter of `S`. Let
`e₀ = piTensorElem g` be the tensor product `g₀ ⊗ g₁` in `ℂ[Ḡ]`, acting on `V` through `ρ`. Then
`‖(1 - e₀) P‖² ≤ 4 b⁻⁴ D_X` in Hilbert–Schmidt norm, where `D_X = S.sourceDim` is the dimension of
the source. -/
theorem HasAmplitudeBlocks.hilbertSchmidtNorm_one_sub_piTensorElem_comp_sq_le [WeilData E]
    (hP : S.HasAmplitudeBlocks ρ P) (hρ : ∀ (s : S.ResidueGL) (x y : V), ⟪ρ s x, ρ s y⟫_ℂ = ⟪x,
      y⟫_ℂ)
    (hg : ∀ i : Fin 2, IsCentralProj (g i))
    (hg_small : ∀ i : Fin 2, ((1 - g i).coeff 1).re ≤ (S.b ^ 8)⁻¹ / 2) :
    hilbertSchmidtNorm ((1 - ρ.asAlgebraHom (piTensorElem g)) ∘ₗ P) ^ 2 ≤
      4 * (S.b ^ 4)⁻¹ * S.sourceDim := by
  let e (i : Fin 2) : End ℂ V := Representation.asAlgebraHom (ρ.comp (.mulSingle _ i)) (g i)
  have h_factor : ρ.asAlgebraHom (piTensorElem g) = e 0 * e 1 := by
    have h_split : g = Pi.mulSingle 0 (g 0) * Pi.mulSingle 1 (g 1) := by
      ext i : 1
      fin_cases i <;> simp
    rw [h_split, map_mul, map_mul, asAlgebraHom_piTensorElem_mulSingle,
      asAlgebraHom_piTensorElem_mulSingle]
  have h_proj : (e 0).IsSymmetricProjection :=
    (hg 0).isSymmetricProjection (ρ := ρ.comp (.mulSingle _ 0)) fun _ ↦ hρ _
  have h_prime (i : Fin 2) : hilbertSchmidtNorm ((1 - e i) ∘ₗ P) ^ 2 ≤ 2 * (S.b ^ 4)⁻¹ *
    S.sourceDim := by
    simpa [e] using hP.hilbertSchmidtNorm_asAlgebraHom_comp_sq_le hρ i (hg i).one_sub (hg_small i)
  rw [h_factor]
  calc hilbertSchmidtNorm ((1 - e 0 * e 1) ∘ₗ P) ^ 2
      ≤ hilbertSchmidtNorm ((1 - e 0) ∘ₗ P) ^ 2 + hilbertSchmidtNorm ((1 - e 1) ∘ₗ P) ^ 2 :=
        hilbertSchmidtNorm_one_sub_mul_comp_sq_le h_proj (e 1) P
    _ ≤ 4 * (S.b ^ 4)⁻¹ * S.sourceDim := by linarith [h_prime 0, h_prime 1]

/-- **Good forms.** Let `S` be admissible filling data (`Filling`, `IsAdmissible`) for a unitary
group `G` over the CM field `E`, which carries Weil data (a primitive `5040`-th root of unity and a
splitting character, see `WeilData`), and let `Ḡ = S.ResidueGL` be the product of the general linear
groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`. The
source is the Euclidean space with coordinates `(c, i)`, where `c` is a class (a double coset of the
definite unitary group `U(X₀)` for the level) and `i` is a coordinate of the Bessel function `W` at
the infinite places. Let `ρ` be a unitary representation of `Ḡ` on `V` and `P` a linear map from the
source to `V`. Suppose `HasAmplitudeBlocks`: the block `(c, c')` of `P_s = P* ρ(s) P` is the
conjugate of `A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and `A(c, s, c')` is the sum,
over the rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with reduction `s`, of an integral
of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class `c`). Let `g_i` be a central
idempotent (an idempotent whose coefficients form a class function; it is then self-adjoint) of the
group algebra of the factor of `Ḡ` above `p_i`, such that the coefficient of `1 - g_i` at `1` has
real part at most `b⁻⁸ / 2`, where `b = S.b ≥ 1000` is the size parameter of `S`. Let
`e₀ = piTensorElem g` be the tensor product `g₀ ⊗ g₁` in `ℂ[Ḡ]`, acting on `V` through `ρ`. Then
`e₀ P` is almost an isometry from below in mean square (`IsNearIsometry`) with error `5 b⁻⁴`:
`‖e₀ P pr_U‖² ≥ dim U - 5 b⁻⁴ D_X` in Hilbert–Schmidt norm for every subspace `U` of the source,
where `pr_U` is the orthogonal projection onto `U` and `D_X` is the dimension of the source. -/
theorem HasAmplitudeBlocks.isNearIsometry_piTensorElem_comp [WeilData E]
    (hP : S.HasAmplitudeBlocks ρ P)
    (hρ : ∀ (s : S.ResidueGL) (x y : V), ⟪ρ s x, ρ s y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hg : ∀ i : Fin 2, IsCentralProj (g i))
    (hg_small : ∀ i : Fin 2, ((1 - g i).coeff 1).re ≤ (S.b ^ 8)⁻¹ / 2) :
    IsNearIsometry (ρ.asAlgebraHom (piTensorElem g) ∘ₗ P) (5 * (S.b ^ 4)⁻¹) := by
  have hb : 1000 ≤ S.b := S.thousand_le_b
  -- `P` itself is almost an isometry, as `‖P* P - 1‖² ≤ b⁻¹² D_X`.
  have h_isom : IsNearIsometry P (S.b ^ 4)⁻¹ := by
    refine isNearIsometry_of_hilbertSchmidtNorm_le (by positivity)
      (hP.hilbertSchmidtNorm_sub_one_sq_le.trans ?_)
    rw [finrank_source_eq_sourceDim, inv_pow, ← pow_mul, ← div_eq_inv_mul]
    gcongr <;> linarith
  have h_bad : hilbertSchmidtNorm ((1 - ρ.asAlgebraHom (piTensorElem g)) ∘ₗ P) ^ 2 ≤
      4 * (S.b ^ 4)⁻¹ * finrank ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord)) := by
    rw [finrank_source_eq_sourceDim]
    exact hP.hilbertSchmidtNorm_one_sub_piTensorElem_comp_sq_le hρ hg hg_small
  have h_proj : (ρ.asAlgebraHom (piTensorElem g)).IsSymmetricProjection :=
    (IsCentralProj.piTensorElem hg).isSymmetricProjection hρ
  exact (h_isom.proj_comp h_proj h_bad).mono (le_of_eq (by ring))

end GoodForms

end New.Filling
