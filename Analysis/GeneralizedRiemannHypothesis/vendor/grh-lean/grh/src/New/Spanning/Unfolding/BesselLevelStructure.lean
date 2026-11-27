import Lib.Adelic.Adeles.LocalFactors
import Lib.Shimura.HeckeTower.HeckeData
import New.Spanning.Unfolding.Setup

/-!
# Bessel data: level subgroup, Eichler maps and strong approximation for the unipotent group

The file works with filling data `S : New.Filling E 𝔰` and the unitary group `S.G` of the form
`T.splitGram`, where `T` is the middle Gram matrix, at rational points, finite adeles and
archimedean points. The middle space is X₀ ⊕ E z, with X₀ spanned by the basis vectors indexed by
`κ`. Write 𝖴 for the Bessel unipotent group `New.Shape.Form.besselU`. Write H for
`New.Shape.Form.besselH`, the unitary group U(X₀), acting only on the basis vectors indexed by `κ`.
Write `New.Shape.Form.besselS` for the group they generate. Write σ = `New.simpleRootSum` for the
sum of the entries just above the diagonal on the frame. The level is `S.M = p₀ p₁` with
`pᵢ = S.levelPrime i`, and `S.chosenPlaces i` are the chosen places of norm `pᵢ`. K(M) is
`S.principalLevel`. For a class c, h_c = `S.classRep c` is its representative in H. For classes c,
d, `S.translateByClassReps c d γ` is h_c⁻¹ γ h_d, and `S.termsOver c s d` is the set of rational γ
with `S.translateByClassReps c d γ` integral of reduction s.

## Main definitions and results

* `New.Filling.besselFn_adelicToInf_mul_eq_prod_wave_smul`, `New.Filling.besselFn_ratToInf_mul`: how
  the Bessel function `New.Filling.besselFn` transforms under left translation by `𝖴`.
* `New.exists_mem_besselU_eq_eichlerMap`: for a hermitian invertible form, if x is a combination of
  the frame vectors of index below a and v is orthogonal to these vectors, then the Eichler map
  along x and v, with ς = τ h(v, v), lies in the unipotent group `New.Shape.Form.besselU`; the lemma
  also computes its `New.simpleRootSum`.
* `New.besselU_dense`, `New.Filling.exists_besselU_approx`: strong approximation for 𝖴.
* `New.Filling.mem_reducedImage_besselU_iff_exists_termsOver`,
  `New.Filling.prod_wave_eq_star_unipotentChar`: the rational points of 𝖴 that are integral for a
  class map onto the reduction of the integral points of 𝖴(𝔸_f), and on them the character at
  infinity is the conjugate of the finite character at an integral point with the same reduction.
* `New.Filling.exists_besselS_mem_termsOver`: each reduction `s` of an integral element of
  `New.Shape.Form.besselS` is reached from each class c by a rational element of
  `New.Shape.Form.besselS`.

Notions from other files:
* `New.Shape.Form.splitGram`: The Gram matrix of ϱ hyperbolic planes and a middle space with Gram
  matrix T: identity blocks pair the first and last ϱ indices, T is the middle block, all else is
  zero.
* `New.Filling.selfDualChar`: The additive character x ↦ ψ_f(−x/ϖ) of the finite adeles.
* `New.Filling.IsAdmissible`: The standing hypotheses on the data: among them, `sourceLevel` is the
  preimage of K(M), `reduction` is onto, and some size inequalities hold.
* `S.GFin`: The finite adelic points of the unitary group in the lattice basis.
* `New.Filling.unipotentChar`: The value of the additive character `S.selfDualChar` at M⁻¹ σ(u),
  where σ(u) = `New.simpleRootSum u` sums the entries of u at the simple roots.

## Relation to the literature

See `Lib.DiscreteSeries.Bruhat.FloorGroups` for sources.
-/

noncomputable section

/-!
## Bessel groups at rational, finite adelic and archimedean points

* `New.Filling.termsOver.mul`, `New.Filling.termsOver.inv`: the sets `New.Filling.termsOver` compose
  like a groupoid.
* `New.Filling.prod_wave_simpleRootSum_adelicToInf`, `New.Filling.prod_wave_simpleRootSum_ratToInf`:
  the character of `𝖴` at infinity in terms of the finite character.
-/

namespace New.Filling

open NumberField Matrix Complex Circle Finset Real Prod Floors.FloorGroups

variable {E : Type} [Field E] [CMType E]
  {𝔰 : Shape} {S : Filling E 𝔰} {R R' : Type} [CommRing R] [CommRing R']

attribute [local aesop simp] selfDualChar ideleM splitGram middleGram latticeMiddleGram
  besselLatticeBasis BesselIndex.level

/-! ### Change of ring and of basis in the Bessel groups -/

/-- A ring homomorphism carries the Gram matrix in the lattice basis over `R` to the one over
`R'`: `S.latticeMiddle R` is the middle block of this matrix and `splitGram` the whole matrix. -/
lemma map_splitGram_latticeMiddle (f : R →+* R') :
    (S.latticeMiddle R).splitGram.map f = (S.latticeMiddle R').splitGram := by
  aesop (add simp [fromBlocks_map, fromCols_map, fromRows_map])

/-- If `γ` agrees with the identity matrix at the entries `(i, j)` with `r i j`, then so does its
image under a ring homomorphism `f`; `agreeWithOneOn` is the group of such invertible matrices. -/
lemma _root_.Membership.mem.map_mem_agreeWithOneOn (f : R →+* R')
    {r : 𝔰.BesselIndex → 𝔰.BesselIndex → Prop}
    {hr : ∀ i k j : 𝔰.BesselIndex, r i j → r i k ∨ r k j} {H : Subgroup (GL 𝔰.BesselIndex R)}
    {γ : H} (hγ : γ ∈ (agreeWithOneOn r R hr).subgroupOf H) :
    GeneralLinearGroup.map f γ.val ∈ agreeWithOneOn r R' hr := by
  aesop (add simp [Subgroup.mem_subgroupOf, Matrix.one_apply])

variable (S) in
lemma isUnit_natCast_N : IsUnit (S.N : E) := (Nat.cast_ne_zero.2 S.N_prime.ne_zero).isUnit

/-- The rational Gram matrix `S.ratMiddle E` of the middle space is hermitian and invertible. -/
instance : Floors.IsHermitianUnit (S.ratMiddle E) where
  conjTranspose_eq := by aesop (add simp fromBlocks_conjTranspose)
  isUnit := by simp [isUnit_iff_isUnit_det, middleGram, Nat.Prime.ne_zero]

/-- A finite adelic point lies in the unipotent group `besselU` in rational coordinates iff it does
in the lattice basis; `S.toLatticeBasis` is the change to the lattice basis. -/
lemma toLatticeBasis_mem_besselU {x : S.G (𝔸f E)} : S.toLatticeBasis x ∈ besselU ↔ x ∈ besselU := by
  -- `S.toLatticeBasis` is conjugation by `S.latticeBasis`; both `S.latticeBasis` and its inverse
  -- are block triangular.
  obtain ⟨h_tri, h_inv_tri⟩ : S.latticeBasis.val.BlockTriangular BesselIndex.level ∧
      (S.latticeBasis⁻¹).val.BlockTriangular BesselIndex.level := by
    aesop (add simp [BlockTriangular, Matrix.one_apply])
  refine ⟨fun hx ↦ ?_, fun hx ↦ conj_mem_unitriangular h_tri hx.out⟩
  have h_eq : S.latticeBasis⁻¹⁻¹ * (S.toLatticeBasis x).val * S.latticeBasis⁻¹ = x.val := by
    simp [toLatticeBasis, mul_assoc]
  rw [Shape.Form.besselU, Subgroup.mem_subgroupOf, ← h_eq]
  exact conj_mem_unitriangular h_inv_tri hx.out

/-- A rational point lies in the unipotent group `besselU` iff its finite adelic image in the
lattice basis does. -/
@[simp]
lemma ratToFin_mem_besselU_iff {γ : S.G E} : S.ratToFin γ ∈ besselU ↔ γ ∈ besselU := by
  have h_entry (i j : 𝔰.BesselIndex) :
      (S.toLatticeBasis.symm (S.ratToFin γ)).val i j = algebraMap E (𝔸f E) (γ.val i j) := by
    simp [ratToFin, adelicToFin, ratToAdelic, U.map]
  rw [← S.toLatticeBasis.apply_symm_apply (S.ratToFin γ), toLatticeBasis_mem_besselU]
  -- The conditions on the entries are reflected by the injective map `E → 𝔸f E`.
  have h_one (i j : 𝔰.BesselIndex) : (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E)) i j =
      algebraMap E (𝔸f E) ((1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) i j) := by
    simp [Matrix.one_apply, apply_ite]
  simp only [mem_besselU, h_entry, h_one, (algebraMap E (𝔸f E)).injective.eq_iff]

/-- The inclusion `S.inclHFin` of the finite adelic points of the unitary group of `X₀` lands in
`besselH`, the isometries that fix the basis vectors outside `κ`. -/
lemma inclHFin_mem_besselH (k : U 1) : S.inclHFin k ∈ besselH := by
  simp [besselLatticeBasis, floorGroup, inclHFin, toLatticeBasis, Subgroup.mem_subgroupOf,
    val_toBesselH_apply_coe, fromBlocks_multiply, fromCols_mul_fromBlocks, Matrix.one_apply]

/-- The image of `S.inclHFin`, the inclusion of the finite adelic points of the unitary group of
`X₀ = span κ` in the lattice basis, is the group `besselH` of isometries that fix the basis vectors
outside `κ`. -/
lemma range_inclHFin : S.inclHFin.range = besselH := by
  refine le_antisymm (Set.range_subset_iff.2 inclHFin_mem_besselH) fun x hx ↦ ?_
  -- In rational coordinates `x` still fixes the basis vectors outside `κ`, as `S.latticeBasis` and
  -- its inverse do (the two goals left by `mul_mem`), so it comes from `toBesselH`.
  have h_mem : S.toLatticeBasis.symm x ∈ besselH := by
    apply mul_mem (mul_mem _ hx.out) <;> aesop (add simp Matrix.one_apply)
  obtain ⟨k, hk⟩ : ∃ k : Gf E 𝔰.κ, S.toLatticeBasis.symm x = toBesselH 𝔰 (S.N : 𝔸f E) k :=
    exists_eq_toBesselH h_mem (by simp [← piN_mul_star])
  exact ⟨k, S.toLatticeBasis.eq_symm_apply.1 hk.symm⟩

/-- The finite image of the rational `toBesselH` of `γ ∈ U(X₀)` is the inclusion `S.inclHFin` of the
finite adelic image of `γ`. -/
lemma ratToFin_toBesselH (γ : U 1) :
    S.ratToFin (toBesselH 𝔰 (S.N : E) γ) = S.inclHFin (stdEmbFin γ) := by
  ext
  simp [stdSpace_embFin γ, coe_ratToFin, val_toBesselH_apply_coe, fromBlocks_map, inclHFin,
    toLatticeBasis]

/-- For a class `c`, let h be the image under `toBesselH` of the chosen element `c.out` of the
double coset `c`, in rational coordinates. This is the finite adelic matrix h · `S.latticeBasis`.
Its columns form a basis of hΛ₀, where Λ₀ is the lattice spanned by the columns of
`S.latticeBasis`. -/
noncomputable def classBasis (c : S.Classes) : GL 𝔰.BesselIndex (𝔸f E) :=
  (toBesselH 𝔰 (S.N : 𝔸f E) c.out).val * S.latticeBasis

lemma classBasis_eq_latticeBasis_mul_classRep (c : S.Classes) :
    classBasis c = S.latticeBasis * (S.classRep c).val := by
  simp [classBasis, classRep, inclHFin, toLatticeBasis, mul_assoc]

/-- The matrix of `S.translateByClassReps c c' γ` is `B_c⁻¹ γ B_c'`, with `B_c = classBasis c`. -/
lemma coe_translateByClassReps (c c' : S.Classes) (γ : S.G E) :
    (S.translateByClassReps c c' γ).val =
      (classBasis c)⁻¹ * GeneralLinearGroup.map (algebraMap E (𝔸f E)) γ.val * classBasis c' := by
  simp only [classBasis_eq_latticeBasis_mul_classRep, translateByClassReps, Subgroup.coe_mul,
    InvMemClass.coe_inv, coe_ratToFin, _root_.mul_inv_rev, mul_assoc]

/-- The chosen representative `h_c = S.classRep c` of a class lies in `besselS`, as it lies in
`besselH`. -/
lemma classRep_mem_besselS (c : S.Classes) : S.classRep c ∈ besselS :=
  mem_partialUnitriangularGroup_of_mem_floorGroup (inclHFin_mem_besselH c.out)

/-- If a rational `γ` lies in `besselU`, then so does `h_c⁻¹ γ h_c = S.translateByClassReps c c
γ`. -/
lemma _root_.Membership.mem.translateByClassReps_mem_besselU {γ : S.G E} (c : S.Classes)
    (hγ : γ ∈ besselU) : S.translateByClassReps c c γ ∈ besselU :=
  -- `besselS` normalises `besselU`.
  (besselS_le_normalizer_besselU (inv_mem (classRep_mem_besselS c)) _).1
    (ratToFin_mem_besselU_iff.2 hγ)

/-- The product of a term over `(c, s, c')` and a term over `(c', t, c'')` is a term over
`(c, s * t, c'')`. -/
lemma termsOver.mul {c : S.Classes} {s : S.ResidueGL} {c' : S.Classes} {t : S.ResidueGL}
    {c'' : S.Classes} {γ δ : S.G E} (hγ : γ ∈ S.termsOver c s c') (hδ : δ ∈ S.termsOver c' t c'') :
    γ * δ ∈ S.termsOver c (s * t) c'' := by
  obtain ⟨(k : S.latticeStabilizer), rfl, hk⟩ := hγ
  obtain ⟨(k' : S.latticeStabilizer), rfl, hk'⟩ := hδ
  exact ⟨k * k', map_mul .., by simp [hk, hk', translateByClassReps, mul_assoc]⟩

/-- The inverse of a term over `(c, s, c')` is a term over `(c', s⁻¹, c)`. -/
lemma termsOver.inv {c : S.Classes} {s : S.ResidueGL} {c' : S.Classes} {γ : S.G E}
    (hγ : γ ∈ S.termsOver c s c') : γ⁻¹ ∈ S.termsOver c' s⁻¹ c := by
  obtain ⟨(k : S.latticeStabilizer), rfl, hk⟩ := hγ
  exact ⟨k⁻¹, map_inv .., by simp [hk, translateByClassReps, mul_assoc]⟩

/-! ### The unipotent transformation law -/

/-- Let `u` be an adelic point of the unitary group of the filling data `S`, and let
`σ = simpleRootSum` be the sum of the entries just above the diagonal on the frame e₁, …, e_ϱ, z.
The value of `σ` at `S.adelicToFin u`, the finite part of `u` written in the lattice basis, is the
finite part (the second component) of the adele `σ(u)`. -/
@[local simp]
lemma simpleRootSum_adelicToFin (u : S.G (𝔸 E)) :
    simpleRootSum (S.adelicToFin u) = (simpleRootSum u).2 := by
  -- Conjugation by the lattice basis does not change the entries just above the diagonal.
  have h_entry (a : Fin 𝔰.ϱ) :
      (S.adelicToFin u).val (𝔰.besselFrame a.castSucc) (𝔰.besselFrame a.succ) =
        (u.val (𝔰.besselFrame a.castSucc) (𝔰.besselFrame a.succ)).2 := by
    cases a.succ using Fin.lastCases <;>
      simp [adelicToFin, besselLatticeBasis, mul_apply, U.map, toLatticeBasis, Matrix.one_apply]
  simp only [simpleRootSum, snd_sum, h_entry]

/-- The sum of the entries just above the diagonal on the frame commutes with the embedding of
`E` in the adeles. -/
@[simp]
lemma simpleRootSum_ratToAdelic (u : S.G E) :
    simpleRootSum (S.ratToAdelic u) = ↑(simpleRootSum u) :=
  (map_sum (toAdele (E := E)) _ _).symm

@[simp]
lemma norm_selfDualChar {x : 𝔸f E} : ‖S.selfDualChar x‖ = 1 := norm_coe _

/-- If a rational `γ` agrees with the identity matrix at the entries `(i, j)` with `r i j`, then so
does each component of its archimedean image `S.ratToInf γ`. -/
lemma _root_.Membership.mem.ratToInf_mem_agreeWithOneOn {γ : S.G E}
    {r : 𝔰.BesselIndex → 𝔰.BesselIndex → Prop}
    {hr : ∀ i k j : 𝔰.BesselIndex, r i j → r i k ∨ r k j}
    (hγ : γ ∈ (agreeWithOneOn r E hr).subgroupOf (S.G E)) (v : InfinitePlace E) :
    S.ratToInf γ v ∈ (agreeWithOneOn r ℂ hr).subgroupOf 𝔰.G₁ := by
  aesop (add simp [Subgroup.mem_subgroupOf, Matrix.one_apply])

variable (S) in
/-- For adelic `x` and an infinite place `v`, `simpleRootSum (S.adelicToInf x v)` is the sum of the
entries just above the diagonal of the block on `(e_0, …, e_{ϱ-1}, z)` of the rescaled `v`-component
of `x`. It equals `-2πi` times the `v`-component of `-simpleRootSum x / (M ϖ)`. Here `M = S.M` is
the level and `ϖ = S.deltaE` generates the different of `E`. -/
lemma simpleRootSum_adelicToInf (x : S.G (𝔸 E)) (v : InfinitePlace E) :
    simpleRootSum (S.adelicToInf x v) =
      -π * 2 * .I * (toAdele (-(S.M * S.deltaE : E)⁻¹) * simpleRootSum x).1 v := by
  have h_entry (a : Fin 𝔰.ϱ) :
      (S.adelicToInf x v).val (𝔰.besselFrame a.castSucc) (𝔰.besselFrame a.succ) =
        (x.val (𝔰.besselFrame a.castSucc) (𝔰.besselFrame a.succ)).1 v * (S.realM v : ℂ)⁻¹ := by
    have h_exp : 𝔰.ϱ - (a.castSucc : ℕ) = 𝔰.ϱ - (a.succ : ℕ) + 1 := by grind
    simp only [adelicToInf_apply, basisScale_besselFrame, h_exp]
    have hN : (√S.N : ℂ) ≠ 0 := by simp [S.N_prime.ne_zero]
    simp [field, pow_succ']
  simp only [simpleRootSum, h_entry, ← sum_mul]
  simp [fst_sum, Finset.sum_apply, coe_realM, field, mul_assoc]

variable (S) in
/-- Let `σ = New.simpleRootSum` be the sum of the entries just above the diagonal on the frame e₁,
…, e_ϱ, z, let `x` be an adelic point, and let `c_v = σ (S.adelicToInf x v)` be the value of `σ` at
the component of `x` at `v`, written in the basis rescaled by `S.basisScale v`. Let `ψ` be the
standard character of the adeles and `ψ_f` its finite part, `M = S.M` the level, the product of the
two primes `S.levelPrime i`, and `ϖ = S.deltaE` the generator of the different of `E`. The product
of the numbers `wave c_v = exp (c_v - c̄_v)` over the infinite places is `ψ(-σ(x) / (M ϖ))` divided
by `S.unipotentChar x_f = ψ_f(-σ(x_f) / (M ϖ))`, where `x_f = S.adelicToFin x` is the finite part of
`x`; that is, it is the archimedean factor of `ψ(-σ(x) / (M ϖ))`. -/
lemma prod_wave_simpleRootSum_adelicToInf (x : S.G (𝔸 E)) :
    ∏ v : InfinitePlace E, wave (simpleRootSum (S.adelicToInf x v)) =
      New.stdAddChar E (toAdele (-(S.M * S.deltaE : E)⁻¹) * simpleRootSum x) /
        S.unipotentChar (S.adelicToFin x) := by
  set z : 𝔸 E := toAdele (-(S.M * S.deltaE : E)⁻¹) * simpleRootSum x with hz
  -- The finite factor of `ψ(z)` is `unipotentChar`, so the quotient is the archimedean factor.
  have h_fin : S.unipotentChar (S.adelicToFin x) = ψf E z.2 := by
    have h_arg : z.2 = algebraMap E (𝔸f E) (-(S.deltaE : E)⁻¹) *
        (algebraMap E (𝔸f E) (S.M : E)⁻¹ * (simpleRootSum x).2) := by
      rw [← mul_assoc, ← map_mul, neg_mul, ← mul_inv, mul_comm (S.deltaE : E)]
      rfl -- the finite component of a product of adeles is the product of the finite components
    have h_coe (t : Circle) : Circle.coeHom t = (t : ℂ) := rfl
    simp [h_arg, unipotentChar, selfDualChar, ideleM, h_coe]
  -- With `c = -2πi z_v` one has `c - c̄ = -2πi · 2 Re z_v`.
  have h_arch (v : InfinitePlace E) : wave (simpleRootSum (S.adelicToInf x v)) =
      Complex.exp (↑(2 * π * -(2 * (z.1 v).re)) * .I) := by
    rw [S.simpleRootSum_adelicToInf x v, ← hz, wave, sub_conj]
    simp [mul_assoc]
  have h_split : New.stdAddChar E z =
      fourierChar (-∑ v : InfinitePlace E, 2 * (z.1 v).re) * ψf E z.2 := rfl
  rw [h_fin, h_split, Circle.coe_mul, mul_div_cancel_right₀ _ (Circle.coe_ne_zero _),
    fourierChar_apply]
  simp only [h_arch, ← Complex.exp_sum, ← sum_mul, ← ofReal_sum, ← mul_sum, sum_neg_distrib]

variable (S) in
/-- For a rational point `γ`, take the product of `wave (simpleRootSum (S.ratToInf γ v))` over the
infinite places `v`; this is the character of `besselU` at infinity. It equals the complex conjugate
of the finite character `S.unipotentChar` at `S.ratToFin γ`, the finite adelic image of `γ`. -/
lemma prod_wave_simpleRootSum_ratToInf (γ : S.G E) :
    ∏ v : InfinitePlace E, wave (simpleRootSum (S.ratToInf γ v)) =
      star (S.unipotentChar (S.ratToFin γ)) := by
  let z : 𝔸 E := toAdele (-(S.M * S.deltaE : E)⁻¹) * simpleRootSum (S.ratToAdelic γ)
  -- The adelic character is trivial on the rational element `z`.
  have h_trivial : New.stdAddChar E z = 1 := by
    simp only [z, simpleRootSum_ratToAdelic, ← map_mul, stdAddChar_toAdele]
  calc _ = New.stdAddChar E z / S.unipotentChar (S.ratToFin γ) :=
      S.prod_wave_simpleRootSum_adelicToInf (S.ratToAdelic γ)
    _ = star (S.unipotentChar (S.ratToFin γ)) := by
      rw [h_trivial, Circle.coe_one, one_div]
      exact Complex.inv_eq_conj norm_selfDualChar

/-- Let `x` be an adelic point in the unipotent group `besselU`. Left translation by
`S.adelicToInf x`, the rescaled infinite components of `x`, multiplies the Bessel function
`S.besselFn side` (full or cut) by a scalar. This scalar is the character of `besselU` at infinity:
the product of `wave (simpleRootSum (S.adelicToInf x v))` over the infinite places `v`. -/
lemma besselFn_adelicToInf_mul_eq_prod_wave_smul {x : S.G (𝔸 E)} {side : FullOrCut}
    (hx : x ∈ besselU) (y : InfinitePlace E → 𝔰.G₁) :
    S.besselFn side (S.adelicToInf x * y) =
      (∏ v : InfinitePlace E, wave (simpleRootSum (S.adelicToInf x v))) • S.besselFn side y := by
  -- Each local Bessel function transforms by `wave c = exp (c - c̄)` under the unipotent group,
  -- which contains every component of `S.adelicToInf x`.
  have h_inf (v : InfinitePlace E) : S.adelicToInf x v ∈ besselU :=
    conj_mem_unitriangular (blockTriangular_diagonal _) (hx.map_mem_agreeWithOneOn _)
  have h_loc (v : InfinitePlace E) (g : 𝔰.G₁) :
    (S.besselSystem v).besselFn side (S.adelicToInf x v * g) =
      wave (simpleRootSum (S.adelicToInf x v)) • (S.besselSystem v).besselFn side g :=
    ((S.besselSystem v).isCutPair.isBesselFunction side).2 _ (h_inf v) g
  funext i
  simp [besselFn, h_loc, prod_mul_distrib]

/-- For rational `γ` in the unipotent group, left translation by the archimedean image of `γ`
multiplies the Bessel function `S.besselFn side` by the inverse of the finite character
`New.Filling.unipotentChar` of the finite image of `γ`. -/
lemma besselFn_ratToInf_mul {γ : S.G E} {side : FullOrCut} (hγ : γ ∈ besselU)
    (y : InfinitePlace E → 𝔰.G₁) :
    S.besselFn side (S.ratToInf γ * y) =
      (S.unipotentChar (S.ratToFin γ))⁻¹ • S.besselFn side y := by
  have h_inv : (S.unipotentChar (S.ratToFin γ))⁻¹ = star (S.unipotentChar (S.ratToFin γ)) :=
    Complex.inv_eq_conj norm_selfDualChar
  rw [h_inv, ← prod_wave_simpleRootSum_ratToInf]
  exact besselFn_adelicToInf_mul_eq_prod_wave_smul (hγ.map_mem_agreeWithOneOn _) y

end New.Filling

/-!
## Unimodularity of the lattice form and Eichler maps in 𝖴

Matrix computations for the form `T.splitGram` of `ϱ` hyperbolic planes and a middle space with Gram
matrix `T`, over a commutative ring with involution.

The basis is `e₁, …, e_ϱ`, a basis of the middle space ending in `z`, and `e*₁, …, e*_ϱ`. The frame
is `f = (e₁, …, e_ϱ, z)`, and `h(x, y)` is `xᴴ J y`.
-/

namespace New

open scoped Classical in
/-- The weight of a head `p 0, …, p (i - 1)` at the finite places: the product over `l < i` of the
`K`-th power of `√(genIndex D)`, where `D = p 0 * ⋯ * p l` and `genIndex D` is the inverse of the
factor by which multiplication by `D` scales Haar measure. It is `0` unless all these partial
products lie in the ring of integers `SemilocalField.O`. -/
noncomputable def finHeadWeight {A : Type*} [SemilocalField A] (K i : ℕ) (p : ℕ → Aˣ) : ℝ :=
  ∏ l ∈ Finset.range i,
    let D : A := ∏ a ∈ Finset.range (l + 1), (p a).1
    if D ∈ SemilocalField.O then √(genIndex D) ^ K else 0

open Matrix Fin Sum Floors Finset

-- `Type _`: the universe is `0` in the statements about `simpleRootSum`, arbitrary in the others.
variable {A : Type _} [CommRing A]
  {R : Subring A} {𝔰 : Shape} {T : Shape.Form 𝔰 A}

/-- Let `R` be a subring of `A` and let `N ∈ R` be fixed by the involution. Then
`latticeMiddleGram 𝔰 N`, the Gram matrix of the middle space `X₀ ⊕ A z` in the lattice basis, is
hermitian and lies in `GL(R)`. -/
lemma isUnimodular_latticeMiddleGram [StarRing A] (𝔰 : Shape) {N : A} (hN : N ∈ R ∧ star N = N) :
    IsUnimodular R (latticeMiddleGram 𝔰 N) := by
  -- the inverse is the same matrix for `N = 0` with `N` put at the diagonal place `(k₀, k₀)`
  let inv : Matrix 𝔰.MiddleIndex 𝔰.MiddleIndex A :=
    latticeMiddleGram 𝔰 0 + diagonal (Pi.single (inl 𝔰.k₀) N)
  have h_inv : latticeMiddleGram 𝔰 N * inv = 1 := by
    aesop (add simp [inv, latticeMiddleGram, mul_apply, diagonal, Matrix.one_apply])
  -- hermitian, as `N` is fixed by `star`; the entries of both matrices are `0`, `±1`, `±N`
  have h_herm : (latticeMiddleGram 𝔰 N)ᴴ = latticeMiddleGram 𝔰 N := by
    aesop (add simp [latticeMiddleGram, diagonal])
  have h_mem (a b : 𝔰.MiddleIndex) : latticeMiddleGram 𝔰 N a b ∈ R ∧ inv a b ∈ R := by
    aesop (add simp [inv, latticeMiddleGram, diagonal])
  let u : GL 𝔰.MiddleIndex A := ⟨latticeMiddleGram 𝔰 N, inv, h_inv, mul_eq_one_comm.1 h_inv⟩
  exact ⟨h_herm, u, mem_intGL.2 ⟨fun a b ↦ (h_mem a b).1, fun a b ↦ (h_mem a b).2⟩, rfl⟩

/-- The combination of the frame vectors e₁, …, e_ϱ, z with coefficients `x` has `e`-coordinates
`init x`, `z`-coordinate the last coefficient, and all other coordinates zero. -/
lemma frameImage_one_mulVec {x : Fin (𝔰.ϱ + 1) → A} :
    frameImage (R := A) (𝔰 := 𝔰) 1 *ᵥ x = init x ⊕ᵥ ((0 ⊕ᵥ fun _ : Unit ↦ x 𝔰.top) ⊕ᵥ 0) :=
  funext (by simp [init, mulVec_eq_sum, sum_univ_castSucc, Matrix.one_apply])

/-- The combination of the columns of `γ` at the frame indices with coefficients `x` is the image
under `γ` of the same combination of the frame vectors. -/
lemma frameImage_mulVec (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) (x : Fin (𝔰.ϱ + 1) → A) :
    frameImage (R := A) (𝔰 := 𝔰) γ *ᵥ x = γ *ᵥ frameImage 1 *ᵥ x := by simp [← mul_inclMatrix]

variable [StarRing A]

/-- For an invertible hermitian matrix `J`, every row vector is `vᴴ J` for some `v`. -/
lemma exists_star_vecMul_eq (J : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) [hJ : IsHermitianUnit J]
    (l : 𝔰.BesselIndex → A) : ∃ v : 𝔰.BesselIndex → A, star v ᵥ* J = l := by
  refine ⟨star (l ᵥ* ↑hJ.isUnit.unit⁻¹), ?_⟩
  -- `-coe_units_inv` keeps the inverse as a unit, so that it cancels `J`.
  simp [-coe_units_inv]

/-- Let `J = T.splitGram` be hermitian and invertible, and `h(y, y') = yᴴ J y'`, conjugate-linear in
`y`. Let `f j = frameImage 1 *ᵥ j` be the combination of the frame vectors e₁, …, e_ϱ, z with
coefficients `j`, and put `x = r • f j`. Suppose `j b = 0` for `b ≥ a`, and that `v` is orthogonal
to the frame vectors of index below `a`. Let `τ = TraceOne.element` be the chosen element with
`τ + τ̄ = 1`, and `ς = τ h(v, v)`. Then the Eichler map `eichlerMap J x v ς : y ↦ y + h(v, y) x -
h(x, y) (v + ς x)` is an element `u` of the unipotent group `besselU`. Its `simpleRootSum`, the sum
of the entries just above the diagonal on the frame, is `r h(v, f j')`, where `j' = cons 0 (init j)`
is `j` shifted by one place. -/
lemma exists_mem_besselU_eq_eichlerMap {v : 𝔰.BesselIndex → A} [hJ : IsHermitianUnit T.splitGram]
    [TraceOne A] (a : Fin (𝔰.ϱ + 1)) (j : Fin (𝔰.ϱ + 1) → A) (r : A) {m : 𝔰.BesselIndex → A}
    (hm : star v ᵥ* T.splitGram = m) (hj : ∀ b : Fin (𝔰.ϱ + 1), a ≤ b → j b = 0)
    (hm_low : ∀ b : Fin (𝔰.ϱ + 1), b < a → m (𝔰.besselFrame b) = 0) :
    ∃ u : T.G, u ∈ T.besselU ∧
      -- (a) the sum of the entries of `u` at the simple roots
      simpleRootSum u = r * m ∘ 𝔰.besselFrame ⬝ᵥ Fin.cons 0 (init j) ∧
      -- (b) `u` is the Eichler map
      u.val.val = eichlerMap T.splitGram (r • frameImage 1 *ᵥ j) v
          (TraceOne.element * star v ⬝ᵥ T.splitGram *ᵥ v) := by
  -- The vector `x = r • frameImage 1 *ᵥ j` has only `e`-coordinates, as `hj` kills the one at `z`.
  -- So the form `h(x, ·)` reads only `e*`-coordinates, and vanishes at `x` and on the frame.
  set x : 𝔰.BesselIndex → A := r • frameImage 1 *ᵥ j
  set ς : A := TraceOne.element * star v ⬝ᵥ T.splitGram *ᵥ v
  have hx : x = (fun b ↦ r * j b.castSucc) ⊕ᵥ 0 := by
    simp [x, frameImage_one_mulVec, funext_iff, init, hj _ (le_last a)]
  have hx_form : star x ᵥ* T.splitGram =
      (0 ⊕ᵥ (0 ⊕ᵥ fun b ↦ star (r * j b.castSucc)) : 𝔰.BesselIndex → A) := by
    simp [hx, funext_iff, splitGram, vecMul, dotProduct, Matrix.one_apply]
  -- `m (besselFrame c)` is the conjugate of the `e*_c`-coordinate of `v`. For `c ≤ b` either
  -- `a ≤ b`, and `j b = 0`, or `c < a`, and that coordinate is `0`.
  have h_low (b c : Fin 𝔰.ϱ) (hcb : c ≤ b) : j b.castSucc = 0 ∨ v (inr (inr c)) = 0 := by
    refine (le_or_gt a b.castSucc).imp (hj _) fun hb ↦ ?_
    simpa [← hm, splitGram, vecMul, dotProduct, Matrix.one_apply] using hm_low c.castSucc (by grind)
  have hxx : star x ⬝ᵥ T.splitGram *ᵥ x = 0 := by
    simp [hx, splitGram, mulVec, dotProduct]
  have hvx : star v ⬝ᵥ T.splitGram *ᵥ x = 0 := by
    have h_term (b : Fin 𝔰.ϱ) : star (v (inr (inr b))) * (r * j b.castSucc) = 0 := by
      obtain h | h := h_low b b le_rfl <;> simp [h]
    simp [hx, splitGram, mulVec, dotProduct, Matrix.one_apply, h_term]
  have hς : ς + star ς = star v ⬝ᵥ T.splitGram *ᵥ v := by
    simp [ς, star_dotProduct_mulVec_comm hJ.conjTranspose_eq, ← add_mul]
  obtain ⟨u, hu⟩ := exists_unitary_eq_eichlerMap hJ.conjTranspose_eq hxx hvx hς
  refine ⟨u, ?_, ?_, hu⟩
  · -- block by block, the entries on and below the diagonal are those of `1`, by `h_low`
    suffices h_below : ∀ p q : 𝔰.BesselIndex, BesselIndex.level q ≤ BesselIndex.level p →
        eichlerMap T.splitGram x v ς p q = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) p q by
      simpa [mem_besselU, hu] using h_below
    simp [eichlerMap, hx, vecMulVec, BesselIndex.level, splitGram, vecMul, dotProduct,
      Matrix.one_apply, sub_eq_zero]
    -- each product left contains `j b` and `v (e*_c)` with `c ≤ b`, so one factor is zero
    grind [star_zero]
  · have h_entry (b : Fin 𝔰.ϱ) : u.val (𝔰.besselFrame b.castSucc) (𝔰.besselFrame b.succ) =
        r * m (𝔰.besselFrame b.succ) * j b.castSucc := by
      rw [hu, eichlerMap, hx_form, hx, hm]
      -- `b.succ` is the index of `z` or of some `e_c`.
      cases hb : b.succ using lastCases <;> simp [vecMulVec, Matrix.one_apply] <;> grind
    simp only [simpleRootSum, h_entry]
    simp [dotProduct, sum_univ_succ, mul_sum, init, mul_assoc]

end New

/-!
## The idele M, the self-dual character and the level subgroup K(M)

The global data `S` are translated into the terms of the abstract local theory over the pair
`Ô E ⊆ 𝔸f E` of integral and all finite adeles.
-/

namespace New.Filling

open Matrix Circle intGL Floors IsHermitianUnit

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} (S : Filling E 𝔰) {F : Type} [CommRing F]

/-- The middle block `S.latticeMiddle F` of the form in the lattice basis, over a ring `F` with
involution, is hermitian and lies in `GL(R)` for every subring `R` of `F`. -/
lemma isUnimodular_latticeMiddle [StarRing F] {R : Subring F} :
    IsUnimodular R (S.latticeMiddle F) := by
  simp [isUnimodular_latticeMiddleGram]

instance [StarRing F] : IsHermitianUnit (S.latticeMiddle F) := by
  obtain ⟨h_herm, u, -, hu⟩ : IsUnimodular ⊤ (S.latticeMiddle F) := S.isUnimodular_latticeMiddle
  exact ⟨h_herm, u, hu⟩

/-- The Gram matrix of the whole form in the lattice basis is symmetric. -/
lemma transpose_splitGram : (S.latticeMiddle F).splitGramᵀ = (S.latticeMiddle F).splitGram := by
  -- For the trivial involution on `F`, hermitian means symmetric.
  let : StarRing F := starRingOfComm
  exact (conjTranspose_eq : (S.latticeMiddle F).splitGramᴴ = (S.latticeMiddle F).splitGram)

/-- The inverse adjoint s ↦ J⁻¹s⁻ᵀJ, an automorphism of the general linear group over F; J is the
Gram matrix in the lattice basis. -/
def invAdjoint : MulAut (Matrix 𝔰.BesselIndex 𝔰.BesselIndex F)ˣ :=
  letI : StarRing F := starRingOfComm
  MulAut.conj (isUnit (J := (S.latticeMiddle F).splitGram)).unit⁻¹ * invTransposeGL

/-- The automorphism s ↦ J⁻¹s⁻ᵀJ of the general linear group over F if b is true, else the
identity; J is the Gram matrix in the lattice basis. -/
def idOrInvAdjoint (b : Bool) : MulAut (Matrix 𝔰.BesselIndex 𝔰.BesselIndex F)ˣ :=
  if b then S.invAdjoint else 1

lemma idOrInvAdjoint_false : S.idOrInvAdjoint (F := F) false = 1 := rfl

lemma idOrInvAdjoint_true : S.idOrInvAdjoint (F := F) true = S.invAdjoint := rfl

/-- For a chosen place w, of norm p₀ or p₁, and a Boolean, the ring homomorphism from the integral
finite adeles to the residue field at w: reduction modulo w, preceded by conjugation if the Boolean
is true. -/
def reduceAboveM (x : (Σ i : Fin 2, S.chosenPlaces i) × Bool) :
    Ô E →+* ResField (x.1.snd : FinPlace E) :=
  if x.2 then (reduceAt (x.1.snd : FinPlace E)).comp (starRingEnd (Ô E))
  else reduceAt (x.1.snd : FinPlace E)

lemma reduceAboveM_false (p : Σ i : Fin 2, S.chosenPlaces i) :
    S.reduceAboveM (p, false) = reduceAt (p.snd : FinPlace E) := rfl

lemma reduceAboveM_true (p : Σ i : Fin 2, S.chosenPlaces i) :
    S.reduceAboveM (p, true) = (reduceAt (p.snd : FinPlace E)).comp (starRingEnd (Ô E)) := rfl

/-- Every element of `S.latticeStabilizer`, the group of integral finite adelic isometries, is the
image of a unitary matrix over the ring `Ô E` of integral finite adeles. -/
lemma exists_map_eq_of_mem_latticeStabilizer {k : S.GFin} (hk : k ∈ S.latticeStabilizer) :
    ∃ g : (S.latticeMiddle (Ô E)).G,
      U.map (Ô E).subtype coe_star_Ô (S.map_splitGram_latticeMiddle (Ô E).subtype) g = k := by
  obtain ⟨k₀, hk₀⟩ :
      ∃ k₀ : GL 𝔰.BesselIndex (Ô E), GeneralLinearGroup.map (Ô E).subtype k₀ = k := hk
  obtain ⟨g, -, hg⟩ := U.mem_range_map coe_star_Ô (Ô E).subtype_injective isUnit
    (S.map_splitGram_latticeMiddle (Ô E).subtype) (congrArg Units.val hk₀)
  exact ⟨g, hg⟩

/-- Let `k` be an integral finite adelic isometry, `i : Fin 2`, `w` a place in `S.chosenPlaces i`
and `b` a Boolean. The image of `k` under `S.reduceAboveM (⟨i, w⟩, b)`, applied entrywise by
`intGL.map`, is `S.idOrInvAdjoint b` applied to the reduction `S.reduction k i w` of `k` at `w`. -/
lemma intGL_map_reduceAboveM (k : S.latticeStabilizer) (i : Fin 2) (w : S.chosenPlaces i)
    (b : Bool) :
    intGL.map (S.reduceAboveM (⟨i, w⟩, b)) ⟨k, k.2⟩ = S.idOrInvAdjoint b (S.reduction k i w) := by
  cases b
  · rfl
  obtain ⟨k, hk⟩ := k
  obtain ⟨g, rfl⟩ := S.exists_map_eq_of_mem_latticeStabilizer hk
  set k : S.latticeStabilizer :=
    ⟨U.map (Ô E).subtype coe_star_Ô (S.map_splitGram_latticeMiddle (Ô E).subtype) g, hk⟩
  let A : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (Ô E) := g
  let A_inv : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (Ô E) := (g⁻¹ : (S.latticeMiddle (Ô E)).G)
  let p : FinPlace E := w
  let J : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (ResField p) :=
    (S.latticeMiddle (ResField p)).splitGram
  -- Transpose `Aᴴ J = J A⁻¹` and reduce it modulo `w`; the Gram matrix `J` is symmetric.
  have h_unitary : J * Aᴴᵀ.map (reduceAt p) = A_invᵀ.map (reduceAt p) * J := by
    have h_form : (Aᴴ * (S.latticeMiddle (Ô E)).splitGram)ᵀ.map (reduceAt p) =
        ((S.latticeMiddle (Ô E)).splitGram * A_inv)ᵀ.map (reduceAt p) := by
      rw [U.form_mul_inv_eq]
    simpa only [transpose_mul, Matrix.map_mul, transpose_splitGram, map_splitGram_latticeMiddle]
      using h_form
  have h_conj : (intGL.map (S.reduceAboveM (⟨i, w⟩, true)) ⟨k, k.2⟩).val =
      Aᴴᵀ.map (reduceAt p) := rfl
  have h_inv : (invTransposeGL (S.reduction k i w)).val = A_invᵀ.map (reduceAt p) := rfl
  rw [idOrInvAdjoint_true, invAdjoint, MulAut.mul_apply, MulAut.conj_apply, inv_inv, mul_assoc,
    eq_inv_mul_iff_mul_eq, Units.ext_iff]
  -- both sides are now the products in `h_unitary`
  simpa only [Units.val_mul, h_conj, h_inv, IsUnit.unit_spec] using h_unitary

lemma ideleM_val : S.ideleM.val = S.M := by simp [ideleM]

lemma ideleM_mem : (S.ideleM : 𝔸f E) ∈ Ô E := by simp [ideleM, mul_mem]

/-- The ring `Ô E` of integral finite adeles is self-dual for the character
`S.selfDualChar : x ↦ ψ_f(-x / ϖ)`, where `ψ_f` is the finite part of the standard additive
character and `ϖ` is the chosen generator of the different of `E`: the character is trivial on
`Ô E * a` iff `a` is integral. -/
lemma forall_selfDualChar_mul_eq_one_iff (a : 𝔸f E) :
    (∀ r : Ô E, S.selfDualChar (r * a) = 1) ↔ a ∈ Ô E := by
  set x : 𝔸f E := algebraMap E (𝔸f E) (-(S.deltaE : E)⁻¹) * a with hx
  have h_char (r : 𝔸f E) : S.selfDualChar (r * a) = 1 ↔ ψf E (r * x) = 1 := by
    simp [hx, mul_left_comm r, selfDualChar, map_eq_one_iff coeHom @Circle.ext]
  -- The different is generated by `ϖ`, which cancels the factor `ϖ⁻¹` in `x`.
  have h_cancel (r : NumberField.RingOfIntegers E) :
      algebraMap E (𝔸f E) ↑(r * S.deltaE) * x = -(r • a) := by
    rw [hx, ← mul_assoc, ← map_mul]
    simp [Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  calc
    _ ↔ ∀ r ∈ Ô E, ψf E (r * x) = 1 := by simp only [h_char, Subtype.forall]
    _ ↔ ∀ d ∈ Ideal.span {S.deltaE}, algebraMap E (𝔸f E) d * x ∈ Ô E := by
      rw [forall_ψf_mul_eq_one_iff, S.span_deltaE]
    _ ↔ ∀ r : NumberField.RingOfIntegers E, r • a ∈ Ô E := by
      simp only [Ideal.mem_span_singleton', forall_exists_index, forall_apply_eq_imp_iff, h_cancel,
        neg_mem_iff]
    _ ↔ a ∈ Ô E := ⟨fun h ↦ by simpa using h 1, fun ha r ↦ mul_mem (coe_mem_Ô r) ha⟩

lemma selfDualChar_eq_one_of_mem (x : 𝔸f E) (hx : x ∈ Ô E) : S.selfDualChar x = 1 := by
  simpa using (S.forall_selfDualChar_mul_eq_one_iff x).2 hx 1

/-- For an integral finite adele `r` and the level `M`, seen as the idele `S.ideleM`, the adele
`M⁻¹ r` is integral iff `r` and its conjugate reduce to `0` at every chosen place; these reductions
are the maps `S.reduceAboveM x`. -/
lemma inv_ideleM_smul_mem_iff (r : Ô E) :
    S.ideleM⁻¹ • (r : 𝔸f E) ∈ Ô E ↔
      ∀ x : ((i : Fin 2) × S.chosenPlaces i) × Bool, S.reduceAboveM x r = 0 := by
  -- `M⁻¹ r` is integral iff `M` divides `r` in `Ô E`, and `M_dvd_iff` describes this by the places.
  have h_coe : ((S.levelPrime 0 * S.levelPrime 1 : ℕ) : Ô E) = (S.ideleM : 𝔸f E) := by
    simp [ideleM_val, -Nat.cast_mul]
  have h_dvd : S.ideleM⁻¹ • (r : 𝔸f E) ∈ Ô E ↔
      ((S.levelPrime 0 * S.levelPrime 1 : ℕ) : Ô E) ∣ r := by
    simp only [dvd_def, Subtype.ext_iff, MulMemClass.coe_mul, h_coe, Units.smul_def, smul_eq_mul,
      ← S.ideleM.inv_mul_eq_iff_eq_mul, Subtype.exists, exists_prop, exists_eq_right']
  simp only [h_dvd, S.M_dvd_iff r, Prod.forall, Bool.forall_bool, reduceAboveM_false,
    reduceAboveM_true, RingHom.comp_apply, starRingEnd_apply]

/-- An integral finite adelic isometry `k` reduces to `1` at all chosen places iff `k` is congruent
to `1` modulo the level `M = S.ideleM`, that is, `M⁻¹ (k - 1)` has integral entries. -/
lemma reduction_eq_one_iff (k : S.latticeStabilizer) :
    S.reduction k = 1 ↔ IsIntMatrix (Ô E)
      (S.ideleM⁻¹ • (((k : S.GFin) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E)) - 1)) := by
  let k' : intGL 𝔰.BesselIndex (Ô E) := ⟨k, k.2⟩
  calc
    -- At a conjugate place the reduction is the inverse adjoint of the one at the place itself.
    _ ↔ ∀ (i : Fin 2) (w : S.chosenPlaces i) (b : Bool),
        S.idOrInvAdjoint b (S.reduction k i w) = 1 := by
      simp only [EmbeddingLike.map_eq_one_iff, forall_const, funext_iff, Pi.one_apply]
    _ ↔ ∀ x : (Σ i : Fin 2, S.chosenPlaces i) × Bool, intGL.map (S.reduceAboveM x) k' = 1 := by
      simp only [Prod.forall, Sigma.forall, ← intGL_map_reduceAboveM, k']
    _ ↔ ∀ (a b : 𝔰.BesselIndex) (x : (Σ i : Fin 2, S.chosenPlaces i) × Bool),
        S.reduceAboveM x (toMatrix k' a b - toMatrix 1 a b) = 0 := by
      simp only [intGL.map_eq_one, forall_comm (α := (Σ i : Fin 2, S.chosenPlaces i) × Bool)]
    _ ↔ _ := forall₂_congr fun a b ↦ by
      rw [← inv_ideleM_smul_mem_iff]
      by_cases hab : a = b <;> simp [k', toMatrix, hab, Units.smul_def]

/-- The image `S.principalLevel` of the kernel of the reduction at the chosen places equals
`unitaryLevel`: the isometries of the Gram matrix `(S.latticeMiddle (𝔸f E)).splitGram` that are
integral over `Ô E` and congruent to `1` modulo the level `M = S.ideleM`. -/
lemma principalLevel_eq_unitaryLevel :
    S.principalLevel = unitaryLevel (Ô E) S.ideleM (S.latticeMiddle (𝔸f E)).splitGram := by
  refine le_antisymm ?_ fun k ⟨hk, h_congr⟩ ↦
    ⟨⟨k, hk⟩, (S.reduction_eq_one_iff ⟨k, hk⟩).2 h_congr, rfl⟩
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k.property, (S.reduction_eq_one_iff k).1 hk⟩

end New.Filling

/-!
## Strong approximation for 𝖴, rational terms of given reduction, and freeness

* `New.Filling.unipotentChar_eq_of_mem_principalLevel`,
  `New.Filling.exists_rat_approx_unipotentChar_eq`: approximation keeps the character
  `S.unipotentChar`.
-/

section UnipotentApproximation

open NumberField Matrix Subgroup Fintype Set New Floors TraceOne Fact IsHermitianUnit FloorGroups
  Function RingHom

section Density

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {𝔰 : Shape}

/-- The element `1 / 2` of the finite adeles has trace one. -/
noncomputable instance : TraceOne (𝔸f E) where
  element := (2⁻¹ : E)
  element_add_star := by norm_num [← map_add]

/-- The Heisenberg element `heisenbergElem a p` of floor `a` over the finite adeles is a continuous
function of its parameter `p`, a pair of a vector and a skew element. -/
lemma New.continuous_heisenbergElem_finAdele {T : 𝔰.Form (𝔸f E)} [IsHermitianUnit T.splitGram]
    (a : Fin 𝔰.ϱ) : Continuous (heisenbergElem (T := T) a) := by
  rw [(U.isClosedEmbedding_coe isUnit).continuous_iff]
  simp [comp_def, heisenbergElem, eichlerMap]
  fun_prop

/-- The skew elements `t - t̄` with `t ∈ E` are dense in the skew finite adeles. -/
lemma New.denseRange_skewPart_algebraMap :
    DenseRange fun t : E ↦ skewPart (algebraMap E (𝔸f E) t) := by
  -- A skew element `β` is the skew part of `τ β`, as `τ + τ̄ = 1`.
  have h_onto : Surjective (skewPart : 𝔸f E → skewAdjoint (𝔸f E)) :=
    fun β ↦ ⟨element * (β : 𝔸f E), by simp [skewPart, ← add_mul]⟩
  exact h_onto.denseRange.comp denseRange_algebraMap_finAdele (by fun_prop)

/-- Let `T` be an invertible hermitian middle block over `E`, and `T'` one over the finite adeles
`𝔸f E` whose Gram matrix `T'.splitGram` is the image of `T.splitGram` (`hT`). Take `a < 𝔰.ϱ`, the
index of a hyperbolic pair (e_a, e*_a). Let `v` be a vector on the basis indices `i` with
`floorOf i ≥ a + 1`. Let `β` be skew. Then `heisenbergElem a (v, β)` is the Eichler map with
e*_a ↦ e*_a + v + (β - h(v, v) / 2) e_a. The map from rational to finite adelic isometries sends the
element for `T` with parameter `(v, skewPart t)`, where `skewPart t = t - t̄`, to the element for
`T'` whose parameter is the image of `(v, t - t̄)` in `𝔸f E`. -/
lemma New.map_heisenbergElem_finAdele {T : 𝔰.Form E} [IsHermitianUnit T] {T' : 𝔰.Form (𝔸f E)}
    [IsHermitianUnit T'.splitGram] (hT : T.splitGram.map (↑) = T'.splitGram) (a : Fin 𝔰.ϱ)
    (v : {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → E) (t : E) :
    (U.map (algebraMap E (𝔸f E)) (h := hT)) (heisenbergElem (T := T) a (v, skewPart t)) =
      heisenbergElem (T := T') a (fun i ↦ (v i : 𝔸f E), skewPart (t : 𝔸f E)) := by
  -- Both sides are the same polynomial expression in `v`, `t`, `τ = 1 / 2` and the Gram matrix.
  ext
  simp [inclMatrix, U.map, heisenbergElem, eichlerMap, ← hT, vecMulVec, vecMul, dotProduct, mulVec,
    apply_ite (algebraMap E (𝔸f E)), apply_ite star, element, -sum_sum_type,
    -splitGram_eq_ite_oppositeIndex, Pi.single_apply, Matrix.one_apply]

/-- Strong approximation for the unipotent group 𝖴 = `besselU` of the form made of ϱ hyperbolic
planes and a middle block. Let `T` be an invertible hermitian middle block over `E`, and `T'` one
over the finite adeles whose Gram matrix is the image of that of `T`. Then 𝖴(𝔸_f) lies in the
closure of the image of 𝖴(E). -/
lemma New.besselU_dense {T : 𝔰.Form E} [IsHermitianUnit T] {T' : 𝔰.Form (𝔸f E)}
    (hT : T.splitGram.map (↑) = T'.splitGram) :
    T'.besselU ≤ (T.besselU.map (U.map (algebraMap E (𝔸f E)) (h := hT))).topologicalClosure := by
  have : IsHermitianUnit T'.splitGram := by
    rw [← hT]
    exact ⟨IsHermitian.map conjTranspose_eq _ fun _ ↦ by simp, isUnit.map (mapMatrix _)⟩
  set C : Subgroup T'.G :=
    (T.besselU.map (U.map (algebraMap E (𝔸f E)) (h := hT))).topologicalClosure
  -- `besselU` is built floor by floor from the groups `floorUnipotent l`, so it is enough that each
  -- of them lies in the closure.
  suffices h_floor : ∀ l : ℕ, ∀ x ∈ floorUnipotent l, x ∈ C by
    rw [← unipotentBelow_eq_besselU (l := 𝔰.ϱ) le_rfl]
    exact unipotentBelow_induction (C := fun _ x ↦ x ∈ C) (one_mem C)
      (fun l x hx y hy ↦ mul_mem (h_floor l x hx) hy) 𝔰.ϱ
  intro l x hx
  obtain hl | hl := le_or_gt 𝔰.ϱ l
  · -- For `ϱ ≤ l` the group `floorUnipotent l` is trivial.
    simp [eq_one_of_mem_floorGroup_inf hx (.inr hl)]
  -- For `l < ϱ`, `x` is a Heisenberg element, and rational parameters are dense.
  let a : Fin 𝔰.ϱ := ⟨l, hl⟩
  obtain ⟨p, rfl⟩ : ∃ p, x = heisenbergElem a p := exists_eq_heisenbergElem_of_mem hx
  have h_dense : DenseRange fun q : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → E) × E ↦
      (fun i ↦ (q.1 i : 𝔸f E), skewPart (q.2 : 𝔸f E)) :=
    (DenseRange.piMap fun _ ↦ denseRange_algebraMap_finAdele).prodMap denseRange_skewPart_algebraMap
  refine map_mem_closure (continuous_heisenbergElem_finAdele a) (h_dense p) ?_
  rintro _ ⟨⟨v, t⟩, rfl⟩
  obtain ⟨-, h_below⟩ := heisenbergElem_mem_floorUnipotent (T := T) a (v, skewPart t)
  exact ⟨_, unipotentBelow_le_besselU h_below, map_heisenbergElem_finAdele hT a v t⟩

end Density

namespace New.Filling

variable {𝔰 : Shape} {E : Type} [Field E] [CMType E] {S : Filling E 𝔰}

@[simp]
lemma unipotentChar_one : S.unipotentChar 1 = 1 := by
  simp [unipotentChar, simpleRootSum_eq_zero_of_mem_besselH]

/-- Strong approximation for the unipotent group 𝖴 = `besselU` of block upper unitriangular
isometries. `K(M) = S.principalLevel` is the group of integral points of `S.GFin` that are congruent
to `1` modulo `M`. For `x ∈ 𝖴(𝔸_f)` and any `y` in `S.GFin`, some rational `u ∈ 𝖴` has `y⁻¹ x⁻¹ u y`
in `K(M)`. -/
lemma exists_besselU_approx {x : S.GFin} (hx : x ∈ besselU) (y : S.GFin) :
    ∃ u : S.G E, u ∈ besselU ∧ y⁻¹ * (x⁻¹ * S.ratToFin u) * y ∈ S.principalLevel := by
  -- In rational coordinates `x` lies in the closure of the rational points of `besselU`, and `V` is
  -- an open neighbourhood of it.
  let f (z : S.G (𝔸f E)) : S.GFin := y⁻¹ * (x⁻¹ * S.toLatticeBasis z) * y
  let V : Set (S.G (𝔸f E)) := f ⁻¹' S.principalLevel
  have h_open : IsOpen V := by
    refine IsOpen.preimage (f := f) (.subtype_mk ?_ _) ?_
    · simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      fun_prop
    · rw [S.principalLevel_eq_unitaryLevel]
      exact (isOpen_intGL isOpen_Ô).preimage_val.and isOpen_Ô.matrix.preimage_of_continuous
  have hxV : S.toLatticeBasis.symm x ∈ V := by simp [V, f, one_mem]
  have hx_bes : S.toLatticeBasis.symm x ∈ besselU :=
    toLatticeBasis_mem_besselU.1 (by simpa using hx)
  let φ : S.G E →* S.G (𝔸f E) :=
    U.map (algebraMap E (𝔸f E)) (h := S.map_splitGram_ratMiddle E (algebraMap E (𝔸f E)))
  obtain ⟨_, hzV, u, hu, rfl⟩ : (V ∩ besselU.map φ).Nonempty :=
    mem_closure_iff.1 (besselU_dense (S.map_splitGram_ratMiddle E _) hx_bes) V h_open hxV
  have h_map : S.ratToFin u = S.toLatticeBasis (φ u) := by
    apply S.toLatticeBasis.symm.injective
    ext
    simp [φ, ratToFin, adelicToFin, ratToAdelic, U.map]
  exact ⟨u, hu, by simpa [V, f, h_map] using hzV⟩

/-- Let `u`, `v` lie in the unipotent group `besselU` inside the finite adelic unitary group
`S.GFin`. Let `g` be a finite adelic point of U(X₀), the unitary group `U 1` of the identity form on
`𝔰.κ`, and let `h = S.inclHFin g` be its image in `S.GFin`, an element of `New.Shape.Form.besselH`.
If `u⁻¹ h⁻¹ v h` lies in the principal congruence subgroup `S.principalLevel`, then the complex
character `S.unipotentChar` has the same value at `u` and `v`. -/
lemma unipotentChar_eq_of_mem_principalLevel {u v : S.GFin} (hu : u ∈ besselU) (hv : v ∈ besselU)
    (g : U (1 : Matrix 𝔰.κ 𝔰.κ (𝔸f E)))
    (h_mem : u⁻¹ * ((S.inclHFin g)⁻¹ * v * S.inclHFin g) ∈ S.principalLevel) :
    S.unipotentChar v = S.unipotentChar u := by
  set h : S.GFin := S.inclHFin g
  set k : S.GFin := u⁻¹ * (h⁻¹ * v * h) with hk
  obtain ⟨hu_bes, hv_bes⟩ : u ∈ besselS ∧ v ∈ besselS :=
    ⟨mem_partialUnitriangularGroup_of_mem_besselU hu,
      mem_partialUnitriangularGroup_of_mem_besselU hv⟩
  have hh_bes : h ∈ besselS := mem_partialUnitriangularGroup_of_mem_floorGroup
    (inclHFin_mem_besselH g)
  have hk_bes : k ∈ besselS :=
    mul_mem (inv_mem hu_bes) (mul_mem (mul_mem (inv_mem hh_bes) hv_bes) hh_bes)
  -- `simpleRootSum` is additive on `besselS`; apply it to `v h = h u k`.
  have h_add : simpleRootSum v = simpleRootSum u + simpleRootSum k := by
    have h_sum : simpleRootSum (v * h) = simpleRootSum (h * (u * k)) := by simp [hk, mul_assoc]
    simp only [simpleRootSum_mul, hv_bes, hh_bes, hu_bes, hk_bes, mul_mem] at h_sum
    linear_combination h_sum
  -- As `k` is congruent to `1` modulo `S.ideleM`, it does not contribute to the character.
  have h_int : ↑S.ideleM⁻¹ * simpleRootSum k ∈ Ô E :=
    inv_mul_simpleRootSum_mem (S.principalLevel_eq_unitaryLevel.le h_mem)
  simp [unipotentChar, h_add, mul_add, S.selfDualChar.map_add_eq_mul,
    S.selfDualChar_eq_one_of_mem _ h_int]

/-- Let `k` be an integral finite adelic isometry, `γ` a rational one, and `c`, `d` classes with
representatives `h_c`, `h_d`. Then `h_c⁻¹ γ h_d = S.translateByClassReps c d γ` is integral with the
same reduction as `k` iff it lies in `k K(M)`, with `K(M) = S.principalLevel`. -/
lemma mem_termsOver_reduction_iff {c d : S.Classes} {γ : S.G E} {k : S.latticeStabilizer} :
    γ ∈ S.termsOver c (S.reduction k) d ↔
      (k : S.GFin)⁻¹ * S.translateByClassReps c d γ ∈ S.principalLevel := by
  constructor
  · rintro ⟨k', h_reduction, h_position⟩
    exact ⟨k⁻¹ * k', by simp [h_reduction, ← h_position]⟩
  · rintro ⟨k', h_kernel, h_position⟩
    exact ⟨k * k', by simp [MonoidHom.mem_ker.1 h_kernel], eq_inv_mul_iff_mul_eq.1 h_position⟩

/-- Let `γ` be a rational point of `𝖴 = besselU` with `h_c⁻¹ γ h_c` integral, where `h_c` represents
the class `c`, and let `k` be an integral point of `𝖴(𝔸_f)` with the same reduction at the chosen
places as `h_c⁻¹ γ h_c`. Let `σ = simpleRootSum` be the sum of the entries just above the diagonal
on the frame e₁, …, e_ϱ, z, and `γ_v = S.ratToInf γ v` the image of `γ` at the infinite place `v`,
in the rescaled basis. With `wave x = exp (x - x̄)`, the product of the numbers `wave (σ γ_v)` over
all `v` is the complex conjugate of `S.unipotentChar k = ψ_f(-σ(k) / (M ϖ))`. Here `ψ_f` is the
standard character of the finite adeles, `M = S.M` is the level and `ϖ` generates the different. -/
theorem prod_wave_eq_star_unipotentChar {c : S.Classes} {γ : S.G E} (hγ : γ ∈ besselU)
    {k : S.latticeStabilizer} (hk : (k : S.GFin) ∈ besselU)
    (h_over : γ ∈ S.termsOver c (S.reduction k) c) :
    ∏ v : InfinitePlace E, wave (simpleRootSum (S.ratToInf γ v)) = star (S.unipotentChar k) := by
  rw [prod_wave_simpleRootSum_ratToInf, unipotentChar_eq_of_mem_principalLevel hk
    (ratToFin_mem_besselU_iff.2 hγ) c.out (mem_termsOver_reduction_iff.1 h_over)]

/-- Let `c`, `d` be classes, that is, double cosets in U(X₀)(E⁺) \ U(X₀)(𝔸_f) / `S.sourceLevel`,
with chosen representatives `h_c = S.classRep c` and `h_d`. Let `S` satisfy the standing hypotheses
`S.IsAdmissible`; they include that `S.sourceLevel` is the preimage in U(X₀)(𝔸_f) of the principal
congruence subgroup `K(M) = S.principalLevel`. Let `γ` be a rational element of the Bessel subgroup
`besselS`. If `S.translateByClassReps c d γ = h_c⁻¹ γ h_d` lies in `K(M)`, then `c = d` and `γ` lies
in `S.classUnipotent c`, the group of rational unipotent `u` with `h_c⁻¹ u h_c ∈ K(M)`. -/
lemma eq_and_mem_classUnipotent_of_besselS [hS : S.IsAdmissible] {c d : S.Classes}
    {γ : (S.ratMiddle E).G} (hγ_bes : γ ∈ besselS)
    (hγ_level : S.translateByClassReps c d γ ∈ S.principalLevel) :
    c = d ∧ γ ∈ S.classUnipotent c := by
  obtain ⟨u, hu, η, rfl⟩ : ∃ u ∈ besselU, ∃ η : U (1 : Matrix 𝔰.κ 𝔰.κ E),
      γ = u * toBesselH 𝔰 (S.N : E) η :=
    exists_besselU_mul_toBesselH hγ_bes S.isUnit_natCast_N
  -- `h_c⁻¹ γ h_d` splits into a part in `besselU` and a part in `besselH`. The second part lies in
  -- `K(M)` too, and relates the representatives of `c` and `d` modulo `S.sourceLevel`.
  have h_split : S.translateByClassReps c d (u * toBesselH 𝔰 (S.N : E) η) =
      S.translateByClassReps c c u * S.inclHFin (c.out⁻¹ * stdEmbFin η * d.out) := by
    simp [translateByClassReps, ratToFin_toBesselH, mul_assoc]
  have h_level : c.out⁻¹ * stdEmbFin η * d.out ∈ S.sourceLevel := by
    rw [h_split, principalLevel_eq_unitaryLevel] at hγ_level
    exact hS.sourceLevel_eq.ge (S.principalLevel_eq_unitaryLevel.ge (mem_unitaryLevel_of_besselU_mul
      (hu.translateByClassReps_mem_besselU c) (inclHFin_mem_besselH _) hγ_level))
  -- The level `S.sourceLevel` is free, so `c = d` and `η = 1`, and `γ` is unipotent.
  have h_free (δ : U (stdSpace E 𝔰.κ).J) (hδ : d.out⁻¹ * stdEmbFin δ * d.out ∈ S.sourceLevel) :
      δ = 1 :=
    (map_eq_one_iff _ out).1 ((S.classAut_eq_bot d.out).le ⟨⟨δ, rfl⟩, hδ⟩)
  obtain ⟨rfl, rfl⟩ : c = d ∧ η = 1 :=
    eq_and_eq_one_of_doubleCoset_rep Quotient.out_eq h_free η h_level
  exact ⟨rfl, by simpa using hu, by simpa [translateByClassReps] using hγ_level⟩

/-- Let `S` be admissible (`S.IsAdmissible`), `c` a class in `S.Classes` with representative `h_c`,
and `u` in `𝖴(𝔸_f)`. There is a rational `u₀ ∈ 𝖴` such that
`S.translateByClassReps c c u₀ = h_c⁻¹ u₀ h_c` lies in `u K(M)`, with `K(M) = S.principalLevel`.
Moreover `S.unipotentChar`, the character u ↦ ψ_f(−σ(u)/(Mϖ)), takes the same value at
`S.ratToFin u₀` and at `u`. -/
lemma exists_rat_approx_unipotentChar_eq [_hS : S.IsAdmissible] (c : S.Classes) {u : S.GFin}
    (hu : u ∈ besselU) :
    ∃ u₀ : S.G E, u₀ ∈ besselU ∧
      u⁻¹ * S.translateByClassReps c c u₀ ∈ S.principalLevel ∧
      S.unipotentChar (S.ratToFin u₀) = S.unipotentChar u := by
  -- Approximate `h_c u h_c⁻¹`, which is unipotent as `besselS` normalises `besselU`.
  have h_conj : S.classRep c * u * (S.classRep c)⁻¹ ∈ besselU :=
    (besselS_le_normalizer_besselU (classRep_mem_besselS c) u).1 hu
  obtain ⟨u₀, hu₀, h_approx⟩ := exists_besselU_approx h_conj (S.classRep c)
  have h_level : u⁻¹ * S.translateByClassReps c c u₀ ∈ S.principalLevel := by
    simpa [translateByClassReps, mul_assoc] using h_approx
  exact ⟨u₀, hu₀, h_level,
    unipotentChar_eq_of_mem_principalLevel hu (ratToFin_mem_besselU_iff.2 hu₀) c.out h_level⟩

/-- Let `S` be admissible. For each class `c` with representative `h_c`, the rational points `γ` of
`𝖴 = besselU` with `h_c⁻¹ γ h_c` integral map onto `S.reducedImage besselU`, the reduction of the
integral points of `𝖴(𝔸_f)`: an element `s` lies in this group if and only if it is the reduction of
some `h_c⁻¹ γ h_c`. -/
theorem mem_reducedImage_besselU_iff_exists_termsOver [hS : S.IsAdmissible] (c : S.Classes)
    {s : S.ResidueGL} :
    s ∈ S.reducedImage besselU ↔ ∃ γ : S.G E, γ ∈ besselU ∧ γ ∈ S.termsOver c s c := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨γ, hγ, h_level, -⟩ := exists_rat_approx_unipotentChar_eq c hk
    exact ⟨γ, hγ, mem_termsOver_reduction_iff.2 h_level⟩
  · rintro ⟨γ, hγ, k, rfl, h_position⟩
    exact ⟨k, by simpa [mem_subgroupOf, h_position] using hγ.translateByClassReps_mem_besselU c,
                   rfl⟩

/-- Let `S` satisfy the standing hypotheses `S.IsAdmissible`. They include that `S.sourceLevel` is
the preimage in U(X₀)(𝔸_f) of `S.principalLevel`, the kernel of reduction at the chosen places. Let
`s` in `S.ResidueGL`, the product of the general linear groups over the residue fields at these
places, be the reduction of an integral finite adelic element of the Bessel subgroup `besselS`. For
each class `c`, a double coset in U(X₀)(E⁺) \ U(X₀)(𝔸_f) / `S.sourceLevel`, there are a class `d`
and a rational `γ ∈ besselS` with `γ ∈ S.termsOver c s d`. -/
lemma exists_besselS_mem_termsOver [hS : S.IsAdmissible] (c : S.Classes) {s : S.ResidueGL}
    (hs : s ∈ S.reducedImage besselS) :
    ∃ (d : S.Classes) (γ : S.G E), γ ∈ besselS ∧ γ ∈ S.termsOver c s d := by
  obtain ⟨k, hk, rfl⟩ := hs
  -- Split `h_c k = u * S.inclHFin g`, approximate `u` by a rational `x`, and write `g` as
  -- `stdEmbFin η * d.out * a` with `η` rational, `d` a class and `a ∈ S.sourceLevel`.
  obtain ⟨u, hu, h, hh, h_split⟩ :
      ∃ u ∈ besselU, ∃ h ∈ besselH, S.classRep c * (k : S.GFin) = u * h :=
    mem_besselS.1 (mul_mem (classRep_mem_besselS c) hk)
  obtain ⟨g, rfl⟩ := S.range_inclHFin.ge hh
  obtain ⟨x, hx, h_approx⟩ := exists_besselU_approx hu (S.inclHFin g)
  obtain ⟨d, η, a, hg⟩ : ∃ (d : S.Classes) (η : U (stdSpace E 𝔰.κ).J) (a : S.sourceLevel),
      g = stdEmbFin η * d.out * a :=
    exists_eq_map_mul_rep_mul stdEmbFin S.sourceLevel Quotient.out_eq g
  let γ : S.G E := x * toBesselH 𝔰 (S.N : E) η
  -- `h_c⁻¹ γ h_d` is `k` times an element of `S.principalLevel`, which reduces to `1`.
  have h_quotient : (k : S.GFin)⁻¹ * S.translateByClassReps c d γ =
      (S.inclHFin g)⁻¹ * (u⁻¹ * S.ratToFin x) * S.inclHFin g * (S.inclHFin a)⁻¹ := by
    simp [eq_mul_inv_of_mul_eq h_split.symm, hg, γ, translateByClassReps, ratToFin_toBesselH η,
      mul_assoc]
  refine ⟨d, γ, mem_besselS.2 ⟨x, hx, _, toBesselH_mem η, rfl⟩, ?_⟩
  rw [mem_termsOver_reduction_iff, h_quotient]
  exact mul_mem h_approx (inv_mem (hS.sourceLevel_eq.le a.property))

/-- Freeness in rank at most `𝔰.k`, the rank of the definite space X₀. Let `E` be a CM field that
contains a primitive 5040th root of unity, and let the filling data `S` over `E` satisfy the
standing hypotheses `S.IsAdmissible`. For `i = 0, 1`, `S.chosenPlaces i` is the chosen set of finite
places of `E` of norm the prime `S.levelPrime i`. Let `γ` be a rational point of the standard
unitary group in `n` variables, `|n| ≤ 𝔰.k`, and `g` a finite adelic point. If `g⁻¹ γ g` is integral
(lies in `stdLevel E n`) and reduces to `1` at every place of `S.chosenPlaces i`, then `γ = 1`. -/
lemma eq_one_of_reduceAt_eq_one [_hS : S.IsAdmissible] [HasPrimitiveRoot5040 E] {n : Type}
    [Fintype n] [DecidableEq n] (hn : card n ≤ 𝔰.k) (i : Fin 2) {γ : U (stdSpace E n).J}
    {g : Gf E n} (h_int : g⁻¹ * (stdSpace E n).embFin γ * g ∈ stdLevel E n)
    (h_red : ∀ w : S.chosenPlaces i,
      stdLevel.reduceAt w ⟨g⁻¹ * (stdSpace E n).embFin γ * g, h_int⟩ = 1) :
    γ = 1 := by
  -- There are `[E : ℚ] / 2` places in `S.chosenPlaces i`, each of norm above `(2 * card n) ^ 2`.
  have h_lt : (2 * card n) ^ 2 < S.levelPrime i :=
    calc
      _ ≤ (𝔰.k * 𝔰.k) ^ 2 := by gcongr; grind [S.thousand_mul_le_k]
      _ = 𝔰.k ^ 4 := by ring
      _ < 𝔰.k ^ 10 := Nat.pow_lt_pow_right (by grind [S.thousand_mul_le_k]) (by norm_num)
      _ ≤ S.levelPrime i := by
        exact_mod_cast (pow_le_pow_left₀ 𝔰.k.cast_nonneg S.k_le_b 10).trans (S.le_levelPrime i)
  have h_prod : (2 * card n) ^ Module.finrank ℚ E < ∏ w : S.chosenPlaces i, w.1.q := by
    simp only [S.chosenPlaces_q i _ (Subtype.prop _), Finset.prod_const, Finset.card_univ,
      S.card_chosenPlaces, finrank_eq_two_mul_card_infinitePlace, pow_mul]
    gcongr
  exact Variety.eq_one_of_reduceAt_eq_one Subtype.val_injective h_prod h_int h_red

end New.Filling

end UnipotentApproximation

end
