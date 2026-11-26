import Lib.DiscreteSeries.Holomorphic.MaximalCompactMinors
import Lib.Weil.Construction.WeilData

/-!
# Gram–Schmidt, tight frames, polar decomposition in U(p,q), forms representing one

This file collects four topics of linear algebra. The first is a Gram–Schmidt process
whose change of basis is block triangular for a weight on the columns. The second concerns tight
frames of `ℂ^Φ` made of vectors of the lattice `𝔞₀` attached to a CM field. The third is the polar
decomposition in the unitary group of a diagonal sign form, with properties of accretive matrices.
The last gives a condition under which a Hermitian form takes the value `1` on a subspace.

## Main definitions and results

* `New.exists_orthonormal_mul`: the columns of a complex matrix with a left inverse
  (`New.HasLeftInv`) become orthonormal after right multiplication by an invertible matrix `b` that
  is block triangular for a given weight `wt` on the columns: `b i j = 0` whenever `wt j < wt i`.
* `New.IsTightFrame`: vectors of `𝔞₀`, with multiplicities, that form a tight frame of `ℂ^Φ`.
* `New.exists_polar`: `g = k * z` with `k` unitary and `z` positive definite and an exponential.
* `New.isAccretive_blockDiagPart_inv_mul`: the block diagonal part of `g` is invertible and
  `(blockDiagPart ε g)⁻¹ * g` is accretive.
* `New.exists_mem_dotProduct_mulVec_eq_one`: a Hermitian form on `ℂ^m` that is not negative
  semidefinite on a subspace takes the value `1` on that subspace.

Notions from other files:
* `New.signMatrix ε`: the diagonal matrix of the signs `ε`; `New.USign ε` is its unitary group, the
  invertible complex matrices `g` with `gᴴ * signMatrix ε * g = signMatrix ε`.
* `New.unitaryLie J`: the Lie algebra of this group for `J = signMatrix ε`: the real vector space
  of complex matrices `X` with `Xᴴ * J + J * X = 0`; `New.expU X` is `exp X` in the group.
* `Matrix.IsAccretive z`: the matrix `z + zᴴ` is positive definite.
* `New.WeilData E`: data on a CM field `E`; only its finite idele `α` is used here.
-/

/-! ## Gram–Schmidt with a block triangular change of basis -/

section GramSchmidt

open Matrix InnerProductSpace

/-- Gram–Schmidt: if the complex n × k matrix X has a left inverse and wt is a weight on its
columns with values in a linear order, then there is an invertible matrix b, block upper triangular
for wt, such that the columns of X b are orthonormal. -/
lemma New.exists_orthonormal_mul {n k α : Type*} [Fintype n] [Fintype k] [DecidableEq k]
    [LinearOrder α] (wt : k → α) {X : Matrix n k ℂ} (hX : HasLeftInv X) :
    ∃ b : GL k ℂ, b.val.BlockTriangular wt ∧ (X * b.val)ᴴ * (X * b.val) = 1 := by
  -- Run Gram–Schmidt on the standard basis of `ℂ^k` for the inner product `⟪X u, X v⟫`, with the
  -- basis vectors ordered by increasing weight. The resulting vectors are the columns of `b`.
  obtain ⟨L, hL⟩ : ∃ L : Matrix k n ℂ, L * X = 1 := hX
  let B : Module.Basis k ℂ (EuclideanSpace ℂ k) := PiLp.basisFun 2 ℂ k
  -- A linear order on `k` refining `wt`: ties are broken by a fixed embedding into the cardinals.
  let order : LinearOrder k :=
    .lift' (fun i : k ↦ toLex (wt i, embeddingToCardinal i)) (fun _ _ _ ↦ by simp_all)
  let finiteOrder : LocallyFiniteOrderBot k := (monoEquivOfFin k rfl).symm.locallyFiniteOrderBot
  -- `X` is injective as it has a left inverse, so the norm and inner product pull back along it.
  have hX_inj : Function.Injective X.toEuclideanLin := Function.LeftInverse.injective
    (g := fun v : EuclideanSpace ℂ n ↦ WithLp.toLp 2 (L *ᵥ v.ofLp)) fun v ↦ by simp [hL]
  let pulledNorm : NormedAddCommGroup (EuclideanSpace ℂ k) := .induced _ _ X.toEuclideanLin hX_inj
  -- No type is written: it would refer to the standard norm instead of `pulledNorm`.
  let pulledInner := induced X.toEuclideanLin
  let G : Matrix k k ℂ := of fun i j ↦ gramSchmidtNormed ℂ B j i
  -- Both entries pair a column of `X * G` with a conjugated column; only the order differs.
  have h_gram : (X * G)ᴴ * (X * G) = gram ℂ (gramSchmidtNormed ℂ B) :=
    Matrix.ext fun _ _ ↦ dotProduct_comm _ _
  have h_orth : (X * G)ᴴ * (X * G) = 1 :=
    h_gram.trans (gram_eq_one_iff_orthonormal.2 (gramSchmidtNormed_orthonormal B.linearIndependent))
  -- If `wt j < wt i` then `j < i` in the refined order, so coordinate `i` of vector `j` vanishes.
  have h_tri : G.BlockTriangular wt := by
    intro i j hij
    have h_lt : j < i := Prod.Lex.toLex_lt_toLex.2 (Or.inl hij)
    have h_zero : gramSchmidt ℂ B j i = 0 := gramSchmidt_triangular h_lt B
    simp [G, gramSchmidtNormed, h_zero]
  -- `(X * G)ᴴ * X` is a left inverse of the square matrix `G`, so `G` is invertible.
  have h_inv : (X * G)ᴴ * X * G = 1 := by rw [Matrix.mul_assoc, h_orth]
  exact ⟨(Units.mkOfMulEqOne _ G h_inv)⁻¹, h_tri, h_orth⟩

end GramSchmidt

/-!
## Tight frames in the lattice 𝔞₀

For a CM field `E` with CM type `Φ` (`New.CMType`) and the finite idele `α` of `New.WeilData`,
`𝔞₀ = E ∩ α Ô` is a lattice in `ℂ^Φ`; `New.Ô` is the ring of integral finite adeles.
-/

namespace New

variable {E I : Type} [Field E] [CMType E] [WeilData E] (w : I → E) [Fintype I]

/-- The finite image of a family w of elements of E: the finite adelic vector α⁻¹w, with α the
idele of the Weil data. -/
noncomputable def finiteImage : (I → E) →ₗ[E] I → 𝔸f E :=
  ((WeilData.α (E := E))⁻¹.val • Algebra.linearMap E (𝔸f E)).compLeft I

/-- The w_i lie in the lattice E ∩ αÔ and, taken m_i times, form a tight frame with frame bound M.
That is, ∑ m_i Φσ(w_i)·conj(Φτ(w_i)) = Mδ_{στ} for all infinite places σ, τ of E, with Φ the CM
type. -/
structure IsTightFrame (m : I → ℕ) (M : ℕ) : Prop where
  /-- Each w_i lies in the lattice E ∩ αÔ. -/
  finiteImage_mem : ∀ i : I, finiteImage w i ∈ Ô E
  /-- The matrix ∑ m_i Φσ(w_i)·conj(Φτ(w_i)) is M times the identity. -/
  sum_mul_conj : ∀ σ τ : NumberField.InfinitePlace E,
    ∑ i : I, m i * (Φ σ (w i) * starRingEnd ℂ (Φ τ (w i))) = if σ = τ then (M : ℂ) else 0

/-- Let E be a CM field with CM type Φ and Weil data. If the w_i, taken with multiplicities m_i, are
a tight frame with bound M (they lie in the lattice E ∩ αÔ and ∑ m_i Φσ(w_i)·conj(Φτ(w_i)) = Mδ_στ),
then so is the family with each w_i repeated m_i times, all with multiplicity one. -/
lemma IsTightFrame.repeat_vectors {m : I → ℕ} {M : ℕ} (hw : IsTightFrame w m M) :
    IsTightFrame (fun x : Σ i : I, Fin (m i) ↦ w x.1) 1 M :=
  ⟨fun x ↦ hw.finiteImage_mem x.1, fun σ τ ↦ by simpa [Fintype.sum_sigma] using hw.sum_mul_conj σ τ⟩

end New

/-! ## Polar decomposition in U(p,q) and accretive matrices -/

section PolarDecomposition

open New Matrix Norms.L2Operator ComplexOrder MatrixOrder CFC IsHermitianInvolution U

variable {n : Type _} [Fintype n] [DecidableEq n]

/-- Polar decomposition in `USign ε = U(diag ε)`, the unitary group of the diagonal form with signs
ε: every g is kz with k in `maxCompactU ε`, the subgroup of unitary matrices, and z positive
definite and in the range of `expU`, the exponential map on the Lie algebra of the group. -/
theorem New.exists_polar {ε : n → ℤˣ} (g : USign ε) :
    ∃ (k : maxCompactU ε) (z : USign ε), z.val.val.PosDef ∧ g = k * z ∧ z ∈ Set.range expU := by
  -- Put `P = gᴴ g`, `L = log P`, `J = signMatrix ε`. The map `X ↦ -J⁻¹ Xᴴ J` fixes `L`, as
  -- `x ↦ (J⁻¹ xᴴ J)⁻¹` fixes `P`; so `L` is in the Lie algebra. Take `z = exp (L / 2)` and
  -- `k = g z⁻¹`.
  let P : Matrix n n ℂ := g.val.valᴴ * g.val.val
  let L : Matrix n n ℂ := log P
  have exp_L : NormedSpace.exp L = P := exp_log P ⟨star_mul_self_nonneg _, by simp [P]⟩
  have L_herm : Lᴴ = L := IsSelfAdjoint.log
  have J_inv : (signMatrix ε)⁻¹ = signMatrix ε := inv_eq_left_inv IsHermitianInvolution.mul_self
  -- `g⁻¹ = J gᴴ J` and `J² = 1` give `(J⁻¹ P J)⁻¹ = P`.
  have P_fixed : ((signMatrix ε)⁻¹ * Pᴴ * signMatrix ε)⁻¹ = P := by
    simp [P, J_inv, ← conjTranspose_nonsing_inv, isHermitian.eq, Matrix.mul_inv_rev,
      inv_coe_eq_mul_conjTranspose_mul,
      ← mul_assoc (signMatrix ε) (signMatrix ε), IsHermitianInvolution.mul_self, mul_assoc]
  have L_fixed : -((signMatrix ε)⁻¹ * Lᴴ * signMatrix ε) = L := by
    -- The left side is hermitian, hence the logarithm of its exponential.
    have h_selfAdjoint : IsSelfAdjoint (-((signMatrix ε)⁻¹ * Lᴴ * signMatrix ε)) := by
      simp [J_inv, star, IsSelfAdjoint, isHermitian.eq, L_herm, mul_assoc]
    rw [← log_exp _ h_selfAdjoint, exp_neg, exp_conj' _ _ isUnit, exp_conjTranspose, exp_L, P_fixed]
  have L_mem : Lᴴ * signMatrix ε + signMatrix ε * L = 0 := by
    nth_rw 2 [← L_fixed]
    simp [IsHermitianInvolution.det_ne_zero, mul_assoc]
  let z : USign ε := expU ((⅟2 : ℝ) • (⟨L, L_mem⟩ : unitaryLie (signMatrix ε)))
  have z_pos : z.val.val.PosDef :=
    (z.val.isStrictlyPositive_of_le (show 0 ≤ z.val.val by cfc_tac)).posDef
  -- `invOf_eq_inv` is excluded so that `⅟2 • L + ⅟2 • L` simplifies to `L`.
  have z_sq : z.val.val * z.val.val = P := by
    simp [z, ← exp_add_of_commute, -invOf_eq_inv, exp_L]
  -- `z² = gᴴ g` and `z` is hermitian, so `g z⁻¹` is unitary.
  have g_adj : g.val.valᴴ = z * z * g⁻¹ := by simp [z_sq, P]
  have k_mem : g * z⁻¹ ∈ maxCompactU ε :=
    mem_U.2 (by simp [z_pos.inv.isHermitian.eq, g_adj, mul_assoc])
  exact ⟨⟨g * z⁻¹, k_mem⟩, z, z_pos, by simp, Set.mem_range_self _⟩

/-- The accretive matrices, those with `z + zᴴ` positive definite, form a neighbourhood of each
accretive matrix `z`. -/
theorem Matrix.IsAccretive.setOf_mem_nhds {z : Matrix n n ℂ} (hz : z.IsAccretive) :
    {y : Matrix n n ℂ | y.IsAccretive} ∈ nhds z := by
  -- `y` is accretive exactly when the real spectrum of `y + star y` lies in the open set
  -- `(0, ∞)`, and the spectrum is upper hemicontinuous.
  have h_spec : UpperHemicontinuous fun y : Matrix n n ℂ ↦ spectrum ℝ (y + star y) :=
    (upperHemicontinuous_spectrum ℝ _).comp (continuous_id.add continuous_star)
  have h_iff (y : Matrix n n ℂ) : y.IsAccretive ↔ spectrum ℝ (y + star y) ⊆ Set.Ioi 0 := by
    simp [IsAccretive, ← star_eq_conjTranspose, ← isStrictlyPositive_iff_posDef, Set.subset_def,
      CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos]
  filter_upwards [h_spec z (Set.Ioi 0) (isOpen_Ioi.mem_nhdsSet.2 ((h_iff z).1 hz))] with y hy
  exact (h_iff y).2 (isOpen_Ioi.mem_nhdsSet.1 hy)

/-- If `z` is accretive (`z + zᴴ` positive definite) and `w` assigns integer weights to the indices,
then `weightMinors w z` is non-zero. Here `weightMinors w z` is the product over `t : ℤ` of the
principal minor of `z` on `{i | t ≤ w i}`, each factor with `t ≤ 0` divided by `det z`. -/
@[simp]
theorem Matrix.IsAccretive.weightMinors_ne_zero {z : Matrix n n ℂ} (hz : z.IsAccretive)
    (w : n → ℤ) : weightMinors w z ≠ 0 := by
  have h_minor (t : ℤ) : principalMinor z (fun i ↦ t ≤ w i) ≠ 0 :=
    det_ne_zero (hz.submatrix (by simp))
  have h_denom (t : ℤ) : (if t ≤ 0 then z.det else 1) ≠ 0 := by grind [det_ne_zero]
  exact finprod_ne_zero fun t ↦ div_ne_zero (h_minor t) (h_denom t)

/-- If `z` is accretive (`z + zᴴ` positive definite) and `k` has non-zero determinant, then
`kᴴ * z * k` is accretive. -/
@[simp]
lemma Matrix.IsAccretive.conjTranspose_mul_mul {z k : Matrix n n ℂ} (hz : z.IsAccretive)
    (hk : k.det ≠ 0) : (kᴴ * z * k).IsAccretive := by
  simpa [IsAccretive, mul_assoc, mul_add, add_mul] using
    PosDef.conjTranspose_mul_mul_same hz (mulVec_injective_of_det_ne_zero hk)

/-- If `k⁻¹ * z` is accretive (its sum with its conjugate transpose is positive definite), then `z`
has non-zero determinant and `z⁻¹ * k` is accretive. -/
theorem Matrix.IsAccretive.det_ne_zero_and_inv_mul {z k : Matrix n n ℂ}
    (h_accr : (k⁻¹ * z).IsAccretive) : z.det ≠ 0 ∧ (z⁻¹ * k).IsAccretive := by
  obtain ⟨hk_det, hz_det⟩ : k.det ≠ 0 ∧ z.det ≠ 0 := by simpa using h_accr.det_ne_zero
  -- With `y = z⁻¹ * k` the inverse of `k⁻¹ * z`, the accretive `yᴴ * (k⁻¹ * z) * y` equals `yᴴ`,
  -- and `yᴴ` has the same hermitian part as `y`.
  have h_adj : (z⁻¹ * k)ᴴ.IsAccretive := by
    simpa [hk_det, hz_det, mul_assoc] using
      h_accr.conjTranspose_mul_mul (k := z⁻¹ * k) (by simp [hk_det, hz_det])
  exact ⟨hz_det, by simpa [IsAccretive, add_comm] using h_adj⟩

/-- For g in `USign ε`, the unitary group of the diagonal form with signs ε, the block diagonal
part B of g (the entries g_ij with ε_i = ε_j) is invertible and B⁻¹ g is accretive: the sum of
B⁻¹ g and its conjugate transpose is positive definite. -/
@[simp]
theorem New.isAccretive_blockDiagPart_inv_mul {ε : n → ℤˣ} (g : USign ε) :
    (blockDiagPart ε g).det ≠ 0 ∧ ((blockDiagPart ε g)⁻¹ * g).IsAccretive := by
  -- With `J = signMatrix ε` the block diagonal part is `(g + J g J) / 2` and `J g J = g⁻¹ᴴ`, so
  -- `g⁻¹ * blockDiagPart ε g = (1 + g⁻¹ g⁻¹ᴴ) / 2` is positive definite; now invert it.
  have h_pos : ((1 / 2 : ℂ) • (1 + g.val.val⁻¹ * g.val.val⁻¹ᴴ)).PosDef :=
    (PosDef.one.add_posSemidef (posSemidef_self_mul_conjTranspose _)).smul one_half_pos
  have h_conj : signMatrix ε * g.val.val * signMatrix ε = g.val.val⁻¹ᴴ := by
    simp [inv_coe_eq_mul_conjTranspose_mul, isHermitian.eq, mul_assoc]
  exact IsAccretive.det_ne_zero_and_inv_mul
    (PosDef.isAccretive (by simpa [blockDiagPart_eq, h_conj, mul_add] using h_pos))

end PolarDecomposition

/-! ## Hermitian forms that represent one -/

section HermitianRepresentsOne

open Matrix ComplexOrder

/-- If the form `v ↦ star v ⬝ᵥ β *ᵥ v` of a Hermitian matrix `β` is not negative semidefinite on a
subspace `S`, then it takes the value `1` on `S`. -/
lemma New.exists_mem_dotProduct_mulVec_eq_one {m : Type*} [Fintype m] {β : Matrix m m ℂ}
    (hβ : β.IsHermitian) (S : Submodule ℂ (m → ℂ)) (hS : ¬∀ v ∈ S, star v ⬝ᵥ β *ᵥ v ≤ 0) :
    ∃ v ∈ S, star v ⬝ᵥ β *ᵥ v = 1 := by
  -- Some `v` has a real, positive value `c`; rescale it by `(√c)⁻¹`.
  obtain ⟨v, hv, h_not_le⟩ := not_forall₂.1 hS
  have h_real : (star v ⬝ᵥ β *ᵥ v).im = 0 := hβ.im_star_dotProduct_mulVec_self v
  have h_pos : 0 < (star v ⬝ᵥ β *ᵥ v).re := by simpa [Complex.le_def, h_real] using h_not_le
  set c : ℝ := (star v ⬝ᵥ β *ᵥ v).re with hc
  have h_scale : (√c)⁻¹ * ((√c)⁻¹ * c) = 1 := by simp [field, Real.sq_sqrt h_pos.le]
  exact ⟨((√c)⁻¹ : ℂ) • v, S.smul_mem _ hv, by
    simp [Complex.ext_iff, h_real, mulVec_smul, ← hc, h_scale]⟩

end HermitianRepresentsOne
