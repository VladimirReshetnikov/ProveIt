import Lib.DiscreteSeries.FlenstedJensen.PsiKTypes
import Lib.DiscreteSeries.Rigidity.HighestVectorsAndFiltration

/-!
# Decay, tail bounds and the L² model of the discrete series coefficient c_λ

Let `G = New.USign ε` be the unitary group of `diag ε`, let `l = 2λ` be a parameter, and let
`c_λ = New.HCParam.dsCoeff l` be its discrete series matrix coefficient. Norms of matrices are
operator norms on Euclidean space, and `a_g = New.blockDiagPart ε g` is the block diagonal part of
`g`. When `l` has gap `h`, Fischer's inequality gives `|c_λ(g)|² |det a_g|^h ≤ 1`, and the lower
bound `(‖g‖/2)² ≤ |det a_g|` turns this into polynomial decay of `c_λ`. The decay yields the
realisation of the module `U(𝔤)c_λ` in `L²(G)`. The file also gives explicit Lipschitz and tail
estimates for `l` with a big gap (`New.HCParam.HasLargeGap`) and entries bounded by `L`. Their
constants are polynomial in `L`.

## Main definitions and results

* `New.DiscreteSeries.norm_dsCoeff_le_pow`: if `l` has gap `h` (`New.HCParam.HasGap`) and `n` is
  nonempty, then |c_λ(g)| ≤ (2/‖g‖)^c for natural numbers c ≤ h.
* `New.HCParam.DsModule`, `New.HCParam.dsAction`, `New.HCParam.dsGenerator`: the module, its
  `gl n`-action by right derivatives, and its generator, which is `K`-highest by
  `New.isKHighest_dsGenerator`.
* `New.exists_smear_dsCoeffSmooth_eq`: every element of the module is an average
  ∫ α(y⁻¹) c_λ(g y) dy against a bump function α (a smearing of c_λ). This gives the decay bound
  `New.HCParam.HasLargeGap.exists_decay_bound`.
* `New.dsCoeff_schur_orthogonality`: Schur's product formula with the formal degree
  `New.HCParam.formalDegree`.
* `New.HCParam.HasLargeGap.toL2`: the embedding in `L²(G)`. The action is the derivative of right
  translation (`New.HCParam.HasLargeGap.isDerivedAction_toL2`), and each function is its own matrix
  coefficient against the generator
  (`New.HCParam.HasLargeGap.inner_toL2_dsGenerator_rightRegularL2`).
* `New.HCParam.HasLargeGap.isUnitaryCasimirGe`: the induced inner product is invariant, and the
  Casimir operator is at least `New.HCParam.casimirValue l`.

Notions from other files:
* `New.HCParam.IsKHighest`: a vector x of a gl_n-module is K-highest of weight ν if each E_aa acts
  on it by ν_a and the compact raising operators kill it.
* `New.HCParam.dsCoeff`: the function c_λ(g) = Ξ(a, a⁻¹g) of a complex matrix g, with a the block
  diagonal part of g and Ξ the normalised integral `New.HCParam.flenstedJensen`.
* `New.HCParam.HasGap`: the entries of `l = 2λ` are distinct and congruent to `n − 1` mod 2, and
  `|λ_i − λ_j| ≥ h` whenever `ε_i ≠ ε_j`.
* `New.HCParam.formalDegree`: for signs ε and l = 2λ, the reciprocal of the integral of |c_λ|² over
  U(diag ε) for the Haar measure normalised by the compact dual.

## Relation to the literature

Known; see `Lib.DiscreteSeries.Rigidity.HighestVectorsAndFiltration`,
`Lib.DiscreteSeries.FlenstedJensen.PsiKTypes` and `Lib.DiscreteSeries.CuspKernel` for sources.
-/

noncomputable section

/-! ## Right translation on L²(U(diag ε)) as a unitary representation -/

section RegularRepL2

open MeasureTheory ContinuousLinearMap LinearIsometry

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ}

/-- The action of U(diag ε) by right translation on the space of complex-valued L² functions on
U(diag ε), as a homomorphism to bounded operators. -/
noncomputable def New.rightRegularL2 :
    USign ε →* (USign ε →₂[volume] ℂ) →L[ℂ] USign ε →₂[volume] ℂ where
  -- Mathlib's action of `(USign ε)ᵐᵒᵖᵈᵐᵃ` on `L²`, as a bounded operator.
  toFun x := (DomMulAct.mk ∘ MulOpposite.op) x • 1
  map_one' := by simp
  map_mul' x y := ContinuousLinearMap.ext fun f ↦
    (inferInstance : MulAction (USign ε)ᵐᵒᵖᵈᵐᵃ _).mul_smul ⟨⟨x⟩⟩ ⟨⟨y⟩⟩ f

/-- Right translation on L²(U(diag ε)) is a unitary representation: it is strongly continuous, the
inner product is a hermitian, positive definite invariant form, and the operator norms are bounded
(growth exponent `A = 0`). -/
theorem New.isUnitaryRep_rightRegularL2 :
    IsUnitaryRep (A := 0) (rightRegularL2 (ε := ε)) (innerSL ℂ) := by
  -- Strong continuity: `g ↦ (· * g)` is continuous into the continuous self-maps of the group.
  let translate : C(USign ε, C(USign ε, USign ε)) :=
    .curry ⟨fun p ↦ p.2 * p.1, continuous_snd.mul continuous_fst⟩
  have h_norm (g : USign ε) (f : USign ε →₂[volume] ℂ) : ‖rightRegularL2 g f‖ = ‖f‖ := by
    simp [rightRegularL2]
  exact
    { continuous f := continuous_const.compMeasurePreservingLp translate.2 _ (by simp)
      invariant g := inner_map_map ⟨(rightRegularL2 g).toLinearMap, h_norm g⟩
      conj_symm := by simp
      pos := by simp [sq]
      growth := ⟨1, by simp [h_norm, opNorm_le_iff]⟩ }

end RegularRepL2

namespace New

/-!
## The determinant of the block diagonal part a_g

* `New.norm_det_blockDiagPart`: `|det a_g|` is the square of the absolute value of the minor on the
  indices of either sign; so the principal minor of g ∈ U(diag ε) on {i | ε i = σ}, for either sign
  σ, is nonzero (`New.U.principalMinor_sign_ne_zero`).
-/

section BlockDiagonalDet

open Matrix Norms.L2Operator MatrixOrder CStarAlgebra Finset Real Unitary Complex U CStarRing

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ}

/-- For `g` in `U(diag ε)` and either sign `σ`, the determinant of the block diagonal part of `g`
(its entries `g i j` with `ε i = ε j`, zero elsewhere) has absolute value the square of that of the
principal minor of `g` on `{i | ε i = σ}` (the determinant of the submatrix on these indices). -/
theorem norm_det_blockDiagPart (σ : ℤˣ) (g : USign ε) :
    ‖(blockDiagPart ε g).det‖ = ‖principalMinor g (ε · = σ)‖ ^ 2 := by
  -- `blockDiagPart ε g` is block diagonal with the two principal blocks of `g`, whose minors have
  -- equal norm.
  have h_zero : ∀ i : n, ¬ε i = σ → ∀ j : n, ε j = σ → blockDiagPart ε g i j = 0 := by
    aesop (add simp blockDiagPart)
  -- there are only two signs, so `ε` is constant on the complement of `{i | ε i = σ}` as well
  have h_block (p : n → Prop) (hp : ∀ i j : n, p i → p j → ε i = ε j) :
      (blockDiagPart ε g).toSquareBlockProp p = g.val.val.toSquareBlockProp p :=
    ext fun i j ↦ ite_eq_left (hp i j i.prop j.prop)
  calc
    _ = ‖principalMinor g (ε · = σ)‖ * ‖principalMinor g (¬ε · = σ)‖ := by
      simp [twoBlockTriangular_det _ _ h_zero, principalMinor, h_block (ε · = σ) (by grind),
        h_block (¬ε · = σ) (by simp +contextual [Int.units_ne_iff_eq_neg])]
    _ = ‖principalMinor g (ε · = σ)‖ ^ 2 := by simp [principalMinor_compl, sq]

@[simp]
theorem U.principalMinor_sign_ne_zero (σ : ℤˣ) (g : USign ε) : principalMinor g (ε · = σ) ≠ 0 := by
  -- if the minor vanished, so would the determinant of the invertible matrix `blockDiagPart ε g`
  intro h_zero
  simpa [h_zero] using norm_det_blockDiagPart σ g

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- For `g` in `U(diag ε)`, the determinant of the block diagonal part of `g` has absolute value at
least `(‖g‖ / 2)²`, where `‖g‖` is the L² operator norm. -/
theorem sq_le_norm_det_blockDiagPart (g : USign ε) [Nonempty n] :
    (‖g.val.val‖ / 2) ^ 2 ≤ ‖(blockDiagPart ε g).det‖ := by
  -- Write `g = k * z` with `k` in `maxCompactU ε` and `z` positive definite. The block diagonal
  -- part of `z` is `(z + z⁻¹) / 2`, so its determinant is the product of `(x + x⁻¹) / 2` over the
  -- eigenvalues `x` of `z`. Each factor is at least 1, and `‖z‖`, `‖z‖⁻¹` are eigenvalues.
  obtain ⟨k, z, hz, rfl, -⟩ := exists_polar g
  have hz_herm : z.val.val.IsHermitian := hz.1
  let ev : n → ℝ := hz_herm.eigenvalues
  have h_block : blockDiagPart ε z = hz_herm.cfc fun x : ℝ ↦ 2⁻¹ * (x + x⁻¹) := by
    rw [← hz_herm.cfc_eq, cfc_const_mul .., cfc_add .., cfc_id' .., cfc_inv_id _]
    -- with `J = signMatrix ε`: the left side is `(z + J z J) / 2`, and `z⁻¹ = J zᴴ J = J z J`
    simp [blockDiagPart_eq, inv_coe_eq_mul_conjTranspose_mul, hz_herm.eq, ← ext_iff]
  -- the unitary factor `k` changes neither side
  have h_norm : ‖(k * z : USign ε).val.val‖ = ‖z.val.val‖ := by
    simp [norm_mem_unitary_mul, mem_iff, ← maxCompactU.coe_inv, star]
  have h_det : ‖(blockDiagPart ε (k * z : USign ε)).det‖ = ∏ x : n, 2⁻¹ * |ev x + (ev x)⁻¹| := by
    -- the excluded simp lemmas would rewrite the conjugation and casts before `det` is evaluated
    simp [← mem_maxCompactU, h_block, IsHermitian.cfc, -conjStarAlgAut_apply, -ofReal_mul, ev]
  have h_spec : spectrum ℝ z.val.val = Set.range ev := hz_herm.spectrum_real_eq_range_eigenvalues
  obtain ⟨i, hi⟩ : ‖z.val.val‖ ∈ Set.range ev := h_spec.le (norm_mem_spectrum_of_nonneg _)
  -- `‖z⁻¹‖ = ‖z‖` lies in the spectrum of `z⁻¹`
  obtain ⟨j, hj⟩ : ‖z.val.val‖⁻¹ ∈ Set.range ev := by
    rw [← h_spec, ← norm_inv z]
    exact spectrum.inv₀_mem (norm_mem_spectrum_of_nonneg _ (CFC.inv_nonneg_of_nonneg _))
  have h_factor (x : n) : 1 ≤ 2⁻¹ * |ev x + (ev x)⁻¹| := by
    grind [one_le_cosh (log (ev x)), cosh_log (hz.eigenvalues_pos x)]
  rw [h_norm, h_det]
  calc
    (‖z.val.val‖ / 2) ^ 2 ≤ ((‖z.val.val‖ + ‖z.val.val‖⁻¹) / 2) ^ 2 := by bound
    _ = ∏ x ∈ {i, j}, 2⁻¹ * |ev x + (ev x)⁻¹| := by
      -- if `i = j`, then `‖z‖ = ‖z‖⁻¹` and both sides are `1`
      rcases eq_or_ne i j with rfl | h_ne <;> grind [Finset.prod_pair]
    _ ≤ ∏ x, 2⁻¹ * |ev x + (ev x)⁻¹| :=
      Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
        (fun x _ ↦ zero_le_one.trans (h_factor x)) fun x _ _ ↦ h_factor x

end BlockDiagonalDet

/-!
## Decay bounds for c_λ

* `New.norm_dsCoeff_sq_mul_det_pow_le_one`: if `l` has gap `h` (`New.HCParam.HasGap`), then
  |c_λ(g)|² · |det a_g|^c ≤ 1 for natural numbers c ≤ h.
-/

section PsiDecay

open Matrix MeasureTheory Finset Real ComplexOrder Norms.L2Operator PosDef U

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} {l : HCParam ε}

/-- For a positive definite matrix z and an integer vector w, the product `weightMinors w z` of
principal minors of z (divided by powers of det z) is positive. -/
theorem weightMinors_pos {z : Matrix n n ℂ} (hz : z.PosDef) (w : n → ℤ) : 0 < weightMinors w z := by
  -- Each factor is a principal minor of `z`, possibly divided by `det z`; all are positive.
  refine finprod_induction _ one_pos (fun _ _ ↦ mul_pos) fun t ↦ ?_
  simp [principalMinor, toSquareBlockProp, toBlock, det_pos, hz, hz.submatrix, apply_ite]

/-- Let `g` in U(diag ε) be positive definite with positive definite block diagonal part `a`, and
let `μ ≤ v` be integer vectors such that, for an integer `t`, the indices `i` with `μ i < t ≤ v i`
all have the same sign. Then |Δ_{t≤v}(a)| ≤ |Δ_{t≤μ}(a)| · |Δ_{t≤μ}(g)| · |Δ_{v<t}(g)|, where Δ is
the principal minor on the indicated indices. -/
theorem norm_principalMinor_blockDiagPart_le {μ v : n → ℤ} (h_le : ∀ i : n, μ i ≤ v i) (t : ℤ)
    (h_sign : ∀ i j : n, μ i < t → t ≤ v i → μ j < t → t ≤ v j → ε i = ε j) {g : USign ε}
    (hg_pos : g.val.val.PosDef) (ha_pos : (blockDiagPart ε g).PosDef) :
    ‖principalMinor (blockDiagPart ε g) (t ≤ v ·)‖ ≤
      ‖principalMinor (blockDiagPart ε g) (t ≤ μ ·)‖ *
        (‖principalMinor g (t ≤ μ ·)‖ * ‖principalMinor g (v · < t)‖) := by
  -- Off `p` all signs agree, so there the block diagonal part coincides with `g`.
  let p (i : n) : Prop := t ≤ μ i ∨ v i < t
  have h_block : principalMinor (blockDiagPart ε g) (¬p ·) = principalMinor g (¬p ·) :=
    congrArg Matrix.det (ext fun i j ↦ ite_eq_left (by grind))
  -- Fischer's inequality for `a`, the passage to the complement, Fischer's inequality for `g`.
  calc
    _ ≤ ‖principalMinor (blockDiagPart ε g) (t ≤ μ ·)‖ *
          ‖principalMinor (blockDiagPart ε g) (¬p ·)‖ :=
      fischer_inequality ha_pos.posSemidef _ _ (by grind) (by grind)
    _ = ‖principalMinor (blockDiagPart ε g) (t ≤ μ ·)‖ * ‖principalMinor g p‖ := by
      simp [h_block, principalMinor_compl]
    _ ≤ _ := by grw [fischer_inequality hg_pos.posSemidef _ _ (by grind) fun _ ↦ .rfl]

/-- Let `l = 2λ` be a parameter of gap h (entries distinct and congruent to `card n - 1` mod 2, with
|λ i - λ j| ≥ h whenever ε i ≠ ε j), let c ≤ h be a natural number, and let `g` be a positive
definite element of U(diag ε) with block diagonal part `a` (the entries (i, j) with ε i = ε j). Then
`|det a| ^ c ≤ |m_{-λ-ρ}(g)|²`. Here λ + ρ is `paramAddRho l`, with ρ the half sum of all roots
positive for l, and m_w = `weightMinors w` is the product over integers t of the principal minors of
g on {i | t ≤ w_i}, each factor with t ≤ 0 divided by det g. -/
theorem norm_det_blockDiagPart_pow_le {h : ℕ} (hg : l.HasGap h) {c : ℕ} (hc : c ≤ h) (g : USign ε)
    (hg_pos : g.val.val.PosDef) :
    ‖(blockDiagPart ε g).det‖ ^ c ≤ ‖weightMinors (-paramAddRho l) g‖ ^ 2 := by
  -- With `μ = λ + ρ` and `v = μ + c` one has `m_v = m_μ · det ^ c`. The claim then reads
  -- `|m_v(a)| ≤ |m_μ(a) m_μ(g) m_v(g⁻¹)|`, which is proved factor by factor.
  -- (The form `ite True c 0` is the one that `weightMinors_add_ite` rewrites.)
  let a : Matrix n n ℂ := blockDiagPart ε g
  let μ : n → ℤ := paramAddRho l
  let v (i : n) : ℤ := μ i + (if True then ↑c else 0)
  -- `a` is the mean of the positive definite matrices `g` and `g⁻¹`.
  have ha_pos : (blockDiagPart ε g).PosDef := by
    rw [← hg_pos.isHermitian]
    simp [blockDiagPart_eq, ← inv_coe_eq_mul_conjTranspose_mul, hg_pos, PosDef.add, PosDef.smul]
  suffices ‖weightMinors v a‖ ≤ ‖weightMinors μ a * weightMinors μ g * weightMinors v g⁻¹‖ by
    -- cancel `|m_μ(a)|`, using `m_v = m_μ · det ^ c` and `m_μ(g⁻¹) = m_{-μ}(g) = conj m_μ(g)`
    simpa [a, μ, v, principalMinor_of_forall, ↓weightMinors_add_ite, weightMinors_neg,
      weightMinors_unitary_inv, ha_pos.isAccretive, field, GeneralLinearGroup.det_ne_zero]
  -- Write each `weightMinors` as a product of minors over `-B < t ≤ B`; by
  -- `jacobi_complementary_minor` and `|det g| = 1`, a minor of `g⁻¹` has the norm of the
  -- complementary minor of `g`.
  obtain ⟨B, h_bounds⟩ : ∃ B : ℤ, ∀ i : n, (-B ≤ μ i ∧ μ i ≤ B) ∧ (-B ≤ v i ∧ v i ≤ B) := by
    simpa [abs_le] using Finite.exists_le (|μ| ⊔ |v|)
  have h_prod : (∏ t ∈ Ioc (-B) B, ‖principalMinor a (t ≤ v ·)‖) ≤
      ∏ t ∈ Ioc (-B) B, ‖principalMinor a (t ≤ μ ·)‖ *
        (‖principalMinor g (t ≤ μ ·)‖ * ‖principalMinor g (v · < t)‖) := by
    refine prod_le_prod₀ (fun t _ ↦ norm_nonneg _) fun t _ ↦
      norm_principalMinor_blockDiagPart_le (fun i ↦ by simp [v]) t ?_ hg_pos ha_pos
    -- Where `μ < t ≤ μ + c` all signs agree, by the gap.
    grind [paramAddRho, HasGap, hg.mono hc]
  -- both sides of the goal are now `(|det a| ^ B)⁻¹` times the two sides of `h_prod`
  simpa [a, h_bounds, jacobi_complementary_minor, weightMinors_eq_det_zpow_mul_prod _ (-B) B,
    mul_assoc, ← prod_mul_distrib, GeneralLinearGroup.det_ne_zero] using
    mul_le_mul_of_nonneg_left h_prod (show (0 : ℝ) ≤ (‖a.det‖ ^ B)⁻¹ by positivity)

/-- For a parameter l = 2λ of gap h (entries of λ with different signs are at least h apart), a
natural number c ≤ h, and g in U(diag ε): |c_λ(g)|²·|det a_g|^c ≤ 1, where c_λ = `l.dsCoeff` is the
discrete series coefficient and a_g is the block diagonal part of g. -/
theorem norm_dsCoeff_sq_mul_det_pow_le_one {h : ℕ} (hg : l.HasGap h) {c : ℕ} (hc : c ≤ h)
    (g : USign ε) : ‖l.dsCoeff g‖ ^ 2 * ‖(blockDiagPart ε g).det‖ ^ c ≤ 1 := by
  -- In `dsCoeff_polar`, bound the denominator below by `norm_det_blockDiagPart_pow_le` and the
  -- numerator by `2 |a b| ≤ |a|² + |b|²`; both squares integrate to `kTypeNormSq`.
  obtain ⟨k, z, hz, h_polar, -⟩ := exists_polar g
  set D : ℝ := ‖(blockDiagPart ε g).det‖ ^ c with hD
  have hD_pos : 0 < D := by simp [hD]
  let f (u : maxCompactU ε) : ℝ := ‖weightMinors l.lowestKType u.val‖ ^ 2
  have h_int : Integrable f (haarK ε) :=
    DiscreteSeries.integrable_of_compactSpace
      (by fun_prop (disch := simp [GeneralLinearGroup.det_ne_zero]))
  -- Factors from `K` on either side do not change `|det a|`, `a` the block diagonal part; so
  -- `g = k * z` and `u⁻¹ * z * u` have the same `D`.
  have h_denom (u : maxCompactU ε) :
      √D ≤ ‖weightMinors (-paramAddRho l) (u.val.val.valᴴ * z * u)‖ := by
    have h_conj_pos : (u⁻¹ * z * u : USign ε).val.val.PosDef := by
      simp [maxCompactU.coe_inv, hz.conjTranspose_mul_mul_same, mulVec_injective_of_isUnit]
    simpa [← mem_maxCompactU, sqrt_le_iff, hD, h_polar, ← maxCompactU.coe_inv] using
      norm_det_blockDiagPart_pow_le hg hc (u⁻¹ * z * u) h_conj_pos
  let F (u : maxCompactU ε) : ℂ :=
    weightMinors l.lowestKType (k * u.val) * starRingEnd ℂ (weightMinors l.lowestKType u) /
      weightMinors (-paramAddRho l) (u.val.val.valᴴ * z * u)
  have h_point (u : maxCompactU ε) : ‖F u‖ ≤ (f (k * u) + f u) / 2 / √D := by
    grw [norm_div, norm_mul, RCLike.norm_conj, ← h_denom u, ← two_mul_le_add_sq]
    simp [mul_assoc]
  have h_psi : ‖l.dsCoeff g‖ ≤ 1 / √D := by
    have h_formula : l.dsCoeff g = (∫ u, F u ∂haarK ε) / l.lowestKType.kTypeNormSq := by
      simpa [F, ← h_polar] using dsCoeff_polar hg k 1 hz
    grw [h_formula, norm_div, norm_integral_le_of_norm_le _ (.of_forall h_point)]
    · -- the two squares have the same integral `kTypeNormSq`, by invariance of `haarK`
      simp only [integral_div, integral_add (h_int.comp_mul_left k) h_int, add_self_div_two,
        integral_mul_left_eq_self f k, f]
      simp [field, abs_of_pos (kTypeNormSq_pos ..), div_self_le_one]
    · exact (((h_int.comp_mul_left k).add h_int).div_const 2).div_const _
  grw [h_psi, div_pow, sq_sqrt hD_pos.le, one_pow, one_div_mul_cancel hD_pos.ne']

/-- For nonempty n, a parameter l = 2λ of gap h, a natural number c ≤ h and g in U(diag ε):
|c_λ(g)| ≤ (2/‖g‖)^c, with the operator norm. -/
theorem DiscreteSeries.norm_dsCoeff_le_pow {h : ℕ} (hg : l.HasGap h) {c : ℕ} (hc : c ≤ h)
    (g : USign ε) [Nonempty n] : ‖l.dsCoeff g‖ ≤ (2 / ‖g.val.val‖) ^ c := by
  -- Use `(‖g‖ / 2)² ≤ |det a|`, `a` the block diagonal part of `g`, in the previous bound.
  have h_sq : (‖l.dsCoeff g‖ * (‖g.val.val‖ / 2) ^ c) ^ 2 ≤ 1 := by
    grw [mul_pow, pow_right_comm, sq_le_norm_det_blockDiagPart,
      norm_dsCoeff_sq_mul_det_pow_le_one hg hc]
  rwa [← inv_div, inv_pow, ← one_div, le_div_iff₀ (by simp), ← sq_le_one_iff₀ (by positivity)]

end PsiDecay

end New

/-!
## The module U(𝔤)c_λ and its L² model

Conventions: `New.HCParam.HasLargeGap l A` is gap `500 n³ + A`; `K = U(diag ε) ∩ U(n)`; `casimirK 1`
(all signs equal) is the Casimir operator `Ω = ∑ E_ab E_ba` of `gl n`.
-/

section SchurOrthogonality

namespace New

open Matrix MeasureTheory ComplexConjugate Complex DiscreteSeries GlModule InnerProductSpace Real
  Norms.L2Operator Submodule Lp simpleFunc MemLp

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} {h A : ℕ} {l : HCParam ε}

/-! ### The module generated by `c_λ` -/

/-- The space U(𝔤)c_λ, l = 2λ, generated by c_λ under right derivatives inside the smooth
functions on U(diag ε). -/
abbrev HCParam.DsModule : Submodule ℂ (SmoothU ε ℂ) :=
  (rightDeriv ε ℂ).filtration 1 l.dsCoeffSmooth 0

/-- The gl_n-module structure on U(𝔤)c_λ obtained by restricting the action by right derivatives
on smooth functions. -/
def HCParam.dsAction : GlModule n l.DsModule := (rightDeriv ε ℂ).generatedModule l.dsCoeffSmooth

/-- The function c_λ regarded as an element of the module U(𝔤)c_λ that it generates. -/
@[simps]
def HCParam.dsGenerator : l.DsModule := ⟨l.dsCoeffSmooth, self_mem_filtration⟩

/-- Equivariance on the right of the function `y ↦ (-l).dsCoeff y⁻¹`, for `l` with gap `h`. If
`x` is block diagonal, invertible and upper triangular in the order of decreasing `l`, then passing
from a group element `g` to `g * x` multiplies this function by `∏ i, x i i ^ Λ i`, where `Λ` is
the highest weight `l.lowestKType` of the lowest `K`-type. -/
theorem dsCoeff_neg_mul_borel_inv (hg : l.HasGap h) (g : USign ε) {x : Matrix n n ℂ}
    (hx_mem : x ∈ blockDiagAlg ε) (hx_borel : IsBorelMatrix (-l) x) :
    (-l).dsCoeff ((g : Matrix n n ℂ) * x)⁻¹ =
      diagChar l.lowestKType x * (-l).dsCoeff (g : Matrix n n ℂ)⁻¹ := by
  have hx_det : x.det ≠ 0 := hx_borel.2
  have h_det : (blockDiagPart ε (g : Matrix n n ℂ)⁻¹).det ≠ 0 := by
    simpa using (isAccretive_blockDiagPart_inv_mul g⁻¹).1
  -- `x` cancels in the denominator of the integrand and stays only as a right factor in the
  -- argument of `weightMinors`, which it multiplies by the character; the sides then differ only
  -- in the order of the factors.
  simp [hx_mem, hx_borel, hx_det, h_det, dsCoeff, flenstedJensen, ← mul_assoc, weightMinors_neg,
    hg.isKDominant_lowestKType.weightMinors_mul_borel hg.neg.injective, ← integral_const_mul,
    mul_div, Matrix.mul_inv_rev, GeneralLinearGroup.det_ne_zero, ne_of_gt]
  ac_rfl

/-- Let `l = 2λ` have gap h (entries distinct and congruent to `card n - 1` mod 2, with |λ i - λ
j| ≥ h whenever ε i ≠ ε j). Then the generator c_λ = `l.dsCoeff` of the module U(𝔤)c_λ, with gl_n
acting by right derivatives (`dsAction`), is a highest vector of weight `l.lowestKType` for
K = U(diag ε) ∩ U(n). That is, each `E a a` acts on it by `lowestKType a`, and it is killed by every
`E a b` with ε a = ε b and l b < l a. Here `lowestKType` is Λ = λ + ρ - 2ρ_c, with ρ the half sum of
the roots positive for l and 2ρ_c the sum of the compact ones (ε i = ε j), i.e. the highest weight
of the lowest K-type. -/
theorem isKHighest_dsGenerator (hg : l.HasGap h) :
    l.IsKHighest l.dsAction l.lowestKType l.dsGenerator := by
  -- On the group `dsCoeff` agrees with `F y = (-l).dsCoeff y⁻¹`, which is holomorphic at `g` and
  -- is scaled by `diagChar l.lowestKType x` from `g` to `g * x` for triangular
  -- `x ∈ blockDiagAlg ε`; differentiate in `x`.
  refine .of_E_eq_smul fun a b (h_sign : ε a = ε b) h_le ↦ ?_
  ext g
  show (rightDeriv ε ℂ (single a b 1) l.dsCoeffSmooth).val g =
    (if a = b then (l.lowestKType a : ℂ) else 0) * l.dsCoeff g
  let F (y : Matrix n n ℂ) : ℂ := (-l).dsCoeff y⁻¹
  have h_ext (u : USign ε) : F u = l.dsCoeff u := by simpa [F] using dsCoeff_inv hg.neg u
  have h_diff : DifferentiableAt ℂ F g :=
    (((-l).analyticAt_dsCoeff g⁻¹).comp_of_eq (analyticAt_matrix_inv g.1.det_ne_zero)
      (by simp)).differentiableAt
  have h_equiv : ∀ᶠ y in nhds (g : Matrix n n ℂ), ∀ x ∈ blockDiagAlg ε, IsBorelMatrix (-l) x →
      y = g * x → F y = diagChar l.lowestKType x * F g :=
    .of_forall <| by simp +contextual [F, dsCoeff_neg_mul_borel_inv hg g]
  rw [rightDeriv_apply_eq_of_hasFDerivAt h_diff.hasFDerivAt h_ext, ← h_ext]
  exact fderiv_eq_of_borel_equivariant ε h_diff.hasFDerivAt h_le h_sign (g * ·) h_equiv
    fun t ↦ by simp [mul_add, -smul_single]

/-- Let `l = 2λ` be a parameter of gap `h` for the signs `ε`: its entries are distinct and of the
parity of `card n - 1`, and `|λ i - λ j| ≥ h` when `ε i ≠ ε j`. Then the function `c_λ = l.dsCoeff`
satisfies `‖c_λ(g)‖ ≤ 1` for every `g` in `U(diag ε)`. -/
theorem DiscreteSeries.norm_dsCoeff_le_one (hg : l.HasGap h) (g : USign ε) : ‖l.dsCoeff g‖ ≤ 1 := by
  -- with exponent `0` the determinant factor is `1`
  simpa using norm_dsCoeff_sq_mul_det_pow_le_one hg (Nat.zero_le h) g

/-! ### Smearing -/

/-- Let n ≥ 1, let λ have gap 500n³+A, and let w be integrable on G = U(diag ε) with ∫_K
conj(m_Λ(k)) w(k⁻¹g) dk = ∫_K |m_Λ|² · w(g) for all g (m_Λ = `New.weightMinors` of the lowest K-type
Λ, and dk = `haarK ε` is the Haar measure of mass one on K = U(diag ε) ∩ U(n)).
Then ∫ w(g)c_λ(xga) dg = c_λ(x) ∫ w(g)c_λ(ga) dg. -/
theorem integral_mul_dsCoeff_translate [Nonempty n] (hg : l.HasLargeGap A) {w : USign ε → ℂ}
    (hw_int : Integrable w)
    (hw_type : ∀ g : USign ε,
      ∫ k : maxCompactU ε, conj (weightMinors l.lowestKType k) * w (k.val⁻¹ * g) ∂haarK ε =
        l.lowestKType.kTypeNormSq * w g)
    (x a : USign ε) :
    ∫ g : USign ε, w g * l.dsCoeff (x * g * a :) =
      l.dsCoeff x * ∫ g : USign ε, w g * l.dsCoeff (g * a :) := by
  -- Average over `K` against `conj (weightMinors l.lowestKType k)`. Putting `k` on `dsCoeff` gives
  -- the right side by `h_proj`, putting it on `w` gives the left side by `hw_type`; both carry
  -- the factor `kTypeNormSq ≠ 0`.
  have h_proj (g : USign ε) : ∫ k : maxCompactU ε,
      conj (weightMinors l.lowestKType k.val) * l.dsCoeff (x * (k.val * (g * a))) ∂haarK ε =
        l.lowestKType.kTypeNormSq * (l.dsCoeff x * l.dsCoeff (g * a)) := by
    simpa [mul_assoc] using integral_conj_weightMinors_lowestKType_mul_dsCoeff hg x (g * a)
  have h_eq : ∫ g : USign ε, (l.lowestKType.kTypeNormSq * w g) * l.dsCoeff (x * g * a :) =
      ∫ g : USign ε, w g * (l.lowestKType.kTypeNormSq * (l.dsCoeff x * l.dsCoeff (g * a :))) := by
    -- both sides are the double integral over `K` and the group
    obtain ⟨h_on_coeff, h_on_w⟩ :=
      integral_conv (k := fun k ↦ conj (weightMinors l.lowestKType k)) (ν := haarK ε) (↑)
        (integrable_of_compactSpace (by fun_prop (disch := simp [GeneralLinearGroup.det_ne_zero])))
        hw_int (.of_continuous ⟨1, fun g ↦ norm_dsCoeff_le_one hg (x * g * a)⟩)
    simpa [hw_type, h_proj, mul_assoc] using h_on_w.symm.trans h_on_coeff
  -- cancel the constant `kTypeNormSq`
  simpa [mul_left_comm (w _), mul_assoc, integral_const_mul, ne_of_gt] using h_eq

variable [Nonempty n]

/-- Let the index type n be nonempty, and let l = 2λ have gap 500n³+A, where n is its cardinality.
Every function f in U(𝔤)c_λ, the space generated by c_λ = `l.dsCoeff` under right derivatives, is a
smearing of c_λ. That is, there is a smooth function β of compact support on U(diag ε) (an element
of `New.DiscreteSeries.Bumps`) with f(g) = ∫ β(y⁻¹) c_λ(gy) dy for all g, which is
`New.DiscreteSeries.smear` of c_λ applied to β. -/
theorem exists_smear_dsCoeffSmooth_eq (hg : l.HasLargeGap A) (f : l.DsModule) :
    ∃ β : Bumps ε, (smear l.dsCoeffSmooth.1) β = f.1 := by
  -- The range of `smear` is stable under `𝔤` (`rightDeriv_smear`), so it suffices that it
  -- contains `c_λ`. Smear with `β g = b(g g*)² c_λ(g)` for a bump `b` at `0`: this is a nonzero
  -- multiple of `c_λ`.
  let b : ContDiffBump (0 : Matrix n n ℂ) := default
  obtain ⟨P, hP⟩ := l.dsCoeffSmooth.2
  have hP_apply (g : USign ε) : P.1 g.1.1 = l.dsCoeff g := congrFun hP g
  have h_smooth : ContDiff ℝ (⊤ : ℕ∞) fun x : Matrix n n ℂ ↦ ↑(b (x * star x) ^ 2) * P.1 x := by
    have h_self_star : ContDiff ℝ (⊤ : ℕ∞) fun x : Matrix n n ℂ ↦ x * star x :=
      contDiff_id.mul (starL' ℝ).contDiff
    exact (ofRealCLM.contDiff.comp ((b.contDiff.comp h_self_star).pow 2)).mul P.2
  have h_supp : HasCompactSupport fun g : USign ε ↦ ↑(b (g * star g.1.1) ^ 2) * l.dsCoeff g :=
    .intro (isCompact_U_norm_le √b.rOut) (by
      simp +contextual [b.zero_of_le_dist, CStarRing.norm_self_mul_star, sqrt_lt', sq, le_of_lt])
  -- as a smooth function with compact support, this is a bump `β`
  obtain ⟨β, hβ⟩ : ∃ β : Bumps ε, ∀ g : USign ε,
      β.1.1 g = ↑(b (g * star g.1.1) ^ 2) * l.dsCoeff g :=
    ⟨⟨⟨_, ⟨_, h_smooth⟩, funext fun g ↦ by simp [← hP_apply]⟩, h_supp⟩, fun _ ↦ rfl⟩
  -- `g ↦ β g⁻¹` has the left `K`-type of `conj c_λ`, as `b (g⁻¹ g⁻¹*)` is left `K`-invariant in `g`
  have h_type (g : USign ε) :
      ∫ k : maxCompactU ε, conj (weightMinors l.lowestKType k) * β.1.1 (k.1⁻¹ * g)⁻¹ ∂haarK ε =
        l.lowestKType.kTypeNormSq * β.1.1 g⁻¹ := by
    set c : ℂ := ↑(b (g⁻¹.1.1 * star g⁻¹.1.1) ^ 2) with hc
    have h_translate (k : maxCompactU ε) : β.1.1 (k.1⁻¹ * g)⁻¹ = c * l.dsCoeff ↑(g⁻¹ * k) := by
      simp [hβ, hc, star, ← maxCompactU.coe_inv, mul_assoc]
    have h_proj :
        ∫ k : maxCompactU ε, conj (weightMinors l.lowestKType k) * l.dsCoeff ↑(g⁻¹ * k) ∂haarK ε =
          l.lowestKType.kTypeNormSq * l.dsCoeff ↑g⁻¹ := by
      simpa using integral_conj_weightMinors_lowestKType_mul_dsCoeff hg g⁻¹ 1
    simp_rw [h_translate, mul_left_comm _ c]
    rw [integral_const_mul, h_proj, hβ, mul_left_comm]
  have h_smear : (smear l.dsCoeffSmooth.1) β =
      ((∫ g : USign ε, β.1.1 g⁻¹ * l.dsCoeff g) • l.dsCoeffSmooth).1 := by
    ext x
    have hβ_int : Integrable fun g : USign ε ↦ β.1.1 g⁻¹ := by
      simpa using integrable_bump_inv_smul (E := ℂ) 1 β
    simpa [mul_comm (dsCoeff ..)] using integral_mul_dsCoeff_translate hg hβ_int h_type x 1
  -- the factor is the integral of `b(…)² |c_λ(g)|² ≥ 0`, which is positive at `g = 1`
  have h_factor : ∫ g, β.1.1 g⁻¹ * l.dsCoeff g ≠ 0 := by
    have h_pos : 0 < ∫ g : USign ε, ‖β.1.1 g⁻¹ • l.dsCoeff g‖ :=
      integral_pos_of_integrable_nonneg_nonzero (x := 1) (by fun_prop)
        (integrable_bump_inv_smul _ β).norm (fun _ ↦ norm_nonneg _)
        (by simp [hβ, b, ContDiffBump.one_of_mem_closedBall, default])
    simpa [hβ, ↓dsCoeff_inv hg, ← ofReal_pow, ← ofReal_mul, mul_assoc, conj_mul',
      integral_complex_ofReal] using h_pos.ne'
  let S : Submodule ℂ (SmoothU ε ℂ) := (smear l.dsCoeffSmooth.1).range.submoduleOf (SmoothU ε ℂ)
  have h_generator : l.dsCoeffSmooth ∈ S := (smul_mem_iff _ h_factor).1 ⟨β, h_smear⟩
  refine mem_sInf.1 f.2 S ⟨h_generator, ?_⟩
  rintro i j - v ⟨α, hα⟩
  exact ⟨_, rightDeriv_smear _ _ hα _⟩

namespace HCParam.HasLargeGap

/-! ### Decay, integrability and the product formula -/

/-- For n ≥ 1, `l = 2λ` a parameter for ε of gap 500n³+A, f in U(𝔤)c_λ and a natural number
c ≤ 500n³+A, there is K with |f(g)| ≤ K(2/‖g‖)^c for all g in U(diag ε). Here c_λ is `dsCoeff`,
U(𝔤)c_λ is the space of smooth functions on U(diag ε) generated by c_λ under right derivatives, and
‖g‖ is the norm of g as a complex matrix. -/
theorem exists_decay_bound (hg : l.HasLargeGap A) (f : l.DsModule) (c : ℕ)
    (hc : c ≤ gapThreshold n A) :
    ∃ K : ℝ, ∀ g : USign ε, ‖f.1.1 g‖ ≤ K * (2 / ‖(g : Matrix n n ℂ)‖) ^ c := by
  -- `f g = ∫ α(y⁻¹) c_λ(g y) dy`, and `‖g‖ ≤ ‖g y‖ ‖y⁻¹‖` carries the decay of `c_λ` over to `f`
  obtain ⟨α, hα⟩ := exists_smear_dsCoeffSmooth_eq hg f
  have h_int : Integrable fun y : USign ε ↦ ‖α.1.1 y⁻¹‖ * ‖y⁻¹.1.1‖ ^ c := by
    simpa [← U.norm_inv] using (integrable_bump_inv_smul (E := ℂ) (fun y ↦ ‖y⁻¹.1.1‖ ^ c) α).norm
  refine ⟨∫ y : USign ε, ‖α.1.1 y⁻¹‖ * ‖y⁻¹.1.1‖ ^ c, fun g ↦ ?_⟩
  rw [← hα, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (h_int.mul_const _) (.of_forall fun y ↦ ?_)
  grw [norm_smul, dsCoeffSmooth, norm_dsCoeff_le_pow hg hc, mul_assoc, ← mul_pow]
  gcongr
  simpa [field] using norm_mul_le (g * y).1.1 y⁻¹.1.1

/-- For `n ≥ 1` and a natural number `c > 8 n²`, the function `g ↦ (2 / ‖g‖) ^ c` is integrable on
`U(diag ε)`, where `‖g‖` is the operator norm. -/
theorem _root_.New.integrable_two_div_norm_pow {c : ℕ} (hc : 8 * Fintype.card n ^ 2 < c) :
    Integrable fun g : USign ε ↦ (2 / ‖(g : Matrix n n ℂ)‖) ^ c := by
  simpa using (integral_decay_le volume (j := .id (USign ε)) .monoidHom_id hc 1).1

/-- For `λ` of gap `500 n³ + A`, `f` in `U(𝔤) c_λ` and a natural number `C ≤ A + 1`, the function
`g ↦ f g * ‖g‖ ^ C` is integrable on `U(diag ε)`, where `‖g‖` is the operator norm. -/
theorem integrable_mul_norm_pow (hg : l.HasLargeGap A) (f : l.DsModule) (C : ℕ) (hC : C ≤ A + 1) :
    Integrable fun g : USign ε ↦ f.val.val g * (‖(g : Matrix n n ℂ)‖ : ℂ) ^ C := by
  -- Decay of order `C + N` absorbs the weight `‖g‖ ^ C` and leaves order `N`, the least
  -- for which `integrable_two_div_norm_pow` gives integrability.
  let N : ℕ := 8 * Fintype.card n ^ 2 + 1
  have h_order : C + N ≤ gapThreshold n A := by
    unfold gapThreshold N
    nlinarith [Fintype.card_pos (α := n), pow_pos (Fintype.card_pos (α := n)) 2]
  obtain ⟨K, hK⟩ := hg.exists_decay_bound f (C + N) h_order
  refine ((integrable_two_div_norm_pow (c := N) (Nat.lt_succ_self _)).const_mul (K * 2 ^ C)).mono'
    (by fun_prop) (.of_forall fun g ↦ ?_)
  grw [norm_mul, hK, pow_add]
  simp [field, div_pow]

/-- For `λ` of gap `500 n³ + A`, every function in `U(𝔤) c_λ` is integrable. -/
theorem integrable (hg : l.HasLargeGap A) (f : l.DsModule) : Integrable f.val.val := by
  simpa using hg.integrable_mul_norm_pow f 0 (Nat.zero_le _)

/-- For `λ` of gap `500 n³ + A`, every function in `U(𝔤) c_λ` is square integrable. -/
theorem memLp (hg : l.HasLargeGap A) (f : l.DsModule) : MemLp f.val.val 2 := by
  -- `f` is integrable and bounded (decay of order `0`), hence square integrable.
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ g : USign ε, ‖f.val.val g‖ ≤ K := by
    simpa using hg.exists_decay_bound f 0 (Nat.zero_le _)
  rw [memLp_two_iff_integrable_sq_norm (by fun_prop)]
  simpa [sq] using (hg.integrable f).norm.mul_bdd (by fun_prop) (.of_forall (by simpa using hK))

/-- For signs `ε` with `n` nonempty and a parameter `l = 2λ` of gap `500 n³ + A`, the formal degree
`deg_λ` is positive; `deg_λ` is the reciprocal of the integral of `|c_λ|²` over `U(diag ε)` for the
Haar measure `haarU`. -/
@[simp]
lemma _root_.New.formalDegree_pos (hg : l.HasLargeGap A) : 0 < l.formalDegree := by
  -- the inverse is the integral of `|c_λ|²`, which is continuous, nonnegative and `1` at `1`
  exact inv_pos.2 (integral_pos_of_integrable_nonneg_nonzero (x := 1) (by fun_prop)
    (hg.memLp l.dsGenerator).norm.integrable_sq (fun _ ↦ sq_nonneg _) (by simp))

/-- Let `l = 2λ` be a parameter for the signs `ε` with gap `500 n³ + A` (`HasLargeGap`), and let
`C ≤ A + 1` be a natural number. Then `g ↦ e_λ g * ‖g‖ ^ C` is integrable on the unitary group
`U(diag ε)`. Here `e_λ = deg_λ · conj c_λ` is `New.HCParam.dsKernel` and `‖g‖` is the operator
norm. -/
theorem integrable_dsKernel_mul_norm_pow (hg : l.HasLargeGap A) (C : ℕ) (hC : C ≤ A + 1) :
    Integrable fun g : USign ε ↦ l.dsKernel g * (‖(g : Matrix n n ℂ)‖ : ℂ) ^ C := by
  -- `conj (l.dsCoeff g)` is `(-l).dsCoeff g`, the generator of the module for the parameter `-l`
  simpa [dsKernel, mul_assoc] using (integrable_mul_norm_pow hg.neg dsGenerator C hC).const_mul
    l.formalDegree

/-- Schur orthogonality: for n ≥ 1, `l = 2λ` a parameter for ε of gap 500n³+A, and x, a in U(diag
ε), deg_λ ∫ c_λ(xya) conj(c_λ(y)) dy = c_λ(x)c_λ(a). Here c_λ is `dsCoeff`, dy is the Haar measure
`volume` on U(diag ε), and deg_λ is the formal degree, the reciprocal of ∫ |c_λ|² dy. -/
theorem _root_.New.dsCoeff_schur_orthogonality (hg : l.HasLargeGap A) (x a : USign ε) :
    l.formalDegree * ∫ y : USign ε, l.dsCoeff (x * y * a :) * conj (l.dsCoeff y) =
      l.dsCoeff x * l.dsCoeff a := by
  -- `integral_mul_dsCoeff_translate` for the weight `g ↦ c_λ(g⁻¹) = conj (c_λ(g))`
  have h_left (x a : USign ε) : ∫ g : USign ε, l.dsCoeff ↑g⁻¹ * l.dsCoeff (x * g * a :) =
      l.dsCoeff x * ∫ g : USign ε, l.dsCoeff ↑g⁻¹ * l.dsCoeff (g * a :) :=
    integral_mul_dsCoeff_translate hg (hg.integrable l.dsGenerator).comp_inv
      (by simpa using (integral_conj_weightMinors_lowestKType_mul_dsCoeff hg ·⁻¹ 1)) x a
  -- substitute `g ↦ a⁻¹ / g` in `h_left a 1` to move `a` from the left to the right
  have h_right : ∫ g : USign ε, l.dsCoeff ↑g⁻¹ * l.dsCoeff (g * a :) =
      l.dsCoeff a * ∫ g : USign ε, l.dsCoeff ↑g⁻¹ * l.dsCoeff g := by
    simpa [div_eq_mul_inv, mul_comm] using (integral_div_left_eq_self _ _ a⁻¹).trans (h_left a 1)
  have h_norm : l.formalDegree * ∫ g : USign ε, l.dsCoeff ↑g⁻¹ * l.dsCoeff g = 1 := by
    simp_rw [dsCoeff_inv hg, conj_mul', ← ofReal_pow, integral_complex_ofReal]
    simpa [formalDegree] using mul_inv_cancel₀ (ofReal_ne_zero.2 (formalDegree_pos hg).ne')
  simp_rw [mul_comm _ (conj _), ← dsCoeff_inv hg, h_left, h_right]
  linear_combination l.dsCoeff x * l.dsCoeff a * h_norm

/-! ### The model in `L²` -/

/-- The linear map from U(𝔤)c_λ to L²(U(diag ε)) sending a function f to √(deg_λ)·f. -/
def toL2 (hg : l.HasLargeGap A) : l.DsModule →ₗ[ℂ] USign ε →₂[volume] ℂ :=
  √l.formalDegree •
    IsLinearMap.mk' (R := ℂ) (fun f : l.DsModule ↦ (hg.memLp f).toLp) ⟨by tauto, by tauto⟩

omit [Nonempty n] in
/-- For square integrable functions `w` and `z` on `U(diag ε)`, the inner product in `L²` of `w`
with the right translate of `z` by `x` is `∫ g, z (g * x) * conj (w g)`. -/
theorem _root_.New.inner_toLp_rightRegularL2_toLp {w z : USign ε → ℂ} (hw : MemLp w 2)
    (hz : MemLp z 2) (x : USign ε) :
    ⟪hw.toLp w, rightRegularL2 x (hz.toLp z)⟫_ℂ = ∫ g : USign ε, z (g * x) * conj (w g) :=
  integral_congr_ae (hw.coeFn_toLp.comp₂ _ (AEEqFun.coeFn_mk ..))

/-- The matrix coefficient of right translation by `x` between the images in `L²` of two functions
`y`, `z` of `U(𝔤) c_λ` is the formal degree times `∫ g, z (g * x) * conj (y g)`. -/
theorem inner_toL2_rightRegularL2 (hg : l.HasLargeGap A) (y z : l.DsModule) (x : USign ε) :
    ⟪hg.toL2 y, rightRegularL2 x (hg.toL2 z)⟫_ℂ =
      l.formalDegree * ∫ g : USign ε, z.val.val (g * x) * conj (y.val.val g) := by
  simp [toL2, inner_smul_left_eq_smul, inner_toLp_rightRegularL2_toLp, smul_smul, ← real_smul,
    inner_smul_right_eq_smul, le_of_lt]

/-- The orbit map `g ↦ R(g) c_λ` of the image of the generator in `L²` is continuous, where `R` is
right translation. -/
theorem continuous_rightRegularL2_toL2_dsGenerator (hg : l.HasLargeGap A) :
    Continuous fun g : USign ε ↦ rightRegularL2 g (hg.toL2 l.dsGenerator) :=
  isUnitaryRep_rightRegularL2.continuous _

/-- The inner product of `w` in `L²` with the smearing of the orbit map `g ↦ R(g) c_λ` by a bump
function `α` may be taken under the integral sign. -/
theorem inner_smear_rightRegularL2_toL2_dsGenerator (hg : l.HasLargeGap A)
    (w : USign ε →₂[volume] ℂ) (α : Bumps ε) (g : USign ε) :
    ⟪w, smear (fun x : USign ε ↦ rightRegularL2 x (hg.toL2 l.dsGenerator))
        hg.continuous_rightRegularL2_toL2_dsGenerator α g⟫_ℂ =
      ∫ u : USign ε, ⟪w, α.val.val u⁻¹ • rightRegularL2 (g * u) (hg.toL2 l.dsGenerator)⟫_ℂ :=
  (integral_inner (integrable_bump_inv_smul _ α
    (hg.continuous_rightRegularL2_toL2_dsGenerator.comp (continuous_const_mul g))) w).symm

/-- If the function `y` of `U(𝔤) c_λ` is the smearing of `c_λ` by a bump function `α`, then its
right translate by `g` in `L²` is `∫ x, α x⁻¹ • R(g x) c_λ`, the smearing by `α` of the orbit map
of `c_λ`. -/
theorem rightRegularL2_toL2_eq_smear (hg : l.HasLargeGap A) {y : l.DsModule} {α : Bumps ε}
    (hα : (smear l.dsCoeffSmooth.val) α = y.val) (g : USign ε) :
    rightRegularL2 g (hg.toL2 y) =
      smear (fun x : USign ε ↦ rightRegularL2 x (hg.toL2 l.dsGenerator))
        hg.continuous_rightRegularL2_toL2_dsGenerator α g := by
  -- Test against simple functions `w`, which are dense, and exchange the two integrals.
  refine (simpleFunc.denseRange (by simp)).eq_of_inner_right ℂ fun w ↦ ?_
  have hw : Integrable (toSimpleFunc w) :=
    (SimpleFunc.memLp_iff_integrable two_ne_zero nofun).1 (simpleFunc.memLp w)
  have h_swap : ∫ x : USign ε, conj (toSimpleFunc w x) *
        ∫ u : USign ε, α.val.val u⁻¹ * l.dsCoeff (x * g * u :) =
      ∫ u : USign ε, α.val.val u⁻¹ *
        ∫ x : USign ε, conj (toSimpleFunc w x) * l.dsCoeff (x * g * u :) := by
    simpa using (integral_conv (· * g) (hw.inner_const 1) (integrable_bump_inv_smul 1 α)
      (.of_continuous ⟨1, norm_dsCoeff_le_one hg⟩)).1
  rw [hg.inner_smear_rightRegularL2_toL2_dsGenerator, ← toLp_toSimpleFunc w]
  simpa [toL2, inner_toLp_rightRegularL2_toLp, -map_mul, ← hα, mul_left_comm, mul_comm,
    inner_smul_right_eq_smul, mul_assoc, integral_const_mul, ne_of_gt] using h_swap

/-- The action `dsAction` of `gl n` on `U(𝔤) c_λ` is the derivative, along `toL2`, of right
translation on `L²`. -/
theorem isDerivedAction_toL2 (hg : l.HasLargeGap A) :
    IsDerivedAction rightRegularL2 hg.toL2 l.dsAction := by
  -- `v` is a smearing of `c_λ` by some `β`, and `Y v` is the smearing by the derivative of `β`.
  intro Y v
  obtain ⟨β, hβ⟩ := exists_smear_dsCoeffSmooth_eq hg v
  have hYβ : (smear l.dsCoeffSmooth.val) (bumpDeriv Y β) = (l.dsAction Y v).val :=
    rightDeriv_smear _ _ hβ Y
  simpa [hg.rightRegularL2_toL2_eq_smear hβ, ↓← hg.rightRegularL2_toL2_eq_smear hYβ] using
    hasDerivAt_smear _ β hg.continuous_rightRegularL2_toL2_dsGenerator (hasDerivAt_expU Y 1 0)

/-- For signs `ε` with `n` nonempty and a parameter `l = 2λ` of gap `500 n³ + A`, let `y` be any
function in `U(𝔤) c_λ`, the module generated by `c_λ` under right derivatives inside the smooth
functions on `U(diag ε)`. Then `y` is its own matrix coefficient against the generator `c_λ`:
`⟪c_λ, R(g) y⟫ = y g` for every `g ∈ U(diag ε)`. Here both functions are placed in `L²(U(diag ε))`
by `toL2` (multiplication by `√deg_λ`), and `R` is right translation. -/
theorem inner_toL2_dsGenerator_rightRegularL2 (hg : l.HasLargeGap A) (y : l.DsModule)
    (g : USign ε) :
    ⟪hg.toL2 l.dsGenerator, rightRegularL2 g (hg.toL2 y)⟫_ℂ = y.val.val g := by
  -- For `y = c_λ` this is Schur orthogonality; a general `y` is a smearing of `c_λ`.
  obtain ⟨β, hβ⟩ := exists_smear_dsCoeffSmooth_eq hg y
  have h_schur (u : USign ε) : ⟪hg.toL2 l.dsGenerator,
      rightRegularL2 (g * u) (hg.toL2 l.dsGenerator)⟫_ℂ = l.dsCoeff (g * u) := by
    simpa [hg.inner_toL2_rightRegularL2, -map_mul] using dsCoeff_schur_orthogonality hg 1 (g * u)
  rw [hg.rightRegularL2_toL2_eq_smear hβ, hg.inner_smear_rightRegularL2_toL2_dsGenerator]
  simp [← hβ, -map_mul, h_schur, inner_smul_right_eq_smul]

/-- For signs `ε` with `n` nonempty, let `l = 2λ` be a parameter with gap `500 n³ + A`
(`hg : l.HasLargeGap A`). Let `toL2` be the embedding f ↦ √(deg_λ)·f of the module `U(𝔤) c_λ`,
generated by `c_λ` under right derivatives, into `L²(U(diag ε))`. Then: the module action `dsAction`
is the derivative of the right regular representation along `toL2`; every `y` satisfies
`⟪toL2 c_λ, R(g) toL2 y⟫ = y(g)`; and `⟪toL2 y, R(x) toL2 z⟫ = deg_λ · ∫ z(g x) · conj(y(g)) dg`
over `U(diag ε)`, where `deg_λ` is the formal degree `formalDegree`. -/
theorem isDerivedAction_toL2_and_inner_toL2 (hg : l.HasLargeGap A) :
    IsDerivedAction rightRegularL2 hg.toL2 l.dsAction ∧
    (∀ (y : l.DsModule) (g : USign ε),
      ⟪hg.toL2 l.dsGenerator, rightRegularL2 g (hg.toL2 y)⟫_ℂ = y.val.val g) ∧
    ∀ (y z : l.DsModule) (x : USign ε), ⟪hg.toL2 y, rightRegularL2 x (hg.toL2 z)⟫_ℂ =
      l.formalDegree * ∫ g : USign ε, z.val.val (g * x) * conj (y.val.val g) :=
  ⟨hg.isDerivedAction_toL2, hg.inner_toL2_dsGenerator_rightRegularL2, hg.inner_toL2_rightRegularL2⟩

/-- The map `toL2` from `U(𝔤) c_λ` to `L²` is injective. -/
theorem toL2_injective (hg : l.HasLargeGap A) : Function.Injective hg.toL2 := by
  -- a function of `U(𝔤) c_λ` is a matrix coefficient of its image in `L²`
  intro y z h_eq
  ext g
  simp only [← hg.inner_toL2_dsGenerator_rightRegularL2, h_eq]

section Instances

variable [hg : l.HasLargeGap A]

/-- The norm that `U(𝔤) c_λ` inherits from `L²` through `toL2`. -/
instance : NormedAddCommGroup l.DsModule := .induced _ _ hg.toL2 hg.toL2_injective

/-- The inner product that `U(𝔤) c_λ` inherits from `L²` through `toL2`. -/
instance : InnerProductSpace ℂ l.DsModule := .induced hg.toL2

end Instances

/-- The generator `c_λ` has norm `1` for the norm pulled back from `L²` by `toL2`. -/
theorem norm_dsGenerator (hg : l.HasLargeGap A) : ‖l.dsGenerator‖ = 1 := by
  -- the inner product of the generator with itself is its value at `1`, which is `1`
  have h_sq : (‖hg.toL2 l.dsGenerator‖ : ℂ) ^ 2 = 1 := by
    simpa using hg.inner_toL2_dsGenerator_rightRegularL2 l.dsGenerator 1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (mod_cast h_sq)

/-- Each value of a function in `U(𝔤) c_λ` is bounded by the norm of the function pulled back from
`L²` by `toL2`. -/
theorem norm_apply_le_norm (hg : l.HasLargeGap A) (y : l.DsModule) (g : USign ε) :
    ‖y.val.val g‖ ≤ ‖y‖ := by
  -- `y g` is a matrix coefficient against a unit vector, and `rightRegularL2` acts by isometries
  have h_norm : ‖hg.toL2 l.dsGenerator‖ = 1 := hg.norm_dsGenerator
  calc ‖y.val.val g‖
    _ = ‖⟪hg.toL2 l.dsGenerator, rightRegularL2 g (hg.toL2 y)⟫_ℂ‖ := by
      rw [hg.inner_toL2_dsGenerator_rightRegularL2]
    _ ≤ ‖hg.toL2 l.dsGenerator‖ * ‖rightRegularL2 g (hg.toL2 y)‖ := norm_inner_le_norm _ _
    _ = ‖hg.toL2 y‖ := by simp [h_norm, rightRegularL2]

/-- The inner product that `U(𝔤) c_λ` inherits from `L²` is invariant under `𝔲(diag ε)`, and the
Casimir operator Ω = ∑ E_ab E_ba of `gl n` is at least `l.casimirValue`, the scalar by which Ω acts
on `c_λ`, on `U(𝔤) c_λ`. -/
theorem isUnitaryCasimirGe (hg : l.HasLargeGap A) : IsUnitaryCasimirGe l l.dsAction := by
  refine ⟨hg.isDerivedAction_toL2.form_E_eq_sign_mul isUnitaryRep_rightRegularL2, ?_⟩
  -- the Casimir operator is central, so it acts on the whole module by its eigenvalue on `c_λ`
  simp [dsAction, casimirK_generatedModule casimir_dsCoeffSmooth, sq]

/-- The three properties of the inner product that `U(𝔤) c_λ` inherits from `L²`: it is invariant
and the Casimir operator Ω = ∑ E_ab E_ba is at least `l.casimirValue`, the scalar by which Ω acts on
`c_λ` (`isUnitaryCasimirGe`); the generator is a unit vector (`norm_dsGenerator`); the values of a
function are bounded by its norm (`norm_apply_le_norm`).

A step in Flensted-Jensen's construction of Harish-Chandra's discrete series of U(p,q), for
parameters of large gap. `IsUnitaryCasimirGe` records only the inequality for Ω, although Ω acts on
the whole module by exactly `l.casimirValue`. -/
theorem isUnitaryCasimirGe_dsAction (hg : l.HasLargeGap A) :
    IsUnitaryCasimirGe l l.dsAction ∧
    ‖l.dsGenerator‖ = 1 ∧
    ∀ (y : l.DsModule) (g : USign ε), ‖y.val.val g‖ ≤ ‖y‖ :=
  ⟨hg.isUnitaryCasimirGe, hg.norm_dsGenerator, hg.norm_apply_le_norm⟩

end HCParam.HasLargeGap

end New

end SchurOrthogonality

/-!
## Lipschitz and tail bounds for c_λ

* `New.norm_dsCoeff_sub_le`: the Lipschitz bound for `c_λ` under right translation.
* `New.measure_ball_le_integral_dsCoeff`: since `‖c_λ‖ ≥ 1 / 2` on a small ball about `1`
  (`New.half_le_norm_dsCoeff`), a covering argument bounds the measure of a ball of radius `r` in
  terms of `∫ ‖c_λ‖ ^ 2`, on any group with a homomorphism to `New.USign ε`.
* `New.integral_formalDegree_mul_two_div_norm_pow_le`: the resulting bound for the integral of
  `l.formalDegree * (2 / ‖g‖) ^ c`.
-/

namespace New

open Matrix MeasureTheory Fintype Ring Real unitInterval DiscreteSeries Norms.L2Operator U GlModule

variable {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] {ε : n → ℤˣ} {l : HCParam ε} {B L : ℕ}

/-- For `l = 2λ` of gap `500 n³ + B` with all `|l a| ≤ L`, the right derivative of `c_λ` along a
matrix `X` is bounded by `(n + 1)⁴ (n + L + 1) ‖X‖` at every point of `U(diag ε)`. -/
theorem norm_rightDeriv_dsCoeffSmooth_le [hg : l.HasLargeGap B] (hL : ∀ a : n, |l a| ≤ L)
    (y : USign ε) (X : Matrix n n ℂ) :
    ‖(rightDeriv ε ℂ X l.dsCoeffSmooth).val y‖ ≤ (card n + 1) ^ 4 * (card n + L + 1) * ‖X‖ := by
  -- The derivative is the image under `X` of the highest vector `l.dsGenerator`, which has norm
  -- one. Values are bounded by norms, so the bound for the action of `X` applies.
  have action_le : ‖l.dsAction X l.dsGenerator‖ ≤
      (card n + 1) ^ 4 * (↑(L + card n) + 1 + (0 : ℕ)) * ‖X‖ * ‖l.dsGenerator‖ :=
    ((isKHighest_dsGenerator hg).norm_apply_le_of_mem_filtration hg.isUnitaryCasimirGe
      (abs_lowestKType_le hg hL) self_mem_filtration X).2
  refine (hg.norm_apply_le_norm (l.dsAction X l.dsGenerator) y).trans (action_le.trans_eq ?_)
  simp [hg.norm_dsGenerator, add_comm]

omit [Nonempty n] in
/-- For g in U(diag ε), A = g − 1 and real t, the matrix γ = 1 + t A u⁻¹ with u = 1 − ((t − 1)/2) A
satisfies γᴴ J γ = J, where J = diag ε and the inverse of a non-unit is 0. -/
theorem conjTranspose_mul_signMatrix_mul_curve (g : USign ε) (t : ℝ) :
    let A : Matrix n n ℂ := g.1.1 - 1
    let u : Matrix n n ℂ := 1 - ((t - 1) * 2⁻¹) • A
    (1 + t • A * u⁻¹ʳ)ᴴ * signMatrix ε * (1 + t • A * u⁻¹ʳ) = signMatrix ε := by
  -- As `γ * u = 1 + ((1 + t) / 2) • A`, one has
  -- `(γ * u)ᴴ J (γ * u) - uᴴ J u = t • (gᴴ J g - J) = 0`.
  intro A u
  by_cases hu : IsUnit u
  · have factor : 1 + t • A * u⁻¹ʳ = (u + t • A) * hu.unit⁻¹ := by
      simp [add_mul, ← inverse_unit, mul_inverse_cancel _ hu]
    rw [factor, gram_mul, gram_inv_of_gram_eq]
    simp [u, A, mem_U.1, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add]
    module
  · simp [inverse_non_unit _ hu]

/-- For l = 2λ a parameter of gap 500n³+B with all |l_a| ≤ L, and x, g in U(diag ε):
|c_λ(xg) − c_λ(x)| ≤ 100(n+L+1)⁵‖g−1‖, in the operator norm. -/
theorem norm_dsCoeff_sub_le [hg : l.HasLargeGap B] (hL : ∀ a : n, |l a| ≤ L) (x g : USign ε) :
    ‖l.dsCoeff (x * g :) - l.dsCoeff x‖ ≤ 100 * (card n + L + 1) ^ 5 * ‖g.val.val - 1‖ := by
  -- Join `1` to `g = 1 + A` by a curve `γ` in the group and bound the derivative along `x * γ t`.
  let A : Matrix n n ℂ := g.1.1 - 1
  by_cases! hA : 1 ≤ ‖A‖
  · -- Far from `1` the trivial bound `2` suffices.
    grw [norm_sub_le, norm_dsCoeff_le_one hg, norm_dsCoeff_le_one hg, ← hA]
    exact mod_cast by lia
  -- With `u t = 1 - ((t - 1) / 2) • A`, the curve is `1 + t • A * (u t)⁻¹` (the inverse of a
  -- non-unit is `0`), which stays in the group.
  let u (t : ℝ) : Matrix n n ℂ := 1 - ((t - 1) * 2⁻¹) • A
  let γ (t : ℝ) : USign ε := of IsHermitianInvolution.isUnit (1 + t • A * (u t)⁻¹ʳ)
    (conjTranspose_mul_signMatrix_mul_curve g t)
  have deriv_le : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ D : ℂ,
      HasDerivAt (fun t ↦ l.dsCoeff (x * γ t :)) D t ∧ ‖D‖ ≤ 100 * (card n + L + 1) ^ 5 * ‖A‖ := by
    rintro t ⟨ht₀, ht₁⟩
    have small : ‖((t - 1) * 2⁻¹) • A‖ ≤ 2⁻¹ := by
      grw [norm_smul, hA, norm_eq_abs]
      grind
    -- `u t` is a unit `w` with `‖w⁻¹‖ ≤ 2`, by the geometric series.
    let w : (Matrix n n ℂ)ˣ := Units.oneSub _ (small.trans_lt two_inv_lt_one)
    have hγ : (γ t).1.1 = 1 + t • (A * w⁻¹) := by simp [γ, ← inverse_unit, u, w]
    have norm_inv_le : ‖w⁻¹.1‖ ≤ 2 := by
      refine (tsum_geometric_le_of_norm_lt_one _ (by grind)).trans ?_
      grw [small]
      bound
    -- The derivative of `γ` at `t`, from that of the inverse at the unit `w`.
    let γ' : Matrix n n ℂ := t • (2 : ℝ)⁻¹ • (A * (w⁻¹ * (A * w⁻¹))) + A * w⁻¹
    have hγ' : HasDerivAt (fun t ↦ (x * γ t).1.1) (x * γ') t := by
      have hw : u t = w.1 := by simp [u, w]
      have h_u : HasDerivAt u (-((2 : ℝ)⁻¹ • A)) t := by
        simpa [u] using ((((hasDerivAt_id t).sub_const 1).mul_const 2⁻¹).smul_const A).const_sub 1
      have h_inv : HasDerivAt (fun s ↦ (u s)⁻¹ʳ) ((2 : ℝ)⁻¹ • (w⁻¹.1 * (A * w⁻¹.1))) t := by
        simpa [Function.comp_def, mul_assoc] using
          (hasFDerivAt_ringInverse (𝕜 := ℝ) w).comp_hasDerivAt_of_eq t h_u hw.symm
      simpa [γ, γ', hw, mul_add, mul_assoc, smul_comm t (2 : ℝ)⁻¹, add_comm] using
        ((((hasDerivAt_id t).smul_const A).mul h_inv).const_add 1).const_mul x.1.1
    have norm_γ : ‖(γ t).1.1‖ ≤ 3 := by
      grw [hγ, norm_add_le, norm_smul, norm_mul_le, norm_inv_le, hA, norm_of_nonneg ht₀, ht₁]
      norm_num
    have norm_γ' : ‖γ'‖ ≤ 4 * ‖A‖ := by
      grw [norm_add_le, norm_smul, norm_smul, norm_mul_le, norm_mul_le, norm_mul_le, norm_inv_le,
        norm_inv_le, norm_of_nonneg ht₀, ht₁]
      norm_num
      nlinarith [norm_nonneg A]
    have direction : x * γ' = (x * γ t).1 * ((γ t)⁻¹.1.1 * γ') := by simp [mul_assoc]
    refine ⟨_, hasDerivAt_curve l.dsCoeffSmooth (hγ'.congr_deriv direction), ?_⟩
    calc _ ≤ (card n + 1) ^ 4 * (card n + L + 1) * ‖(γ t)⁻¹.1.1 * γ'‖ :=
           norm_rightDeriv_dsCoeffSmooth_le hL ..
      _ ≤ (card n + L + 1) ^ 4 * (card n + L + 1) * (3 * (4 * ‖A‖)) := by
        grw [norm_mul_le, U.norm_inv, norm_γ, norm_γ']
        gcongr
        simp
      _ = 12 * (card n + L + 1) ^ 5 * ‖A‖ := by ring
      _ ≤ 100 * (card n + L + 1) ^ 5 * ‖A‖ := by gcongr; norm_num
  -- The mean value inequality on `[0, 1]`, with `γ 0 = 1` and `γ 1 = g`.
  choose! D hD D_le using deriv_le
  simpa [γ, u, A] using (convex_Icc 0 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht ↦ (hD t ht).hasDerivWithinAt) D_le zero_mem one_mem

/-- Let `l` have gap 500n³+B, all |l_a| ≤ L, and β ≥ n + L + 1, where n = card n. If g in
`New.USign ε` satisfies ‖g − 1‖ ≤ (200 β⁵)⁻¹ in the operator norm, then ‖c_λ(g)‖ ≥ 1/2. -/
theorem half_le_norm_dsCoeff [hg : l.HasLargeGap B] (hL : ∀ a : n, |l a| ≤ L) {β : ℝ}
    (hβ : card n + L + 1 ≤ β) {g : USign ε} (hg_near : ‖g.val.val - 1‖ ≤ (200 * β ^ 5)⁻¹) :
    2⁻¹ ≤ ‖l.dsCoeff g‖ := by
  have β_pos : 0 < β := lt_of_lt_of_le (by positivity) hβ
  -- `l.dsCoeff g` is within `1 / 2` of `l.dsCoeff 1 = 1`.
  have close : ‖l.dsCoeff g - 1‖ ≤ 2⁻¹ :=
    calc _ ≤ 100 * (card n + L + 1) ^ 5 * ‖g.1.1 - 1‖ := by simpa using norm_dsCoeff_sub_le hL 1 g
      _ ≤ 100 * β ^ 5 * (200 * β ^ 5)⁻¹ := by grw [hg_near, hβ]
      _ = 2⁻¹ := by field
  grind [abs_norm_sub_norm_le (l.dsCoeff g) 1, norm_one]

/-- Let `l` have gap `500 n³ + B` and all `|l a| ≤ L`. Let `j` be a homomorphism from a group `S`
to `USign ε` and `ν` a right invariant measure on `S` for which `l.dsCoeff ∘ j` is square
integrable. For `r ≥ 1` the set of `s` with `‖j s‖ ≤ r` has measure at most
`(2000 * ℓ ^ 6 * r ^ 2) ^ (2 * card n ^ 2)` times `∫ 4 * ‖l.dsCoeff (j s)‖ ^ 2`, where
`ℓ = card n + L + 1`. -/
theorem measure_ball_le_integral_dsCoeff [hg : l.HasLargeGap B] (hL : ∀ a : n, |l a| ≤ L)
    {S : Type} [Group S] [MeasurableSpace S] [MeasurableMul S] (ν : Measure S)
    [ν.IsMulRightInvariant] (j : S →* USign ε)
    (h_int : Integrable (fun s : S ↦ ‖l.dsCoeff (j s)‖ ^ 2) ν) (r : ℝ) (hr : r ≥ 1) :
    ν {s : S | ‖(j s).val.val‖ ≤ r} ≤
      ENNReal.ofReal ((2000 * (card n + L + 1) ^ 6 * r ^ 2) ^ (2 * card n ^ 2)) *
        ENNReal.ofReal (∫ s : S, 4 * ‖l.dsCoeff (j s)‖ ^ 2 ∂ν) := by
  let δ : ℝ := (200 * (card n + L + 1) ^ 5)⁻¹
  -- On the ball of radius `δ` around `1` we have `1 ≤ 4 * ‖l.dsCoeff (j s)‖ ^ 2`.
  have small_ball : ν {s | ‖(j s).1.1 - 1‖ ≤ δ} ≤ .ofReal (∫ s, 4 * ‖l.dsCoeff (j s)‖ ^ 2 ∂ν) := by
    refine (h_int.const_mul 4).measure_le_integral (.of_forall (by simp)) fun s hs ↦ ?_
    grw [← half_le_norm_dsCoeff hL le_rfl hs]
    norm_num
  -- The covering bound `measure_ball_le_covering` compares the two balls, with the factor
  -- `K ^ (2 * card n ^ 2)` for any `K ≥ 3 * δ⁻¹ * r ^ 2`.
  have const_le :
      3 * (200 * (card n + L + 1) ^ 5) * r ^ 2 ≤ 2000 * (card n + L + 1) ^ 6 * r ^ 2 := by
    rw [← mul_assoc]
    gcongr <;> norm_num [add_nonneg, le_add_iff_nonneg_left]
  grw [← small_ball]
  simpa [δ] using measure_ball_le_covering ν j 1 (by bound) hr const_le

/-- For a parameter `l` and a natural number `c > 8 n²`, the function
`g ↦ deg_λ * (2 / ‖g‖) ^ c` is integrable on `U(diag ε)`, where `deg_λ = l.formalDegree`. -/
theorem integrable_formalDegree_mul_two_div_norm_pow (l : HCParam ε) {c : ℕ}
    (hc : 8 * card n ^ 2 < c) :
    Integrable fun g : USign ε ↦ l.formalDegree * (2 / ‖(g : Matrix n n ℂ)‖) ^ c :=
  (integrable_two_div_norm_pow hc).const_mul l.formalDegree

/-- Let n = `card n` ≥ 1, and let `l = 2λ` be a parameter of gap `500 n³ + B`: its entries are
distinct and congruent to n - 1 mod 2, and |λ i - λ j| ≥ 500 n³ + B whenever ε i ≠ ε j. Suppose all
`|l a| ≤ L` and `c > 8 n²` is a natural number. Then the integral of `deg_λ * (2 / ‖g‖) ^ c` over
`U(diag ε)`, for its `volume` `New.haarU`, is at most `8 (2000 (n + L + 1)⁶) ^ (2 n²) 2 ^ c`, where
`deg_λ = l.formalDegree` is the reciprocal of the integral of |c_λ|² = |`l.dsCoeff`|² for that same
measure. -/
theorem integral_formalDegree_mul_two_div_norm_pow_le [hg : l.HasLargeGap B]
    (hL : ∀ a : n, |l a| ≤ L) {c : ℕ} (hc : 8 * card n ^ 2 < c) :
    ∫ g : USign ε, l.formalDegree * (2 / ‖(g : Matrix n n ℂ)‖) ^ c ≤
      8 * (2000 * (card n + L + 1) ^ 6) ^ (2 * card n ^ 2) * 2 ^ c := by
  -- Balls have measure at most `(K * R ^ 2) ^ (2 * card n ^ 2) * (4 / l.formalDegree)`;
  -- integrating by layers costs a factor `2`, because `c ≤ 2 * (c - 4 * card n ^ 2)`.
  have h_deg_pos : 0 < l.formalDegree := formalDegree_pos hg
  let K : ℝ := 2000 * (card n + L + 1) ^ 6
  have h_mass : ∫ g : USign ε, 4 * ‖l.dsCoeff g‖ ^ 2 = 4 / l.formalDegree := by
    simp [integral_const_mul, formalDegree, div_eq_mul_inv]
  have h_ball (R : ℝ) (hR : R ≥ 1) : volume {g : USign ε | ‖(g : Matrix n n ℂ)‖ ≤ R} ≤
      .ofReal ((K * R ^ 2) ^ (2 * card n ^ 2)) * .ofReal (4 / l.formalDegree) := by
    simpa only [MonoidHom.id_apply, h_mass] using measure_ball_le_integral_dsCoeff hL volume
      (.id (USign ε)) (hg.memLp l.dsGenerator).norm.integrable_sq R hR
  have h_factor : (c : ℝ) ≤ 2 * (c - (2 : ℕ) * (2 * card n ^ 2 : ℕ)) := by
    push_cast
    linarith [show 8 * (card n : ℝ) ^ 2 ≤ c from mod_cast hc.le]
  have h_layers : ∫ g : USign ε, ‖(g : Matrix n n ℂ)‖ ^ (-c : ℝ) ≤
      K ^ (2 * card n ^ 2) * 2 * (ENNReal.ofReal (4 / l.formalDegree)).toReal :=
    integral_rpow_neg_le_of_measure_sublevel_le (by fun_prop) (one_le_norm ·) (by positivity)
      ENNReal.ofReal_ne_top h_ball (mod_cast by omega) h_factor
  calc ∫ g : USign ε, l.formalDegree * (2 / ‖(g : Matrix n n ℂ)‖) ^ c
      = l.formalDegree * 2 ^ c * ∫ g : USign ε, ‖(g : Matrix n n ℂ)‖ ^ (-c : ℝ) := by
        simp [div_eq_mul_inv, mul_pow, mul_assoc, integral_const_mul]
    _ ≤ l.formalDegree * 2 ^ c * (K ^ (2 * card n ^ 2) * 2 * (4 / l.formalDegree)) := by
        grw [h_layers, ENNReal.toReal_ofReal (by positivity)]
    _ = 8 * K ^ (2 * card n ^ 2) * 2 ^ c := by field

/-- For `l = 2λ` of gap `500 n³ + B` with all `|l a| ≤ L` and a natural number `c > 8 n²`, the
function `g ↦ deg_λ * (2 / ‖g‖) ^ c` is integrable on `U(diag ε)`, with integral at most
`8 (2000 (n + L + 1)⁶) ^ (2 n²) 2 ^ c`, where `deg_λ = l.formalDegree`. -/
theorem integral_tail_le [hg : l.HasLargeGap B] (hL : ∀ a : n, |l a| ≤ L) (c : ℕ)
    (hc : 8 * card n ^ 2 < c) :
    Integrable (fun g : USign ε ↦ l.formalDegree * (2 / ‖(g : Matrix n n ℂ)‖) ^ c) ∧
    ∫ g : USign ε, l.formalDegree * (2 / ‖(g : Matrix n n ℂ)‖) ^ c ≤
      8 * (2000 * (card n + L + 1) ^ 6) ^ (2 * card n ^ 2) * 2 ^ c :=
  ⟨integrable_formalDegree_mul_two_div_norm_pow l hc,
    integral_formalDegree_mul_two_div_norm_pow_le hL hc⟩

end New

end
