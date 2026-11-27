import Lib.SiegelWeil.Formula.LagrangianZeroTerms
import Lib.Weil.DualPair.ThetaIntegrals

/-!
# Siegel sets and the Siegel–Weil formula in Weil's range

This file develops reduction theory for a hermitian space `S` split into `p` hyperbolic planes
(`P : New.SiegelWeil.CompleteSplitting S p`). It proves the Siegel–Weil formula for a space `T` of
rank greater than `2 p`. Write `a_x` for the Levi element `P.levi (Core.dyadicDiag x, 1)`, where
`New.Core.dyadicDiag x` is diagonal with entries `2 ^ x i` at the infinite places and `1` at the
finite places. Write `n(ν)` for `P.radicalElement 0 ν`. Siegel sets give the bound in the cusp used
in the proof of the formula.

## Main definitions and results

* `New.SiegelWeil.exists_compact_parabolic_normal_form`: a normal form `δ⁻¹ g = n(ν) a_x⁻¹ κ`
  adapted to a given rational Lagrangian.
* `New.SiegelWeil.exists_siegel_set`: every adelic point is `γ a_x κ` with `γ` rational, `x ≥ 0`,
  `κ` in a compact set.
* `New.SiegelWeil.exists_summable_zeroTerm_bound`: in Weil's range the zero terms
  `New.SiegelWeil.Lagrangian.zeroTerm`, composed with the normalised torus action
  `New.SiegelWeil.normalisedTorus` (`splitWeil S T`, the Weil representation on `𝒮 (S.hom T)`, of
  `a_x` scaled by `2 ^ (-d * card m * ∑ i, x i)`, with `d` the number of infinite places), are
  bounded by one summable function of the Lagrangian.
* `New.SiegelWeil.siegel_weil`: the mean of theta over `[U(T)]` is the sum of the zero terms.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to diag(s) at the infinite places and 1 at the finite places.
* `New.SiegelWeil.CompleteSplitting`: The splittings S = lE^p ⊕ kE^p into two isotropic frames l and
  k, which pair to p hyperbolic planes; `P.k` is the isotropic frame k and `P.kAdelic` is x⁻¹k, the
  same frame in standard coordinates.
* `New.Space.Splitting.levi`: The homomorphism GL_p(𝔸) × G(V₀) → G(V) sending (m, g₀) to the element
  with k ↦ km, ι ↦ ιg₀, l ↦ l m*⁻¹.
* `New.Space.Splitting.radicalElement`: `P.radicalElement 0 b`, written `n(b)`, is the unipotent
  element with k ↦ k and l ↦ l − k(½ȷ⁻¹(b + b*)), where ȷ is the purely imaginary element of
  `WeilData E`.
* `New.SiegelWeil.Lagrangian.zeroTerm`: The zero term along a Lagrangian L, which is the value at 0
  (`New.SiegelWeil.mixedValue`) in the Schrödinger model of a chosen complete splitting with
  kE^p = L.

## Relation to the literature

Siegel–Weil formula in the convergent range. Here a split space of rank 2p is paired
with a hermitian space of rank above 2p, both unimodular at every finite place, over a CM field `E`
with `WeilData E` (so it contains the 5040th roots of unity and E/E⁺ is unramified at the finite
places), and the Eisenstein series is written as a sum over Lagrangians. Source: A. Weil, Sur la
formule de Siegel dans la théorie des groupes classiques, Acta Math. 113 (1965), n° 52 Thm 5; the
method of proof follows Andrianov (1979), Harris (1981), and P. Garrett, The Siegel-Weil formula in
the convergent range (notes, 2005).

Reduction theory, namely the existence of Siegel sets. The compactness criterion of Mahler that it
uses is from `Lib.Adelic.Reduction.FiniteVolume`.
-/

/-! ## Siegel sets and uniform summability of the zero terms -/

section SiegelSets

namespace New.SiegelWeil

open ENNReal Matrix Space _root_.New.Core Splitting Finset Fintype Set MonoidHom Int G
  Subsingleton Lagrangian
variable {E n m p : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m] [Fintype p] [DecidableEq p] {s : n → ℤˣ} {t : m → ℤˣ} {S : Space E n s}
  (T : Space E m t) (P : CompleteSplitting S p)

/-- Conjugation by the Levi element of the invertible adelic matrix `a` sends the element
`n(b) = P.radicalElement 0 b` of the unipotent radical to `n(a b a*)`. -/
@[local simp]
lemma radicalElement_eq_conj_levi (a : GL p (𝔸 E)) (b : Matrix p p (𝔸 E)) :
    P.radicalElement 0 (a.val * (b * a.valᴴ)) = MulAut.conj (P.levi (a, 1))
      (P.radicalElement 0 b) := by
  simp [↓P.levi_conj_radicalElement, mul_assoc]

/-- Normal form for the complete splitting `P` of `S` into `p` hyperbolic planes, with isotropic
frame `k`. There is a compact set `Ω` such that for every adelic `g` and rational `γ` there
are a rational `δ`, integers `x`, a rational invertible `y` and a matrix `ν` with (a)
`δ⁻¹ g = n(ν) a_x⁻¹ κ` and `(ν, κ) ∈ Ω`, where `n(ν) = P.radicalElement 0 ν` is unipotent and
`a_x = P.levi (Core.dyadicDiag x, 1)` is the Levi element of the diagonal matrix with entries
`2 ^ x i` at the infinite places, and (b) `δ⁻¹ γ` acting on the isotropic frame `k` by
`k ↦ k y` (`P.ActsOnFrame`); so `δ k` and `γ k` span the same Lagrangian. -/
lemma exists_compact_parabolic_normal_form :
    ∃ Ω : Set (Matrix p p (𝔸 E) × G E s),
      IsCompact Ω ∧
      ∀ (g : G E s) (γ : U S.J), ∃ (δ : U S.J) (x : p → ℤ), ∃ y : GL p E, ∃ ν : Matrix p p (𝔸 E),
        -- (a)
        (ν, P.levi (dyadicDiag x, 1) * (P.radicalElement 0 ν)⁻¹ * S.ratEmbed δ⁻¹ * g) ∈ Ω ∧
        -- (b)
        P.ActsOnFrame (S.ratEmbed (δ⁻¹ * γ)) (y.map toAdele).val := by
  -- Write `γ⁻¹ g κ = n(z) m(a)` by Iwasawa. Reduction theory gives a rational basis `y` with
  -- `a⁻¹ y (dyadicDiag x)⁻¹` in a compact set, and a rational `r` moves the conjugate of `z` into a
  -- compact set. With `δ = n(r) m(y⁻¹)`, the rational point that is asked for is `γ δ⁻¹`.
  obtain ⟨N, hN, hN_cover⟩ := IsCovolOneLattice.exists_compact_cover (ratMatrices E p p)
  obtain ⟨M, _, hM, h_bases⟩ := exists_isCompact_profileBases E p
  have h_levi : Continuous fun a : GL p (𝔸 E) ↦ P.levi (a, 1) := by
    simp [↓continuous_iff, Splitting.levi, -coe_units_inv]
    fun_prop
  -- The compact set is `N ×ˢ (K * levi '' M)⁻¹` with `K` the maximal compact subgroup.
  open Pointwise in
    let Ω : Set (Matrix p p (𝔸 E) × G E s) :=
      N ×ˢ ((maxCompact E s : Set (G E s)) * (fun a : GL p (𝔸 E) ↦ P.levi (a, 1)) '' M)⁻¹
    refine ⟨Ω, hN.prod (isCompact_maxCompact.mul (hM.image h_levi)).inv, fun g γ ↦ ?_⟩
  obtain ⟨κ, hκ, a, -, -, c, z, u, h_iwa⟩ := P.iwasawa ((S.ratEmbed γ)⁻¹ * g) (wt := 0)
  -- The complement of the splitting is zero-dimensional.
  obtain rfl : c = 0 := eq_zero c
  obtain rfl : u = 1 := eq_one u
  obtain ⟨x, y, hy, -⟩ := h_bases a
  obtain ⟨r, hr, hr_mem⟩ := hN_cover ((y⁻¹.map toAdele).val * z * (y⁻¹.map toAdele).valᴴ)
  obtain ⟨δ, hδ⟩ := mul_mem (P.radicalElement_mem_Gamma 0 hr) (P.levi_mem_Gamma y⁻¹ (one_mem _))
  let ν : Matrix p p (𝔸 E) := r + (y⁻¹.map toAdele).val * z * (y⁻¹.map toAdele).valᴴ
  refine ⟨γ * δ⁻¹, x, y⁻¹, ν, ⟨hr_mem, κ, hκ, _, mem_image_of_mem _ hy, ?_⟩, ?_⟩
  · -- The unipotent parts cancel, and the Levi parts multiply.
    have h_eq : (S.ratEmbed γ)⁻¹ * g = P.radicalElement 0 z * P.levi (a, 1) * κ⁻¹ :=
      eq_mul_inv_of_mul_eq h_iwa
    simp [ν, hδ, h_eq, ← inl_apply, mul_assoc, ↓ ← radicalElement_zero_mul, -coe_units_inv]
  · -- Here `(γ δ⁻¹)⁻¹ γ = δ = n(r) m(y⁻¹)`, which acts on the frame by `y⁻¹`.
    simp [hδ, ← (adeleMatrix _).mul_assoc, Matrix.mul_assoc, actsOnFrame_levi,
      actsOnFrame_radicalElement]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Siegel sets for a hermitian space `S` with complete splitting `P`: there is a compact `Ω` such
that every adelic point `g` of the unitary group is a rational point (embedded by `S.ratEmbed`)
times the Levi element of `dyadicDiag x`, the diagonal matrix with entries `2 ^ x i` at infinity and
`1` at the finite places, `x i ≥ 0`, times an element of `Ω`. -/
lemma exists_siegel_set :
    ∃ Ω : Set (G E s), IsCompact Ω ∧ ∀ g : G E s, ∃ (γ : U S.J) (x : p → ℕ), ∃ κ ∈ Ω,
      g = S.ratEmbed γ * P.levi (dyadicDiag fun i : p ↦ x i, 1) * κ := by
  -- By Mahler's criterion there are a rational basis `W` and a set `I` of columns such that, for
  -- `D = projectionOff E I`, `(S.x g)⁻¹ W D` lies in a compact set and the Gram matrix of `W D`
  -- in a finite set `F`. An isotropic frame `r` fixed for each `I` and each member of `F` gives a
  -- rational Lagrangian with a basis bounded at `g`; in the normal form
  -- `exists_compact_parabolic_normal_form` this bounds the torus exponents on one side.
  obtain ⟨Ω, hΩ, normal⟩ := exists_compact_parabolic_normal_form P
  obtain ⟨F, C, Cf, hF, hC, -, mahler⟩ :=
    exists_isBoundedDualBasis ((toFinite {stdForm E s}).preimage
      Units.val_injective.injOn).isCompact
  -- For each `I` and `A`, fix once and for all an `R` with `projectionOff E I * R` left invertible
  -- and `Rᴴ A R = 0`, if there is one (`hr` has its existence as a hypothesis).
  choose! r hr using fun (I : Finset n) (A : Matrix n n E)
    (h : ∃ R : Matrix n p E, HasLeftInv (projectionOff E I * R) ∧ Rᴴ * A * R = 0) ↦ h
  let entries (i : p) : Set (𝔸 E) := ⋃ G ∈ F, ⋃ (I : Finset n), ⋃ (j : p),
    (fun q : (Matrix p p (𝔸 E) × _) × Matrix n n (𝔸 E) ↦
      (P.kCoord * q.1.2.adeleMatrix * q.2 * (r I G).map toAdele) i j) '' (Ω ×ˢ C)
  -- A rational `a` with `2 ^ (-e) * a` in the compact set `entries i` and `e < c i` is zero.
  have h_compact (i : p) : IsCompact (entries i) :=
    hF.isCompact_biUnion fun G _ ↦ isCompact_iUnion fun I ↦ isCompact_iUnion fun j ↦
      (hΩ.prod hC).image_of_continuous _
  have h_threshold : ∀ i : p, ∃ c : ℤ, ∀ e < c, ∀ {a : E},
      (twoAtInfinity E ^ (-e)).val * a ∈ entries i → a = 0 := fun i ↦
    exists_eq_zero_of_zpow_mul_mem (h_compact i)
  choose c hc using h_threshold
  refine ⟨_, ((isCompact_closedBall_prod_integral (E := E)).matrix.prod hΩ).image_of_continuous
    fun (a, b, κ) ↦ P.radicalElement 0 (a * b * aᴴ) * ((P.levi (dyadicDiag (-c), 1))⁻¹ * κ),
    fun g ↦ ?_⟩
  obtain ⟨Y, I, hY⟩ := mahler S.isUnit_J.unit _ (S.move g).gram_point
  let W : GL n E := formDual S.isUnit_J.unit Y
  let D : Matrix n n E := projectionOff E I
  have mem_F : (W.val * D)ᴴ * S.J * (W.val * D) ∈ F := hY.gram_mem
  have mem_C : (S.move g).x⁻¹.val * (W.val * D).map toAdele ∈ C := hY.frame_mem
  -- The columns `Y i` with `i ∈ I` span an isotropic subspace, so are orthogonal to a Lagrangian
  -- `γ k`, which is then fixed by `W D W⁻¹`.
  let A : Matrix n I E := Y.val.submatrix id ((↑) : I → n)
  have hA_inv : HasLeftInv A :=
    ⟨_, (congrArg (submatrix · _ _) Y.inv_val).trans (submatrix_one _ (by simp))⟩
  have hA_isotropic : Aᴴ * S.J * A = 0 := funext₂ fun i j ↦ hY.isotropic i i.2 j j.2
  obtain ⟨γ, hγ⟩ := exists_isometry_orthogonal P hA_inv hA_isotropic
  let γk : Matrix n p E := γ.val.val * P.k
  have fix : W.val * (D * (⅟W.val * γk)) = γk := by
    suffices h : D * (⅟W.val * γk) = ⅟W.val * γk by rw [h, Matrix.mul_invOf_cancel_left]
    ext i j
    simp only [D, projectionOff, diagonal_mul, ite_mul, zero_mul, one_mul, ite_eq_right_iff]
    exact fun hi ↦ (congrFun₂ hγ ⟨i, hi⟩ j).symm
  -- So `W⁻¹ γ k` has the property asked of `r`; hence so does the value `R` of `r`, and by Witt's
  -- theorem `W D R = a k` for a rational isometry `a`.
  have left_inv : HasLeftInv (D * (⅟W.val * γk)) :=
    ⟨(γ.val.val * P.l)ᴴ * S.J * W.val, by
      rw [Matrix.mul_assoc, fix, U.gram_invariant, P.gram_lk]⟩
  have isotropic : γkᴴ * S.J * γk = 0 := by rw [U.gram_invariant, P.gram_kk]
  rw [← fix, ← W.val.mul_assoc, gram_mul] at isotropic
  obtain ⟨⟨L, hL⟩, R_iso⟩ := hr I _ ⟨_, left_inv, isotropic⟩
  let R : Matrix n p E := r I ((W.val * D)ᴴ * S.J * (W.val * D))
  have frame_left_inv : L * W.val⁻¹ * (W.val * D * R) = 1 := by
    simpa [R, D, Matrix.mul_assoc] using hL
  have frame_gram : P.kᴴ * S.J * P.k = (W.val * D * R)ᴴ * S.J * (W.val * D * R) :=
    P.gram_kk.trans ((gram_mul ..).trans R_iso).symm
  obtain ⟨a, ha⟩ := S.witt ⟨_, P.gram_lk⟩ ⟨L * W.val⁻¹, frame_left_inv⟩ frame_gram
  obtain ⟨δ, x, y, ν, hκ, hy⟩ :
      ∃ (δ : U S.J) (x : p → ℤ) (y : GL p E) (ν : Matrix p p (𝔸 E)),
        (ν, P.levi (dyadicDiag x, 1) * (P.radicalElement 0 ν)⁻¹ * S.ratEmbed δ⁻¹ * g) ∈ Ω ∧
          P.ActsOnFrame (S.ratEmbed (δ⁻¹ * a)) (y.map toAdele).val :=
    normal g a
  -- In standard coordinates `δ⁻¹` carries the frame `W D R = a k` to `k y`.
  have h_act : (S.ratEmbed δ)⁻¹.adeleMatrix * (S.x⁻¹.val * (W.val * D * R).map toAdele) =
      P.kAdelic * y.val.map toAdele := by
    simpa [← ha, kAdelic, adeleMatrix_ratEmbed, Matrix.map_mul, map_inv, Matrix.mul_assoc] using hy
  -- The entries `2 ^ x i * y i j` lie in the compact set that defines `c i`, and row `i` of `y` is
  -- not zero; hence `x i ≤ -c i`.
  have x_le (i : p) : x i ≤ -c i := by
    refine le_neg.1 (not_lt.1 fun hi ↦ y.det_ne_zero (det_eq_zero_of_row_eq_zero i fun j ↦ ?_))
    -- It suffices that `2 ^ x i * y i j` is an entry of a product that defines `entries i`.
    refine hc i (-x i) hi
      (mem_biUnion mem_F (mem_iUnion₂.2 ⟨I, j, (_, _), ⟨hκ, mem_C⟩, ?_⟩))
    simp [R, move, adeleMatrix.eq_1 g, radicalElement_inv, mul_assoc, Matrix.mul_assoc, dyadicDiag,
      ↓ ← Matrix.map_mul, -coe_units_inv] at h_act ⊢
    rw [h_act]
    simp [← Matrix.mul_assoc, actsOnFrame_radicalElement, actsOnFrame_levi]
  -- With `x i + t i = -c i`, the torus part of `g` is `dyadicDiag t` up to the fixed factor
  -- `(dyadicDiag (-c))⁻¹`.
  choose t ht using fun i : p ↦ le.dest (x_le i)
  refine ⟨δ, t, _, ⟨(_, _), ⟨dyadicDiag_inv_mem t, hκ⟩, rfl⟩, ?_⟩
  simp [← inl_apply, ← ht, dyadicDiag, mul_assoc, _root_.zpow_add, ↓ ← Pi.mul_def,
    -coe_units_inv]

/-- Let `exps : ι → p → ℕ` give a vector of exponents for each index, let `d ≠ 0` and `C ≠ ∞`, and
suppose that, for every vector `x`, at most `C * (2 ^ d) ^ (∑ i, ∑ j, (x i + x j)) * N` indices have
exponents `x`. Then the sum over the indices `L` of `A / ((2 ^ d) ^ ∑ i, exps L i) ^ k` is finite
if `2 * card p < k`. -/
lemma tsum_div_two_pow_lt_top {ι : Type*} {exps : ι → p → ℕ} {d k N : ℕ} {C : ℝ≥0∞} (A : NNReal)
    (hd : d ≠ 0) (hk : 2 * Fintype.card p < k) (hC : C ≠ ∞)
    (fibre_le : ∀ x : p → ℕ,
      ((exps ⁻¹' {x}).encard : ℝ≥0∞) ≤
        C * ENNReal.ofReal ((2 ^ d) ^ ∑ i : p, ∑ j : p, (x i + x j : ℤ).toNat) * N) :
    ∑' L : ι, (A / ((2 ^ d) ^ ∑ i : p, exps L i) ^ k : ℝ≥0∞) < ∞ := by
  -- Sum over the fibres of `exps`: a product of geometric series of ratio `ratio < 1`.
  let ratio : ℝ≥0∞ := .ofReal (2 ^ (2 * card p) / 2 ^ k) ^ d
  have summand_eq (x : p → ℕ) :
      C * ENNReal.ofReal ((2 ^ d) ^ ∑ i : p, ∑ j : p, (x i + x j : ℤ).toNat) * N *
          (A / ((2 ^ d) ^ ∑ i : p, x i) ^ k) =
        C * N * A * ∏ i : p, ratio ^ x i := by
    simp [ratio, toNat_add, division_def, prod_pow_eq_pow_sum, ← mul_sum, ENNReal.inv_pow,
      sum_add_distrib, mul_assoc]
    ring
  calc ∑' L : ι, (A / ((2 ^ d) ^ ∑ i : p, exps L i) ^ k : ℝ≥0∞)
    _ = ∑' x : p → ℕ, ((exps ⁻¹' {x}).encard : ℝ≥0∞) * (A / ((2 ^ d) ^ ∑ i : p, x i) ^ k) := by
      rw [← tsum_fiberwise _ exps]
      exact tsum_congr fun x ↦ by rw [tsum_congr fun L ↦ by rw [L.prop], tsum_set_const]
    _ ≤ ∑' x : p → ℕ, C * N * A * ∏ i : p, ratio ^ x i := by
      grw [fibre_le, tsum_congr summand_eq]
    _ ≤ C * N * A * ∏ _i : p, ∑' a : ℕ, ratio ^ a := by
      grw [ENNReal.tsum_mul_left, tsum_prod_le_prod_tsum]
    _ < ∞ := by
      simp [ratio, mul_lt_top_iff, hC.lt_top, div_lt_one, pow_lt_one_iff, pow_lt_pow_right₀, hk, hd]

omit [WeilData E] in
/-- Let `δ` be a rational point of the unitary group of `S`. No column of `δ k` vanishes, where `k`
is the isotropic frame of the complete splitting `P`. -/
lemma exists_mul_k_apply_ne_zero (δ : U S.J) (j : p) :
    ∃ i : n, (δ.val.val * P.k) i j ≠ 0 := by
  by_contra! h_col
  have h_pair : (δ.val.val * P.l)ᴴ * S.J * (δ.val.val * P.k) = 1 :=
    (U.gram_invariant ..).trans P.gram_lk
  -- The diagonal entry `j` of this pairing would be zero.
  simpa [Matrix.mul_apply, h_col] using congrFun₂ h_pair j j

/-- Let `γ k` be orthogonal to the Lagrangian `L` of `S`, where `k` is the isotropic frame of the
complete splitting `P` (`h_orth` tests this on the frame of the chosen splitting of `L`), and let
`δ` be a rational isometry with `γ k = δ k y` for an invertible `y`. Then `L` is the Lagrangian
spanned by the columns of `δ k`: that is the Lagrangian of `(isometrySplitting δ).comp P`, the
splitting `P` moved by `δ`. -/
lemma lagrangian_isometrySplitting_comp_eq (L : Lagrangian S) {γ δ : U S.J} {y : GL p E}
    (h_orth : L.chosenSplitting.kᴴ * S.J * (γ.val.val * P.k) = 0)
    (h_frame : γ.val.val * P.k = δ.val.val * (P.k * y.val)) :
    CompleteSplitting.lagrangian ((isometrySplitting δ).comp P) = L := by
  -- The columns of `δ k` are orthogonal to `L`, so they lie in `L`.
  refine eq_of_le ?_
  rintro _ ⟨v, rfl⟩
  have h_zero : L.chosenSplitting.kᴴ * S.J * (δ.val.val * P.k) = 0 := by
    -- Cancel the invertible `y` in `γ k = δ k y`.
    rw [← Matrix.mul_one (_ * (δ.val.val * P.k)), ← y.mul_inv, ← Matrix.mul_assoc,
      Matrix.mul_assoc _ _ y.val, Matrix.mul_assoc δ.val.val, ← h_frame, h_orth, Matrix.zero_mul]
  have h_dot : L.chosenSplitting.kᴴ *ᵥ S.J *ᵥ
      ((isometrySplitting δ).comp P).k.mulVecLin v = 0 := by
    simpa [Splitting.comp, isometrySplitting, Matrix.mul_assoc]
      using congrArg (· *ᵥ (v ∘ Sum.inr)) h_zero
  refine (L.property _).2 ?_
  rw [← congrArg Subtype.val L.lagrangian_chosenSplitting]
  exact forall_colSpan_dot_eq_zero_iff.2 h_dot

open Pointwise in
/-- Let `P` be a complete splitting of `S` into `p` hyperbolic planes and let `T` have rank greater
than `2 p`. There is a summable function `c` on the Lagrangians `L` of `S` such that, for every
`x : p → ℕ`, the operator norm of `Lagrangian.zeroTerm T L` composed with `normalisedTorus T P x` is
at most `c L`. Here the zero term along `L` sends `f` to its value at `0` in the Schrödinger model
of a splitting whose frame `k` spans `L`, and `normalisedTorus T P x` is `splitWeil S T` of the Levi
element `diag (2 ^ x i)` (entries `1` at the finite places) scaled by
`2 ^ (-d * rank T * ∑ i, x i)`, with `d` the number of infinite places. At `x = 0` this is the
convergence of the Eisenstein series in the Siegel–Weil formula. -/
lemma exists_summable_zeroTerm_bound (hm : 2 * Fintype.card p < Fintype.card m) :
    ∃ c : Lagrangian S → ℝ,
      Summable c ∧
      ∀ (x : p → ℕ) (L : Lagrangian S),
        ‖Lagrangian.zeroTerm T L ∘L normalisedTorus T P x‖ ≤ c L := by
  -- Put each `L` in the normal form `exists_compact_parabolic_normal_form` at `g = 1`, with torus
  -- exponents `d + t L`, `t L ∈ ℕ^p`. Then the term of `L` is `O(2 ^ (-f ∑ t L i * card m))` with
  -- `f = Core.numInfPlaces E`, while only `O(2 ^ (2 f ∑ t i * card p))` Lagrangians have a given
  -- `t`; the geometric series converges as `2 * card p < card m`.
  obtain ⟨Ω, hΩ, normal⟩ := exists_compact_parabolic_normal_form P
  obtain ⟨N, hN, hN_cover⟩ := IsCovolOneLattice.exists_compact_cover (ratMatrices E p p)
  -- The columns of `γ L * k` are orthogonal to `L`.
  choose γ hγ using fun L : Lagrangian S ↦
    exists_isometry_orthogonal P ⟨_, gram_lk _⟩ L.chosenSplitting.gram_kk
  choose δ x y ν hκ hy using fun L ↦ normal 1 (γ L)
  -- `d j` is a threshold below which a scaled rational entry in column `j` must vanish.
  let column (j : p) : Set (𝔸 E) := ⋃ i : n,
    (fun q : Matrix p p (𝔸 E) × _ ↦ (S.x.val * q.2⁻¹.adeleMatrix * P.kAdelic) i j) '' Ω
  choose d hd using fun j : p ↦ exists_eq_zero_of_zpow_mul_mem (B := column j) <|
    isCompact_iUnion fun i ↦ hΩ.image_of_continuous _
  -- Column `j` of `δ L * k` is rational, not zero, and `2 ^ x L j` times a bounded vector.
  have d_le (L : Lagrangian S) (j : p) : d j ≤ x L j := by
    refine not_lt.1 fun hlt ↦ ?_
    obtain ⟨i, hi⟩ := exists_mul_k_apply_ne_zero P (δ L) j
    refine hi (hd j (x L j) hlt ⟨_, ⟨i, rfl⟩, _, hκ L, ?_⟩)
    simp [← (adeleMatrix _).mul_assoc, ← map_inv, adeleMatrix_ratEmbed, dyadicDiag,
      Matrix.mul_assoc, actsOnFrame_levi, actsOnFrame_radicalElement]
    simp [kAdelic, ← Matrix.mul_assoc, mul_comm, ↓ ← Matrix.map_mul]
  choose t ht using fun (L : Lagrangian S) (j : p) ↦ le.dest (d_le L j)
  obtain rfl : (fun L j ↦ d j + t L j : Lagrangian S → p → ℤ) = x := funext₂ ht
  let K : Set (G E s) :=
    P.radicalElement 0 '' N * (fun q ↦ (P.levi (dyadicDiag d, 1))⁻¹ * q.2) '' Ω
  have hK : IsCompact K := (hN.image_of_continuous _).mul (hΩ.image_of_continuous _)
  -- Three uniform bounds: on the operators attached to points of `K`, on rational points of
  -- `K⁻¹ * K`, and on rational hermitian matrices in a scaled compact set.
  obtain ⟨R, hR⟩ := exists_zeroTerm_normalisedTorus_le T P P P.kCoord (by simp) hK
  obtain ⟨F, hF⟩ : ∃ F : ℕ, (S.ratEmbed ⁻¹' (K⁻¹ * K)).encard = F :=
    (tendsto_cofinite_cocompact_iff.1 (tendsto_coe_cofinite_of_isDiscrete S.ratEmbed_injective
      ⟨S.discreteTopology_Gamma⟩) _ (hK.inv.mul hK)).exists_encard_eq_coe
  obtain ⟨C, hC, herm_le⟩ := encard_hermitian_le <|
    ((isCompact_closedBall_prod_integral (E := E)).matrix.prod (hN.prod hΩ)).image_of_continuous
    fun (a, u, v, _) ↦ a * (u + uᴴ) * aᴴ - (v + vᴴ)
  -- Restate `hy` with matrices over `E`.
  replace hy (L : Lagrangian S) :
      (γ L).val.val * P.k = (δ L).val.val * (P.k * (y L).val) := by
    simpa [kAdelic, -map_inv, adeleMatrix_ratEmbed, coe_units_inv,
      inv_mul_eq_iff_eq_mul_of_invertible,
      (map_injective (toAdele (E := E)).injective).eq_iff, Matrix.mul_assoc,
      ↓ ← Matrix.map_mul] using hy L
  -- The unipotent of a rational `b L` moves `P.levi (dyadicDiag (t L), 1) * (δ L)⁻¹` into `K`;
  -- `InK L ρ` says this with `ρ` for `δ L`.
  let diagT (L : Lagrangian S) : GL p (𝔸 E) := dyadicDiag fun i ↦ t L i
  choose b b_mem using fun L ↦ show ∃ a : Matrix p p E,
      a.map toAdele + (diagT L).val * ν L * (diagT L).valᴴ ∈ N by
    simpa [ratMatrices] using hN_cover ((diagT L).val * ν L * (diagT L).valᴴ)
  let InK (L : Lagrangian S) (ρ : U S.J) : Prop :=
    P.radicalElement 0 ((b L).map toAdele) * P.levi (diagT L, 1) * S.ratEmbed ρ⁻¹ ∈ K
  have h_inK (L : Lagrangian S) : InK L (δ L) :=
    ⟨_, ⟨_, b_mem L, rfl⟩, _, ⟨_, hκ L, rfl⟩, by simp [diagT, ← inl_apply, -coe_diagGL,
      ↓ ← radicalElement_zero_mul, dyadicDiag, mul_assoc, _root_.zpow_add, ↓ ← Pi.mul_def]⟩
  have lag_eq (L : Lagrangian S) :
      CompleteSplitting.lagrangian ((isometrySplitting (δ L)).comp P) = L :=
    lagrangian_isometrySplitting_comp_eq P L (hγ L) (hy L)
  -- Counting: on a fibre of `t`, `InK L` depends only on `b L + (b L)ᴴ`, so `L` is determined by
  -- that hermitian matrix and the rational point `epsilon (InK L) * (δ L)⁻¹` of `K⁻¹ * K`.
  have fibre_le (x : p → ℕ) : ((t ⁻¹' {x}).encard : ℝ≥0∞) ≤
      C * .ofReal ((2 ^ Core.numInfPlaces E) ^ ∑ i : p, ∑ j : p, (x i + x j : ℤ).toNat) * F := by
    refine (mul_le_mul_left (herm_le fun i ↦ x i) F).trans' ?_
    rw_mod_cast [← hF, ← encard_prod]
    refine encard_le_encard_of_injOn
      (f := fun L ↦ (b L + (b L)ᴴ, Classical.epsilon (InK L) * (δ L)⁻¹))
      (fun L hL ↦ ⟨⟨by simp [add_comm], ?_⟩, ?_⟩) fun L hL M hM ↦ ?_
    · refine ⟨(_, _, _), ⟨dyadicDiag_inv_mem x, b_mem L, hκ L⟩, ?_⟩
      ext <;> simp [diagT, hL.symm, ← map_inv, add_sub_add_comm, mul_add, twoAtInfinity, field,
        dyadicDiag, _root_.zpow_add]
    · exact ⟨_, inv_mem_inv.2 (Classical.epsilon_spec ⟨_, h_inK L⟩), _, h_inK L,
        by simp [mul_assoc]⟩
    · simp +contextual [InK, diagT, radicalElement, ← Matrix.map_add, hL.trans hM.symm,
        ← (lag_eq L).congr (lag_eq M)]
  let bound (L : Lagrangian S) : ℝ≥0∞ :=
    R / ((2 ^ Core.numInfPlaces E) ^ ∑ i : p, t L i) ^ card m
  have h_finite : ∑' L : Lagrangian S, bound L < ∞ :=
    tsum_div_two_pow_lt_top R (by simp) hm hC fibre_le
  refine ⟨fun L ↦ (bound L).toReal, summable_toReal h_finite.ne,
    fun x L ↦ (_ ∘L _).opNorm_le_bound toReal_nonneg fun f ↦ ?_⟩
  -- The term of `L` is the term of `P.lagrangian` after `(δ L)⁻¹`; the factors `radicalElement` and
  -- `levi` of the point of `K` multiply its norm by `1` and by
  -- `√|det (dyadicDiag (t L))| ^ card m` (`norm_zeroTerm_parabolic_mul`).
  have h_term (g : 𝒮 (S.hom T)) : L.zeroTerm T g =
      P.lagrangian.zeroTerm T (splitWeil S T (S.ratEmbed (δ L)⁻¹, 1) g) := by
    rw [← zeroTerm_lagrangian_isometrySplitting_comp, lag_eq L]
  have h_norm (g : 𝒮 (S.hom T)) : ‖P.lagrangian.zeroTerm T (splitWeil S T
      (P.radicalElement 0 ((b L).map toAdele) * P.levi (diagT L, 1) * S.ratEmbed (δ L)⁻¹, 1) g)‖ =
      √(ideleAbs (diagT L).det) ^ card m * ‖L.zeroTerm T g‖ := by
    rw [mul_assoc, norm_zeroTerm_parabolic_mul (a := 1) (by simp [actsOnFrame_radicalElement]),
      norm_zeroTerm_parabolic_mul (actsOnFrame_levi ..), h_term]
    simp
  have h_bound : √(ideleAbs (diagT L).det) ^ card m *
      ‖L.zeroTerm T (normalisedTorus T P x f)‖ ≤ R * ‖f‖ := by
    simpa [← h_norm] using hR _ (h_inK L) x x rfl f
  simpa [bound, diagT, field, mul_comm, ideleAbs_det_dyadicDiag_natCast,
    Real.sqrt_sq_eq_abs] using h_bound

end New.SiegelWeil

end SiegelSets

/-!
## The Siegel–Weil formula in Weil's range

`New.SiegelWeil.normalisedTorus T P x`, for `x : p → ℕ`, is the normalised action of the torus
element `diag (2 ^ x i)` (at the infinite places) of the Levi subgroup of `P`. Let `ℓ` be the
difference of the two sides of `New.SiegelWeil.siegel_weil`. Splitting off one isotropic line and
using induction on the rank of `S`, `ℓ ∘ normalisedTorus T P x` tends to `0` as any `x ι → ∞`.
Siegel sets turn this into a bound in the cusp, from which
`New.SiegelWeil.eq_zero_of_le_tsum_zeroTerm` gives `ℓ = 0`.
-/

section SiegelWeilFormula

open Set Matrix MeasureTheory Filter Fintype New Core Space Splitting SiegelWeil.Lagrangian Metric
  Subsingleton

variable {E n m p : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p] {s : n → ℤˣ} {t : m → ℤˣ}
  {S : Space E n s} (T : Space E m t) (P : SiegelWeil.CompleteSplitting S p)

omit [WeilData E] in
/-- Let `P` be a complete splitting of `S` with frame `k` and let `D₁` split off the line spanned by
the column `ι` of `k`. The Levi element of `diag (2 ^ x i)` scales the row `D₁.lCoord` by the
conjugate of `2 ^ (-x ι)` (at the infinite places; `twoAtInfinity E` is `2` there and `1` at the
finite places; `adeleMatrix` is the matrix of a group element in standard coordinates). The row
`D₁.lCoord` gives the `l`-coordinate of an adelic vector in `D₁`. -/
lemma New.SiegelWeil.lCoord_mul_levi_dyadicDiag {n₁ : Type} [Fintype n₁] [DecidableEq n₁]
    {s₁ : n₁ → ℤˣ} {S₁ : Space E n₁ s₁} {ι : p}
    (D₁ : S.Splitting S₁ Unit) (hk : D₁.k = replicateCol Unit fun i : n ↦ P.k i ι) (x : p → ℕ) :
    D₁.lCoord * (P.levi (dyadicDiag (x ·), 1)).adeleMatrix =
      star (twoAtInfinity E ^ x ι)⁻¹.val • D₁.lCoord := by
  have h_row : P.lCoord * (P.levi (dyadicDiag (x ·), 1)).adeleMatrix =
      ((dyadicDiag (x ·) : GL p (𝔸 E))⁻¹.val)ᴴ * P.lCoord :=
    P.lCoord_mul_adeleMatrix (P.actsOnFrame_levi (dyadicDiag (x ·)) 1)
  ext1
  -- Entry `ι` of the row identity for `P`.
  simpa [dyadicDiag, ← map_inv, lCoord, kAdelic, hk] using! congrFun₂ h_row ι _

/-- Let `P` be a complete splitting of `S` into `p` planes, let the rank of `T` exceed `2 p`, and
let `D₁` split off the isotropic line spanned by the column `ι` of `P.k`, with complement `S₁`. As
`x ι → ∞`, uniformly for `f` in a compact set `C`, the integral over `[U(T)]` of the difference
between the theta function of the zero term of `normalisedTorus T P x f` along the line and that of
`normalisedTorus T P x f` tends to `0`. Here `splitWeil` is the Weil representation of the pair of
unitary groups, `D₁.homSource T` is the splitting that `D₁` gives of the space on which it acts, and
`T.quotMeasure` is the measure of `[U(T)]`. -/
lemma New.SiegelWeil.tendsto_integral_theta_zeroTerm_sub
    (hm : 2 * card p < card m) {n₁ : Type} [Fintype n₁] [DecidableEq n₁] {s₁ : n₁ → ℤˣ}
    {S₁ : Space E n₁ s₁} {ι : p} (D₁ : S.Splitting S₁ Unit)
    (hk : D₁.k = replicateCol Unit fun i : n ↦ P.k i ι) {C : Set (𝒮 (S.hom T))} (hC : IsCompact C) :
    Tendsto
      (fun z : (p → ℕ) × C ↦
        ∫ h : G E t, θ (S₁.hom T)
            (splitWeil S₁ T (1, h) ((D₁.homSource T).zeroTerm (normalisedTorus T P z.1 z.2))) -
          θ (S.hom T) (splitWeil S T (1, h) (normalisedTorus T P z.1 z.2)) ∂T.quotMeasure)
      (atTop.comap fun z : (p → ℕ) × C ↦ z.1 ι) (nhds 0) := by
  -- The zero term is a mean of Heisenberg translates. Moved through the torus element, the
  -- translations shrink by `2 ^ x ι` at infinity, and `theta_normalisedTorus_le` bounds the error
  -- by `B h` times the modulus of continuity of the translates on `C`.
  -- `B h` bounds the normalised theta function at `h`, uniformly in the torus element.
  obtain ⟨B, hB_meas, hB_fin, h_theta⟩ :
      ∃ B : G E t → ENNReal,
        Measurable B ∧
        ∫⁻ (h : G E t), B h ∂T.quotMeasure ≠ ⊤ ∧
        ∀ (h : G E t) (x : p → ℕ) (f : 𝒮 (S.hom T)),
          ‖(S.hom T).θ (splitWeil S T (1, h) (normalisedTorus T P x f))‖ₑ ≤ B h * ‖f‖ₑ :=
    theta_normalisedTorus_le T P hm
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ f ∈ C, ‖f‖ ≤ R := hC.isBounded.exists_norm_le
  obtain ⟨Ω, hΩ, h_cover⟩ := IsCovolOneLattice.exists_compact_cover (ratVectors E (m × Unit))
  let translate (h : G E t) (y : m × Unit → 𝔸 E) (f : 𝒮 (S.hom T)) : 𝒮 (S.hom T) :=
    ϱ _ ((h⁻¹.adeleMatrix * T.dualFrame⁻¹.val).kronecker D₁.lCoordᵀ *ᵥ y) f
  -- `modulus (a, h)` is the largest distance of `translate h (a • y) f` from `f` for
  -- `y ∈ Ω` and `f ∈ C`.
  let modulus : C(𝔸 E × G E t, ENNReal) :=
    ⟨fun a ↦ sSup ((fun y ↦ ‖translate a.2 (a.1 • y.1) y.2 - y.2‖ₑ) '' Ω ×ˢ C),
      (hΩ.prod hC).continuous_sSup (by fun_prop [kronecker, kroneckerMap])⟩
  have modulus_le (a : 𝔸 E × G E t) : modulus a ≤ ENNReal.ofReal (R + R) :=
    sSup_le <| forall_mem_image.mpr fun ⟨_, f⟩ ⟨_, hf⟩ ↦ by
      grw [← ofReal_norm, norm_sub_le, (heisenbergRep _).norm_map, hR _ hf]
  have modulus_zero (h : G E t) : modulus (0, h) = 0 := by simp [modulus, translate, sSup_image]
  -- By dominated convergence the integral of `B * modulus` tends to `0` with the scalar `a`.
  have h_lim : Tendsto (fun a : 𝔸f E × (NumberField.InfinitePlace E → ℂ) ↦
      ∫⁻ h : G E t, B h * modulus (a.swap, h) ∂T.quotMeasure) (nhds 0) (nhds 0) := by
    let Φ (a : 𝔸f E × (NumberField.InfinitePlace E → ℂ)) (h : G E t) : ENNReal :=
      B h * modulus (a.swap, h)
    have h_integrable : ∫⁻ h : G E t, B h * .ofReal (R + R) ∂T.quotMeasure ≠ ⊤ :=
      (lintegral_mul_const _ hB_meas).trans_ne (by finiteness)
    have h_meas (a : 𝔸f E × (NumberField.InfinitePlace E → ℂ)) : Measurable (Φ a) := by fun_prop
    have h_bound (a : 𝔸f E × (NumberField.InfinitePlace E → ℂ)) (h : G E t) :
        Φ a h ≤ B h * .ofReal (R + R) := mul_right_mono (modulus_le _)
    have h_pointwise : ∀ᵐ h ∂T.quotMeasure, Tendsto (Φ · h) (nhds 0) (nhds (Φ 0 h)) :=
      (ae_lt_top hB_meas hB_fin).mono fun _ _ ↦
        Continuous.tendsto (by fun_prop (disch := order)) 0
    simpa [Φ, modulus_zero] using tendsto_lintegral_filter_of_dominated_convergence _
      (.of_forall h_meas) (.of_forall fun a ↦ .of_forall (h_bound a)) h_integrable h_pointwise
  refine tendsto_zero_iff_enorm_tendsto_zero.mpr (ENNReal.tendsto_nhds_zero.mpr fun ε hε ↦ ?_)
  -- The scalar that is `M` at the finite places and `M / 2 ^ j` at infinity is small for a
  -- suitable integer `M` and large `j`.
  obtain ⟨M, hM, h_small⟩ : ∃ M : ℕ, M ≠ 0 ∧
      ∀ a ∈ Ô E, ∀ᶠ z : NumberField.InfinitePlace E → ℂ in nhds 0,
        ∫⁻ h : G E t, B h * modulus (Prod.swap (M * a, z), h) ∂T.quotMeasure ≤ ε :=
    mem_nhds_zero_finAdele_iff.mp (h_lim.eventually_le_const hε).curry_nhds
  let z (j : ℕ) : NumberField.InfinitePlace E → ℂ := (1 / 2 : ℝ) ^ j • ↑M
  have hz : Tendsto z atTop (nhds 0) := (summable_geometric_two.smul_const _).tendsto_atTop_zero
  filter_upwards [(hz.comp tendsto_comap).eventually (h_small 1 (one_mem _))] with ⟨x, f⟩ hx
  grw [enorm_integral_le_lintegral_enorm]
  refine le_trans (lintegral_mono fun h ↦ ?_) hx
  -- The torus element scales the row `D₁.lCoord`, and `h` commutes with the zero term.
  have h_torus := lCoord_mul_levi_dyadicDiag P D₁ hk x
  have h_comm (g : 𝒮 (S.hom T)) : splitWeil S₁ T (1, h) ((D₁.homSource T).zeroTerm g) =
      (D₁.homSource T).zeroTerm (splitWeil S T (1, h) g) := by
    simpa [splitWeil, D₁.card_eq, pow_succ, Prod.mk_one_one] using
      (D₁.homSlice_levi T _ 1 1 1 h 0 g).symm
  let F : 𝒮 (S.hom T) := splitWeil S T (1, h) (normalisedTorus T P x f)
  rw [h_comm, theta_apply, Splitting.zeroTerm_apply, ← edist_eq_enorm_sub]
  -- A mean lies in a closed ball if all values do.
  refine (convex_closedEBall ..).integral_mem isClosed_closedEBall (.of_forall fun q ↦ ?_)
    (isContPeriodic_along_k ..).integrable_out
  -- Write `q = M b` and move `b` into `Ω` by a rational `c`; the integrand is periodic.
  obtain ⟨b, hb⟩ : ∃ b : m × Unit → 𝔸 E, toAdele (M : E) • b = q.out :=
    ((Nat.cast_ne_zero (R := E).mpr hM).isUnit.map toAdele).smul_bijective.2 q.out
  obtain ⟨c, hc, hcb⟩ : ∃ γ ∈ ratVectors E (m × Unit), γ + b ∈ Ω := h_cover b
  let y : m × Unit → 𝔸 E := star (twoAtInfinity E ^ x ι)⁻¹.val • (M • c + q.out)
  have hy : (Prod.swap (M * 1, z (x ι)) : 𝔸 E) • (c + b) = y := by
    ext <;> simp [y, z, ← hb, twoAtInfinity, mul_add]
  let along (v : m × Unit → 𝔸 E) : _ :=
    F ((D₁.homSource T).iAdelic *ᵥ 0 + (D₁.homSource T).kAdelic *ᵥ v)
  have h_periodic : along (M • c + q.out) = along q.out :=
    (isContPeriodic_along_k F 0).2 _ (nsmul_mem hc M) q.out
  have h_mem : ‖translate h y f - f‖ₑ ≤ modulus (Prod.swap (M * 1, z (x ι)), h) :=
    le_sSup ⟨(c + b, f), ⟨hcb, f.prop⟩, by simp only [hy]⟩
  calc edist (along q.out) (θ _ F)
    _ = edist (along (M • c + q.out)) (θ _ F) := by rw [h_periodic]
    _ = ‖θ _ (splitWeil S T (1, h) (normalisedTorus T P x (translate h y f - f)))‖ₑ := by
      -- Commute the translation past `h` and the torus element, using `h_torus`.
      simp only [along, F, translate, y]
      simp [normalisedTorus, rho_pairWeil, -theta_apply, h_torus, ← mul_sub, ← theta_rho,
        splitWeil, ↓mulVec_smul, kronecker_mulVec_eq_matrixToVec, homSource_kAdelic,
        edist_eq_enorm_sub, Matrix.mul_assoc]
    _ ≤ B h * ‖translate h y f - f‖ₑ := h_theta h x _
    _ ≤ B h * modulus (Prod.swap (M * 1, z (x ι)), h) := mul_right_mono h_mem

/-- Let `T` have nonzero rank, and let the Lagrangian `L` of `S` not contain the column `ι` of
`P.k`, where `P` is a complete splitting `S = l E ^ p ⊕ k E ^ p` with isotropic frame `P.k`. Then
the zero term along `L` of `normalisedTorus T P x f` tends to `0` as `x ι → ∞`, uniformly for `f` in
a set `C` of norm at most `R`. Here `normalisedTorus T P x` is the normalised action of the torus
element `diag (2 ^ x i)`, and the zero term along `L` sends `f` to the mean of `θ (ϱ z f)` over the
maps `z : S → T` vanishing on `L`, adelic modulo rational. -/
lemma New.SiegelWeil.tendsto_zeroTerm_of_notMem (hm : card m ≠ 0) {L : Lagrangian S} {ι : p}
    (hL_notMem : P.k.col ι ∉ L.val) {C : Set (𝒮 (S.hom T))} {R : ℝ}
    (h_norm_le : ∀ f ∈ C, ‖f‖ ≤ R) :
    Tendsto (fun z : (p → ℕ) × C ↦ Lagrangian.zeroTerm T L (normalisedTorus T P z.1 z.2))
      (atTop.comap fun z : (p → ℕ) × C ↦ z.1 ι) (nhds 0) := by
  -- Write `L = k' E^r` and extend `l'* J` from `L` to a rational `Y` that kills column `ι` of `k`.
  obtain ⟨⟨r, P'⟩, rfl⟩ : { P : (r : ℕ) × CompleteSplitting S (Fin r) // P.snd.lagrangian = L } :=
    L.completeSplitting
  obtain ⟨Y, hY, hYι⟩ : ∃ Y : Matrix (Fin r) n E,
      (∀ v ∈ P'.lagrangian.val, Y *ᵥ v = (P'.lᴴ * S.J) *ᵥ v) ∧ Y *ᵥ P.k.col ι = 0 := by
    obtain ⟨φ, hφ, hφι⟩ :=
      ((P'.lᴴ * S.J).toLin'.domRestrict P'.lagrangian.val).exists_extend_of_notMem hL_notMem 0
    exact ⟨LinearMap.toMatrix' φ, fun v hv ↦ by simpa using LinearMap.congr_fun hφ ⟨v, hv⟩,
      by simpa using hφι⟩
  have hYk : Y * P'.k = 1 :=
    ext_iff_mulVec.mpr fun v ↦ by simpa [← Matrix.mul_assoc] using hY _ ⟨v, rfl⟩
  have h_left_inv : Y.map (toAdele : E → 𝔸 E) * (S.x : Matrix n n (𝔸 E)) * kAdelic P' = 1 := by
    simp [kAdelic, ← Matrix.mul_assoc, ← Matrix.map_mul, hYk]
  obtain ⟨c, hc⟩ := exists_zeroTerm_normalisedTorus_le T P P' (Y.map toAdele * S.x.val) h_left_inv
    (isCompact_singleton (x := 1))
  -- Column `ι` of `Y k` vanishes, so the exponent `x ι` may be replaced by `0`.
  have hYkι (i : Fin r) : (Y * P.k) i ι = 0 := congrFun hYι i
  have bound (x : p → ℕ) (f : 𝒮 (S.hom T)) :
      ‖Lagrangian.zeroTerm T P'.lagrangian (normalisedTorus T P x f)‖ ≤
        c * ‖f‖ / ((2 ^ Core.numInfPlaces E) ^ x ι) ^ card m := by
    let u : p → ℕ := indicator {ι}ᶜ x
    -- `Z` applies `Y`, a left inverse of the frame of `P'`, to the columns of the frame of `P`.
    let Z : Matrix (Fin r) p (𝔸 E) :=
      Y.map toAdele * S.x.val * G.adeleMatrix (1 : G E s) * kAdelic P
    have h_same : Z * (dyadicDiag (x ·) : GL p (𝔸 E)).val =
        Z * (dyadicDiag (u ·) : GL p (𝔸 E)).val := by
      simp [Z, u, indicator, kAdelic, dyadicDiag, ← ext_iff, ← Matrix.mul_assoc, ← Matrix.map_mul,
        apply_ite, hYkι]
    have h_exp : ∑ i : p, (u i : ℤ) - ∑ i : p, (x i : ℤ) = -(x ι : ℤ) := by
      simp [u, indicator, ← Finset.sum_sub_distrib, apply_ite, ite_sub]
    simpa [h_exp, div_eq_mul_inv, Prod.mk_one_one] using hc 1 rfl x u h_same f
  refine squeeze_zero_norm (fun z ↦ (bound z.1 z.2).trans (by grw [h_norm_le _ z.2.prop])) ?_
  have h_grow : Tendsto (fun z : (p → ℕ) × C ↦ (((2 : ℝ) ^ Core.numInfPlaces E) ^ z.1 ι) ^ card m)
      (atTop.comap fun z : (p → ℕ) × C ↦ z.1 ι) atTop :=
    (tendsto_pow_atTop hm).comp
      ((tendsto_pow_atTop_atTop_of_one_lt (mod_cast by simp)).comp tendsto_comap)
  exact h_grow.const_div_atTop _

/-- Let `ℓ` be a continuous linear functional on `𝒮 (S.hom T)` that is invariant under the rational
points of `S`. Suppose that `ℓ (normalisedTorus T P x f)` tends to `0` as any `x ι → ∞`, uniformly
for `f` in compact sets, and that the zero terms are absolutely summable over the Lagrangians of
`S`. Then for each `f`, `‖ℓ (ω(g) f)‖` exceeds `∑' L, ‖zeroTerm L (ω(g) vacElem)‖` by at most a
constant independent of `g`. Here `ω(g)` is `splitWeil S T (g, 1)`, `vacElem` is the vacuum vector
of `𝒮`, `normalisedTorus T P x` is the normalised action of the torus element `diag (2 ^ x i)`, and
the zero term along a Lagrangian `L` sends `f` to the mean of `θ (ϱ z f)` over the maps `z : S → T`
vanishing on `L`, adelic modulo rational. -/
lemma New.SiegelWeil.bddAbove_norm_sub_tsum_norm_zeroTerm {ℓ : 𝒮 (S.hom T) →L[ℂ] ℂ}
    (h_inv : ∀ (γ : U S.J) (f : 𝒮 (S.hom T)), ℓ (splitWeil S T (S.ratEmbed γ, 1) f) = ℓ f)
    (h_lim : ∀ C : Set (𝒮 (S.hom T)), IsCompact C → ∀ ι : p,
      Tendsto (fun z : (p → ℕ) × C ↦ ℓ (normalisedTorus T P z.1 z.2))
        (atTop.comap fun z : (p → ℕ) × C ↦ z.1 ι) (nhds 0))
    (h_summable : ∀ f : 𝒮 (S.hom T),
      Summable fun L : Lagrangian S ↦ ‖Lagrangian.zeroTerm T L f‖)
    (f : 𝒮 (S.hom T)) :
    BddAbove
      (range fun g : G E s ↦
        ‖ℓ (splitWeil S T (g, 1) f)‖ -
          ∑' L : Lagrangian S,
            ‖Lagrangian.zeroTerm T L (splitWeil S T (g, 1) (vacElem (S.hom T)))‖) := by
  -- Write `g = γ a_x κ` with `κ` in a compact set (`exists_siegel_set`). The uniform limit settles
  -- all but finitely many `x`; for the others `a_x κ` ranges over a compact set.
  obtain ⟨Ω, hΩ, h_siegel⟩ := exists_siegel_set P
  -- `K` holds the translates of `f` by `κ ∈ Ω`, divided by the size `vacSize κ > 0` of the zero
  -- term of the translated vacuum.
  let vacSize (κ : G E s) : ℝ := ‖P.lagrangian.zeroTerm T (splitWeil S T (κ, 1) (vacElem _))‖
  let K : Set (𝒮 (S.hom T)) := (fun κ ↦ (vacSize κ)⁻¹ • splitWeil S T (κ, 1) f) '' Ω
  have h_vacSize : Continuous fun κ : G E s ↦ (vacSize κ)⁻¹ :=
    .inv₀ (by fun_prop) fun κ ↦ (norm_zeroTerm_vacElem_pos T P κ).ne'
  have hK : IsCompact K := hΩ.image (by fun_prop)
  let bad : Set (p → ℕ) := {x | ∃ v ∈ K, 1 < ‖ℓ (normalisedTorus T P x v)‖}
  have h_fin : bad.Finite := by
    -- For each `ι` the norm is at most `1` for large `x ι`, so each coordinate of a bad `x` lies
    -- in a finite set.
    have h_ev (ι : p) : ∀ᶠ j : ℕ in cofinite,
        ∀ z : (p → ℕ) × K, z.1 ι = j → ‖ℓ (normalisedTorus T P z.1 z.2)‖ ≤ 1 :=
      Nat.cofinite_eq_atTop.le (eventually_comap.mp
        ((h_lim K hK ι).norm.eventually_le_const (by simp)))
    exact (Finite.pi' h_ev).subset
      fun x ⟨v, hv, h_gt⟩ ι h_le ↦ h_gt.not_ge (h_le (x, ⟨v, hv⟩) rfl)
  let a (x : p → ℕ) : G E s := P.levi (dyadicDiag (x ·), 1)
  obtain ⟨B, hB₀, hB⟩ :
      ∃ B > (0 : ℝ),
        ∀ z ∈ (fun g : G E s ↦ ℓ (splitWeil S T (g, 1) f)) '' Set.image2 (· * ·) (a '' bad) Ω,
        ‖z‖ ≤ B :=
    (((h_fin.image a).isCompact.mul hΩ).image (by fun_prop)).isBounded.exists_pos_norm_le
  refine ⟨B, forall_mem_range.mpr fun g ↦ sub_le_iff_le_add'.mpr ?_⟩
  obtain ⟨γ, x, κ, hκ, rfl⟩ := h_siegel g
  -- `ℓ` does not see `γ`, which moves the zero term along each `L` to that along `σ L`.
  obtain ⟨σ, hσ⟩ :
      ∃ σ : Lagrangian S ≃ { L : Lagrangian S // colSpan (isometrySplitting γ).k ≤ L },
        ∀ (L : Lagrangian S) (f : 𝒮 (S.hom T)),
        Lagrangian.zeroTerm T (σ L) f = Lagrangian.zeroTerm T L (Splitting.zeroTerm f) :=
    exists_lagrangian_equiv_containing T (isometrySplitting γ)
  rw [mul_assoc, ← Prod.mk_one_mul_mk_one, ← rep_apply_apply, h_inv]
  by_cases hx : x ∈ bad
  · exact le_add_of_nonneg_of_le (by positivity)
      (hB _ (mem_image_of_mem _ (mul_mem_mul (mem_image_of_mem a hx) hκ)))
  have h_small : ‖ℓ (normalisedTorus T P x ((vacSize κ)⁻¹ • splitWeil S T (κ, 1) f))‖ ≤ 1 :=
    not_lt.1 fun h_gt ↦ hx ⟨_, mem_image_of_mem _ hκ, h_gt⟩
  -- Keep only the term of `σ P.lagrangian`; the torus scales it by the factor that normalises
  -- `normalisedTorus`.
  let v : 𝒮 (S.hom T) := splitWeil S T ((S.ratEmbed γ, 1) * (a x * κ, 1)) (vacElem (S.hom T))
  have h_term :
      ‖ℓ (splitWeil S T (a x * κ, 1) f)‖ ≤ ‖Lagrangian.zeroTerm T (σ P.lagrangian).val v‖ := by
    simpa [v, a, vacSize, hσ, zeroTerm_isometrySplitting, normalisedTorus,
      norm_zeroTerm_parabolic_mul (actsOnFrame_levi ..), rep_apply_apply, field,
      div_le_iff₀ (norm_zeroTerm_vacElem_pos ..), mul_assoc, ideleAbs_det_dyadicDiag_natCast,
      Real.sqrt_sq_eq_abs] using h_small
  exact (h_term.trans ((h_summable v).le_tsum _ fun L _ ↦ norm_nonneg _)).trans
    (le_add_of_nonneg_right hB₀.le)

/-- Let `D₁` split off the isotropic line spanned by the column `ι` of `P.k`. The Lagrangians of the
complement `S₁` correspond to the Lagrangians of `S` through that line, and the zero term along the
image of `L` is the zero term along `L` taken after the zero term along the line. -/
lemma New.SiegelWeil.exists_lagrangian_equiv_col_mem
    {n₁ : Type} [Fintype n₁] [DecidableEq n₁] {s₁ : n₁ → ℤˣ} {S₁ : Space E n₁ s₁} {ι : p}
    (D₁ : S.Splitting S₁ Unit) (hk : D₁.k = replicateCol Unit fun i : n ↦ P.k i ι) :
    ∃ σ : Lagrangian S₁ ≃ {L : Lagrangian S // P.k.col ι ∈ L.val},
      ∀ (L : Lagrangian S₁) (f : 𝒮 (S.hom T)),
        Lagrangian.zeroTerm T (σ L).val f =
          Lagrangian.zeroTerm T L ((D₁.homSource T).zeroTerm f) := by
  obtain ⟨τ, hτ⟩ := exists_lagrangian_equiv_containing T D₁
  refine ⟨τ.trans (.subtypeEquivRight fun L ↦ ?_), hτ⟩
  -- The span of a single column lies in `L` exactly when the column does.
  have h_col : D₁.k.col PUnit.unit = P.k.col ι := congrArg (·.col PUnit.unit) hk
  simp [range_mulVecLin, range_unique, h_col]

/-- The induction step of the Siegel–Weil formula. In Weil's range, let `D₁` split off the line
spanned by the column `ι` of `P.k`, let the zero terms of `S` be summable and theta integrable, and
let the formula hold for the complement `S₁`. Then the difference of the two sides of the formula
for `S` at `normalisedTorus T P x f` tends to `0` as `x ι → ∞`, uniformly for `f` in a compact
set. Here Weil's range means `2 * card p < card m`, `θ` is the theta functional on the test
functions and `splitWeil` is the Weil representation of the pair of unitary groups. -/
lemma New.SiegelWeil.tendsto_tsum_zeroTerm_sub_integral_theta (hm : 2 * card p < card m)
    (h_summable : ∀ f : 𝒮 (S.hom T), Summable fun L : Lagrangian S ↦ Lagrangian.zeroTerm T L f)
    (h_int : ∀ f : 𝒮 (S.hom T),
      Integrable (fun h : G E t ↦ θ (S.hom T) (splitWeil S T (1, h) f)) T.quotMeasure)
    {n₁ : Type} [Fintype n₁] [DecidableEq n₁] {s₁ : n₁ → ℤˣ} {S₁ : Space E n₁ s₁} {ι : p}
    (D₁ : S.Splitting S₁ Unit) (hk : D₁.k = replicateCol Unit fun i : n ↦ P.k i ι)
    (h_formula : ∀ f : 𝒮 (S₁.hom T),
      Integrable (fun h : G E t ↦ θ (S₁.hom T) (splitWeil S₁ T (1, h) f)) T.quotMeasure ∧
      ∫ h : G E t, θ (S₁.hom T) (splitWeil S₁ T (1, h) f) ∂T.quotMeasure =
        T.quotMeasure.real univ * ∑' L : Lagrangian S₁, Lagrangian.zeroTerm T L f)
    {C : Set (𝒮 (S.hom T))} (hC : IsCompact C) :
    Tendsto
      (fun z : (p → ℕ) × C ↦
        T.quotMeasure.real univ *
            ∑' L : Lagrangian S, Lagrangian.zeroTerm T L (normalisedTorus T P z.1 z.2) -
          ∫ h : G E t, θ (S.hom T) (splitWeil S T (1, h) (normalisedTorus T P z.1 z.2))
            ∂T.quotMeasure)
      (atTop.comap fun z : (p → ℕ) × C ↦ z.1 ι) (nhds 0) := by
  -- The terms through the line give theta of `S₁` by the formula; those off the line tend to `0`.
  obtain ⟨σ, hσ⟩ := exists_lagrangian_equiv_col_mem T P D₁ hk
  let A : Set (Lagrangian S) := {L | P.k.col ι ∈ L.val}
  have h_on (g : 𝒮 (S.hom T)) :
      (T.quotMeasure.real univ : ℂ) * ∑' L : A, Lagrangian.zeroTerm T L.val g =
        ∫ h : G E t, θ (S₁.hom T) (splitWeil S₁ T (1, h) ((D₁.homSource T).zeroTerm g))
          ∂T.quotMeasure := by
    rw [(h_formula _).2]
    exact congrArg _ ((σ.tsum_eq _).symm.trans (tsum_congr (hσ · g)))
  have h_split (g : 𝒮 (S.hom T)) :
      T.quotMeasure.real univ * ∑' L : Lagrangian S, Lagrangian.zeroTerm T L g -
          ∫ h : G E t, θ (S.hom T) (splitWeil S T (1, h) g) ∂T.quotMeasure =
        ∫ h : G E t, (θ (S₁.hom T) (splitWeil S₁ T (1, h) ((D₁.homSource T).zeroTerm g)) -
            θ (S.hom T) (splitWeil S T (1, h) g)) ∂T.quotMeasure +
          T.quotMeasure.real univ * ∑' L : ↑Aᶜ, Lagrangian.zeroTerm T L.val g := by
    rw [integral_sub (h_formula _).1 (h_int g), ← h_on,
      ← (h_summable g).tsum_subtype_add_tsum_subtype_compl A]
    ring
  -- The terms off the line tend to `0` one by one, and are dominated by `b L * R`.
  obtain ⟨b, hb, h_term⟩ := exists_summable_zeroTerm_bound T P hm
  obtain ⟨R, hR⟩ := hC.isBounded.exists_norm_le
  have h_off : Tendsto
      (fun z : (p → ℕ) × C ↦
        ∑' L : ↑Aᶜ, Lagrangian.zeroTerm T L.val (normalisedTorus T P z.1 z.2))
      (atTop.comap fun z : (p → ℕ) × C ↦ z.1 ι) (nhds (∑' _ : ↑Aᶜ, 0)) :=
    tendsto_tsum_of_dominated_convergence ((hb.mul_right R).subtype _)
      (fun L ↦ tendsto_zeroTerm_of_notMem T P hm.ne_bot L.prop hR) (.of_forall fun z L ↦
        ((Lagrangian.zeroTerm T L.val).comp (normalisedTorus T P z.1)).le_of_opNorm_le_of_le
          (h_term z.1 L) (hR _ z.2.prop))
  simpa [h_split, -theta_apply] using
    (tendsto_integral_theta_zeroTerm_sub T P hm D₁ hk hC).add
      (h_off.const_mul (T.quotMeasure.real univ : ℂ))

/-- If `T` has rank greater than `2 p`, the theta function `h ↦ θ (ω(1, h) f)` is integrable over
the quotient `[U(T)]` for every test function `f`, where `ω` is `splitWeil S T`. -/
lemma New.SiegelWeil.integrable_theta_splitWeil (P : SiegelWeil.CompleteSplitting S p)
    (hm : 2 * card p < card m) (f : 𝒮 (S.hom T)) :
    Integrable (fun h : G E t ↦ θ (S.hom T) (splitWeil S T (1, h) f)) T.quotMeasure := by
  -- It is dominated by `N h * ‖f‖ₑ`: this is `theta_normalisedTorus_le` at `x = 0`.
  obtain ⟨N, mN, hN, h_theta⟩ := theta_normalisedTorus_le T P hm
  refine ⟨by fun_prop, ?_⟩
  calc ∫⁻ h, ‖θ _ (splitWeil S T (1, h) f)‖ₑ ∂T.quotMeasure ≤ ∫⁻ h, N h * ‖f‖ₑ ∂T.quotMeasure :=
      lintegral_mono fun h ↦ by simpa [normalisedTorus_zero, -theta_apply] using h_theta h 0 f
    _ < ⊤ := (lintegral_mul_const _ mN).trans_lt (by finiteness)

/-- The Siegel–Weil formula in Weil's range. Let `S` be split into `p` hyperbolic planes and let `T`
have rank greater than `2 p`. Then the operator norms of the zero terms along the Lagrangians `L` of
`S` are summable. Moreover, for every `f` the function `h ↦ θ (ω(1, h) f)` is integrable for the
measure `T.quotMeasure` of the quotient `[U(T)]`, and its mean (integral divided by total mass)
equals the sum of the zero terms of `f`, that is, the Eisenstein series at `f`. Here `ω` is the Weil
representation `splitWeil S T`, `𝒮 (S.hom T)` is the space of test functions on which it acts, and
the zero term of `f` along `L` is the value of `f` at `0` in the Schrödinger model of a splitting
whose isotropic frame spans `L`. An integrable majorant of theta that is uniform in `f` is given by
`New.SiegelWeil.theta_normalisedTorus_le`.

The pairs are unimodular over a CM field with `WeilData`, and the test functions are taken in `𝒮`
rather than among Schwartz–Bruhat functions. -/
theorem New.SiegelWeil.siegel_weil (P : SiegelWeil.CompleteSplitting S p)
    (hm : 2 * card p < card m) :
    (Summable fun L : Lagrangian S ↦ ‖Lagrangian.zeroTerm T L‖) ∧
    ∀ f : 𝒮 (S.hom T),
      Integrable (fun h : G E t ↦ θ (S.hom T) (splitWeil S T (1, h) f)) T.quotMeasure ∧
      ∫ h : G E t, θ (S.hom T) (splitWeil S T (1, h) f) ∂T.quotMeasure =
        T.quotMeasure.real univ * ∑' L : Lagrangian S, Lagrangian.zeroTerm T L f := by
  classical
  -- Let `ℓ` be the volume times the sum of the zero terms minus the integral of theta. By
  -- induction on `card n`, `ℓ` tends to `0` along the torus, so it is small in the cusp and
  -- `eq_zero_of_le_tsum_zeroTerm` gives `ℓ = 0`.
  induction h_card : card n using Nat.strongRec generalizing n p with | _ d IH =>
  -- The zero terms of `normalisedTorus T P x` have norm at most `b L` with `b` summable; at
  -- `x = 0` this gives summability.
  obtain ⟨b, hb, h_term⟩ := exists_summable_zeroTerm_bound T P hm
  have h_int := integrable_theta_splitWeil T P hm
  have hs : Summable fun L : Lagrangian S ↦ ‖Lagrangian.zeroTerm T L‖ :=
    hb.of_nonneg_of_le (fun L ↦ norm_nonneg _) fun L ↦ by
      simpa [ContinuousLinearMap.one_def] using h_term 0 L
  have h_sum (f : 𝒮 (S.hom T)) : HasSum (fun L : Lagrangian S ↦ Lagrangian.zeroTerm T L f)
      ((∑' L : Lagrangian S, Lagrangian.zeroTerm T L) f) := hs.of_norm.hasSum.mapL (.apply ℂ _ f)
  let ℓ : 𝒮 (S.hom T) →L[ℂ] ℂ :=
    T.quotMeasure.real univ • ∑' L : Lagrangian S,
      Lagrangian.zeroTerm T L - strongIntegral T.quotMeasure fun h ↦ θ _ ∘L splitWeil S T (1, h)
  have hℓ (f : 𝒮 (S.hom T)) :
      ℓ f = T.quotMeasure.real univ * ∑' L : Lagrangian S, Lagrangian.zeroTerm T L f -
        ∫ h : G E t, θ _ (splitWeil S T (1, h) f) ∂T.quotMeasure := by
    rw [(h_sum f).tsum_eq]
    simp [ℓ, strongIntegral_apply T.quotMeasure (fun h ↦ θ _ ∘L splitWeil S T (1, h)) h_int,
      -theta_apply]
  refine ⟨hs, fun f ↦ ⟨h_int f, ?_⟩⟩
  cases isEmpty_or_nonempty n
  · -- For `S = 0` there is one Lagrangian, and theta is its zero term.
    simp [Lagrangian.zeroTerm, mixedValue, Splitting.zeroTerm_apply, pairWeil, eq_one (G.onHom _),
      eq_zero (_ + _), sum_subsingleton _ P.lagrangian]
  have h_lim (C : Set (𝒮 (S.hom T))) (hC : IsCompact C) (ι : p) :
      Tendsto (fun z : (p → ℕ) × C ↦ ℓ (normalisedTorus T P z.1 z.2))
        (atTop.comap fun z : (p → ℕ) × C ↦ z.1 ι) (nhds 0) := by
    -- Split off the line spanned by the column `ι`. Its complement `S₁` has a Lagrangian, hence a
    -- complete splitting, and the formula holds for it by induction.
    let k : Matrix n Unit E := replicateCol Unit fun i : n ↦ P.k i ι
    have hk_ne : (fun i : n ↦ P.k i ι) ≠ 0 := fun h_zero ↦ by
      simpa [funext_iff.mp h_zero] using exists_mul_k_apply_ne_zero P 1 ι
    have hk_isotropic : kᴴ * S.J * k = 0 :=
      congrArg (fun M : Matrix p p E ↦ M.submatrix (fun _ : Unit ↦ ι) fun _ : Unit ↦ ι) P.gram_kk
    obtain ⟨n₁, s₁, S₁, D₁, hk⟩ := S.exists_splitting (HasLeftInv.of_ne_zero hk_ne) hk_isotropic
    obtain ⟨σ, -⟩ := exists_lagrangian_equiv_col_mem T P D₁ hk
    let L₁ := σ.symm ⟨P.lagrangian, Pi.single ι 1, mulVec_single_one P.k ι⟩
    have P₁ : CompleteSplitting S₁ (Fin L₁.numPlanes) := L₁.chosenSplitting
    obtain ⟨-, ih⟩ := IH _ (by simp [← h_card, D₁.card_eq]) P₁
      (by linarith [P.card_eq, P₁.card_eq, D₁.card_eq]) rfl
    simpa only [hℓ] using tendsto_tsum_zeroTerm_sub_integral_theta T P hm
      (fun g ↦ (h_sum g).summable) h_int D₁ hk ih hC
  -- `ℓ` is invariant under `U(T)(𝔸)` and under the rational points of `S`.
  have h_invT (h : G E t) (g : 𝒮 (S.hom T)) : ℓ (splitWeil S T (1, h) g) = ℓ g := by
    simpa [hℓ, Lagrangian.zeroTerm, mixedValue_splitWeil] using!
      Exchange.thetaIntegral_pairWeil (S := S) (T := T) (1, h) 1
  have h_invS (γ : U S.J) (g : 𝒮 (S.hom T)) :
      ℓ (splitWeil S T (S.ratEmbed γ, 1) g) = ℓ g := by
    obtain ⟨σ, hσ⟩ := exists_lagrangian_equiv_containing T (isometrySplitting γ)
    have h_aut (h : G E t) :
        θ _ (splitWeil S T (S.ratEmbed γ, h) g) = θ _ (splitWeil S T (1, h) g) := by
      simpa only [mul_one] using (pairThetaKer ..).theta_rat_mul _ ⟨γ, rfl⟩ 1
    rw [hℓ, ← (σ.trans (.subtypeUnivEquiv (by simp [isometrySplitting, colSpan]))).tsum_eq]
    simp [hℓ, hσ, zeroTerm_isometrySplitting, rep_apply_apply, h_aut, -theta_apply, Prod.mk_one_one]
  rw [eq_comm, ← sub_eq_zero, ← hℓ]
  exact eq_zero_of_le_tsum_zeroTerm (by simp [P.card_eq]) hm h_invT (fun g ↦ (h_sum g).summable)
    (bddAbove_norm_sub_tsum_norm_zeroTerm T P h_invS h_lim fun g ↦ (h_sum g).summable.norm)

end SiegelWeilFormula
