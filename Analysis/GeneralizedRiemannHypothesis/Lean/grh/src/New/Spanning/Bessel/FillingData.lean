import Lib.DiscreteSeries.Character.FormalDegree
import New.Determinant.AuxiliaryForms.DeepLevelPoincarePeriod
import New.Spanning.Bessel.CutTailBound
import New.Spanning.Bessel.SchurBound
import New.Spanning.Frames.RealBandLimits
import New.Spanning.Unfolding.Climbing
import New.UpperBound.Objects.Rows

/-!
# Filling data from admissible data, with Bessel systems at the real places

The filling theorem is stated for abstract data (`New.Filling`). This file builds such data from
admissible data D (`New.Data`). At each real place it constructs a Bessel system of the type fixed
by D. It then assembles these systems, the relevant primes and places, and the level `D.levelX 0`
into the filling data. It identifies that level with the preimage of the level K(M) of
`New.Filling.principalLevel`: here M = p₀ p₁, and K(M) includes a congruence modulo π.

## Main definitions and results

* `New.Data.exists_besselSystem`: the Bessel function at a real place, with its normalisation,
  Schur's bound, decay, cut and local bounds. That its coordinates are orthonormal is
  `New.BesselSystem.orthonormal`, in `New.Spanning.Bessel.Orthonormality`.
* `New.Data.filling`: the prime `New.Data.N`, the primes p₀, p₁ (field `levelPrime`) with their
  chosen places, the level `D.levelX 0` and a Bessel system at each infinite place.
* `New.Data.levelX_zero_eq_comap`: the level `D.levelX 0` is the preimage of the principal
  congruence subgroup K(M), that is `New.Filling.principalLevel`.

Notions from other files:
* `New.Data.piNIdele`: the principal finite idele of `π`, where `N = π π̄`; `New.Data.piNPlaces` is
  the set of places dividing `π`.
* `New.Data.piM`: the conjugate of the integer `D.piMBar` of norm `p₀ p₁`; the chosen places are its
  prime divisors.

## Relation to the literature

At a real place, integrals of a Bessel function on an indefinite unitary group against its
translates have Fourier transforms decaying beyond a band; the bounds themselves are proved in the
imported files. These integrals replace Petersson's J-Bessel kernel in showing that few translates
almost span the target forms. Rank one is classical, and Bessel kernels are studied for GL(n) and
GSp(4).

Related work: Petersson, Über die Entwicklungskoeffizienten der automorphen Formen, 1932; NIST DLMF
§10.22; Baruch, Bessel distributions on the open cell, 2001–2004; Comtat et al., Effective Kuznetsov
trace formula for GSp(4), 2025.
-/

namespace New.Data

/-!
## Bessel systems at the real places

The Bessel function at each real place is built at a stationary point given by
`New.DiscreteSeries.IsSteep.exists_stationary_point`.
-/

section BesselSystemExists

open MeasureTheory Matrix Finset Fintype Filling RealPlace DiscreteSeries Norms.L2Operator CStarRing
  MatrixOrder ConjAct

variable {P : Parameters} (D : Data P)

lemma card_X₀ : Fintype.card (D.X 0) = D.k := by grind [card_X, n]

/-- An orthonormal frame with the signs of `Y₀`. -/
noncomputable instance unitarySignFrameY : UnitarySignFrame D.shape (D.signsY 0 ·) :=
  Nonempty.some <|
  -- For a string of length `2 ϱ + 1`, `exists_conjTranspose_mul_gradedGram_mul_eq_signMatrix` asks
  -- for `ϱ + 1` minus signs.
  have ⟨p, hp_form, hp_unitary⟩ := Seesaw.exists_conjTranspose_mul_gradedGram_mul_eq_signMatrix
    D.shape.besselIndexEquiv (.id ℂ)
    one_pos ((D.negCount_gridSigns false 0 0).trans (by grind))
  ⟨{ matrix := (.mkOfMulEqOne _ _ (hp_unitary rfl))⁻¹
     gram_eq := by
       -- The two Gram matrices agree entry by entry.
       convert! hp_form
       simp [← ext_iff, gradedGram, Shape.besselIndexEquiv, splitGram, middleGram, Fin.rev,
         Matrix.one_apply]
       lia
     mem_unitary := ⟨hp_unitary rfl, Units.inv_mul _⟩ }⟩

/-- The Schur matrices of weight `w`, written in an orthonormal basis for their Gram form, give a
continuous unitary representation of U(n), with n = `𝔰.κ`, which is conjugate to the transposed
Schur matrices of transposes and is irreducible: only scalars commute with it. If `u` is the
Harish-Chandra parameter of the weight `w`, then `dsCoeff`, the coefficient attached to `u`, is a
diagonal matrix coefficient of it, seen as operators by `besselValueRep`. -/
lemma exists_unitary_schur_rep {𝔰 : Shape} {w : Unit → ℕ → ℕ} {u : Unit → HCParam (n := 𝔰.κ) 1}
    (hu : IsHCParam w 0 u) :
    ∃ rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup (WeylIndex 𝔰.κ w) ℂ,
      -- (a) `rep` is conjugate to the transposed Schur matrices of the transposes
      (∃ C : (Matrix (WeylIndex 𝔰.κ w) (WeylIndex 𝔰.κ w) ℂ)ˣ, ∀ h : U 1,
        C.val * (rep h).val = (schur w fun _ : Unit ↦ h.val.valᵀ)ᵀ * C.val) ∧
      -- (b) only scalars commute with `rep`
      (∀ M : Matrix (WeylIndex 𝔰.κ w) (WeylIndex 𝔰.κ w) ℂ,
        (∀ h : U 1, Commute M (rep h).val) → M ∈ Set.range (scalar (WeylIndex 𝔰.κ w))) ∧
      -- (c) continuity
      Continuous rep ∧
      -- (d) `dsCoeff` is a diagonal matrix coefficient
      ∃ v : EuclideanSpace ℂ (WeylIndex 𝔰.κ w), ∀ k : U 1,
        inner ℂ v ((besselValueRep rep k).val v) = (u ()).dsCoeff k := by
  -- Write the positive definite Gram matrix as `star B * B` and conjugate the Schur matrices by
  -- `B`: adjointness for the Gram form becomes adjointness for the standard form.
  obtain ⟨_, ⟨B, rfl⟩, h_gram⟩ : ∃ b : Matrix (WeylIndex 𝔰.κ w) (WeylIndex 𝔰.κ w) ℂ,
      IsUnit b ∧ weylGramOver = star b * b :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp weylGramOver_posDef.isStrictlyPositive
  let φ :=
    MulSemiringAction.toAlgEquiv ℂ (Matrix (WeylIndex 𝔰.κ w) (WeylIndex 𝔰.κ w) ℂ) (toConjAct B)
  have hφ (A : Matrix (WeylIndex 𝔰.κ w) (WeylIndex 𝔰.κ w) ℂ) : φ A = B.val * A * B.val⁻¹ := by
    simp [φ, units_smul_def]
  have h_unitary (g : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) :
      φ (schur w fun _ : Unit ↦ g.val.val) ∈ unitaryGroup (WeylIndex 𝔰.κ w) ℂ := by
    -- The Schur matrix of a unitary `g` keeps the Gram form.
    have h_form : (schur w fun _ : Unit ↦ g.val.val)ᴴ *
        (weylGramOver * schur w fun _ : Unit ↦ g.val.val) = weylGramOver (R := ℂ) := by
      simpa [← U.inv_val_eq_conjTranspose] using GL.schur_conjTranspose_weylGram_schur .refl
        (κ := w) (fun _ : Unit ↦ g.val.val) (fun _ : Unit ↦ g.val.val)
    rw [mem_unitaryGroup_iff', hφ]
    simpa [h_gram, star_eq_conjTranspose, conjTranspose_nonsing_inv, mul_assoc] using
      congrArg (fun A ↦ B.valᴴ⁻¹ * A * B.val⁻¹) h_form
  let rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup (WeylIndex 𝔰.κ w) ℂ :=
    .mk' (fun g ↦ ⟨φ (schur w fun _ : Unit ↦ g.val.val), h_unitary g⟩) (by simp [schur_mul_left])
  refine ⟨rep, ⟨star B, fun g ↦ ?_⟩, fun M hM ↦ ?_, ?_,
    .toLp 2 (B.val *ᵥ highestVector w u), fun k ↦ ?_⟩
  · -- `star B = weylGramOver * B⁻¹`, so this is adjointness for the Gram form.
    have h_adjoint : (weylGramOver * schur w fun _ : Unit ↦ g.val.val) =
        (schur w fun _ : Unit ↦ g.val.valᵀ)ᵀ * weylGramOver := weylGramOver_mul_schur (R := ℂ) _
    rw [h_gram] at h_adjoint
    simp [rep, hφ, ← mul_assoc, h_adjoint]
  · -- Schur's lemma for `φ.symm M`.
    obtain ⟨c, hc⟩ : φ.symm M ∈ Set.range (scalar (WeylIndex 𝔰.κ w)) :=
      mem_range_scalar_of_commute_schur fun g hg ↦ by
        simpa [rep] using! (hM (U.of isUnit_one (g ()) (by simp [hg]))).map φ.symm
    exact ⟨c, (φ.commutes c).symm.trans (φ.eq_symm_apply.mp hc)⟩
  · refine Continuous.subtype_mk ?_ h_unitary
    simp only [hφ]
    fun_prop
  · -- The coefficient at `B x`, with `x` the highest vector, is that of `x` for the Gram form: a
    -- product of principal minors of `k` in the decreasing order `p` of `u ()`, as is `dsCoeff` on
    -- this group.
    obtain ⟨p, hp⟩ := exists_equiv_decreasingPosition (hu ()).1
    set x : WeylIndex 𝔰.κ w → ℂ := highestVector w u with hx
    calc _ = star (B.val *ᵥ x) ⬝ᵥ φ (schur w fun _ : Unit ↦ k.val.val) *ᵥ B.val *ᵥ x :=
          dotProduct_comm _ _
      _ = x ⬝ᵥ weylGramOver *ᵥ (schur w fun _ : Unit ↦ k.val.val) *ᵥ x := by
          simp [hx, hφ, h_gram, star_mulVec, star_highestVector, dotProduct_mulVec, mul_assoc,
            star_eq_conjTranspose]
      _ = (u ()).dsCoeff k := by
          simpa [hx, weylRep, hp, highestVector, funext (hu.lowestKType_eq _),
            dsCoeff_of_mem_maxCompactU (hu.hasGap () 0) (k := ⟨k, _⟩) k.prop] using!
            weylRep_coeff_eq_prod_weightMinors (κ := w) (e := 0) (fun _ : Unit ↦ p) _

/-- If the parameter `D.paramW v` of the discrete series at the place `v` has entries of size at
most `3 a`, then Weyl's dimension polynomial at it is at most `b ^ (2 r ^ 2)`, where `a` and `b` are
the size parameters of D and `r` is the number of its row indices. -/
lemma weylDimensionPoly_paramW_le (v : D.Φ)
    (h_abs : ∀ i : D.RowIndex, |D.paramW v i| ≤ ↑(3 * D.a)) :
    weylDimensionPoly (D.paramW v) ≤ D.b ^ (2 * D.r ^ 2) := by
  -- Each of the at most `r ^ 2` halved differences is at most `3 a ≤ b ^ 2`, and the denominator is
  -- at least one.
  have hb : 1 ≤ D.b ^ 2 := one_le_pow₀ D.le_of_hasLogBound
  have h_factor (i j : D.RowIndex) : |(D.paramW v i - D.paramW v j : ℝ) / 2| ≤ D.b ^ 2 := by
    rify at h_abs
    grw [abs_div, abs_sub, h_abs, h_abs, abs_two, add_self_div_two]
    exact D.le_of_hasLogBound
  have h_denom : (1 : ℝ) ≤ ∏ i ∈ Finset.range (Fintype.card D.RowIndex), ↑i.factorial :=
    Finset.one_le_prod₀ fun i _ ↦ mod_cast i.factorial_pos
  calc weylDimensionPoly (D.paramW v)
      ≤ ∏ i, ∏ j with D.paramW v j < D.paramW v i, |(D.paramW v i - D.paramW v j : ℝ) / 2| := by
        grw [weylDimensionPoly, le_abs_self (∏ _, _), ← h_denom, div_one]
        simp only [abs_prod, le_refl]
    _ ≤ ∏ _ : D.RowIndex, (D.b ^ 2) ^ D.r := by
        gcongr with i
        grw [h_factor, prod_const, card_filter_le, card_univ, card_rowIndex]
    _ = D.b ^ (2 * D.r ^ 2) := by
        rw [prod_const, card_univ, card_rowIndex, ← pow_mul, ← pow_mul, ← sq]

/-- The quotient of the volumes of U(k) and U(r) is at most `(b ^ r) ^ r`, where `k` and `r` are the
rank of X₀ and the number of row indices of D, and `b` is its size parameter. -/
lemma volU_div_volU_le : volU D.k / volU D.r ≤ (D.b ^ D.r) ^ D.r := by
  -- The quotient is a product of `r - k` numbers `i! / (2 π ^ (i + 1)) ≤ b ^ r`.
  have h_factor (i : ℕ) (hi : i < D.r) : (sphereDensity (i + 1) 1)⁻¹ ≤ D.b ^ D.r := by
    calc (sphereDensity (i + 1) 1)⁻¹ = i.factorial / (2 * Real.pi ^ (i + 1)) := by
          simp [sphereDensity, div_eq_mul_inv]
      _ ≤ (D.r : ℝ) ^ D.r := by
          grw [← show 1 ≤ 2 * Real.pi ^ (i + 1) by bound [Real.two_le_pi], div_one,
            Nat.factorial_le hi.le, Nat.factorial_le_pow, Nat.cast_pow]
      _ ≤ D.b ^ D.r := pow_le_pow_left₀ D.r.cast_nonneg D.le_of_hasLogBound _
  calc volU D.k / volU D.r = ∏ i ∈ Ico D.k D.r, (sphereDensity (i + 1) 1)⁻¹ := by
        rw [volU.eq_1 D.r, ← prod_range_mul_prod_Ico _ D.k_le_r, ← volU, prod_inv_distrib,
          div_mul_cancel_left₀ (volU_pos _).ne']
    _ ≤ ∏ _ ∈ Ico D.k D.r, D.b ^ D.r := by
        gcongr with i hi
        exact h_factor i (mem_Ico.1 hi).2
    _ ≤ (D.b ^ D.r) ^ D.r := by
        grw [prod_const, Nat.card_Ico, tsub_le_self]
        exact one_le_pow₀ D.le_of_hasLogBound

/-- The constant `scaledVolumeRatio` of the local bounds for the shape of D is at most
`b ^ (2 r ^ 2)`, where `b` is the size parameter of D and `r` the number of its row indices. -/
lemma scaledVolumeRatio_le : D.shape.scaledVolumeRatio ≤ D.b ^ (2 * D.r ^ 2) := by
  have hb : 1 ≤ D.b := D.le_of_hasLogBound
  have h_pi : Real.pi ≤ D.b := D.le_of_hasLogBound
  have h_mul : (2 * D.shape.ϱ + 1) * D.k ≤ D.r ^ 2 := D.nat_le_of_hasLogBound
  grw [Shape.scaledVolumeRatio, show D.shape.k = D.k from D.card_X₀,
    show D.shape.r = D.r from D.card_rowIndex, D.volU_div_volU_le, h_pi, h_mul]
  exact le_of_eq (by ring)

/-- If every entry `D.paramW v i` has absolute value at most `3 * D.a`, then Weyl's dimension
polynomial at `D.paramW v`, times the constant `D.shape.scaledVolumeRatio` of the local bounds, is
at most `D.b ^ (4 r ^ 2)`, where `r = D.shape.r` is the rank of G₁. -/
lemma weylDimensionPoly_mul_scaledVolumeRatio_le (v : D.Φ)
    (h_abs : ∀ i : D.RowIndex, |D.paramW v i| ≤ ↑(3 * D.a)) :
    weylDimensionPoly (D.paramW v) * D.shape.scaledVolumeRatio ≤ D.b ^ (4 * D.shape.r ^ 2) := by
  have h_nonneg : 0 ≤ D.shape.scaledVolumeRatio :=
    mul_nonneg (div_pos (volU_pos _) (volU_pos _)).le (by positivity)
  grw [D.weylDimensionPoly_paramW_le v h_abs, D.scaledVolumeRatio_le,
    show D.shape.r = D.r from D.card_rowIndex, ← pow_add]
  exact le_of_eq (by ring)

/-- The entries of `D.paramW v`, twice the Harish-Chandra parameter at the place `v` of the discrete
series on G₁, have absolute value at most `3 a`, where `a = D.a` is a size parameter of D. -/
lemma abs_paramW_le (v : D.Φ) (i : D.RowIndex) : |D.paramW v i| ≤ ↑(3 * D.a) :=
  (D.abs_gridParam_le (z := false) v bot_le bot_le i).trans (mod_cast D.nat_le_of_hasLogBound)

/-- Let `u ()`, indexed by the basis `D.shape.κ` of X₀, list twice the Harish-Chandra parameter of
the weight on the compact group U(X₀) that has `D.columnCount v h` columns of height `h` for each
`h` below the rank. Then the highest weight `lowestKType` attached to `u ()` is `D.columnCount v 1`
at one index `i` and `0` at the others, and the entries of `u ()` have absolute value at most
`3 * D.a`. Here the natural number `D.a` is a size parameter of the data D, the product
`D.natX * D.natB`. -/
lemma exists_lowestKType_eq_ite (v : D.Φ) {u : Unit → D.shape.κ → ℤ}
    (hu : IsHCParam (fun _ : Unit ↦ D.columnCount v) 0 u) :
    ∃ i : D.shape.κ,
      (∀ j : D.shape.κ, (toHCParam 1 (u ())).lowestKType j =
        ↑(if j = i then D.columnCount v 1 else 0 : ℕ)) ∧
      ∀ j : D.shape.κ, |u () j| ≤ ↑(3 * D.a) := by
  have h_card : card D.shape.κ = D.k := D.card_X₀
  -- The index `i` is the one at which `u` is largest.
  obtain ⟨i, hi⟩ := hu.exists_decreasingPosition_eq () card_pos
  have hk : D.k ≤ D.a := D.nat_le_of_hasLogBound
  -- Of the heights above `p` and below `k`, only height 1 has columns; so the sum vanishes
  -- unless `p = 0`.
  have h_column (p : ℕ) :
      ∑ q ∈ Ioo p (card D.shape.κ), D.columnCount v q = if p = 0 then D.columnCount v 1 else 0 := by
    rw [sum_eq_ite 1] <;> grind [columnCount]
  refine ⟨i, fun j ↦ ?_, fun j ↦ ?_⟩
  · have h_position : decreasingPosition (u ()) j = 0 ↔ j = i := by
      grind [(hu ()).1, hu.eq_hcParameter () j]
    rw [hu.lowestKType_eq, diagramWeight_apply, rankAt, h_column]
    simp [h_position]
  · -- The entry at `j` is the Harish-Chandra value at the position of `j`.
    rw [hu.eq_hcParameter () j, hcParameter, diagramWeight_apply, h_column, Pi.zero_apply]
    grind [columnCount, decreasingPosition]

/-- The size inequalities `Floors.RealPlaceSizes`, under which cut Bessel functions have local
bounds, hold for `D.shape` with box radius `b ^ (6 n + 2)`, exponent `k - (3 n + 6)` and base
`b = D.b`. Here `D.shape` describes the hermitian space Y₀, the sum of some hyperbolic planes, a
space X₀ and a line; `n = D.shape.n` is the number of planes plus one and `k = D.shape.k` is the
rank of X₀. -/
lemma realPlaceSizes : Floors.RealPlaceSizes D.shape (D.b ^ (6 * D.shape.n + 2))
    (D.shape.k - (3 * D.shape.n + 6)) D.b := by
  have h_card : D.shape.k = D.k := D.card_X₀
  have h_room : 10 ^ 9 * D.shape.n ^ 3 + (3 * D.shape.n + 6) < D.shape.k :=
    h_card.ge.trans_lt' D.nat_lt_of_hasLogBound
  exact {
    rho_eq := rfl, k_eq := by omega, mul_cube_lt_s := by omega
    eight_mul_r_le_rho := D.le_of_hasLogBound.trans (le_self_pow₀ D.le_of_hasLogBound nofun)
    pow_seven_le_k := h_card.ge.trans' D.nat_le_of_hasLogBound
    ten_pow_le_varrho := D.nat_le_of_hasLogBound
    two_le_b := D.le_of_hasLogBound }

/-- An inequality of exponents of `b = D.b`, where `r` and `k` are the ranks of G₁ and U(X₀): the
loss `3 * (20 * (r + k) ^ 2)` in the lower bound for the period and the further `99 r ^ 2` allowed
for cutting the Bessel function add up to at most `400 r ^ 2`. -/
lemma exponent_add_le_mul_sq_r :
    3 * (20 * (D.shape.r + D.shape.k) ^ 2) + 99 * D.shape.r ^ 2 ≤ 400 * D.shape.r ^ 2 := by
  have hk : D.shape.k ≤ D.shape.r := D.card_X₀.trans_le (D.k_le_r.trans D.card_rowIndex.ge)
  nlinarith

/-- At an infinite place `v`, three times `D.liftWeight 0 v`, which is the weight of the character
of the lift of index `0` (the first one), plus the number `D.columnCount v 1` of columns of height 1
in the weight on X₀ is at most `b ^ 2`, where `b = D.b` is the size parameter of D. -/
lemma liftWeight_add_columnCount_le (v : D.Φ) :
    3 * (D.liftWeight 0 v : ℝ) + D.columnCount v 1 ≤ D.b ^ 2 := by
  have h_count : D.columnCount v 1 ≤ D.a := by grind [columnCount]
  grw [h_count]
  exact D.le_of_hasLogBound

/-- The ranks `r` of G₁ and `k` of U(X₀) and the bound `3 a` on the entries of the parameters
`D.paramW v` add up to at most `b ^ 3`, where `a` and `b` are the size parameters of D. -/
lemma rank_add_le_cube : D.shape.r + D.shape.k + (3 * D.a : ℕ) ≤ D.b ^ 3 := by
  have h_card : D.shape.k = D.k := D.card_X₀
  rw [h_card]
  exact D.le_of_hasLogBound

/-- For the ranks `r` of G₁ and `k` of U(X₀) and the size parameter `b` of D, the number `r ^ 7`,
which bounds from below the gaps of the Harish-Chandra parameters at the real places, is at least
`10 ^ 30` times the cube of `(r + k) ^ 2 log (b ^ 3)`. -/
lemma rank_sq_mul_log_le :
    10 ^ 30 * ((D.shape.r + D.shape.k) ^ 2 * (D.b ^ 3).log) ^ 3 ≤ (D.r ^ 7 : ℕ) := by
  have h_card : D.shape.k = D.k := D.card_X₀
  rw [h_card]
  exact D.le_of_hasLogBound

/-- Let `l` be a parameter of large gap, with coefficient `c_l` on G₁ and formal degree `deg`. If a
Bessel function `F` is fixed by convolution with `deg * c_l`, then each coordinate of `F` is fixed
by right convolution with the kernel `l.dsKernel`, carried over from `USign ε` by the frame. -/
lemma _root_.New.IsBesselFunction.integral_dsKernel_mul_eq_of_convolve_eq {𝔰 : Shape}
    {ε : 𝔰.BesselIndex → ℤˣ} [SignFrame 𝔰.J₁ ε] [IsHermitianInvolution 𝔰.J₁] {I : Type}
    [Fintype I] [DecidableEq I] {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ}
    {F : 𝔰.G₁ → EuclideanSpace ℂ I} (hF : IsBesselFunction rep F) {l : HCParam ε} {A : ℕ}
    (h_gap : l.HasLargeGap A)
    (hF_fix : convolve F (fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g) = F)
    (y : 𝔰.G₁) (j : I) :
    ∫ g : USign ε, l.dsKernel g * F (y * frameEquiv.symm g) j = F y j := by
  have h_ker : IsIdempotentKernel fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g :=
    isIdempotentKernel_dsCoeffInFrame h_gap
  have h_inv (g : 𝔰.G₁) :
      l.formalDegree * l.dsCoeffInFrame g⁻¹ = l.dsKernel (frameEquiv g) :=
    (h_ker.apply_inv g).trans (by simp [HCParam.dsKernel, HCParam.dsCoeffInFrame])
  calc ∫ g : USign ε, l.dsKernel g * F (y * frameEquiv.symm g) j
      = ∫ g : 𝔰.G₁, ((l.formalDegree * l.dsCoeffInFrame g⁻¹) • F (y * g)) j := by
        simp [← integral_comp_frameEquiv (J := 𝔰.J₁), h_inv]
    _ = convolve F (fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g) y j :=
        (eval_integral_piLp (hF.integrable_smul h_ker.integrable.comp_inv y).eval_piLp j).symm
    _ = F y j := by rw [hF_fix]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- **Bessel functions at a real place**: for each infinite place `v : D.Φ` of the field of `D`
there is a Bessel system `B : BesselSystem D.shape D.b D.f`. Such a system is a full Bessel function
on the group G₁, the unitary group of the hermitian form of the shape `D.shape`, together with a cut
version of bounded support, and the two satisfy the bounds listed in `BesselSystem`. It is built for
the shape `D.shape` of the hermitian space Y₀ of `D`, with size parameter `D.b`, and the number
`D.f` of infinite places sets the rate of decay. Its type (`IsDiscreteSeriesBessel`) is
`(D.paramW v, D.columnCount v)`: the doubled parameter of the discrete series whose Bessel function
is the full function, and the numbers of columns of each height in the weight of the representation
on the values. -/
lemma exists_besselSystem (v : D.Φ) :
    ∃ B : BesselSystem D.shape D.b D.f, IsDiscreteSeriesBessel B (D.paramW v)
      (D.columnCount v) := by
  -- `F` is the normalised Bessel average `besselAverage` at a stationary point `x`; it is fixed by
  -- the kernel of the parameter `l`, and the second function of the system is its cut. The L² norm
  -- of `F` and the volume of balls give the local bounds of the cut.
  have : IsHermitianInvolution D.shape.J₁ := isHermitianInvolution_J₁
  -- The parameter `l` on `G₁`, in the frame of signs `ε`: size, gap and formal degree.
  let ε : D.shape.BesselIndex → ℤˣ := (D.signsY 0 ·)
  let frame : SignFrame D.shape.J₁ ε := D.unitarySignFrameY.toSignFrame
  let l : HCParam ε := toHCParam ε (D.paramW v)
  have h_abs : ∀ i : D.RowIndex, |D.paramW v i| ≤ ↑(3 * D.a) := D.abs_paramW_le v
  have h_gap : l.HasLargeGap (D.r ^ 7) := (D.hasGap_signsY_paramW v).mono D.nat_le_of_hasLogBound
  have h_deg_pos : 0 < l.formalDegree := formalDegree_pos h_gap
  have h_deg : l.formalDegree = weylDimensionPoly (D.paramW v) :=
    (Orbital.harish_chandra_degree_and_orbital (h_gap.mono D.nat_le_of_hasLogBound)).1
  -- The representation on the values, with a unit vector `e` at which its coefficient is `dsCoeff`.
  obtain ⟨u, hu⟩ : ∃ u : Unit → D.shape.κ → ℤ, IsHCParam (fun _ : Unit ↦ D.columnCount v) 0 u :=
    ⟨_, isHCParam_hcParameter D.shape.κ _ 0⟩
  obtain ⟨rep, ⟨C, hC⟩, h_irred, h_cont, e, h_coef⟩ := exists_unitary_schur_rep hu
  have he : ‖e‖ = 1 := by
    have h_sq : ‖e‖ ^ 2 = 1 := by simpa using congrArg norm (h_coef 1)
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg e) two_ne_zero).1 h_sq
  -- A point `x` of length at most `b ^ (5 n)` where the volume of the unit ball is bounded by the
  -- L² norm of the average.
  obtain ⟨x, hx, h_volume⟩ : ∃ x : D.shape.G₁, besselLength x ≤ D.b ^ (5 * D.shape.n) ∧
      besselBallVolume (ε := ε) x ≤
        .ofReal (D.b ^ (3 * (20 * (D.shape.r + D.shape.k) ^ 2))) * (.ofReal l.formalDegree *
          ∫⁻ y : D.shape.G₁, ‖besselAverage l rep x e y‖ₑ ^ 2 ∂besselQuotMeasure) := by
    obtain ⟨i, h_weight, h_abs_u⟩ := D.exists_lowestKType_eq_ite v hu
    obtain ⟨numbering, h_steep⟩ := D.exists_isSteep false
    have hu_gap : (toHCParam 1 (u ())).HasLargeGap (D.r ^ 7) := hu.hasGap () _
    -- At the stationary point the period is large.
    obtain ⟨x, hx, h_period⟩ := (h_steep v).exists_stationary_point (.swap (.inr ()) i)
      (ha := by simpa using h_weight) (hB := D.le_of_hasLogBound)
      (hb := D.liftWeight_add_columnCount_le v) (hb_rank := D.le_of_hasLogBound) (hl := h_gap)
      (hu := hu_gap) (hL := h_abs) (hK := h_abs_u) (hβ := D.le_of_hasLogBound)
      (h_rank := D.rank_add_le_cube) (h_excess := D.rank_sq_mul_log_le)
    refine ⟨x, hx, ?_⟩
    rw [pow_mul]
    exact besselBallVolume_le_of_period x h_cont h_gap (by positivity) h_coef h_period
  -- The normalised average `F` is fixed by the kernel and forms a cut pair with its cut.
  let I : Type := WeylIndex D.shape.κ fun _ : Unit ↦ D.columnCount v
  obtain ⟨c, F, hF_eq, hF_fix, h_tail⟩ : ∃ (c : ℝ) (F : C(D.shape.G₁, EuclideanSpace ℂ I)),
      (∀ y : D.shape.G₁, F y = c • besselAverage l rep x e y) ∧
      convolve F (fun g : D.shape.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g) = F ∧
      IsCutPair D.b D.f rep (FullOrCut.select F (besselCut D.b F)) :=
    exists_isCutPair_besselAverage h_gap h_abs D.f h_cont he h_volume hx
      (hb_large := D.le_of_hasLogBound) (hr := D.nat_le_of_hasLogBound)
      (hm := D.exponent_add_le_mul_sq_r) (hL_le := D.le_of_hasLogBound)
      (hf := D.nat_le_of_hasLogBound)
  have hF : IsBesselFunction rep F := h_tail.isBesselFunction .full
  have hF_norm : ∫⁻ y : D.shape.G₁, ‖F y‖ₑ ^ 2 ∂besselQuotMeasure = card I :=
    h_tail.lintegral_sq_full_eq
  have h_schur (P : ℝ) (hP : D.b ^ 5 ≤ P) :
      HasSchurBound F rep P (.ofReal l.formalDegree⁻¹ * card I) := by
    rw [← hF_norm]
    exact hF.hasSchurBound_of_convolve_eq h_gap h_abs h_tail.integrable P hF_fix
      (D.le_of_hasLogBound.trans hP)
  have h_const : l.formalDegree * D.shape.scaledVolumeRatio ≤ D.b ^ (4 * D.shape.r ^ 2) := by
    grw [h_deg, D.weylDimensionPoly_mul_scaledVolumeRatio_le v h_abs]
  -- The local bounds use the norm of the matrix coefficient of `F` and the volume of balls.
  obtain ⟨J, h_band⟩ : ∃ J : ℕ → (ℕ → ℂˣ) → (ℕ → ℂˣ) → ℂ,
      HasLocalBounds D.b (besselCut D.b F) l.formalDegree J := by
    have h_coeff : ∫⁻ g : D.shape.G₁, ‖Floors.quotientPairing F F g‖ₑ ^ 2 =
        .ofReal l.formalDegree⁻¹ * card I ^ 2 := by
      rw [← hF_norm]
      exact hF.lintegral_enorm_sq_integral_inner_translate h_gap h_tail.integrable hF_fix
    exact Floors.exists_hasLocalBounds_of_isCutBessel ⟨h_tail, D.realPlaceSizes, h_irred⟩ h_deg_pos
      h_coeff.le h_const (fun _ ↦ formalDegree_mul_volume_ball_le h_gap h_abs D.le_of_hasLogBound
        D.le_of_hasLogBound) D.nat_le_of_hasLogBound
  refine ⟨{
      Index := I, besselFn := FullOrCut.select F (besselCut D.b F),
      deg := l.formalDegree, deg_pos := h_deg_pos, rep := rep, isCutPair := h_tail,
      irreducible := h_irred, hasSchurBound := h_schur, eight_mul_rank_le := D.le_of_hasLogBound,
      bandLimit := J, hasLocalBounds := h_band }, {
      deg_eq := h_deg, exists_conj_rep_eq_schur := ⟨C.val, C⁻¹.val, C.mul_inv, C.inv_mul, hC⟩,
      exists_eq_besselAverage :=
        ⟨c, x, e, fun y ↦ ⟨integrable_besselIntegrand x h_cont he h_gap y, hF_eq y⟩⟩,
      integral_dsKernel_mul := hF.integral_dsKernel_mul_eq_of_convolve_eq h_gap hF_fix }⟩

end BesselSystemExists

section FillingData

open Real Parameters Nat

variable {P : Parameters} (D : Data P)

/-- The prime `D.levelPrime i` divides an integral finite adele `r` (an element of `Ô D.E`) iff the
component of `r` has valuation less than 1 at each chosen place `w` above that prime (the type
`D.ChosenPlace i`) and at the conjugate place `star w`. -/
lemma natCast_levelPrime_dvd_iff (i : Fin 2) (r : Ô D.E) :
    ↑(D.levelPrime i) ∣ r ↔
      ∀ w : D.ChosenPlace i, Valued.v (r.1 w) < 1 ∧ Valued.v (r.1 (star w.1)) < 1 := by
  -- As the prime is unramified, it divides `r` iff `r` vanishes modulo every place above it.
  have h_red : ↑(D.levelPrime i) ∣ r ↔ ∀ w : FinPlace D.E,
    ↑(D.levelPrime i) ∈ w.1 → Valued.v (r.1 w) < 1 := by
    simpa using dvd_iff_reduceAt_eq_zero
      (intValuation_natCast_eq_exp_neg_one ·
        (not_dvd_q₁_mul_d_of_modEq_one (D.levelPrime_modEq_one i))) r
  refine h_red.trans ⟨fun h_vanish ⟨w, _, hw⟩ ↦ ⟨h_vanish w hw, h_vanish (star w) (by simpa)⟩,
    fun h_pairs w hw ↦ ?_⟩
  -- A place above the prime is chosen or is the conjugate of a chosen place.
  by_cases h_chosen : D.IsChosen w
  · exact (h_pairs ⟨w, h_chosen, hw⟩).1
  · have h_conj := (h_pairs ⟨star w, (isChosen_star_iff hw).2 h_chosen, by simpa⟩).2
    rwa [star_star] at h_conj

instance : D.HasLogLower (ofNat(2) ^ D.ϱ) (10 * D.logB) where
  out := by
    -- Take logarithms and replace log 2 by a rational lower bound, which `D.le_of_hasLogBound` can
    -- compare.
    suffices h : 10 * D.logB ≤ D.ϱ * Real.log 2 by simpa [← le_log_iff_exp_le] using h
    grw [← log_two_gt_d9]
    norm_num
    exact D.le_of_hasLogBound

/-- The filling data `New.Filling` attached to the admissible data D. They record the prime N, the
idele of π (in the field `piN`), the primes p₀, p₁ with chosen places, `deltaE`, and Bessel systems
chosen from `New.Data.exists_besselSystem`. The type of the chosen systems is stated in
`New.Data.isDiscreteSeriesBessel_filling_besselSystem`. -/
noncomputable def filling : Filling D.E D.shape where
  N := D.N
  levelPrime := D.levelPrime
  piN := D.piNIdele
  deltaE := P.deltaE D.towerExp
  b := D.b
  chosenPlaces i := fun w ↦ D.piM ∈ w.1 ∧ ↑(D.levelPrime i) ∈ w.1
  fintypeChosen i := inferInstanceAs (Fintype (D.ChosenPlace i))
  sourceLevel := D.levelX 0
  classAut_eq_bot := D.classAut_levelX_zero_eq_bot
  besselSystem v := (D.exists_besselSystem v).choose
  piN_mul_star := mod_cast D.isSplitSquarefree_piNIdele.algebraMap_eq_mul_star.symm
  N_prime := D.N_prime
  N_split w := by
    by_cases hw : w ∈ D.piNPlaces
    · refine .inr ⟨D.isSplitLevel_piNPlaces.q_eq w hw, ?_⟩
      rw [D.isSplitSquarefree_piNIdele.v_apply,
        ite_eq_right (D.isSplitSquarefree_piNIdele.star_notMem w hw)]
    · exact .inl (by rw [D.isSplitSquarefree_piNIdele.v_apply, ite_eq_right hw])
  piN_mem := coe_mem_Ô D.piN
  levelPrime_prime_and_ne i := ⟨D.levelPrime_prime i, D.nat_lt_of_hasLogBound.ne⟩
  le_levelPrime i := (D.levelPrime_mem i).1
  levelPrime_le i := (D.levelPrime_mem i).2
  chosenPlaces_q i w hw := D.q_eq_levelPrime hw.2
  chosenPlaces_injective := D.isConjApart_chosenPlace.1
  star_notMem_chosenPlaces hw hw' := IsChosen.not_star hw.1 hw'.1
  M_dvd_iff r := by
    -- The primes `D.levelPrime 0` and `D.levelPrime 1` are distinct, so their product divides `r`
    -- iff both do.
    have h_prod : ↑(D.levelPrime 0 * D.levelPrime 1) ∣ r ↔ ∀ i : Fin 2, ↑(D.levelPrime i) ∣ r := by
      have h_cop : (D.levelPrime 0).Coprime (D.levelPrime 1) := by grind [coprime_primes, Data]
      simpa using ⟨fun h ↦ ⟨dvd_of_mul_right_dvd h, dvd_of_mul_left_dvd h⟩,
        fun ⟨h₀, h₁⟩ ↦ h_cop.cast.mul_dvd h₀ h₁⟩
    rw [h_prod, Sigma.forall]
    exact forall_congr' fun i ↦ (D.natCast_levelPrime_dvd_iff i r).trans
      (forall_congr' fun w ↦ by simp)
  card_chosenPlaces := D.card_chosenPlace
  star_deltaE := P.star_deltaE
  span_deltaE := P.differentIdeal_eq_span_deltaE
  -- Each size inequality is compared on the logarithmic scale; `D.card_X₀` identifies the rank.
  ten_pow_five_le_varrho := D.nat_le_of_hasLogBound
  half_pow_le_inv_pow_six := by
                 rify [inv_pow]
                 exact D.le_of_hasLogBound
  mul_finrank_le_pow := by
             rify [finrank_eq_two_mul_card_infinitePlace, pow_mul']
             exact D.le_of_hasLogBound
  pow_le_k := D.nat_le_of_hasLogBound.trans D.card_X₀.ge
  thousand_mul_le_k := D.nat_le_of_hasLogBound.trans D.card_X₀.ge
  k_le_f := D.card_X₀.trans_le D.nat_le_of_hasLogBound
  mul_rootDiscr_pow_le := by
                 rify [Shape.k, card_X₀]
                 exact D.le_of_hasLogBound
  numInfPlaces_le_div := D.le_of_hasLogBound
  k_le_b := (Nat.cast_le.2 D.card_X₀.le).trans D.le_of_hasLogBound
  rootDiscr_le_b := D.le_of_hasLogBound
  succ_le_b := D.le_of_hasLogBound
  thousand_le_b := D.le_of_hasLogBound
  one_le_b := D.le_of_hasLogBound
  M_le_b_pow := D.le_of_hasLogBound
  le_M := D.le_of_hasLogBound
  five_le_N := D.le_of_hasLogBound
  pow_chain := ⟨D.nat_le_of_hasLogBound, D.nat_le_of_hasLogBound,
    D.nat_le_of_hasLogBound.trans D.card_X₀.ge⟩

/-- The Bessel system of `D.filling` at the infinite place `v` has type
`(D.paramW v, D.columnCount v)`: its full function is the Bessel function of the discrete series of
parameter `D.paramW v`, with values in the representation of U(X₀) of weight `D.columnCount v`. -/
lemma isDiscreteSeriesBessel_filling_besselSystem (v : D.Φ) :
    Filling.IsDiscreteSeriesBessel (D.filling.besselSystem v) (D.paramW v) (D.columnCount v) :=
  (D.exists_besselSystem v).choose_spec

/-- The level of index `0`, `D.levelX 0`, is a level on the first hermitian space X₀ of the sequence
X_j of D. It is the preimage, under the embedding `inclHFin` of the finite adelic points of U(X₀) in
those of U(Y₀), of `New.Filling.principalLevel`, the level K(M) of the elements that satisfy the
congruence modulo π and reduce to 1 at the chosen places. -/
lemma levelX_zero_eq_comap :
    D.levelX 0 = D.filling.principalLevel.comap D.filling.inclHFin := by
  -- Both sides say that `k` satisfies the congruence modulo `piN` and reduces to `1` at the chosen
  -- places; the left side also asks for `k ∈ stdLevel` (integrality), which the congruence
  -- contains.
  ext k
  -- The chosen places stay subtypes (`-Subtype.forall`), as the lemma on reductions is stated.
  simp [levelX, Filling.principalLevel, levelOf, Subgroup.mem_comap, funext_iff, Sigma.forall,
    D.filling.reduction_inclHFin_eq_one_iff, D.filling.inclHFin_mem_latticeStabilizer_iff,
      -Subtype.forall]
  exact ⟨fun ⟨⟨_, h_red⟩, h_cong⟩ ↦ ⟨h_cong, h_red⟩,
    fun ⟨h_cong, h_red⟩ ↦ ⟨⟨h_cong.1, h_red⟩, h_cong⟩⟩

end FillingData

end New.Data
