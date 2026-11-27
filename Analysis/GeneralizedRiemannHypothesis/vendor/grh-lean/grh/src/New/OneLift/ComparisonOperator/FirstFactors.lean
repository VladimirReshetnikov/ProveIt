import New.Determinant.Twist.FitTwists
import New.OneLift.ComparisonOperator.LineCoordinates
import New.UpperBound.Kernels.DefiniteKernelSize
import New.UpperBound.Size.Estimates

/-!
# The first factors: P_V along W_j and W^add, integrality and size

Fix admissible data `D`, a tame character `ϑ` and an index `1 ≤ j ≤ m`. Write `E^n` for
the standard definite space of rank `n`, V″ for the one on `New.Data.FirstFactorIndex` and
W^add = E^{3m−j} ⊕ W♭ ⊕ E^{3m} for the one on `New.Data.AddedIndex`. Throughout, k = `D.k`,
m = `D.m`, M = `D.M`, and W_j is the space on `D.RowIndex` with r₊ = `D.posRank j` = k + j − 1
plus signs. This file writes P_V as a sum of products of a polynomial in X and a coordinate of
ζ(z), where X are the variables in the positive basis vectors of W_j and z those in W^add. Each
value of Υ is a double class sum of products of three theta kernels of definite spaces, and this
file bounds these kernels. By `New.Data.exists_isIntegralAndSmall_leftSideSeries`, for one constant
`c″ ≠ 0` the first factors φ″, the complex conjugates of c″Υ, are integral away from the norm of Q
and, if Q is empty, all their images under automorphisms of ℂ are small
(`New.Data.IsIntegralAndSmall`).

## Main definitions and results

* `New.Data.renameRowsCols_stackedDetProd_eq_sum`: P_V as a sum of products of a polynomial in X and
  a coordinate of ζ(z).
* `New.Data.exists_isIntegralAndSmall_leftSideSeries`: for 1 ≤ j ≤ m there is one c ≠ 0, independent
  of i, ϑ and h, such that every first factor y = conj (c · Υ) is integral and small in the sense of
  `New.Data.IsIntegralAndSmall`.

Notions from other files:
* `New.toPoly`, `New.weylNormSq`: the polynomial of a coordinate vector of weight κ, and the squared
  norm of the vector for the Gram matrix of κ. Here `κ τ h` counts the columns of height `h` at `τ`.
* `New.Data.FirstFactorIndex`: the indices of W_j, (E^j)⁻, E^{3m−j} and W♭ = E^{6m+1}.
* `New.Data.TameChar`, `New.Data.twistModulus`: a character `ϑ` of U(1)(𝔸) of weight 0 with tame
  part on a finite set Q = `ϑ.Q` of places, and the moduli ϖ^c Q.
* `New.Data.stackedDetProdCoords`: the coordinates of the polynomial map ζ.
* `New.Data.leftSideSeries`: the series Υ, built from theta kernels of definite spaces.

## Relation to the literature

The first factors enter the comparison of twisted theta forms on U(W_j) with twist-free ones,
`New.Data.exists_mul_thirdExchangeLeftSide_eq_choiceFn` in
`New.OneLift.ComparisonOperator.ThreeExchanges`: for every twist, an explicit theta form times a
number is a twist-free function, and the squared modulus of the number is a constant independent of
the twist divided by a product of squared Hecke L-values and powers of norms of places. This file
proves that the first factors are integral off the conductor and small when untwisted. The rank one
case (the lift is a scalar of square modulus an L-value), twisting on a square block and integral
theta data are known in the literature. Related work: T. Yang, Theta liftings and Hecke L-functions,
1997; Böcherer–Schmidt, p-adic measures attached to Siegel modular forms, 2000; Harris–Li–Skinner,
The Rallis inner product formula and p-adic L-functions, 2005.
-/

noncomputable section

/-!
## The product of determinants as a sum of products, along W_j and W^add
-/

section LineLeftSide

open Matrix MvPolynomial New Rows Finset

/-- The determinant product `New.Rows.stackedDetProd` of the matrices `New.Data.constantRows` for
the short basis `D.shortRows i` at the class chosen by `i` has its columns renamed. `f` renames the
positive indices of W_j, the space of the `j`-th lift with indices `D.RowIndex`. `g` renames the
indices `AddedIndex j` of W^add. The result equals the sum over `l` of the products of two factors:
the letter polynomial (`New.letterPoly`) of the `l`-th unit vector in the letters of sign `1`,
renamed by `f`, and the `l`-th coordinate `New.Data.stackedDetProdCoords`, renamed by `g`. -/
lemma New.Data.renameRowsCols_stackedDetProd_eq_sum {P : Parameters} {D : Data P}
    (j : D.LiftIndex) (i : D.RowChoice) {n : Type*} (f : D.RowIndex → n) (g : AddedIndex j → n) :
    renameRowsCols id (f ∘ D.rowIndexOfNumber ∘ Fin.val ⊕ᵥ g)
        (stackedDetProd (posEquiv j) (constantRows j i (D.shortRows i))) =
      ∑ l : WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus,
        renameRowsCols id f (letterPoly (D.signsW j) (untwistedDescentPair j).numbering 1
            (untwistedDescentPair j).colsPlus (Pi.single l 1)) *
          renameRowsCols id g (stackedDetProdCoords j i (D.shortRows i) l) := by
  -- The renaming factors through `inFirstCols`: the first columns go to the letters of sign `1` on
  -- `D.RowIndex`, placed by `f`, and the coefficients to the variables on `AddedIndex j`, placed by
  -- `g`.
  have rename_eq : renameRowsCols (id : FirstFactorIndex j → FirstFactorIndex j)
        (f ∘ D.rowIndexOfNumber ∘ Fin.val ⊕ᵥ g) =
      (aevalTower (renameRowsCols id g) fun x : ((_ : D.Φ) × FirstFactorIndex j) × ℕ ↦
          renameRowsCols id f (fockLetters (D.signsW j) (untwistedDescentPair j).numbering 1
            (.X x))).comp
        (inFirstCols (Φ := D.Φ) (p := D.posRank j)) := by
    ext1 ⟨τ, a, s | s⟩
    · -- exactly one index has sign `1` and number `s`, namely `D.rowIndexOfNumber s`
      simp [inFirstCols, fockLetters, descentPair]
      rw [sum_eq_single] <;> grind [rowIndexOfNumber, D.basisNumber.eq_symm_apply, signsW]
    · simp [inFirstCols]
  -- `toPoly_stackedDetProdCoords` expands `inFirstCols (stackedDetProd …)` in the basis
  -- `nablaBasis` with coordinates `stackedDetProdCoords`; both sides become the same double sum, up
  -- to the order of summation.
  rw [rename_eq]
  simp [← toPoly_stackedDetProdCoords, toPoly, letterPoly, dotProduct, mulVec, nablaBasis,
    tableauPoly, minor, smul_eq_C_mul, AlgHom.map_det, Matrix.map, Fintype.linearCombination_apply,
    sum_mul, mul_right_comm _ (rename _ _)]
  exact sum_comm

end LineLeftSide

/-!
## Integrality and size of the first factors

Each value of Υ is a double class sum of products of three theta kernels of definite pairs, to which
`New.Rows.exists_ne_zero_isModKernelScale` applies; the third is evaluated on the polynomial
coordinates `New.Data.stackedDetProdCoords`, whose degree and denominator come from
`New.Data.exists_isHomogeneousOverEntries_smul_stackedDetProdCoords`.

`New.weylGauge κ e h y ≤ 1` says that `y` is `p`-integral for the lattice at `h`, read through the
embedding `ιₚ : ℂ → ℂ_[p]` given by the instance `[PadicPlace p]`.
-/

namespace New.Data

open Real Matrix Finset Rows MvPolynomial Ideal ComplexConjugate Sum Fintype NeZero RingHom

variable {P : Parameters} {D : Data P} {ϑ : D.TameChar}

/-- With `M = D.M`, the integer `ϑ.normQ * M ^ c` lies in the ideal of the modulus
`D.twistModulus ϑ c`: the `c`-th power of the product of the chosen places (the places
`D.chosenPlace` of the data) times the product of the places in `ϑ.Q`. -/
lemma normQ_mul_M_pow_mem_modulus {c : ℕ} :
    ↑(ϑ.normQ * D.M ^ c) ∈ (D.twistModulus ϑ c).ideal := by
  -- `D.M` lies in the product `(D.piM)` of the chosen places, and each norm `w.q` in `w`.
  have hM_mem : ↑D.M ∈ ∏ i, (D.chosenPlace i).1 := by
    rw [← span_piM D, mem_span_singleton]
    exact Dvd.intro _ D.piM_mul_star
  rw [TameChar.normQ, ← ϑ.Q.prod_coe_sort FinPlace.q, Nat.cast_mul, Nat.cast_pow, Nat.cast_prod]
  exact mul_mem_mul_rev (pow_mem_pow hM_mem c) (prod_mem_prod fun w _ ↦ absNorm_mem w.1.1)

/-- Replacing the matrix Y by Y·Bᵀ multiplies the matrices `constantRows` on the right by the
transpose of the block diagonal matrix (1, 1, τB, τA) at each τ, whatever A is. -/
lemma constantRows_mul_transpose_eq_mul_fromBlocks (j : D.LiftIndex) (i : D.RowChoice)
    (Y B : Matrix D.FlatIndex D.FlatIndex D.E) (A : Matrix D.CarrierIndex D.CarrierIndex D.E) :
    constantRows j i (Y * Bᵀ) = fun (τ : D.Φ) (k : DetIndex j τ) ↦
      constantRows j i Y τ k *
        (fromBlocks 1 0 0 ((fromBlocks 1 0 0 (fromBlocks B 0 0 A)).map (Φ τ)))ᵀ := by
  ext τ k x z
  -- Write the entry of the product on the right as a sum.
  refine .trans ?_ Matrix.mul_apply.symm
  obtain k | k := k
  · -- A row that is a standard basis vector, in a block where the matrix is the identity.
    obtain z | z | z | z := z
    all_goals
      simp [constantRows, inclMatrix, one_apply]
      split <;> simp [one_apply, eq_comm]
  · -- A row of τ(Y), supported on the block of B.
    obtain z | z | z | z := z <;> simp [constantRows, mul_apply]

/-- Let `q` be the bound on the number of determinants, `n ≤ (10 m + 1) q` a degree with `n ≤ D.M`
and `0 < H ≤ (n ^ n) ^ 3` a denominator. Then the constant `chosenGroupOrder ^ 2`, the two class
numbers, three kernel bounds `exp x₁`, the order of GL_{3m} over the residue ring and the bound on
`H` times the coordinates give at most exp(f m b log² b) after squaring. Here f = `D.f` is the
number of infinite places, b = `D.b` and `D.natB` the weight at the b-places, log b = `D.logB`,
`D.offWeight` the weight at the other places, `D.gap` = 2 r⁸ the gap, x₁ = `D.x₁` the second cut-off
and `D.chosenGroupOrder` a common multiple of the orders of the stabilisers. -/
lemma firstFactorSize_sq_le_exp {q n : ℕ} {H : ℤ}
    (hq : q = Fintype.card D.Φ * (D.natB + D.offWeight + D.gap + D.m * D.gap))
    (hn : n ≤ (10 * D.m + 1) * q) (hn_le_M : n ≤ D.M) (H_pos : 0 < H)
    (H_le : H ≤ (n ^ n) ^ 3) (φ : ℂ ≃+* ℂ) :
    ‖φ (D.chosenGroupOrder ^ 2)‖ ^ 2 *
        (Nat.card (StdClasses (stdLevel D.E D.CarrierIndex)) *
          (Nat.card (StdClasses (stdLevel D.E (Fin D.m))) *
            (rexp D.x₁ * rexp D.x₁ *
              (rexp D.x₁ * Fintype.card (GL D.CarrierIndex (D.untwistedModulus 2).ResidueRing) *
                √((H : ℝ) ^ 2 * (D.M ^ 9) ^ ((12 * D.m + 1) * q)))))) ^ 2 ≤
      rexp (D.f * D.m * D.b * D.logB ^ 2) := by
  -- With M = `D.M` and R the residue ring of `D.untwistedModulus 2`: both class numbers are at
  -- most exp(x³⁰), H ≤ n³ⁿ ≤ M³ⁿ, |GL(R)| ≤ |R|^{(3m)²}, and |R| ≤ (M²)^{2e} with
  -- e = `Core.numInfPlaces D.E`. The logarithm of the product is then the left side of `h_scale`,
  -- and with n ≤ (10 m + 1) q the scale inequalities of the data put it below f m b log² b.
  have h_scale :
      4 * log D.chosenGroupOrder +
        2 * (D.x ^ 30 + (D.x ^ 30 + (D.x₁ + D.x₁ +
          (D.x₁ + 2 * (2 * Core.numInfPlaces D.E * (2 * D.m + D.m) ^ 2) * log D.M +
            (n * 3 * 2 * log D.M / 2 + 9 * ((12 * D.m + 1) * q) * log D.M / 2))))) ≤
      D.f * D.m * D.b * D.logB ^ 2 := by
    grw [hn, hq]
    exact D.le_of_hasLogBound
  have h_carrier : card D.CarrierIndex ≤ D.n D.m := by simpa using D.nat_le_of_hasLogBound
  have h_fin : card (Fin D.m) ≤ D.n D.m := by simpa using D.nat_le_of_hasLogBound
  grw [D.card_stdClasses_le_exp principalLevel_le_stdLevel h_carrier,
    D.card_stdClasses_le_exp principalLevel_le_stdLevel h_fin]
  grw [H_le, hn_le_M, card_eq_nat_card, card_GL_le,
    Modulus.card_residueRing_le (levelModulus_ideal_le normQ_mul_M_pow_mem_modulus),
    ← le_exp_of_log_le]
  -- The goals left are the inequality of logarithms, which is `h_scale`, and positivity conditions.
  all_goals simp [log_mul, ne, log_sqrt, pos, sqrt_eq_zero', ← pow_mul,
    toAutChar_one_and_toTwist_one_and_Q_one]
  exact h_scale

/-- Equivariance under rational points. Let Γ and γ' be rational unitary points of the definite
spaces W^add and V″, and let the constant rows built from Y' be those built from Y multiplied by
diag(1, Γ)ᵀ at each place. Then γ'⁻¹, acting on vectors of weight μ⁺, carries the complex conjugate
of the vector l ↦ c 𝖪[H·ζ_l](Γ g, γ' h) for Y' to that of l ↦ c 𝖪[H·ζ_l](g, h) for Y. Here 𝖪 is the
theta kernel `modKernelBilin` of (W^add, V″) for the datum Ψ modulo 𝔪, with both characters
`firstFactorChar ϑ j`, and ζ = `stackedDetProdCoords`. -/
lemma modKernelBilin_stackedDetProdCoords_equivariant (j : D.LiftIndex) (i : D.RowChoice)
    {Y Y' : Matrix D.FlatIndex D.FlatIndex D.E} {𝔪 : Modulus D.E}
    (Ψ : Matrix (FirstFactorIndex j) (AddedIndex j) 𝔪.ResidueRing → ℂ)
    (Γ : U (stdSpace D.E (AddedIndex j)).J) (γ' : U (stdSpace D.E (FirstFactorIndex j)).J)
    (g : Gf D.E (AddedIndex j)) (h : Gf D.E (FirstFactorIndex j)) (c : ℂ) (H : ℤ)
    (h_rows : constantRows j i Y' = fun (τ : D.Φ) (k : DetIndex j τ) ↦
      constantRows j i Y τ k *
        (fromBlocks 1 0 0 ((Γ : Matrix (AddedIndex j) (AddedIndex j) D.E).map (Φ τ)))ᵀ) :
    (stdSpace D.E (FirstFactorIndex j)).weightRep (untwistedDescentPair j).colsPlus 0 γ'⁻¹
        (star (c • modKernelBilin (stdSpace D.E (AddedIndex j)) (stdSpace D.E (FirstFactorIndex j))
          (firstFactorChar ϑ j) (firstFactorChar ϑ j) 𝔪
            (1, (stdSpace D.E (AddedIndex j)).embFin Γ * g)
          (1, (stdSpace D.E (FirstFactorIndex j)).embFin γ' * h) Ψ ∘
            (H • stackedDetProdCoords j i Y'))) =
      star (c • modKernelBilin (stdSpace D.E (AddedIndex j)) (stdSpace D.E (FirstFactorIndex j))
        (firstFactorChar ϑ j) (firstFactorChar ϑ j) 𝔪 (1, g) (1, h) Ψ ∘
          (H • stackedDetProdCoords j i Y)) := by
  -- The substitution by `γ'⁻¹` and `Γ` carries the coordinates for `Y'`, mixed by the Schur matrix
  -- of `γ'⁻¹`, to those for `Y` up to determinants, and these cancel against the change of the
  -- characters.
  have h_char : (firstFactorChar ϑ j).HasWeight
    (fun τ : D.Φ ↦ firstFactorCharExp j + -D.liftWeight j τ)
      (D.liftTamePart ϑ j) := inferInstance
  -- `A`, `B` and `B'` are the images of `γ'⁻¹`, `Γ` and diag(1, Γ) at the infinite places.
  let A (τ : D.Φ) : Matrix (FirstFactorIndex j) (FirstFactorIndex j) ℂ :=
    (↑γ'⁻¹ : Matrix (FirstFactorIndex j) (FirstFactorIndex j) D.E).map (Φ τ)
  let B (τ : D.Φ) : Matrix (AddedIndex j) (AddedIndex j) ℂ :=
    (Γ : Matrix (AddedIndex j) (AddedIndex j) D.E).map (Φ τ)
  let B' (τ : D.Φ) :
      Matrix (Fin (D.posRank j) ⊕ AddedIndex j) (Fin (D.posRank j) ⊕ AddedIndex j) ℂ :=
    fromBlocks 1 0 0 (B τ)
  have h_subst : twoSidedSubst A B' (stackedDetProd (posEquiv j) (constantRows j i Y')) =
      (∏ τ : D.Φ, ((A τ).det * (B' τ).det) ^ card (DetIndex j τ)) •
        stackedDetProd (posEquiv j) (constantRows j i Y) := by
    rw [h_rows]
    exact twoSidedSubst_stackedDetProd (posEquiv j) (constantRows j i Y) A B'
  -- The kernel of the mixed coordinates for `Y'` at the translated points is the kernel of the
  -- coordinates for `Y` at `(g, h)`.
  let θ' : MvPolynomial (D.Φ × FirstFactorIndex j × AddedIndex j) ℂ →ₗ[ℂ] ℂ :=
    modKernelBilin (stdSpace D.E (AddedIndex j)) (stdSpace D.E (FirstFactorIndex j))
      (firstFactorChar ϑ j)
      (firstFactorChar ϑ j) 𝔪 (1, (stdSpace D.E (AddedIndex j)).embFin Γ * g)
      (1, (stdSpace D.E (FirstFactorIndex j)).embFin γ' * h) Ψ
  let θ : MvPolynomial (D.Φ × FirstFactorIndex j × AddedIndex j) ℂ →ₗ[ℂ] ℂ :=
    modKernelBilin (stdSpace D.E (AddedIndex j)) (stdSpace D.E (FirstFactorIndex j))
      (firstFactorChar ϑ j)
      (firstFactorChar ϑ j) 𝔪 (1, g) (1, h) Ψ
  have h_kernel (l : WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus) :
      θ' (∑ k, schur (untwistedDescentPair j).colsPlus A l k • stackedDetProdCoords j i Y' k) =
        θ (stackedDetProdCoords j i Y l) := by
    refine (modKernelStdSpace_embFin_mul h_char h_char 𝔪 Ψ _ Γ γ' g h).trans ?_
    rw [twoSidedSubst_firstColsCoord A B h_subst]
    -- the powers of the determinants cancel
    simp [θ, A, B, B', ← modKernelBilin_apply, ← map_det, mul_pow,
      ← card_detIndex_add_firstFactorCharExp,
      add_assoc, -card_sum, ← mapMatrix_apply, prod_mul_distrib]
    field [prod_ne_zero_iff, GeneralLinearGroup.det_ne_zero]
  -- On complex conjugates `γ'⁻¹` acts by the Schur matrix of `A`.
  have h_rep (v : WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus → ℂ) :
      (stdSpace D.E (FirstFactorIndex j)).weightRep (untwistedDescentPair j).colsPlus 0 γ'⁻¹
        (star v) =
        star (schur (untwistedDescentPair j).colsPlus A *ᵥ v) := by
    have h_conj (τ : D.Φ) : ((starRingEnd ℂ).comp (Φ τ)).comp (starRingEnd D.E) = Φ τ :=
      RingHom.ext fun x ↦ by simp [starRingEnd_apply (R := D.E)]
    have hA : A = fun τ : D.Φ ↦
        (GeneralLinearGroup.map (Φ τ) (↑γ'⁻¹ : GL (FirstFactorIndex j) D.E)).val := rfl
    have h_star : conj ∘ star v = v := star_star v
    refine star_injective ((map_weightRep conj γ'⁻¹ (star v)).trans ?_)
    simp [weylRep, h_conj, hA, h_star]
  have h_coords : schur (untwistedDescentPair j).colsPlus A *ᵥ θ' ∘ stackedDetProdCoords j i Y' =
      θ ∘ stackedDetProdCoords j i Y := by
    ext l
    simpa [mulVec, dotProduct] using h_kernel l
  have h_smul (θ₀ : MvPolynomial (D.Φ × FirstFactorIndex j × AddedIndex j) ℂ →ₗ[ℂ] ℂ)
      (Y₀ : Matrix D.FlatIndex D.FlatIndex D.E) :
      θ₀ ∘ (H • stackedDetProdCoords j i Y₀) = H • θ₀ ∘ stackedDetProdCoords j i Y₀ := by
    ext l
    simp only [Function.comp_apply, Pi.smul_apply, map_zsmul]
  rw [h_rep, h_smul, h_smul, mulVec_smul, mulVec_smul, h_coords]

/-- Let `i` be a class with its short basis, whose vectors are the rows of `D.shortRows i`, and let
`γ` be a rational unitary point that moves the representative of the class into the points integral
above `p`. Then the entries of `D.shortRows i * γᵀ` are `p`-integral under every embedding `σ`. -/
lemma norm_shortRows_mul_transpose_le_one (i : D.RowChoice) {p : ℕ} [Fact p.Prime]
    (σ : D.E →+* ℂ_[p]) {γ : U (stdSpace D.E D.FlatIndex).J}
    (hγ : (stdSpace D.E D.FlatIndex).embFin γ * i.classRep ∈ integralAbove D.FlatIndex p)
    (x z : D.FlatIndex) :
    ‖σ ((D.shortRows i * (γ : Matrix D.FlatIndex D.FlatIndex D.E)ᵀ) x z)‖ ≤ 1 := by
  -- With Y = `D.shortRows i`, the matrix γ Yᵀ = (γ g)(g⁻¹ Yᵀ) is a product of integral matrices.
  -- Here g is the representative of the class, and `Z` is g⁻¹ Yᵀ.
  let Z : Matrix D.FlatIndex D.FlatIndex (𝔸f D.E) :=
    ((i.classRep⁻¹ : Gf D.E D.FlatIndex) : Matrix D.FlatIndex D.FlatIndex (𝔸f D.E)) *
      (D.shortRows i)ᵀ.map (algebraMap D.E (𝔸f D.E))
  have hZ_int : IsIntMatrix (Ô D.E) Z :=
    (Space.exists_short_basis_stdSpace P.conductor_mem_differentIdeal i.classRep).choose_spec.left
  have hZ_map : IsIntMatrix NormedField.valuation.integer (Z.map (adeleExtension σ)) :=
    fun a b ↦ norm_adeleExtension_le_one σ (hZ_int a b)
  have h_prod : IsIntMatrix NormedField.valuation.integer
      (((γ : Matrix D.FlatIndex D.FlatIndex D.E) * (D.shortRows i)ᵀ).map σ) := by
    simpa [Z, ← Matrix.map_mul, mul_assoc, Function.comp_def] using
      (adeleExtension_mem_intGL σ hγ).isIntMatrix.mul hZ_map
  have h_entry :
      ‖σ (((γ : Matrix D.FlatIndex D.FlatIndex D.E) * (D.shortRows i)ᵀ) z x)‖ ≤ 1 := h_prod z x
  simpa [Matrix.mul_apply, mul_comm] using h_entry

/-- Let v(Y, g, h) be the vector l ↦ conj (c 𝖪[H·ζ_l](g, h)). Here ζ = `stackedDetProdCoords j i Y`,
and 𝖪 is the theta kernel of the standard definite spaces W^add on `AddedIndex j` and V″ on
`FirstFactorIndex j`, with both characters `firstFactorChar ϑ j` for the tame character `ϑ` and a
datum `Ψ` on matrices modulo the modulus `𝔪`. Suppose that v(Y, g', h') has `p`-integral coordinates
under `ιₚ : ℂ → ℂ_[p]` whenever the finite adelic points `g'`, `h'` have integral components at the
primes above `p` (`integralAbove`) and the entries of `Y`, embedded in ℂ by `Φ τ`, are `p`-integral
under `ιₚ ∘ conj`. Let g be the block diagonal point (`U.blockSumOne`) with blocks `1`, the
representative in U(W♭) of the class of `i`, and `w` in U(E^{3m}). Then v(`D.shortRows i`, g, h) has
gauge at most one at every `h` (`weylGauge`): all coordinates of h⁻¹ · ιₚ(v) have norm at most
one. -/
lemma weylGauge_modKernelBilin_stackedDetProdCoords_le_one (j : D.LiftIndex) (i : D.RowChoice)
    {𝔪 : Modulus D.E} (Ψ : Matrix (FirstFactorIndex j) (AddedIndex j) 𝔪.ResidueRing → ℂ)
    {p : ℕ} [Fact p.Prime] [PadicPlace p] (c : ℂ) (H : ℤ)
    (h_int : ∀ g' ∈ integralAbove (AddedIndex j) p, ∀ h' ∈ integralAbove (FirstFactorIndex j) p,
      ∀ Y : Matrix D.FlatIndex D.FlatIndex D.E,
        (∀ (τ : D.Φ) (x z : D.FlatIndex), ‖ιₚ (conj (Φ τ (Y x z)))‖ ≤ 1) →
        ∀ l : WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus,
          ‖ιₚ (conj (c * modKernelStdSpace (stdSpace D.E (AddedIndex j)) (firstFactorChar ϑ j)
            (firstFactorChar ϑ j) 𝔪 Ψ (H • stackedDetProdCoords j i Y l) (1, g') h'))‖ ≤ 1)
    (w : Gf D.E D.CarrierIndex) (h : Gf D.E (FirstFactorIndex j)) :
    weylGauge (untwistedDescentPair j).colsPlus 0 h
      (star (c • modKernelBilin (stdSpace D.E (AddedIndex j)) (stdSpace D.E (FirstFactorIndex j))
        (firstFactorChar ϑ j) (firstFactorChar ϑ j) 𝔪
          (1, U.blockSumOne (1, U.blockSumOne (i.classRep, w))) (1, h)
        Ψ ∘ (H • stackedDetProdCoords j i (D.shortRows i)))) ≤ 1 := by
  -- Weak approximation: rational points move the two blocks and h into the integral points.
  obtain ⟨γ₁, hγ₁, -⟩ := exists_mul_mem_integralAbove p i.classRep 1 (stdSpace D.E D.FlatIndex)
  obtain ⟨γ₂, hγ₂, -⟩ := exists_mul_mem_integralAbove p w 1 (stdSpace D.E D.CarrierIndex)
  obtain ⟨γ', hγ', -⟩ := exists_mul_mem_integralAbove p h 1 (stdSpace D.E (FirstFactorIndex j))
  -- Move `g` by the block matrix Γ; the short basis becomes Y'.
  let g : Gf D.E (AddedIndex j) := U.blockSumOne (1, U.blockSumOne (i.classRep, w))
  let Γ : U (stdSpace D.E (AddedIndex j)).J := U.blockSumOne (1, U.blockSumOne (γ₁, γ₂))
  let Y' : Matrix D.FlatIndex D.FlatIndex D.E :=
    D.shortRows i * (γ₁ : Matrix D.FlatIndex D.FlatIndex D.E)ᵀ
  have hΓ : (stdSpace D.E (AddedIndex j)).embFin Γ * g ∈ integralAbove (AddedIndex j) p :=
    blockSumOne_mul_mem_integralAbove (γ := 1) (by simp) (blockSumOne_mul_mem_integralAbove hγ₁ hγ₂)
  have h_rows : constantRows j i Y' = fun (τ : D.Φ) (k : DetIndex j τ) ↦
      constantRows j i (D.shortRows i) τ k *
        (fromBlocks 1 0 0 ((Γ : Matrix (AddedIndex j) (AddedIndex j) D.E).map (Φ τ)))ᵀ :=
    constantRows_mul_transpose_eq_mul_fromBlocks ..
  have hY' (τ : D.Φ) (x z : D.FlatIndex) : ‖ιₚ (conj (Φ τ (Y' x z)))‖ ≤ 1 :=
    norm_shortRows_mul_transpose_le_one i ((ιₚ.comp conj).comp (Φ τ)) hγ₁ x z
  -- By equivariance the gauge at h is the gauge of the vector for Y' at the integral point γ' h,
  -- where gauge ≤ 1 means that all coordinates are integral.
  rw [← modKernelBilin_stackedDetProdCoords_equivariant j i Ψ Γ γ' g h c H h_rows,
    ← weylGauge_embFin,
    Representation.self_inv_apply, weylGauge_le_one_iff _ hγ']
  exact h_int _ hΓ _ hγ' Y' hY'

/-- Let `ϑ` be a tame character with set of places Q, let ϖ be the product of the chosen places, and
let `u`, `x` be matrices modulo ϖ² and ϖ²Q. The datum `addedDatum ϑ j u x` is `0` or a sum, over
GL_{3m}(O_E/ϖ²), of values of the additive character attached to `u`. For each `n` it has norm at
most one under all ring maps `ℂ → ℂ_[l]` with `l` a prime coprime to `n`
(`New.Seesaw.integralAway`). -/
lemma addedDatum_mem_integralAway {ϑ : D.TameChar} (j : D.LiftIndex)
    (u : Matrix D.CarrierIndex (FirstFactorIndex j) (D.untwistedModulus 2).ResidueRing)
    (x : Matrix (FirstFactorIndex j) (AddedIndex j) (D.twistModulus ϑ 2).ResidueRing) (n : ℕ) :
    addedDatum ϑ j u x ∈ Seesaw.integralAway n := by
  -- The values of an additive character of a finite group are roots of unity.
  have h_char (y : Matrix (FirstFactorIndex j) D.CarrierIndex (D.untwistedModulus 2).ResidueRing) :
      traceChar u y ∈ Seesaw.integralAway n := fun l _ _ ι ↦
    ((ι.compAddChar _).norm_apply _).le
  rw [addedDatum]
  split
  · exact sum_mem fun g _ ↦ h_char _
  · exact zero_mem _

/-- Every conjugate of a value of `New.Data.addedDatum`, for a matrix `u` modulo ϖ², has absolute
value at most the order of GL over the residue ring of `D.untwistedModulus 2` (the modulus ϖ², ϖ
the product of the chosen places), the number of terms in the sum defining it. -/
lemma norm_map_addedDatum_le (j : D.LiftIndex)
    (u : Matrix D.CarrierIndex (FirstFactorIndex j) (D.untwistedModulus 2).ResidueRing)
      (σ : ℂ ≃+* ℂ)
    (x : Matrix (FirstFactorIndex j) (AddedIndex j) (D.twistModulus ϑ 2).ResidueRing) :
    ‖σ (addedDatum ϑ j u x)‖ ≤ card (GL D.CarrierIndex (D.untwistedModulus 2).ResidueRing) := by
  -- The value is 0 or a sum, over this group, of values of an additive character.
  rw [addedDatum]
  split
  · simpa using! norm_sum_le_of_le univ fun _ _ ↦ ((σ.toRingHom.compAddChar _).norm_apply _).le
  · simp

/-- The ranks of the five spaces in the three kernels are at most the gap `Δ = D.gap`. -/
lemma card_le_gap (j : D.LiftIndex) :
    card (Fin D.m) ≤ D.gap ∧
    card D.CarrierIndex ≤ D.gap ∧
    card (Fin j) ≤ D.gap ∧
    card (FirstFactorIndex j) ≤ D.gap ∧
    card (AddedIndex j) ≤ D.gap := by
  have h_gap : 40 * D.k ≤ D.gap := mod_cast (D.le_of_hasLogBound : (40 * D.k : ℝ) ≤ D.gap)
  grind [card_sum, card_rowIndex, Fintype.card_fin]

/-- Let ζ = `stackedDetProdCoords j i (D.shortRows i)` be the vector of coordinates of the product
of determinants, polynomials in variables indexed by an infinite place in `D.Φ`, a row in
`FirstFactorIndex j` and a column in `AddedIndex j`. Evaluate `H • ζ` at a point `z` whose
`σ`-conjugates are at most `M ^ 4`, where `M = D.M`, and apply `σ`. If `q` bounds the total number
of determinants, the root of the squared norm (`New.weylNormSq`) of the result is at most
`√(H ^ 2 (M ^ 9) ^ ((12 m + 1) q))`, with `m = D.m`. -/
lemma sqrt_weylNormSq_smul_eval_stackedDetProdCoords_le (j : D.LiftIndex) (i : D.RowChoice) {q : ℕ}
    (hq : ∑ τ : D.Φ, card (DetIndex j τ) ≤ q) (H : ℤ) (σ : ℂ ≃+* ℂ)
    {z : D.Φ × FirstFactorIndex j × AddedIndex j → ℂ}
    (hz : ∀ x : D.Φ × FirstFactorIndex j × AddedIndex j, ‖σ (z x)‖ ≤ D.M ^ 4) :
    √(weylNormSq (σ ∘ eval z ∘ (H • stackedDetProdCoords j i (D.shortRows i)))) ≤
      √((H : ℝ) ^ 2 * (D.M ^ 9) ^ ((12 * D.m + 1) * q)) := by
  -- The rows `D.shortRows i` form a short basis, so their entries are small too.
  have hY_small (ψ : D.E →+* ℂ) (x y : D.FlatIndex) :
      ‖ψ (D.shortRows i x y)‖ ≤ Space.shortBasisConst D.E D.FlatIndex (P.q₁ D.towerExp * P.d) :=
    (Space.exists_short_basis_stdSpace P.conductor_mem_differentIdeal i.1.out).choose_spec.2 ψ y x
  have hY_le (τ : D.Φ) (x y : D.FlatIndex) : ‖σ (Φ τ (D.shortRows i x y))‖ ≤ D.M ^ 4 :=
    (hY_small (.comp σ (Φ τ)) x y).trans (by simpa using D.le_of_hasLogBound)
  have h_coords : weylNormSq ((σ : ℂ →+* ℂ) ∘ eval z ∘ stackedDetProdCoords j i (D.shortRows i)) ≤
      ↑(D.M ^ 9) ^ ((12 * D.m + 1) * ∑ τ : D.Φ, card (DetIndex j τ)) :=
    weylNormSq_comp_eval_stackedDetProdCoords_le j i (D.shortRows i) hY_le hz
  have h_smul : eval z ∘ (H • stackedDetProdCoords j i (D.shortRows i)) =
      (H : ℂ) • eval z ∘ stackedDetProdCoords j i (D.shortRows i) := by simp [funext_iff]
  -- The scalar `H` multiplies the squared norm by `H ^ 2`, and `M ^ 9 ≥ 1` lets `q` replace the
  -- number of determinants.
  grw (transparency := default) [h_smul, weylNormSq_comp_smul, h_coords, hq]
  · simp
  · exact D.le_of_hasLogBound

/-- Duality for a vector `v` of homogeneous polynomials of degree `n`. Its coordinates are indexed
by the basis `WeylIndex N κ` of the Weyl module of GL_N whose diagram at each `τ : T` has `κ τ h`
columns of height `h`. The norm of a coordinate vector is the square root of `weylNormSq`, its
squared norm for the positive definite Hermitian form of the Gram matrix. Let `σ` be a ring
automorphism of ℂ. Suppose that the `σ`-conjugates of the values of `v` on a set `S` have norm at
most `B`. Suppose also that a linear form `θ` has `‖σ (θ Q)‖ ≤ C` for every homogeneous `Q` of
degree `n` with `‖σ (Q z)‖ ≤ B` on `S`. Then the `σ`-conjugate of `θ ∘ v` has norm at most `C`. -/
lemma sqrt_weylNormSq_comp_le_of_eval_le {T N ι : Type} [Fintype T] [DecidableEq T] [Fintype N]
    [DecidableEq N] {κ : T → ℕ → ℕ} (σ : ℂ ≃+* ℂ) (θ : MvPolynomial ι ℂ →ₗ[ℂ] ℂ)
    {v : WeylIndex N κ → MvPolynomial ι ℂ} {n : ℕ} {S : Set (ι → ℂ)} {B C : ℝ}
    (hv_hom : ∀ l : WeylIndex N κ, (v l).IsHomogeneous n)
    (hv_le : ∀ z ∈ S, √(weylNormSq (σ ∘ eval z ∘ v)) ≤ B)
    (hθ : ∀ Q : MvPolynomial ι ℂ, Q.IsHomogeneous n → (∀ z ∈ S, ‖σ (Q.eval z)‖ ≤ B) →
      ‖σ (θ Q)‖ ≤ C) :
    √(weylNormSq (σ ∘ θ ∘ v)) ≤ C := by
  -- Test against a functional f of norm at most one, and apply `hθ` to Q = ∑ f l • v l.
  refine sqrt_weylNormSq_le_of_dual σ fun f hf ↦ ?_
  have hQ_hom : (∑ l, f l • v l).IsHomogeneous n :=
    (homogeneousSubmodule ι ℂ n).sum_mem fun l _ ↦ Submodule.smul_mem _ (f l) (hv_hom l)
  have hQ_le (z : ι → ℂ) (hz : z ∈ S) : ‖σ ((∑ l, f l • v l).eval z)‖ ≤ B := by
    simpa [dotProduct] using (hf (eval z ∘ v)).trans (hv_le z hz)
  simpa [dotProduct] using hθ _ hQ_hom hQ_le

/-- Let `p` be a prime with an embedding `ιₚ : ℂ → ℂ_[p]` (`PadicPlace p`). A vector `y` of weight
μ⁺ = `(untwistedDescentPair j).colsPlus` is `p`-integral at `h` if `weylGauge μ⁺ 0 h y ≤ 1`: all
coordinates of h⁻¹ · ιₚ(y) have norm at most one. Let every `f w v` be `p`-integral at `h`. Then so
is their double class sum over U(E^{3m}) and U(E^m) (`stdClassSum`, the sum of the values at class
representatives divided by the orders of the stabilisers), multiplied by the square of
`D.chosenGroupOrder`, which is a common multiple of these orders. -/
lemma weylGauge_stdClassSum_stdClassSum_le_one {j : D.LiftIndex} {p : ℕ} [Fact p.Prime]
    [PadicPlace p] (h : Gf D.E (FirstFactorIndex j))
    {f : Gf D.E D.CarrierIndex → Gf D.E (Fin D.m) →
      WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus → ℂ}
    (hf : ∀ (w : Gf D.E D.CarrierIndex) (v : Gf D.E (Fin D.m)),
      weylGauge (untwistedDescentPair j).colsPlus 0 h (f w v) ≤ 1) :
    weylGauge (untwistedDescentPair j).colsPlus 0 h
      ((D.chosenGroupOrder ^ 2 : ℂ) •
        stdClassSum (stdLevel D.E D.CarrierIndex) fun w : Gf D.E D.CarrierIndex ↦
          stdClassSum (stdLevel D.E (Fin D.m)) (f w)) ≤ 1 := by
  -- Each of the two class sums takes one factor `D.chosenGroupOrder`, a multiple of the orders of
  -- all the stabilisers.
  let A : ℕ := D.chosenGroupOrder
  have h_carrier : card D.CarrierIndex ≤ 2 * D.n D.m := by simpa using D.nat_le_of_hasLogBound
  have h_fin : card (Fin D.m) ≤ 2 * D.n D.m := by simpa using D.nat_le_of_hasLogBound
  have h_inner (w : Gf D.E D.CarrierIndex) :
      weylGauge (untwistedDescentPair j).colsPlus 0 h
        ((A : ℂ) • stdClassSum (stdLevel D.E (Fin D.m)) (f w)) ≤ 1 := by
    simpa [A] using weylGauge_classSum_le_one h (card_classAut_dvd_chosenGroupOrder h_fin le_rfl)
      (c := 1) (f := f w) fun v ↦ by simpa using hf w v
  simpa [A, sq] using
    weylGauge_classSum_le_one h (card_classAut_dvd_chosenGroupOrder h_carrier le_rfl) h_inner

/-- Let `q` = |D.Φ| (natB + offWeight + Δ + m Δ) be the bound on the number of determinants, with
the weights `D.natB`, `D.offWeight` and the gap Δ = `D.gap`. Let `n ≤ (10 m + 1) q`, `n ≤ M` for
M = `D.M`, and `0 < H ≤ (n ^ n) ^ 3`. Let every vector `F w v` have `φ`-conjugate of norm at most
exp(3 x₁) |GL_{3m}(O_E/ϖ²)| √(H² M^{9 (12 m + 1) q}), where x₁ = `D.x₁` is a size parameter of the
data and ϖ² = `D.untwistedModulus 2` is the square of the product of the chosen places. Then the
double class sum of `F`, multiplied by the square of `D.chosenGroupOrder` (a common multiple of the
orders of the stabilisers), has `φ`-conjugate of squared norm at most exp(f m b log² b), for the
number f = `D.f` of infinite places, the weight b = `D.b` and log b = `D.logB`. -/
lemma weylNormSq_stdClassSum_stdClassSum_le {j : D.LiftIndex} {q n : ℕ} {H : ℤ}
    (hq : q = Fintype.card D.Φ * (D.natB + D.offWeight + D.gap + D.m * D.gap))
    (hn : n ≤ (10 * D.m + 1) * q) (hn_le_M : n ≤ D.M) (H_pos : 0 < H)
    (H_le : H ≤ (n ^ n) ^ 3) (φ : ℂ ≃+* ℂ)
    {F : Gf D.E D.CarrierIndex → Gf D.E (Fin D.m) →
      WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus → ℂ}
    (hF : ∀ (w : Gf D.E D.CarrierIndex) (v : Gf D.E (Fin D.m)),
      √(weylNormSq (φ ∘ F w v)) ≤ rexp D.x₁ * rexp D.x₁ *
        (rexp D.x₁ * card (GL D.CarrierIndex (D.untwistedModulus 2).ResidueRing) *
          √((H : ℝ) ^ 2 * (D.M ^ 9) ^ ((12 * D.m + 1) * q)))) :
    weylNormSq (φ ∘ ((D.chosenGroupOrder ^ 2 : ℂ) •
        stdClassSum (stdLevel D.E D.CarrierIndex) fun w : Gf D.E D.CarrierIndex ↦
          stdClassSum (stdLevel D.E (Fin D.m)) (F w))) ≤
      rexp (D.f * D.m * D.b * D.logB ^ 2) := by
  -- Each class sum multiplies the bound by its class number; the rest is numerical.
  have h_sum : √(weylNormSq (φ ∘ stdClassSum (stdLevel D.E D.CarrierIndex)
        fun w : Gf D.E D.CarrierIndex ↦ stdClassSum (stdLevel D.E (Fin D.m)) (F w))) ≤
      Nat.card (StdClasses (stdLevel D.E D.CarrierIndex)) *
        (Nat.card (StdClasses (stdLevel D.E (Fin D.m))) *
        (rexp D.x₁ * rexp D.x₁ *
          (rexp D.x₁ * card (GL D.CarrierIndex (D.untwistedModulus 2).ResidueRing) *
            √((H : ℝ) ^ 2 * (D.M ^ 9) ^ ((12 * D.m + 1) * q))))) :=
    sqrt_weylNormSq_classSum_le φ fun w ↦ sqrt_weylNormSq_classSum_le φ (hF w)
  grw (transparency := default) [weylNormSq_comp_smul, (sqrt_le_iff.1 h_sum).2]
  exact firstFactorSize_sq_le_exp hq hn hn_le_M H_pos H_le φ

/-- The vector `y` of weight `(untwistedDescentPair j).colsPlus` is integral at `h` away from the
norm `ϑ.normQ` of Q (the product of the norms of the places in `ϑ.Q`), and has small conjugates if
`ϑ.Q` is empty: the bound is exp(f m b log² b), for the number f = `D.f` of infinite places, the
weight b = `D.b` and log b = `D.logB`. -/
structure IsIntegralAndSmall (ϑ : D.TameChar) (j : D.LiftIndex) (h : Gf D.E (FirstFactorIndex j))
    (y : WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus → ℂ) : Prop where
  /-- `y` is `p`-integral at `h` for every prime `p` that does not divide `ϑ.normQ`. -/
  weylGauge_le_one (p : ℕ) [Fact p.Prime] [PadicPlace p] (hp : p.Coprime ϑ.normQ) :
    weylGauge (untwistedDescentPair j).colsPlus 0 h y ≤ 1
  /-- If `ϑ.Q` is empty, all conjugates of `y` have squared norm at most exp(f m b log² b). -/
  weylNormSq_le (hQ : ϑ.Q = ∅) (φ : ℂ ≃+* ℂ) :
    weylNormSq (φ ∘ y) ≤ Real.exp (D.f * D.m * D.b * D.logB ^ 2)

/-- Let `ϑ` be a tame character and χ′ = χ^j ϑ, where χ = `D.chiM` is the fixed character of U(1)(𝔸)
of weight `0` and tame part `D.chiMLocal`. Take the theta kernel of the standard definite spaces
(E^m, E^{3m}) with characters χ′ and `1`, unit modulus, datum `1` and polynomial `1`, and a constant
`c` that normalises such kernels. For every prime `p` with an embedding `ιₚ : ℂ → ℂ_[p]`, the image
of `c` times the kernel has norm at most one at all finite adelic points `v`, `w`. -/
lemma norm_mul_modKernelStdSpace_twistedChiMPow_le_one {ϑ : D.TameChar} {j : D.LiftIndex} {c : ℂ}
    (hc : IsModKernelScale (Fin D.m) D.CarrierIndex D 0 c) {p : ℕ} [Fact p.Prime] [PadicPlace p]
    (v : Gf D.E (Fin D.m)) (w : Gf D.E D.CarrierIndex) :
    ‖ιₚ (c * modKernelStdSpace (stdSpace D.E (Fin D.m)) (twistedChiMPow ϑ j) 1 (unitModulus D.E) 1 1
      (1, v) w)‖ ≤ 1 := by
  -- Move v and w into the integral points; the kernel does not change, as the polynomial is 1 and
  -- both characters have weight 0.
  obtain ⟨γv, hγv, -⟩ := exists_mul_mem_integralAbove p v 1 (stdSpace D.E (Fin D.m))
  obtain ⟨γw, hγw, -⟩ := exists_mul_mem_integralAbove p w 1 (stdSpace D.E D.CarrierIndex)
  have h_char := twistedChiMPow_hasWeight ϑ j
  have h_inv : modKernelStdSpace (stdSpace D.E (Fin D.m)) (twistedChiMPow ϑ j) 1 (unitModulus D.E)
      1 1 (1, (stdSpace D.E (Fin D.m)).embFin γv * v)
        ((stdSpace D.E D.CarrierIndex).embFin γw * w) =
      modKernelStdSpace (stdSpace D.E (Fin D.m)) (twistedChiMPow ϑ j) 1 (unitModulus D.E) 1 1
        (1, v) w := by
    simp [modKernelStdSpace_embFin_mul h_char .one]
  rw [← h_inv]
  exact hc.norm_le_one (q := 1) h_char .one Submodule.mem_top (by simp) (isHomogeneous_one _ _)
    p.coprime_one_right hγv hγw (one_mem _)

/-- Take the theta kernel `modKernelStdSpace` of (E^j, V″), with V″ the standard definite space on
the index set `FirstFactorIndex j`, for the characters `1` and `b`, a datum `Ψ` modulo `𝔪` and the
polynomial `1`. Let `c` be a constant that normalises such kernels. Let `b` have weight `e` at the
infinite places `D.Φ` and tame part `ψ`, a character of the residue field `ResField w` at each
finite place `w`. Let `𝔪` contain `q * D.M ^ 2`, with `D.M` the integer `M` of the data. Let the
values of `Ψ` have norm at most one under all ring maps `ℂ → ℂ_[l]` with `l` a prime coprime to `q`.
Let `p` be a prime coprime to `q`, and let `h` lie in `Gf D.E (FirstFactorIndex j)`, the finite
adelic unitary group of V″. Then the image under `ιₚ : ℂ → ℂ_[p]` of `c` times the kernel at `1` and
`h` has norm at most one. -/
lemma norm_mul_modKernelStdSpace_one_le_one {j : D.LiftIndex} {c : ℂ}
    (hc : IsModKernelScale (Fin j) (FirstFactorIndex j) D 0 c) {b : AutChar D.E} {e : D.Φ → ℤ}
    {ψ : (w : FinPlace D.E) → MulChar (ResField w) ℂ} (hb : b.HasWeight e ψ) {q : ℕ}
    {𝔪 : Modulus D.E} (h𝔪 : ↑(q * D.M ^ 2) ∈ 𝔪.ideal)
    {Ψ : Matrix (FirstFactorIndex j) (Fin j) 𝔪.ResidueRing → ℂ}
    (hΨ : ∀ x : Matrix (FirstFactorIndex j) (Fin j) 𝔪.ResidueRing, Ψ x ∈ Seesaw.integralAway q)
    {p : ℕ} [Fact p.Prime] [PadicPlace p] (hp : p.Coprime q) (h : Gf D.E (FirstFactorIndex j)) :
    ‖ιₚ (c * modKernelStdSpace (stdSpace D.E (Fin j)) 1 b 𝔪 Ψ 1 (1, 1) h)‖ ≤ 1 := by
  -- Move h into the integral points; the kernel does not change, as the polynomial and the first
  -- character are 1.
  obtain ⟨γ, hγ, -⟩ := exists_mul_mem_integralAbove p h 1 (stdSpace D.E (FirstFactorIndex j))
  have h_inv : modKernelStdSpace (stdSpace D.E (Fin j)) 1 b 𝔪 Ψ 1 1
      ((stdSpace D.E (FirstFactorIndex j)).embFin γ * h) =
      modKernelStdSpace (stdSpace D.E (Fin j)) 1 b 𝔪 Ψ 1 1 h := by
    simpa [Prod.mk_one_one] using modKernelStdSpace_embFin_mul .one hb 𝔪 Ψ 1 1 γ 1 h
  simpa [h_inv, Prod.mk_one_one] using
    hc.norm_le_one .one hb h𝔪 hΨ (isHomogeneous_one _ _) hp (one_mem _) hγ (one_mem _)

/-- Expansion of the conjugate of a multiple of the series Υ = `leftSideSeries ϑ j (u, i) h`, for a
tame character `ϑ`, a matrix `u` modulo ϖ² (`D.untwistedModulus 2`, ϖ the product of the chosen
places) and a class with rows `i`. Let g = `D.chosenGroupOrder`, a common multiple of the orders of
the stabilisers. There is `c` of modulus one, depending only on `j`, such that the conjugate of g²
c₂ H c₀ conj(c₁) c Υ is g² times a double class sum over U(E^{3m}) and U(E^m) of conjugates of
products of three theta kernels of definite spaces: `k₀` of (E^m, E^{3m}), the conjugate of `k₁` of
(E^j, V″), and c₂ times the kernel of (W^add, V″) at the polynomial vector
`H • stackedDetProdCoords j i (D.shortRows i)`, formed with a short basis of the class. V″ and W^add
are the spaces on `FirstFactorIndex j` and `AddedIndex j`, and the last two kernels have modulus
ϖ²Q. Here `Ψ x` is the conjugate, at `normNegOne • x` (a chosen element of norm −1, reduced), of the
indicator of the matrix of the inclusion E^j → V″ (`inclMatrix`), and `b'` is the inverse of the
character `firstFactorChar ϑ j` times the power rank V″ of `upsilonU1` (υ on the norm-one ideles).
The scalars `c₀`, `c₁`, `c₂` and the integer `H` are arbitrary. -/
lemma exists_star_leftSideSeries_eq_classSum (j : D.LiftIndex) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ (c₀ c₁ c₂ : ℂ) (H : ℤ)
      (u : Matrix D.CarrierIndex (FirstFactorIndex j) (D.untwistedModulus 2).ResidueRing)
      (i : D.RowChoice) (ϑ : D.TameChar) (h : Gf D.E (FirstFactorIndex j)),
      let Ψ : Matrix (FirstFactorIndex j) (Fin j) (D.twistModulus ϑ 2).ResidueRing → ℂ := fun x ↦
        (conj ∘ Pi.single (inclMatrix (D.twistModulus ϑ 2).ResidueRing (inl ∘ inr ∘ inl)) 1)
          ((D.twistModulus ϑ 2).normNegOne • x)
      let b' : AutChar D.E := (firstFactorChar ϑ j)⁻¹ * WeilData.upsilonU1 ^ Nat.card
        (FirstFactorIndex j)
      let k₀ (v : Gf D.E (Fin D.m)) (w : Gf D.E D.CarrierIndex) : ℂ :=
        c₀ * modKernelStdSpace (stdSpace D.E (Fin D.m)) (twistedChiMPow ϑ j) 1 (unitModulus D.E) 1 1
          (1, v) w
      let k₁ : ℂ := c₁ * modKernelStdSpace (stdSpace D.E (Fin j)) 1 b' (D.twistModulus ϑ 2) Ψ 1
        (1, 1) h
      star ((D.chosenGroupOrder * D.chosenGroupOrder * c₂ * H * c₀ * conj c₁ * c : ℂ) •
          leftSideSeries ϑ j (u, i) h) =
        (D.chosenGroupOrder ^ 2 : ℂ) •
          stdClassSum (stdLevel D.E D.CarrierIndex) fun w : Gf D.E D.CarrierIndex ↦
            stdClassSum (stdLevel D.E (Fin D.m)) fun v : Gf D.E (Fin D.m) ↦
              star ((k₀ v w * conj k₁) • c₂ •
                modKernelBilin (stdSpace D.E (AddedIndex j)) (stdSpace D.E (FirstFactorIndex j))
                  (firstFactorChar ϑ j) (firstFactorChar ϑ j) (D.twistModulus ϑ 2)
                  (1, U.blockSumOne (1, U.blockSumOne (i.classRep, w))) (1, h)
                  (addedDatum ϑ j u) ∘
                (H • stackedDetProdCoords j i (D.shortRows i))) := by
  -- The first factor of Υ, a kernel of ((E^j)⁻, V″), is a multiple of conj k₁. The other factor is
  -- a double class sum once `carrierCoeff` is expanded. Then conjugate term by term.
  obtain ⟨c, hc, h_neg⟩ :=
    exists_conj_modKernel_eq_mul_modKernel_neg (stdSpace D.E (Fin j))
      (stdSpace D.E (FirstFactorIndex j))
  refine ⟨c, hc, fun c₀ c₁ c₂ H u i ϑ h ↦ ?_⟩
  intro Ψ b' k₀ k₁
  ext l
  have h_char : b'⁻¹ * WeilData.upsilonU1 ^ card (FirstFactorIndex j) = firstFactorChar ϑ j := by
    rw [← Nat.card_eq_fintype_card, mul_inv, inv_inv, inv_mul_cancel_right]
  have h_first : conj k₁ = conj c₁ * c *
      modKernelStdSpace (stdSpace D.E (Fin j)).neg (WeilData.upsilonU1 ^ j.val)
        (firstFactorChar ϑ j) (D.twistModulus ϑ 2)
        (Pi.single (inclMatrix (D.twistModulus ϑ 2).ResidueRing (inl ∘ inr ∘ inl)) 1) 1 1 h := by
    rw [map_mul, h_neg, h_char, mul_assoc]
    simp [Ψ, Prod.mk_one_one]
  -- `θ w` is the kernel of (W^add, V″) at the coordinate `l` of ζ.
  let θ (w : Gf D.E D.CarrierIndex) : ℂ :=
    modKernelStdSpace (stdSpace D.E (AddedIndex j)) (firstFactorChar ϑ j) (firstFactorChar ϑ j)
      (D.twistModulus ϑ 2) (addedDatum ϑ j u) (stackedDetProdCoords j i (D.shortRows i) l)
      (1, U.blockSumOne (1, U.blockSumOne (i.classRep, w))) h
  have h_series : c₂ * H * c₀ * conj c₁ * c * leftSideSeries ϑ j (u, i) h l =
      stdClassSum (stdLevel D.E D.CarrierIndex) fun w : Gf D.E D.CarrierIndex ↦
        stdClassSum (stdLevel D.E (Fin D.m)) fun v : Gf D.E (Fin D.m) ↦
          k₀ v w * conj k₁ * (c₂ * (H * θ w)) := by
    simp only [leftSideSeries, carrierCoeff, classSum_mul, mul_classSum, h_first, k₀, θ]
    ac_rfl
  -- Class sums of vectors are computed coordinate by coordinate.
  have h_coord {n : Type} [Fintype n] [DecidableEq n]
      (F : Gf D.E n → WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus → ℂ) :
      stdClassSum (stdLevel D.E n) F l = stdClassSum (stdLevel D.E n) fun g : Gf D.E n ↦ F g l :=
    map_classSum (Pi.evalAddMonoidHom (fun _ ↦ ℂ) l) F
  have h_scalar : D.chosenGroupOrder * D.chosenGroupOrder * c₂ * H * c₀ * conj c₁ * c *
      leftSideSeries ϑ j (u, i) h l =
        D.chosenGroupOrder ^ 2 * (c₂ * H * c₀ * conj c₁ * c * leftSideSeries ϑ j (u, i) h l) := by
    ring
  rw [Pi.star_apply, Pi.smul_apply, smul_eq_mul, h_scalar, h_series]
  simp [h_coord, map_classSum, θ, ← Int.cast_smul_eq_zsmul ℂ H]

/-- For 1 ≤ j ≤ m there is one c ≠ 0, independent of i, ϑ and h, such that every vector y = conj
(c · Υ) is integral and small in the sense of `New.Data.IsIntegralAndSmall`: for every prime p that
does not divide `ϑ.normQ`, the product of the norms of the places in `ϑ.Q`, the coordinates of
h⁻¹ · ιₚ(y) are `p`-integral (`New.weylGauge` ≤ 1), and if `ϑ.Q = ∅`, every conjugate φ ∘ y,
φ ∈ Aut(ℂ), has squared norm at most exp(f m b log² b), with the number f = `D.f` of infinite
places, m = `D.m`, the weight b = `D.b` and log b = `D.logB`. -/
lemma exists_isIntegralAndSmall_leftSideSeries (j : D.LiftIndex) :
    ∃ c ≠ (0 : ℂ), ∀ (i : ChoiceIndex j) (ϑ : D.TameChar) (h : Gf D.E (FirstFactorIndex j)),
      IsIntegralAndSmall ϑ j h (star (c • leftSideSeries ϑ j i h)) := by
  -- Write the vector y as a double class sum of terms conj(k₀ · conj k₁ · k₂), three kernels of
  -- definite pairs, each made integral by a constant from `exists_ne_zero_isModKernelScale`;
  -- the last is evaluated on H·`stackedDetProdCoords`. Integrality: move the classes into the
  -- p-integral points and multiply the three bounds. Size: bound each term by duality, count the
  -- classes, via `weylNormSq_stdClassSum_stdClassSum_le`. `q` bounds the total number of
  -- determinants, over the infinite places.
  let q : ℕ := card D.Φ * (D.natB + D.offWeight + D.gap + D.m * D.gap)
  have h_detCount : ∑ τ : D.Φ, card (DetIndex j τ) ≤ q :=
    sum_le_card_nsmul _ _ _ fun τ _ ↦ card_detIndex_le j τ
  -- The degree n ≤ (10 m + 1) q and the denominator 0 < H ≤ n³ⁿ of ζ: by `h_denom`, each
  -- `H • stackedDetProdCoords j i Y l` is homogeneous of degree n, with coefficients in every
  -- subring of ℂ that contains the conjugates of the entries of `Y`.
  obtain ⟨n, hn, H, H_pos, H_le, h_denom⟩ :=
    exists_isHomogeneousOverEntries_smul_stackedDetProdCoords j
  grw [h_detCount] at hn
  have hn_le_M : n ≤ D.M := hn.trans D.nat_le_of_hasLogBound
  -- The constants of the three kernels: by `K₀`, `K₁`, `K₂`, cᵢ times the kernel is integral at
  -- p-integral points and has bounded conjugates.
  obtain ⟨c₀, hc₀, K₀⟩ := exists_ne_zero_isModKernelScale (Fin D.m) D.CarrierIndex D 0
  obtain ⟨c₁, hc₁, K₁⟩ := exists_ne_zero_isModKernelScale (Fin j) (FirstFactorIndex j) D 0
  obtain ⟨c₂, hc₂, K₂⟩ := exists_ne_zero_isModKernelScale (AddedIndex j) (FirstFactorIndex j) D
    n
  obtain ⟨c, hc, h_expand⟩ := exists_star_leftSideSeries_eq_classSum j
  let scale : ℂ := D.chosenGroupOrder * D.chosenGroupOrder * c₂ * H * c₀ * conj c₁ * c
  refine ⟨scale, ?_, ?_⟩
  · simp [scale, H_pos.ne', ne, ← norm_pos_iff, hc, hc₀, hc₁, hc₂]
  intro ⟨u, i⟩ ϑ h
  -- The characters and the data of the kernels; the data are integral away from `ϑ.normQ`.
  let 𝔪 : Modulus D.E := D.twistModulus ϑ 2
  let b' : AutChar D.E := (firstFactorChar ϑ j)⁻¹ * WeilData.upsilonU1 ^ Nat.card
    (FirstFactorIndex j)
  have hb : (firstFactorChar ϑ j).HasWeight (firstFactorCharExp j + -D.liftWeight j ·)
    (D.liftTamePart ϑ j) :=
    inferInstance
  have hb' : b'.HasWeight _ (D.liftTamePart ϑ j)⁻¹ := hb.inv.mul_upsilonU1_pow _
  let Ψ : Matrix (FirstFactorIndex j) (Fin j) 𝔪.ResidueRing → ℂ := fun x ↦
    (conj ∘ Pi.single (inclMatrix 𝔪.ResidueRing (inl ∘ inr ∘ inl)) 1) (𝔪.normNegOne • x)
  have hΨ (x : Matrix (FirstFactorIndex j) (Fin j) 𝔪.ResidueRing) :
    Ψ x ∈ Seesaw.integralAway ϑ.normQ := by
    simp [Ψ, apply_ite, Pi.single_apply]
  have h𝔪 : ↑(ϑ.normQ * D.M ^ 2) ∈ 𝔪.ideal := normQ_mul_M_pow_mem_modulus
  -- The kernels: `k₀`, `k₁` with their constants, and `θ w` as a linear map on polynomials.
  let k₀ (v : Gf D.E (Fin D.m)) (w : Gf D.E D.CarrierIndex) : ℂ :=
    c₀ * modKernelStdSpace (stdSpace D.E (Fin D.m)) (twistedChiMPow ϑ j) 1 (unitModulus D.E) 1 1
      (1, v)
      w
  let k₁ : ℂ := c₁ * modKernelStdSpace (stdSpace D.E (Fin j)) 1 b' 𝔪 Ψ 1 (1, 1) h
  let θ (w : Gf D.E D.CarrierIndex) : MvPolynomial (D.Φ × FirstFactorIndex j × AddedIndex j) ℂ →ₗ[ℂ]
    ℂ :=
    modKernelBilin (stdSpace D.E (AddedIndex j)) (stdSpace D.E (FirstFactorIndex j))
      (firstFactorChar ϑ j)
      (firstFactorChar ϑ j) 𝔪 (1, U.blockSumOne (1, U.blockSumOne (i.classRep, w))) (1, h)
      (addedDatum ϑ j u)
  have hy : star (scale • leftSideSeries ϑ j (u, i) h) =
      (D.chosenGroupOrder ^ 2 : ℂ) •
        stdClassSum (stdLevel D.E D.CarrierIndex) fun w ↦
          stdClassSum (stdLevel D.E (Fin D.m)) fun v ↦
          star ((k₀ v w * conj k₁) • c₂ • θ w ∘ (H • stackedDetProdCoords j i (D.shortRows i))) :=
    h_expand c₀ c₁ c₂ H u i ϑ h
  rw [hy]
  refine ⟨fun p _ _ hp ↦ ?_, fun hQ_empty φ ↦ ?_⟩
  · -- Integrality of each term of the double class sum.
    refine weylGauge_stdClassSum_stdClassSum_le_one h fun w v ↦ ?_
    -- The vector is a complex conjugate, so its factors are read at the place ι = `ιₚ ∘ conj`.
    let ι : ℂ →+* ℂ_[p] := ιₚ.comp conj
    have int₀ : ‖ι (k₀ v w)‖ ≤ 1 :=
      let _ : PadicPlace p := ⟨ι⟩
      norm_mul_modKernelStdSpace_twistedChiMPow_le_one K₀ v w
    have int₁ : ‖ιₚ k₁‖ ≤ 1 := norm_mul_modKernelStdSpace_one_le_one K₁ hb' h𝔪 hΨ hp h
    have gauge₂ : weylGauge (untwistedDescentPair j).colsPlus 0 h
        (star (c₂ • θ w ∘ (H • stackedDetProdCoords j i (D.shortRows i)))) ≤ 1 := by
      refine weylGauge_modKernelBilin_stackedDetProdCoords_le_one j i _ c₂ H
        (fun g' hg' h' hh' Y hY l ↦ ?_) w h
      let _ : PadicPlace p := ⟨ι⟩
      exact K₂.norm_le_one hb hb h𝔪 (addedDatum_mem_integralAway j u · ϑ.normQ)
        (isHomogeneous_iff_aeval_smul_X.2 (h_denom i Y l).aeval_smul_X) hp hg' hh'
        ((h_denom i Y l).mem_range _ hY)
    rw [star_smul, weylGauge_smul]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans gauge₂
    simpa [ι] using (mul_le_of_le_one_left (norm_nonneg _) int₀).trans int₁
  · -- Size. With σ = φ ∘ conj, bound the σ-conjugates of the three kernels.
    let σ : ℂ ≃+* ℂ := starRingAut.trans φ
    have h_level : ϑ.normQ = 1 := by simp [hQ_empty]
    rw [h_level, one_mul] at h𝔪
    obtain ⟨hm, h_carrier, hj, h_first, h_added⟩ := card_le_gap j
    have size₀ (v : Gf D.E (Fin D.m)) (w : Gf D.E D.CarrierIndex) : ‖σ (k₀ v w)‖ ≤ rexp D.x₁ := by
      simpa [k₀] using K₀.norm_map_le hm h_carrier (Nat.zero_le _) (twistedChiMPow_hasWeight ϑ j)
        .one
        (𝔪 := unitModulus D.E) (Ψ := 1) (A := 1) (B := 1) Submodule.mem_top (by simp)
        (isHomogeneous_one _ _) σ (by simp) v w
    have size₁ : ‖σ (conj k₁)‖ ≤ rexp D.x₁ := by
      simpa [k₁] using K₁.norm_map_le hj h_first (Nat.zero_le _) .one hb' h𝔪 (Ψ := Ψ) (A := 1)
        (B := 1) (by simp [Ψ, apply_ite, ite_apply, Pi.single_apply]) (isHomogeneous_one _ _)
        (starRingAut.trans σ) (by simp) 1 h
    -- N bounds the datum `addedDatum`, and B the vector H·`stackedDetProdCoords` at small points.
    let N : ℕ := card (GL D.CarrierIndex (D.untwistedModulus 2).ResidueRing)
    let B : ℝ := √((H : ℝ) ^ 2 * (D.M ^ 9) ^ ((12 * D.m + 1) * q))
    -- By duality it is enough to bound the kernel at every Q that is small at the small points.
    refine weylNormSq_stdClassSum_stdClassSum_le rfl hn hn_le_M H_pos H_le φ fun w v ↦
      sqrt_weylNormSq_comp_le_of_eval_le σ ((k₀ v w * conj k₁) • c₂ • θ w)
        (S := {z | ∀ x, ‖σ (z x)‖ ≤ D.M ^ 4})
        (fun l ↦ isHomogeneous_iff_aeval_smul_X.2 (h_denom i (D.shortRows i) l).aeval_smul_X)
        (fun z hz ↦ sqrt_weylNormSq_smul_eval_stackedDetProdCoords_le j i h_detCount H σ hz)
        fun Q hQ_hom hQ_le ↦ ?_
    have size₂ : ‖σ (c₂ * θ w Q)‖ ≤ rexp D.x₁ * N * B :=
      K₂.norm_map_le h_added h_first hn_le_M hb hb h𝔪 (norm_map_addedDatum_le j u) hQ_hom σ hQ_le
        _ h
    simpa [mul_assoc] using norm_mul_le_of_le (norm_mul_le_of_le (size₀ v w) size₁) size₂

end New.Data

end
