import Lib.GLn.SchurModule.MinorBasis
import Lib.General.Groups.CongruenceSubgroups

/-!
# Schur matrices, the standard basis of ∇, its weights and the highest vector

Polynomials are taken in the entries of an array y with rows (τ, a). Here κ_τ(h) is the number of
columns of height h at the place τ; `New.rankAt n τ` = |n_τ|, and
λ = `New.diagramWeight (rankAt n) κ` has λ(τ, k) = Σ_{k<h<|n_τ|} κ_τ(h). The products
b_i = `New.nablaBasis` of minors of y along standard fillings form a basis of the module
∇ = `New.nablaFamily` of Borel semi-invariants. The Schur matrix S_κ(z) = `New.schur κ z` of a
family of matrices z_τ records the expansion of b'_i(zy); for square z this gives a polynomial
representation of ∏_τ GL(n_τ), which `New.weylRep` twists by integer powers of determinants. For one
place and a one-row shape, S_κ over ℂ is a symmetric power, and, over a topological ring, S_κ(z) is
continuous in z for square z.

## Main definitions and results

* `New.linearIndependent_nablaBasis`, `New.range_nablaCombination`: the b_i form a basis of ∇ over
  every commutative ring.
* `New.sum_schur_smul_nablaBasis`, `New.GL.schur_eq_of_expansion`: row i of S_κ(z) is characterised
  by the expansion of b'_i(zy) in the products b_j(y) ∏_τ det(y_τ)^{d_τ}, with
  d = `New.schurDetExp`.
* `New.schur_map`, `New.schur_mul_left`, `New.schur_mul_right`, `New.schur_apply_eq_prod`: base
  change, multiplicativity, and the product over the places τ.
* `New.schur_diagonal`, `New.weyl_character`: diagonal matrices and Weyl's character formula.
* `New.weylRep κ e` is the matrix representation of `∏ τ, GL (n τ) R` of weight `(κ, e)`: the Schur
  matrix `New.schur κ g` twisted by the powers `det (g τ) ^ e τ`, with integer exponents `e τ`.
* `New.map_nablaBasis_eq_map_weylKernel_mul_weylEval`: fix enumerations e_τ of the rows. Let φ be a
  linear form with φ(b_i) ≠ 0 only if λ(τ, e_τ(a)) ≤ `New.tableauWeight` i τ a for every row (τ, a).
  Then φ(b_i) = φ(k)·b_i(y). Here y is the permutation array of e (`New.permArray`), and k is the
  kernel `New.weylKernel` at y, a substitution (`New.rowSubst`) of the product `New.highestPoly` of
  leading minors, with value k(y) = 1. So on the span of the b_i, φ is determined by its value on k.

Notions from other files:
* `New.schur`: The Schur matrix S_κ(z) of matrices z_τ of size n'_τ×n_τ. Row i holds chosen
  coordinates of b'_i(zy) in the family b_j(y)·∏_τ det(y_τ)^{d_τ}. Here b'_i and b_j are the
  standard basis polynomials in the rows n' and n, and d is given by `New.schurDetExp`.
* `New.rowSubst`: For matrices z_τ of size n'_τ×n_τ, the algebra homomorphism f ↦ f(zy) sending
  variable y_{(τ,b),i} to Σ_a z_τ(b,a) y_{(τ,a),i}.
* `New.WeylIndexFamily`: The type of families choosing, for each place τ, a filling in the chosen
  standard set with rows n_τ, heights below |n_τ| and multiplicities κ_τ.
* `New.schurDetExp`: The natural number κ_τ(|n_τ|) if |n_τ| < |n'_τ|, and 0 otherwise, as a function
  of the place τ.
* `New.FitsRanks`: For row families n and n', the condition, at every place τ, that |n_τ| ≤ |n'_τ|
  and κ_τ(h) = 0 for |n_τ| < h < |n'_τ|.
* `New.detPow`: The product over places τ of the determinant of the variables in all rows of block τ
  (fixed enumeration) and first |n_τ| columns, raised to e_τ.

## Relation to the literature

Known; see `Lib.GLn.SchurModule.MinorBasis` for sources.
-/

/-!
## The standard basis of ∇ and Schur matrices

Rectangular z_τ, of size n'_τ × n_τ, are allowed under the condition `New.FitsRanks`.
-/

namespace New

open MvPolynomial Finset Matrix «GL» Submodule Equiv Fintype Function Sigma

variable {Φ : Type}
  {R S F : Type _} [CommRing R] [CommRing S] [Fintype Φ]
  {n n' : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)]
  [∀ τ : Φ, Fintype (n' τ)] [∀ τ : Φ, DecidableEq (n' τ)] {κ : Φ → ℕ → ℕ}
  (e : Φ → ℕ) (g : ∀ τ : Φ, Matrix (n τ) (n τ) R) (x : ∀ τ : Φ, n τ → R)

/-! ### The standard basis of ∇ -/

omit [∀ τ : Φ, Fintype (n' τ)] [∀ τ : Φ, DecidableEq (n' τ)] in
/-- For each place τ, let `T τ` be a filling with entries in `n' τ` that has `κ τ h` columns of
height `h` for each `h < M τ`. Take the product over τ of the minor products of `T τ`, taken in the
rows (τ, ·). This product lies in `nabla R Sigma.fst (diagramWeight M κ)`. That is, with rows
coloured by τ, it satisfies f(yβ) = ∏ β_{τ,ii}^{l(τ,i)} f(y) for upper triangular β_τ, where l(τ, i)
is the sum of `κ τ h` over i < h < M τ. -/
lemma prod_tableauPoly_mem_nabla [DecidableEq Φ]
    {M : Φ → ℕ} {T : ∀ τ : Φ, Tableau (n' τ) (M τ) (κ τ)} :
    ∏ τ : Φ, tableauPoly R (Sigma.mk τ) (T τ) ∈ nabla R Sigma.fst (diagramWeight M κ) := by
  -- The product is the product `minorProduct` of the minors over all columns of all colours.
  let I : ColouredTableau (J := Σ τ : Φ, Σ h : Fin (M τ), Fin (κ τ h)) fst (fun j ↦ j.fst)
      (fun j ↦ j.snd.fst) :=
    fun j s ↦ ⟨⟨j.fst, T j.fst j.snd.fst j.snd.snd s⟩, rfl⟩
  have h_prod : minorProduct R I = ∏ τ : Φ, tableauPoly R (Sigma.mk τ) (T τ) := by
    simp [I, tableauPoly, minor, minorProduct, Fintype.prod_sigma]
  rw [← h_prod, diagramWeight_eq_columnWeight]
  exact minorProduct_mem_nabla I

/-- Let ι be a finite alphabet and fix a shape with `k h` columns of height h for each h < M. A
filling (`New.Tableau ι M k`) assigns to each column an h-tuple in ι, with no ordering condition.
Some finite set s of fillings satisfies two conditions: (a) over every commutative ring, the minor
products of the fillings in s form a basis of the span of all minor products; (b) for every
enumeration e of ι and every x : ι → ℂ, (Σ_{T∈s} x^T)·a_0(x) = a_λ(x), where x^T is the product of x
over the entries of T, a is the alternant `New.GL.alternant`, and λ(i) = Σ_{i<h<M} k(h). -/
lemma exists_isTableauBasis {ι : Type} [Fintype ι] {M : ℕ} {k : ℕ → ℕ} :
    ∃ s : Finset (Tableau ι M k), IsTableauBasis s := by
  classical
  -- `exists_isStdMinorFamily`, with one colour and `k h` columns of each height `h`, gives a
  -- standard family `I` of fillings: its minor products are independent and span `nabla` over
  -- every ring and satisfy the character formula. Read it as a set of fillings.
  let J : Type := Σ _ : Unit, Σ h : Fin M, Fin (k h)
  obtain ⟨ι', h_fintype, I, hI⟩ :=
    exists_isStdMinorFamily (J := J) (m := ι) 0 fst (fun j ↦ j.snd.fst)
  let fill (i : ι') : Tableau ι M k := fun h j s ↦ I i ⟨(), h, j⟩ s
  have h_prod (R : Type) [CommRing R] : tableauPoly R id ∘ fill = fun i ↦ minorProduct R (I i) :=
    funext fun i ↦ by simp [fill, J, tableauPoly, minorProduct, Fintype.prod_sigma]
  have h_indep (R : Type) [CommRing R] : LinearIndependent R (tableauPoly R id ∘ fill) := by
    rw [h_prod R]
    exact hI.linearIndependent R
  -- Independent vectors are distinct, so distinct indices give distinct fillings.
  have fill_inj : Injective fill := .of_comp (h_indep ℤ).injective
  refine ⟨univ.map ⟨fill, fill_inj⟩,
    .of_linearIndepOn_of_mem_span_of_character (fun R _ ↦ ?_) (fun R _ T ↦ ?_) ?_⟩
  · simpa using (linearIndepOn_univ_iff.mpr (h_indep R)).image_of_comp
  · -- The minor product of any filling `T` lies in `nabla` for this weight, so in the span.
    let cols_T : ColouredTableau (J := J) 0 fst (fun j ↦ j.snd.fst) :=
      fun j s ↦ ⟨T j.snd.fst j.snd.snd s, rfl⟩
    have h_tableau : tableauPoly R id T = minorProduct R cols_T := by
      simp [tableauPoly, minorProduct, cols_T, J, Fintype.prod_sigma]
    rw [h_tableau]
    simpa [← Set.range_comp, h_prod] using
      hI.nabla_le_span R (minorProduct_mem_nabla cols_T)
  · simpa [fill, J, Fintype.prod_sigma, ← diagramWeight_eq_columnWeight, diagramWeight_apply] using
      hI.character ()

/-- Over a finite alphabet `ι`, consider the set of fillings chosen by `Classical.epsilon` (heights
below `M`, `k h` columns of height `h`), which is the set behind `BasisTableau`. This set is a
standard set: (a) over every commutative ring its minor products form a basis of the span of all
minor products; (b) for every enumeration of the rows and every x : ι → ℂ, (Σ_{T∈s} x^T)
a_0(x) = a_λ(x). Here x^T is the product of x over the entries of T, a is the alternant, and λ(i) is
the sum of k(h) over i < h < M.

A weaker form of the standard basis theorem for products of minors. The basis is chosen abstractly,
not described by standard tableaux. -/
lemma isTableauBasis_epsilon {ι : Type} [Fintype ι] {M : ℕ} {k : ℕ → ℕ} :
    IsTableauBasis (Classical.epsilon IsTableauBasis : Finset (Tableau ι M k)) :=
  Classical.epsilon_spec exists_isTableauBasis

/-- The minor products of the chosen fillings `New.BasisTableau` are linearly independent over
every ring. -/
lemma linearIndependent_basisTableau {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ} {k : ℕ → ℕ}
    (R : Type) [CommRing R] :
    LinearIndependent R fun T : BasisTableau ι M k ↦ tableauPoly R id T.val := by
  -- `BasisTableau ι M k` is the subtype of the members of the chosen set.
  exact (isTableauBasis_epsilon (ι := ι) (M := M) (k := k)).linearIndepOn R

/-- The minor product of any filling is a linear combination of those of the standard fillings. -/
lemma exists_sum_basisTableau_smul_eq {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ} {k : ℕ → ℕ}
    (R : Type) [CommRing R] (T : Tableau ι M k) :
    ∃ c : BasisTableau ι M k → R,
      ∑ U : BasisTableau ι M k, c U • tableauPoly R id U.val = tableauPoly R id T := by
  -- The chosen set of fillings spans all minor products.
  exact (mem_span_image_finset_iff_exists_fun R).mp (isTableauBasis_epsilon.mem_span R T)

/-- The character formula for the standard fillings: the sum of their monomials, times the
alternant of weight zero, is the alternant of the weight whose `i`-th entry counts the columns of
height greater than `i`. -/
lemma sum_basisTableau_mul_alternant {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ} {k : ℕ → ℕ}
    {a : ℕ} (e : Fin a ≃ ι) (x : ι → ℂ) :
    (∑ T : BasisTableau ι M k, ∏ h : Fin M, ∏ j : Fin (k h), ∏ s : Fin h, x (T.val h j s)) *
        alternant (x ∘ e) 0 =
      alternant (x ∘ e) fun i : ℕ ↦ ∑ h ∈ Finset.Ioo i M, k h := by
  -- Read the sum over the subtype as a sum over the chosen set of fillings.
  have h_sum :
      ∑ T : BasisTableau ι M k, ∏ h : Fin M, ∏ j : Fin (k h), ∏ s : Fin h, x (T.val h j s) =
        ∑ T ∈ Classical.epsilon IsTableauBasis,
          ∏ h : Fin M, ∏ j : Fin (k h), ∏ s : Fin h, x (T h j s) :=
    sum_coe_sort _ fun T : Tableau ι M k ↦ ∏ h : Fin M, ∏ j : Fin (k h), ∏ s : Fin h, x (T h j s)
  rw [h_sum]
  exact isTableauBasis_epsilon.weyl_character_formula a e x

/-- Over any commutative ring `R`, the polynomials `nablaBasis R n κ` are linearly independent. For
a family `i` of chosen standard fillings, `nablaBasis R n κ i` is the product over places `τ` of the
minor product of `i τ` in the rows of block `τ`.

Part of the standard basis theorem for Schur (dual Weyl) modules over any ring. -/
lemma linearIndependent_nablaBasis [DecidableEq Φ] : LinearIndependent R (nablaBasis R n κ) := by
  -- Induction on the number of places. Single out a place `τ` and view polynomials in all rows as
  -- polynomials in the rows of the other places, over the polynomials in the rows of `τ`; then a
  -- basis product is a scalar (its factor at `τ`) times a basis product for the other places.
  induction hk : card Φ using Nat.strongRec generalizing Φ R with | ind k ih => ?_
  rcases isEmpty_or_nonempty Φ with hΦ | ⟨⟨τ⟩⟩
  · -- With no place there is a single, empty product, equal to `1`.
    exact .of_subsingleton' default fun r h_zero ↦ by
      simpa [nablaBasis, univ_eq_empty, ← C_mul'] using h_zero
  let P : Type := MatrixPoly (n τ) R
  let split : MatrixPoly (Σ σ, n σ) R →ₐ[R] MatrixPoly (Σ σ : {σ // σ ≠ τ}, n σ) P :=
    aeval fun (⟨σ, a⟩, j) ↦
      if hσ : σ = τ then C (X ⟨cast (congrArg n hσ) a, j⟩) else X ⟨⟨⟨σ, hσ⟩, a⟩, j⟩
  -- The factors at `τ` are independent over `R` by the choice of the standard set, the products
  -- over the other places are independent over the larger ring by induction.
  have h_card_lt : card {σ : Φ // σ ≠ τ} < k :=
    (card_subtype_lt (x := τ) fun h_ne ↦ h_ne rfl).trans_eq hk
  have h_rest : LinearIndependent P (nablaBasis P (fun σ : {σ : Φ // σ ≠ τ} ↦ n σ) fun σ ↦ κ σ) :=
    ih _ h_card_lt rfl
  -- `split` carries each basis product to the corresponding product of the two families.
  have h_split (i : WeylIndexFamily n κ) :
      split (nablaBasis R n κ i) =
        (tableauPoly R id (i τ).val : P) •
          nablaBasis P (fun σ : {σ : Φ // σ ≠ τ} ↦ n σ) (fun σ ↦ κ σ) (fun σ ↦ i σ) := by
    have h_ne (σ : {σ : Φ // σ ≠ τ}) : (σ : Φ) ≠ τ := σ.prop
    simp [P, split, nablaBasis, prod_eq_mul_prod_subtype_ne _ τ, h_ne, tableauPoly, minor, ← C_mul',
      RingHom.map_det, Matrix.map, AlgHom.map_det]
  have h_one :
      LinearIndependent R fun T : BasisTableau (n τ) (rankAt n τ) (κ τ) ↦ tableauPoly R id T.val :=
    linearIndependent_basisTableau R
  refine .of_comp split.toLinearMap
    ((linearIndependent_equiv' (piSplitAt τ _) ?_).mpr (linearIndependent_smul h_one h_rest))
  funext i
  exact (h_split i).symm

omit [∀ τ : Φ, DecidableEq (n τ)] in
/-- Over any commutative ring, the polynomial ∏_τ det(y_τ)^{e_τ} is a regular element (not a
zero divisor) of the polynomial ring. -/
lemma isRegular_detPow {e : Φ → ℕ} : IsRegular (detPow R n e) := by
  -- The involution `y ↦ 1 - y` of the polynomial ring (`1` the array of identity matrices) gives
  -- the product of determinants the constant term `1`, so that its image in the power series
  -- ring is not a zero divisor.
  let reflect : MatrixPoly (Σ τ, n τ) R →ₐ[R] MatrixPoly (Σ τ, n τ) R :=
    bind₁ (permArray (fun τ a ↦ rowEquivFin n τ a) - X)
  have h_reflect : Involutive reflect := fun f ↦ by simp [reflect, bind₁_bind₁, permArray]
  have h_inj : Injective ((coeToMvPowerSeries.algHom R).comp reflect) :=
    (coe_injective _ R).comp h_reflect.injective
  rw [isRegular_iff_mem_nonZeroDivisors]
  refine mem_nonZeroDivisors_of_injective h_inj
    (MvPowerSeries.mem_nonZeroDivisors_of_constantCoeff ?_)
  -- The constant coefficient of the image is `1`.
  simp [reflect, map_pow, map_sub, detPow, minor, AlgHom.map_det, Matrix.map, permArray,
    ← Fin.ext_iff, RingHom.map_det, ← diagonal.eq_1]

omit [Fintype Φ]
  [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, Fintype (n' τ)] [∀ τ : Φ, DecidableEq (n' τ)] in
/-- For I a tuple of |n_τ| rows of n'_τ, the substitution y ↦ zy sends the minor on rows I
(determinant of the variables in rows (τ, I a) and columns 0, …, |n_τ|−1) to det(z_τ[I, ·]) times
the minor on the rows of n_τ, both taken in the fixed enumeration `New.GL.rowEquivFin n τ` of
n_τ. -/
lemma GL.rowSubst_minor (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R) (τ : Φ)
    (I : Fin (Fintype.card (n τ)) → n' τ) :
    rowSubst z (minor R fun a : Fin (Fintype.card (n τ)) ↦ ⟨τ, I a⟩) =
      det ((z τ).submatrix I (rowEquivFin n τ).symm) •
        minor R fun a : Fin (Fintype.card (n τ)) ↦ ⟨τ, (rowEquivFin n τ).symm a⟩ := by
  -- The substitution multiplies the matrix of variables on the left by the rows `I` of `z τ`.
  simp [rowSubst, reindex_equiv (rowEquivFin n τ).symm, ← C_mul', minor, AlgHom.map_det, Matrix.map,
    RingHom.map_det, ← det_mul]
  -- Both sides are the determinant of the same matrix: once entrywise, once as a product.
  show (of fun (a b : Fin (Fintype.card (n τ))) ↦ ∑ c : Fin (Fintype.card (n τ)),
        C (z τ (I a) ((rowEquivFin n τ).symm c)) *
          X ((⟨τ, (rowEquivFin n τ).symm c⟩ : Σ σ : Φ, n σ), (b : ℕ))).det =
      ((of fun (a c : Fin (Fintype.card (n τ))) ↦ C (z τ (I a) ((rowEquivFin n τ).symm c))) *
        of fun (c b : Fin (Fintype.card (n τ))) ↦
          X ((⟨τ, (rowEquivFin n τ).symm c⟩ : Σ σ : Φ, n σ), (b : ℕ))).det
  refine congrArg det (Matrix.ext fun a b ↦ ?_)
  rw [Matrix.mul_apply]
  simp

/-- Substituting y ↦ g y, for square matrices g_τ of size n_τ, multiplies the product
∏_τ det(y_τ)^{e_τ} of determinants by the scalar ∏_τ det(g_τ)^{e_τ}. -/
@[simp]
lemma rowSubst_detPow : rowSubst g (detPow R n e) = (∏ τ : Φ, (g τ).det ^ e τ) • detPow R n e := by
  simp [rowSubst_minor, mul_pow, detPow, ← C_mul', prod_mul_distrib]

variable [DecidableEq Φ]

/-- Consider polynomials over `R` in a matrix of variables whose rows, indexed by pairs (τ, row of
`n τ`), are coloured by the place τ. Let f be a Borel semi-invariant (`nabla`) whose weight is
`diagramWeight (rankAt n) κ` plus `e τ` at each column i < |n τ| of each place τ, i.e. the weight of
`κ` with `e τ` further full-height columns at τ. Then f is an `R`-linear combination of the products
`nablaBasis R n κ U * detPow R n e` over `U : WeylIndexFamily n κ`, where `detPow` is the product
over τ of the `e τ`-th powers of the determinants of the block-τ variables in the first |n τ|
columns. -/
lemma nabla_le_span_nablaBasis_mul_detPow (e : Φ → ℕ) :
    nabla R Sigma.fst (diagramWeight (rankAt n) κ +
        ∑ τ : Φ, e τ • ∑ i ∈ range (rankAt n τ), Finsupp.single (τ, i) 1) ≤
      (Fintype.linearCombination R fun U : WeylIndexFamily n κ ↦
        nablaBasis R n κ U * detPow R n e).range := by
  -- The weight is that of the columns of `κ` together with `e τ` further columns of full height at
  -- each `τ`, so the module lies in a span of products of minors on these columns. In a product
  -- the minors on the columns of `κ` expand in the standard ones, and a minor of full height is a
  -- multiple of the determinant.
  let J : Type := (Σ τ : Φ, Σ h : Fin (rankAt n τ), Fin (κ τ h)) ⊕ Σ τ : Φ, Fin (e τ)
  let colour : J → Φ := Sigma.fst ⊕ᵥ Sigma.fst
  let height : J → ℕ := (fun j ↦ j.snd.fst) ⊕ᵥ fun j ↦ rankAt n j.fst
  have h_weight : columnWeight colour height =
      diagramWeight (rankAt n) κ +
        ∑ τ : Φ, e τ • ∑ i ∈ range (rankAt n τ), Finsupp.single (τ, i) 1 := by
    simp_rw [← Fin.sum_const, ← Fintype.sum_sigma', diagramWeight_eq_columnWeight]
    exact sum_sum_type _
  obtain ⟨ι, h_fintype, I, hI⟩ : ∃ (ι : Type) (_ : Fintype ι)
      (I : ι → ColouredTableau (fst : (Σ τ : Φ, n τ) → Φ) colour height), IsStdMinorFamily I :=
    exists_isStdMinorFamily (m := Σ τ : Φ, n τ) fst colour height
  rw [← h_weight]
  refine (hI.nabla_le_span R).trans ?_
  rw [span_le, Set.range_subset_iff]
  intro i
  -- The entries of the filling `I i` are the rows `⟨colour j, T j s⟩`.
  have h_rows (j : J) (s : Fin (height j)) :
      ∃ a : n (colour j), (sigmaSubtype (colour j)).symm a = I i j s :=
    (sigmaSubtype (colour j)).symm.surjective (I i j s)
  choose T hT using h_rows
  have h_expand (τ : Φ) : ∃ a : BasisTableau (n τ) (rankAt n τ) (κ τ) → R,
      ∑ U : BasisTableau (n τ) (rankAt n τ) (κ τ), a U • tableauPoly R id U.val =
        tableauPoly R id fun h j ↦ T (.inl ⟨τ, h, j⟩) :=
    exists_sum_basisTableau_smul_eq R _
  choose a ha using h_expand
  -- A minor of full height is a multiple of the determinant (`rowSubst_minor` with `z = 1`).
  have h_full (j : Σ τ : Φ, Fin (e τ)) : ∃ b_j : R,
      (minor R fun s ↦ (⟨j.fst, T (.inr j) s⟩ : Σ τ : Φ, n τ)) =
        b_j • minor R fun s ↦ (⟨j.fst, (rowEquivFin n j.fst).symm s⟩ : Σ τ : Φ, n τ) :=
    by
    refine ⟨det ((1 : Matrix (n j.fst) (n j.fst) R).submatrix (T (.inr j))
      (rowEquivFin n j.fst).symm), ?_⟩
    exact (rowSubst_one _).symm.trans (rowSubst_minor (R := R) (fun _ ↦ 1) j.fst (T (.inr j)))
  choose b hb using h_full
  -- Multiply all these expansions together.
  rw [← funext₂ hT]
  refine ⟨fun U ↦ (∏ j, b j) * ∏ τ, a τ (U τ), ?_⟩
  have h_prod :
      (∏ τ : Φ, rename (Prod.map (Sigma.mk τ) id)
          (∑ U : BasisTableau (n τ) (rankAt n τ) (κ τ), a τ U • tableauPoly R id U.val)) *
          ∏ j : Σ τ : Φ, Fin (e τ),
            b j • minor R (fun s ↦ (⟨j.fst, (rowEquivFin n j.fst).symm s⟩ : Σ τ : Φ, n τ)) =
        (∏ τ : Φ, rename (Prod.map (Sigma.mk τ) id)
          (tableauPoly R id fun h j ↦ T (.inl ⟨τ, h, j⟩))) *
          ∏ j : Σ τ : Φ, Fin (e τ), minor R fun s ↦ (⟨j.fst, T (.inr j) s⟩ : Σ τ : Φ, n τ) := by
    simp only [ha, hb]
  -- The rows of the filling, as elements of the sigma type.
  have h_entry (τ : Φ) (t : n τ) : ((sigmaSubtype τ).symm t : Σ σ : Φ, n σ) = ⟨τ, t⟩ := rfl
  -- The left side of `h_prod` is the combination of the `nablaBasis R n κ U * detPow R n e` with
  -- the coefficients above, the right side the minor product of the filling, after unfolding `J`.
  -- `using!`: after simp the two sides differ only by `(id ∘ T j) s` against `T j s` inside a
  -- dependent pair, where simp does not rewrite.
  simpa [linearCombination_apply, ← Fin.prod_const, -prod_const, J, colour, height,
    nablaBasis, h_entry, rowEquivFin, minor, AlgHom.map_det, Matrix.map, detPow, Fintype.prod_sigma,
    minorProduct, tableauPoly, prod_univ_sum, prod_smul, sum_mul, smul_sum,
    ← mul_smul] using! h_prod

/-- The map `New.GL.nablaCombination` κ, which sends coefficients to the linear combination of the
basis minor products b_i, is injective. -/
lemma GL.nablaCombination_injective : Injective (nablaCombination (R := R) (n := n) κ) :=
  linearIndependent_nablaBasis.fintypeLinearCombination_injective

/-- The R-linear map `nablaCombination κ`, sending ξ to Σ_i ξ_i b_i with b_i the basis products of
minors `nablaBasis` (indexed by families of chosen standard fillings), has range exactly
`nablaFamily R n κ`. That is the module of Borel semi-invariant polynomials in rows (τ,a), coloured
by τ, whose weight is the partition tuple built from κ using heights below |n_τ|, over any
commutative ring R. -/
lemma range_nablaCombination : (nablaCombination κ).range = nablaFamily R n κ := by
  -- The basis products lie in `∇` (`prod_tableauPoly_mem_nabla`), and
  -- `nabla_le_span_nablaBasis_mul_detPow` with `e = 0` is the converse.
  refine le_antisymm ?_ ?_
  · rw [nablaCombination, Fintype.range_linearCombination, span_le, Set.range_subset_iff]
    exact fun i ↦ prod_tableauPoly_mem_nabla
  · -- For `e = 0` the extra weight is `0` and `detPow R n 0 = 1`.
    simpa [nablaFamily, nablaCombination] using
      nabla_le_span_nablaBasis_mul_detPow (R := R) (n := n) (κ := κ) 0

/-- For f in ∇ = `New.nablaFamily`, the coordinates chosen by `invFun` of the linear combination map
`New.GL.nablaCombination` give back f as a combination of the basis products b_i. -/
lemma sum_coords_nablaBasis {f : MatrixPoly (Sigma n) R} (hf : f ∈ nablaFamily R n κ) :
    ∑ i : WeylIndexFamily n κ, invFun (nablaCombination κ) f i • nablaBasis R n κ i = f :=
  invFun_eq (range_nablaCombination.ge hf)

/-- Over any commutative ring R and for any exponents e_τ, the polynomials b_i · ∏_τ
det(y_τ)^{e_τ}, with b_i the basis minor products for κ, are linearly independent over R. -/
lemma GL.linearIndependent_nablaBasis_mul_detPow :
    LinearIndependent R fun i : WeylIndexFamily n κ ↦ nablaBasis R n κ i * detPow R n e :=
  linearIndependent_nablaBasis.map_injOn (LinearMap.mulRight R (detPow R n e))
    isRegular_detPow.right.injOn

/-- If all coefficients of a combination of the basis products times `detPow R n e` lie in an
additive subgroup `A` of `R`, then so do the coordinates of the combination.

A consequence of the standard basis theorem for products of minors, stated for membership in an
additive subgroup A and with a determinant-power factor. -/
lemma GL.coord_mem_of_coeff_mem (A : AddSubgroup R) (e : Φ → ℕ) {f : MatrixPoly (Σ τ : Φ, n τ) R}
    {x : WeylIndexFamily n κ → R}
    (h_sum : ∑ j : WeylIndexFamily n κ, x j • (nablaBasis R n κ j * detPow R n e) = f)
    (h_coeff : ∀ d : (Σ τ : Φ, n τ) × ℕ →₀ ℕ, f.coeff d ∈ A) (i : WeylIndexFamily n κ) :
      x i ∈ A := by
  -- `A` need not be an ideal, so pass to the ring `Q = ℤ ⊕ R ⧸ A` with `(R ⧸ A)² = 0`. The products
  -- have integer coefficients and stay independent over `Q`, and the classes of the `x j` form a
  -- linear relation among them.
  have h_int (S : Type) [CommRing S] (j : WeylIndexFamily n κ) (d : (Σ τ, n τ) × ℕ →₀ ℕ) :
      (nablaBasis S n κ j * detPow S n e).coeff d =
        ((nablaBasis ℤ n κ j * detPow ℤ n e).coeff d : ℤ) := by
    simpa using (nablaBasis ℤ n κ j * detPow ℤ n e).coeff_map (algebraMap ℤ S) d
  let Q : Type := TrivSqZeroExt ℤᵐᵒᵖ (TensorProduct ℤ ℤᵐᵒᵖ (R ⧸ A))
  let φ : R ⧸ A → Q := TrivSqZeroExt.inrHom ℤᵐᵒᵖ _ ∘ TensorProduct.mk ℤ ℤᵐᵒᵖ (R ⧸ A) 1
  have h_rel : ∑ j, φ (x j) • (nablaBasis Q n κ j * detPow Q n e) = 0 := by
    ext1 d
    -- The class of `f.coeff d` in `R ⧸ A` is zero; expand `f` by `h_sum` and apply `φ`.
    have h_class : ((f.coeff d : R) : R ⧸ A) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr (h_coeff d)
    simpa [φ, Q, ← h_sum, coeff_sum, h_int R, h_int Q, ← zsmul_eq_mul'] using congrArg φ h_class
  have h_zero : φ (x i) = 0 :=
    linearIndependent_iff.mp (linearIndependent_nablaBasis_mul_detPow e) (fun j ↦ φ (x j)) h_rel i
  -- `φ` is injective: its value at `x i` is zero only if the class of `x i` is.
  have h_class_zero : ((x i : R) : R ⧸ A) = 0 := by simpa [φ, Q, TrivSqZeroExt.ext_iff] using h_zero
  exact (QuotientAddGroup.eq_zero_iff _).mp h_class_zero

/-! ### Characterisation of Schur matrices and diagonal matrices -/

omit [Fintype Φ] [DecidableEq Φ] [∀ τ : Φ, DecidableEq (n τ)] in
/-- A family of row types fits itself: no height lies strictly between |n_τ| and |n_τ|. -/
@[simp]
lemma FitsRanks.refl : FitsRanks n n κ := by grind

omit [Fintype Φ] [DecidableEq Φ] [∀ τ : Φ, DecidableEq (n τ)] in
/-- For equal row families no extra power of the determinants occurs. -/
@[simp]
lemma schurDetExp_self : schurDetExp n n κ = 0 := funext (by simp [schurDetExp])

/-- Let M be a matrix whose row i gives coordinates of b'_i(zy) in the family
b_j(y)·∏_τ det(y_τ)^{d_τ}, with b, b' the basis products `New.nablaBasis` for the rows n and n' and
d = `New.schurDetExp`. Then M is the Schur matrix S_κ(z): the family is linearly independent, so
these coordinates are unique. -/
lemma GL.schur_eq_of_expansion {M : Matrix (WeylIndexFamily n' κ) (WeylIndexFamily n κ) R}
    {z : ∀ τ : Φ, Matrix (n' τ) (n τ) R}
    (h_expand : ∀ i : WeylIndexFamily n' κ,
      ∑ j : WeylIndexFamily n κ, M i j • (nablaBasis R n κ j * detPow R n (schurDetExp n n' κ)) =
        rowSubst z (nablaBasis R n' κ i)) :
    schur κ z = M := by
  -- Row `i` of either matrix holds coordinates of the same polynomial in an independent family.
  funext i
  apply (linearIndependent_nablaBasis_mul_detPow _).fintypeLinearCombination_injective
  exact (sum_schur_smul_eq_rowSubst_of_exists κ z i ⟨M i, h_expand i⟩).trans (h_expand i).symm

/-- The Schur matrix of diagonal matrices diag(x_τ) is diagonal; its entry at i is the product of
x_τ over all entries of the fillings i_τ. -/
@[local simp]
lemma schur_diagonal_eq_prod :
    schur κ (fun τ : Φ ↦ diagonal (x τ)) =
      diagonal fun i : WeylIndexFamily n κ ↦
        ∏ τ : Φ, ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ τ h), ∏ s : Fin h, x τ ((i τ).val h j s) := by
  -- Each minor of `b_i` is multiplied by the product of the `x` over its rows, and the
  -- determinant factor is trivial.
  refine schur_eq_of_expansion fun i ↦ ?_
  simp [diagonal, nablaBasis, rowSubst, ← prod_mul_distrib, tableauPoly, minor, detPow, ← C_mul',
    ← det_mul_column, AlgHom.map_det, Matrix.map]

/-- Weyl's character formula over ℂ, for polynomial weights and with the Vandermonde denominator
cleared. Let e_τ enumerate the a_τ rows at each place τ, let x_τ be complex numbers indexed by these
rows, and let λ = `New.diagramWeight`, so λ(τ, k) = Σ_{k<h<|n_τ|} κ_τ(h). The trace of the Schur
matrix `schur κ` of the diagonal matrices diag(x_τ), times the product over τ of the Vandermonde
determinants of x_τ ∘ e_τ, is the product over τ of the determinants of the matrices with (i, j)
entry x_τ(e_τ(i))^{λ(τ, a_τ − 1 − j) + j}. -/
lemma weyl_character {a : Φ → ℕ} (e : ∀ τ : Φ, Fin (a τ) ≃ n τ) (x : ∀ τ : Φ, n τ → ℂ) :
    (schur κ fun τ : Φ ↦ Matrix.diagonal (x τ)).trace *
        ∏ τ : Φ, (vandermonde (x τ ∘ e τ)).det =
      ∏ τ : Φ, det (of fun i j : Fin (a τ) ↦
        x τ (e τ i) ^ (diagramWeight (rankAt n) κ (τ, j.rev) + j)) := by
  -- At each place the character identity is part of the choice of the standard set. By
  -- `schur_diagonal_eq_prod` the trace is the product over the places of the sums over these sets.
  have h_place (τ : Φ) :
      (∑ T : BasisTableau (n τ) (rankAt n τ) (κ τ),
          ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ τ h), ∏ s : Fin h, x τ (T.val h j s)) *
          (vandermonde (x τ ∘ e τ)).det =
        det (of fun i j : Fin (a τ) ↦
          x τ (e τ i) ^ (diagramWeight (rankAt n) κ (τ, j.rev) + j)) := by
    have h_card : a τ = rankAt n τ := by simpa using card_congr (e τ)
    -- The alternant of weight zero is the Vandermonde determinant, the other one that on the right.
    simpa [alternant, vandermonde, h_card, diagramWeight_apply] using
      sum_basisTableau_mul_alternant (M := rankAt n τ) (k := κ τ) (e τ) (x τ)
  have h_trace : (schur κ fun τ : Φ ↦ Matrix.diagonal (x τ)).trace =
      ∏ τ : Φ, ∑ T : BasisTableau (n τ) (rankAt n τ) (κ τ),
        ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ τ h), ∏ s : Fin h, x τ (T.val h j s) := by
    rw [schur_diagonal_eq_prod, trace_diagonal, Fintype.prod_sum]
  rw [h_trace, ← prod_mul_distrib]
  exact Finset.prod_congr rfl fun τ _ ↦ h_place τ

/-- The Schur matrix of a family of identity matrices is the identity matrix. -/
@[simp]
lemma schur_one (hg : ∀ τ : Φ, g τ = 1) : schur κ g = 1 := by
  -- With `g = 1` the substitution is the identity and there is no determinant factor.
  refine schur_eq_of_expansion fun i ↦ ?_
  simp [hg, rowSubst, Matrix.one_apply, detPow, minor]

/-- The Schur matrix of a tuple of diagonal matrices diag(x_τ) is diagonal, with i-th entry ∏_τ
∏_a x_τ(a)^{w}, where w is the number of entries equal to a in the filling i_τ. -/
lemma schur_diagonal :
    schur κ (fun τ : Φ ↦ Matrix.diagonal (x τ)) =
      Matrix.diagonal fun i : WeylIndexFamily n κ ↦
        ∏ τ : Φ, ∏ a : n τ, x τ a ^ tableauWeight i τ a := by
  -- (`sum_boole` is removed: it undoes `card_filter`)
  simp [tableauWeight, prod_comm (γ := n _), card_filter, -sum_boole, ← prod_pow_eq_pow_sum]

/-! ### Base change and multiplicativity -/

omit [DecidableEq Φ] [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, DecidableEq (n' τ)] in
/-- If the sizes fit κ, the weight of κ in the larger ranks is its weight in the smaller ranks plus
that of the power `schurDetExp n n' κ` of the determinants. -/
lemma GL.diagramWeight_eq_of_fitsRanks (h : FitsRanks n n' κ) :
    diagramWeight (rankAt n') κ =
      diagramWeight (rankAt n) κ +
        ∑ τ : Φ,
          schurDetExp n n' κ τ • ∑ i ∈ Finset.range (rankAt n τ), Finsupp.single ⟨τ, i⟩ 1 := by
  -- At `τ` the heights from `rankAt n τ` to `rankAt n' τ - 1` are new; by the hypothesis `h` only
  -- the height `rankAt n τ` can have columns, and `schurDetExp n n' κ τ` counts them.
  rw [diagramWeight, diagramWeight, ← sum_add_distrib]
  refine sum_congr rfl fun τ _ ↦ ?_
  obtain ⟨h_le, h_zero_between⟩ :
      rankAt n τ ≤ rankAt n' τ ∧ ∀ k ∈ Ioo (rankAt n τ) (rankAt n' τ), κ τ k = 0 := h τ
  grind [zero_smul, schurDetExp, sum_eq_ite (rankAt n τ), sum_range_add_sum_Ico _ h_le]

/-- Assume `FitsRanks n n' κ`: for every τ, |n_τ| ≤ |n'_τ| and κ_τ(h) = 0 for |n_τ| < h < |n'_τ|.
Let b = `nablaBasis` for `n`, b' = `nablaBasis` for `n'`, and let d τ be κ_τ(|n_τ|) if
|n_τ| < |n'_τ| and 0 otherwise. Then for matrices z_τ of size n'_τ × n_τ, row `i` of the Schur
matrix `schur κ z` expresses b'_i(zy) as Σ_j S_{ij} b_j(y) ∏_τ det(y_τ)^{d τ}, where
y_{(τ,b),k} ↦ Σ_a z_τ(b,a) y_{(τ,a),k} defines zy and y_τ is the block of rows (τ, ·) and the first
|n_τ| columns. -/
@[simp ← low] lemma sum_schur_smul_nablaBasis (h : FitsRanks n n' κ)
    (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R) (i : WeylIndexFamily n' κ) :
    ∑ j : WeylIndexFamily n κ, schur κ z i j •
      (nablaBasis R n κ j * detPow R n (schurDetExp n n' κ)) =
      rowSubst z (nablaBasis R n' κ i) := by
  -- The substituted polynomial is again semi-invariant, of the weight of the products on the left.
  have h_mem : rowSubst z (nablaBasis R n' κ i) ∈ nabla R Sigma.fst (diagramWeight (rankAt n) κ +
      ∑ τ : Φ, schurDetExp n n' κ τ • ∑ k ∈ range (rankAt n τ), Finsupp.single (τ, k) 1) := by
    rw [← diagramWeight_eq_of_fitsRanks h, nablaBasis]
    exact rowSubst_mem_nabla z prod_tableauPoly_mem_nabla
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (nabla_le_span_nablaBasis_mul_detPow _ h_mem)
  exact sum_schur_smul_eq_rowSubst_of_exists κ z i
    ⟨w, by simpa [Fintype.linearCombination_apply] using hw⟩

/-- Base change: assume `FitsRanks n n' κ`, that is, for every τ, |n_τ| ≤ |n'_τ| and κ_τ(h) = 0 for
|n_τ| < h < |n'_τ|. Then for a ring homomorphism φ, the Schur matrix of φ(z) (φ applied entrywise)
is φ applied entrywise to the Schur matrix S_κ(z). Here S_κ(z) = `schur κ z` has as row i the
coordinates of b'_i(zy) in the family b_j(y) ∏_τ det(y_τ)^{d τ}, where b and b' are the `nablaBasis`
for `n` and `n'`, and d = `schurDetExp n n' κ`. -/
@[simp ←]
lemma schur_map (h_fits : FitsRanks n n' κ) (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R)
    [FunLike F R S] [RingHomClass F R S] (φ : F) :
    schur κ (fun τ : Φ ↦ (z τ).map φ) = (schur κ z).map φ := by
  -- Apply `φ` to the coefficients in the expansion `sum_schur_smul_nablaBasis`.
  refine schur_eq_of_expansion fun i ↦ ?_
  simpa [rowSubst, map_bind₁, minor, ← C_mul', RingHom.map_det] using
    congrArg (MvPolynomial.map (φ : R →+* S)) (sum_schur_smul_nablaBasis h_fits z i)

/-- Entrywise form of `New.schur_map`: φ applied to an entry of S_κ(z) is the same entry of the
Schur matrix of the matrices with entries φ(z_τ(a, b)). -/
lemma map_schur (h_fits : FitsRanks n n' κ) (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R)
    [FunLike F R S] [RingHomClass F R S] (φ : F) (i : WeylIndexFamily n' κ)
      (j : WeylIndexFamily n κ) :
    φ (schur κ z i j) = schur κ (fun τ : Φ ↦ of fun (a : n' τ) (b : n τ) ↦ φ (z τ a b)) i j := by
  rw [← Matrix.map_apply (f := φ), ← schur_map h_fits z φ]
  rfl

/-- Assume `FitsRanks n n' κ`: at every place τ, |n_τ| ≤ |n'_τ| and κ_τ(h) = 0 for
|n_τ| < h < |n'_τ|. Let S_κ(z) = `schur κ z` be the matrix whose row i holds the coordinates of
b'_i(z y) in the family b_j(y)·∏_τ det(y_τ)^{d_τ}, where b and b' are `nablaBasis` for n and n', and
d is `schurDetExp`. Then S_κ(g z) = S_κ(g) S_κ(z) for square matrices g_τ of size n'_τ and matrices
z_τ of size n'_τ × n_τ over R. -/
@[simp ←]
lemma schur_mul_left (h_fits : FitsRanks n n' κ) (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R)
    (g : ∀ τ : Φ, Matrix (n' τ) (n' τ) R) :
    (schur κ fun τ : Φ ↦ g τ * z τ) = schur κ g * schur κ z := by
  -- Substitute `g`, then `z` (`rowSubst_rowSubst`), and expand both times by
  -- `sum_schur_smul_nablaBasis`.
  refine schur_eq_of_expansion fun i ↦ ?_
  -- `g` is square, so its expansion has no determinant factor.
  have h_expand_g : rowSubst g (nablaBasis R n' κ i) =
      ∑ k : WeylIndexFamily n' κ, schur κ g i k • nablaBasis R n' κ k := by
    rw [← sum_schur_smul_nablaBasis FitsRanks.refl g i]
    simp only [schurDetExp_self, detPow_zero, mul_one]
  calc ∑ j : WeylIndexFamily n κ, (schur κ g * schur κ z) i j •
          (nablaBasis R n κ j * detPow R n (schurDetExp n n' κ))
      = ∑ k : WeylIndexFamily n' κ, schur κ g i k • ∑ j : WeylIndexFamily n κ, schur κ z k j •
          (nablaBasis R n κ j * detPow R n (schurDetExp n n' κ)) := by
        simpa only [Matrix.mul_apply, sum_smul, smul_sum, mul_smul] using sum_comm
    _ = ∑ k : WeylIndexFamily n' κ, schur κ g i k • rowSubst z (nablaBasis R n' κ k) := by
        simp only [sum_schur_smul_nablaBasis h_fits z]
    _ = rowSubst z (rowSubst g (nablaBasis R n' κ i)) := by simp [h_expand_g]
    _ = rowSubst (fun τ : Φ ↦ g τ * z τ) (nablaBasis R n' κ i) := rowSubst_rowSubst ..

/-- Assume `FitsRanks n n' κ`: at every place τ, |n_τ| ≤ |n'_τ| and κ_τ(h) = 0 for
|n_τ| < h < |n'_τ|. Let S_κ(z) = `schur κ z` be the matrix whose row i holds the coordinates of
b'_i(z y) in the family b_j(y)·∏_τ det(y_τ)^{d_τ}, where b and b' are `nablaBasis` for n and n', and
d_τ = `schurDetExp n n' κ τ` is κ_τ(|n_τ|) if |n_τ| < |n'_τ| and 0 otherwise. Then S_κ(z g) = ∏_τ
det(g_τ)^{d_τ} · S_κ(z) S_κ(g) for z_τ of size n'_τ × n_τ and square g_τ of size n_τ over R. -/
lemma schur_mul_right (h_fits : FitsRanks n n' κ) (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R)
    (g : ∀ τ : Φ, Matrix (n τ) (n τ) R) :
    schur κ (fun τ : Φ ↦ z τ * g τ) =
      (∏ τ : Φ, (g τ).det ^ schurDetExp n n' κ τ) • (schur κ z * schur κ g) := by
  -- Substitute `z`, then `g`, and expand both times by `sum_schur_smul_nablaBasis`; `g` multiplies
  -- the power of the determinants in the first expansion by the scalar (`rowSubst_detPow`).
  refine schur_eq_of_expansion fun i ↦ ?_
  calc ∑ j : WeylIndexFamily n κ, ((∏ τ : Φ, (g τ).det ^ schurDetExp n n' κ τ) •
          (schur κ z * schur κ g)) i j • (nablaBasis R n κ j * detPow R n (schurDetExp n n' κ))
      = ∑ k : WeylIndexFamily n κ, schur κ z i k •
          rowSubst g (nablaBasis R n κ k * detPow R n (schurDetExp n n' κ)) := by
        simpa [mul_sum, mul_left_comm, Matrix.mul_apply, sum_smul, sum_mul, smul_sum,
          ← mul_smul] using sum_comm
    _ = rowSubst g (rowSubst z (nablaBasis R n' κ i)) := by
        simp only [← sum_schur_smul_nablaBasis h_fits z i, map_sum, map_smul]
    _ = rowSubst (fun τ : Φ ↦ z τ * g τ) (nablaBasis R n' κ i) := rowSubst_rowSubst ..

omit [Fintype Φ] [DecidableEq Φ] [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, DecidableEq (n' τ)] in
/-- The determinant exponent of the one-place families with the data at τ is that at τ. -/
private lemma schurDetExp_unit_eq (τ : Φ) :
    schurDetExp (fun _ : Unit ↦ n τ) (fun _ : Unit ↦ n' τ) (fun _ : Unit ↦ κ τ) () =
      schurDetExp n n' κ τ :=
  rfl

/-- Assume `FitsRanks n n' κ`: at every place τ, |n_τ| ≤ |n'_τ| and κ_τ(h) = 0 for
|n_τ| < h < |n'_τ|. For matrices z_τ of size n'_τ × n_τ, row i of the Schur matrix `schur κ z` holds
the coordinates of b'_i(z y) in the family b_j(y)·∏_τ det(y_τ)^{d_τ}, where b and b' are
`nablaBasis` for n and n', and d is `schurDetExp n n' κ`. Its (i, j) entry equals the product over τ
of the (i τ, j τ) entries of the one-place Schur matrices, namely those of the families over `Unit`
with data κ τ and z τ. -/
lemma schur_apply_eq_prod (h_fits : FitsRanks n n' κ) (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R)
    (i : WeylIndexFamily n' κ) (j : WeylIndexFamily n κ) :
    schur κ z i j =
      ∏ τ : Φ, schur (fun _ : Unit ↦ κ τ) (fun _ : Unit ↦ z τ) (fun _ : Unit ↦ i τ)
        fun _ : Unit ↦ j τ := by
  -- Check that the product of the one-place entries satisfies the expansion that characterises the
  -- Schur matrix (`schur_eq_of_expansion`): it is the product over `τ` of the one-place expansions.
  let S (τ : Φ) : Matrix (WeylIndexFamily (fun _ : Unit ↦ n' τ) fun _ : Unit ↦ κ τ)
      (WeylIndexFamily (fun _ : Unit ↦ n τ) fun _ : Unit ↦ κ τ) R :=
    schur (fun _ : Unit ↦ κ τ) fun _ : Unit ↦ z τ
  suffices h_schur : schur κ z = fun (i : WeylIndexFamily n' κ) (j : WeylIndexFamily n κ) ↦
      ∏ τ : Φ, S τ (fun _ : Unit ↦ i τ) fun _ : Unit ↦ j τ from congrFun₂ h_schur i j
  refine schur_eq_of_expansion fun i ↦ ?_
  have one_place (τ : Φ) :
      ∑ a : BasisTableau (n τ) (rankAt n τ) (κ τ), S τ (fun _ ↦ i τ) (fun _ ↦ a) •
          (nablaBasis R (fun _ : Unit ↦ n τ) (fun _ ↦ κ τ) (fun _ ↦ a) *
            detPow R _ (schurDetExp (fun _ ↦ n τ) (fun _ ↦ n' τ) fun _ ↦ κ τ)) =
        rowSubst (fun _ : Unit ↦ z τ) (nablaBasis R (fun _ ↦ n' τ) (fun _ ↦ κ τ) fun _ ↦ i τ) :=
    ((piUnique _).symm.sum_comp _).trans (sum_schur_smul_nablaBasis (fun _ : Unit ↦ h_fits τ)
      (fun _ : Unit ↦ z τ) fun _ : Unit ↦ i τ)
  -- Move each expansion into the variables of colour `τ`, multiply, and expand the product of sums.
  have h_prod :
      ∏ τ : Φ, rename (Prod.map (fun p : (Σ _ : Unit, n τ) ↦ (⟨τ, p.snd⟩ : Σ σ : Φ, n σ)) id)
          (∑ a : BasisTableau (n τ) (rankAt n τ) (κ τ), S τ (fun _ ↦ i τ) (fun _ ↦ a) •
            (nablaBasis R (fun _ : Unit ↦ n τ) (fun _ ↦ κ τ) (fun _ ↦ a) *
              detPow R _ (schurDetExp (fun _ ↦ n τ) (fun _ ↦ n' τ) fun _ ↦ κ τ))) =
        ∏ τ : Φ, rename (Prod.map (fun p : (Σ _ : Unit, n τ) ↦ (⟨τ, p.snd⟩ : Σ σ : Φ, n σ)) id)
          (rowSubst (fun _ : Unit ↦ z τ) (nablaBasis R (fun _ ↦ n' τ) (fun _ ↦ κ τ) fun _ ↦ i τ)) :=
    prod_congr rfl fun τ _ ↦ by rw [one_place τ]
  simpa [nablaBasis, rowSubst, prod_mul_distrib, tableauPoly, minor, detPow, ← C_mul',
    AlgHom.map_det, Matrix.map, prod_univ_sum, schurDetExp_unit_eq] using h_prod

/-- If the sizes fit κ, scaling z_τ by t_τ scales S_κ(z) by the product of the t_τ^{|κ_τ|}, where
|κ_τ| = Σ_{h < |n'_τ|} h κ_τ(h) is the number of boxes at τ. -/
lemma schur_smul (h_fits : FitsRanks n n' κ) (t : Φ → R) (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R) :
    (schur κ fun τ : Φ ↦ t τ • z τ) =
      (∏ τ : Φ, t τ ^ ∑ i ∈ range (rankAt n' τ), i * κ τ i) • schur κ z := by
  -- A scalar is a diagonal matrix, whose Schur matrix is again a scalar.
  simp [smul_eq_diagonal_mul, schur_mul_left h_fits, sum_range, ← pow_mul, ← prod_pow_eq_pow_sum]

end New

/-! ## Schur representations twisted by determinants -/

/-- The action on the Weyl module of a dominant weight μ, given as (κ, e): κ_τ(h) = μ_h − μ_{h+1} is
the number of columns of height h < |n_τ| at the place τ, and the integer e_τ is the last entry of
μ_τ. The monoid homomorphism sends a family g of invertible matrices g_τ ∈ GL(n_τ, R) to ∏_τ
det(g_τ)^{e_τ} times the Schur matrix S_κ(g). -/
noncomputable def New.weylRep {Φ R : Type} [CommRing R] [Fintype Φ] [DecidableEq Φ]
    {n : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)] (κ : Φ → ℕ → ℕ)
    (e : Φ → ℤ) :
    ((τ : Φ) → GL (n τ) R) →* Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) R :=
  MonoidHom.mk
    { toFun := fun g : ∀ τ : Φ, GL (n τ) R ↦
        (∏ τ : Φ, (g τ).det ^ e τ) • schur κ fun τ : Φ ↦ (g τ : Matrix (n τ) (n τ) R)
      map_one' := by simp }
    (by simp [mul_zpow, smul_mul_smul, Finset.prod_mul_distrib])

/-!
## Weights of the basis, evaluation vectors, the highest basis vector, one-row shapes

Weights of the standard basis b_i = `New.nablaBasis` of the module ∇ = `New.nablaFamily`.

* `New.sum_tableauWeight_le`: the weight of each b_i is dominated by the partition
  λ = `New.diagramWeight`.
* `New.schur_mulVec_weylEval`: the Schur matrix of z carries the vector of values b_j(y)
  (`New.weylEval`) to the vector of values at zy, up to a power of determinants of y.
* `New.map_nablaBasis_eq_map_weylKernel_mul_weylEval`: a linear form that sees only basis vectors of
  highest weight is determined by its value on the kernel `New.weylKernel`.
-/

namespace New

variable {Φ : Type}
  {R : Type} [CommRing R] [Fintype Φ]
  {n : Φ → Type} {n' : Φ → Type _}
  {κ : Φ → ℕ → ℕ} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)]
  [∀ τ : Φ, Fintype (n' τ)] [∀ τ : Φ, DecidableEq (n' τ)]

open MvPolynomial Finset Matrix «GL» Equiv Fintype

/-- Let i be a family of chosen standard fillings (`New.WeylIndexFamily`). At a place τ, the column
j of height h of the filling i_τ is an h-tuple of rows; its entries are distinct. -/
lemma tableau_col_injective [DecidableEq Φ] (i : WeylIndexFamily n κ) (τ : Φ) (h : Fin (rankAt n τ))
    (j : Fin (κ τ h)) :
    Function.Injective ((i τ).val h j) := by
  -- A repeated entry gives a minor with two equal rows, so b_i = 0 over ℤ; but the basis products
  -- are linearly independent, hence not zero.
  intro s s' h_eq
  by_contra h_ne
  have h_minor : minor (m := Σ τ : Φ, n τ) ℤ (Sigma.mk τ ∘ (i τ).val h j) = 0 :=
    det_zero_of_row_eq h_ne (by ext b; simp [h_eq])
  apply (linearIndependent_nablaBasis (R := ℤ)).ne_zero i
  simp only [nablaBasis, tableauPoly]
  exact prod_eq_zero (mem_univ τ) (prod_eq_zero (mem_univ h) (prod_eq_zero (mem_univ j) h_minor))

omit [Fintype Φ] in
/-- Let i be a family of chosen standard fillings (`New.WeylIndexFamily`) and τ a place. The number
`New.tableauWeight i τ a` of entries of i_τ equal to the row a, summed over all rows a, is the
number of boxes Σ_{h<|n_τ|} h·κ_τ(h). -/
lemma sum_tableauWeight (i : WeylIndexFamily n κ) (τ : Φ) :
    ∑ a : n τ, tableauWeight i τ a = ∑ h ∈ range (rankAt n τ), h * κ τ h := by
  simp [sum_comm, sum_range, mul_comm, tableauWeight, sum_card_fiberwise_eq_card_filter]

/-- Let i be a family of chosen standard fillings (`New.WeylIndexFamily`) and A a set of rows at the
place τ. Write λ = `New.diagramWeight`, so λ(τ,k) = Σ_{k<h<|n_τ|} κ_τ(h).
(a) The number of entries of i_τ lying in A (counted by `New.tableauWeight`) is at most
Σ_{k<|A|} λ(τ,k).
(b) If equality holds, every entry of a column of height h ≤ |A| lies in A. -/
lemma sum_tableauWeight_le [DecidableEq Φ] (i : WeylIndexFamily n κ) (τ : Φ) (A : Finset (n τ)) :
    -- (a)
    ∑ a ∈ A, tableauWeight i τ a ≤ ∑ k ∈ range #A, diagramWeight (rankAt n) κ ⟨τ, k⟩ ∧
    -- (b)
    (∑ k ∈ range #A, diagramWeight (rankAt n) κ ⟨τ, k⟩ ≤ ∑ a ∈ A, tableauWeight i τ a →
     ∀ (h : Fin (rankAt n τ)) (j : Fin (κ τ h)) (s : Fin h),
       (h : ℕ) ≤ #A → (i τ).val h j s ∈ A) := by
  -- Count column by column: a column of height `h` has distinct entries, so at most `min #A h` of
  -- them lie in `A`. Summed over the columns, the two sides are the two sides of the claim.
  let count (p : Σ h : Fin (rankAt n τ), Fin (κ τ h)) : ℕ := #{s | (i τ).val p.fst p.snd s ∈ A}
  have h_col (p : Σ h : Fin (rankAt n τ), Fin (κ τ h)) : count p ≤ min #A p.fst := by
    apply le_min
    · -- the entries of the column that lie in `A` are distinct elements of `A`
      exact card_le_card_of_injOn _ (fun s hs ↦ by simpa using hs)
        (tableau_col_injective i τ p.fst p.snd).injOn
    · exact card_finset_fin_le _
  have h_left : ∑ a ∈ A, tableauWeight i τ a = ∑ p, count p := by
    simp [count, Fintype.sum_sigma, sum_comm, tableauWeight, sum_card_fiberwise_eq_card_filter]
  have h_right : ∑ k ∈ range #A, diagramWeight (rankAt n) κ ⟨τ, k⟩ =
      ∑ p : Σ h : Fin (rankAt n τ), Fin (κ τ h), min #A p.fst := by
    -- (`mem_range` is removed: with it simp applies `sum_comm` back and forth)
    simp [-mem_range, mul_comm, Fintype.sum_sigma, sum_range (n := rankAt n τ), sum_comm,
      diagramWeight, Finsupp.single_apply, ite_and]
  rw [h_left, h_right]
  refine ⟨sum_mono h_col, ?_⟩
  intro h_ge h j s h_le
  -- In the case of equality every column attains its bound, which is `h` when `h ≤ #A`.
  have h_all : ∀ p ∈ (univ : Finset (Σ h : Fin (rankAt n τ), Fin (κ τ h))),
      count p = min #A p.fst :=
    (sum_eq_sum_iff_of_le fun p _ ↦ h_col p).mp ((sum_mono h_col).antisymm h_ge)
  have h_full : count ⟨h, j⟩ = #(univ : Finset (Fin h)) := by
    simpa [h_le] using h_all ⟨h, j⟩ (mem_univ _)
  exact card_filter_eq_iff.mp h_full s (mem_univ s)

omit [Fintype Φ] [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, Fintype (n' τ)]
  [∀ τ : Φ, DecidableEq (n' τ)] in
/-- Let z_τ be matrices of size n'_τ×n_τ, y an array over R with rows (τ, a), and f a polynomial
in an array with rows (τ, b). Then `New.rowSubst z f` evaluated at y is f evaluated at the product
array zy, whose entry at row (τ, b) and column k is Σ_a z_τ(b,a)·y((τ,a),k). -/
lemma GL.eval_rowSubst (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R) (y : ((τ : Φ) × n τ) × ℕ → R)
    (f : MatrixPoly ((τ : Φ) × n' τ) R) :
    eval y (rowSubst z f) = eval (fun x : ((τ : Φ) × n' τ) × ℕ ↦
      ∑ a : n x.1.fst, z x.1.fst x.1.snd a * y (⟨x.1.fst, a⟩, x.2)) f := by
  -- `rowSubst z` substitutes a polynomial for each variable (it is `bind₁`), and evaluation after
  -- a substitution evaluates the substituted polynomials (`eval₂Hom_bind₁`).
  rw [rowSubst, aeval_eq_bind₁, MvPolynomial.eval, eval₂Hom_bind₁]
  simp

/-- Assume `FitsRanks n n' κ`: for every τ, |n_τ| ≤ |n'_τ| and κ_τ(h) = 0 for |n_τ| < h < |n'_τ|.
Let z_τ be matrices of size n'_τ × n_τ, let y be an array with rows (τ, a), and let zy be the array
with entries (zy)_{(τ,b),k} = Σ_a z_τ(b,a) y_{(τ,a),k}. Write ev_y for the vector of values b_j(y)
of the basis products of minors `nablaBasis` (`weylEval`) and d τ = κ_τ(|n_τ|) if |n_τ| < |n'_τ|,
else 0. Then ∏_τ det(y_τ)^{d τ} · S_κ(z) ev_y = ev_{zy}, where y_τ is the square block of the first
|n_τ| columns of y at τ and S_κ(z) = `schur κ z` is the matrix expressing each b'_i(zy) in the
b_j(y) ∏_τ det(y_τ)^{d τ}. -/
lemma schur_mulVec_weylEval [DecidableEq Φ]
    (h_fits : FitsRanks n n' κ) (z : (τ : Φ) → Matrix (n' τ) (n τ) R)
    (y : ((τ : Φ) × n τ) × ℕ → R) :
    (detPow R n (schurDetExp n n' κ)).eval y • schur κ z *ᵥ weylEval n κ y =
      weylEval n' κ fun x : ((τ : Φ) × n' τ) × ℕ ↦
        ∑ a : n x.1.fst, z x.1.fst x.1.snd a * y (⟨x.1.fst, a⟩, x.2) := by
  -- Evaluate at `y` the expansion `b'_i(zy) = Σ_j S(z)_{ij} b_j(y) ∏ det(y_τ)^{d_τ}` of
  -- `sum_schur_smul_nablaBasis`, one row `i` at a time.
  funext i
  simpa [weylEval, GL.eval_rowSubst, mulVec, dotProduct, mul_sum, mul_rotate'] using
    congrArg (eval y) (sum_schur_smul_nablaBasis h_fits z i)

/-- Suppose the sizes fit κ (`New.FitsRanks`) and the determinant exponents `New.schurDetExp` are
all zero. Then the Schur matrix S_κ(z) carries the evaluation vector `New.weylEval` at y to the
evaluation vector at the product array zy. -/
lemma schur_mulVec_weylEval_of_schurDetExp_eq_zero [DecidableEq Φ] (h_fits : FitsRanks n n' κ)
    (h_detExp : schurDetExp n n' κ = 0) (z : (τ : Φ) → Matrix (n' τ) (n τ) R)
    (y : ((τ : Φ) × n τ) × ℕ → R) :
    schur κ z *ᵥ weylEval n κ y =
      weylEval n' κ fun x : ((τ : Φ) × n' τ) × ℕ ↦
        ∑ a : n x.1.fst, z x.1.fst x.1.snd a * y (⟨x.1.fst, a⟩, x.2) := by
  simp [← schur_mulVec_weylEval h_fits, h_detExp]

omit [∀ τ : Φ, DecidableEq (n τ)] in
/-- For every array y over R with rows (τ, a), the kernel `New.weylKernel` at y lies in the module
∇ = `New.nablaFamily` of Borel semi-invariants: it is a substitution of the product of leading
minors `New.highestPoly`. -/
lemma weylKernel_mem_nablaFamily [DecidableEq Φ] (y : ((τ : Φ) × n τ) × ℕ → R) :
    weylKernel n κ y ∈ nablaFamily R n κ := by
  rw [weylKernel, highestPoly]
  exact rowSubst_mem_nabla _ prod_tableauPoly_mem_nabla

/-- Let e_τ enumerate the rows at each place τ, and let y be the permutation array of e
(`New.permArray`): y((τ,a),k) is 1 if e_τ(a) = k and 0 otherwise. The kernel `New.weylKernel` at
y, evaluated at y, equals 1. -/
lemma GL.eval_weylKernel_permArray (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ)) :
    (weylKernel n κ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ))).eval
      (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) =
      (1 : R) := by
  -- At y, the substituted array of the kernel is the identity matrix, whose leading minors are 1.
  simp [← eq_symm_apply, ← diagonal.eq_1, weylKernel, rowSubst, permArray, Fin.val_inj, highestPoly,
    tableauPoly, minor, AlgHom.map_det, Matrix.map, RingHom.map_det]

/-- Let e_τ enumerate the rows at each place τ, and let y be the permutation array of e
(`New.permArray`). Let i be a family of chosen standard fillings (`New.WeylIndexFamily`) in which
every entry of a column of height k of i_τ has position below k in the enumeration e_τ. Then the
basis vector b_i = `New.nablaBasis` is its value b_i(y) (`New.weylEval`) times the kernel
`New.weylKernel` at y. -/
lemma nablaBasis_eq_weylEval_smul_weylKernel_of_lt (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    (i : WeylIndexFamily n κ)
    (h_lt : ∀ (τ : Φ) (k : Fin (rankAt n τ)) (j : Fin (κ τ k)) (s : Fin k),
      e τ ((i τ).val k j s) < k) :
    nablaBasis R n κ i =
      (weylEval n κ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) i : R) •
        weylKernel n κ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) := by
  -- The rows of each minor are among the first `k` rows, so the minor is its value at y times the
  -- leading minor of the substituted array, by multiplying determinants.
  -- (`prod_const` is left out: it turns the equal factors into a power before the determinants are
  -- multiplied)
  simp [nablaBasis, ← C_mul', ← prod_mul_distrib, ← det_mul, -prod_const, tableauPoly, minor,
    weylEval, RingHom.map_det, Matrix.map, permArray, weylKernel, rowSubst, Fin.val_inj,
    highestPoly, AlgHom.map_det]
  -- For each column, the matrix of variables is the product of the 0/1 matrix of the positions of
  -- its rows (the value at y) and the matrix of the substituted array.
  congr!
  ext a b
  -- In entry `(a, b)` of the product only the position of row `a` of the column contributes; it
  -- is below the height by `h_lt`.
  rw [mul_apply, sum_eq_ite ⟨_, h_lt ..⟩]
  · -- the term at that position is the variable of entry `(a, b)`
    aesop
  · -- the terms at the other positions are zero
    aesop

/-- Let e_τ enumerate the rows at each place τ, and let y be the permutation array of e
(`New.permArray`). If, for a family i of chosen standard fillings, some entry of a column of height
k of i_τ has position at least k in the enumeration e_τ, then the value b_i(y) of the basis vector
(`New.weylEval`) is zero. -/
lemma weylEval_permArray_eq_zero_of_le (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    (i : WeylIndexFamily n κ) (τ : Φ) (k : Fin (rankAt n τ)) (j : Fin (κ τ k)) (s : Fin k)
    (h_le : k ≤ e τ ((i τ).val k j s)) :
    weylEval n κ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) i = (0 : R) := by
  -- Row `s` of the minor of column `(τ, k, j)` is zero at `y`: its entry in a column `b < k` is
  -- 1 only if the position of the row is `b`, but that position is at least `k`.
  have h_minor : eval (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ))
      (minor (m := Σ τ : Φ, n τ) R (Sigma.mk τ ∘ (i τ).val k j)) = 0 := by
    rw [minor, RingHom.map_det]
    apply det_eq_zero_of_row_eq_zero s
    intro b
    have h_ne : (e τ ((i τ).val k j s) : ℕ) ≠ b := by omega
    simp [permArray, h_ne]
  simp only [weylEval, nablaBasis, tableauPoly, map_prod]
  exact prod_eq_zero (mem_univ τ) (prod_eq_zero (mem_univ k) (prod_eq_zero (mem_univ j) h_minor))

/-- Let e_τ enumerate the rows at each place τ, let i be a family of chosen standard fillings
(`New.WeylIndexFamily`) with basis vector b_i = `New.nablaBasis`, and let φ be an R-linear form on
polynomials. Suppose that φ(b_i) ≠ 0 only when, at each row (τ, a), the number of entries of i_τ
equal to a (`New.tableauWeight`) is at least λ(τ, e_τ(a)), where λ = `New.diagramWeight`. Then
φ(b_i) = φ(k)·b_i(y), where y is the permutation array of e (`New.permArray`), k is the kernel
`New.weylKernel` at y, and b_i(y) = `New.weylEval`. -/
lemma map_nablaBasis_eq_map_weylKernel_mul_weylEval [DecidableEq Φ]
    (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    (i : WeylIndexFamily n κ) (φ : MatrixPoly (Σ τ : Φ, n τ) R →ₗ[R] R)
    (h_wt :
      φ (nablaBasis R n κ i) ≠ 0 →
      ∀ (τ : Φ) (a : n τ), diagramWeight (rankAt n) κ (τ, e τ a) ≤ tableauWeight i τ a) :
    φ (nablaBasis R n κ i) =
      φ (weylKernel n κ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ))) *
        weylEval n κ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) i := by
  by_cases! h_lt : ∀ (τ : Φ) (k : Fin (rankAt n τ)) (j : Fin (κ τ k)) (s : Fin k),
      e τ ((i τ).val k j s) < k
  · -- Every column of height `k` has its entries among the first `k` rows.
    rw [nablaBasis_eq_weylEval_smul_weylKernel_of_lt e i h_lt, map_smul, smul_eq_mul, mul_comm]
  obtain ⟨τ, k, j, s, h_le⟩ := h_lt
  rw [weylEval_permArray_eq_zero_of_le e i τ k j s h_le, mul_zero]
  -- If `φ` saw this basis product, equality would hold in `sum_tableauWeight_le` for the set `A`
  -- of the first `k` rows, so the entry `s` would lie in `A`, against `h_le`.
  by_contra h_ne
  let A : Finset (n τ) := (Iio k).map (e τ).symm.toEmbedding
  have h_ge : ∑ l ∈ range #A, diagramWeight (rankAt n) κ ⟨τ, l⟩ ≤ ∑ a ∈ A, tableauWeight i τ a := by
    grw [← h_wt h_ne]
    simp [A, ← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, diagramWeight, Finsupp.single_apply,
      ite_and]
  have h_mem : (i τ).val k j s ∈ A := (sum_tableauWeight_le i τ A).2 h_ge k j s (by simp [A])
  exact h_le.not_gt (by simpa [A] using h_mem)

/-- One place (Φ = Unit) with a row type m of size |m| > 1, and column multiplicities k with
k(1) = a and k(h) = 0 for 1 < h < |m|: the shape is one row of length a. `New.WeylIndexFamily`
indexes the basis `nablaBasis` b, and S_k(z) (`New.schur`) is the matrix whose row i holds chosen
coordinates of b_i(z y) in the family b_j(y)·det(y)^d. Let q : σ ≃ m be a bijection. Then there is a
bijection φ from these basis indices to the exponents of degree a in σ (`New.Monomials`) such that,
for all complex c and square z, c^a·S_k(z)_{ij} is the (φ j, φ i) entry of the a-th symmetric power
`New.symPowMatrix` of c·zᵀ reindexed along q. -/
lemma exists_equiv_schur_one_row_eq_symPowMatrix {a : ℕ} {m σ : Type} [Fintype m] [DecidableEq m]
    [Fintype σ] [DecidableEq σ] {k : ℕ → ℕ} (q : σ ≃ m) (h_card : 1 < Fintype.card m)
    (h_k_eq : ∀ i : ℕ, i > 0 → i < Fintype.card m → k i = if i = 1 then a else 0) :
    ∃ φ : WeylIndexFamily (fun _ : Unit ↦ m) (fun () ↦ k) ≃ Monomials σ a,
      ∀ (c : ℂ) (z : Matrix m m ℂ) (i j : WeylIndexFamily (fun _ : Unit ↦ m) fun _ : Unit ↦ k),
        c ^ a * schur (fun () ↦ k) (fun _ ↦ z) i j =
          symPowMatrix a (c • zᵀ.submatrix q q) (φ j) (φ i) := by
  -- Only columns of height `1` count, so each basis vector is a monomial of degree `a` in the
  -- first column of variables, and all such monomials occur. In this basis `schur` is the matrix
  -- of a linear substitution on forms of degree `a`.
  have h_size : ∑ h ∈ range (card m), h * k h = a := by grind [sum_eq_ite 1]
  have h_monomial (i : WeylIndexFamily (fun _ : Unit ↦ m) fun () ↦ k) :
      ∃ d : Monomials σ a,
        nablaBasis ℂ (fun _ ↦ m) (fun () ↦ k) i =
          bind₁ (fun b ↦ X (⟨(), q b⟩, 0)) (monomial d 1) := by
    -- The exponent of `b` is the number of entries of the filling equal to `q b`.
    refine ⟨⟨∑ h, ∑ j, ∑ s, Finsupp.single (q.symm ((i ()).val h j s)) 1, ?_⟩, ?_⟩
    · -- its degree is the number of boxes, `a`
      simp [sum_comm (γ := σ), ← h_size, sum_range, mul_comm]
    -- Unfolded, the left side is the product of the minors of the columns, the right side the
    -- product of the variables `X (entry, 0)` over all entries.
    simp [nablaBasis, monomial_sum_one, ← X.eq_1, tableauPoly, minor]
    -- Compare column by column, by the height of the column: minors of size `0` and `1` are the
    -- products of their variables, and there are no columns of height at least `2`.
    congr! with ⟨_ | _ | _⟩
    · -- height `0`: the empty determinant and the empty product
      simp [univ_eq_empty]
    · -- height `1`: a `1 × 1` determinant
      simp
    · -- height at least `2`: `k h = 0` by `h_k_eq`
      grind [cases Fin]
  choose φ hφ using h_monomial
  -- Distinct basis vectors are distinct monomials.
  have h_inj : Function.Injective φ := fun i j h_eq ↦
    (linearIndependent_nablaBasis (R := ℂ)).injective (by rw [hφ, hφ, h_eq])
  have h_surj : Function.Surjective φ := by
    rintro ⟨d, hd⟩
    -- A monomial of degree `a` in the first column is semi-invariant of the right weight.
    have h_mem : bind₁ (fun b ↦ X (⟨(), q b⟩, 0)) (monomial d 1) ∈
        nablaFamily ℂ (fun _ ↦ m) fun () ↦ k := by
      -- Only columns of height `1` count, `k 1 = a` of them: the weight is `a` at `((), 0)`.
      simp_all [mem_nabla, monomial_eq, borelMul, mul_pow, prod_pow_eq_pow_sum, prod_mul_distrib,
        diagramWeight]
      rw [sum_eq_ite 1]
      · simp [h_card, h_k_eq 1 one_pos h_card, mul_comm]
      · intro h h_mem_range h_ne_one
        rcases Nat.eq_zero_or_pos h with h_zero | h_pos
        · simp [h_zero]
        · simp [h_k_eq h h_pos (mem_range.mp h_mem_range), h_ne_one]
    -- so it is a combination `Σ_i c_i b_i` of the basis vectors, which are the monomials `φ i`.
    by_contra h_miss
    obtain ⟨c, h_sum⟩ : ∃ c : (WeylIndexFamily (fun _ : Unit ↦ m) fun () ↦ k) → ℂ,
        ∑ i, c i • nablaBasis ℂ (fun _ ↦ m) (fun () ↦ k) i =
          bind₁ (fun b ↦ X (⟨(), q b⟩, 0)) (monomial d 1) :=
      ⟨_, sum_coords_nablaBasis h_mem⟩
    -- Rename the variable `(q b, 0)` back to `b` and take the coefficient of `d`: it is `0` on the
    -- left, where no `φ i` is `d`, and `1` on the right.
    have h_coeff :
        (rename (fun x : ((_ : Unit) × m) × ℕ ↦ q.symm x.1.snd)
          (∑ i, c i • nablaBasis ℂ (fun _ ↦ m) (fun () ↦ k) i)).coeff d =
        (rename (fun x : ((_ : Unit) × m) × ℕ ↦ q.symm x.1.snd)
          (bind₁ (fun b ↦ X (⟨(), q b⟩, 0)) (monomial d 1))).coeff d := by
      rw [h_sum]
    have h_ne : ∀ i, (φ i : σ →₀ ℕ) ≠ d := fun i h_eq ↦ h_miss ⟨i, Subtype.ext h_eq⟩
    -- With the coefficients computed, `h_coeff` reads `0 = 1`.
    simp [hφ, rename_bind₁, h_ne] at h_coeff
  have h_bij : Function.Bijective φ := ⟨h_inj, h_surj⟩
  refine ⟨.ofBijective φ h_bij, ?_⟩
  intro c z i j
  -- The scalar `c` comes out of the Schur matrix as `c ^ a` (`schur_smul`).
  have h_scalar : c ^ a * schur (fun () ↦ k) (fun _ ↦ z) i j =
      schur (fun () ↦ k) (fun () ↦ c • z) i j := by simp [schur_smul, h_size]
  rw [h_scalar]
  -- By `schur_eq_of_expansion`, the Schur matrix is the matrix that expands the substituted basis.
  apply congrFun₂ (schur_eq_of_expansion fun i ↦ ?_)
  let f : MvPolynomial σ ℂ := linSubst (c • zᵀ.submatrix q q) (monomial (φ i).1 1)
  have h_expand : ∑ β : Monomials σ a, f.coeff β • monomial β 1 = f :=
    sum_monomials_eq_of_isHomogeneous ((φ i).isHomogeneous_linSubst _)
  -- Substitute the first column of variables into this expansion of `f`.
  have h_subst : bind₁ (fun b ↦ X ((⟨(), q b⟩ : Σ _ : Unit, m), 0))
        (∑ β : Monomials σ a, f.coeff β • monomial β 1) =
      bind₁ (fun b ↦ X ((⟨(), q b⟩ : Σ _ : Unit, m), 0)) f := by rw [h_expand]
  -- Reindex the sum over monomials by the bijection `φ`.
  rw [← h_bij.sum_comp (fun β : Monomials σ a ↦ f.coeff β • monomial (β : σ →₀ ℕ) 1)] at h_subst
  simpa [f, hφ, monomial_eq, reindex_equiv q, symPowMatrix, linSubst, rowSubst] using h_subst

end New

/-! ## Continuity of Schur matrices -/

/-- Over a topological ring R, the Schur matrix S_κ(g) = `New.schur κ g` of a family g of square
matrices g_τ of size n_τ is continuous in g: by base change (`New.schur_map`) each of its entries is
a polynomial in the entries of g. -/
@[fun_prop]
lemma New.continuous_schur {Φ : Type} {n : Φ → Type} {κ : Φ → ℕ → ℕ} {R : Type} [Fintype Φ]
    [DecidableEq Φ] [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)] [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (schur κ : (∀ τ : Φ, Matrix (n τ) (n τ) R) →
      Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) R) := by
  -- By base change (`schur_map`), the entries of `schur κ g` are the polynomial entries of the
  -- Schur matrix of the generic matrices `GL.genericMatrixAt R n`, evaluated at the entries of `g`.
  have h_eval (g : ∀ τ : Φ, Matrix (n τ) (n τ) R) :
      (schur κ (GL.genericMatrixAt R n)).map (GL.evalMatrix g) = schur κ g := by
    simp [← schur_map .refl]
  refine .congr (continuous_matrix fun i j ↦ ?_) h_eval
  simp only [Matrix.map_apply, MvPolynomial.eval_eq]
  fun_prop
