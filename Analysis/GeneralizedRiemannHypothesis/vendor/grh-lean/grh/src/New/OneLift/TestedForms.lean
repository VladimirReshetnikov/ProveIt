import Lib.LocalGL.Green.LabelCharacters
import New.UpperBound.Objects.AuxiliaryPair

/-!
# Point forms, Hecke adjoints and false lifts on the definite space of a descent pair

This file studies algebraic forms on the definite space `V = I_n` of a descent pair `O`
(`New.DescentPair`). The pair gives a space `W` of rank `r`, an embedding `O.incl` of `r` into `n`,
and places indexed by `O.ChosenIndex` (the set M of chosen places) and `O.TwistIndex` (the set Q of
the twist). For each `σ ∈ Aut ℂ`, `New.LevelPlaces.LevelForm.innerAt σ` is `σ⁻¹` of the inner
product of the `σ`-conjugates of two forms. Point forms, supported on one class, have explicit inner
products and descents, and the Hecke polynomial `H_w(X)` at a split place has an explicit adjoint
for these pairings. Let `Z` (in use, the space of lifts) lie in the image of a central idempotent
`e₀` and be killed by `H_w(X_*)`, where `X_* = O.liftHeckeRoot w`. On forms orthogonal to the false
lifts, the orthogonal projection (for `σ = 1`) to `Z` does not increase the norm at any `σ`.

## Main definitions and results

* `New.Rows.IsPointLift`, `New.Rows.exists_isPointLift`, `New.Rows.pointLift`: an element `A` of the
  integral level with prescribed columns at `O.ChosenIndex` and rows at `O.TwistIndex`.
* `New.Rows.pointForm`: the point form at `h A`; `New.Rows.inner_pointForm` and
  `New.Rows.normalizedDescent_pointForm` compute its inner products and its descent
  `New.DescentPair.normalizedDescent`, whose finite datum is `New.Rows.pointFormDatum`.
* `New.LevelPlaces.LevelForm.innerAt_heckePolyOnForms` computes the adjoint of `H_w(X)` for the
  pairing `innerAt σ`.
* `New.DescentPair.falseLiftsAt`, `New.DescentPair.IsOrthogonalToFalseLifts`,
  `New.DescentPair.IsTestForm`: false lifts, the forms orthogonal to them, and the integral ones
  among these for a fixed `e₀` and `Z = ker O.normalizedDescent`.
* `New.Selmer.DenominatorLe`: a bound on the ℓ-adic denominator of the projection to a subspace Z.
* `New.DescentPair.normSqAt_starProjection_le`: on forms orthogonal to the false lifts the
  projection to Z does not increase the norm at σ.

Notions from other files:
* `New.DescentPair`: A descent pair: places M and Q, a space W of rank r with numbered basis
  vectors, an embedding of the index set r into the larger index set n, weights k⁺ and k⁻, and a
  character μ whose tame part is trivial off these places.
* `New.DescentPair.FormV`: the algebraic forms on V = I_n with the weight, level and character of
  the pair; the level sits at two finite sets of split places, M and Q.
* `New.DescentPair.heckePolyOnForms`: the operator H_w(X) = ∑_i (−X)^i q^{i(i−1)/2} T_{w,i} on
  forms, for a split place w that, with its conjugate, is off M and Q;
  `New.DescentPair.liftHeckeRoot` w is the value X_* at which it is taken.
* `New.DescentPair.normalizedDescent`: the descent, a linear map from forms Ξ on V to functions on
  U(W)(𝔸): its value at g is the class sum over h, for `New.DescentPair.levelGroup`, of
  `New.DescentPair.conjKernel` at g and h applied to Ξ(h). It is adjoint to the lift from W
  (`New.DescentPair.inner_thetaLift`).
* `New.LevelPlaces.placeAt`: the chosen places and the places of Q as one family, indexed by
  `O.ChosenIndex ⊕ O.TwistIndex`.

## Relation to the literature

See `New.OneLift.ComparisonOperator.GluingMaps` and `New.OneLift.LiftVolumeHeight` for related
work.
-/

/-!
## Point forms with prescribed finite datum: inner products and descent

Moving the point by an element `A` of the integral level changes the block datum `Ψ(T)` of the
descent to `Ψ(A⁻¹ T)`.
-/

namespace New.Rows

open Matrix NumberField ComplexConjugate

variable {E r n : Type} [Field E] [CMType E] [Fintype r] [DecidableEq r]
  [Fintype n] [DecidableEq n] {O : DescentPair E r n}

/-- The element `k` of the integral level `New.stdLevel` has component 1 at every finite place
other than those of M and Q (the set `O.places`) and their conjugates, its reductions at the chosen
places `O.placeAt (Sum.inl i)` have the columns `Y i` at the indices `O.incl`, and its reductions at
the places `O.placeAt (Sum.inr i)` of the twist have unit vectors in the rows `e`. Columns are
selected by `inclMatrix R u`, the matrix whose columns are the unit vectors at the indices `u`. -/
structure IsPointLift (Y : ∀ i : O.ChosenIndex, Matrix n r (ResField (O.placeAt (Sum.inl i))))
    (e : r ↪ n) (k : stdLevel E n) : Prop where
  /-- `k` is supported on the places of `O` and their conjugates. -/
  mem_supportedOn : (k : Gf E n) ∈ Gf.supportedOn n O.places
  /-- At a place of `O.ChosenIndex` the columns `O.incl` of the reduction of `k` form `Y i`. -/
  columns_eq (i : O.ChosenIndex) :
    (stdLevel.reduceAt (O.placeAt (Sum.inl i)) k).val *
      inclMatrix (ResField (O.placeAt (Sum.inl i))) O.incl = Y i
  /-- At a place of `O.TwistIndex` the row `e j` of the reduction of `k` is the unit vector
  `O.incl j`. -/
  rows_eq (i : O.TwistIndex) :
    (stdLevel.reduceAt (O.placeAt (Sum.inr i)) k).valᵀ * inclMatrix
      (ResField (O.placeAt (Sum.inr i))) e =
      inclMatrix (ResField (O.placeAt (Sum.inr i))) O.incl

/-- Given matrices `Y i` of full column rank over the residue fields at the places of
`O.ChosenIndex` and `r` distinct rows `e`, there is an element `k` of the integral level
`New.stdLevel` with `IsPointLift Y e k`: it is supported on the places of `O`, has the columns `Y i`
at `O.ChosenIndex`, and has unit vectors in the rows `e` at `O.TwistIndex`. -/
lemma exists_isPointLift {Y : ∀ i : O.ChosenIndex, Matrix n r (ResField (O.placeAt (Sum.inl i)))}
    (hY : ∀ i : O.ChosenIndex, (Y i).mulVec.Injective) (e : r ↪ n) :
    ∃ k : stdLevel E n, IsPointLift Y e k := by
  -- At the places of `O.ChosenIndex` extend `Y i` to an invertible matrix `A i`; at those of
  -- `O.TwistIndex` take `B i` whose columns `e` are the unit vectors `O.incl`. Lift the family
  -- `(A, Bᵀ)` to one element of `stdLevel`.
  have h_chosen (i : O.ChosenIndex) : ∃ A : GL n (ResField (O.placeAt (.inl i))),
      A.val * inclMatrix _ O.incl = Y i :=
    exists_GL_mul_inclMatrix O.incl (hY i)
  choose A hA using h_chosen
  have h_twist (i : O.TwistIndex) : ∃ B : GL n (ResField (O.placeAt (.inr i))),
      B.val * inclMatrix _ e = inclMatrix _ O.incl :=
    exists_GL_mul_inclMatrix e (inclMatrix_mulVecLin_injective O.incl _)
  choose B hB using h_twist
  obtain ⟨k, hk_supp, h_red⟩ : ∃ k : stdLevel E n, k.val ∈ Gf.supportedOn n O.places ∧
      stdLevel.reduceFamily O.placeAt k = Sum.rec A fun i ↦ transposeGL (B i) :=
    exists_reduceFamily_eq _
  refine ⟨k, hk_supp, fun i ↦ ?_, fun i ↦ ?_⟩
  · rw [show stdLevel.reduceAt (O.placeAt (.inl i)) k = A i from congrFun h_red (.inl i)]
    exact hA i
  · rw [show stdLevel.reduceAt (O.placeAt (.inr i)) k = transposeGL (B i)
      from congrFun h_red (.inr i)]
    exact hB i

variable (O) in
/-- The map sending `v` to the form `δ_h (v)` on `V = I_n` (`New.deltaForm`), supported on the class
of the point `h` of the finite unitary group `Gf E n`: its value at `y` is the sum of
`O.levelChar (h⁻¹ γ y) • ρ γ⁻¹ v` over the rational `γ` (embedded by `embFin`) with `h⁻¹ γ y` in the
level group of `O`. Here `ρ` is the representation whose highest weight is given by `O.columnCount`
and the determinant exponents `O.detExp`, and `WeylIndex n O.columnCount` indexes the coordinates of
its vectors. -/
noncomputable def classForm (h : Gf E n) : (WeylIndex n O.columnCount → ℂ) →ₗ[ℂ] O.FormV :=
  deltaForm (stdSpace E n).embFin ((stdSpace E n).weightRep O.columnCount O.detExp) O.levelChar h

/-- The inner product of two forms on `V` is the class sum of the pairings of their values under
`gramForm`, the hermitian form `(ξ, η) ↦ ξ* G η` of the integral Gram matrix `G` of the weight. The
class sum `stdClassSum` of a function `f` for the level group of `O` is the sum of
`f (g_c) / #Aut (g_c)` over the double cosets `c` of the rational points and that group. -/
lemma inner_eq_stdClassSum_gramForm (φ φ' : O.FormV) :
    inner ℂ φ φ' = stdClassSum O.levelGroup fun g : Gf E n ↦ gramForm (φ g) (φ' g) :=
  LevelPlaces.LevelForm.innerAt_eq_stdClassSum 1 φ φ'

/-- Let `h` be a point of the finite unitary group `Gf E n` of `V`. The inner product of the form
`δ_h (v) = classForm O h v`, supported on the class of `h`, with a form `φ` is the Gram pairing
`gramForm` of `v` with the value of `φ` at `h`. -/
lemma inner_classForm (h : Gf E n) (φ : O.FormV) (v : WeylIndex n O.columnCount → ℂ) :
    inner ℂ (classForm O h v) φ = gramForm v (φ h) := by
  -- The inner product is a class sum. By `classSum_deltaForm` the class sum of an invariant
  -- pairing against `δ_h (v)` is the value of the pairing at the point.
  let L (g : Gf E n) : (WeylIndex n O.columnCount → ℂ) →+ ℂ := (gramForm.flip (φ g)).toAddMonoidHom
  have h_sum : inner ℂ (classForm O h v) φ =
      stdClassSum O.levelGroup fun g : Gf E n ↦ L g (classForm O h v g) :=
    inner_eq_stdClassSum_gramForm (classForm O h v) φ
  refine h_sum.trans (classSum_deltaForm L fun γ k ↦ ?_)
  set ρ : Representation ℂ (U (stdSpace E n).J) (WeylIndex n O.columnCount → ℂ) :=
    (stdSpace E n).weightRep O.columnCount O.detExp
  have h_equivariant : φ ((stdSpace E n).embFin γ * h * k) = O.levelChar k • ρ γ (φ h) :=
    levelSpace_smoothFormRep_apply φ.property γ h k
  have h_unitary : gramForm (ρ γ v) (ρ γ (φ h)) = gramForm v (φ h) := by
    simp only [ρ, Space.weightRep_apply, gramForm_conjWeylRep]
  have h_unit : conj (O.levelChar k) * O.levelChar k = 1 := by
    rw [Complex.conj_mul', (LevelPlaces.isOfFinOrder_level_char k).norm_eq_one]
    simp
  change gramForm (O.levelChar k • ρ γ v) (φ ((stdSpace E n).embFin γ * h * k)) = gramForm v (φ h)
  rw [h_equivariant, LinearMap.map_smulₛₗ₂, map_smul, smul_smul, h_unit, one_smul, h_unitary]

/-- Let `h` be a point of the finite unitary group `Gf E n` of `V` and `g` a point of the adelic
unitary group `G E O.signs` of the space `O.W` of rank `r`. The descent `O.normalizedDescent` is the
linear map, adjoint to the theta lift from `O.W`, that takes forms on `V` to functions on that
group. Its value at `g` on the form `δ_h (v) = classForm O h v`, supported on the class of `h`, is
the complex conjugate of the theta kernel `modKernel` of the pair `(O.W, V)` at `(g, h)`, twisted
by the characters `O.charW`, `O.charV`. Its polynomial is `O.fockPoly (star v)`, the polynomial in
the Fock variables attached linearly to the conjugate weight vector. Its datum is a function of a
matrix `T` modulo `O.levelModulus 2`: it applies `O.residueBlockDatum` to the reductions
`levelResidueAt i` of `T` at the places `i` of M = `O.ChosenIndex` and Q = `O.TwistIndex`. That
datum is 0 unless each reduction at M is the inclusion matrix of `O.incl`, and is then the product
over the places w of Q of `O.tamePart w`, a character of the residue field, at the determinant of
the rows `O.incl`. -/
lemma normalizedDescent_classForm [WeilData E] (h : Gf E n) (v : WeylIndex n O.columnCount → ℂ)
    (g : G E O.signs) :
    O.normalizedDescent (classForm O h v) g = conj
      (modKernel O.W (stdSpace E n) O.charW O.charV (O.levelModulus 2)
      (fun T : Matrix n r (O.levelModulus 2).ResidueRing ↦
        O.residueBlockDatum fun i : O.ChosenIndex ⊕ O.TwistIndex ↦ T.map (levelResidueAt i))
      (O.fockPoly (star v)) g h) := by
  -- The right side is the definition of `O.conjKernel g h v`.
  change O.normalizedDescent (classForm O h v) g = O.conjKernel g h v
  exact classSum_deltaForm (fun x : Gf E n ↦ (O.conjKernel g x).toAddMonoidHom)
    fun γ k ↦ O.conjKernel_equivariant γ k v g h

/-- For matrices `Y i` of full column rank and `r` distinct rows `e`, a chosen element of the
integral level `New.stdLevel` as in `exists_isPointLift`. Its properties are stated in
`isPointLift_pointLift`. -/
noncomputable def pointLift
    {Y : ∀ i : O.ChosenIndex, Matrix n r (ResField (O.placeAt (Sum.inl i)))}
    (hY : ∀ i : O.ChosenIndex, (Y i).mulVec.Injective) (e : r ↪ n) : stdLevel E n :=
  (exists_isPointLift hY e).choose

lemma isPointLift_pointLift
    {Y : ∀ i : O.ChosenIndex, Matrix n r (ResField (O.placeAt (Sum.inl i)))}
    (hY : ∀ i : O.ChosenIndex, (Y i).mulVec.Injective) (e : r ↪ n) :
    IsPointLift Y e (pointLift hY e) :=
  (exists_isPointLift hY e).choose_spec

/-- The point form: the map sending `v` to the form `δ_{h A} (v)`, supported on the class of `h A`,
where `A = pointLift hY e`. The finite datum of its descent is `1[T = Y i]` at `O.ChosenIndex` and
`ψ (det T_e)` at `O.TwistIndex`, with `T_e` the rows `e` of `T` (`pointFormDatum`,
`normalizedDescent_pointForm`). -/
noncomputable def pointForm (h : Gf E n)
    {Y : ∀ i : O.ChosenIndex, Matrix n r (ResField (O.placeAt (Sum.inl i)))}
    (hY : ∀ i : O.ChosenIndex, (Y i).mulVec.Injective) (e : r ↪ n) :
    (WeylIndex n O.columnCount → ℂ) →ₗ[ℂ] O.FormV :=
  classForm O (h * pointLift hY e)

/-- The inner product of the point form made from `v` with a form `φ` is the Gram pairing `gramForm`
of `v` with the value of `φ` at the point `h A`, where `A = pointLift hY e`. -/
lemma inner_pointForm (h : Gf E n)
    {Y : ∀ i : O.ChosenIndex, Matrix n r (ResField (O.placeAt (Sum.inl i)))}
    (hY : ∀ i : O.ChosenIndex, (Y i).mulVec.Injective) (e : r ↪ n)
    (φ : O.FormV) (v : WeylIndex n O.columnCount → ℂ) :
    inner ℂ (pointForm h hY e v) φ = gramForm v (φ (h * pointLift hY e)) :=
  inner_classForm (h * (pointLift hY e : Gf E n)) φ v

open scoped Classical in
/-- The finite datum of the descent of a point form, as a function of families `X` of matrices over
the residue fields at the places of `O`. If `X` equals `Y` at every place of `O.ChosenIndex`, it is
the product over the places `w` of `O.TwistIndex` of `O.tamePart w` of the determinant of the rows
`e` of `X` at `w`; otherwise it is `0`. Here `O.tamePart w` is the character of the residue field at
`w` given by `O`. -/
noncomputable def pointFormDatum
    (Y : ∀ i : O.ChosenIndex, Matrix n r (ResField (O.placeAt (Sum.inl i)))) (e : r ↪ n)
    (X : ∀ i : O.ChosenIndex ⊕ O.TwistIndex, Matrix n r (ResField (O.placeAt i))) : ℂ :=
  if ∀ i : O.ChosenIndex, X (Sum.inl i) = Y i then
    ∏ i : O.TwistIndex, O.tamePart (O.placeAt (Sum.inr i)) ((X (Sum.inr i)).submatrix e id).det
  else
    0

/-- Let `Y i` be matrices of full column rank at the places of M = `O.ChosenIndex` and `e` an
injection choosing `r` rows. Let `A = pointLift hY e` be the chosen integral element whose
reductions have the columns `Y i` at `O.incl` over M, and unit vectors in the rows `e` over
Q = `O.TwistIndex`. Let `X` be a family of matrices over the residue fields at M and Q.
`O.residueBlockDatum` is 0 unless the matrices at M are the inclusion matrix of `O.incl`, and is
then the product over w in Q of `O.tamePart w`, a character of the residue field, at the determinant
of the rows `O.incl`. At the family `A⁻¹ X` it equals `pointFormDatum Y e X`, the same expression
with `Y i` for the inclusion matrix and the rows `e` for `O.incl`. -/
lemma residueBlockDatum_inv_pointLift_mul
    {Y : ∀ i : O.ChosenIndex, Matrix n r (ResField (O.placeAt (Sum.inl i)))}
    (hY : ∀ i : O.ChosenIndex, (Y i).mulVec.Injective) (e : r ↪ n)
    (X : ∀ i : O.ChosenIndex ⊕ O.TwistIndex, Matrix n r (ResField (O.placeAt i))) :
    O.residueBlockDatum (fun i : O.ChosenIndex ⊕ O.TwistIndex ↦
        (stdLevel.reduceAt (O.placeAt i) (pointLift hY e)⁻¹).val * X i) =
      pointFormDatum Y e X := by
  classical
  set A : stdLevel E n := pointLift hY e
  have hA : IsPointLift Y e A := isPointLift_pointLift hY e
  have h_chosen (i : O.ChosenIndex) :
      (stdLevel.reduceAt (O.placeAt (.inl i)) A⁻¹).val * X (.inl i) = inclMatrix _ O.incl ↔
        X (.inl i) = Y i := by
    rw [← hA.columns_eq, map_inv, Matrix.coe_units_inv, inv_mul_eq_iff_eq_mul_of_invertible]
  have h_twist (i : O.TwistIndex) :
      ((stdLevel.reduceAt (O.placeAt (.inr i)) A⁻¹).val * X (.inr i)).submatrix O.incl id =
        (X (.inr i)).submatrix e id := by
    -- Rows are selected by transposed inclusion matrices, and those for `O.incl` and `e` differ
    -- by the reduction of `A`, which cancels against that of `A⁻¹`.
    have h_incl : (inclMatrix (ResField (O.placeAt (.inr i))) O.incl)ᵀ =
        (inclMatrix (ResField (O.placeAt (.inr i))) e)ᵀ *
          (stdLevel.reduceAt (O.placeAt (.inr i)) A).val := by
      rw [← hA.rows_eq, transpose_mul, transpose_transpose]
    rw [← inclMatrix_transpose_mul, ← inclMatrix_transpose_mul, h_incl, Matrix.mul_assoc, map_inv,
      Matrix.coe_units_inv, mul_inv_cancel_left_of_invertible]
  simp only [DescentPair.residueBlockDatum, pointFormDatum, h_chosen, h_twist]

/-- Let `Y i` be matrices of full column rank at the places of M = `O.ChosenIndex`, `e` a choice of
`r` rows, and `h` a point of the finite unitary group of `V`. The point form `pointForm h hY e v`
is the form with vector `v` supported on the class of `h A`, where `A = pointLift hY e` is an
integral element with columns `Y i` over M and unit vectors in the rows `e` over
Q = `O.TwistIndex`. Its descent `O.normalizedDescent` (adjoint to the theta lift from `O.W`), at a
point `g` of the adelic unitary group `G E O.signs` of `O.W`, is the complex conjugate of the theta
kernel `modKernel` of the pair `(O.W, V)` at `(g, h)`, twisted by the characters `O.charW`,
`O.charV`. Its polynomial is `O.fockPoly (star v)`, the polynomial in the Fock variables attached
linearly to the conjugate weight vector. Its datum applies `pointFormDatum Y e` to the reductions
`levelResidueAt i` of a matrix modulo `O.levelModulus 2`: this is 0 unless they are `Y i` at M,
and is then the product over w in Q of `O.tamePart w`, a character of the residue field, at the
determinant of the rows `e`. -/
lemma normalizedDescent_pointForm [WeilData E] (h : Gf E n)
    {Y : ∀ i : O.ChosenIndex, Matrix n r (ResField (O.placeAt (Sum.inl i)))}
    (hY : ∀ i : O.ChosenIndex, (Y i).mulVec.Injective) (e : r ↪ n)
    (v : WeylIndex n O.columnCount → ℂ) (g : G E O.signs) :
    O.normalizedDescent (pointForm h hY e v) g = conj
      (modKernel O.W (stdSpace E n) O.charW O.charV (O.levelModulus 2)
      (fun T : Matrix n r (O.levelModulus 2).ResidueRing ↦
        pointFormDatum Y e fun i : O.ChosenIndex ⊕ O.TwistIndex ↦ T.map (levelResidueAt i))
      (O.fockPoly (star v)) g h) := by
  -- Move `A` from the argument of the kernel into the datum, which becomes `O.residueBlockDatum` of
  -- the reductions of `A⁻¹ T`, times the factor `O.charW (det A) = 1`.
  let A : stdLevel E n := pointLift hY e
  have h_red (T : Matrix n r (O.levelModulus 2).ResidueRing) (i : O.ChosenIndex ⊕ O.TwistIndex) :
      (((O.levelModulus 2).reductionGL A)⁻¹.val * T).map (levelResidueAt i) =
        (stdLevel.reduceAt (O.placeAt i) A⁻¹).val * T.map (levelResidueAt i) := by
    simp [← map_inv]
  rw [pointForm, normalizedDescent_classForm, modKernel_mul_stdLevel_right,
    show (O.charW.val (detFin 1 A.val) : ℂ) = 1 by simp, one_smul]
  simp only [h_red, A, residueBlockDatum_inv_pointLift_mul]

end New.Rows

/-! ## The adjoint of the Hecke polynomial at a split place -/

namespace New

/-- The σ-conjugate pairing `New.LevelPlaces.LevelForm.innerAt σ` on forms on V is the restriction
of a pairing `B` of all smooth forms of the same weight, semilinear for σ⁻¹ ∘ conj ∘ σ in the first
variable, that is invariant under right translation `New.Space.formTranslation`. -/
lemma DescentPair.exists_invariant_pairing_eq_innerAt {E r n : Type} [Field E] [CMType E]
    [WeilData E] [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] (O : DescentPair E r n)
    (σ : ℂ ≃+* ℂ) :
    ∃ B : (stdSpace E n).forms (O.columnCount, O.detExp)
        →ₛₗ[(↑σ⁻¹ : ℂ →+* ℂ).comp ((starRingEnd ℂ).comp (σ : ℂ →+* ℂ))]
        (stdSpace E n).forms (O.columnCount, O.detExp) →ₗ[ℂ] ℂ,
      (∀ φ φ' : O.FormV, φ.innerAt σ φ' = B φ.toSmoothForm φ'.toSmoothForm) ∧
      ∀ (g : Gf E n) (x y : (stdSpace E n).forms (O.columnCount, O.detExp)),
        B ((stdSpace E n).formTranslation (O.columnCount, O.detExp) g x)
          ((stdSpace E n).formTranslation (O.columnCount, O.detExp) g y) = B x y := by
  -- By definition `innerAt σ` is the restriction of `smoothPairing` for the Gram form `G`, times
  -- the index of the level.
  let G : (WeylIndex n O.columnCount → ℂ)
    →ₛₗ[(↑σ⁻¹ : ℂ →+* ℂ).comp ((starRingEnd ℂ).comp (σ : ℂ →+* ℂ))]
      (WeylIndex n O.columnCount → ℂ) →ₗ[ℂ] ℂ :=
    Matrix.toLinearMapₛₗ₂' ℂ _ (RingHom.id ℂ) weylGramOver
  have hG (γ : U (stdSpace E n).J) (u v : WeylIndex n O.columnCount → ℂ) :
      G ((stdSpace E n).weightRep O.columnCount O.detExp γ u)
        ((stdSpace E n).weightRep O.columnCount O.detExp γ v) =
        G u v := by
    -- After applying `σ` this is the invariance of `gramForm` on `σ`-conjugates.
    apply σ.injective
    simpa [G, Int.cast_comm, Matrix.toLinearMapₛₗ₂'_apply, gramForm_apply, dotProduct,
      Matrix.mulVec, Finset.mul_sum] using gramForm_map_weightRep σ γ u v
  refine ⟨(stdLevelIndex O.levelGroup : ℂ) • smoothPairing (κ := (O.columnCount, O.detExp)) G hG,
    fun φ φ' ↦ ?_, fun g x y ↦ by simp only [LinearMap.smul_apply, smoothPairing_formTranslation]⟩
  unfold LevelPlaces.LevelForm.innerAt
  rfl

/-- Let w ≠ w̄ be a finite place such that w and w̄ are off the level, that is, outside the places
of M and Q and their conjugates. The operator H_w(X) = `O.heckePolyOnForms` on forms on V is the
polynomial ∑ (−X)^i q^{i(i−1)/2} T_{w,i} in the Hecke operators at w, q the norm of w. Its adjoint
for the σ-conjugate pairing `New.LevelPlaces.LevelForm.innerAt` is H_{w̄}(X'), with
X' = σ⁻¹(conj(σX)). -/
lemma LevelPlaces.LevelForm.innerAt_heckePolyOnForms {E r n : Type} [Field E] [CMType E]
    [WeilData E] [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] {O : DescentPair E r n}
    (σ : ℂ ≃+* ℂ) (φ φ' : O.FormV) {w : FinPlace E} (hw : star w ≠ w)
    (hw_off : w ∉ O.places.conjClosure) (hw_star_off : star w ∉ O.places.conjClosure) (X : ℂ) :
    innerAt σ (O.heckePolyOnForms hw hw_off X φ) φ' =
      innerAt σ φ
        (O.heckePolyOnForms (star_injective.ne hw) hw_star_off (σ.symm (star (σ X))) φ') := by
  obtain ⟨B, hB_eq, hB_inv⟩ := O.exists_invariant_pairing_eq_innerAt σ
  rw [hB_eq, hB_eq]
  exact heckePolyOp_adjoint hw B (mem_sphericalAt φ hw_off) (mem_sphericalAt φ' hw_off) hB_inv X

/-!
## False lifts, denominators of lifts and the norm bound for projections

Orthogonal complements and projections refer to the inner product `innerAt 1`.
-/

namespace DescentPair

open LinearMap Complex LevelPlaces.LevelForm Submodule IsSymmetric MonoidHom Module Matrix

variable {E r n : Type} [Field E] [CMType E] [WeilData E] [Fintype r] [DecidableEq r] [Fintype n]
  [DecidableEq n] (O : DescentPair E r n)

/-- The operator by which e₀, in the group algebra of ∏_{w ∈ M} GL_r(k_w), acts on forms on V
through the representation `New.DescentPair.formAction`. -/
noncomputable abbrev groupAlgAction (e₀ : MonoidAlgebra ℂ (O.ChosenGL r)) : End ℂ O.FormV :=
  O.formAction.asAlgebraHom e₀

/-- The false lifts for a split place `w` off the level: the forms in the image of `e₀` that are
killed by the Hecke polynomial operator `H_w`, at the value `O.liftHeckeRoot w`, and lie in `Z`. In
use `Z` is the orthogonal complement of a space of lifts, or the kernel of the descent
`O.normalizedDescent`. -/
noncomputable abbrev falseLiftsAt {w : FinPlace E} (hw : star w ≠ w)
    (hS : w ∉ O.places.conjClosure) (e₀ : MonoidAlgebra ℂ (O.ChosenGL r))
    (Z : Submodule ℂ O.FormV) : Submodule ℂ O.FormV :=
  (O.groupAlgAction e₀).range ⊓ (O.heckePolyOnForms hw hS (O.liftHeckeRoot w)).ker ⊓ Z

/-- The form `y` on `V` is orthogonal to the false lifts `O.falseLiftsAt hw hS e₀ Z` for every split
place `w` off the level. -/
def IsOrthogonalToFalseLifts (e₀ : MonoidAlgebra ℂ (O.ChosenGL r)) (Z : Submodule ℂ O.FormV)
    (y : O.FormV) : Prop :=
  ∀ (w : FinPlace E) (hw : star w ≠ w) (hS : w ∉ O.places.conjClosure),
    y ∈ (O.falseLiftsAt hw hS e₀ Z)ᗮ

open scoped Classical in
/-- The form Ξ is integral above l (at every embedding ℂ → ℂ_l, all values of Ξ have gauge at
most 1: `integralForms`) and orthogonal to the false lifts
(`New.DescentPair.IsOrthogonalToFalseLifts`) for e₀ and Z. Here e₀ is `tupleIdem` at X − 1, that is,
the tensor product over w ∈ M of the idempotents `labelIdem` of GL_r(k_w) attached to the polynomial
X − 1; for W of rank one it is the mean over ∏_{w ∈ M} GL_1(k_w). The space Z is the kernel of the
descent `O.normalizedDescent`, the adjoint of the lift from W. -/
def IsTestForm (l : ℕ) [Fact l.Prime] (Ξ : O.FormV) : Prop :=
  (∀ j : PadicPlace l, Ξ ∈ integralForms j) ∧
  O.IsOrthogonalToFalseLifts (tupleIdem r fun _ : O.ChosenIndex ↦ Polynomial.X - 1)
    O.normalizedDescent.ker Ξ

/-- The `ℓ`-adic place of `ℂ` given by an isomorphism `ι : ℂ ≃ ℚ̄_ℓ`, followed by `ℚ̄_ℓ ⊆ ℂ_ℓ`. -/
noncomputable abbrev _root_.New.PadicPlace.ofIso {ℓ : ℕ} [Fact ℓ.Prime] (ι : ℂ ≃+* PadicAlgCl ℓ) :
    PadicPlace ℓ :=
  ⟨(algebraMap (PadicAlgCl ℓ) ℂ_[ℓ]).comp ι.toRingHom⟩

/-- The place `PadicPlace.ofIso ι` is `ι` followed by `ℚ̄_ℓ ⊆ ℂ_ℓ`. -/
lemma _root_.New.PadicPlace.ιₚ_ofIso {ℓ : ℕ} [Fact ℓ.Prime] (ι : ℂ ≃+* PadicAlgCl ℓ) (z : ℂ) :
    (PadicPlace.ofIso ι).ιₚ z = algebraMap (PadicAlgCl ℓ) ℂ_[ℓ] (ι z) :=
  rfl

/-- The projection `pr` to `Z` has denominator at most `exp β` per dimension and row at `ι`: there
is an operator `Λ` on `Z` with `log |ι (det Λ)| ≥ -dim Z * #r * β` such that, for every form `y`
that is integral at `ι` and has `O.IsOrthogonalToFalseLifts e₀ Zᗮ y`, the form `Λ (pr y)` is
integral at `ι`, and its inner product with every form that is integral at every embedding `ℂ → ℂ_ℓ`
has absolute value at most 1 at `ι`. A form is integral (`integralForms`) at an embedding if all its
values have gauge at most 1 there. -/
def _root_.New.Selmer.DenominatorLe {ℓ : ℕ} [Fact ℓ.Prime] (ι : ℂ ≃+* PadicAlgCl ℓ)
    (O : DescentPair E r n) (e₀ : MonoidAlgebra ℂ (O.ChosenGL r)) (Z : Submodule ℂ O.FormV)
    (β : ℝ) : Prop :=
  ∃ Λ : Module.End ℂ Z, Real.exp (-(finrank ℂ Z * (Fintype.card r * β))) ≤ ‖ι Λ.det‖ ∧
    ∀ y ∈ integralForms (PadicPlace.ofIso ι),
      O.IsOrthogonalToFalseLifts e₀ Zᗮ y →
        (Λ (Z.orthogonalProjectionOnto y) : O.FormV) ∈ integralForms (PadicPlace.ofIso ι) ∧
        ∀ y' : O.FormV, (∀ j : PadicPlace ℓ, y' ∈ integralForms j) →
          ‖ι (inner ℂ y' (Λ (Z.orthogonalProjectionOnto y) : O.FormV))‖ ≤ 1

omit [WeilData E] [DecidableEq n] in
/-- For g in ∏_{w ∈ M} GL_r(k_w), the number ∏_w χ_w(det g_w) is a root of unity, where
χ_w = `O.tamePart w` is the tame part at w of the character μ of `O`, a character of the residue
field k_w. -/
lemma isOfFinOrder_prod_tamePart_det (g : O.ChosenGL r) :
    IsOfFinOrder (∏ i : O.ChosenIndex, O.tamePart (O.chosenPlace i) (g i).val.det) :=
  (CommMonoid.torsion ℂ).prod_mem fun i _ ↦
    isOfFinOrder (O.tamePart (O.chosenPlace i)).toMonoidHom (g i).det.isUnit.isOfFinOrder

/-- Let M = `O.ChosenIndex` be the set of chosen places w of the pair, with residue fields k_w, and
ψ_w = `O.tamePart w` the tame part at w of the character μ of `O`, a character of k_w. In the
action `O.formAction` of ∏_{w ∈ M} GL_r(k_w) on forms on V, an element g acts as ∏_w ψ_w(det g_w)
times right translation by an integral element that reduces at each w in M to the matrix equal to
g_w on the indices `O.incl` and to 1 on the others, and to 1 at the places of Q. For every
automorphism σ of ℂ this action preserves the σ-conjugate pairing: ⟨gx, gy⟩_σ = ⟨x, y⟩_σ. -/
lemma innerAt_formAction (σ : ℂ ≃+* ℂ) (g : O.ChosenGL r) (x y : O.FormV) :
    innerAt σ (O.formAction g x) (O.formAction g y) = innerAt σ x y := by
  -- `O.formAction g` is a translation `T` times a root of unity `c`.
  let c : ℂ := ∏ i : O.ChosenIndex, O.tamePart (O.chosenPlace i) (g i).val.det
  let T : End ℂ ((stdSpace E n).forms (O.columnCount, O.detExp)) :=
    (stdSpace E n).formTranslation (O.columnCount, O.detExp)
      (liftResidue (firstBlockHom O.toLevelPlaces O.incl g))
  have h_act (z : O.FormV) : (O.formAction g z).toSmoothForm = c • T z.toSmoothForm := rfl
  have h_norm : ‖σ c‖ = 1 :=
    (isOfFinOrder σ.toMonoidHom (O.isOfFinOrder_prod_tamePart_det g)).norm_eq_one
  have h_unit : σ.symm (star (σ c)) * c = 1 := by
    apply σ.injective
    simp [conj_mul', h_norm]
  obtain ⟨B, hB_eq, hB_inv⟩ := O.exists_invariant_pairing_eq_innerAt σ
  calc innerAt σ (O.formAction g x) (O.formAction g y)
      = (σ.symm (star (σ c)) * c) • B (T x.toSmoothForm) (T y.toSmoothForm) := by
        rw [hB_eq, h_act, h_act, map_smulₛₗ₂, LinearMap.map_smul, smul_smul]
        rfl
    _ = innerAt σ x y := by rw [h_unit, one_smul, hB_inv, hB_eq]

omit [WeilData E] in
/-- An operator f on forms on V that commutes with the action `New.DescentPair.formAction` of
∏_{w ∈ M} GL_r(k_w) preserves the image of every element e₀ of the group algebra. -/
lemma range_groupAlgAction_mem_invtSubmodule {e₀ : MonoidAlgebra ℂ (O.ChosenGL r)}
    {f : End ℂ O.FormV} (h_comm : ∀ g : O.ChosenGL r, Commute f (O.formAction g)) :
    (O.groupAlgAction e₀).range ∈ End.invtSubmodule f := by
  have : Fintype (O.ChosenGL r) := Fintype.ofFinite _
  rintro _ ⟨y, rfl⟩
  have h_apply (g : O.ChosenGL r) : f (O.formAction g y) = O.formAction g (f y) :=
    LinearMap.congr_fun (h_comm g).eq y
  -- `O.groupAlgAction e₀` is a linear combination of the `O.formAction g`.
  have h_alg : O.groupAlgAction e₀ (f y) = f (O.groupAlgAction e₀ y) := by
    simp [asAlgebraHom_eq_sum, h_apply]
  exact ⟨f y, h_alg⟩

omit [WeilData E] in
/-- The Hecke polynomial operators `New.DescentPair.heckePolyOnForms` at two split places w and u
off the level commute: H_w(X) H_u(Y) y = H_u(Y) H_w(X) y for all complex X, Y and all forms y on V.
The places may be equal or conjugate. -/
lemma heckePolyOnForms_comm {w : FinPlace E} (hw : star w ≠ w) (hw_off : w ∉ O.places.conjClosure)
    {u : FinPlace E} (hu : star u ≠ u) (hu_off : u ∉ O.places.conjClosure) (X Y : ℂ) (y : O.FormV) :
    O.heckePolyOnForms hw hw_off X (O.heckePolyOnForms hu hu_off Y y) =
      O.heckePolyOnForms hu hu_off Y (O.heckePolyOnForms hw hw_off X y) := by
  -- Both sides are double sums of products of Hecke operators at `w` and `u`, which commute on
  -- `y` since it is spherical at both places.
  let π : Representation ℂ (Gf E n)
      (SmoothForm (stdSpace E n).embFin ((stdSpace E n).weightRep O.columnCount O.detExp)) :=
    algFormRep O.columnCount O.detExp
  have h_comm (i j : ℕ) :
      heckeSplit π hw i (heckeSplit π hu j y.val) = heckeSplit π hu j (heckeSplit π hw i y.val) :=
    heckeSplit_comm hw hu i j (y.mem_sphericalAt hw_off) (y.mem_sphericalAt hu_off)
  apply Subtype.ext
  change heckePolyOp π hw X (heckePolyOp π hu Y y.val) =
    heckePolyOp π hu Y (heckePolyOp π hw X y.val)
  simpa [heckePolyOp, heckePolyEval, Finset.smul_sum, smul_smul, h_comm, mul_comm] using
    Finset.sum_comm

/-- A central idempotent e₀ of the group algebra of ∏_{w ∈ M} GL_r(k_w) acts on forms on V
self-adjointly for the pairing `innerAt σ`, for every σ: ⟨e₀x, y⟩_σ = ⟨x, e₀y⟩_σ. -/
lemma innerAt_groupAlgAction {e₀ : MonoidAlgebra ℂ (O.ChosenGL r)} (he : IsCentralProj e₀)
    (σ : ℂ ≃+* ℂ) (x y : O.FormV) :
    innerAt σ (O.groupAlgAction e₀ x) y = innerAt σ x (O.groupAlgAction e₀ y) := by
  have : Fintype (O.ChosenGL r) := Fintype.ofFinite _
  exact he.self_adjoint O.formAction σ (innerAt σ) (O.innerAt_formAction σ) x y

/-- The Hecke polynomial operator H_w(X) at a split place w off the level is normal for the pairing
`innerAt σ`: it has an adjoint `A'` with which it commutes. -/
lemma exists_adjoint_heckePolyOnForms_comm {w : FinPlace E} (hw : star w ≠ w)
    (hw_off : w ∉ O.places.conjClosure) (X : ℂ) (σ : ℂ ≃+* ℂ) :
    ∃ A' : End ℂ O.FormV,
      (∀ x y : O.FormV, innerAt σ (O.heckePolyOnForms hw hw_off X x) y = innerAt σ x (A' y)) ∧
      ∀ x : O.FormV,
        O.heckePolyOnForms hw hw_off X (A' x) = A' (O.heckePolyOnForms hw hw_off X x) := by
  have hw_star_off : star w ∉ O.places.conjClosure := by
    simpa [Set.conjClosure, and_comm] using hw_off
  exact ⟨O.heckePolyOnForms (star_injective.ne hw) hw_star_off (σ.symm (star (σ X))),
    fun x y ↦ innerAt_heckePolyOnForms σ x y hw hw_off hw_star_off X,
    O.heckePolyOnForms_comm hw hw_off (star_injective.ne hw) hw_star_off X _⟩

/-- The image of the Hecke polynomial operator H_w(X) is orthogonal to its kernel for the pairing
`innerAt σ`. -/
lemma innerAt_heckePolyOnForms_eq_zero {w : FinPlace E} (hw : star w ≠ w)
    (hw_off : w ∉ O.places.conjClosure) (X : ℂ) (σ : ℂ ≃+* ℂ) {z : O.FormV}
    (hz : O.heckePolyOnForms hw hw_off X z = 0) (v : O.FormV) :
    innerAt σ (O.heckePolyOnForms hw hw_off X v) z = 0 := by
  obtain ⟨A', h_adj, h_comm⟩ := O.exists_adjoint_heckePolyOnForms_comm hw hw_off X σ
  have h_self : innerAt σ (A' z) (A' z) = 0 := by
    simp [← h_adj, h_comm, hz]
  rw [h_adj, eq_zero_of_innerAt_self σ (A' z) h_self, map_zero]

/-- A form orthogonal to the image of the Hecke polynomial operator H_w(X) lies in its kernel. -/
lemma orthogonal_range_heckePolyOnForms_le_ker {w : FinPlace E} (hw : star w ≠ w)
    (hw_off : w ∉ O.places.conjClosure) (X : ℂ) :
    (O.heckePolyOnForms hw hw_off X).rangeᗮ ≤ (O.heckePolyOnForms hw hw_off X).ker := by
  intro u hu
  obtain ⟨A', h_adj, h_comm⟩ := O.exists_adjoint_heckePolyOnForms_comm hw hw_off X 1
  have h_orth : innerAt 1 u (O.heckePolyOnForms hw hw_off X (A' u)) = 0 :=
    inner_left_of_mem_orthogonal (mem_range_self _ (A' u)) hu
  exact eq_zero_of_innerAt_self 1 _ (by rw [h_adj, ← h_comm, h_orth])

omit [WeilData E] in
/-- The squared norm ‖v‖²_σ = `normSqAt v σ`, defined as the class sum of the squared Gram norms of
the vectors σ(v(g)), is the real part of σ(⟨v, v⟩_σ), where ⟨v, v⟩_σ = `innerAt σ v v`. -/
lemma normSqAt_eq_re_innerAt (v : O.FormV) (σ : ℂ ≃+* ℂ) :
    normSqAt v σ = re (σ (innerAt σ v v)) := by
  have h_sum : σ (innerAt σ v v) =
      stdClassSum O.levelGroup fun g : Gf E n ↦ gramForm (σ ∘ v g) (σ ∘ v g) :=
    (congrArg σ (innerAt_eq_stdClassSum σ v v)).trans (σ.apply_symm_apply _)
  rw [h_sum]
  exact (map_classSum reLm _).symm

omit [WeilData E] in
/-- If ⟨x, z⟩_σ = 0, then ‖z‖²_σ ≤ ‖z + x‖²_σ for the squared norm `normSqAt`, the class sum of the
squared Gram norms of the σ-conjugated values of a form. -/
lemma normSqAt_le_add_of_innerAt_eq_zero {σ : ℂ ≃+* ℂ} {x z : O.FormV}
    (h_orth : innerAt σ x z = 0) : normSqAt z σ ≤ normSqAt (z + x) σ := by
  have h_orth' : innerAt σ z x = 0 := by simp [← conj_innerAt σ z x, h_orth]
  have h_pythagoras : normSqAt (z + x) σ = normSqAt z σ + normSqAt x σ := by
    simp [normSqAt_eq_re_innerAt, h_orth, h_orth']
  linarith [show 0 ≤ normSqAt x σ from finsum_nonneg fun c ↦ by simp [smul_nonneg]]

/-- Let e₀ be a central idempotent of the group algebra of ∏_{v ∈ M} GL_r(k_v), M the chosen places
of the pair, acting on forms on V through `O.formAction`, and let Z be a space of forms. For a place
w ≠ w̄ off the level let H_w(X_*) be the Hecke polynomial operator at the explicit number
X_* = `O.liftHeckeRoot w`, built from the norm of w and a character of the Weil data. A false lift
for e₀ and Z^⊥ is a form in Z^⊥ and in the image of e₀ that such an operator kills. If y is
orthogonal to all false lifts, then for every such w it lies in the sum of Z, the kernel of e₀ and
the image of H_w(X_*). -/
lemma mem_sup_ker_sup_range_of_isOrthogonalToFalseLifts {w : FinPlace E} (hw : star w ≠ w)
    (hw_off : w ∉ O.places.conjClosure) {e₀ : MonoidAlgebra ℂ (O.ChosenGL r)}
    {Z : Submodule ℂ O.FormV} (he : IsCentralProj e₀) {y : O.FormV}
      (hy : O.IsOrthogonalToFalseLifts e₀ Zᗮ y) :
    y ∈ Z ⊔
      ((O.groupAlgAction e₀).ker ⊔ (O.heckePolyOnForms hw hw_off (O.liftHeckeRoot w)).range) := by
  -- As e₀ is self-adjoint and A = H_w(X_*) is normal, a form orthogonal to ker e₀ + range A lies in
  -- range e₀ ∩ ker A; if it is also orthogonal to Z, it is a false lift.
  set A : End ℂ O.FormV := O.heckePolyOnForms hw hw_off (O.liftHeckeRoot w)
  have h_symm : (O.groupAlgAction e₀).IsSymmetric := O.innerAt_groupAlgAction he 1
  have h_le : (Z ⊔ ((O.groupAlgAction e₀).ker ⊔ A.range))ᗮ ≤ O.falseLiftsAt hw hw_off e₀ Zᗮ := by
    intro u hu
    obtain ⟨huZ, hu_e, hu_range⟩ : u ∈ Zᗮ ∧ u ∈ (O.groupAlgAction e₀).range ∧ u ∈ A.rangeᗮ := by
      simpa only [← inf_orthogonal, ← h_symm.orthogonal_range, orthogonal_orthogonal, mem_inf]
        using hu
    exact ⟨⟨hu_e, O.orthogonal_range_heckePolyOnForms_le_ker hw hw_off _ hu_range⟩, huZ⟩
  rw [← orthogonal_orthogonal (Z ⊔ _)]
  exact orthogonal_le h_le (hy w hw hw_off)

/-- Let e₀ be a central idempotent of the group algebra of ∏_{v ∈ M} GL_r(k_v), M the chosen places
of the pair: an idempotent whose coefficients form a class function. Let Z be a space of forms in
the image of e₀ killed by the Hecke polynomial operator H_w(X) = ∑ (−X)^i q^{i(i−1)/2} T_{w,i} at
the explicit number X = X_* = `O.liftHeckeRoot w`, for one place w ≠ w̄ off the level, q its norm.
Let y be orthogonal to the false lifts. Then the orthogonal projection of y to Z (for σ = 1) has
squared norm `normSqAt` at most that of y, at every σ. -/
lemma normSqAt_starProjection_le {w : FinPlace E} (hw : star w ≠ w)
    (hw_off : w ∉ O.places.conjClosure) {e₀ : MonoidAlgebra ℂ (O.ChosenGL r)}
    {Z : Submodule ℂ O.FormV} (he : IsCentralProj e₀)
    (hZ : Z ≤ (O.groupAlgAction e₀).range ⊓
      (O.heckePolyOnForms hw hw_off (O.liftHeckeRoot w)).ker)
    {y : O.FormV} (hy : O.IsOrthogonalToFalseLifts e₀ Zᗮ y) (σ : ℂ ≃+* ℂ) :
    normSqAt (Z.starProjection y) σ ≤ normSqAt y σ := by
  -- Write y = z + x with z in Z and x in ker e₀ + range A, where A = H_w(X_*). This space is
  -- orthogonal to range e₀ ∩ ker A, so to Z, at every σ. Hence z is the projection of y, and
  -- Pythagoras applies at σ.
  set A : End ℂ O.FormV := O.heckePolyOnForms hw hw_off (O.liftHeckeRoot w)
  obtain ⟨z, hz, x, hx, rfl⟩ : ∃ z ∈ Z, ∃ x ∈ (O.groupAlgAction e₀).ker ⊔ A.range, z + x = y :=
    mem_sup.mp (O.mem_sup_ker_sup_range_of_isOrthogonalToFalseLifts hw hw_off he hy)
  have h_orth (τ : ℂ ≃+* ℂ) (z' : O.FormV) (hz' : z' ∈ Z) : innerAt τ x z' = 0 := by
    obtain ⟨⟨u, rfl⟩, hAz : A (O.groupAlgAction e₀ u) = 0⟩ := hZ hz'
    obtain ⟨k, hk : O.groupAlgAction e₀ k = 0, _, ⟨v, rfl⟩, rfl⟩ :
        ∃ k ∈ (O.groupAlgAction e₀).ker, ∃ m ∈ A.range, k + m = x := mem_sup.mp hx
    have h_ker : innerAt τ k (O.groupAlgAction e₀ u) = 0 := by
      rw [← O.innerAt_groupAlgAction he, hk, LinearMap.map_zero₂]
    have h_range : innerAt τ (A v) (O.groupAlgAction e₀ u) = 0 :=
      O.innerAt_heckePolyOnForms_eq_zero hw hw_off _ τ hAz v
    rw [LinearMap.map_add₂, h_ker, h_range, add_zero]
  have h_proj : Z.starProjection (z + x) = z :=
    eq_starProjection_of_mem_of_inner_eq_zero hz fun z' hz' ↦ by
      rw [add_sub_cancel_left]
      exact h_orth 1 z' hz'
  rw [h_proj]
  exact O.normSqAt_le_add_of_innerAt_eq_zero (h_orth σ z hz)

end DescentPair

end New
