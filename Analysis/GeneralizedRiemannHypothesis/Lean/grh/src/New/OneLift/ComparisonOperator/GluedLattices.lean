import New.OneLift.ComparisonOperator.OneExchange
import New.OneLift.TestedForms

/-!
# Gluing: residue rings, divided lattices, the congruence group and glued lattices

This file sets up the change of lattice at the chosen places for a divided splitting
`V : New.Rows.DividedSplitting N m a O z` of `V = V″ ⊕ V°`. It introduces the residue rings
modulo `ϖ²` and `ϖ²Q`, the conjugate kernel vector and the kernel summed over classes. It then
defines divided lattices, the congruence group of matrices that are `1` modulo `ϖ`, and product
forms. It constructs, for every matrix `s` modulo `ϖ²`, a lattice glued for `s`, and writes the
datum of the lift at `γ⁻¹ x` as a sum over the congruence group.

Here `O` is a descent pair with the space `W = O.W` of rank `r`. `N` indexes `V″`, `m` indexes
`V°`, `z : r ↪ m` marks `r` basis vectors of `V°`, and `a` indexes the rows of a matrix `s` modulo
`ϖ²`, the linear forms on `V″` on which a finer congruence is imposed. The idele `ϖ = O.genIdele`
generates the product of the chosen places `O.chosenPlace i`, and `Q` is the product of the places
`O.twistPlace i`. We write `(1; 0)` for an inclusion matrix `New.inclMatrix` with `r` columns.
The datum of the theta lift from `W` to `V` asks for `x ≡ (1; 0)` modulo `ϖ`. A product datum asks
for conditions modulo `ϖ²` on the two blocks of `x`. The lattice that connects them is spanned by
the columns of the matrix that is `(1; 0)` on both summands, by `L″_s = {u | s u ≡ 0 modulo ϖ}` in
`V″` and by `ϖ` times the standard lattice of `V°`. The matrix of a basis is called `γ`, and it is
handled through the integral matrix `ϖ γ⁻¹`.

## Main definitions and results

* `New.Rows.DividedLattice`, `New.Rows.DividedLattice.reducedInverse`: a point `γ` of G_f supported
  at the chosen places such that `ϖ γ⁻¹` is integral, and the reduction of `ϖ γ⁻¹` modulo `ϖ²`.
* `New.Rows.DividedSplitting.congruenceGroup`: the invertible `r × r` matrices modulo `ϖ²` that are
  `1` modulo `ϖ`.
* `New.Rows.DividedSplitting.productForm`: the form supported on the class of `(h, h°) γ` with the
  product of two vectors as its value. The product of vectors is `New.Rows.cartanProduct`.
* The datum. `New.Rows.DividedSplitting.exists_isGlued`: for every `s` there is a lattice glued for
  `s`. `New.Rows.DividedSplitting.IsGlued.indicator_eq_sum`: the datum of the lift at `γ⁻¹ x` is the
  sum of the translates of the product datum under the congruence group.

Notions from other files:
* `New.DescentPair`: A descent pair: chosen places and twist places, a space W of rank r with
  numbered basis vectors, an embedding of indices into n > r, two diagrams given by their numbers of
  columns of each height, and a character μ whose tame part, a character `O.tamePart w` of the
  residue field at each place w, is trivial off these places.
* `New.LevelPlaces.levelModulus`: `levelModulus c` is the modulus ϖ^c·Q, and `levelModulus c false`
  is ϖ^c.
* `New.inclMatrix`: For a map u: m → n of index sets, the n×m matrix whose j-th column is the
  standard basis vector e_{u(j)}.
* `New.Rows.liftMod`: A chosen lift of an invertible matrix modulo an ideal to an integral point of
  G_f that is 1 outside the places dividing the ideal and their conjugates.
-/

noncomputable section

namespace New.Rows

/-!
## Residue rings modulo ϖ² and ϖ²Q and the divided splitting

* `New.Rows.DividedSplitting.genResidue_smul_eq_inclMatrix_iff`: a matrix agrees with an inclusion
  matrix modulo `ϖ²` after multiplication by `ϖ` exactly when they agree at every chosen place.
-/

section DividedSplitting

open Matrix NumberField Ideal Modulus Set Gf Sum LevelPlaces Quotient

section

variable {E r n N m a : Type} [Field E] [NumberField E] [IsCMField E] [Fintype r] [DecidableEq r]
  [Fintype n] [DecidableEq n] [Fintype N] [Fintype m] {S : LevelPlaces E}

/-- The modulus `ϖ²`, the square of the product of the chosen places of `S`. -/
abbrev _root_.New.LevelPlaces.chosenModulusSq (S : LevelPlaces E) : Modulus E :=
  S.levelModulus 2 false

/-- The block diagonal matrix of two integral unitary matrices, reindexed by `ε`, is integral. Its
reduction along a homomorphism `f` from the integral finite adeles is the block diagonal matrix of
the two reductions. -/
lemma map_block_eq_blockGL [DecidableEq m] [DecidableEq N] {R : Type*} [CommRing R] (f : Ô E →+* R)
    (ε : N ⊕ m ≃ n) (k : stdLevel E N) (l : stdLevel E m) :
    ∃ h, stdLevel.map (S := R) n f ⟨U.block ε (k, l), h⟩ =
      reindexGL ε (blockGL (stdLevel.map N f k, stdLevel.map m f l)) := by
  -- Compare entries, indexed through `ε` by the indices of the two blocks.
  refine ⟨?_, ?_⟩
  · simp [mem_stdLevel, mem_stdLevel.1, reindex_equiv ε]
  · simp [Units.ext_iff, ← ext_iff, reindex_equiv ε, ← ZeroMemClass.zero_def]

/-- The ideal `ϖ² Q` is contained in `ϖ²`, where `ϖ` generates the product of the chosen places
and `Q` is the product of the twist places of `S`. -/
lemma levelModulus_ideal_le : (S.levelModulus 2).ideal ≤ S.chosenModulusSq.ideal :=
  mul_mono_right (by simp)

/-- For `c ≠ 0`, the places dividing the `c`-th power of the product of the chosen places of `S`
are the chosen places. -/
lemma places_levelModulus_false {c : ℕ} [NeZero c] :
    (S.levelModulus c false).places = range S.chosenPlace := by
  ext w
  simp [Modulus.places, levelModulus, IsPrime.pow_le_iff, NeZero.ne, prod_places_le_iff]

/-- The reduction homomorphism from the residue ring modulo `ϖ² Q` to that modulo `ϖ²`. -/
abbrev reduceToChosenModulusSq : (S.levelModulus 2).ResidueRing →+* S.chosenModulusSq.ResidueRing :=
  factor levelModulus_ideal_le

/-- The chosen lift `liftMod B` to G_f of an invertible matrix `B` modulo `ϖ²` is supported at the
chosen places of `S`, whose product `ϖ` generates. -/
lemma liftMod_mem_supportedOn (B : GL n S.chosenModulusSq.ResidueRing) :
    ↑(liftMod B) ∈ supportedOn n (range S.chosenPlace) := by
  grind [places_levelModulus_false, liftMod]

end

variable {E r n : Type} (N m a : Type) [Field E] [CMType E] [Fintype r] [DecidableEq r] [Fintype n]
  [Fintype N] [Fintype m] {S : LevelPlaces E} (O : DescentPair E r n)

/-- A point `k` of G_f supported at the chosen places of `S` is `1` at every twist place of `S`. -/
lemma atPlace_twistPlace_eq_one [DecidableEq n]
    {k : Gf E n} (hk : k ∈ supportedOn n (range S.chosenPlace))
    (i : S.TwistIndex) : k.atPlace (S.twistPlace i) = 1 := by
  obtain ⟨h_inj, h_conj⟩ := S.apart
  -- Neither `S.twistPlace i` nor its conjugate is one of the places `S.chosenPlace j`.
  have h_ne (j : S.ChosenIndex) :
      S.chosenPlace j ≠ S.twistPlace i ∧ S.chosenPlace j ≠ star (S.twistPlace i) :=
    ⟨fun h ↦ Sum.inl_ne_inr (h_inj (a₁ := inl j) (a₂ := inr i) h),
      (h_conj (inr i) (inl j)).symm⟩
  simp_all

/-! ### The splitting and the generator `ϖ` -/

/-- A splitting `N ⊕ m ≃ n` of the indices of `V = V″ ⊕ V°` with embeddings of `r` and of `a` in
`N`, with `O.incl` landing in `N` through the embedding of `r`. The diagram `O.colsPlus` for `V″`
and the diagram `O.colsMinus` for `V°` satisfy `New.Rows.HasColumnsBelow`: each column of height
below the rank of `V` has height below the rank of the summand. -/
structure DividedSplitting (z : r ↪ m) extends ε : N ⊕ m ≃ n where
  /-- The `r` indices of `V″` that form the top block of a datum. -/
  fixedEmb : r ↪ N
  /-- The embedding `O.incl` lands in `V″`, where it is given by `fixedEmb`. -/
  equiv_inl_fixedEmb (i : r) : ε (inl (fixedEmb i)) = O.incl i
  /-- As many indices of `V″` as `a` has elements. After a change of basis these are the directions
  in which the lattice of `V″` is made smaller. -/
  dividedEmb : a ↪ N
  /-- The diagram `O.colsPlus` has no column of a height `h` with `#N ≤ h < #n`, and `O.colsMinus`
  none with `#m ≤ h < #n`. -/
  hasColumnsBelow : HasColumnsBelow n N O.colsPlus ∧ HasColumnsBelow n m O.colsMinus

/-- The integral idele `ϖ` that generates the product of the chosen places of `O`. It equals `1` at
all other places. -/
def _root_.New.DescentPair.genIdele : (𝔸f E)ˣ := (O.levelModulus 1 false).generator

/-- The idele `ϖ = O.genIdele` as an element of the ring `Ô E` of integral finite adeles. -/
abbrev _root_.New.DescentPair.genIntAdele : Ô E :=
  ⟨O.genIdele, (generator_spec (O.levelModulus 1 false)).1⟩

variable {N m a O} {z : r ↪ m}

lemma genIdele_apply_of_notMem {w : FinPlace E} (hw : w ∉ range O.chosenPlace) :
    O.genIdele.val w = 1 := by
  obtain ⟨-, h_one, -⟩ := generator_spec (O.levelModulus 1 false)
  exact h_one w (by rwa [places_levelModulus_false])

/-- An integral finite adele `x` is `0` modulo the `c`-th power of the product of the chosen places
(the modulus `O.levelModulus c false`, where `false` leaves out the twist places) if and only if
`ϖ⁻¹ ^ c * x` is integral, where `ϖ = O.genIdele` generates that product. -/
lemma reduction_levelModulus_eq_zero_iff {c : ℕ} {x : Ô E} :
    (O.levelModulus c false).reduction x = 0 ↔ O.genIdele⁻¹.val ^ c * x ∈ Ô E := by
  obtain ⟨-, -, h_reduction⟩ := generator_spec (O.levelModulus c false)
  -- The product `I` of the chosen places is not `0`, as `I Q ≠ 0`. So the multiplicity of a prime
  -- in `I ^ c` is `c` times that in `I`.
  have h_val (w : FinPlace E) : Valued.v ((O.levelModulus c false).generator⁻¹.val w) =
      Valued.v (O.genIdele⁻¹.val w) ^ c := by
    have h_mult : multiplicity w.asIdeal (O.levelModulus c false).ideal =
        c * multiplicity w.asIdeal (O.levelModulus 1 false).ideal := by
      have := (O.levelModulus 1).ne_bot
      simp_all [levelModulus, FiniteMultiplicity.multiplicity_pow,
        FiniteMultiplicity.of_prime_left, w.prime]
    simp [DescentPair.genIdele, idele_inv_apply_and_ne_zero, valued_generator, h_mult]
  simp [h_reduction, mem_Ô, h_val]

namespace DividedSplitting

/-- The class modulo `ϖ²` of the idele `ϖ = O.genIdele`, which generates the product of the places
`O.chosenPlace i`. It depends on `O` only. The argument allows the notation `V.genResidue`. -/
abbrev genResidue (_ : DividedSplitting N m a O z) : O.chosenModulusSq.ResidueRing :=
  O.chosenModulusSq.reduction O.genIntAdele

/-- Let `T` be a matrix modulo `ϖ² Q = O.levelModulus 2`, with `Q` the product of the twist places,
and let `inclMatrix _ u` be the matrix whose `j`-th column is the basis vector `u j`. Then `ϖ T` and
`ϖ • inclMatrix _ u` agree modulo `ϖ²` if and only if `T` reduces to that inclusion matrix in the
residue field of every chosen place, the place of index `inl i` among the chosen and the twist
places. -/
lemma genResidue_smul_eq_inclMatrix_iff (V : DividedSplitting N m a O z) [DecidableEq n]
    {k c : Type} [DecidableEq k] (T : Matrix k c (O.levelModulus 2).ResidueRing) (u : c → k) :
    V.genResidue • T.map reduceToChosenModulusSq =
        V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing u ↔
      ∀ i : O.ChosenIndex,
        T.map (levelResidueAt (inl i)) =
          inclMatrix (ResField ((O.chosenPlace ⊕ᵥ O.twistPlace) (inl i))) u := by
  -- Write `T = inclMatrix u + X` with `X` integral.
  choose X hX using show ∀ (a : k) (b : c), ∃ x : Ô E,
      inclMatrix (O.levelModulus 2).ResidueRing u a b + (O.levelModulus 2).reduction x = T a b from
    fun a b ↦ ((add_left_surjective _).comp (reduction_surjective _)) (T a b)
  -- Chinese remainder theorem: `X ≡ 0` modulo `ϖ` iff `X` vanishes at every place
  -- `O.chosenPlace i`.
  have h_crt : (∀ a b, (O.levelModulus 1 false).reduction (X a b) = 0) ↔
      ∀ i a b, Valued.v ((X a b).val (O.chosenPlace i)) < 1 := by
    simpa [← ext_iff] using matrix_eq_iff_map_modulusResidue_eq O.isConjApart_chosenPlace.injective
      O.ideal_levelModulus_one_false (x := (of X).map (O.levelModulus 1 false).reduction) (y := 0)
  -- Both `ϖ X ≡ 0` modulo `ϖ²` and `X ≡ 0` modulo `ϖ` say that `ϖ⁻¹ X` is integral.
  have h_smul_iff :
      V.genResidue • T.map reduceToChosenModulusSq =
          V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing u ↔
        ∀ a b, (O.levelModulus 1 false).reduction (X a b) = 0 := by
    simp [inclMatrix, apply_ite reduceToChosenModulusSq, ← ext_iff, ← hX, ← map_mul,
      reduction_levelModulus_eq_zero_iff, sq, mul_add, mul_assoc, Matrix.one_apply]
  have h_levelResidueAt_iff (i : O.ChosenIndex) :
      T.map (levelResidueAt (inl i)) =
          inclMatrix (ResField ((O.chosenPlace ⊕ᵥ O.twistPlace) (inl i))) u ↔
        ∀ a b, Valued.v ((X a b).val (O.chosenPlace i)) < 1 := by
    simp [inclMatrix, apply_ite (levelResidueAt (inl i)), ← ext_iff, ← hX, Matrix.one_apply,
      -elim_inl]
    -- The place at the index `inl i` is `O.chosenPlace i` by definition.
    rfl
  simp only [h_smul_iff, h_crt, h_levelResidueAt_iff]

end DividedSplitting

end DividedSplitting

/-!
## The conjugate kernel vector and the kernel summed over classes

The theta kernels (`New.modKernelStdSpace`) of the space `O.W` of a descent pair `O`
(`New.DescentPair`) with the standard definite space `I_m` on the indices `m` are packaged in two
ways.

* `New.Rows.kernelVector`: the vector of conjugate kernels for a basis of polynomials in the columns
  of sign `-1`. It is used for `V°`.
* `New.Rows.kernelClassSum`: the kernel with the polynomial of a vector `y h` in the columns of sign
  `1`, summed over the classes `h` of level `New.Rows.rowFixingLevel`. It is used for `V″`.

`New.fockLetters` and `New.letterPoly` substitute for each variable the sum of the variables at the
basis vectors of `O.W` of a given sign and number.
-/

section MemberKernels

variable {E r n m : Type} [Field E] [CMType E] [Fintype r] [DecidableEq r] [Fintype n] [Fintype m]
  [DecidableEq m] [WeilData E] (O : DescentPair E r n) (b : AutChar E)

/-- The vector whose i-th coordinate is the conjugate theta kernel of (W, I_m) at (g, h), with
datum Ψ modulo 𝔪 and the basis polynomial `nablaBasis ℂ _ κ i` of weight κ put into the columns of
sign `-1`. The characters `O.charW` and `b` of U(1)(𝔸) are those that the kernel takes for W and for
I_m. -/
def kernelVector (𝔪 : Modulus E) (Ψ : Matrix m r 𝔪.ResidueRing → ℂ)
    (κ : NumberField.InfinitePlace E → ℕ → ℕ) (g : G E O.signs) (h : Gf E m)
    (i : WeylIndex m κ) : ℂ :=
  star (modKernelStdSpace O.W O.charW b 𝔪 Ψ
    (fockLetters O.signs O.numbering (-1) (nablaBasis ℂ _ κ i))
    g h)

/-- The level that fixes the rows `w`: the integral points (elements of `stdLevel E m`) whose
reduction modulo `ϖ² Q` has the columns of the identity matrix off `e`, and whose reduction `A`
modulo `ϖ²` satisfies `w A = w`. Here `ϖ` generates the product of the chosen places of `S`, and `Q`
is the product of its twist places. -/
abbrev rowFixingLevel {c : Type} (S : LevelPlaces E) (w : Matrix c m S.chosenModulusSq.ResidueRing)
    (e : r ↪ m) : Subgroup (Gf E m) :=
  (S.levelModulus 2).levelOfSubgroup (rowStabilizer reduceToChosenModulusSq w e)

/-- The sum, over the classes h of level `New.Rows.rowFixingLevel` for `w` and `e`, of the theta
kernel of (W, I_m) at (g, h), with the characters `O.charW` of W and `b` of I_m. The polynomial is
that of y(h) in the columns of sign `1`. The datum `columnDatum` at `σ` modulo `ϖ² Q` is
`χ (det of the rows e of σ)` if `w σ ≡ w (1; 0)` modulo `ϖ²` and `0` otherwise, where `χ`, the
`charOfTamePart`, is the product of the characters `O.tamePart w` of the residue fields at the
places. -/
def kernelClassSum {c : Type} (w : Matrix c m O.chosenModulusSq.ResidueRing) (e : r ↪ m)
    (y : Gf E m → WeylIndex m O.colsPlus → ℂ) (g : G E O.signs) : ℂ :=
  stdClassSum (rowFixingLevel O.toLevelPlaces w e) fun h ↦
    modKernelStdSpace O.W O.charW b (O.levelModulus 2)
      (columnDatum (Modulus.charOfTamePart (O.levelModulus 2) O.tamePart) reduceToChosenModulusSq w
        e)
      (letterPoly O.signs O.numbering 1 O.colsPlus (y h)) g h

end MemberKernels

/-! ## Divided lattice points, the congruence group and product forms -/

section GluedForms

open Matrix Sum Set Finset Gf Units Modulus

variable {E r n N m a : Type} [Field E] [CMType E] [Fintype r] [DecidableEq r] [Fintype n]
  [DecidableEq n] [Fintype N] [DecidableEq N] [Fintype m] [DecidableEq m] [Fintype a]
  {O : DescentPair E r n} {z : r ↪ m}

variable (O) in
/-- A lattice `γ 𝒪ⁿ`, where `γ` is the field `point`, with `ϖ 𝒪ⁿ ⊆ γ 𝒪ⁿ ⊆ 𝒪ⁿ` at the chosen places,
where `ϖ = O.genIdele`. The one condition, that `ϖ γ⁻¹` is integral, gives the first inclusion; read
at the conjugate places, it gives the second by unitarity. -/
structure DividedLattice where
  /-- The point of G_f. -/
  point : Gf E n
  /-- The point is supported on the chosen places. -/
  mem_supportedOn : point ∈ supportedOn n (Set.range O.chosenPlace)
  /-- The entries of `ϖ γ⁻¹` are integral. -/
  mul_inv_mem (a b : n) : O.genIdele * point⁻¹.val.val a b ∈ Ô E

/-- The reduction modulo `ϖ²` of the integral matrix `ϖ γ⁻¹`. -/
def DividedLattice.reducedInverse (L : DividedLattice O) :
    Matrix n n O.chosenModulusSq.ResidueRing :=
  of fun a b : n ↦ O.chosenModulusSq.reduction
    ⟨O.genIdele * L.point⁻¹.val.val a b, L.mul_inv_mem a b⟩

/-- The scalar `c_γ = χ(δ) / √|δ| ^ r` by which the matrix `γ` of the lattice multiplies the finite
datum. Here `δ` is the determinant of `γ` at the chosen places, `χ` the character that `O.charW`
attaches to a space of rank `r`, and `r` the rank of `O.W`. -/
def DividedLattice.weilScalar [WeilData E] (L : DividedLattice O) : ℂ :=
  let δ : (𝔸 E)ˣ := detOn (Set.range O.chosenPlace) L.point.val
  (O.charW.spaceChar (Fintype.card r)).val δ / √(ideleAbs δ) ^ Fintype.card r

section

/-- Let `ϖ = O.genIdele` generate the product of the chosen places, and let `γ = L.point` be a point
of the finite adelic unitary group, supported at the chosen places, with `ϖ γ⁻¹` integral (a
`DividedLattice`). If the integral point `j` is `1` modulo `ϖ²`, then `γ⁻¹ j γ` is integral and
reduces to `1` at every chosen place. -/
lemma DividedLattice.reduceAt_conj_eq_one (L : DividedLattice O) (j : stdLevel E n)
    (hj : O.chosenModulusSq.reductionGL j = 1) :
    ∃ h : L.point⁻¹ * j.val * L.point ∈ stdLevel E n, ∀ i : O.ChosenIndex,
      stdLevel.reduceAt (O.chosenPlace i) ⟨L.point⁻¹ * j.val * L.point, h⟩ = 1 := by
  -- Write `γ⁻¹ j γ - 1 = γ⁻¹ (j - 1) γ`. At a chosen place `γ` and `ϖ γ⁻¹` are integral and
  -- `j - 1` is divisible by `ϖ²`. To cover the conjugate places as well, use that `ϖ γ⁻¹` and
  -- `conj ϖ • γ` are integral everywhere and that `j - 1` is divisible by `ϖ² conj ϖ`.
  have h_sq (k : stdLevel E n) (hk : O.chosenModulusSq.reductionGL k = 1) (c d : n) :
      O.genIdele⁻¹.val ^ 2 * (k.val.val.val - 1) c d ∈ Ô E := by
    simpa using reduction_levelModulus_eq_zero_iff.1 ((stdLevel.map_eq_one n).1 hk c d)
  -- As `j⁻¹ = jᴴ` is also `1` modulo `ϖ`, the matrix `j - 1` is divisible by `conj ϖ`.
  have h_star (c d : n) : star O.genIdele⁻¹.val * (j.val.val.val - 1) c d ∈ Ô E := by
    have h_inv : O.genIdele.val * (O.genIdele⁻¹.val ^ 2 * ((j⁻¹).val.val.val - 1) d c) ∈ Ô E :=
      mul_mem O.genIntAdele.2 (h_sq j⁻¹ (by simp [hj]) d c)
    rw [Subgroup.coe_inv, U.inv_val_eq_conjTranspose] at h_inv
    simpa [sq, mul_assoc, one_apply, apply_ite star, @eq_comm n] using star_mem_Ô h_inv
  have h_div (c d : n) :
      star O.genIdele⁻¹.val * (O.genIdele⁻¹.val ^ 2 * (j.val.val.val - 1) c d) ∈ Ô E := by
    refine mem_Ô.2 fun w ↦ ?_
    have := mem_Ô.1 (h_star c d) w
    have := mem_Ô.1 (h_sq j hj c d) w
    -- At the place `w` one of `ϖ` and `conj ϖ` is `1`.
    have h_one {w : FinPlace E} (hw : w ∉ O.chosenModulusSq.places) : O.genIdele.val w = 1 :=
      genIdele_apply_of_notMem (by rwa [← places_levelModulus_false (c := 2)])
    obtain hw | hw : O.genIdele.val w = 1 ∨ O.genIdele.val (star w) = 1 :=
      (imp_iff_not_or.1 (disjoint_left.1 O.chosenModulusSq.isConjDisjoint_places ·)).imp h_one h_one
    <;> simp_all [idele_inv_apply_and_ne_zero]
  have h_div_conj (a b : n) :
      O.genIdele⁻¹.val * ((L.point⁻¹ * j * L.point).val.val - 1) a b ∈ Ô E := by
    have h_conj : (L.point⁻¹ * j * L.point).val.val - 1 =
        L.point⁻¹.val.val * (j.val.val.val - 1) * L.point.val.val := by simp [mul_sub, sub_mul]
    have h_int (d : n) : star O.genIdele.val * L.point.val.val d b ∈ Ô E := by
      have h_adj := star_mem_Ô (L.mul_inv_mem b d)
      rw [U.inv_val_eq_conjTranspose] at h_adj
      simpa using h_adj
    -- Each term is a product of the three integral factors above.
    have h_sum : ∑ d : n, ∑ c : n,
          O.genIdele.val * L.point⁻¹.val.val a c *
              (star O.genIdele⁻¹.val * (O.genIdele⁻¹.val ^ 2 * (j.val.val.val - 1) c d)) *
            (star O.genIdele.val * L.point.val.val d b) ∈ Ô E :=
      sum_mem fun d _ ↦ sum_mem fun c _ ↦
        mul_mem (mul_mem (L.mul_inv_mem a c) (h_div c d)) (h_int d)
    rw [h_conj]
    simpa [mul_apply, sum_mul, mul_sum, sq, mul_assoc, mul_left_comm, ← Units.coe_star,
      -coe_star_inv] using h_sum
  refine ⟨mem_stdLevel.2 fun a b ↦ ?_, fun i ↦ (stdLevel.map_eq_one _).2 fun a b ↦ ?_⟩
  · simpa [sub_eq_add_neg, add_mem_cancel_right, ite_mem, Matrix.one_apply] using
      mul_mem O.genIntAdele.2 (h_div_conj a b)
  · -- Reduction at `O.chosenPlace i` factors through reduction modulo `ϖ`, which kills every
    -- entry of `γ⁻¹ j γ - 1`.
    rw [← modulusResidue_reduction (O.levelModulus 1 _) (places_levelModulus_false.ge ⟨i, rfl⟩),
      reduction_levelModulus_eq_zero_iff.2 (by simpa using h_div_conj a b), map_zero]

/-- If integral matrices C and G satisfy `C * G = ϖ • 1`, where `ϖ = O.genIntAdele` generates the
product of the chosen places, then some divided lattice (a point γ of G_f at the chosen places with
`ϖ γ⁻¹` integral) has `ϖ γ⁻¹ ≡ G` modulo `ϖ²`. -/
lemma DividedLattice.exists_reducedInverse_eq (C G : Matrix n n (Ô E))
    (hCG : C * G = O.genIntAdele • 1) :
    ∃ L : DividedLattice O, L.reducedInverse = G.map O.chosenModulusSq.reduction := by
  classical
  have hC : C.map (Ô E).subtype * O.genIdele⁻¹.1 • G.map (Ô E).subtype = 1 := by
    ext
    simp [← Matrix.map_mul, hCG, apply_ite, -Subring.coe_subtype, Matrix.one_apply]
  let c : GL n (𝔸f E) :=
    cutGL (idem_mul_self O.chosenModulusSq.places) ⟨_, _, hC, mul_eq_one_comm.1 hC⟩
  set e := idem O.chosenModulusSq.places with he
  -- No chosen place is conjugate to a chosen place, so `c` and `cᴴ` commute and `γ` is unitary.
  have h_disj : e * star e = 0 := idem_mul_star O.chosenModulusSq.isConjDisjoint_places
  have h_comm : Commute (star c) c := Units.ext <| by
    -- Since `e * star e = 0`, both products are the same combination of `C`, `Cᴴ` and `1`.
    simp [c, cutGL, mul_add, add_mul, smul_smul, h_disj, mul_comm, ← he]
    ac_rfl
  let γ : Gf E n := ⟨star c⁻¹ * c, val_inj.2 <|
    show star (star c⁻¹ * c) * 1 * (star c⁻¹ * c) = 1 by simp [h_comm.inv_right.eq]⟩
  -- `ϖ γ⁻¹` is `G` at the chosen places, `ϖ Cᴴ` at their conjugates and `ϖ` elsewhere.
  have h_entry (a b : n) : O.genIdele * γ⁻¹.1.1 a b =
      e * G a b + star e * (O.genIdele * star (C b a).1) +
        if a = b then (1 - e - star e) * O.genIdele else 0 := by
    simp [γ, c, cutGL, mul_add, add_mul, h_disj, mul_left_comm O.genIdele.1, ← mul_assoc (star _),
      mul_comm (star _), ← he, Matrix.one_apply]
    -- The remaining identity follows from `e * star e = 0`.
    grind
  have h_support : γ ∈ supportedOn n (Set.range O.chosenPlace) := by
    simp +contextual [atPlace, γ, c, map_evalAt_cutGL, Units.ext_iff, evalAt_star_GL (star_star _),
      places_levelModulus_false]
  refine ⟨⟨γ, h_support, fun a b ↦ ?_⟩, ext fun a b ↦ reduction_congr _ fun w hw ↦ ?_⟩
  · rw [h_entry]
    simp (maxDischargeDepth := 5) [e, star_mem_Ô, O.genIntAdele.2, add_mem, mul_mem, sub_mem,
      ite_mem]
  -- At a chosen place `e` is `1` and its conjugate is `0`.
  have h_star : star e w = 0 := by
    simpa [e, idem_apply, hw] using congrArg (fun x : 𝔸f E ↦ x w) h_disj
  change (O.genIdele * γ⁻¹.1.1 a b) w = (G a b).1 w
  rw [h_entry]
  split_ifs <;> simp [h_star, e, hw, -finAdele_star_apply]

/-- The rows of `s`, indexed by `a`, stacked above the rows of `ϖ • 1`, indexed by `N`. With this
matrix `w`, the one equation `w x = w x'` modulo `ϖ²` says that `s x ≡ s x'` modulo `ϖ²` and
`x ≡ x'` modulo `ϖ`. -/
def DividedSplitting.stackOverGenScalar (V : DividedSplitting N m a O z)
    (s : Matrix a N O.chosenModulusSq.ResidueRing) :
    Matrix (a ⊕ N) N O.chosenModulusSq.ResidueRing :=
  fromRows s (V.genResidue • 1 : Matrix N N O.chosenModulusSq.ResidueRing)

omit [DecidableEq m] [Fintype a] in
/-- Let `V` split the indices `n` as `N ⊕ m`, with the embedding `V.fixedEmb : r ↪ N`, and let `s`
be an `a × N` matrix modulo `ϖ²`. Consider the integral unitary `N × N` matrices whose reduction
fixes the rows `V.stackOverGenScalar s` modulo `ϖ²` and has the columns of the identity off
`V.fixedEmb` modulo `ϖ² Q` (`rowFixingLevel`). Each of them reduces to `1` at every chosen place,
that is, lies in the level `levelOf O.chosenPlace ⊥`. -/
lemma rowFixingLevel_le_levelOf (V : DividedSplitting N m a O z)
    (s : Matrix a N O.chosenModulusSq.ResidueRing) :
    rowFixingLevel O.toLevelPlaces (V.stackOverGenScalar s) V.fixedEmb ≤
      levelOf O.chosenPlace ⊥ := by
  rintro _ ⟨k, ⟨-, h_rows⟩, rfl⟩
  -- The lower rows of `V.stackOverGenScalar s` are `genResidue • 1`, and they are fixed by the
  -- reduction of `k`.
  have h_fix :
      V.genResidue • ((O.levelModulus 2).reductionGL k).val.map reduceToChosenModulusSq =
        V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing id := by
    simpa [DividedSplitting.stackOverGenScalar, inclMatrix, -factor_reductionGL] using
      congrArg toRows₂ h_rows
  -- It remains that `k` reduces to `1` at each chosen place.
  refine ⟨k, funext fun i ↦ ext ?_, rfl⟩
  exact (reductionGL_map_modulusResidue ..).symm.trans
    ((V.genResidue_smul_eq_inclMatrix_iff _ id).1 h_fix i)

end

namespace DividedSplitting

/-- The subgroup Γ of GL_r(`O.chosenModulusSq.ResidueRing`) of matrices that are 1 modulo ϖ. It is
defined as the stabiliser of the scalar matrix `V.genResidue • 1` under multiplication. -/
def congruenceGroup (V : DividedSplitting N m a O z) :
    Subgroup (GL r O.chosenModulusSq.ResidueRing) :=
  MulAction.stabilizer (GL r O.chosenModulusSq.ResidueRing)
    (V.genResidue • 1 : Matrix r r O.chosenModulusSq.ResidueRing)

omit [DecidableEq n] [DecidableEq N] [DecidableEq m] [Fintype a] in
/-- An invertible matrix `A` lies in `V.congruenceGroup` exactly when
`V.genResidue • A = V.genResidue • 1`. Here `V.genResidue` is the class of `ϖ = O.genIdele` modulo
`ϖ²`, so this says that `A` is `1` modulo `ϖ`. -/
lemma mem_congruenceGroup_iff (V : DividedSplitting N m a O z)
    (A : GL r O.chosenModulusSq.ResidueRing) :
    A ∈ V.congruenceGroup ↔ V.genResidue • A.val = V.genResidue • 1 := by
  simp [congruenceGroup, MulAction.mem_stabilizer_iff, Units.smul_def]

omit [DecidableEq N] [DecidableEq m] [Fintype a] in
/-- The lift of an element of the congruence group (the matrices that are `1` modulo `ϖ`) reduces to
`1` at every chosen place. -/
lemma reduceAt_liftMod_congruenceGroup (V : DividedSplitting N m a O z) (Y : V.congruenceGroup)
    (i : O.ChosenIndex) :
    stdLevel.reduceAt (O.placeAt (inl i)) (liftMod Y.val) = 1 := by
  -- The equation `genResidue • Y = genResidue • 1` says that the lift of `Y` is `1` modulo each
  -- chosen place.
  have hY :
      V.genResidue • ((O.levelModulus 2).reductionGL (liftMod Y.val)).val.map
        reduceToChosenModulusSq =
        V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing id := by
    simpa [inclMatrix] using (V.mem_congruenceGroup_iff _).1 Y.2
  exact ext ((reductionGL_map_modulusResidue ..).symm.trans
    ((V.genResidue_smul_eq_inclMatrix_iff _ id).1 hY i))

/-- The two conditions on the blocks of a matrix `x`: its block on `V°` is `(1; 0)` modulo `ϖ²`, and
its block on `V″` lies in `(1; 0) + ϖ L″_s`, where `L″_s` consists of the `u` with `s u ≡ 0` modulo
`ϖ`. Here the `1` of `(1; 0)` stands in the rows `z` of `V°` and in the rows `V.fixedEmb` of `V″`,
which are the rows `O.incl` of `V`. -/
def IsBlockNormalised (V : DividedSplitting N m a O z)
    (s : Matrix a N O.chosenModulusSq.ResidueRing)
    (x : Matrix n r O.chosenModulusSq.ResidueRing) : Prop :=
  x.submatrix (V.ε ∘ inr) id = inclMatrix O.chosenModulusSq.ResidueRing z ∧
    V.stackOverGenScalar s * x.submatrix (V.ε ∘ inl) id =
      V.stackOverGenScalar s * inclMatrix O.chosenModulusSq.ResidueRing V.fixedEmb

/-- `L` is glued for `s`. With `γ = L.point`, the congruence `γ⁻¹ x ≡ (1; 0)` modulo `ϖ`, written as
`(ϖ γ⁻¹) x ≡ ϖ (1; 0)` modulo `ϖ²`, holds exactly when `x Y` satisfies the conditions on the two
blocks (`IsBlockNormalised`) for some `Y` in the congruence group, and this `Y` is then unique.
Moreover `γ⁻¹` is integral at the chosen places on all vectors of a suitable basis of `V″`, apart
from those indexed by `V.dividedEmb`, the chosen copy of the index set `a` of the rows of `s` in the
index set `N` of `V″`. -/
structure IsGlued (V : DividedSplitting N m a O z)
    (s : Matrix a N O.chosenModulusSq.ResidueRing) (L : DividedLattice O) : Prop where
  /-- If `γ⁻¹ x ≡ (1; 0)` modulo `ϖ`, then for exactly one `Y` that is `1` modulo `ϖ` the translate
  `x Y` satisfies the conditions on the two blocks. -/
  existsUnique (x : Matrix n r O.chosenModulusSq.ResidueRing)
    (hx : L.reducedInverse * x = V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing O.incl) :
    ∃! Y : V.congruenceGroup, V.IsBlockNormalised s
      (x * ((Y : GL r O.chosenModulusSq.ResidueRing) : Matrix r r O.chosenModulusSq.ResidueRing))
  /-- Conversely, a matrix with such a translate satisfies the congruence. -/
  mul_eq_of_isBlockNormalised (x : Matrix n r O.chosenModulusSq.ResidueRing) (Y : V.congruenceGroup)
    (hY : V.IsBlockNormalised s
      (x * ((Y : GL r O.chosenModulusSq.ResidueRing) : Matrix r r O.chosenModulusSq.ResidueRing))) :
    L.reducedInverse * x = V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing O.incl
  /-- After a column operation, the columns of `ϖ γ⁻¹` in `V″` vanish modulo `ϖ` outside
  `V.dividedEmb`. -/
  exists_cols_eq_zero : ∃ K : GL N O.chosenModulusSq.ResidueRing, ∀ x : n,
    ∀ y : N, y ∉ univ.map V.dividedEmb →
    V.genResidue * (L.reducedInverse.submatrix id (V.ε ∘ inl) * K.val) x y = 0

open scoped Classical in
/-- As `L` is glued for `s` (`IsGlued`), the congruence `(ϖ γ⁻¹) x ≡ ϖ • inclMatrix _ O.incl` modulo
`ϖ²` holds exactly when `x Y` is block normalised for some `Y` in `V.congruenceGroup`, and this `Y`
is unique. So the indicator of the congruence is the sum over `Y` of the indicators that `x Y` is
block normalised. -/
lemma IsGlued.indicator_eq_sum {V : DividedSplitting N m a O z}
    {s : Matrix a N O.chosenModulusSq.ResidueRing} {L : DividedLattice O} (hL : V.IsGlued s L)
    (x : Matrix n r O.chosenModulusSq.ResidueRing) (c : ℂ) :
    (if L.reducedInverse * x = V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing O.incl then c
      else 0) =
      ∑ Y : V.congruenceGroup,
        if V.IsBlockNormalised s (x * ((Y : GL r O.chosenModulusSq.ResidueRing) :
          Matrix r r O.chosenModulusSq.ResidueRing))
        then c else 0 := by
  split_ifs with hx
  · -- Exactly one `Y` contributes to the sum.
    obtain ⟨Y, hY, h_unique⟩ := hL.existsUnique x hx
    rw [Fintype.sum_eq_single Y fun Y' h_ne ↦ ite_eq_right (mt (h_unique Y') h_ne), ite_eq_left hY]
  · -- No `Y` contributes to the sum.
    rw [sum_eq_zero fun Y _ ↦ ite_eq_right (mt (hL.mul_eq_of_isBlockNormalised x Y) hx)]

/-! ### Product forms and the construction of glued lattices -/

/-- For a pair `h = (h.1, h.2)` of points on `V″` and `V°` and a vector `y` of weight `O.colsPlus`
on `V″`, the linear map sending a vector `η` of weight `O.colsMinus` on `V°` to the form on `V` that
is supported on the class of `U.block V.ε h * γ`, the block diagonal point of `h` times the matrix
of the lattice `L`. Its value there (`classForm`) is the product `cartanProduct V.ε 1 y η` of `y`
and `η`, moved by the identity. -/
def productForm (V : DividedSplitting N m a O z) (L : DividedLattice O) (h : Gf E N × Gf E m)
    (y : WeylIndex N O.colsPlus → ℂ) :
    (WeylIndex m O.colsMinus → ℂ) →ₗ[ℂ] O.FormV :=
  classForm O (U.block V.ε h * L.point) ∘ₗ cartanProduct V.ε 1 y

omit [DecidableEq n] [DecidableEq N] [DecidableEq m] [Fintype a] in
/-- Let `ϖ` generate the product of the chosen places of `O`, with class `V.genResidue` in the
residue ring modulo `ϖ²`. If an `r × r` matrix `Y` has `ϖ Y = 0` modulo `ϖ²`, then `1 - Y` is the
inverse of an element of `V.congruenceGroup`, the invertible matrices modulo `ϖ²` that are `1`
modulo `ϖ`. -/
lemma exists_congruenceGroup_inv_eq_one_sub (V : DividedSplitting N m a O z)
    {Y : Matrix r r O.chosenModulusSq.ResidueRing} (hY : V.genResidue • Y = 0) :
    ∃ A : V.congruenceGroup, A⁻¹.val.val = 1 - Y := by
  -- `ϖ Y = 0` modulo `ϖ²` says that every entry of `Y` is divisible by `ϖ`. So `Y² = 0`, and
  -- `1 - Y` is a unit that fixes `ϖ • 1`.
  have h_sq : Y ^ 2 = 0 := by
    choose X hX using fun i j ↦ reduction_surjective O.chosenModulusSq (Y i j)
    have h_div (i j : r) : O.genIdele⁻¹.val * (X i j).val ∈ Ô E := by
      have h_zero : O.chosenModulusSq.reduction (O.genIntAdele * X i j) = 0 := by
        simpa [hX] using congrFun₂ hY i j
      simpa [sq, mul_assoc] using reduction_levelModulus_eq_zero_iff.1 h_zero
    have h_mul (i j k : r) : O.chosenModulusSq.reduction (X i j * X j k) = 0 :=
      reduction_levelModulus_eq_zero_iff.2
        (by simpa [sq, mul_mul_mul_comm] using mul_mem (h_div i j) (h_div j k))
    ext i k
    simp [sq, mul_apply, ← hX, ← map_mul, h_mul]
  obtain ⟨A, hA⟩ : IsUnit (1 - Y) := IsNilpotent.isUnit_one_sub ⟨2, h_sq⟩
  exact ⟨⟨A, by simp [V.mem_congruenceGroup_iff, hA, hY, smul_sub]⟩⁻¹, by simp [hA]⟩

variable (O z) in
/-- The matrix with the blocks `D`, `-D ι_e ι_zᵀ`, `0` and the diagonal matrix that is `ϖ` on the
range of `z` and `1` elsewhere, where `ι_e` and `ι_z` are the inclusion matrices (`inclMatrix`) of
`e` and `z`. For suitable `D` and `e` it is `ϖ γ⁻¹` at the chosen places, up to the order of the
rows, for the lattice of `exists_isGlued`. -/
def glueMatrix (e : r ↪ N) (D : Matrix N N (Ô E)) : Matrix (N ⊕ m) (N ⊕ m) (Ô E) :=
  fromBlocks D (-D.submatrix id e * (inclMatrix (Ô E) z)ᵀ) 0
    (.diagonal fun i ↦ if i ∈ range z then O.genIntAdele else 1)

omit [DecidableEq n] [Fintype a] in
/-- Let `V.ε : N ⊕ m ≃ n` split the indices, let `ϖ` generate the product of the chosen places, with
class `V.genResidue` modulo `ϖ²`, and let `w = V.stackOverGenScalar s` be `s` stacked above `ϖ • 1`.
Write `ι_e` for the inclusion matrix of `e`, whose `j`-th column is the basis vector `e j`. A matrix
`x` modulo `ϖ²` is block normalised if its rows in `m` form `ι_z` and its rows `u` in `N` satisfy
`w u = w ι_e`, for `e = V.fixedEmb : r ↪ N`. Let the integral matrix `D` impose the same equations
as `w` modulo `ϖ²`, and let `glueMatrix` have the blocks `D`, `-D ι_e ι_zᵀ`, `0` and the diagonal
matrix that is `ϖ` on the range of `z` and `1` elsewhere. Then `x` is block normalised if and only
if its rows `z` in `m` form the identity matrix and `glueMatrix` takes `x` to `ϖ ι_{inr ∘ z}`. -/
lemma isBlockNormalised_iff (V : DividedSplitting N m a O z)
    (s : Matrix a N O.chosenModulusSq.ResidueRing) {D : Matrix N N (Ô E)}
    (h_rows : ∀ X Y : Matrix N r O.chosenModulusSq.ResidueRing,
      V.stackOverGenScalar s * X = V.stackOverGenScalar s * Y ↔
        D.map O.chosenModulusSq.reduction * X = D.map O.chosenModulusSq.reduction * Y)
    (x : Matrix n r O.chosenModulusSq.ResidueRing) :
    V.IsBlockNormalised s x ↔ x.submatrix (V.ε ∘ inr ∘ z) id = 1 ∧
      (glueMatrix O z V.fixedEmb D).map O.chosenModulusSq.reduction * x.submatrix V.ε id =
        V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing (inr ∘ z) := by
  -- Read the last equation by blocks: the rows of `V″` give the condition with `D`, and the rows
  -- of `V°` say that the block on `V°` is the inclusion of `z`.
  let X : Matrix N r O.chosenModulusSq.ResidueRing := x.submatrix (V.ε ∘ inl) id
  let X' : Matrix m r O.chosenModulusSq.ResidueRing := x.submatrix (V.ε ∘ inr) id
  let D' : Matrix N N O.chosenModulusSq.ResidueRing := D.map O.chosenModulusSq.reduction
  let Δ : Matrix m m O.chosenModulusSq.ResidueRing :=
    .diagonal fun i ↦ if i ∈ range z then V.genResidue else 1
  have h_split :
      (glueMatrix O z V.fixedEmb D).map O.chosenModulusSq.reduction * x.submatrix V.ε id =
          V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing (inr ∘ z) ↔
        D' * X = D'.submatrix id V.fixedEmb * X'.submatrix z id ∧
          Δ * X' = V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing z := by
    simp [glueMatrix, D', X, X', Δ, inclMatrix, apply_ite O.chosenModulusSq.reduction,
      diagonal_apply, sum_mul, sum_comm (γ := m), add_neg_eq_zero,
      ← ext_iff, Matrix.mul_apply, Matrix.one_apply]
  have h_diag_mul_eq_iff (h_top : X'.submatrix z id = 1) :
      Δ * X' = V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing z ↔
        X' = inclMatrix O.chosenModulusSq.ResidueRing z := by
    simp only [← ext_iff, Δ, X', diagonal_mul, inclMatrix, Matrix.smul_apply, submatrix_apply,
      id_eq, Function.comp_apply, _root_.smul_eq_mul, mul_ite, mul_one, mul_zero,
      Matrix.one_apply] at h_top ⊢
    grind
  rw [IsBlockNormalised, h_rows, mul_inclMatrix, h_split]
  constructor
  · rintro ⟨h_m : X' = inclMatrix O.chosenModulusSq.ResidueRing z, h_N⟩
    have h_top : X'.submatrix z id = 1 := by
      simp [h_m, inclMatrix]
    exact ⟨h_top, by rwa [h_top, Matrix.mul_one], (h_diag_mul_eq_iff h_top).2 h_m⟩
  · rintro ⟨h_top : X'.submatrix z id = 1, h_N, h_m⟩
    exact ⟨(h_diag_mul_eq_iff h_top).1 h_m, by rwa [h_top, Matrix.mul_one] at h_N⟩

omit [Fintype a] in
/-- Let `ϖ` generate the product of the chosen places, with class `V.genResidue` modulo `ϖ²`, and
let `L.reducedInverse` be `ϖ γ⁻¹` modulo `ϖ²` for the point `γ` of the lattice `L`. Suppose that it
is the reduction of an integral matrix `G` whose rows are ordered by `ε'` and whose columns are
ordered by the splitting `V.ε : N ⊕ m ≃ n`, where `ε'` takes the indices `z : r ↪ m` to the indices
`O.incl : r ↪ n`. Then `(ϖ γ⁻¹) x` is `ϖ` times the inclusion matrix of `O.incl` if and only if `G`
takes `x`, with its rows ordered by `V.ε`, to `ϖ` times the inclusion matrix of `inr ∘ z`. -/
lemma reducedInverse_mul_eq_iff (V : DividedSplitting N m a O z) {L : DividedLattice O}
    {G : Matrix (N ⊕ m) (N ⊕ m) (Ô E)} {ε' : N ⊕ m ≃ n}
    (hε' : ∀ i : r, ε' (inr (z i)) = O.incl i)
    (hL : L.reducedInverse = (reindex ε' V.ε G).map O.chosenModulusSq.reduction)
    (x : Matrix n r O.chosenModulusSq.ResidueRing) :
    L.reducedInverse * x = V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing O.incl ↔
      G.map O.chosenModulusSq.reduction * x.submatrix V.ε id =
        V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing (inr ∘ z) := by
  rw [hL, ← (reindex ε'.symm (.refl r)).injective.eq_iff]
  have h_reindex_mul :
      reindex ε'.symm (.refl r) ((reindex ε' V.ε G).map O.chosenModulusSq.reduction * x) =
      G.map O.chosenModulusSq.reduction * x.submatrix V.ε id := by
    ext i j
    simp [mul_apply, ← V.ε.sum_comp]
  have h_reindex_incl : reindex ε'.symm (.refl r)
      (V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing O.incl) =
        V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing (inr ∘ z) := by
    ext i j
    simp [inclMatrix, ← hε', Matrix.one_apply]
  rw [h_reindex_mul, h_reindex_incl]

omit [DecidableEq n] [DecidableEq N] [DecidableEq m] [Fintype a] in
/-- Right multiplication by an element of the congruence group, whose elements fix `ϖ • 1`, does not
change whether a matrix equals `ϖ B` modulo `ϖ²`. -/
lemma mul_congruenceGroup_eq_smul_iff (V : DividedSplitting N m a O z)
    (A B : Matrix n r O.chosenModulusSq.ResidueRing) (Y : V.congruenceGroup) :
    A * Y.val.val = V.genResidue • B ↔ A = V.genResidue • B := by
  have hY : V.genResidue • Y.val.val = V.genResidue • 1 := (V.mem_congruenceGroup_iff _).1 Y.2
  have h_fix : V.genResidue • B * Y.val.val = V.genResidue • B := by
    rw [smul_mul, ← Matrix.mul_smul, hY, Matrix.mul_smul, Matrix.mul_one]
  nth_rw 1 [← h_fix]
  exact Matrix.mul_left_inj_of_invertible (m := n) Y.val.val

omit [Fintype a] in
/-- Let `V.ε : N ⊕ m ≃ n` split the indices, let `ϖ` generate the product of the chosen places, and
let the integral matrix `D` impose modulo `ϖ²` the same equations as `w = V.stackOverGenScalar s`,
which is `s` stacked above `ϖ • 1`. Write `ι_e` for the inclusion matrix of `e`. Suppose that
`L.reducedInverse`, the matrix `ϖ γ⁻¹` modulo `ϖ²` for the point `γ` of `L`, is `glueMatrix`, with
rows ordered by an `ε'` taking `z` to `O.incl`. Let `Y` be invertible and `1` modulo `ϖ`. Then `x Y`
is block normalised if and only if the rows `z` of `x` in `m` form `Y⁻¹` and
`(ϖ γ⁻¹) x ≡ ϖ ι_{O.incl}` modulo `ϖ²`. -/
lemma isBlockNormalised_mul_iff (V : DividedSplitting N m a O z)
    (s : Matrix a N O.chosenModulusSq.ResidueRing) {L : DividedLattice O} {D : Matrix N N (Ô E)}
    {ε' : N ⊕ m ≃ n} (hε' : ∀ i : r, ε' (inr (z i)) = O.incl i)
    (hL : L.reducedInverse =
      (reindex ε' V.ε (glueMatrix O z V.fixedEmb D)).map O.chosenModulusSq.reduction)
    (h_rows : ∀ X Y : Matrix N r O.chosenModulusSq.ResidueRing,
      V.stackOverGenScalar s * X = V.stackOverGenScalar s * Y ↔
        D.map O.chosenModulusSq.reduction * X = D.map O.chosenModulusSq.reduction * Y)
    (x : Matrix n r O.chosenModulusSq.ResidueRing) (Y : V.congruenceGroup) :
    V.IsBlockNormalised s (x * Y.val.val) ↔
      x.submatrix (V.ε ∘ inr ∘ z) id = Y⁻¹.val.val ∧
        L.reducedInverse * x = V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing O.incl := by
  -- The rows `z` of `x` form `Y⁻¹` exactly when those of `x Y` form `1`, and right multiplication
  -- by `Y` does not change the congruence.
  have h_top : x.submatrix (V.ε ∘ inr ∘ z) id = Y⁻¹.val.val ↔
      (x * Y.val.val).submatrix (V.ε ∘ inr ∘ z) id = 1 := Y.val.mul_eq_one_iff_eq_inv.symm
  rw [h_top, V.isBlockNormalised_iff s h_rows, ← V.reducedInverse_mul_eq_iff hε' hL,
    ← Matrix.mul_assoc, V.mul_congruenceGroup_eq_smul_iff]

omit [DecidableEq n] [DecidableEq m] in
/-- Let `ϖ = O.genIntAdele` be the integral finite adele (element of `Ô E`) that generates the
product of the chosen places of `O`, and let `s` be an `a × N` matrix over the residue ring modulo
`ϖ²`. There are integral `N × N` matrices `B` and `D` with `B D = ϖ • 1` such that, modulo `ϖ²`,
each of `D` and `V.stackOverGenScalar s` is a left multiple of the other. -/
lemma exists_divisor_assoc_stackOverGenScalar (V : DividedSplitting N m a O z)
    (s : Matrix a N O.chosenModulusSq.ResidueRing) :
    ∃ (B D : Matrix N N (Ô E)) (P : Matrix (a ⊕ N) N O.chosenModulusSq.ResidueRing)
      (Q : Matrix N (a ⊕ N) O.chosenModulusSq.ResidueRing),
      B * D = O.genIntAdele • 1 ∧
      V.stackOverGenScalar s = P * D.map O.chosenModulusSq.reduction ∧
      D.map O.chosenModulusSq.reduction = Q * V.stackOverGenScalar s := by
  classical
  -- Lift `s` to a matrix `t` over `Ô E`, take a Hermite form of `t` stacked over `ϖ`, and reduce.
  obtain ⟨t, rfl⟩ : ∃ t : Matrix a N (Ô E), t.map O.chosenModulusSq.reduction = s := by
    choose t ht using fun i j ↦ reduction_surjective O.chosenModulusSq (s i j)
    exact ⟨of t, ext ht⟩
  obtain ⟨U, -, D, -, hP, hQ⟩ :=
    isValuationPair_Ô.top.hermite .inr (fromRows t (O.genIntAdele • 1 : Matrix N N (Ô E)))
  -- Reduction takes `t` stacked over `ϖ` to the matrix `V.stackOverGenScalar s`.
  have h_stack : (fromRows t (O.genIntAdele • 1 : Matrix N N (Ô E))).map
      O.chosenModulusSq.reduction = V.stackOverGenScalar (t.map O.chosenModulusSq.reduction) := by
    simp [stackOverGenScalar, map_smul', fromRows_map]
  refine ⟨U.val.toBlocks₂₂, D, (U.val.submatrix id inr).map O.chosenModulusSq.reduction,
    (U⁻¹.val.submatrix inr id).map O.chosenModulusSq.reduction, (congrArg toRows₂ hP).symm, ?_, ?_⟩
  · rw [← h_stack, ← Matrix.map_mul]
    exact congrArg (fun X ↦ X.map O.chosenModulusSq.reduction) hP
  · rw [← h_stack, ← Matrix.map_mul]
    exact (congrArg (fun X ↦ X.map O.chosenModulusSq.reduction) hQ).symm

omit [DecidableEq n] [DecidableEq m] in
/-- There is an invertible `K` such that the columns of `V.stackOverGenScalar s * K` outside
`V.dividedEmb` vanish modulo `ϖ`, that is, are killed by `V.genResidue` modulo `ϖ²`. -/
lemma exists_genResidue_mul_stackOverGenScalar_eq_zero (V : DividedSplitting N m a O z)
    (s : Matrix a N O.chosenModulusSq.ResidueRing) :
    ∃ K : GL N O.chosenModulusSq.ResidueRing, ∀ i : a ⊕ N, ∀ y ∉ range V.dividedEmb,
      V.genResidue * (V.stackOverGenScalar s * K.val) i y = 0 := by
  -- `K` clears the columns of `s` outside `V.dividedEmb`, and `ϖ` kills the rows `ϖ K`.
  obtain ⟨K, -, hK⟩ := (isValuationPair_residueRing _).exists_mul_clear_cols s V.dividedEmb
  have h_sq : V.genResidue * V.genResidue = 0 := by
    simp [← map_mul, reduction_levelModulus_eq_zero_iff, sq, mul_assoc]
  refine ⟨K, fun i y hy ↦ ?_⟩
  cases i with
  | inl i => simp [stackOverGenScalar, hK i y hy]
  | inr i => simp [stackOverGenScalar, ← mul_assoc, h_sq]

omit [DecidableEq n] [Fintype a] in
/-- Let `ϖ = O.genIntAdele` be the integral finite adele that generates the product of the chosen
places, and let `e = V.fixedEmb : r ↪ N` and `z : r ↪ m` be the
embeddings. If `B D = ϖ • 1` for integral `B` and `D`, then some integral matrix `C` satisfies
`C * glueMatrix O z e D = ϖ • 1`. -/
lemma exists_mul_glueMatrix_eq (V : DividedSplitting N m a O z) {B D : Matrix N N (Ô E)}
    (hBD : B * D = O.genIntAdele • 1) :
    ∃ C : Matrix (N ⊕ m) (N ⊕ m) (Ô E),
      C * glueMatrix O z V.fixedEmb D = O.genIntAdele • 1 := by
  classical
  -- `C` has the blocks `B`, `ι_e ι_zᵀ`, `0` and the diagonal matrix with `ϖ` off the range of `z`.
  refine ⟨fromBlocks B (inclMatrix (Ô E) V.fixedEmb * (inclMatrix (Ô E) z)ᵀ) 0
    (.diagonal fun i ↦ if i ∈ range z then 1 else O.genIntAdele), ?_⟩
  -- Only the top right block needs an argument: the rows `z` of the diagonal block of
  -- `glueMatrix` are `ϖ` times those of `1`.
  have h_diag :
      inclMatrix (Ô E) V.fixedEmb *
          (Matrix.diagonal fun i : m ↦ if ∃ y : r, z y = i then O.genIntAdele else 1).submatrix
            z id =
        O.genIntAdele • (inclMatrix (Ô E) V.fixedEmb * (inclMatrix (Ô E) z)ᵀ) := by
    rw [← Matrix.mul_smul]
    congr 1
    ext i j
    simp [inclMatrix, diagonal_apply, Matrix.one_apply, eq_comm]
  rw [glueMatrix, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul, fromBlocks_inj]
  refine ⟨by simp [hBD], ?_, by simp, ?_⟩
  · rw [Matrix.mul_assoc _ _ᵀ, inclMatrix_transpose_mul]
    simp [← mul_inclMatrix, ← B.mul_assoc, hBD, h_diag]
  · ext i j
    by_cases i ∈ Set.range z <;> simp_all [diagonal_apply, Matrix.one_apply]

/-- Let `V.ε : N ⊕ m ≃ n` split the indices, let `ϖ` generate the product of the chosen places of
`O`, and write `ι_e` for the inclusion matrix of `e`. For every `a × N` matrix `s` modulo `ϖ²` there
is a divided lattice `L` (a unitary point `γ` at the chosen places with `ϖ γ⁻¹` integral) that is
glued for `s`. This means two things. First, an `n × r` matrix `x` modulo `ϖ²` satisfies
`(ϖ γ⁻¹) x ≡ ϖ ι_{O.incl}` if and only if `x Y` is block normalised for some invertible `Y ≡ 1`
modulo `ϖ`, and this `Y` is unique. Block normalised means that the rows in `m` form `ι_z` and the
rows `u` in `N` have `s u ≡ s ι_e` modulo `ϖ²` and `u ≡ ι_e` modulo `ϖ`, for `e = V.fixedEmb`.
Second, for some invertible `N × N` matrix `K`, the columns of `ϖ γ⁻¹` in `N`, multiplied by `K` on
the right, vanish modulo `ϖ` outside the range of `V.dividedEmb : a ↪ N`. -/
lemma exists_isGlued (V : DividedSplitting N m a O z)
    (s : Matrix a N O.chosenModulusSq.ResidueRing) :
    ∃ L : DividedLattice O, V.IsGlued s L := by
  classical
  -- Take a Hermite form `D` of `V.stackOverGenScalar s`. At the chosen places `ϖ γ⁻¹` will be
  -- `glueMatrix` for `D`, up to the order of the rows, and `γ` the matrix `C` below, up to the
  -- order of the columns.
  obtain ⟨B, D, P, Q, hBD, hP, hQ⟩ := V.exists_divisor_assoc_stackOverGenScalar s
  have h_rows (X Y : Matrix N r O.chosenModulusSq.ResidueRing) :
      V.stackOverGenScalar s * X = V.stackOverGenScalar s * Y ↔
        D.map O.chosenModulusSq.reduction * X = D.map O.chosenModulusSq.reduction * Y :=
    ⟨fun h ↦ by rw [hQ, Matrix.mul_assoc, h, Matrix.mul_assoc],
      fun h ↦ by rw [hP, Matrix.mul_assoc, h, Matrix.mul_assoc]⟩
  let G : Matrix (N ⊕ m) (N ⊕ m) (Ô E) := glueMatrix O z V.fixedEmb D
  obtain ⟨C, hCG⟩ : ∃ C : Matrix (N ⊕ m) (N ⊕ m) (Ô E), C * G = O.genIntAdele • 1 :=
    V.exists_mul_glueMatrix_eq hBD
  -- Reorder the basis of the lattice so that the indices `z` of `V°` go to the indices `O.incl`.
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (f := V.ε ∘ inr ∘ z) (g := O.incl)
    (V.ε.injective.comp (inr_injective.comp z.injective)) O.incl.injective
  let ε' : N ⊕ m ≃ n := V.ε.trans σ
  have hε' : ∀ i : r, ε' (inr (z i)) = O.incl i := hσ

  obtain ⟨L, hL⟩ : ∃ L : DividedLattice O,
      L.reducedInverse = (reindex ε' V.ε G).map O.chosenModulusSq.reduction :=
    DividedLattice.exists_reducedInverse_eq (reindex V.ε ε' C) _ (by simp [hCG, submatrix_smul])
  have h_blockNormalised_iff (x : Matrix n r O.chosenModulusSq.ResidueRing)
      (Y : V.congruenceGroup) :
      V.IsBlockNormalised s (x * Y.val.val) ↔
        x.submatrix (V.ε ∘ inr ∘ z) id = Y⁻¹.val.val ∧
          L.reducedInverse * x = V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing O.incl :=
    V.isBlockNormalised_mul_iff s hε' hL h_rows x Y
  refine ⟨L,
    { existsUnique := fun x hx ↦ ?_
      mul_eq_of_isBlockNormalised := fun x Y hY ↦ ((h_blockNormalised_iff x Y).1 hY).2
      exists_cols_eq_zero := ?_ }⟩
  · -- The rows `z` show that the top block of `x` on `V°` is `1` modulo `ϖ`; `Y` is its inverse,
    -- and this determines it.
    have h_one : V.genResidue • (1 - x.submatrix (V.ε ∘ inr ∘ z) id) = 0 := by
      ext i j
      simpa [G, glueMatrix, apply_ite, mul_apply, inclMatrix, diagonal_apply, mul_sub,
        Matrix.one_apply, sub_eq_zero] using
        congrFun₂ ((V.reducedInverse_mul_eq_iff hε' hL x).1 hx).symm (inr (z i)) j
    obtain ⟨Y, hY⟩ : ∃ Y : V.congruenceGroup,
        Y⁻¹.val.val = x.submatrix (V.ε ∘ inr ∘ z) id := by
      simpa only [sub_sub_cancel] using V.exists_congruenceGroup_inv_eq_one_sub h_one
    refine ⟨Y, (h_blockNormalised_iff x Y).2 ⟨hY.symm, hx⟩,
      fun Y' hY' ↦ inv_injective (Subtype.ext (Units.ext ?_))⟩
    rw [hY, ((h_blockNormalised_iff x Y').1 hY').1]
  · -- The columns of `glueMatrix` in `V″` are `(D; 0)`, and `D` is a left multiple of the stacked
    -- rows.
    obtain ⟨K, hK⟩ := V.exists_genResidue_mul_stackOverGenScalar_eq_zero s
    have h_cols (x y : N) (hy : y ∉ range V.dividedEmb) :
        V.genResidue * (D.map O.chosenModulusSq.reduction * K.val) x y = 0 := by
      rw [hQ, Matrix.mul_assoc, mul_apply]
      simp [mul_add, mul_sum, mul_left_comm V.genResidue, hK _ y hy]
    refine ⟨K, ?_⟩
    simpa [hL, G, glueMatrix, ← submatrix_map, ε'.surjective.forall, mul_apply, -map_apply,
      fromBlocks_map] using h_cols

end DividedSplitting

end GluedForms

end New.Rows

end
