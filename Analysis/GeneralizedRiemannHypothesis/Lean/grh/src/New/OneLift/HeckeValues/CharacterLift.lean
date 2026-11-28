import Lib.Weil.CompactLift.DefiniteThetaLift
import New.Determinant.Norms.VectorKernel
import New.UpperBound.Kernels.JetConjugatesAndBounds

/-!
# The lift of a character from U(1): kernel, descent and Galois conjugates

Let `χ` be a character of `U(1)` over the adeles. Its lift is the algebraic form `φ` on the standard
definite space `V` of rank `card n` that is the sum, over the classes of `U(1)` at the level of
the chosen places, of the theta kernel formed with `χ` and the block datum. It is a multiple of the
theta lift of the constant function `1`. This file defines `φ`, computes its inner products through
the descent from `V` to the line, and shows that a Galois conjugate of `φ` is, up to simple factors,
the lift of the conjugate character.

## Main definitions and results

* `New.LValueData`: the chosen places and the places of the twist, the row lengths `rowLength τ`
  and the character `u1Char` of `U(1)`. `New.LValueData.descentPair` is the descent datum
  (`New.DescentPair`) whose source `W` is the definite line and whose weight has one row of length
  `rowLength τ` at `τ`.
* `New.LValueData.kernelForm`: the theta kernel at a finite point `g` of `U(1)`, as a form on `V`;
  the lift `New.LValueData.trivialLift` is its class sum over `U(1)`.
* `New.LValueData.theta_pairThetaKernel_omega_fockDatum`: the pairings of the kernel with vectors of
  the weight are theta values of Fock vectors.
* `New.LValueData.normalizedDescent_eq_inner_kernelForm`, `New.LValueData.inner_trivialLift`: the
  descent `New.DescentPair.normalizedDescent` of a form is its inner product with the kernel, so the
  inner product with the lift is the class sum of the descent.
* `New.DescentPair.heckePolyOnForms_liftHeckeRoot_eq_zero`: the Hecke polynomial
  `New.DescentPair.heckePolyOnForms`, evaluated at the number `New.DescentPair.liftHeckeRoot`,
  annihilates every form with the Hecke polynomials of a lift
  (`New.DescentPair.HasLiftHeckePolynomial`).
* `New.LValueData.map_trivialLift`: the Galois conjugates of the lift.

Notions from other files:

* `New.DescentPair`: a descent datum, that is places, a hermitian space `W` of rank less than
  `card n`, two weights and a character; `New.DescentPair.FormV` is the space of algebraic forms on
  `V` of its weight and level, and `New.DescentPair.blockDatum` is the block datum on `Hom(W, V)`
  times the vacuum.
* `Gf E n`, `stdLevel E n`: the finite adelic points of the unitary group of `V` and their integral
  subgroup; `levelOf w H` is the level of elements of `stdLevel` that reduce into `H` at the places
  `w`.
* `classSum Γ K f`: the weighted sum of `f` over `Γ \ G / K`; `stdClassSum` takes `Γ` rational.
* `schurJet κ`: the jets of a power series along the Schur matrix of the weight `κ`.

## Relation to the literature

Known; see `Lib.SiegelWeil.RallisInner.SharpData` for sources.

The sections "The lift and the descent" and "The parameter of the line and a Hecke operator" set
up, for the data `New.LValueData`, steps of the known expression of critical Hecke L-values of CM
fields as squared norms of theta lifts from U(1).
-/

noncomputable section

namespace New

open NumberField (InfinitePlace)

/-!
## The lift and the descent

The lemmas `New.LevelPlaces.LevelForm.inner_eq_petersson` and
`New.LValueData.hookNumber_eq_prod_factorial` give constants in the norm of the lift.
-/

section CharacterLift

open «GL» MvPolynomial Matrix Fintype Space Exchange Rows DescentPair

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]

/-- On a standard space `V` with signs `s`, let `l` be twice the Harish-Chandra parameter of the
weight `(κ, e)`. Let the residue group `H` be a group of families of invertible matrices over the
residue fields at the places `placeAt i`, for `i` in the index set `ChosenIndex ⊕ TwistIndex` of
the chosen places and the places of the twist; the level `levelOf S.placeAt H` is the group of
elements of `stdLevel E n`, the stabilizer of the standard lattice in the finite adelic unitary
group, that reduce into `H`. Let `φ`, `φ'` be algebraic forms of weight `(κ, e)` on which the level
acts by `χ`. Their inner product is the weighted sum, over the double cosets of the rational points
and the level, of the Gram pairings of their values. It equals the index of the level in
`stdLevel E n`, times the dimension `card (WeylIndex n κ)` of the weight, times the Petersson
product of `ofAlgForm l s φ` and `ofAlgForm l s φ'`, the functions on the adelic unitary group that
belong to the forms. -/
lemma LevelPlaces.LevelForm.inner_eq_petersson {s : n → ℤˣ} (V : Space E n s)
    {κ : NumberField.InfinitePlace E → ℕ → ℕ} {e : NumberField.InfinitePlace E → ℤ}
    {l : NumberField.InfinitePlace E → n → ℤ} [V.IsStd] (h_param : IsHCParam κ e l)
    {S : LevelPlaces E}
    {H : Subgroup ((i : S.ChosenIndex ⊕ S.TwistIndex) → GL n (ResField (S.placeAt i)))} {χ : H →* ℂ}
    (φ φ' : S.LevelForm H χ κ e) :
    inner ℂ φ φ' =
      (levelOf S.placeAt H).relIndex (stdLevel E n) * card (WeylIndex n κ) *
        V.petersson (ofAlgForm l s φ.val) (ofAlgForm l s φ'.val) := by
  -- The inner product is the class sum of the Gram pairings at the level; the character factors
  -- through a finite group.
  rw [show inner ℂ φ φ' = classSum stdRatPoints (levelOf S.placeAt H)
      fun g : Gf E n ↦ gramForm (φ.val.val g) (φ'.val.val g) from
    innerAt_eq_stdClassSum (RingEquiv.refl ℂ) φ φ']
  exact V.classSum_gramForm_eq_mul_petersson h_param _ (χ.comp (levelOf.reduction S.placeAt H))
    (fun _ ↦ χ.isOfFinOrder (isMulTorsion_of_finite _)) φ.prop φ'.prop

variable [WeilData E]

/-- The one-point type `Unit` embeds in every non-empty type. -/
lemma nonempty_unit_embedding {α : Type} [h : Nonempty α] : Nonempty (Unit ↪ α) :=
  h.map Function.Embedding.punit

/-- For non-empty `n`, an arbitrary embedding of the one-point type `Unit` into `n`, that is, an
arbitrary index. -/
def arbitraryIndexEmbedding [h : Nonempty n] : Unit ↪ n := (nonempty_unit_embedding (h := h)).some

/-! ### The data and the theta kernel -/

variable (E n) in
/-- Data for a lift from `U(1)` to the definite unitary group of rank `card n > 1`: two finite
families of finite places (`New.LevelPlaces`), the chosen places, which give the level, and the
places of the twist; row lengths `rowLength τ`; and a character of weight
`-(rowLength τ + ⌊card n / 2⌋)` whose tame part is trivial off these places. -/
structure LValueData extends LevelPlaces E where
  /-- The length of the one row of the weight at `τ`; it is the order of the derivatives taken. -/
  rowLength : NumberField.InfinitePlace E → ℕ
  /-- The character of `U(1)` over the adeles that enters the lift. -/
  u1Char : AutChar E
  /-- The tame part of `u1Char`: a character of the residue field at each finite place. -/
  tamePart : (w : FinPlace E) → MulChar (ResField w) ℂ
  /-- `u1Char` has weight `-(rowLength τ + ⌊card n / 2⌋)` at `τ` and tame part `tamePart`. -/
  hasWeight : u1Char.HasWeight (fun τ : NumberField.InfinitePlace E ↦
    -(rowLength τ + card n / 2 : ℕ)) tamePart
  /-- The rank `card n` is at least `2`. -/
  one_lt_card : 1 < card n
  /-- The tame part is trivial off `toLevelPlaces.places`, the places of the two families. -/
  unramified : ∀ w ∉ toLevelPlaces.places, tamePart w = 1

namespace LValueData

section Definitions

variable (X : LValueData E n)

/-- The descent datum (`New.DescentPair`) attached to `X`: the source `W` is the standard definite
line, and the weight has one row of length `rowLength τ` at each `τ`. -/
abbrev descentPair : DescentPair E Unit n :=
  DescentPair.mk X.toLevelPlaces (signs := 1) (W := stdSpace E Unit)
    (incl := arbitraryIndexEmbedding (h := card_pos_iff.1 X.one_lt_card.le)) (numbering := 0)
    (colsPlus := fun τ ↦ Pi.single 1 (X.rowLength τ)) (colsMinus := 0) (u1Char := X.u1Char)
    (weight := fun τ ↦ -(X.rowLength τ + card n / 2 : ℕ)) (tamePart := X.tamePart)
      (hasWeight := X.hasWeight)
    (tame_eq_one := X.unramified) (rank_lt := X.one_lt_card)

section

omit [WeilData E]

omit [DecidableEq n] in
/-- At the place `τ` the weight `colsPlus` of `X.descentPair` has `rowLength τ` columns of height
one and no column of any other height. -/
lemma descentPair_colsPlus_apply (τ : NumberField.InfinitePlace E) (k : ℕ) :
    X.descentPair.colsPlus τ k = if k = 1 then X.rowLength τ else 0 :=
      Pi.single_apply 1 (X.rowLength τ) k

/-- The vector of derivatives, for the one-row weight of `X` and with variables scaled by `c`, of
the theta function of the datum `ω(g, h) f`, for a finite point `(g, h)` of `U(1) × U(n)`. -/
def kernelValue (c : ℂ) (f : 𝒮 (X.descentPair.W.hom (stdSpace E n))) (g : Gf E Unit) (h : Gf E n) :
    WeylIndexFamily (fun _ : NumberField.InfinitePlace E ↦ n) X.descentPair.columnCount → ℂ :=
  schurJet X.descentPair.columnCount (jetSeries (X.descentPair.W.hom (stdSpace E n)) c
    (X.descentPair.pairThetaKernel.ω ((1, g), 1, h) f)) *ᵥ 1

omit [DecidableEq n] in
/-- The weight `X.descentPair.columnCount` with exponent `0` in rank `1` goes up to rank `card n`
along the exponent `-rowLength τ` (`New.IsLiftWeight`): it has no column of height strictly between
`1` and `card n`, `1 < card n`, and its `rowLength τ` columns of height `1` make up the difference
of the two exponents. -/
lemma isLiftWeight : IsLiftWeight Unit n X.descentPair.columnCount (-X.rowLength ·) 0 := by
  have h_one_lt : 1 < card n := X.one_lt_card
  refine ⟨?_, by simpa using h_one_lt, ?_⟩
  · simp_all [FitsRanks, le_of_lt, ne_of_gt]
  · simp [funext_iff, DescentPair.columnCount, mixedWeight]

/-- The character `X.descentPair.charW`, the power of the splitting character of the Weil
representation whose exponent is the number of negative signs of the source, has trivial tame part
and weight `X.descentPair.detExp`, the exponent of the determinant in the weight on `V`. The source
is definite and the weight has no `colsMinus`, so both exponents are `0`. -/
instance charW_hasWeight : X.descentPair.charW.HasWeight X.descentPair.detExp 1 :=
  (WeilData.hasWeight_upsilonU1_pow _).of_weight_eq (by simp [funext_iff])

/-- The character `X.descentPair.charV`, which is `X.u1Char` times the power `⌊card n / 2⌋` of
`WeilData.upsilonU1`, has weight `-rowLength τ` at each infinite place `τ` and tame part
`X.tamePart`. -/
instance charV_hasWeight : X.descentPair.charV.HasWeight (-X.rowLength ·) X.tamePart :=
  X.hasWeight.hasWeight_rankTwist.of_weight_eq (by simp)

/-- The theta kernel `New.thetaKernel` between the standard spaces of ranks `1` and `card n`, for
the weight and the characters of `X`, with derivatives scaled by `1`. As a `New.Kernel` it is an
action of the finite points of both groups on Schwartz functions, with a jet map to vectors of the
weight, of exponent `0` in rank `1` and `detExp` in rank `card n`. The subgroup `⊤` is the level
at which its lifts would integrate. -/
abbrev liftKernel :
    Kernel Unit n X.descentPair.columnCount 0 X.descentPair.detExp ⊤
      ↥((stdSpace E Unit).hom (stdSpace E n)).finitePart :=
  thetaKernel X.isLiftWeight 1 X.charW_hasWeight X.charV_hasWeight ⊤

omit [DecidableEq n] in
/-- Every point `x` of the archimedean unitary group `GInf E X.descentPair.signs` of the definite
line acts trivially: `conjWeylRep` of the weight `X.descentPair.columnCount` with exponent `0` sends
`x` to `1`. -/
@[simp]
lemma conjWeylRep_eq_one (x : GInf E X.descentPair.signs) :
    conjWeylRep X.descentPair.columnCount 0 x = 1 := by
  simp_all [conjWeylRep, schur_eq_one, weylRep]

end

/-! ### The kernel as a form on `V`, and the lift -/

/-- For a finite point `g` of `U(1)`, the function `h ↦ X.kernelValue 1 f g h` as an algebraic
form on the standard space `V` of rank `card n`. Here `f = X.descentPair.blockDatum` is the block
datum at the places of `X` times the vacuum. -/
def kernelForm (g : Gf E Unit) : X.descentPair.FormV :=
  -- The level acts through its character, by the law `DescentPair.omega_blockDatum_eq_smul`; so the
  -- function is smooth.
  have h_level (k : X.descentPair.levelGroup) :
      rightRegular ℂ (Gf E n) _ k.1 (X.kernelValue 1 X.descentPair.blockDatum g) =
        X.descentPair.residueLevelChar.comp (levelOf.reduction ..) k •
          X.kernelValue 1 X.descentPair.blockDatum g := by
    ext h' i
    have h_omega : X.descentPair.pairThetaKernel.ω ((1, 1), 1, k.val) X.descentPair.blockDatum.val =
        X.descentPair.residueLevelChar.comp (levelOf.reduction ..) k •
          X.descentPair.blockDatum.val := by
      simpa using X.descentPair.omega_blockDatum_eq_smul 1 ⟨k, levelOf_le_stdLevel k.2⟩
        (levelOf.reduction _ _ k) (by simp [levelOf.reduction]; rfl)
    -- The jets are linear in the datum, and `ω` is multiplicative.
    simpa [kernelValue, rep_apply_apply, smul_mulVec] using
      congr_fun (congr_fun (congr_arg (X.kernelValue 1 · g) h_omega) h') i
  -- Equivariance under the rational points of `V` is that of the theta kernel.
  ⟨⟨X.kernelValue 1 X.descentPair.blockDatum g,
    mem_smoothFunctions_of_eigen _ isOpen_levelOf h_level,
      fun γ h ↦ by simpa [Kernel.omega_omega] using!
        X.liftKernel.equivariant 1 γ (X.liftKernel.ω (g, h) X.descentPair.blockDatum) 1⟩,
    fun k ↦ Subtype.ext (h_level k)⟩

/-- The principal level of the finite adelic U(1) at the places `chosenPlace`: integral elements
that reduce to 1 at each of these places. -/
abbrev chosenLevel : Subgroup (Gf E Unit) := levelOf (n := Unit) X.chosenPlace ⊥

/-- The lift of the character of `X`: the class sum of the kernel `New.LValueData.kernelForm` over
`U(1)` at the principal level at the chosen places. It is a multiple of the theta lift of the
constant function `1`. -/
def trivialLift : X.descentPair.FormV := stdClassSum X.chosenLevel X.kernelForm

end Definitions

/-- Let `X` be data for a lift from `U(1)`. The theta kernel `X.kernelForm` is a function from the
finite adelic points `g` of `U(1)` to algebraic forms on the definite space of rank `card n`. It is
invariant under rational points on the left and, on the right, under `X.chosenLevel`, the integral
points that reduce to `1` at the places `X.chosenPlace`, one of the two finite families of places
in `X`. -/
lemma kernelForm_invariant (X : LValueData E n) :
    stdRatPoints.FixesLeft X.kernelForm ∧ X.chosenLevel ≤ rightStabilizer X.kernelForm := by
  constructor
  · -- Left invariance is the equivariance of the theta kernel; `U(1)` acts trivially on the weight.
    rintro _ ⟨γ, hγ⟩ g
    refine Subtype.ext (Subtype.ext (funext fun h ↦ ?_))
    simpa [kernelForm, hγ, weightRep, Kernel.omega_omega] using!
      X.liftKernel.equivariant γ 1 (X.liftKernel.ω (g, h) X.descentPair.blockDatum) 1
  · -- By `omega_blockDatum_eq_smul` at `(k, 1)`, `k` multiplies `blockDatum` by a character of its
    -- reduction at the places `chosenPlace`, and that is `1`.
    rintro _ ⟨k, hk : stdLevel.reduceFamily _ k = 1, rfl⟩ g
    refine Subtype.ext (Subtype.ext (funext fun h ↦ ?_))
    have h_omega : X.descentPair.pairThetaKernel.ω ((1, k.val), 1, 1) X.descentPair.blockDatum.val =
        X.descentPair.blockDatum.val := by
      simpa [hk] using X.descentPair.omega_blockDatum_eq_smul k 1 1 (by simp [hk])
    simpa [kernelForm, kernelValue, rep_apply_apply] using
      congr_fun (congr_arg (X.kernelValue 1 · g) h_omega) h

/-- Let `X` be data for a lift from `U(1)`, and let `z` be a finite adelic point of `U(1)`. The lift
`X.trivialLift` is the weighted sum (`stdClassSum`) of the theta kernel `g ↦ X.kernelForm g` over
the double cosets of the rational points and `X.chosenLevel`, the group of integral points that
reduce to `1` at the chosen places. It is also the weighted sum of the translated kernel
`g ↦ X.kernelForm (g * z)` over the same double cosets. -/
lemma trivialLift_eq_stdClassSum_translate (X : LValueData E n) (z : Gf E Unit) :
    X.trivialLift = stdClassSum X.chosenLevel fun g : Gf E Unit ↦ X.kernelForm (g * z) := by
  -- The group is commutative, so conjugation by `z` fixes the level, and translation by `z` only
  -- permutes the classes.
  obtain ⟨h_left : stdRatPoints.FixesLeft X.kernelForm,
    h_right : X.chosenLevel ≤ rightStabilizer X.kernelForm⟩ := X.kernelForm_invariant
  have h_out (g : Gf E Unit) :
      X.kernelForm (DoubleCoset.mk stdRatPoints X.chosenLevel (g * z)).out =
        X.kernelForm (g * z) :=
    apply_doubleCoset_out h_left h_right (g * z)
  have h_conj : X.chosenLevel.comap (MulAut.conj z : Gf E Unit →* Gf E Unit) = X.chosenLevel := by
    simp [SetLike.ext_iff, mul_comm' z]
  have h_translate :
      classSum stdRatPoints X.chosenLevel (fun g : Gf E Unit ↦ X.kernelForm (g * z)) =
        (X.chosenLevel.relIndex X.chosenLevel : ℚ) •
          classSum stdRatPoints X.chosenLevel X.kernelForm :=
    classSum_eq_relIndex_smul le_rfl z h_conj h_out
  -- The index of the level in itself is `1`.
  rw [Subgroup.relIndex_self, Nat.cast_one, one_smul] at h_translate
  exact h_translate.symm

/-! ### Adjointness of the lift and the descent -/

omit [WeilData E] in
/-- Let `X` be data for a lift from `U(1)`, and let `η` be a coordinate vector of the Weyl module
whose weight, that of the descent datum `X.descentPair`, has one row of length `X.rowLength τ` at
each infinite place `τ`. The polynomial `toPoly (fun _ ↦ n) _ η`, with rows indexed by `n` at every
place, is `∑ i, (G η) i • b i`, for the Gram matrix `G` and the basis `b` of products of minors. It
is obtained from the Fock polynomial `X.descentPair.fockPoly η` by renaming the variable at the
place `τ`, row `a` and the one column `u` to the variable with row index `⟨τ, a⟩` and column `0`. -/
lemma toPoly_eq_rename_fockPoly (X : LValueData E n)
    (η : WeylIndex n (mixedWeight n X.descentPair.colsPlus X.descentPair.colsMinus) → ℂ) :
    toPoly (fun _ : NumberField.InfinitePlace E ↦ n)
        (mixedWeight n X.descentPair.colsPlus X.descentPair.colsMinus) η =
      rename (fun ((τ, a, _) : NumberField.InfinitePlace E × n × Unit) ↦ (⟨τ, a⟩, 0))
        (X.descentPair.fockPoly η) := by
  -- Both sides are linear in `η`, so it suffices to compare them on the translates of the
  -- evaluation vector (`ext_schur_weylEval`), where the laws `top` and `intertwines` of the matrix
  -- `mixedCartan` compute `fockPoly`.
  refine LinearMap.congr_fun (g := (rename _).toLinearMap ∘ₗ X.descentPair.fockPoly)
    (ext_schur_weylEval (rowEquivFin _) fun g : InfinitePlace E → GL n ℂ ↦ ?_) η
  have h_intertwines := (mixedCartan n X.descentPair.colsPlus 0).intertwines g
  -- `↓rowSubst_highestPoly` has to rewrite before `rowSubst` and `highestPoly` are unfolded.
  simp_all [DescentPair.fockPoly, -mulVec_mulVec, MixedCartanEmbedding.top, letterPoly, weylKernel,
    ↓rowSubst_highestPoly, rowSubst, fockLetters, X.one_lt_card, weylRep, mixedWeight,
    Pi.single_apply, kronecker_mulVec_vec, mul_vecMulVec, vecMul_transpose, vecMulVec_mul]

omit [WeilData E] in
/-- The Fock polynomial of a coordinate vector `η` for the weight `κ` of `X.descentPair` is the
matrix coefficient `z ↦ (ηᵀ G) S_κ(z) 1` (`New.schurCoeffPoly`) of the Schur matrix `S_κ`, where
`G = weylGramOver` is the Gram matrix of the weight. -/
lemma fockPoly_eq_schurCoeffPoly (X : LValueData E n)
    (η : WeylIndex n (mixedWeight n X.descentPair.colsPlus X.descentPair.colsMinus) → ℂ) :
    X.descentPair.fockPoly η = schurCoeffPoly (η ᵥ* weylGramOver) 1 := by
  -- Compare values at `z`. By `toPoly_eq_rename_fockPoly` the left side is the value of
  -- `toPoly η` at an array `y` whose evaluation vector is the translate by `z` of the evaluation
  -- vector of rank one (`schur_mulVec_weylEval`), which is `1`.
  refine funext fun z : InfinitePlace E × n × Unit → ℂ ↦ ?_
  let y : (Σ _ : InfinitePlace E, n) × ℕ → ℂ := fun x ↦ ∑ a : Unit, z (x.1.fst, x.1.snd, a) * 1
  have h_eval_fock : eval z (X.descentPair.fockPoly η) =
      eval y (toPoly _ (mixedWeight n X.descentPair.colsPlus X.descentPair.colsMinus) η) := by
    simp [y, toPoly_eq_rename_fockPoly, eval_rename, Function.comp_def]
  have h_minor (I : Fin 1 → Σ _ : InfinitePlace E, Unit) : minor ℂ I = MvPolynomial.X (I 0, 0) :=
    det_unique _
  have h_one :
      weylEval (fun _ ↦ Unit) X.descentPair.columnCount (1 : (Σ _ : InfinitePlace E, Unit) × ℕ → ℂ)
        = 1 := by
    ext
    simp +contextual [weylEval, nablaBasis_eq_one, columnCount, mixedWeight]
  -- The left side is the pairing of the translated evaluation vector with `G η`.
  rw [h_eval_fock, eval_toPoly, eval_schurCoeffPoly X.isLiftWeight]
  erw [← schur_mulVec_weylEval X.isLiftWeight.1 (fun τ a b ↦ z (τ, a, b)) 1]
  have h_gram : η ᵥ* weylGramOver = weylGramOver *ᵥ η :=
    funext fun _ ↦ by simp [mulVec, vecMul, dotProduct, weylGram_isSymm.apply, mul_comm]
  rw [h_one, dotProduct_comm, h_gram]
  simp [detPow, h_minor]
  rfl

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let `X` be data for a lift from `U(1)`. The space `X.descentPair.W.hom (stdSpace E n)` is
`Hom(W, V)`, for the standard definite spaces `W` of rank `1` and `V` of rank `card n`; `Space.θ` is
its theta functional and `ω` the Weil action of `U(W) × U(V)` on its Schwartz space. The vector
`X.descentPair.fockDatum η` is the Fock vector of the polynomial `fockPoly η` at the infinite
places, tensored with the finite datum `blockDatum`: the function `residueBlockDatum` of the
residues at the places of `X`, and the vacuum at the other finite places. The theta value of its
image under `ω((x, g), (y, h))` is the bilinear pairing, by the Gram matrix, of `η` with the vector
`X.kernelForm g h` moved by `y⁻¹`. The value does not depend on the real point `x` of `U(1)`. -/
lemma theta_pairThetaKernel_omega_fockDatum (X : LValueData E n) (x : GInf E X.descentPair.signs)
    (η : WeylIndex n (mixedWeight n X.descentPair.colsPlus X.descentPair.colsMinus) → ℂ)
    (y : GInf E (1 : n → ℤˣ)) (g : Gf E Unit) (h : Gf E n) :
    Space.θ (X.descentPair.W.hom (stdSpace E n))
        (X.descentPair.pairThetaKernel.ω ((x, g), y, h) (X.descentPair.fockDatum η)) =
      gramForm (star η)
        (conjWeylRep (mixedWeight n X.descentPair.colsPlus X.descentPair.colsMinus)
          X.descentPair.detExp y⁻¹
          (X.kernelForm g h)) := by
  -- Both sides are `θ` of a Fock vector tensored with `ω((1, g), (1, h)) blockDatum`: on the left
  -- the real points act on the Fock vector alone (`pairWeil_integrated_all`); on the right the
  -- pairing is the jet along a polynomial `schurCoeffPoly` (`dotProduct_schurJet_mulVec`).
  -- `erw`, since `fockDatum`, `kernelForm` and `gramForm` have to be unfolded for these rewrites.
  erw [pairWeil_integrated_all, gramForm_apply, mulVec_mulVec, dotProduct_mulVec,
    dotProduct_schurJet_mulVec]
  -- The simp lemma `jet_jetSeries_eq_theta` turns the jet into a theta value. Then compare the
  -- vectors: `y⁻¹` moves the covector, and `x` acts trivially.
  simp [fockPoly_eq_schurCoeffPoly, realPairWeil_schurCoeffPoly X.isLiftWeight]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let `X` be data for a lift from `U(1)` with all row lengths `0`, so that the weight is trivial
and no derivative is taken. Then every coordinate of the vector valued theta kernel
`X.kernelForm g h` is the value of the scalar theta kernel `modKernel W V a b 𝔪 Ψ P`, the function
`(g, h) ↦ θ (ω(g, h) f)` for the datum `f` made of a function `Ψ` on matrices modulo `𝔪` and the
Fock vector of a polynomial `P`, at the adelic points `(1, g)` and `(1, h)` with trivial real parts.
The characters that twist `ω` are `a = 1` and `b = X.descentPair.charV`, which is `X.u1Char` times
the power `⌊card n / 2⌋` of the character `WeilData.upsilonU1`, and `P = 1`. The modulus
`𝔪 = X.levelModulus 2` is the square of the product of the chosen places times the product of the
places of the twist. The function `Ψ` reduces a matrix at each of these places (`levelResidueAt`)
and applies `residueBlockDatum`: this is `0` unless the reductions at the chosen places are the
basis vector `incl ()`, and then the product, over the places of the twist, of the tame characters
at the entry in the row `incl ()`. -/
lemma kernelForm_of_rowLength_eq_zero (X : LValueData E n) (g : Gf E Unit) (h : Gf E n)
    (h_rowLength : X.rowLength = 0) (i : WeylIndex n X.descentPair.columnCount) :
    X.kernelForm g h i = modKernel (stdSpace E Unit) (stdSpace E n) 1
      X.descentPair.charV (X.levelModulus 2) (fun Y : Matrix n Unit (X.levelModulus 2).ResidueRing ↦
        X.descentPair.residueBlockDatum fun j :
          X.descentPair.ChosenIndex ⊕ X.descentPair.TwistIndex ↦
          Y.map (levelResidueAt j)) 1 (1, g) (1, h) := by
  -- The coordinate `i` is the jet along the sum of row `i` of the Schur matrix, so it is the theta
  -- value of the datum with that polynomial (`jet_jetSeries_eq_theta`).
  have h_charW : X.descentPair.charW = 1 := by simp [charW]
  simp only [kernelForm, kernelValue, columnCount, mulVec_apply_eq_sum, Pi.one_apply, mul_one]
  -- `erw`, since `schurJet` has to be unfolded to a linear map in each entry.
  erw [← LinearMap.sum_apply, ← map_sum, jet_jetSeries_eq_theta, ← pairWeil_integrated_fin, h_charW]
  congr
  -- In degree zero all basis polynomials are `1`, so `sum_schur_smul_nablaBasis` says that the
  -- row sums to `1`.
  apply C_injective ((Σ _ : InfinitePlace E, Unit) × ℕ)
  simpa [nablaBasis_eq_one, schurDetExp, h_rowLength, smul_eq_C_mul, columnCount, mixedWeight,
    detPow] using sum_schur_smul_nablaBasis X.isLiftWeight.1 _ i

/-- The form `X.kernelForm g` is the kernel `New.DescentPair.vectorKernelForm` of the pair
`X.descentPair` at the point `(x, g)` of `U(1)`, for every real component `x`. -/
lemma kernelForm_eq_vectorKernelForm (X : LValueData E n) (x : GInf E X.descentPair.signs)
    (g : Gf E Unit) :
    X.kernelForm g = X.descentPair.vectorKernelForm (x, g) := by
  refine Subtype.ext (Subtype.ext (funext fun h ↦ ext_gramForm_left fun ζ ↦ ?_))
  change gramForm ζ (X.kernelForm g h) = gramForm ζ (X.descentPair.vectorKernel (x, g) h)
  rw [gramForm_vectorKernel, pairTheta]
  simpa using (X.theta_pairThetaKernel_omega_fockDatum x (star ζ) 1 g h).symm

/-- The descent `New.DescentPair.normalizedDescent` of a form `y` on `V`, at the point `(x, g)` of
`U(1)`, is the inner product of the kernel `X.kernelForm g` with `y`. -/
lemma normalizedDescent_eq_inner_kernelForm (X : LValueData E n) (x : GInf E X.descentPair.signs)
    (y : X.descentPair.FormV) (g : Gf E Unit) :
    X.descentPair.normalizedDescent y (x, g) = inner ℂ (X.kernelForm g) y := by
  rw [X.kernelForm_eq_vectorKernelForm x, normalizedDescent_eq_inner_vectorKernelForm]

/-- For a form `y` on `V` and a finite point `z` of `U(1)`, the inner product of the lift
`X.trivialLift` with `y` is the class sum over `U(1)`, at the principal level at the chosen places,
of `g ↦ θ y (g z)`, where `θ` is the descent `New.DescentPair.normalizedDescent`. -/
lemma inner_trivialLift (X : LValueData E n) (z : Gf E Unit) (y : X.descentPair.FormV) :
    inner ℂ X.trivialLift y =
      stdClassSum X.chosenLevel fun g : Gf E Unit ↦
        X.descentPair.normalizedDescent y (1, g * z) := by
  simp_rw [X.trivialLift_eq_stdClassSum_translate z, X.normalizedDescent_eq_inner_kernelForm]
  -- The inner product with `y` is additive in its first argument, so commutes with class sums.
  simpa using map_classSum (innerSLFlip ℂ y) fun g : Gf E Unit ↦ X.kernelForm (g * z)

/-! ### The hook number of the weight -/

omit [DecidableEq n] [WeilData E] in
/-- The hook number (the Fock pairing of the highest weight polynomial with itself) of the weight
`κ` of `X.descentPair`, in rank `card n` at every place, is the product of the `(rowLength τ)!`. -/
lemma hookNumber_eq_prod_factorial (X : LValueData E n) :
    hookNumber X.descentPair.columnCount (rankAt fun _ ↦ n) =
      ∏ τ : NumberField.InfinitePlace E, (X.rowLength τ).factorial := by
  -- The weight has one row at each place, of length `rowLength`.
  have h_weight (τ : InfinitePlace E) (j : ℕ) :
      X.descentPair.columnCount τ j = if j = 1 then X.rowLength τ else 0 := by
        simp [columnCount, mixedWeight, Pi.single_apply]
  rw [hookNumber_one_row (fun _ ↦ X.one_lt_card) fun τ j hj _ ↦ by simp [h_weight, hj.ne']]
  simp [h_weight]

/-- Let `X` be data for a lift from `U(1)`, with row lengths `X.rowLength τ`. Let `pairWeil` be the
Weil action `ω` of `U(1) × U(n)`, twisted by `charW` and `charV`, and let `blockDatum` be the
finite datum that is given by residues at the places of `X` and is the vacuum elsewhere. The jet
series `jetSeries _ c f` is the Taylor series `F` of the theta function of `f` in the variable
multiplied by `c`, and `schurJet κ F` is the matrix of the `P(∂) F` at `0`, for `P` the entries of
the Schur matrix of the weight `κ`. For `f = ω(g, h) blockDatum` its row sums are
`c ^ ∑ τ, X.rowLength τ` times the coordinates of `X.kernelForm g h`, the row sums at `c = 1`. -/
lemma schurJet_jetSeries_eq_kernelForm (X : LValueData E n) (c : ℂ) (g : Gf E Unit) (h : Gf E n)
    (i : WeylIndex n X.descentPair.columnCount) :
    (schurJet X.descentPair.columnCount (jetSeries ((stdSpace E Unit).hom (stdSpace E n)) c
        (pairWeil (stdSpace E Unit) (stdSpace E n) X.descentPair.charW X.descentPair.charV
          ((1, g), 1, h)
          X.descentPair.blockDatum)) *ᵥ 1) i =
      c ^ (∑ τ : NumberField.InfinitePlace E, X.rowLength τ) * X.kernelForm g h i := by
  have h_boxes : boxes X.descentPair.columnCount (card n) = ∑ τ : InfinitePlace E,
    X.rowLength τ := by
    simp [boxes, DescentPair.columnCount, mixedWeight, Pi.single_apply, X.one_lt_card]
  rw [schurJet_jetSeries_eq_smul X.isLiftWeight c, h_boxes, smul_mulVec]
  rfl

end LValueData

end CharacterLift

/-! ## The parameter of the line and a Hecke operator -/

section DescentPairHecke

variable {E r n : Type} [Field E] [CMType E] [WeilData E] [Fintype r] [DecidableEq r] [Fintype n]

omit [WeilData E] in
/-- On a line, the weight of `X.descentPair` with determinant exponent `0` has the Harish-Chandra
parameter `0`. -/
lemma LValueData.isHCParam_zero (X : LValueData E n) :
    IsHCParam X.descentPair.columnCount 0 (0 : NumberField.InfinitePlace E → Unit → ℤ) := by
  have h_empty : Finset.Ioo 0 1 = (∅ : Finset ℕ) := rfl
  exact fun w ↦ ⟨Function.injective_of_subsingleton _, fun _ ↦
    ⟨0, by simp, by simp [hcParameter, diagramWeight_apply, h_empty]⟩⟩

omit [WeilData E] in
/-- Let `X` be data for a lift from `U(1)`. Its descent datum `X.descentPair` goes from the standard
positive definite space `W` of rank `1` to the standard space `V` of rank `card n`, with a weight
that has one row at each infinite place. The parameter `0` on `W` fits this datum. It corresponds
under the block rule to `paramV`, twice the Harish-Chandra parameter of the weight of the forms on
`V`. The index `numbering` of the one basis vector of `W` is `0`, its position in the order by the
parameter. The partitions `colsPlus` and `colsMinus` have no column higher than the number of basis
vectors of `W` with sign `1` and `-1`. -/
lemma LValueData.fitsParams_descentPair (X : LValueData E n) : X.descentPair.FitsParams 0 := by
  classical
  -- Both spaces are definite, and the weight `0` on the line goes up to the weight on `V`.
  have h_correspond :
      ParamsCorrespond X.descentPair.detExp (-X.rowLength ·) 0 X.descentPair.paramV 1 1 :=
    (X.isHCParam_zero.paramsCorrespond_iff X.isLiftWeight).2 X.descentPair.isHCParam_paramV
  have h_detExp : (fun _ : InfinitePlace E ↦ (Exchange.negCount X.descentPair.signs : ℤ)) =
      X.descentPair.detExp := by simp [funext_iff, DescentPair.detExp, Exchange.negCount]
  -- The other conditions are clear on a line (only columns of height `1` occur).
  exact
    { paramsCorrespond := by simpa [← h_detExp] using h_correspond
      numbering_eq := by simp
      colsPlus_eq_zero τ i h_gt := by
        have h_ne : i ≠ 1 := by simpa using h_gt.ne'
        rw [X.descentPair_colsPlus_apply, ite_eq_right h_ne]
      colsMinus_eq_zero := by simp }

/-- Let `O` be a descent datum from a space `W` of rank `card r` to the standard space `V` of rank
`card n`, and let `w` be a split place of norm `q` with `w` and `star w` off the places of `O`. Let
`y` be an algebraic form on `V` of the weight and level of `O` (`O.FormV`) with the Hecke
polynomials of a lift of the eigensystem `z`: at such places `y` is spherical, and its Hecke
polynomial is `∏_{l < t} (1 - q ^ l ν T)` times a rescaled Hecke polynomial of rank `card r` with
eigenvalues `z w`, where `t = card n - card r` and `ν = O.charW.frobValue r w`. Then the operator
`O.heckePolyOnForms hw hw_level T = ∑_i (-T) ^ i q ^ (i (i - 1) / 2) T_{w,i}` annihilates `y` at
`T = O.liftHeckeRoot w = (ν q ^ (t - 1))⁻¹`, the zero of the factor with `l = t - 1`. -/
lemma DescentPair.heckePolyOnForms_liftHeckeRoot_eq_zero {O : DescentPair E r n} {w : FinPlace E}
    (hw : star w ≠ w) (hw_level : w ∉ O.places.conjClosure) [DecidableEq n] {y : O.FormV}
    {z : FinPlace E → ℕ → ℂ} (h_lifts : O.HasLiftHeckePolynomial y z) :
    O.heckePolyOnForms hw hw_level (O.liftHeckeRoot w) y = 0 := by
  -- `O.heckePolyOnForms` acts on `y` by the value of its Hecke polynomial, and `O.liftHeckeRoot w`
  -- is the zero of the last factor `1 - q ^ k * ν * X` of `SiegelWeil.qPochhammer`, where
  -- `O.rankDiff = k + 1`.
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt O.rank_lt
  have h_zero : SiegelWeil.qPochhammer w.q O.rankDiff (O.charW.frobValue r w * O.liftHeckeRoot w) =
    0 := by
    simp [liftHeckeRoot, rankDiff, hk, Finset.prod_range_succ, add_assoc, AutChar.frobValue,
      HeckeChar.atUniformizer, field]
  rw [O.heckePolyOnForms_eq_smul _ _ (h_lifts w hw hw_level), h_zero, zero_mul, zero_smul]

end DescentPairHecke

/-!
## Galois conjugates of the lift

With no places of the twist and even rank, a conjugate of the lift is, up to simple factors, the
lift of the conjugate character. The semilinear map that conjugates Taylor series of theta
functions is moved past the Weil operators; on the block datum it acts by a central element, which
only permutes the classes of `U(1)`.
-/

section CharacterLiftGalois

open Matrix Finset Fintype Space Prod G Rows Parameters

/-- Let `κ τ j` be the number of columns of height `j` of a partition at the index `τ : Φ`, and let
this weight `κ` fit the ranks `1` and `card n`. For a power series `F` in the entries of columns
`z τ` of size `n`, the matrix `schurJet κ F` has the entries `P(∂) F` at `0`, for `P` the entries of
the Schur matrix `schur κ z`. Let `e` be a permutation of `Φ`. If the variables of `F` are renamed
along `e.symm`, this matrix for `κ` is that of `F` for the weight `κ ∘ e.symm`, with rows and
columns permuted by `e`. -/
lemma schurJet_rename_perm {Φ n : Type} [Fintype Φ] [DecidableEq Φ] [Fintype n] [DecidableEq n]
    {κ : Φ → ℕ → ℕ} (hκ : FitsRanks (fun _ : Φ ↦ Unit) (fun _ : Φ ↦ n) κ) (e : Equiv.Perm Φ)
    (F : MvPowerSeries (Φ × n × Unit) ℂ) :
    schurJet κ (F.rename (Prod.map e.symm id)) =
      (schurJet (fun τ : Φ ↦ κ (e.symm τ)) F).submatrix (e.piCongrLeft' _) (e.piCongrLeft' _) := by
  have hκ_perm : FitsRanks (fun _ : Φ ↦ Unit) _ (fun τ : Φ ↦ κ (e.symm τ)) := (hκ <| e.symm ·)
  ext i j
  -- It suffices that the polynomials at `(i, j)` correspond under the renaming of the variables.
  apply jet_rename (Equiv.prodCongr e.symm 1).toEmbedding
  rw [map_schur hκ_perm, schur_apply_eq_prod hκ, ← e.symm.prod_comp, schur_apply_eq_prod hκ_perm]
  simp
  rfl

/-- In `U(1) × U(n)` acting on matrices `n × 1` (`G.onHom`), right translation of `g` by the scalar
`z⁻¹` of `U(1)` is right translation of the image of `(g, h)` by the scalar `z`. -/
lemma onHom_mul_scalarFin_inv {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
    (g : Gf E Unit) (h : Gf E n) (z : unitary (𝔸f E)) :
    G.onHom (s := 1) (s' := 1) ((1, g * scalarFin Unit z⁻¹), 1, h) =
      G.onHom ((1, g), 1, h) * (1, scalarFin (n × Unit) z) := by
  have h_scalar : G.onHom (s := 1) (s' := 1) ((1, scalarFin Unit z⁻¹), 1, scalarFin n 1) =
      (1, scalarFin (n × Unit) z) := by rw [onHom_scalarFin, one_div, inv_inv]
  simp [← h_scalar, ← map_mul]

/-- The space `Hom(W, V)` from the standard line `W` to the standard space `V` of rank `card n`;
its signs `homSigns 1 1`, the products of those of `W` and `V`, are all `1`. -/
abbrev stdLineHom (E n : Type) [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] :
    Space E (n × Unit) (homSigns 1 1) := (stdSpace E Unit).hom (stdSpace E n)

/-- Let `L` be a `σ`-semilinear map on the Schwartz space of `stdLineHom`, the space `Hom(W, V)` of
columns for the standard spaces `W`, `V` of ranks `1` and `card n = 2 * m`. Let `L` scale finite
translations by `b`. Let `X` be data for a lift from `U(1)` with no places of the twist; `X.u1Char`
is its character of adelic `U(1)`. For a Schwartz–Bruhat function `Ψ` at the places of `X`, let
`schrodingerOp X.places Ψ` be the combination of Heisenberg operators that realizes `Ψ` in the
Schrödinger model, and let `vacElem` be the vacuum. For every such `Ψ` let `L` send
`schrodingerOp X.places Ψ vacElem` to `l ω(z)` applied to the same vector for `σ ∘ Ψ`. Let `Y` be
data with the places of `X` whose character agrees with `σ ∘ X.u1Char` on finite points. Let `g` and
`h` be finite points of `U(1)` and `U(n)`. Let `f = X.descentPair.blockDatum` be the block datum: at
the chosen places the indicator of the columns that reduce to a fixed basis vector, and the vacuum
elsewhere. Then `L` carries `ω(g, h) f`, for the Weil action `ω` of the pair, to a multiple of the
same vector for `Y` at `(g z⁻¹, h)`. The factor is the product of `l`, the value at `z⁻¹` of
`Y.descentPair.charV`, and `multiplierRatio σ = σ Δ / Δ`, for the multiplier `Δ` of the Weil
representation, at the finite component of `x ↦ h x`, the image of `(1, 1, h)` under `G.onHom`. -/
lemma LValueData.map_pairWeilFinite_blockDatum {P : Parameters} {s : ℕ} {n : Type} [Fintype n]
    [DecidableEq n] {σ : Gal(ℂ/K P)} {b : 𝔸f (P.E s)} {l : ℂ} {z : unitary (𝔸f (P.E s))}
    {L : 𝒮 (stdLineHom (P.E s) n) →ₛₗ[(σ : ℂ →+* ℂ)] 𝒮 (stdLineHom (P.E s) n)}
    (hL_scale : (stdLineHom (P.E s) n).ScalesTranslations σ b L)
    (X : LValueData (P.E s) n) (h_no_twist : IsEmpty X.TwistIndex)
    (hL_schrodinger : ∀ Ψ : (n × Unit → 𝔸f (P.E s)) → ℂ, IsSchwartzBruhat X.places Ψ →
      L ((stdLineHom (P.E s) n).schrodingerOp X.places Ψ (stdLineHom (P.E s) n).vacElem) =
        l • (stdLineHom (P.E s) n).ω (1, scalarFin (n × Unit) z)
          ((stdLineHom (P.E s) n).schrodingerOp X.places (σ ∘ Ψ) (stdLineHom (P.E s) n).vacElem))
    {m : ℕ} (hm : Fintype.card n = 2 * m)
    (Y : LValueData (P.E s) n) (hY_places : Y.toLevelPlaces = X.toLevelPlaces)
    (hY_char : ∀ u : unitary (𝔸 (P.E s)), (u : 𝔸 (P.E s)).fst = 1 →
      Y.u1Char.val u = σ (X.u1Char.val u))
    (g : Gf (P.E s) Unit) (h : Gf (P.E s) n) :
    L (pairWeilFinite X.descentPair.W (stdSpace (P.E s) n) X.descentPair.charW X.descentPair.charV
        (g, h) X.descentPair.blockDatum) =
      (l * Y.descentPair.charV.val (detFin 1 (scalarFin Unit z⁻¹)) *
          multiplierRatio σ (G.onHom (s := X.descentPair.signs) (s' := 1) (1, 1, h)).snd) •
        pairWeil (stdSpace (P.E s) Unit) (stdSpace (P.E s) n) Y.descentPair.charW
          Y.descentPair.charV ((1, g * scalarFin Unit z⁻¹), 1, h) Y.descentPair.blockDatum := by
  -- The action of a pair is a character times `ω ∘ G.onHom`. Compute `L` on the block datum
  -- (`h_datum`), move it past `ω` (`h_omega`), and compare the scalars (`h_char`).
  classical
  let V : Space (P.E s) (n × Unit) (homSigns 1 1) := stdLineHom (P.E s) n
  -- The block data realize the functions `ΨX`, `ΨY` of residues. With `TwistIndex` empty both
  -- are the same function with values `0` and `1`, which `σ` fixes.
  let ΨX : (n × Unit → 𝔸f (P.E s)) → ℂ := residueDatum X.placeAt X.descentPair.residueBlockDatum
  let ΨY : (n × Unit → 𝔸f (P.E s)) → ℂ := residueDatum Y.placeAt Y.descentPair.residueBlockDatum
  have hX_block : X.descentPair.blockDatum.val = V.schrodingerOp X.places ΨX V.vacElem := by
    simp only [DescentPair.blockDatum, places_levelModulus, liftFn_eq_residueDatum, V, ΨX]
  have hY_block : Y.descentPair.blockDatum.val = V.schrodingerOp X.places ΨY V.vacElem := by
    rw [← hY_places]
    simp only [DescentPair.blockDatum, places_levelModulus, liftFn_eq_residueDatum, V, ΨY]
  have hΨ_conj : σ ∘ ΨX = ΨY := by
    obtain ⟨S, d, μ, ψ, hμ_weight, h_card, hψ_unramified⟩ := Y
    obtain rfl : S = X.toLevelPlaces := hY_places
    ext x
    simp [ΨX, ΨY, univ_eq_empty, residueDatum, DescentPair.residueBlockDatum, apply_ite σ]
  have h_datum : L X.descentPair.blockDatum.val =
      l • V.ω (1, scalarFin (n × Unit) z) Y.descentPair.blockDatum.val := by
    rw [hX_block, hY_block, ← hΨ_conj]
    exact hL_schrodinger ΨX (isSchwartzBruhat_residueDatum _ X.apart.star_ne)
  -- The images `g'`, `h'` of `g` and `h` act on `V`, and `L` moves past each of them.
  let g' : Gf (P.E s) (n × Unit) := (G.onHom (s := 1) (s' := 1) ((1, g), 1)).snd
  let h' : Gf (P.E s) (n × Unit) := (G.onHom (s := 1) (s' := 1) (1, 1, h)).snd
  have hg' : G.onHom (s := 1) (s' := 1) ((1, g), 1) = (1, g') := onHom_fin g 1
  have hh' : G.onHom (s := 1) (s' := 1) (1, 1, h) = (1, h') := onHom_fin 1 h
  have h_onHom : G.onHom (s := 1) (s' := 1) ((1, g), 1, h) = (1, g') * (1, h') := by
    rw [← hg', ← hh', ← map_mul, mk_mul_mk, mul_one, one_mul]
  let fY : 𝒮 V := V.ω (G.onHom ((1, g * scalarFin Unit z⁻¹), 1, h)) Y.descentPair.blockDatum.val
  have h_omega : L (V.ω (G.onHom ((1, g), 1, h)) X.descentPair.blockDatum.val) =
      (multiplierRatio σ g' * multiplierRatio σ h' * l) • fY := by
    have h_mem : X.descentPair.blockDatum.val ∈ V.finitePart := X.descentPair.blockDatum.prop
    have hfY : fY = V.ω (1, g') (V.ω (1, h')
        (V.ω (1, scalarFin (n × Unit) z) Y.descentPair.blockDatum.val)) := by
      simp only [fY, onHom_mul_scalarFin_inv, h_onHom, map_mul, mul_apply_eq_comp]
    rw [hfY, h_onHom, map_mul, mul_apply_eq_comp,
      hL_scale.map_omega g' (omega_mem_finitePart h' h_mem), hL_scale.map_omega h' h_mem, h_datum]
    simp only [V, map_smul, smul_smul, mul_assoc]
  -- The ratio `σ Δ / Δ` at `g'` is that at `g⁻¹` to the power `2 * m`, and the ratio at `g⁻¹` has
  -- square `σ υ / υ` at `u = det g`.
  let u : unitary (𝔸 (P.E s)) := detFin 1 g
  let v : unitary (𝔸 (P.E s)) := detFin 1 (scalarFin Unit z⁻¹)
  have h_ratio : multiplierRatio σ g' =
      (σ (WeilData.upsilonU1.val u) / WeilData.upsilonU1.val u) ^ m := by
    have h_pow : multiplierRatio σ g' = (multiplierRatio σ g⁻¹ ^ 2) ^ m := by
      rw [← pow_mul, ← hm, multiplierRatio, multiplierRatio, finMultiplier_onHom_left, map_pow,
        div_pow]
    have h_det : detFin 1 g⁻¹ = u⁻¹ := map_inv G.det (1, g)
    rw [h_pow, multiplierRatio_sq, h_det]
    simp [div_eq_mul_inv, mul_comm]
  -- The characters `charV` are `X.u1Char υ ^ m` and `Y.u1Char υ ^ m`, and `hY_char` turns
  -- `σ X.u1Char` into `Y.u1Char`.
  have h_charV_conj :
      σ (X.descentPair.charV.val u) = Y.descentPair.charV.val u * multiplierRatio σ g' := by
    have h_char_u : Y.u1Char.val u = σ (X.u1Char.val u) := hY_char u (by simp [u, funext_iff])
    simp [h_ratio, rankTwist, hm, h_char_u, div_pow, field]
  -- The characters `charW` are trivial, so the characters of the two pairs are inverse values of
  -- `charV`.
  let χX : ℂ := pairChar (s := 1) (s' := 1) X.descentPair.charW X.descentPair.charV ((1, g), 1, h)
  let χY : ℂ :=
    pairChar (s := 1) (s' := 1) Y.descentPair.charW Y.descentPair.charV
      ((1, g * scalarFin Unit z⁻¹), 1, h)
  have hχX : χX = (X.descentPair.charV.val u : ℂ)⁻¹ := by simp [χX, DescentPair.charW, u]
  have hχY : χY = (Y.descentPair.charV.val u * Y.descentPair.charV.val v : ℂ)⁻¹ := by
    simp only [χY, pairChar_apply, ← one_mk_mul_one_mk g, map_mul]
    simp [DescentPair.charW, u, v]
  have h_char : σ χX * multiplierRatio σ g' = Y.descentPair.charV.val v * χY := by
    have h_ratio_ne : multiplierRatio σ g' ≠ 0 := by simp [h_ratio]
    rw [hχX, hχY, map_inv₀, h_charV_conj]
    field_simp
  calc L (χX • V.ω (G.onHom ((1, g), 1, h)) X.descentPair.blockDatum.val)
    _ = (σ χX * multiplierRatio σ g' * (multiplierRatio σ h' * l)) • fY := by
      rw [map_smulₛₗ, h_omega, smul_smul, mul_assoc, mul_assoc]
      rfl
    _ = (l * Y.descentPair.charV.val v * multiplierRatio σ h') • χY • fY := by
      rw [h_char, smul_smul]
      ring_nf

/-- Conjugates of the lift. The parameters `P` and the natural number `s` give the CM field `P.E s`
over the imaginary quadratic field `K P`, the positive number `P.bigOmega s` and the scale
`P.jetScale s` at which Taylor series of theta functions are taken. Fix places `S` of `P.E s` with
no places of the twist (`S.TwistIndex` is empty), and `σ ∈ Gal(ℂ/K P)`. Data `X : LValueData` on
`S` add row lengths `X.rowLength τ` at the infinite places and a character `X.u1Char` of adelic
`U(1)`. The lift `X.trivialLift` is the class sum over `U(1)` of the theta kernel of `X`; its value
at a finite point `h` of `U(n)` is a vector of the Weyl module of the one-row weight, with
coordinates `i` indexed by a basis tableau `i τ` at each `τ`.

There are constants `t`, `l` and `u` with `‖t‖ = (√(P.bigOmega s))⁻¹` and `l ≠ 0` such that the
following holds for all data `X` on `S` with `card n = 2 * m`. Let `e = placePerm s σ`, the
permutation of the infinite places by `σ`. Let `μ` be a character of weight
`-(X.rowLength (e⁻¹ τ) + card n / 2)` at each infinite place `τ`, with tame part `ψ` trivial off the
places, and `μ v = σ (X.u1Char v)` at finite points `v`. Let `Y` be the data on `S` with character
`μ` and row lengths `X.rowLength (e⁻¹ τ)`. Put `D = ∑ τ, X.rowLength τ`. The conjugate under `σ` of
the `i`-th coordinate of `P.jetScale s ^ D • X.trivialLift` at `h` is the product of `t ^ D`, `l`
and three more factors. The first is the value at `u` of `Y.descentPair.charV`, which is `μ` times
the `m`-th power of the character `WeilData.upsilonU1`. The second is
`multiplierRatio σ = σ Δ / Δ`, for the multiplier `Δ` of the Weil representation, at the finite
component of the map `x ↦ h x` on columns, the image of `(1, 1, h)` under `G.onHom`. The third is
the coordinate of the lift of `Y` at `h` with index `τ ↦ i (e⁻¹ τ)`. -/
lemma LValueData.map_trivialLift {P : Parameters} {s : ℕ} (n : Type) [Fintype n] [DecidableEq n]
    (S : LevelPlaces (P.E s)) (h_no_twist : IsEmpty S.TwistIndex) (σ : Gal(ℂ/K P)) :
    ∃ (t l : ℂ) (u : unitary (𝔸 (P.E s))),
      ‖t‖ = (√(P.bigOmega s))⁻¹ ∧
      l ≠ 0 ∧
      ∀ {X : LValueData (P.E s) n} {e : Equiv.Perm (NumberField.InfinitePlace (P.E s))}
        {μ : AutChar (P.E s)} {ψ : (w : FinPlace (P.E s)) → MulChar (ResField w) ℂ} {m : ℕ}
        (hμ_weight : μ.HasWeight
          (fun τ : NumberField.InfinitePlace (P.E s) ↦
            -(X.rowLength (e.symm τ) + Fintype.card n / 2 : ℕ)) ψ)
        (hψ_unramified : ∀ w : FinPlace (P.E s), w ∉ X.places → ψ w = 1)
        (_hX_places : X.toLevelPlaces = S),
        let Y : LValueData (P.E s) n :=
          { toLevelPlaces := X.toLevelPlaces
            rowLength := fun τ : NumberField.InfinitePlace (P.E s) ↦ X.rowLength (e.symm τ)
            u1Char := μ
            tamePart := ψ
            hasWeight := hμ_weight
            one_lt_card := X.one_lt_card
            unramified := hψ_unramified }
        ∀ (_hm : Fintype.card n = 2 * m) (_he : placePerm s σ = e)
          (_hμ : ∀ v : unitary (𝔸 (P.E s)), (v : 𝔸 (P.E s)).fst = 1 →
            μ.val v = σ (X.u1Char.val v))
          (h : Gf (P.E s) n) (i : WeylIndex n X.descentPair.columnCount),
          σ ((P.jetScale s ^ (∑ τ : NumberField.InfinitePlace (P.E s), X.rowLength τ) •
              X.trivialLift) h i) =
            (t ^ ∑ τ : NumberField.InfinitePlace (P.E s), X.rowLength τ) *
              (l * Y.descentPair.charV.val u) *
              multiplierRatio σ (G.onHom (s := X.descentPair.signs) (s' := 1) (1, 1, h)).snd *
              Y.trivialLift h fun τ : NumberField.InfinitePlace (P.E s) ↦ i (e.symm τ) := by
  -- Both sides are class sums over `U(1)`, the right one after translation by `z⁻¹`; compare them
  -- term by term. The kernels are jets of data, and the semilinear map `L` of
  -- `exists_isJetConjugation` carries one datum to a multiple of the other.
  obtain ⟨t, b, L, hL⟩ := exists_isJetConjugation (stdLineHom (P.E s) n) σ
  have hS_disjoint : S.places.IsConjDisjoint := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
    exact S.apart.star_ne i j hj.symm
  obtain ⟨l, hl : l ≠ 0, z, -, hL_schrodinger⟩ := hL.exists_map_schrodingerOp hS_disjoint
  obtain ⟨ht_sq : ‖t‖ ^ 2 = (P.bigOmega s)⁻¹, hL_scale, hL_jet⟩ := hL
  refine ⟨t, l, detFin 1 (scalarFin Unit z⁻¹), ?_, hl, ?_⟩
  · rw [← Real.sqrt_sq (norm_nonneg t), ht_sq, Real.sqrt_inv]
  rintro X e μ ψ m hμ_weight hψ_unramified rfl Y hm he hμ h i
  rw [he] at hL_jet
  set D : ℕ := ∑ τ : InfinitePlace (P.E s), X.rowLength τ
  set c : ℂ := t ^ D * (l * Y.descentPair.charV.val (detFin 1 (scalarFin Unit z⁻¹))) *
    multiplierRatio σ (G.onHom (s := X.descentPair.signs) (s' := 1) (1, 1, h)).snd
  set i' : WeylIndex n Y.descentPair.columnCount := fun τ : InfinitePlace (P.E s) ↦ i (e.symm τ)
  suffices h_term : ∀ g : Gf (P.E s) Unit, σ (P.jetScale s) ^ D * σ (X.kernelForm g h i) =
      c * Y.kernelForm (g * scalarFin Unit z⁻¹) h i' by
    have hX_sum : (P.jetScale s ^ D • X.trivialLift) h i =
        P.jetScale s ^ D * stdClassSum X.chosenLevel fun g ↦ X.kernelForm g h i :=
      congrArg (P.jetScale s ^ D * ·) (map_classSum (LinearMap.proj i ∘ₗ evalForm h) X.kernelForm)
    have hY_sum : Y.trivialLift h i' =
        stdClassSum X.chosenLevel fun g ↦ Y.kernelForm (g * scalarFin Unit z⁻¹) h i' := by
      rw [Y.trivialLift_eq_stdClassSum_translate (scalarFin Unit z⁻¹)]
      exact map_classSum (LinearMap.proj i' ∘ₗ evalForm h) _
    rw [hX_sum, hY_sum, map_mul, map_pow, map_classSum, mul_classSum, mul_classSum]
    exact congrArg (stdClassSum X.chosenLevel) (funext h_term)
  intro g
  -- The jets of `f = ω(g, h) blockDatum` are the kernel of `X`; its image under `L` is a multiple
  -- of the datum of `Y` at `(g z⁻¹, h)`.
  let V : Space (P.E s) (n × Unit) (homSigns 1 1) := stdLineHom (P.E s) n
  let f : V.finitePart := pairWeilFinite (stdSpace (P.E s) Unit) (stdSpace (P.E s) n)
    X.descentPair.charW X.descentPair.charV (g, h) X.descentPair.blockDatum
  calc σ (P.jetScale s) ^ D * σ (X.kernelForm g h i)
    _ = σ ((schurJet X.descentPair.columnCount (jetSeries V (P.jetScale s) f) *ᵥ 1) i) := by
      rw [← map_pow, ← map_mul, ← X.schurJet_jetSeries_eq_kernelForm]
      rfl
    _ = (schurJet X.descentPair.columnCount
          ((jetSeries V (P.jetScale s) f).map (σ : ℂ →+* ℂ)) *ᵥ 1) i := by
      simp [mulVec, dotProduct, ← map_schurJet X.isLiftWeight]
    _ = (schurJet Y.descentPair.columnCount (jetSeries V t (L f)) *ᵥ 1) i' := by
      rw [hL_jet f f.prop, schurJet_rename_perm X.isLiftWeight.1 e, submatrix_mulVec_equiv]
      rfl
    _ = c * Y.kernelForm (g * scalarFin Unit z⁻¹) h i' := by
      rw [X.map_pairWeilFinite_blockDatum hL_scale h_no_twist hL_schrodinger hm Y rfl hμ g h]
      simp only [map_smul, smul_mulVec, Pi.smul_apply, smul_eq_mul]
      rw [Y.schurJet_jetSeries_eq_kernelForm, Equiv.sum_comp e.symm X.rowLength]
      ring

end CharacterLiftGalois

end New

end
