import Lib.Adelic.AutomorphicForms.AutomorphicAsAlgebraic
import Lib.ClassField.HeckeCharacter.TameModulus
import Lib.GLn.Dual
import Lib.General.Algebra.LevelModulus
import Lib.Weil.Unramified.HeckeTransfer

/-!
# Descent pairs: descent data for theta lifts to definite unitary groups

This file sets up the theta lift from U(W), with W of rank r, to the definite group U(V), with
V = `New.stdSpace` of rank n > r, and the descent from V to W. One structure, `New.DescentPair`,
holds the data: the places of the level, the space W, an embedding of the indices of its basis into
those of V, a numbering of its basis vectors, the numbers of columns k⁺ and k⁻, and a character of
U(1)(𝔸) with its weight and tame part. The level sits at two finite families of split places
(`New.LevelPlaces`): M, the chosen places `chosenPlace`, and Q, the places `twistPlace` of the
twist. The residue field at w is k_w = `New.ResField w`. The finite datum Ψ_bl ⊗ vac is a vector of
the Weil representation `New.pairWeil` on `Hom(W, V)`: the block datum Ψ_bl, a function of the
reductions of a matrix at M and Q, with the vacuum at the other finite places.

For a descent pair `O`, the character of the descent datum is `O.u1Char`, with weight `O.weight` and
tame part `O.tamePart`. The highest weight of the forms on V is `(O.columnCount, O.detExp)`, given
by numbers of columns. Vectors of the representation of this weight are written ξ, and forms on V
are written Ξ.

## Main definitions and results

* `New.DescentPair`: the data of a descent pair; `New.DescentPair.FormV`: its forms on V, with the
  action `New.DescentPair.formAction` of ∏_M GL_r and the Hecke polynomial
  `New.DescentPair.heckePolyOnForms`.
* `New.DescentPair.fockPoly`, `New.DescentPair.blockDatum`, `New.DescentPair.conjKernel`,
  `New.DescentPair.normalizedDescent`: the Fock polynomial of a vector, the finite datum Ψ_bl ⊗ vac,
  the conjugate theta kernel as a linear form on weight vectors, and the normalized descent from
  forms on V to functions on U(W)(𝔸).
* `New.DescentPair.blockDatum_eq_sum_modDatum`: Ψ_bl ⊗ vac is the sum of the translates of Ψ¹ ⊗ vac,
  with Ψ¹ = `New.DescentPair.identityBlockIndicator`, by lifts (`New.LevelPlaces.twistResidueLift`)
  of the inverses of the elements of `∏ GL(k_w)` over `Q` (`New.LevelPlaces.TwistGL`).
* `New.DescentPair.paramV`, `New.DescentPair.isHCParam_paramV`: the doubled parameter `l'` of the
  weight of forms on `V`.
* `New.DescentPair.FitsParams`: the data of a descent pair `O` are those of a parameter `l` on `W`
  and `l'` on `V`.
* `New.DescentPair.FitsParams.exists_isJointHarmonic`, `New.DescentPair.FitsParams.isEdge`: then the
  polynomial of the highest vector is a product of joint harmonics (staircases of minors), so it is
  an edge from `l` to `l'`.
* `New.DescentPair.normalizedDescent_eq_smul_star_lift_swap`: the normalized descent
  `New.DescentPair.normalizedDescent`, defined by a class sum, is a multiple of the descent by the
  datum of the highest vector, the conjugate of the transposed lift (`New.Space.lift` from `V` to
  `W`) of the conjugate form.

Notions from other files:
* `New.levelOf w H`: the subgroup of K₀ = `New.stdLevel` of the elements whose reductions at the
  places `w i` form an element of H.
* `New.levelSpace π K χ`: the vectors on which each k in K acts through π by the scalar χ(k).
* `New.HasHeckePolynomial π hw p y`: y is spherical at the split place w, and the Hecke polynomial
  at T acts on it by p(T).
* `New.IsJointHarmonic`: a nonzero polynomial that is highest, of the lowest K-types, for the row
  and the column actions and harmonic in both directions.

## Relation to the literature

See `Lib.Adelic.Unitary.CongruenceLevels` for sources.
-/

noncomputable section

namespace New

/-!
## Descent pairs, their level and their lifts

Block 0 is the image of the embedding r ↪ n, block 1 the rest (`New.rangeParabolic`).

* `New.DescentPair.HasLiftHeckePolynomial`: a form on V has the Hecke polynomials of a lift of a
  given eigensystem.
-/

section DescentPair

open Matrix NumberField ComplexConjugate Fintype Subgroup Space WeilData Rows Sum

section

variable {E r n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype r] [DecidableEq r]
  [Fintype n] [DecidableEq n] (S : LevelPlaces E) (u : r ↪ n)

/-- The finite group given by the product over the M-places w of GL_r of the residue field at w. -/
abbrev LevelPlaces.ChosenGL (r : Type) [Fintype r] [DecidableEq r] : Type :=
  ∀ i : S.ChosenIndex, GL r (ResField (S.chosenPlace i))

/-! ### Levels at the places of M and Q -/

-- Two spellings of one place are compared without unfolding its ring of integers.
attribute [local irreducible] IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers

/-- The homomorphism sending (g_w) in ∏_M GL_r(k_w) to the family equal to diag(g_w, 1) at the
places of M and 1 at those of Q. -/
def firstBlockHom :
    S.ChosenGL r →* ∀ i : S.ChosenIndex ⊕ S.TwistIndex, GL n (ResField (S.placeAt i)) :=
  MonoidHom.pi fun
    | .inl i => (extendGL u).comp (Pi.evalMonoidHom _ i)
    | .inr _ => 1

/-- At a place w of M the component of `firstBlockHom S u g` is diag(g_w, 1). -/
lemma firstBlockHom_apply_inl (g : S.ChosenGL r) (i : S.ChosenIndex) :
    firstBlockHom S u g (inl i) = extendGL (R := ResField (S.placeAt (inl i))) u (g i) := rfl

/-- At a place of Q the component of `firstBlockHom S u g` is 1. -/
lemma firstBlockHom_apply_inr (g : S.ChosenGL r) (i : S.TwistIndex) :
    firstBlockHom S u g (inr i) = 1 := rfl

/-- The group of families in GL_n(k_w) that at the places of M fix the basis vectors indexed by u,
and at the places of Q preserve the span of the other basis vectors. -/
def descentResidueLevel : Subgroup (∀ i : S.ChosenIndex ⊕ S.TwistIndex,
  GL n (ResField (S.placeAt i))) :=
  pi Set.univ fun
    | .inl i => MulAction.stabilizer (GL n (ResField (S.placeAt (inl i))))
        (inclMatrix (ResField (S.placeAt (inl i))) u).col
    | .inr _ => rangeParabolic u

omit [Fintype r] [DecidableEq r] in
/-- A family `g` lies in `New.descentResidueLevel S u` if and only if two conditions hold. First, at
each chosen place (`S.ChosenIndex`) it fixes the n × r inclusion matrix of `u`, whose columns are
the basis vectors indexed by `u`. Second, at each place of the twist (`S.TwistIndex`) it lies in the
opposite parabolic `New.rangeParabolic u`. -/
lemma mem_descentResidueLevel_iff {g : ∀ i : S.ChosenIndex ⊕ S.TwistIndex, GL n (ResField
  (S.placeAt i))} :
    g ∈ descentResidueLevel S u ↔
      (∀ i : S.ChosenIndex, (g (inl i)).val * inclMatrix (ResField (S.placeAt (inl i))) u =
        inclMatrix (ResField (S.placeAt (inl i))) u) ∧
      ∀ i : S.TwistIndex, g (inr i) ∈ rangeParabolic u := by
  simp only [descentResidueLevel, mem_pi, Set.mem_univ, true_implies, Sum.forall,
    mem_stabilizer_col_iff]

/-- Conjugation by `firstBlockHom S u s` does not change the components of `x` at the places of the
twist, indexed by `S.TwistIndex`. -/
lemma firstBlockHom_conj_apply_inr (s : S.ChosenGL r)
    (x : ∀ i : S.ChosenIndex ⊕ S.TwistIndex, GL n (ResField (S.placeAt i))) (i : S.TwistIndex) :
    ((firstBlockHom S u s)⁻¹ * x * firstBlockHom S u s) (inr i) = x (inr i) := by
  rw [Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, firstBlockHom_apply_inr, inv_one, one_mul, mul_one]

/-- Conjugation by an element of the image of `New.firstBlockHom`, that is, by diag(s_w, 1) at the
places w of M (indexed by `S.ChosenIndex`) and 1 at those of Q (indexed by `S.TwistIndex`), maps
the level `New.descentResidueLevel` into itself. -/
lemma firstBlockHom_conj_mem_descentResidueLevel (s : S.ChosenGL r)
    {x : ∀ i : S.ChosenIndex ⊕ S.TwistIndex, GL n (ResField (S.placeAt i))}
    (hx : x ∈ descentResidueLevel S u) :
    (firstBlockHom S u s)⁻¹ * x * firstBlockHom S u s ∈ descentResidueLevel S u := by
  obtain ⟨h_fix, h_parabolic⟩ := (mem_descentResidueLevel_iff S u).1 hx
  refine (mem_descentResidueLevel_iff S u).2 ⟨fun i ↦ ?_, fun i ↦ ?_⟩
  · -- With `d = diag(t, 1)` and `e` the inclusion matrix, `d * e = e * t`, so `x` fixes `d * e`.
    let t : GL r (ResField (S.placeAt (inl i))) := s i
    let d : GL n (ResField (S.placeAt (inl i))) := extendGL u t
    let e : Matrix n r (ResField (S.placeAt (inl i))) := inclMatrix _ u
    have h_block : d.val * e = e * t.val := extendGL_mul_inclMatrix u t
    have h_fix_block : (x (inl i)).val * (d.val * e) = d.val * e := by
      rw [h_block, ← Matrix.mul_assoc, h_fix i]
    have h_apply : ((firstBlockHom S u s)⁻¹ * x * firstBlockHom S u s) (inl i) =
        d⁻¹ * x (inl i) * d := rfl
    rw [h_apply, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, h_fix_block,
      ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  · simpa only [firstBlockHom_conj_apply_inr] using h_parabolic i

end

variable (E r n : Type) [Field E] [CMType E] [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n]
  [WeilData E]

/-! ### Descent pairs and their forms on V -/

/-- A descent pair: places M and Q, a space W of rank r with an index `numbering` on its basis
vectors, an embedding of indices into n > r, column multiplicities k⁺ and k⁻, and a character
μ = `u1Char` whose tame part is trivial off M and Q. -/
structure DescentPair extends LevelPlaces E where
  /-- The signs of the basis vectors of `W` at the infinite places. -/
  signs : r → ℤˣ
  /-- The hermitian space `W` of rank `r` with the given signs, as a `New.Space`. -/
  W : Space E r signs
  /-- The embedding of the index set of the basis of `W` in that of `V = I_n`. -/
  incl : r ↪ n
  /-- An index for each basis vector of `W`; under `New.DescentPair.FitsParams` it numbers the
  vectors within each sign. -/
  numbering : r → ℕ
  /-- k⁺: the number of columns of height `i` of the partition at `τ` for the sign `1`, as a
  function of `τ` and `i`. -/
  colsPlus : InfinitePlace E → ℕ → ℕ
  /-- k⁻: the number of columns of height `i` of the partition at `τ` for the sign `-1`, as a
  function of `τ` and `i`. -/
  colsMinus : InfinitePlace E → ℕ → ℕ
  /-- The character μ of `U(1)(𝔸)`, trivial on rational points. -/
  u1Char : AutChar E
  /-- The weight of `u1Char`, an integer for each infinite place. -/
  weight : InfinitePlace E → ℤ
  /-- The tame part of `u1Char`, a character ψ_w of the residue field for each finite place w. -/
  tamePart : ∀ w : FinPlace E, MulChar (ResField w) ℂ
  /-- The character `u1Char` has weight `weight` and tame part `tamePart`. -/
  hasWeight : u1Char.HasWeight weight tamePart
  /-- The tame part is trivial at every place other than the chosen places of `M` and `Q`. -/
  tame_eq_one : ∀ w : FinPlace E, w ∉ toLevelPlaces.places → tamePart w = 1
  /-- `W` has smaller rank than `V`: `r < n`. -/
  rank_lt : card r < card n

namespace DescentPair

attribute [instance] hasWeight

variable {E r n} (O : DescentPair E r n)

/-- The level of the descent pair: the elements of K₀ whose reductions modulo the places of M fix
the basis vectors indexed by `incl`, and whose reductions modulo the places of Q preserve the span
of the other basis vectors. -/
abbrev levelGroup : Subgroup (Gf E n) := levelOf O.placeAt
  (descentResidueLevel O.toLevelPlaces O.incl)

open scoped Classical in
/-- The block datum Ψ_bl as a function of families X of residue matrices: it is the product over
w ∈ Q of ψ_w(det of the rows of X_w indexed by `incl`) if X_w is the inclusion matrix of `incl` at
every w in M, else 0. -/
def residueBlockDatum (X : ∀ i : O.ChosenIndex ⊕ O.TwistIndex,
  Matrix n r (ResField (O.placeAt i))) : ℂ :=
  if ∀ i : O.ChosenIndex, X (Sum.inl i) = inclMatrix (ResField (O.placeAt (inl i))) O.incl then
    ∏ i : O.TwistIndex, O.tamePart (O.placeAt (inr i)) ((X (Sum.inr i)).submatrix O.incl id).det
  else 0

/-- The column numbers (τ, i) ↦ k⁺(τ, i) + k⁻(τ, n − i) of the highest weight of the forms on
V = I_n, with n the rank of V. -/
abbrev columnCount : InfinitePlace E → ℕ → ℕ := mixedWeight n O.colsPlus O.colsMinus

/-- For an infinite place τ, the integer −∑_{1 ≤ i < n} k⁻(τ, i), the power of the determinant in
the highest weight of the forms on V. -/
abbrev detExp (τ : InfinitePlace E) : ℤ := -((∑ i ∈ Finset.Ico 1 (card n), O.colsMinus τ i :) : ℤ)

/-- The character of `New.descentResidueLevel` sending g to ∏_{w ∈ Q} ψ_w⁻¹(det g_{w,00}). Here
g_{w,00} is the diagonal block of the component of g at w on the basis vectors indexed by `incl`
(block 0 of `New.rangeParabolic`). It is multiplicative because these components are block
triangular. -/
def residueLevelChar : descentResidueLevel O.toLevelPlaces O.incl →* ℂ where
  toFun g := ∏ i : O.TwistIndex,
    O.tamePart⁻¹ (O.placeAt (inr i)) ((g.val (Sum.inr i)).val.submatrix O.incl O.incl).det
  -- `elim_inr` would change the residue field in the type of the matrix, so `simp` leaves it out.
  map_one' := by simp [-elim_inr]
  map_mul' g h := by
    -- On the opposite parabolic the first block of a product is the product of the first blocks.
    obtain ⟨-, h_parabolic⟩ := (mem_descentResidueLevel_iff O.toLevelPlaces O.incl).1 g.prop
    simp [submatrix_mul_of_mem_rangeParabolic _ (h_parabolic _), Finset.prod_mul_distrib, -elim_inr]

omit [WeilData E] in
/-- `O.residueLevelChar g` is the product over the places w = `O.placeAt (inr i)` of Q of
`O.tamePart⁻¹` at w, applied to the determinant of the block of the component of g at w on the basis
vectors indexed by `O.incl`. -/
lemma residueLevelChar_apply (g : descentResidueLevel O.toLevelPlaces O.incl) :
    O.residueLevelChar g = ∏ i : O.TwistIndex,
      O.tamePart⁻¹ (O.placeAt (inr i)) ((g.val (Sum.inr i)).val.submatrix O.incl O.incl).det := rfl

omit [WeilData E] in
/-- The character `New.DescentPair.residueLevelChar` is invariant under conjugation by the image of
`New.firstBlockHom`, as it only reads the components at the places of Q. -/
lemma residueLevelChar_firstBlockHom_conj (s : O.ChosenGL r)
    (x : descentResidueLevel O.toLevelPlaces O.incl) :
    O.residueLevelChar
        ⟨(firstBlockHom O.toLevelPlaces O.incl s)⁻¹ * x * firstBlockHom O.toLevelPlaces O.incl s,
          firstBlockHom_conj_mem_descentResidueLevel O.toLevelPlaces O.incl s x.prop⟩ =
      O.residueLevelChar x := by
  simp only [residueLevelChar_apply, firstBlockHom_conj_apply_inr]

/-- The character of `New.DescentPair.levelGroup` obtained by reduction modulo the places of M and Q
followed by `New.DescentPair.residueLevelChar`. -/
abbrev levelChar : levelOf O.placeAt (descentResidueLevel O.toLevelPlaces O.incl) →* ℂ :=
  O.residueLevelChar.comp (levelOf.reduction O.placeAt (descentResidueLevel O.toLevelPlaces O.incl))

/-- Algebraic forms on V = I_n of weight (`O.columnCount`, `O.detExp`) whose level fixes the basis
vectors indexed by `incl` modulo the places of M and the span of the other basis vectors modulo the
places of Q, with character ∏_Q ψ_w⁻¹(det g₀₀), g₀₀ the diagonal block on `incl`. -/
abbrev FormV : Type := O.LevelForm (descentResidueLevel O.toLevelPlaces O.incl) O.residueLevelChar
  O.columnCount O.detExp

/-- The representation of ∏_{w∈M} GL_r(k_w) on the vectors of π on which
`New.DescentPair.levelGroup` acts by `New.DescentPair.levelChar`. An element g acts by ∏_w ψ_w(det
g_w) times π of a lift of the family equal to diag(g_w, 1) at M and to 1 at Q. -/
def chosenGLRep {W : Type*} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (Gf E n) W) :
    Representation ℂ (O.ChosenGL r)
      (levelSpace π (levelOf O.placeAt (descentResidueLevel O.toLevelPlaces O.incl)) O.levelChar)
        where
  toFun g := (∏ i : O.ChosenIndex, O.tamePart (O.chosenPlace i) (g i).val.det) •
    levelRep π O.residueLevelChar (firstBlockHom O.toLevelPlaces O.incl)
      (fun s x ↦ ⟨firstBlockHom_conj_mem_descentResidueLevel O.toLevelPlaces O.incl s x.prop,
        O.residueLevelChar_firstBlockHom_conj s x⟩) g
  map_one' := by simp
  map_mul' := by simp [← smul_mul_smul, Finset.prod_mul_distrib]

/-- The representation `New.DescentPair.chosenGLRep` on right translation of algebraic forms
(`New.algFormRep`): the action of ∏_M GL_r(k_w) on the forms on V. -/
def formAction : Representation ℂ (O.ChosenGL r) O.FormV :=
  O.chosenGLRep (algFormRep O.columnCount O.detExp)

/-! ### The theta kernel and the normalized descent -/

/-- The linear map from V_{k⁺} ⊗ V_{k⁻}, seen as functions on pairs of indices of Weyl module bases
(`New.WeylIndex`: families of standard fillings over the places), to polynomials, sending a ⊗ b to
the product of the polynomials (`New.letterPoly`) of a in the Fock variables of the basis vectors of
W of sign 1 and of b in those of sign −1. The letter h of a filling stands for the sum of the
variables of the basis vectors of that sign with `O.numbering` equal to h. -/
def tensorPoly : (WeylIndex n O.colsPlus × WeylIndex n O.colsMinus → ℂ) →ₗ[ℂ]
    MvPolynomial (InfinitePlace E × n × r) ℂ :=
  Fintype.linearCombination ℂ fun p : WeylIndex n O.colsPlus × WeylIndex n O.colsMinus ↦
    letterPoly O.signs O.numbering 1 O.colsPlus (Pi.single p.1 1) *
      letterPoly O.signs O.numbering (-1) O.colsMinus (Pi.single p.2 1)

omit [WeilData E] in
/-- The value of `New.DescentPair.tensorPoly` at a pure tensor a ⊗ b, the vector with entry a_i b_j
at (i, j) (that is, `(vecMulVec b a).vec`), is the product of the polynomials (`New.letterPoly`) of
a and b in the variables of the positive, resp. negative, sign. -/
@[simp]
lemma tensorPoly_vecMulVec (a : WeylIndex n O.colsPlus → ℂ) (b : WeylIndex n O.colsMinus → ℂ) :
    O.tensorPoly (vecMulVec b a).vec =
      letterPoly O.signs O.numbering 1 O.colsPlus a * letterPoly O.signs O.numbering (-1)
        O.colsMinus b := by
  -- Both sides are bilinear in `(a, b)`: expand `a` and `b` in the standard bases.
  rw [pi_eq_sum_univ' a, pi_eq_sum_univ' b]
  simp [tensorPoly, linearCombination_apply, sum_prod_type, sum_mul_sum, vecMulVec_apply, mul_smul,
    Pi.single_apply]

/-- The Fock polynomial of a vector: the linear map ξ ↦ P_ξ that applies the integer matrix of
`New.mixedCartan`, a chosen embedding of the module of weight
`mixedWeight n O.colsPlus O.colsMinus` into the tensor product of those of weights k⁺ and k⁻, and
reads the resulting tensor as a polynomial in the Fock variables by `New.DescentPair.tensorPoly`. -/
def fockPoly : (WeylIndex n (mixedWeight n O.colsPlus O.colsMinus) → ℂ) →ₗ[ℂ]
    MvPolynomial (InfinitePlace E × n × r) ℂ :=
  O.tensorPoly ∘ₗ ((mixedCartan n O.colsPlus O.colsMinus).matrix.map (↑)).mulVecLin

/-- The character ν_W of U(1)(𝔸) attached to W: `upsilonU1` raised to the number r₋ of basis
vectors of W with sign −1. It belongs to the standard splitting character υ^{2r₋ − r} of W, with υ
the character of the Weil data. -/
abbrev charW : AutChar E := upsilonU1 ^ Exchange.negCount O.signs

/-- The character ν_V = μ·υ^{⌊n/2⌋} of U(1)(𝔸) attached to V, for μ the character of the descent
pair, υ that of the Weil data and n the rank of V. For even n it belongs to the splitting character
of V that is the base change of μ (`New.Exchange.spaceChar_rankTwist`). -/
abbrev charV : AutChar E := rankTwist O.u1Char n

/-- The theta kernel of the pair (W, I_n) of the descent pair, with the characters
`New.DescentPair.charW` and `New.DescentPair.charV`. -/
abbrev pairThetaKernel : ThetaKernel (𝒮 (O.W.hom (stdSpace E n))) O.W (stdSpace E n) :=
  pairThetaKer O.W (stdSpace E n) O.charW O.charV

/-- The finite datum Ψ_bl ⊗ vac on Hom(W, I_n): the block datum `New.DescentPair.residueBlockDatum`
at the places of M and Q and the vacuum at the other finite places. It is the `New.vacuumDatum`, an
element of the finite part of the space of data, of the function of matrices modulo M²Q that applies
the block datum to their reductions at these places; reading it modulo MQ gives the same vector. -/
def blockDatum : (O.W.hom (stdSpace E n)).finitePart :=
  delta% vacuumDatum O.W (stdSpace E n) (O.levelModulus 2) fun X ↦
    O.residueBlockDatum fun i ↦ X.map (levelResidueAt i)

/-- The datum v_{P_ξ} ⊗ Ψ_bl ⊗ vac in 𝒮(Hom(W, V)): the Fock vector of the polynomial
P_ξ = `New.DescentPair.fockPoly` ξ tensored with the finite datum `New.DescentPair.blockDatum`. -/
@[simp]
abbrev fockDatum (ξ : WeylIndex n (mixedWeight n O.colsPlus O.colsMinus) → ℂ) :
    𝒮 (O.W.hom (stdSpace E n)) :=
  integrated (O.W.hom (stdSpace E n)) (O.fockPoly ξ) O.blockDatum.val

/-- The linear form ξ ↦ conj θ(ω_{ν_W,ν_V}(g, h)(v_{P_ξ̄} ⊗ Ψ_bl ⊗ vac)) for g in U(W)(𝔸) and finite
h in U(V). Here ν_W = `O.charW`, ν_V = `O.charV`, and v_{P_ξ} is the Fock vector of the polynomial
P_ξ. -/
def conjKernel (g : G E O.signs) (h : Gf E n) :
    (WeylIndex n (mixedWeight n O.colsPlus O.colsMinus) → ℂ) →ₗ[ℂ] ℂ :=
  IsLinearMap.mk' (R := ℂ)
    (fun ξ ↦ conj (pairTheta O.W (stdSpace E n) O.charW O.charV (O.fockDatum (star ξ)) (g, 1, h)))
    ⟨fun ξ η ↦ by simp [pairTheta], fun c ξ ↦ by simp [pairTheta]⟩

/-- The normalized descent, a linear map from forms Ξ on V to functions on U(W)(𝔸): θΞ(g) is the
class sum over h, for `New.DescentPair.levelGroup`, of `New.DescentPair.conjKernel` at g and h
applied to Ξ(h). -/
def normalizedDescent : O.FormV →ₗ[ℂ] G E O.signs → ℂ where
  toFun Ξ g := stdClassSum O.levelGroup fun h ↦ O.conjKernel g h (Ξ h)
  -- The double cosets are finite; `↓` turns each `∑ᶠ` into a sum before its summand is rewritten.
  map_add' Ξ Ξ' := funext fun g ↦ by
    simp [apply_eq_evalForm, classSum, ↓ finsum_eq_sum_of_fintype, Finset.sum_add_distrib]
  map_smul' c Ξ := funext fun g ↦ by
    simp [apply_eq_evalForm, classSum, ↓ finsum_eq_sum_of_fintype, Finset.mul_sum]

/-! ### Hecke polynomials -/

/-- For split w with w, w̄ off M and Q, the operator H_w(X) = ∑_{i≤n} (−X)^i q^{i(i−1)/2} T_{w,i} on
the forms on V, with q the norm of w. -/
def heckePolyOnForms {w : FinPlace E} (hw : star w ≠ w) (hS : w ∉ O.places.conjClosure) (X : ℂ) :
    Module.End ℂ O.FormV :=
  (heckePolyOp (algFormRep O.columnCount O.detExp) hw X).restrict fun y hy ↦ by
    -- `y` is spherical at `w`, so each `T_{w,j}` keeps its level and character.
    have h_sph : y ∈ sphericalAt (algFormRep O.columnCount O.detExp) w :=
      LevelPlaces.LevelForm.mem_sphericalAt ⟨y, hy⟩ hS
    simp [heckePolyOp, heckePolyEval, sum_mem, Submodule.smul_mem,
      heckeSplit_mem_levelSpace hw _ h_sph levelOf_le_stdLevel hy]

omit [WeilData E] in
/-- Let w be split with w, w̄ off M and Q. If a form y on V, viewed as a function on the finite
points, is spherical at w and the Hecke polynomial at each T acts on it by p(T)
(`New.HasHeckePolynomial`), then `New.DescentPair.heckePolyOnForms` at X sends y to p(X) • y. -/
lemma heckePolyOnForms_eq_smul {w : FinPlace E} (hw : star w ≠ w)
    (hS : w ∉ O.places.conjClosure) {y : O.FormV} {p : ℂ → ℂ}
    (hy : HasHeckePolynomial (rightRegular ℂ (Gf E n) (WeylIndex n O.columnCount → ℂ)) hw p
      y.val.val) (X : ℂ) :
    O.heckePolyOnForms hw hS X y = p X • y := by
  obtain ⟨-, h_eigen⟩ := hy
  -- The inclusion of algebraic forms commutes with the Hecke operators.
  have h_incl : (heckePolyOp (algFormRep O.columnCount O.detExp) hw X y.val).val =
      heckePolyOp (rightRegular ℂ (Gf E n) (WeylIndex n O.columnCount → ℂ)) hw X y.val.val :=
    map_heckePolyOp (Submodule.subtype _) X fun _ _ ↦ rfl
  exact Subtype.ext (Subtype.ext (h_incl.trans (h_eigen X)))

/-- The difference of ranks t = n − r = dim V − dim W of the descent pair. -/
abbrev rankDiff (_ : DescentPair E r n) : ℕ := card n - card r

/-- The complex number q^{1−n+r/2} υ(ϖ_w)^{r−2r₋}, with υ the character of the Weil data, q the
norm of w, ϖ_w the chosen uniformiser and r₋ the number of minus signs of W. -/
def liftHeckeRoot (w : FinPlace E) : ℂ := (O.charW.frobValue r w * w.q ^ (O.rankDiff - 1))⁻¹

/-- At each split w with w, w̄ off M and Q, y is spherical with Hecke polynomial
∏_{l<n−r} (1 − q^l νT) · H_{z(w)}(q^{n−r} νT/ν'). Here q is the norm of w, H_{z(w)} is the rank r
polynomial `New.heckePolyEval` with eigenvalues z(w), and ν, ν' are the `New.AutChar.frobValue` of
the characters `O.charW`, `O.charV` in ranks r, n. -/
def HasLiftHeckePolynomial (y : O.FormV) (z : FinPlace E → ℕ → ℂ) : Prop :=
  ∀ (w : FinPlace E) (hw : star w ≠ w), w ∉ O.places.conjClosure →
    HasHeckePolynomial (rightRegular ℂ (Gf E n) (WeylIndex n O.columnCount → ℂ)) hw
      (fun T : ℂ ↦ SiegelWeil.qPochhammer w.q O.rankDiff (O.charW.frobValue r w * T) *
        heckePolyEval r w (z w) (w.q ^ O.rankDiff * O.charW.frobValue r w / O.charV.frobValue n w *
          T))
      y.val.val

end DescentPair

end DescentPair

/-!
## The block datum as a sum of translates, and the action of the level on it

In this section `n` indexes the basis of `W` and `n'` that of `V`.

* `New.DescentPair.identityBlockIndicator`: the function Ψ¹, which is Ψ_bl with the character of the
  determinant at each place of `Q` replaced by the indicator of the identity block.
-/

section AuxDatumLaw

open Matrix LevelPlaces MulChar Finset Rows stdLevel

variable {E n n' : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] (S : LevelPlaces E) (O : DescentPair E n n')

/-- The product of the groups GL_n(k_w) over the places w of Q, where k_w is the residue field at
w. -/
abbrev LevelPlaces.TwistGL (n : Type*) [Fintype n] [DecidableEq n] : Type _ :=
  ∀ i : S.TwistIndex, GL n (ResField (S.placeAt (Sum.inr i)))

/-- The group ∏_{w ∈ Q} GL_n(k_w) is finite. -/
instance : Fintype (S.TwistGL n) := .ofFinite _

/-- For A in the product of GL_n(k_w) over Q, the family of residue matrices that is 1 at the places
of M and the inverse of the component of A at each place of Q. -/
def LevelPlaces.twistResidue (A : TwistGL S n) :
    ∀ i : S.ChosenIndex ⊕ S.TwistIndex, GL n (ResField (S.placeAt i))
  | .inl _ => 1
  | .inr i => (A i)⁻¹

/-- The family `twistResidue A` is 1 at the places of M. -/
lemma LevelPlaces.twistResidue_inl (A : TwistGL S n) (i : S.ChosenIndex) :
    S.twistResidue A (.inl i) = 1 := rfl

/-- For an index `i : S.TwistIndex` of a place of the twist, the family `S.twistResidue A` at
`.inr i` is `(A i)⁻¹`, the inverse of the component of `A` at that place. -/
lemma LevelPlaces.twistResidue_inr (A : TwistGL S n) (i : S.TwistIndex) :
    S.twistResidue A (.inr i) = (A i)⁻¹ := rfl

/-- For A in the product of GL_n(k_w) over Q, a chosen element of K₀ reducing to A⁻¹ at the
places in Q and to 1 at those in M. -/
def LevelPlaces.twistResidueLift (A : TwistGL S n) : stdLevel E n := liftResidue (S.twistResidue A)

/-- The lift `twistResidueLift A` reduces to the family `twistResidue A`. -/
lemma LevelPlaces.reduceFamily_twistResidueLift (A : TwistGL S n) :
    reduceFamily S.placeAt (S.twistResidueLift A) = S.twistResidue A :=
  reduceFamily_liftResidue (S.twistResidue A)

/-- The lift `twistResidueLift A` reduces to 1 at each chosen place `S.placeAt (.inl i)`. -/
lemma LevelPlaces.reduceAt_twistResidueLift_inl (A : TwistGL S n) (i : S.ChosenIndex) :
    stdLevel.reduceAt (S.placeAt (.inl i)) (S.twistResidueLift A) = 1 :=
  (congrFun (S.reduceFamily_twistResidueLift A) (.inl i)).trans (S.twistResidue_inl A i)

/-- The lift `twistResidueLift A` reduces to `(A i)⁻¹` at each place of the twist
`S.placeAt (.inr i)`. -/
lemma LevelPlaces.reduceAt_twistResidueLift_inr (A : TwistGL S n) (i : S.TwistIndex) :
    stdLevel.reduceAt (S.placeAt (.inr i)) (S.twistResidueLift A) = (A i)⁻¹ :=
  (congrFun (S.reduceFamily_twistResidueLift A) (.inr i)).trans (S.twistResidue_inr A i)

variable [WeilData E]

open scoped Classical in
/-- The indicator Ψ¹ of the matrices `y` modulo `M Q` that reduce to the inclusion matrix of the
embedding of indices of the pair at the places of `M` and whose rows indexed by that embedding
reduce to the identity at the places of `Q`. -/
def DescentPair.identityBlockIndicator (y : Matrix n' n (O.levelModulus 1).ResidueRing) : ℂ :=
  let X (i : O.ChosenIndex ⊕ O.TwistIndex) :=
    Matrix.map y (levelResidueAt (S := O.toLevelPlaces) (c := 1) i)
  if (∀ i : O.ChosenIndex,
      X (Sum.inl i) = inclMatrix (ResField ((O.chosenPlace ⊕ᵥ O.twistPlace) (Sum.inl i))) O.incl) ∧
    ∀ i : O.TwistIndex, (X (Sum.inr i)).submatrix O.incl id = 1 then 1 else 0

omit [DecidableEq n'] in
/-- For `k` in `stdLevel E n` (integral finite points of U(W)), `O.charV` of `detFin O.signs k` is
the product over the places `O.placeAt i` of M and Q of `O.tamePart` at that place, applied to the
determinant of `stdLevel.reduceAt` of `k` there (k mod w). -/
lemma DescentPair.charV_detFin_eq_prod (k : stdLevel E n) :
    O.charV.val (detFin O.signs k.val) = ∏ i : O.ChosenIndex ⊕ O.TwistIndex,
      O.tamePart (O.placeAt i) (stdLevel.reduceAt (O.placeAt i) k).val.det :=
  O.hasWeight.hasWeight_rankTwist.apply_det_eq_prod O.apart.injective O.tame_eq_one k

omit [WeilData E] in
open scoped Classical in
/-- Here M and Q are the families of places indexed by `O.ChosenIndex` and `O.TwistIndex`, ψ_w is
`O.tamePart w`, and Ψ_bl = `New.DescentPair.residueBlockDatum`. The value of Ψ_bl at a family `X` of
residue matrices is a sum over the families `A` of invertible matrices at `Q`. The term of `A` is
`∏ ψ_w (det A_w)` if `X` is the inclusion matrix at `M` and `A` consists of the rows of `X` indexed
by `O.incl`, and `0` if not. -/
lemma DescentPair.residueBlockDatum_eq_sum
    (X : ∀ i : O.ChosenIndex ⊕ O.TwistIndex, Matrix n' n (ResField (O.placeAt i))) :
    O.residueBlockDatum X = ∑ A : O.TwistGL n,
      if (∀ i : O.ChosenIndex, X (.inl i) = inclMatrix (ResField (O.placeAt (.inl i))) O.incl) ∧
          ∀ i : O.TwistIndex, (X (.inr i)).submatrix O.incl id = (A i).val then
        ∏ i : O.TwistIndex, O.tamePart (O.placeAt (.inr i)) (A i).val.det
      else 0 := by
  rw [residueBlockDatum]
  by_cases h_blocks : ∀ i : O.TwistIndex, IsUnit ((X (.inr i)).submatrix O.incl id)
  · -- All blocks are invertible: only the family `A` of these blocks contributes.
    choose A hA using h_blocks
    simp only [← hA, Units.val_inj, ← funext_iff, ite_and, sum_ite_irrel, sum_ite_eq, mem_univ,
      ite_true, sum_const_zero]
  · -- Some block is singular: no `A` matches it, and `ψ` kills its determinant.
    obtain ⟨i, hi⟩ := not_forall.1 h_blocks
    have h_zero : O.tamePart (O.placeAt (.inr i)) ((X (.inr i)).submatrix O.incl id).det = 0 :=
      map_nonunit _ (mt (isUnit_iff_isUnit_det _).2 hi)
    rw [prod_eq_zero (mem_univ i) h_zero, ite_self, sum_eq_zero]
    exact fun A _ ↦ ite_eq_right fun ⟨_, hA⟩ ↦ hi (by simpa only [hA i] using (A i).isUnit)

/-- The finite datum Ψ_bl ⊗ vac of a descent pair (W, V) is the sum, over A in ∏_{w ∈ Q} GL_n(k_w)
(Q indexed by `O.TwistIndex`, n the rank of W), of the datum Ψ¹ ⊗ vac, moved by the element
`New.LevelPlaces.twistResidueLift` A of U(W), a lift of A⁻¹. Here Ψ¹ =
`New.DescentPair.identityBlockIndicator` is the indicator of the matrices modulo MQ that reduce to
the inclusion matrix of `O.incl` at M and whose rows indexed by `O.incl` reduce to 1 at Q, and vac
is the vacuum at the other finite places. -/
lemma DescentPair.blockDatum_eq_sum_modDatum :
    O.blockDatum.val = ∑ A : O.TwistGL n,
      O.pairThetaKernel.ω ((1, (O.twistResidueLift A).val), 1)
        (modDatum O.W (stdSpace E n') (O.levelModulus 1) O.identityBlockIndicator
          Fock.vacVector) := by
  classical
  -- Write both sides as lifts of functions of residue matrices, move the datum of
  -- `identityBlockIndicator` by `pairWeil_modDatum_stdLevel`, and compare the naming functions at a
  -- matrix `x`.
  have h_one : (1 : G E (1 : n' → ℤˣ)) = (1, (1 : stdLevel E n').val) := rfl
  simp_rw [h_one, blockDatum, liftFn_eq_residueDatum places_levelModulus,
    ← liftFn_eq_residueDatum (places_levelModulus (c := 1)), pairWeil_modDatum_stdLevel,
    modDatum_vacVector, places_levelModulus, ← _root_.smul_apply, ← _root_.sum_apply, ← map_smul,
    ← map_sum]
  congr 3 with x
  rw [Function.comp_apply, O.residueBlockDatum_eq_sum, Finset.sum_apply]
  refine sum_congr rfl fun A _ ↦ ?_
  -- As `twistResidueLift A` reduces to `1` at `M` and to `A⁻¹` at `Q`, the conditions on `x` agree,
  -- and the scalar `(O.charV (det (twistResidueLift A)))⁻¹` is `∏ ψ (det (A i))`. The lemmas
  -- `Sum.elim_inl` and `Sum.elim_inr` are removed: they would rewrite the places on which the
  -- residue fields depend.
  simp [charV_detFin_eq_prod, identityBlockIndicator, submatrix_mul (e₂ := id),
    reduceAt_twistResidueLift_inl,
    reduceAt_twistResidueLift_inr, mul_inv_eq_iff_eq_mul_of_invertible, ← inv_apply',
      inv_apply_eq_inv',
    -Sum.elim_inl, -Sum.elim_inr]

omit [WeilData E] in
/-- Here M and Q are the families of places indexed by `O.ChosenIndex` and `O.TwistIndex`, and ψ_w
is `O.tamePart w`. Let `k`, `k'` be families of invertible residue matrices of ranks `n`, `n'` and
`j` an element of `New.descentResidueLevel`, such that `k' = diag(k, 1) j` at `M` and `k' = j` at
`Q`. Replacing `X` by `k'⁻¹ X k` multiplies `New.DescentPair.residueBlockDatum` by
`New.DescentPair.residueLevelChar j`, the product over `Q` of ψ_w⁻¹ of the corner determinant of
`j`, times `∏ ψ_w (det k_w)` over `Q`. -/
lemma DescentPair.residueBlockDatum_inv_mul_mul
    {k : ∀ i : O.ChosenIndex ⊕ O.TwistIndex, GL n (ResField (O.placeAt i))}
    {k' : ∀ i : O.ChosenIndex ⊕ O.TwistIndex, GL n' (ResField (O.placeAt i))}
    {j : descentResidueLevel O.toLevelPlaces O.incl}
    (h_chosen : ∀ i : O.ChosenIndex, k' (.inl i) = extendGL O.incl (k (.inl i)) * j.val (.inl i))
    (h_twist : ∀ i : O.TwistIndex, k' (.inr i) = j.val (.inr i))
    (X : ∀ i : O.ChosenIndex ⊕ O.TwistIndex, Matrix n' n (ResField (O.placeAt i))) :
    O.residueBlockDatum (fun i : O.ChosenIndex ⊕ O.TwistIndex ↦ (k' i)⁻¹.val * X i * (k i).val) =
      O.residueLevelChar j * (∏ i : O.TwistIndex,
        O.tamePart (O.placeAt (.inr i)) (k (.inr i)).val.det) *
        O.residueBlockDatum X := by
  classical
  obtain ⟨h_fix, h_parabolic⟩ := (mem_descentResidueLevel_iff O.toLevelPlaces O.incl).1 j.prop
  -- The supports agree: at `M`, `j` fixes the inclusion matrix, and
  -- `diag(k, 1) * inclMatrix = inclMatrix * k`.
  have h_support (i : O.ChosenIndex) :
      (k' (.inl i))⁻¹.val * X (.inl i) * (k (.inl i)).val = inclMatrix _ O.incl ↔
        X (.inl i) = inclMatrix _ O.incl := by
    simp [h_chosen, h_fix, Matrix.mul_assoc, inv_mul_eq_iff_eq_mul_of_invertible,
      Matrix.mul_left_inj_of_invertible, -Sum.elim_inl]
  -- At `Q` the rows `O.incl` of `j⁻¹ X k` are the corner of `j⁻¹` times those of `X` times `k`.
  have h_block (i : O.TwistIndex) :
      ((k' (.inr i))⁻¹.val * X (.inr i) * (k (.inr i)).val).submatrix O.incl id =
        (j.val (.inr i))⁻¹.val.submatrix O.incl O.incl * (X (.inr i)).submatrix O.incl id *
          (k (.inr i)).val := by
    rw [submatrix_mul (e₂ := id) _ _ _ _ Function.bijective_id, submatrix_id_id, h_twist,
      submatrix_mul_of_mem_rangeParabolic _ (inv_mem (h_parabolic i))]
  have h_char : O.residueLevelChar j = ∏ i : O.TwistIndex,
      O.tamePart (O.placeAt (.inr i)) ((j.val (.inr i))⁻¹.val.submatrix O.incl O.incl).det := by
    rw [← inv_inv j, map_inv, inv_inv]
    simp [residueLevelChar, inv_apply_eq_inv', -Sum.elim_inr]
  rw [residueBlockDatum, residueBlockDatum, mul_ite, mul_zero]
  refine if_congr (forall_congr' h_support) ?_ rfl
  simp only [h_block, h_char, det_mul, map_mul, prod_mul_distrib]
  ring

/-- Here M and Q are the places `O.chosenPlace` and those indexed by `O.TwistIndex`, and ψ_w is
`O.tamePart w`. Let `k`, `k'` lie in `stdLevel`. Suppose the reduction `reduceFamily O.placeAt k'`
is `firstBlockHom` of `reduceFamily O.chosenPlace k` times `j.val`. The element `j` lies in
`New.descentResidueLevel`, so it fixes the basis vectors indexed by `O.incl` at `M` and preserves
the span of the others at `Q`. Then the Weil action `O.pairThetaKernel.ω (k, k')` multiplies
Ψ_bl ⊗ vac = `O.blockDatum` by (∏ over `M` of ψ_w (det (k mod w)))⁻¹ times
`New.DescentPair.residueLevelChar j`. -/
lemma DescentPair.omega_blockDatum_eq_smul (k : stdLevel E n) (k' : stdLevel E n')
    (j : descentResidueLevel O.toLevelPlaces O.incl)
    (h_reduction : reduceFamily O.placeAt k' =
      firstBlockHom O.toLevelPlaces O.incl (reduceFamily O.chosenPlace k) * j.val) :
    O.pairThetaKernel.ω (k, k') O.blockDatum.val =
      ((∏ i : O.ChosenIndex, O.tamePart (O.chosenPlace i)
        (reduceFamily O.chosenPlace k i).val.det)⁻¹ *
        O.residueLevelChar j) • O.blockDatum := by
  -- The reductions of `k'` at the places of `M` and of `Q`.
  have h_chosen (i : O.ChosenIndex) : reduceFamily O.placeAt k' (.inl i) =
      extendGL O.incl (reduceFamily O.placeAt k (.inl i)) * j.val (.inl i) :=
    congrFun h_reduction (.inl i)
  have h_twist (i : O.TwistIndex) : reduceFamily O.placeAt k' (.inr i) = j.val (.inr i) :=
    (congrFun h_reduction (.inr i)).trans (one_mul _)
  have h_reduce (x : Matrix n' n (O.levelModulus 2).ResidueRing)
    (i : O.ChosenIndex ⊕ O.TwistIndex) :
      (((O.levelModulus 2).reductionGL k')⁻¹.val * x *
          ((O.levelModulus 2).reductionGL k).val).map (levelResidueAt i) =
        (reduceFamily O.placeAt k' i)⁻¹.val * x.map (levelResidueAt i) *
          (reduceFamily O.placeAt k i).val := by
    simp only [← map_inv, Matrix.map_mul, reductionGL_map_modulusResidue]
    rfl
  -- The factors `tamePart (det k)⁻¹` at `Q` in the scalar of `pairWeil_modDatum_stdLevel` cancel
  -- those of `residueBlockDatum_inv_mul_mul`; the character `O.charW ∘ det` is trivial on integral
  -- points.
  have h_scalar : (O.charW.val (detFin 1 k'.val) * (O.charV.val (detFin O.signs k.val))⁻¹).val *
        ∏ i : O.TwistIndex, O.tamePart (O.placeAt (.inr i))
          (reduceFamily O.placeAt k (.inr i)).val.det =
      (∏ i : O.ChosenIndex, O.tamePart (O.chosenPlace i)
        (reduceFamily O.chosenPlace k i).val.det)⁻¹ := by
    rw [mul_comm]
    simp [charV_detFin_eq_prod, reduceFamily, prod_eq_zero_iff, apply_eq_zero_iff,
      GeneralLinearGroup.det_ne_zero, -Sum.elim_inl, -Sum.elim_inr]
    rfl
  -- Move the datum by `pairWeil_modDatum_stdLevel` and compare the naming functions at a matrix
  -- `x`.
  simp_rw [blockDatum, ← modDatum_vacVector, pairWeil_modDatum_stdLevel, modDatum_vacVector,
    ← _root_.smul_apply, ← map_smul]
  congr 3 with x
  simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, h_reduce,
    O.residueBlockDatum_inv_mul_mul h_chosen h_twist, ← h_scalar]
  ring

end AuxDatumLaw

end New

/-!
## The real datum and the normalized descent

This section starts from the real data of a descent pair `O : New.DescentPair` (a space `W` of rank
`r` with signs `O.signs`, and `V = I_n` definite of larger rank), whose Fock polynomials are
`New.DescentPair.fockPoly`.

Throughout, r₋ = `card {c // O.signs c = -1}` is the number of minus signs of `W`, k⁺ and k⁻ are
`O.colsPlus` and `O.colsMinus`, and P_ξ is `O.fockPoly ξ`.
-/

namespace New.DescentPair

open Matrix Finset Fintype Fock Space «GL» MvPolynomial Exchange
open NumberField (InfinitePlace)

variable {E r n : Type} [Field E] [CMType E] [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n]

/-- The doubled parameter on `V`: at the place `w`, the entry at `i` is the entry of
`New.hcParameter` of the weight `(O.columnCount, O.detExp)` in rank `card n` at the position of `i`
in the numbering of `n`. -/
noncomputable def paramV (O : DescentPair E r n) (w : InfinitePlace E) (i : n) : ℤ :=
  hcParameter O.columnCount O.detExp (Fintype.card n) w (Fintype.equivFin n i)

omit [DecidableEq n] in
/-- `O.paramV` is twice the Harish-Chandra parameter of the weight `(O.columnCount, O.detExp)` of
forms on `V`, in the sense of `New.IsHCParam`. -/
lemma isHCParam_paramV (O : DescentPair E r n) : IsHCParam O.columnCount O.detExp O.paramV :=
  isHCParam_hcParameter n O.columnCount O.detExp

/-- The doubled parameter l on W fits the descent pair O: it corresponds to l' = `O.paramV` on V
(`New.ParamsCorrespond`: at each infinite place the two satisfy the block rule `New.IsBlockRule` for
the weights), the numbering `O.numbering` lists the basis vectors of sign ±1 by decreasing ±l, and
k^± have no column higher than the number r_± of signs ±1. -/
structure FitsParams (O : DescentPair E r n) (l : InfinitePlace E → r → ℤ) where
  /-- The parameters `l` on `W` and `O.paramV` on `V` correspond, for the weights r₋ (the number of
  minus signs of `W`) and ⌊n/2⌋ plus `O.weight`, the weight of `O.u1Char`. -/
  paramsCorrespond :
      ParamsCorrespond (fun _ ↦ negCount O.signs) ((Fintype.card n / 2 : ℕ) + O.weight ·) l O.paramV
        O.signs 1
  /-- At every place the basis vectors `c` of each sign are numbered from `0` by decreasing
  `O.signs c * l w c`. -/
  numbering_eq (w : InfinitePlace E) (c : r) :
      O.numbering c = #{c' : r | O.signs c' = O.signs c ∧ O.signs c * l w c < O.signs c * l w c'}
  /-- `O.colsPlus τ i` vanishes when `i` exceeds the number r₊ of plus signs of `W`. -/
  colsPlus_eq_zero (τ : InfinitePlace E) (i : ℕ) :
      Fintype.card {c // O.signs c = 1} < i → O.colsPlus τ i = 0
  /-- `O.colsMinus τ i` vanishes when `i` exceeds the number r₋ of minus signs of `W`. -/
  colsMinus_eq_zero (τ : InfinitePlace E) (i : ℕ) : negCount O.signs < i → O.colsMinus τ i = 0

/-! ### The action of the real points of `U(V)` -/

/-- The substitution of Fock variables by which y in the compact group U(n)(ℝ) acts on the rows: the
variable (τ, i, a) goes to ∑_j (y_τ)_{j i} X(τ, j, a) if the column a has sign s(a) = 1, and to
∑_j (y_τ⁻¹)_{i j} X(τ, j, a) otherwise. -/
noncomputable def _root_.New.fockRowSubst (s : r → ℤˣ) (y : GInf E (1 : n → ℤˣ)) :
    MvPolynomial (InfinitePlace E × n × r) ℂ →ₐ[ℂ] MvPolynomial (InfinitePlace E × n × r) ℂ :=
  aeval fun ((τ, i, a) : InfinitePlace E × n × r) ↦
    if s a = 1 then ∑ j : n, (y τ).val.val j i • X (τ, j, a)
    else ∑ j : n, (y τ)⁻¹.val.val i j • X (τ, j, a)

/-- Let the pair be U(diag s) and the compact group U(n)(ℝ), so that the Fock variables have the
signs s (`New.realSigns` of `New.homSigns s 1`). In its real Weil representation `New.realPairWeil`
with first weight the number of negative signs of s and any second weight γ', (1, y) acts on the
Fock vector of a polynomial P by the substitution `New.fockRowSubst s y`. -/
lemma _root_.New.realPairWeil_one_polyVector (s : r → ℤˣ) (γ' : InfinitePlace E → ℤ)
    (y : GInf E (1 : n → ℤˣ)) (P : MvPolynomial (InfinitePlace E × n × r) ℂ) :
    realPairWeil (fun _ ↦ negCount s) γ' (1, y) (polyVector (realSigns E (homSigns s 1)) P) =
      polyVector (realSigns E (homSigns s 1)) (fockRowSubst s y P) := by
  -- The first weight makes the scalar of `realPairWeil_polyVector` trivial.
  simp [realPairWeil_polyVector, fockRowSubst, negCount, eq_comm (a := (1 : ℤˣ)),
    DiscreteSeries.principalMinor_of_forall_not, Matrix.one_apply]

omit [DecidableEq r] [CMType E] in
/-- Let F be a polynomial in an array of variables with rows (τ, i) and columns h ∈ ℕ. Then
`New.fockLetters s ord c F` replaces the variable (τ, i, h) by the sum of the X(τ, i, a) with
s a = c and ord a = h. On it the substitution `New.fockRowSubst s y` is the substitution
(`New.rowSubst`) of yᵀ in the variables of F if c = 1, and of y⁻¹ otherwise. -/
lemma _root_.New.fockRowSubst_fockLetters (s : r → ℤˣ) (ord : r → ℕ) (y : GInf E (1 : n → ℤˣ))
    (c : ℤˣ) (F : MatrixPoly ((_ : InfinitePlace E) × n) ℂ) :
    fockRowSubst s y (fockLetters s ord c F) =
      fockLetters s ord c
        (rowSubst (fun τ : InfinitePlace E ↦ if c = 1 then (y τ).val.valᵀ else (y τ)⁻¹.val.val)
          F) := by
  -- Both sides are algebra maps in `F`. Compare the images of a variable after exchanging the sum
  -- over the columns `a` of sign `c` with the sum over the rows.
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  refine AlgHom.congr_fun (algHom_ext fun x ↦ ?_) F
  simp only [AlgHom.comp_apply, fockLetters, rowSubst, fockRowSubst, aeval_X, map_sum, map_smul,
    smul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun a ha ↦ ?_
  obtain ⟨rfl, -⟩ : s a = c ∧ ord a = x.2 := (mem_filter.1 ha).2
  split_ifs <;> rfl

/-- If the first weight is the number of negative signs of s, then (1, y), y in the compact group
U(n)(ℝ), acts on the Fock vector of `New.fockLetters s ord c F` by substituting yᵀ in the variables
of F if c = 1, and y⁻¹ otherwise. -/
lemma _root_.New.realPairWeil_fockLetters [WeilData E]
    (s : r → ℤˣ) (ord : r → ℕ) (γ' : InfinitePlace E → ℤ)
    (y : GInf E 1) (c : ℤˣ) (F : MatrixPoly ((_ : InfinitePlace E) × n) ℂ) :
    realPairWeil (n' := n) (s := s) (fun _ ↦ negCount s) γ' (1, y) (fockLetters s ord c F) =
      fockLetters s ord c
        (rowSubst (fun τ : InfinitePlace E ↦ if c = 1 then (y τ).val.valᵀ else (y τ)⁻¹.val.val)
          F) := by
  rw [realPairWeil_one_polyVector, fockRowSubst_fockLetters]

open scoped Kronecker in
/-- Let O be a descent pair with signs `O.signs` and column numbers k⁺ = `O.colsPlus` and
k⁻ = `O.colsMinus`. Let y lie in `GInf E 1`, the compact group U(n)(ℝ). Let v be a tensor in
V_{k⁺} ⊗ V_{k⁻}, given by its coordinates at pairs of indices of the Weyl module bases
(`New.WeylIndex`). The substitution `New.fockRowSubst O.signs y` sends the Fock polynomial
`O.tensorPoly v` of v to the polynomial of (S_{k⁺}(y) ⊗ S_{k⁻}(y⁻ᵀ)) v. Here S_k is the Schur matrix
`New.schur k`, the action on the Weyl module V_k. -/
lemma fockRowSubst_tensorPoly (O : DescentPair E r n) (y : GInf E (1 : n → ℤˣ))
    (v : WeylIndex n O.colsPlus × WeylIndex n O.colsMinus → ℂ) :
    fockRowSubst O.signs y (O.tensorPoly v) =
      O.tensorPoly (schur O.colsPlus (fun τ : InfinitePlace E ↦ (y τ).val.val) ⊗ₖ
        schur O.colsMinus (fun τ : InfinitePlace E ↦ (y τ)⁻¹.val.valᵀ) *ᵥ v) := by
  -- Both sides are linear in `v`; on a basis tensor `O.tensorPoly` is a product of two
  -- polynomials, one in the letters of each sign.
  rw [pi_eq_sum_univ' v]
  simp [fockRowSubst_fockLetters, mulVec_sum, sum_prod_type, ← vec_single,
    single_eq_single_vecMulVec_single, letterPoly, -mulVec_single, mulVec_smul,
    kronecker_mulVec_vec, mul_vecMulVec, vecMulVec_mul, vecMul_transpose]

/-- In the real Weil representation `realPairWeil` of the descent pair `O`, with weight
`negCount O.signs` at every place and any weight `γ'`, a real point `y` of U(V) sends the Fock
vector of the polynomial `O.fockPoly (star ξ)` to that of `O.fockPoly (star (ρ(y)ξ))`. Here
ρ = `New.conjWeylRep` is the action through the conjugate matrices, by which algebraic forms
transform, so that conj(ρ(y)ξ) is the image of conj(ξ) under y. -/
lemma realPairWeil_fockPoly (O : DescentPair E r n) {γ' : InfinitePlace E → ℤ} (y : GInf E 1)
    (ξ : WeylIndex n O.columnCount → ℂ) :
    realPairWeil (s := O.signs) (s' := 1) (fun _ ↦ negCount O.signs) γ' (1, y)
        (O.fockPoly (star ξ)) =
      O.fockPoly (star (conjWeylRep O.columnCount O.detExp y ξ)) := by
  have h_conj : star (conjWeylRep O.columnCount O.detExp y ξ) =
      weylRep O.columnCount O.detExp (fun τ ↦ (y τ).val) *ᵥ star ξ := by
    change star (weylRep _ _ (fun τ ↦ GeneralLinearGroup.map (starRingEnd ℂ) (y τ).val) *ᵥ ξ) = _
    simp [star_mulVec, weylRep_map, ← mulVec_transpose, conjTranspose_transpose, Function.comp_def]
  -- `MixedCartanEmbedding.intertwines` turns the action on `ξ` into a Kronecker product of two
  -- Schur matrices.
  rw [realPairWeil_one_polyVector, h_conj]
  simp only [fockPoly, LinearMap.comp_apply, mulVecLin_apply, fockRowSubst_tensorPoly,
    MixedCartanEmbedding.intertwines]
  rfl

/-! ### Joint harmonics and the edge -/

/-- The product of minors at the infinite place w. Order the rows by decreasing η·l', with
l' = `O.paramV w`, and the columns of sign η by `O.numbering`. It is the product over η = ±1 and
p < n of the minor (the determinant of `New.staircaseBlock`) on the first p rows and columns for η,
raised to the power k⁺(w, p) = `O.colsPlus w p` for η = 1 and k⁻(w, p) = `O.colsMinus w p` for
η = −1. -/
noncomputable def productOfMinors (O : DescentPair E r n) (w : InfinitePlace E) :
    MvPolynomial (n × r) ℂ :=
  ∏ η : ℤˣ, ∏ p : Fin (Fintype.card n),
    (staircaseBlock O.signs O.numbering (O.paramV w) η p).det ^
      (if η = 1 then O.colsPlus w else O.colsMinus w) p

omit [DecidableEq n] in
/-- For each place `w` and index `a`, the position `decreasingPosition` of `a` in `O.paramV w` (the
number of entries larger than the one at `a`) is `Fintype.equivFin n a`. Its position in
`-O.paramV w` is the reversed index `(Fintype.equivFin n a).rev`. -/
lemma decreasingPosition_paramV (O : DescentPair E r n) (w : InfinitePlace E) (a : n) :
    decreasingPosition (O.paramV w) a = Fintype.equivFin n a ∧
      decreasingPosition (-O.paramV w) a = (Fintype.equivFin n a).rev := by
  obtain ⟨f, hf⟩ : ∃ f : n ≃ Fin (Fintype.card n), ∀ a : n,
      decreasingPosition (O.paramV w) a = f a ∧ decreasingPosition (-O.paramV w) a = (f a).rev :=
    exists_equiv_decreasingPosition (O.isHCParam_paramV w).1
  -- `hcParameter` is strictly decreasing and takes the value `O.paramV w a` at both numbers.
  have h_eq : (Fintype.equivFin n a : ℕ) = decreasingPosition (O.paramV w) a :=
    hcParameter_strictAnti.injective (O.isHCParam_paramV.eq_hcParameter w a)
  simp [Fin.val_rev, h_eq, hf a]

/-- The Fock polynomial `O.fockPoly` of `highestVector O.columnCount O.paramV` (the highest vector
of weight `O.columnCount` for the parameter `O.paramV`) is the product over the infinite places w of
the products of minors `O.productOfMinors w`, each in the variables of w. -/
lemma fockPoly_highestVector (O : DescentPair E r n) :
    O.fockPoly (highestVector O.columnCount O.paramV) =
      ∏ w : InfinitePlace E, (O.productOfMinors w).rename (w, ·) := by
  -- An evaluation vector gives a product of powers of minors.
  have h_minors (η : ℤˣ) (k : InfinitePlace E → ℕ → ℕ) (pos : n → ℕ) :
      letterPoly O.signs O.numbering η k (weylEval (fun _ ↦ n) k (permArray fun _ (a : n) ↦ pos a))
        =
        ∏ w : InfinitePlace E, ∏ p : Fin (Fintype.card n),
          rename (w, ·) (of fun i j : Fin p ↦ ∑ a : n, ∑ c : r,
            if pos a = i ∧ O.signs c = η ∧ O.numbering c = j.val then X (a, c) else 0).det ^ k w
              p := by
    simp [letterPoly, weylKernel, highestPoly, permArray, Matrix.map, tableauPoly, minor,
      AlgHom.map_det, rowSubst, ite_and, fockLetters, apply_ite, sum_filter]
  -- `MixedCartanEmbedding.top` sends the highest vector to a tensor of two evaluation vectors.
  simp [productOfMinors, staircaseBlock, decreasingPosition_paramV, fockPoly, highestVector,
    MixedCartanEmbedding.top, prod_mul_distrib, h_minors]

/-- If l fits O, consider the standard Fock dual pair on the variables n × r with signs 1 on the
rows and `O.signs` on the columns and weights r₋ (the number of minus signs) and
−(⌊n/2⌋ + `O.weight w`). For it the product of minors `O.productOfMinors w` is nonzero, harmonic on
both sides, and highest (`IsJointHighest`) for the rows, ordered by `O.paramV w`, of weight the
lowest K-type of this parameter, and for the columns, ordered by −l_w, of weight
`New.staircaseWeight`. -/
lemma FitsParams.isJointHighest_productOfMinors {O : DescentPair E r n}
    {l : InfinitePlace E → r → ℤ} (h_fits : O.FitsParams l) (w : InfinitePlace E) :
    (FockDualPair.std 1 O.signs (negCount O.signs)
        (-((Fintype.card n / 2 : ℕ) + O.weight w))).IsJointHighest
      (O.paramV w) (-l w) (O.productOfMinors w) (toHCParam 1 (O.paramV w)).lowestKType
      (staircaseWeight n O.signs O.numbering
        (fun η : ℤˣ ↦ if η = 1 then O.colsPlus w else O.colsMinus w)
        (-((Fintype.card n / 2 : ℕ) + O.weight w))) := by
  refine isJointHighest_prod_det_pow_staircaseWeight
    (h_fits.paramsCorrespond w).hasGap_left.injective
    (O.isHCParam_paramV w).1 (h_fits.numbering_eq w) _ (fun η ↦ ?_) ?_ fun a ↦ ?_
  · -- No minor is larger than the number of columns of its sign.
    fin_cases η
    exacts [fun i hi _ ↦ h_fits.colsPlus_eq_zero w i hi,
      fun i hi _ ↦ h_fits.colsMinus_eq_zero w i hi]
  · -- Minors of opposite signs fit into the rows, as `r₊ + r₋ = card r < card n`.
    have h_signs : card {c // O.signs c = 1} + negCount O.signs = card r := by
      simpa [Fintype.card_subtype, negCount] using card_congr (.sigmaFiberEquiv O.signs)
    have h_rank : card r < card n := O.rank_lt
    intro i j hij
    by_cases hi : card {c // O.signs c = 1} < i
    · exact Or.inl (h_fits.colsPlus_eq_zero w i hi)
    · exact Or.inr (h_fits.colsMinus_eq_zero w j (by omega))
  · -- The weight on the rows is the lowest K-type of `O.paramV w`: unfold both and split the sum
    -- over the minors of sign `-1`, using that the orders of `± O.paramV w` are reverse.
    have h_lt : decreasingPosition (O.paramV w) a < card n := by simp [decreasingPosition_paramV]
    have h_split :
        ∑ i ∈ Ico 1 (card n - decreasingPosition (O.paramV w) a), (O.colsMinus w i : ℤ) +
            ∑ i ∈ Ico (decreasingPosition (-O.paramV w) a + 1) (card n), (O.colsMinus w i : ℤ) =
          ∑ i ∈ Ico 1 (card n), (O.colsMinus w i : ℤ) := by
      have h_rev : decreasingPosition (-O.paramV w) a + 1 = card n - decreasingPosition (O.paramV w)
        a := by
        grind [decreasingPosition_paramV]
      rw [h_rev, sum_Ico_consecutive _ (by omega) (by omega)]
    simp [subtype_card, Int.units_ne_iff_eq_neg, vacuumWeight, detExp, sum_Ico_reflect,
      diagramWeight_apply, ← Ico_succ_left_eq_Ioo, O.isHCParam_paramV.lowestKType_eq,
      sum_add_distrib, negCount, rankAt]
    omega

/-- If l fits O, the lowest K-type of −l_w on W is `New.staircaseWeight`, the column weight of the
staircase, that is, of the product over both signs and all p < n of the leading p × p minors to the
powers k⁺(p) = `O.colsPlus w p` (sign 1) and k⁻(p) = `O.colsMinus w p` (sign −1), for the weight
−(⌊n/2⌋ + `O.weight w`). -/
lemma FitsParams.lowestKType_eq_staircaseWeight {O : DescentPair E r n}
    {l : InfinitePlace E → r → ℤ} (h_fits : O.FitsParams l) (w : InfinitePlace E) (c : r) :
    (toHCParam O.signs (-l w)).lowestKType c =
      staircaseWeight n O.signs O.numbering
        (fun η : ℤˣ ↦ if η = 1 then O.colsPlus w else O.colsMinus w)
        (-((Fintype.card n / 2 : ℕ) + O.weight w)) c := by
  -- A joint harmonic `Q` for the two lowest K-types exists by `paramsCorrespond`, and it spans the
  -- polynomials with the properties of the product of minors. So both have the same column weight.
  let γ : ℤ := (card n / 2 : ℕ) + O.weight w
  let T : FockDualPair (1 : n → ℤˣ) O.signs (n × r) :=
    FockDualPair.std 1 O.signs (negCount O.signs) (-γ)
  let ν : r → ℤ := staircaseWeight n O.signs O.numbering
    (fun η ↦ if η = 1 then O.colsPlus w else O.colsMinus w) (-γ)
  obtain ⟨Q, hQ⟩ : ∃ Q : MvPolynomial (n × r) ℂ, IsJointHarmonic T (O.paramV w) (-l w) Q :=
    (h_fits.paramsCorrespond.isMatch w).exists_isJointHarmonic
  obtain ⟨h_ne, ⟨h_torus, h_cols⟩, h_harm, h_rows, h_harm_swap⟩ :
      T.IsJointHighest (O.paramV w) (-l w) (O.productOfMinors w)
        (toHCParam 1 (O.paramV w)).lowestKType ν :=
    h_fits.isJointHighest_productOfMinors w
  obtain ⟨a, ha⟩ : ∃ a : ℂ, O.productOfMinors w = a • Q :=
    hQ.exists_eq_smul_of_row_weight h_harm h_harm_swap h_rows h_cols
  -- Compare the eigenvalues of the column torus on the nonzero polynomial `a • Q`.
  have h_eigen : T.swap.oscRows.E c c (O.productOfMinors w) =
      ((toHCParam O.signs (-l w)).lowestKType c : ℂ) • O.productOfMinors w := by
    obtain ⟨h_torus_Q, -⟩ := hQ.isJointHighest.isKHighest_cols
    rw [ha, map_smul, h_torus_Q, smul_comm]
  have h_cast : ((toHCParam O.signs (-l w)).lowestKType c : ℂ) = ν c :=
    (smul_left_inj h_ne).1 (h_eigen.symm.trans (h_torus c))
  exact Int.cast_injective h_cast

/-- If l fits O, the product of minors at w is a joint harmonic for (V, W), with weights r₋ (the
number of minus signs of W) and −(⌊n/2⌋ + `O.weight w`) and parameters `O.paramV w` and −l_w. -/
lemma FitsParams.isJointHarmonic_productOfMinors {O : DescentPair E r n}
    {l : InfinitePlace E → r → ℤ} (h_fits : O.FitsParams l) (w : InfinitePlace E) :
    IsJointHarmonic
      (FockDualPair.std 1 O.signs (negCount O.signs) (-((Fintype.card n / 2 : ℕ) + O.weight w)))
      (O.paramV w) (-l w) (O.productOfMinors w) := by
  refine ⟨h_fits.paramsCorrespond.isMatch w, ?_⟩
  rw [funext (h_fits.lowestKType_eq_staircaseWeight w)]
  exact h_fits.isJointHighest_productOfMinors w

/-- Let the parameter l fit O, let l' = `O.paramV`, let r₋ be the number of minus signs of W and
γ_w = ⌊n/2⌋ + `O.weight w`. There are polynomials Φ_w, one for each infinite place w, such that
Φ_w is a joint harmonic for (V, W) with weights r₋, −γ_w and parameters l'_w, −l_w, and the
polynomial `O.fockPoly` of the highest vector of l' is the product of the Φ_w, each in the variables
of w. Moreover, the lowest K-type of −l_w is `New.staircaseWeight`, the column weight of a product
of leading p × p minors of the two signs to the powers k⁺ = `O.colsPlus w` and k⁻ = `O.colsMinus w`.
-/
lemma FitsParams.exists_isJointHarmonic (O : DescentPair E r n) {l : InfinitePlace E → r → ℤ}
    (h_fits : O.FitsParams l) :
    (∃ Φ : InfinitePlace E → MvPolynomial (n × r) ℂ,
      (∀ w : InfinitePlace E, IsJointHarmonic
        (FockDualPair.std 1 O.signs (negCount O.signs) (-((Fintype.card n / 2 : ℕ) + O.weight w)))
        (O.paramV w) (-l w) (Φ w)) ∧
      O.fockPoly (highestVector O.columnCount O.paramV) = ∏ w : InfinitePlace E,
        (Φ w).rename (w, ·)) ∧
    ∀ (w : InfinitePlace E) (c : r), (toHCParam O.signs (-l w)).lowestKType c =
      staircaseWeight n O.signs O.numbering
        (fun η : ℤˣ ↦ if η = 1 then O.colsPlus w else O.colsMinus w)
        (-((Fintype.card n / 2 : ℕ) + O.weight w)) c :=
  ⟨⟨O.productOfMinors, h_fits.isJointHarmonic_productOfMinors, O.fockPoly_highestVector⟩,
    h_fits.lowestKType_eq_staircaseWeight⟩

variable (O : DescentPair E r n) [WeilData E]

/-- Suppose W has positive rank (`Nonempty r`) and l fits the descent pair O (`O.FitsParams l`). Let
v⁺ = `New.highestVector` for l' = `O.paramV`, and let P_{v⁺} be its polynomial `O.fockPoly`. Then
the Fock vector of P_{v⁺} is an edge from `New.typeKernel l O.signs` to `New.typeKernel O.paramV 1`.
Here `New.typeKernel` is the product over the infinite places of the discrete series kernels, and an
edge (`New.IsEdge`) is a half edge in both directions between two such kernels. -/
lemma FitsParams.isEdge [Nonempty r] {l : InfinitePlace E → r → ℤ} (h_fits : O.FitsParams l) :
    IsEdge
      (realPairWeil (fun _ ↦ negCount O.signs)
        fun w : InfinitePlace E ↦ (Fintype.card n / 2 : ℕ) + O.weight w)
      (typeKernel l O.signs) (typeKernel O.paramV 1)
      (O.fockPoly (highestVector O.columnCount O.paramV)) := by
  obtain ⟨⟨Φ, h_joint, h_prod⟩, -⟩ := h_fits.exists_isJointHarmonic
  have : Nonempty n := .map O.incl inferInstance
  simpa only [h_prod] using isEdge_of_isJointHarmonic h_joint

/-! ### The descent as the conjugate of a lift -/

/-- For a descent pair (W, V), x real in U(V) and k in the level of V, the Weil operator of (1, (x,
k)) of the theta kernel sends `O.fockDatum` at conj ξ to `O.levelChar k` times `O.fockDatum` at
conj(ρ(x)ξ), where ρ = `New.conjWeylRep`. -/
lemma omega_fockDatum_star (x : GInf E 1) (k : O.levelGroup) (ξ : WeylIndex n O.columnCount → ℂ) :
    O.pairThetaKernel.ω (1, x, k.val) (O.fockDatum (star ξ)) =
      O.levelChar k • O.fockDatum (star (conjWeylRep O.columnCount O.detExp x ξ)) := by
  -- `x` acts on the Fock vector by `realPairWeil_fockPoly`, and `k` multiplies `O.blockDatum` by
  -- the character of the level (`omega_blockDatum_eq_smul` with trivial component in `U(W)`).
  let j := levelOf.reduction O.placeAt (descentResidueLevel O.toLevelPlaces O.incl) k
  have h_reduce : stdLevel.reduceFamily O.placeAt ⟨k, levelOf_le_stdLevel k.prop⟩ =
      firstBlockHom O.toLevelPlaces O.incl (stdLevel.reduceFamily O.chosenPlace 1) * j.val := by
    rw [map_one, map_one, one_mul]
    rfl
  have h_fin : pairWeil O.W (stdSpace E n) O.charW O.charV ((1, 1), 1, k.val) O.blockDatum.val =
      O.levelChar k • O.blockDatum.val := by
    simpa [j] using O.omega_blockDatum_eq_smul 1 ⟨k, levelOf_le_stdLevel k.prop⟩ j h_reduce
  refine (pairWeil_integrated_all 1 1 x k.val _ O.blockDatum.val).trans ?_
  rw [realPairWeil_fockPoly, h_fin, map_smul]

open ComplexConjugate in
/-- For rational γ in U(I_n) and k in the level, the kernel `New.DescentPair.conjKernel` with vector
c(k)ρ(γ)v at (g, γxk) equals that with vector v at (g, x). Here ρ = `New.Space.weightRep` and
c = `New.DescentPair.levelChar`. -/
lemma conjKernel_equivariant (γ : U (stdSpace E n).J) (k : O.levelGroup)
    (v : WeylIndex n O.columnCount → ℂ) (g : G E O.signs) (x : Gf E n) :
    O.conjKernel g (stdEmbFin γ * x * k.val)
        (O.levelChar k • (stdSpace E n).weightRep O.columnCount O.detExp γ v) =
      O.conjKernel g x v := by
  -- Move the real part of `γ` and `k⁻¹` onto the datum by `omega_fockDatum_star`; the character has
  -- modulus 1, so its value at `k⁻¹` is the conjugate of its value at `k`.
  have h_inv : O.levelChar k⁻¹ = conj (O.levelChar k) := by
    rw [map_inv, Complex.inv_eq_conj (LevelPlaces.isOfFinOrder_level_char k).norm_eq_one]
  have h_move : O.fockDatum (star (O.levelChar k • (stdSpace E n).weightRep O.columnCount O.detExp γ
    v)) =
      O.pairThetaKernel.ω (1, ((stdSpace E n).ratEmbed γ).1, (k⁻¹).val) (O.fockDatum (star v)) := by
    rw [O.omega_fockDatum_star]
    simp [h_inv, weightRep_apply]
  have h_point : ((g, 1, stdEmbFin γ * x * k.val) *
      (1, ((stdSpace E n).ratEmbed γ).1, (k⁻¹).val) : G E O.signs × G E (1 : n → ℤˣ)) =
      (g, (stdSpace E n).ratEmbed γ * (1, x)) := by
    simp [Prod.mul_def]
    rfl
  simp only [conjKernel, IsLinearMap.mk'_apply, h_move, ← pairTheta_mul, h_point]
  -- The theta kernel is left invariant under rational points.
  exact congrArg conj (O.pairThetaKernel.swap.theta_rat_mul _ ⟨γ, rfl⟩ (1, x))

/-- The normalized descent θΞ = `O.normalizedDescent Ξ`, for a form `Ξ : O.FormV` on V, equals
d · [`stdLevel` : `O.levelGroup`] times the descent of Ξ♮ from V to W by the datum
`O.fockDatum v⁺` = v_{P_{v⁺}} ⊗ `O.blockDatum`. Here d, the dimension of the Weyl module of
`O.columnCount`, is the number of elements of `WeylIndex n O.columnCount`. v⁺ is the highest vector
for `O.paramV`. Ξ♮ = `ofAlgForm O.paramV 1 Ξ` is the function g ↦ ⟨v⁺, ρ(g_∞⁻¹) Ξ(g_f)⟩ on U(V)(𝔸),
the signs 1 saying that V is definite. -/
lemma normalizedDescent_eq_smul_star_lift_swap (Ξ : O.FormV) :
    O.normalizedDescent Ξ = (Fintype.card (WeylIndex n O.columnCount) * stdLevelIndex O.levelGroup :
      ℂ) •
      star (lift O.pairThetaKernel.swap (O.fockDatum (highestVector O.columnCount O.paramV))
        (star (ofAlgForm O.paramV 1 Ξ.val))) := by
  ext y
  let v : WeylIndex n O.columnCount → ℂ := highestVector O.columnCount O.paramV
  let Φ : G E (1 : n → ℤˣ) → ℂ :=
    star fun x ↦ pairTheta O.W (stdSpace E n) O.charW O.charV (O.fockDatum (star v)) (y, x)
  -- The conjugate lift at `y` is the integral of the conjugate kernel `Φ` against the form.
  have h_lift :
      star (lift O.pairThetaKernel.swap (O.fockDatum v) (star (ofAlgForm O.paramV 1 Ξ.val))) y =
        ∫ x, Φ x * ofAlgForm O.paramV 1 Ξ.val x ∂(stdSpace E n).quotMeasure := by
    simp [lift, ← integral_conj, Φ, v, star_highestVector, pairTheta]
  have h_aut : (stdSpace E n).IsAutomorphic Φ := by
    obtain ⟨K, K', h_level⟩ := exists_level_pairWeil O.charW O.charV O.blockDatum.prop
    refine (O.pairThetaKernel.swap.isAutomorphic K' (fun k hk ↦ ?_) y).conj
    change pairWeil O.W (stdSpace E n) O.charW O.charV ((1, 1), 1, k) (O.fockDatum (star v)) = _
    rw [pairWeil_integrated_fin, h_level 1 (one_mem K) k hk]
  -- `Φ (x, g)` is `O.conjKernel y g` of the translate of the highest vector by the real point `x`.
  have h_real (x : GInf E (1 : n → ℤˣ)) (g : Gf E n) :
      Φ (x, g) = O.conjKernel y g (conjWeylRep O.columnCount O.detExp x v) := by
    have h_move : pairWeil O.W (stdSpace E n) O.charW O.charV (1, x, 1) (O.fockDatum (star v)) =
        O.fockDatum (star (conjWeylRep O.columnCount O.detExp x v)) := by
      simpa using O.omega_fockDatum_star x 1 v
    simp [conjKernel, Φ, ← h_move, ← pairTheta_mul]
  -- The function `g ↦ O.conjKernel y g (Ξ g)` is invariant under the level, so its integral over
  -- the finite points is the class sum that defines `O.normalizedDescent`.
  have h_inv : O.levelGroup ≤ rightStabilizer fun g : Gf E n ↦ O.conjKernel y g (Ξ.val.val g) := by
    intro k hk g
    have h_law := O.conjKernel_equivariant 1 ⟨k, hk⟩ (Ξ.val.val g) y g
    rw [← levelSpace_smoothFormRep_apply Ξ.prop] at h_law
    simpa using h_law
  rw [Pi.smul_apply, h_lift,
    integral_mul_eq_classIntegral O.isHCParam_paramV O.levelGroup h_aut (O.conjKernel y) h_real,
    classIntegral_eq_classSum h_inv]
  simp [field, normalizedDescent, -Fintype.card_pi]

end New.DescentPair

/-!
## Residue rings and level indices for the modulus of level places

`X.levelModulus 1` is the product of the places of `X : New.LevelPlaces E`; we consider its quotient
ring.
-/

namespace New.LevelPlaces

open Matrix Fintype

variable {N : Type} [Fintype N] [DecidableEq N] {E : Type} [Field E] [CMType E]

/-- Let `X` be a choice of level places: the chosen places and the places of the twist. An element
of `stdLevel E N`, the stabiliser of the standard lattice in the finite adelic unitary group,
reduces to `1` modulo `X.levelModulus 1`, the product of all places of `X`, exactly if it reduces
to `1` modulo each place of `X`. -/
lemma ker_reductionGL_eq (X : LevelPlaces E) :
    (X.levelModulus 1).reductionGL.ker = (stdLevel.reduceFamily (n := N) X.placeAt).ker := by
  -- By the Chinese remainder theorem for matrices, it suffices to reduce at each place of `X`.
  ext k
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, funext_iff, Units.ext_iff,
    Modulus.matrix_eq_iff_map_modulusResidue_eq X.apart.injective X.ideal_levelModulus_one]
  refine forall_congr' fun i ↦ ?_
  rw [Rows.reductionGL_map_modulusResidue, Units.ext_iff]
  simp [stdLevel.reduceFamily]

/-- The quotient ring of `X.levelModulus e`, the modulus `M ^ e Q`, has as order the `e`-th power of
the product of the norms of the places of `M`, times the product of the norms of the places of
`Q`. -/
lemma card_levelModulus_residueRing (X : LevelPlaces E) (e : ℕ) :
    card (X.levelModulus e).ResidueRing =
      (∏ i : X.ChosenIndex, (X.chosenPlace i).q) ^ e * ∏ i : X.TwistIndex, (X.twistPlace i).q := by
  -- The cardinality of the residue ring is the absolute norm of the ideal, which is multiplicative.
  rw [card_eq_nat_card]
  change Ideal.absNorm (X.levelModulus e).ideal = _
  simp [levelModulus]

variable (N)

/-- Let `R` be the residue ring of `X.levelModulus 1`, the modulus M·Q, where M and Q are the
products of the chosen places and of the places of the twist of X. Then the order of `GL N R` is the
level index `stdLevelIndex (levelOf X.placeAt ⊥)`, with ⊥ the trivial subgroup. -/
lemma card_GL_levelModulus (X : LevelPlaces E) :
    card (GL N (X.levelModulus 1).ResidueRing) = stdLevelIndex (levelOf (n := N) X.placeAt ⊥) := by
  -- The level is the kernel of reduction modulo `X.levelModulus 1`, the preimage of the trivial
  -- subgroup of `GL N ResidueRing`; its index is that of the trivial subgroup.
  have h_level : levelOf (n := N) X.placeAt ⊥ = (X.levelModulus 1).levelOfSubgroup ⊥ := by
    rw [levelOf, MonoidHom.comap_bot, ← ker_reductionGL_eq, ← MonoidHom.comap_bot]
  rw [h_level, Modulus.stdLevelIndex_levelOfSubgroup, Subgroup.index_bot, card_eq_nat_card]

end New.LevelPlaces

end
