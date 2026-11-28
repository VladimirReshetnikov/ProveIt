import Lib.ClassField.HeckeCharacter.SplitTameCharacters
import Lib.Weil.MixedModel.AdaptedSplitting

/-!
# Coordinates on a line parabolic and Poisson's formula for terms along lines

This file concerns the stabiliser of an isotropic line in a hermitian space `V'`, split by
`D : V'.Splitting V Unit` into a hyperbolic plane and `V`. It gives coordinates on the unipotent
radical and on the Levi factor of this stabiliser.

## Main definitions and results

* `New.Exchange.lineTerm`: two families, indexed by an adele, of operators from `Hom(W', V')` data
  to those of `Hom(W, V)`: a rank-one translation, then both zero terms.
* `New.Exchange.lineTerm_pairWeil_levi`: if the line of `W'` is fixed or `W` and `V` have equal
  rank, they intertwine the Weil representations `New.pairWeil` on Levi elements, up to a scalar and
  a rescaling of the adele.
* `New.Exchange.tsum_lineTerm`: the theta sums over `E` of the two families agree, since they are
  the two mixed models of one hyperbolic plane.
* `New.Exchange.lineTermSplitting`, `New.Exchange.frameAt_lineTermSplitting`: the splittings behind
  the two models, and their frames.

Notions from other files:
* `New.Space`: a hermitian space over `E` with Gram matrix `J` and an adelic frame `x` that
  diagonalises `J` at every place; `𝒮 V` is its data space and `θ V` the theta functional on it.
* `New.Space.Splitting`: for `D : V.Splitting V₀ p`, dual isotropic frames `k`, `l` indexed by `p`
  and an isometric embedding `i` of `V₀` orthogonal to both, which together fill `V`.
* `New.Space.Splitting.zeroTerm`: the map `𝒮 V → 𝒮 V₀` that averages over the adelic span of `k`
  modulo its rational points; `D.slice x` is translation by `l x` followed by it.
* `New.Space.Splitting.levi`: the homomorphism sending `(m, g₀)` to the element that acts by `m` on
  the frame `k`, by `g₀` on `V₀` and by `m*⁻¹` on the frame `l`.
* `New.pairWeil W V a b`: the Weil representation of the two unitary groups on `𝒮 (W.hom V)`,
  twisted by the automorphic characters `a` and `b` of the determinants.

## Relation to the literature

Known; see `Lib.SiegelWeil.Tower.LargeSideConstantTerm` for sources.
-/

noncomputable section

namespace New.Exchange

/-!
## Coordinates on the radical and Levi factor of a line stabiliser

For a splitting `D : V'.Splitting V Unit` of `V'` into a hyperbolic plane and `V`, coordinates on
the stabiliser of the isotropic line: `New.Exchange.lineRadical` on the unipotent radical and
`New.Exchange.lineLevi` on the Levi factor.
-/

section LineParabolic

variable {E n m : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m] {s : n → ℤˣ} {t : m → ℤˣ} {V' : Space E m t} {V : Space E n s}
  (D : V'.Splitting V Unit)

/-- The element `D.radicalElement c b` of the unipotent radical with `c = V.x⁻¹ * q.1` and
`b = 2 q.2`. -/
abbrev lineRadical (q : Matrix n Unit (𝔸 E) × Matrix Unit Unit (𝔸 E)) : G E t :=
  D.radicalElement (V.x⁻¹.val * q.1) (toAdele (2 : E) • q.2)

/-- The homomorphism that sends an idele `a` and an element `g` of the group of `V` to the Levi
element `D.levi (a⁻¹, g)`, which acts by `a⁻¹` on the isotropic line. -/
def lineLevi : (𝔸 E)ˣ × G E s →* G E t :=
  D.levi.comp (((Matrix.GeneralLinearGroup.scalar Unit).comp invMonoidHom).prodMap (.id (G E s)))

end LineParabolic

/-!
## Terms along a line in two models and Poisson's formula

Let `A` split `W'` as a hyperbolic plane plus `W`, and `X` split `V'` as a hyperbolic plane plus `V`
(`New.Space.Splitting`: isotropic dual frames `k`, `l` and an isometry `i`; `kAdelic`, `lAdelic`,
`iAdelic` are these in adelic coordinates, `kCoord`, `lCoord`, `iCoord` the forms that give the
three coordinates of a vector).
-/

section TwoLineTerms

open Matrix Kronecker Fintype WeilData Space Splitting Function

variable {E : Type} [Field E] [CMType E] [WeilData E] {n n' r r' : Type} [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n'] [Fintype r] [DecidableEq r] [Fintype r'] [DecidableEq r']
  {s : n → ℤˣ} {s' : n' → ℤˣ} {t : r → ℤˣ} {t' : r' → ℤˣ} {W : Space E n s} {W' : Space E n' s'}
  {V : Space E r t} {V' : Space E r' t'} (A : W'.Splitting W Unit) (X : V'.Splitting V Unit)

/-- The term at the adele `a`, from `𝒮 (W'.hom V')` to `𝒮 (W.hom V)`, in the model `β`. For
`β = true` it is translation by the map `a • X.kAdelic * A.kCoord`, followed by the zero term along
the line of `A` and then the one along the line of `X`. For `β = false` it is translation by
`a • X.lAdelic * A.lCoord`, followed by the zero term along the line of `X` and then that of `A`. -/
noncomputable def lineTerm (β : Bool) (a : 𝔸 E) : 𝒮 (W'.hom V') →L[ℂ] 𝒮 (W.hom V) :=
  if β then (X.homTarget W).zeroTerm ∘L A.homSlice V' (a • X.kAdelic)
  else (A.homSource V).zeroTerm ∘L (X.homTarget W').zeroTerm ∘L
    ϱ (W'.hom V') (matrixToVec (a • X.lAdelic * A.lCoord))

section

omit [WeilData E]

/-- The block on `W` of the Levi element of `A` attached to an invertible `m` and a unitary `g`
is `g`. -/
lemma iCoord_levi_iAdelic (m : GL Unit (𝔸 E)) (g : G E s) :
    A.iCoord * ((A.levi (m, g)).adeleMatrix * A.iAdelic) = g.adeleMatrix := by
  simp [Splitting.levi, Matrix.mul_assoc, G.adeleMatrix_ofMatrix, Matrix.add_mul, coord_mul_frame,
    coord_mul_frame_mul]

/-- The Levi element of `A` acting by the scalar `u` on its line, on the right, and the inverse of
`lineLevi X (c, h)`, on the left, scale the rank-one map `X.kAdelic * A.kCoord` by `c * u`. -/
lemma lineLevi_inv_mul_kAdelic_mul_levi (u c : (𝔸 E)ˣ) (g : G E s) (h : G E t) :
    (lineLevi X (c, h))⁻¹.adeleMatrix *
        (X.kAdelic * (A.kCoord * (A.levi (GeneralLinearGroup.scalar Unit u, g)).adeleMatrix)) =
      (↑(c * u) : 𝔸 E) • (X.kAdelic * A.kCoord) := by
  simp [lineLevi, Splitting.levi, G.adeleMatrix_inv, G.adeleMatrix_ofMatrix, conjTranspose_coord,
    Pi.star_def, ← smul_eq_diagonal_mul, smul_smul, Matrix.mul_assoc, Matrix.mul_add,
    Matrix.add_mul, stdForm_mul_stdForm_mul, coord_mul_frame_mul, mul_comm]

/-- The Levi element of `A` acting by the scalar `u` on its line, on the right, and the inverse of
`lineLevi X (c, h)`, on the left, scale the rank-one map `X.lAdelic * A.lCoord` by the conjugate of
`(c * u)⁻¹`. -/
lemma lineLevi_inv_mul_lAdelic_mul_levi (u c : (𝔸 E)ˣ) (g : G E s) (h : G E t) :
    (lineLevi X (c, h))⁻¹.adeleMatrix *
        (X.lAdelic * (A.lCoord * (A.levi (GeneralLinearGroup.scalar Unit u, g)).adeleMatrix)) =
      star (↑(c * u)⁻¹ : 𝔸 E) • (X.lAdelic * A.lCoord) := by
  simp [lineLevi, Splitting.levi, G.adeleMatrix_inv, G.adeleMatrix_ofMatrix, conjTranspose_coord,
    Pi.star_def, ← smul_eq_diagonal_mul, smul_smul, Matrix.mul_assoc, Matrix.mul_add,
    Matrix.add_mul, stdForm_mul_stdForm_mul, coord_mul_frame_mul, mul_comm]

end

/-- Equivariance of `lineTerm` under Levi elements. `lineTerm A X β ξ` is the term at the adele `ξ`
from data on `Hom(W', V')` to data on `Hom(W, V)`, in one of two models chosen by `β`. Let the idele
`u` act on the line of `A` in `W'` and `c⁻¹` on that of `X` in `V'`, and assume that `u = 1` or that
`W` and `V` have equal rank. Apply these Levi elements (with `g`, `h` on `W`, `V`) in the
representation twisted by `a * upsilonU1`, with `upsilonU1` the fixed splitting character on
norm-one ideles. The result is the following, with `x = c * u`: replace `ξ` by `ξ x` if `β` holds
and by `ξ (star x)⁻¹` otherwise, apply `(g, h)` in the representation twisted by `a`, and multiply
by `√|u|^(2 card r + 2) / (a.spaceChar (card n) x * √|x|^(card n + 2))`, where the `+ 2` in the last
exponent is present only when `β` is false. Here `a.spaceChar k` is the idele character attached to
`a` in rank `k`, and `|·|` is the idele norm `ideleAbs`. -/
lemma lineTerm_pairWeil_levi {u : (𝔸 E)ˣ} (hu : u = 1 ∨ card r = card n) (a : AutChar E) (β : Bool)
    (ξ : 𝔸 E) (g : G E s) (c : (𝔸 E)ˣ) (h : G E t) (f : 𝒮 (W'.hom V')) :
    let x : (𝔸 E)ˣ := c * u
    lineTerm A X β ξ (pairWeil W' V' (a * upsilonU1) (a * upsilonU1)
        (A.levi (GeneralLinearGroup.scalar Unit u, g), lineLevi X (c, h)) f) =
      (√(ideleAbs u) ^ (2 * card r + 2) /
          ((a.spaceChar (card n)).val x * √(ideleAbs x) ^ (card n + (if β then 0 else 2))) : ℂ) •
        pairWeil W V a a (g, h) (lineTerm A X β (ξ * (if β then ↑x else star ↑x⁻¹)) f) := by
  intro x
  -- The zero terms along the lines of `X` and of `A` under a Levi point, for any partner `T`.
  have h_target {m : Type} [Fintype m] [DecidableEq m] {σ : m → ℤˣ} (T : Space E m σ)
      (b b' : AutChar E) (k : G E σ) (φ : 𝒮 (T.hom V')) :
      (X.homTarget T).zeroTerm (pairWeil T V' b (b' * upsilonU1) (k, lineLevi X (c, h)) φ) =
        (((b.spaceChar (card m)).val c : ℂ)⁻¹ * (√(ideleAbs c) ^ card m : ℂ)⁻¹) •
          pairWeil T V b b' (k, h) ((X.homTarget T).zeroTerm φ) := by
    simpa [lineLevi] using X.homTarget_zeroTerm_pairWeil T b b' _ h _
      (X.actsOnFrame_levi (.scalar _ c⁻¹) h) (iCoord_levi_iAdelic X _ h) k φ
  have h_source {m : Type} [Fintype m] [DecidableEq m] {σ : m → ℤˣ} (T : Space E m σ)
      (b b' : AutChar E) (k : G E σ) (φ : 𝒮 (W'.hom T)) :
      (A.homSource T).zeroTerm (pairWeil W' T (b * upsilonU1) b' (A.levi (.scalar _ u, g), k) φ) =
        (((b'.spaceChar (card m)).val u : ℂ)⁻¹ * √(ideleAbs u) ^ card m) •
          pairWeil W T b b' (g, k) ((A.homSource T).zeroTerm φ) := by
    simpa using A.homSource_zeroTerm_pairWeil T b b' _ g _
      (A.actsOnFrame_levi (.scalar _ u) g) (iCoord_levi_iAdelic A _ g) k φ
  -- The scalars given by the two laws agree with the stated one: if `u = 1` or the ranks are equal,
  -- the powers of the splitting character and of the norm at `u` match, by field arithmetic.
  obtain ⟨h_scalar_k, h_scalar_l⟩ :
      (((a * upsilonU1).spaceChar (card r')).val u : ℂ)⁻¹ * √(ideleAbs u) ^ card r' *
        (((a.spaceChar (card n)).val c : ℂ)⁻¹ * (√(ideleAbs c) ^ card n : ℂ)⁻¹) =
      √(ideleAbs u) ^ (2 * card r + 2) / ((a.spaceChar (card n)).val x * √(ideleAbs x) ^ card n) ∧
      (((a * upsilonU1).spaceChar (card n')).val c : ℂ)⁻¹ * (√(ideleAbs c) ^ card n' : ℂ)⁻¹ *
        (((a.spaceChar (card r)).val u : ℂ)⁻¹ * √(ideleAbs u) ^ card r) =
      √(ideleAbs u) ^ (2 * card r + 2) /
        ((a.spaceChar (card n)).val x * √(ideleAbs x) ^ (card n + 2)) := by
    obtain hu | hu := hu <;> simp [x, hu, A.card_eq, X.card_eq, AutChar.spaceChar, field, pow_add,
      baseChange_upsilonU1, circleChar_inv_apply, pow_mul', mul_pow, ideleAbs_nonneg_and_ne_zero]
  -- In each model move `ϱ` across `pairWeil`, which rescales `ξ`, then apply the two laws.
  cases β <;> simp [x, lineTerm, homSlice, rho_pairWeil, h_target, h_source, Matrix.mul_assoc,
    vecToMatrix_matrixToVec, lineLevi_inv_mul_kAdelic_mul_levi, lineLevi_inv_mul_lAdelic_mul_levi,
    smul_smul, h_scalar_k, h_scalar_l, -matrixToVec_smul]

/-- The index set of the isotropic frames that split `W'.hom V'` over `W.hom V`. The right summand
indexes one line of the hyperbolic plane `Hom(A, B) ⊕ Hom(A*, B*)`, where `A`, `A*` are the lines
spanned by `A.k`, `A.l` and `B`, `B*` those spanned by `X.k`, `X.l`. -/
abbrev LineIndex (n r : Type) : Type := (Unit × (n ⊕ Unit) ⊕ r × Unit) ⊕ Unit × Unit

/-- A shortcut: the search for this instance inside larger index sets exceeds the default size. -/
instance : DecidableEq (LineIndex n r) := inferInstance

/-- The splitting of `Hom(W', V')` along `Hom(W ⊕ A*, B) ⊕ Hom(A*, V)`, over the plane
`Hom(A, B) ⊕ Hom(A*, B*)` plus `Hom(W, V)`. Here `hyperbolicSum p T` is the orthogonal sum of
`card p` hyperbolic planes and `T`, and `A`, `A*`, `B`, `B*` are the lines as in `LineIndex`. -/
noncomputable def planeSplitting :
    (W'.hom V').Splitting (hyperbolicSum (Unit × Unit) (W.hom V))
      (Unit × (n ⊕ Unit) ⊕ r × Unit) := by
  -- `A.kᴴ * W'.J`, `A.lᴴ * W'.J` and `W.J⁻¹ * A.iᴴ * W'.J` are the coordinates on `W'` along
  -- `A*`, `A` and `W`. The relations of the frame follow from those of `A` and `X`.
  use fromCols (X.k ⊗ₖ (fromRows (W.J * (W.J⁻¹ * A.iᴴ * W'.J)) (A.kᴴ * W'.J))ᵀ)
      ((X.i * V.J⁻¹) ⊗ₖ (A.kᴴ * W'.J)ᵀ),
    fromCols (X.l ⊗ₖ (fromRows (W.J⁻¹ * A.iᴴ * W'.J) (A.lᴴ * W'.J))ᵀ) (X.i ⊗ₖ (A.lᴴ * W'.J)ᵀ),
    fromCols (fromCols (X.k ⊗ₖ (A.lᴴ * W'.J)ᵀ) (X.l ⊗ₖ (A.kᴴ * W'.J)ᵀ))
      (X.i ⊗ₖ (W.J⁻¹ * A.iᴴ * W'.J)ᵀ)
  all_goals
    simp [hom, hyperbolicSum, conjTranspose_J, ← W'.J⁻¹.mul_assoc, ← Matrix.mul_assoc _ (i _),
      conjTranspose_nonsing_inv, conjTranspose_fromCols_eq_fromRows_conjTranspose,
      conjTranspose_fromRows_eq_fromCols_conjTranspose, gram_kk, gram_ki, gram_ll, gram_li, gram_il,
      gram_ii, gram_lk, gram_kl, gram_ik, conjTranspose_kronecker,
      conjTranspose_transpose_eq_transpose_conjTranspose, ← mul_kronecker_mul, ← transpose_mul]
  -- `↓`: the Gram relations must fire before their subterms are simplified.
  all_goals simp [← ext_iff, A.card_eq, X.card_eq, Matrix.mul_assoc, ↓gram_ik, ↓gram_ii, ↓gram_il,
    fromBlocks_one]
  ring

variable (W V) in
/-- The two splittings over `Hom(W, V)` of the plane `Hom(A, B) ⊕ Hom(A*, B*)` plus `Hom(W, V)`.
For `β = true` the first line is the frame `l` of the translation and the second the frame `k` of
the zero term; for `β = false` the two lines are exchanged. -/
noncomputable def planeModel (β : Bool) :
    (hyperbolicSum (Unit × Unit) (W.hom V)).Splitting (W.hom V) (Unit × Unit) :=
  cond β (removePlanes (Unit × Unit) (W.hom V)) (removePlanes (Unit × Unit) (W.hom V)).symm

/-- In each model, the adelic frame `l` of the plane, embedded in `Hom(W', V')` by `planeSplitting`,
is the Kronecker product of the frames of the two lines that translate in `lineTerm`. -/
lemma planeSplitting_iAdelic_mul_planeModel_lAdelic (β : Bool) :
    (planeSplitting A X).iAdelic * (planeModel W V β).lAdelic =
      cond β (X.kAdelic ⊗ₖ A.kCoordᵀ) (X.lAdelic ⊗ₖ A.lCoordᵀ) := by
  cases β <;> simp [planeModel, planeSplitting, removePlanes, Splitting.symm, kAdelic, lAdelic,
    iAdelic, kCoord, lCoord, Space.map_J, hom_point_inv_mul_kronecker, conjTranspose_map_toAdele,
    Matrix.mul_assoc, ratMap_mul_toAdele, fromCols_mul_fromRows, -coe_units_inv, -transpose_mul]

/-- Each line term is the zero term for `planeSplitting` followed by the mixed term `slice`
(translation by `l`, then the zero term) of `planeModel W V β`, the model `β` of the hyperbolic
plane, at the vector with single coordinate `a`. -/
lemma lineTerm_eq_comp_zeroTerm (β : Bool) (a : 𝔸 E) :
    lineTerm A X β a =
      (planeModel W V β).slice (matrixToVec (scalar Unit a)) ∘L (planeSplitting A X).zeroTerm := by
  -- Both sides are a zero term in stages after the same translation.
  have h_zeroTerm : cond β ((A.homSource V').comp (X.homTarget W)).zeroTerm
      ((X.homTarget W').comp (A.homSource V)).zeroTerm =
      ((planeSplitting A X).comp (planeModel W V β)).zeroTerm := by
    -- The hypotheses of `zeroTerm_congr`: the frames `k` are orthogonal, the embeddings `i` equal.
    cases β <;> apply zeroTerm_congr <;>
      simp [planeModel, planeSplitting, removePlanes, Splitting.symm, Splitting.comp, hom,
        homSource, homTarget, conjTranspose_J, ← W'.J⁻¹.mul_assoc, ← Matrix.mul_assoc _ (i _),
        conjTranspose_nonsing_inv, conjTranspose_fromCols_eq_fromRows_conjTranspose,
        fromCols_mul_fromRows, conjTranspose_fromRows_eq_fromCols_conjTranspose, gram_kk, gram_ki,
        gram_kl, gram_lk, conjTranspose_kronecker,
        conjTranspose_transpose_eq_transpose_conjTranspose, ← mul_kronecker_mul, ← transpose_mul]
    -- `↓`: the Gram relation must fire before its product is reassociated.
    all_goals simp [Matrix.mul_assoc, ↓gram_ik]
  have h_point : ((planeSplitting A X).iAdelic * (planeModel W V β).lAdelic) *ᵥ
      matrixToVec (diagonal fun _ : Unit ↦ a) =
      a • matrixToVec (cond β (X.kAdelic * A.kCoord) (X.lAdelic * A.lCoord)) := by
    cases β <;> simp [planeSplitting_iAdelic_mul_planeModel_lAdelic, matrixToVec_smul,
      kronecker_mulVec_eq_matrixToVec, ← smul_eq_mul_diagonal, vecToMatrix_matrixToVec]
  ext1 f
  cases β <;> simp [lineTerm, homSlice, slice, ← zeroTerm_rho_iAdelic, ← zeroTerm_comp, h_point,
    ← h_zeroTerm]

/-- Poisson's formula along the line: the values of the theta functional `θ` at the line terms,
summed over the rational points `ξ : E`, have the same sum in the model `β` as in `true`. -/
lemma tsum_lineTerm (β : Bool) (f : 𝒮 (W'.hom V')) :
    ∑' ξ : E, θ (W.hom V) (lineTerm A X true (toAdele ξ) f) =
      ∑' ξ : E, θ (W.hom V) (lineTerm A X β (toAdele ξ) f) := by
  -- Both sums are the theta value of the zero term of `f` for `planeSplitting`.
  have h_sum (b : Bool) : ∑' ξ : E, θ (W.hom V) (lineTerm A X b (toAdele ξ) f) =
      θ (hyperbolicSum (Unit × Unit) (W.hom V)) ((planeSplitting A X).zeroTerm f) := by
    let _ : Unique (Unit × Unit) := Unique.mk' (Unit × Unit)
    let e : (Unit × Unit → E) ≃ E := Equiv.funUnique (Unit × Unit) E
    have h_point (ξ : E) : matrixToVec (scalar Unit (toAdele ξ)) = toAdele ∘ e.symm ξ :=
      funext fun _ ↦ by simp [e, matrixToVec]
    simp only [lineTerm_eq_comp_zeroTerm, h_point, ContinuousLinearMap.comp_apply]
    rw [← ((planeModel W V b).hasSum_theta_slice _).tsum_eq, ← e.symm.tsum_eq]
  rw [h_sum, h_sum]

/-- The splitting of `Hom(W', V')` over `Hom(W, V)` behind the model `β`. -/
noncomputable def lineTermSplitting (β : Bool) : (W'.hom V').Splitting (W.hom V) (LineIndex n r) :=
  (planeSplitting A X).comp (planeModel W V β)

variable (W V) in
/-- The block-diagonal change of basis, built from `star W.x` and `adaptedHomBasis Unit V`, in which
the frame of `lineTermSplitting` is adapted (`isAdapted_lineTermSplitting`). -/
noncomputable def lineTermBasis : GL (LineIndex n r) (𝔸 E) :=
  blockGL (blockGL (kroneckerGL 1 (transposeGL (blockGL (star W.x, 1))), adaptedHomBasis Unit V), 1)

/-- Each line term is the mixed term `slice` (translation by `l`, then the zero term) of
`lineTermSplitting`, the composite of `planeSplitting` and the model `β`, at the vector with last
coordinate `a` and all others `0`, transformed by the conjugate transpose of the inverse of the
basis `lineTermBasis` (`matrixToVec` reads a matrix as a vector). -/
lemma lineTerm_eq_slice (β : Bool) (a : 𝔸 E) :
    lineTerm A X β a = (lineTermSplitting A X β).slice
      ((lineTermBasis W V)⁻¹.valᴴ *ᵥ (0 ⊕ᵥ matrixToVec (scalar Unit a))) := by
  -- Both sides are one zero term, taken in stages, after the same translation.
  have h_point (v : Unit × Unit → 𝔸 E) :
      ((lineTermSplitting A X β).lAdelic * (lineTermBasis W V)⁻¹.valᴴ) *ᵥ (0 ⊕ᵥ v) =
        ((planeSplitting A X).iAdelic * (planeModel W V β).lAdelic) *ᵥ v := by
    simp [lineTermSplitting, lineTermBasis, Splitting.comp, lAdelic, iAdelic, ← map_inv,
      ratMap_mul_toAdele, fromCols_map, fromBlocks_conjTranspose, fromCols_mul_fromBlocks,
      Matrix.mul_assoc, -coe_units_inv]
  ext1 f
  simp [lineTerm_eq_comp_zeroTerm, slice, ← h_point, lineTermSplitting, ← zeroTerm_rho_iAdelic,
    ← zeroTerm_comp, -coe_units_inv]

/-- The frame of `lineTermSplitting` in the basis `lineTermBasis` at the group element `1`
(`frameAt`: the columns of `l`, `k` and `i` in adelic coordinates), as a block matrix of Kronecker
products of the frames of `X` and `A`; `stdForm` is the diagonal matrix of the signs. The two models
differ by the exchange of two columns. -/
lemma frameAt_lineTermSplitting (β : Bool) :
    (lineTermSplitting A X β).frameAt 1 (lineTermBasis W V) =
      ((((X.lAdelic ⊗ₖ fromCols A.iCoordᵀ A.kCoordᵀ).fromCols (X.iAdelic ⊗ₖ A.kCoordᵀ)).fromCols
            (cond β (X.kAdelic ⊗ₖ A.kCoordᵀ) (X.lAdelic ⊗ₖ A.lCoordᵀ))).fromCols
          (((X.kAdelic ⊗ₖ fromCols (A.iAdelicᴴ * stdForm E s')ᵀ A.lCoordᵀ).fromCols
              ((X.iAdelic * stdForm E t) ⊗ₖ A.lCoordᵀ)).fromCols
            (cond β (X.lAdelic ⊗ₖ A.lCoordᵀ) (X.kAdelic ⊗ₖ A.kCoordᵀ)))).fromCols
        (X.iAdelic ⊗ₖ A.iCoordᵀ) := by
  -- Compare the three column blocks: the basis and its dual are block diagonal, so they act on each
  -- frame separately.
  simp only [Splitting.frameAt, inv_one, G.adeleMatrix_one, Matrix.one_mul, fromCols_ext_iff]
  cases β
  -- The second `simp` may open `hom` only after `hom_point_inv_mul_kronecker` has been used.
  all_goals
    simp [lineTermSplitting, lineTermBasis, adaptedHomBasis, kroneckerGL, transposeGL, ← map_inv,
      fromBlocks_conjTranspose, conjTranspose_kronecker, planeSplitting, planeModel, map_J_inv,
      conjTranspose_transpose_eq_transpose_conjTranspose, star, Space.ratMap, removePlanes, kAdelic,
      lAdelic, iAdelic, kCoord, lCoord, iCoord, Space.map_J, Splitting.symm, Splitting.comp,
      hom_point_inv_mul_kronecker, Matrix.mul_assoc, fromCols_mul_fromRows, fromCols_map,
      fromRows_map, fromCols_mul_fromBlocks, conjTranspose_map_toAdele, ← mul_kronecker_mul,
      ← transpose_mul, -coe_units_inv]
    simp [hom, transpose_fromRows, conjTranspose_nonsing_inv, fromBlocks_mul_fromRows,
      Matrix.mul_assoc, ← mul_kronecker_mul, ← transpose_mul]

/-- If the frames of `A` and `X` are orthonormal at the infinite places and integral at the finite
ones, so is the frame of `lineTermSplitting` in the basis `lineTermBasis`. -/
lemma isAdapted_lineTermSplitting [hA : IsBaseAdapted A] [hX : IsBaseAdapted X] (β : Bool) :
    (lineTermSplitting A X β).IsAdapted 1 (lineTermBasis W V) := by
  -- Up to signs `stdForm` on both sides, the frame is a choice of columns, listed by `cols`, of the
  -- Kronecker product of the adapted frame of `X` and the entrywise conjugate of that of `A`. Here
  -- `colMap .inl` lists the columns of the frame `l` and `colMap .inr` those of `k`.
  let colMap (x : Unit → Unit ⊕ Unit) : LineIndex n r → ((Unit ⊕ Unit) ⊕ r) × ((Unit ⊕ Unit) ⊕ n)
    | .inl (.inl (b, .inl i)) => (.inl (x b), .inr i)
    | .inl (.inl (b, .inr a)) => (.inl (x b), .inl (x a))
    | .inl (.inr (j, a)) => (.inr j, .inl (x a))
    | .inr (b, a) => (.inl (cond β (x b).swap (x b)), .inl (cond β (x a) (x a).swap))
  let signs : (LineIndex n r ⊕ LineIndex n r) ⊕ r × n → ℤˣ :=
    (fun p : Unit × (n ⊕ Unit) ↦ (s ⊕ᵥ 1) p.2) ⊕ᵥ 1 ⊕ᵥ 1 ⊕ᵥ
      (1 ⊕ᵥ (fun p : r × Unit ↦ t p.1) ⊕ᵥ 1) ⊕ᵥ fun p : r × n ↦ s p.2
  let cols : (LineIndex n r ⊕ LineIndex n r) ⊕ r × n → ((Unit ⊕ Unit) ⊕ r) × ((Unit ⊕ Unit) ⊕ n) :=
    colMap .inl ⊕ᵥ colMap .inr ⊕ᵥ Prod.map .inr .inr
  have h_cols : Injective cols := by cases β <;> simp [cols, colMap, Injective]
  refine .of_eq_submatrix_mul (.mul (.of_stdForm fun p ↦ s' p.2)
    (hX.isOrthoIntegral.kronecker hA.isOrthoIntegral)) cols (.of_stdForm signs) ?_ h_cols
  rw [frameAt_lineTermSplitting]
  -- The matrix identity, block by block: every entry is a signed product of entries of the frames.
  cases β
  all_goals
    simp [cols, colMap, signs, ← ext_iff, stdForm, iAdelic, kCoord, lCoord, iCoord,
      Matrix.mul_assoc, conjTranspose_fromCols_eq_fromRows_conjTranspose]
    ac_nf
    grind

end TwoLineTerms

end New.Exchange

end
