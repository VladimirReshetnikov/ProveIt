import Lib.ClassField.HeckeCharacter.TameModulus
import Lib.SiegelWeil.Tower.RealConeIntegral

/-!
# Zero terms of the mixed models of the Weil representation at the real places

The hermitian space `W'` splits as an isotropic line, `W` and a dual line (the splitting
`A : W'.Splitting W Unit`), and `V'` splits as an isotropic line `B`, `V` and a dual line (the
splitting `X : V'.Splitting V Unit`). This file studies the zero term along `Hom(W, B)` of slices of
vectors in the mixed models of the Weil representation at the real places.

## Main definitions and results

* `New.Exchange.realTargetZeroTerm W X`: the zero term along `Hom(W, B)` at the real places.
* `New.Exchange.lineTermReal_true_eq_realTargetZeroTerm`: the real part of the line term is this
  zero term of a slice.
* `New.Exchange.exists_realTargetZeroTerm_eq`: every Schwartz vector is such a zero term.
* `New.Exchange.realSlice_realPairWeil`, `New.Exchange.exists_realTargetZeroTerm_realPairWeil`: real
  points of the target group act on slices, and those with `lineVector X` as an eigenvector at every
  place act on zero terms when `2 ∣ card n`.

Notions from other files:
* `New.Space.Splitting V' V p`: a decomposition of `V'` into isotropic frames `l`, `k` with `p`
  columns and an isometric copy of `V`; `kAdelic`, `lAdelic`, `iAdelic` are its adelic frames, and
  `IsBaseAdapted` says that together they are orthonormal at the infinite places and integral at the
  finite places.
* `homSource`, `homTarget`: the splittings of `Hom(W', V')` over `Hom(W, V')` and of `Hom(W, V')`
  over `Hom(W, V)` induced by `A` and by `X`; `zeroTerm` is the zero term of a splitting.
* `IsAdapted.mixedModel`: the mixed model at the real places of a splitting adapted to a basis; its
  `slice` at a point, and `realSlice` for the splitting `homSource`, map the Fock space `PairFock`
  of one space of homomorphisms to that of a smaller one.
* `lineTerm`, `lineTermReal`: the operator that translates along the line and takes both zero terms,
  and its real part; `realPairWeil γ γ'` is the real Weil action of a pair with weights.

## Relation to the literature

Known; see `Lib.Weil.MixedModel.ZeroTerm` for sources.
-/

noncomputable section

namespace New.Exchange

/-!
## The zero term along `Hom(W, B)` at the real places

The real part `lineTermReal A X true a` of the line term is the zero term along `Hom(W, B)` of the
slice along `A` at `a` times the frame of `B` (`lineTermReal_true_eq_realTargetZeroTerm`). Every
Schwartz vector for `(W, V)` is such a zero term (`exists_realTargetZeroTerm_eq`).
-/

variable {E : Type} [Field E] [CMType E] [WeilData E] {n n' r r' : Type} [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n'] [Fintype r] [DecidableEq r] [Fintype r'] [DecidableEq r']
  {s : n → ℤˣ} {s' : n' → ℤˣ} {t : r → ℤˣ} {t' : r' → ℤˣ} {W : Space E n s} {W' : Space E n' s'}
  {V : Space E r t} {V' : Space E r' t'} (A : W'.Splitting W Unit) (X : V'.Splitting V Unit)

section TargetZeroTerm

open Matrix Kronecker NumberField Fintype Fock Space Splitting WeilData

variable (W) in
/-- The change of basis that makes the frame of `X.homTarget W` orthonormal and integral. -/
def adaptedTargetBasis : GL (Unit × n) (𝔸 E) :=
  kroneckerGL 1 (transposeGL W.dualFrame⁻¹)

variable (W) in
omit [WeilData E] in
/-- In the basis `adaptedTargetBasis W`, the frame of the splitting `X.homTarget W` of `Hom(W, V')`
has the column blocks `X.lAdelic ⊗ₖ stdForm E s` (`stdForm E s` is the diagonal matrix of the signs
`s`), `X.kAdelic ⊗ₖ 1` and `X.iAdelic ⊗ₖ 1`. -/
lemma frameAt_homTarget :
    (X.homTarget W).frameAt 1 (adaptedTargetBasis W) =
      ((X.lAdelic ⊗ₖ stdForm E s).fromCols (X.kAdelic ⊗ₖ 1)).fromCols (X.iAdelic ⊗ₖ 1) := by
  have h_l : (X.homTarget W).lAdelic = X.lAdelic ⊗ₖ W.x.valᵀ := by
    simp [lAdelic, homTarget, hom, map_kronecker, ← mul_kronecker_mul]
  have h_basis : (adaptedTargetBasis W).val = 1 ⊗ₖ W.dualFrame⁻¹.valᵀ := rfl
  have h_inv : (adaptedTargetBasis W)⁻¹.val = 1 ⊗ₖ W.dualFrame.valᵀ := rfl
  have h_dual : W.x.valᵀ * W.dualFrame.valᵀᴴ = stdForm E s := by
    have h_pair : W.dualFrame.valᴴ * W.x.val = stdForm E s := by
      simp [dualFrame, Matrix.mul_assoc]
    rw [conjTranspose_transpose_eq_transpose_conjTranspose, ← transpose_mul, h_pair, stdForm,
      diagonal_transpose]
  rw [Splitting.frameAt, h_l, homTarget_kAdelic, homTarget_iAdelic, h_basis, h_inv,
    conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul, h_dual, ← transpose_mul,
    Units.inv_mul]
  simp

variable (W) in
omit [WeilData E] in
/-- If the frames of `X` are orthonormal at the infinite places and integral (`IsBaseAdapted`), the
splitting `X.homTarget W` is adapted at `1` to the basis `adaptedTargetBasis W`. -/
lemma isAdapted_homTarget [IsBaseAdapted X] :
    (X.homTarget W).IsAdapted 1 (adaptedTargetBasis W) := by
  -- Up to signs on the columns and a reordering `e` of them, the frame of the induced splitting is
  -- `F ⊗ₖ 1`, where `F` is the frame of `X`.
  let F : Matrix r' ((Unit ⊕ Unit) ⊕ r) (𝔸 E) :=
    (X.lAdelic.fromCols X.kAdelic).fromCols X.iAdelic
  let e : ((Unit × n) ⊕ (Unit × n)) ⊕ (r × n) → ((Unit ⊕ Unit) ⊕ r) × n :=
    (Equiv.sumProdDistrib (Unit ⊕ Unit) r n).symm ∘
      Sum.map (Equiv.sumProdDistrib Unit Unit n).symm id
  let ε : ((Unit × n) ⊕ (Unit × n)) ⊕ (r × n) → ℤˣ := (fun x ↦ s x.2) ⊕ᵥ 1 ⊕ᵥ 1
  have h_kron : IsOrthoIntegral (F ⊗ₖ (1 : Matrix n n (𝔸 E))ᴴᵀ) :=
    IsOrthoIntegral.kronecker IsBaseAdapted.isOrthoIntegral .one
  refine h_kron.of_eq_submatrix_mul e (.of_stdForm ε) (Matrix.ext ?_)
    (by simp [e, Function.Injective])
  rw [frameAt_homTarget]
  simp +contextual [F, e, ε, stdForm, diagonal_apply, Matrix.one_apply, ← Pi.one_def,
    Prod.mk_one_one, ite_eq_iff']

variable (W) in
/-- The zero term along `Hom(W, B)` at the real places, where `B` is the isotropic line of `X`. -/
def realTargetZeroTerm [IsBaseAdapted X] : PairFock E s t' →L[ℂ] PairFock E s t :=
  (isAdapted_homTarget W X).mixedModel.slice 0

/-- Let `x` be an adelic matrix with finite part zero. The term `A.homSlice` at `scaleIdele E • x`
of the datum `integrated v f` (real part `v`, finite part `f`) is the datum with real part the slice
of `v` at `x` and finite part the zero term of the real vacuum projection of `f`. -/
lemma homSlice_integrated_of_real [IsBaseAdapted A] {x : Matrix r' Unit (𝔸 E)}
    (hx : ∀ (i : r') (j : Unit), (x i j).2 = 0) (v : PairFock E s' t') (f : 𝒮 (W'.hom V')) :
    A.homSlice V' (scaleIdele E • x) ((W'.hom V').integrated v f) =
      (W.hom V').integrated (realSlice A V' x v)
        ((A.homSource V').zeroTerm ((W'.hom V').projReal f)) := by
  have h_real : realCoord (matrixToVec (scaleIdele E • x)) = fun p ↦ (matrixToVec x p.2).1 p.1 := by
    simp [funext_iff, realCoord, Units.smul_def, matrixToVec, scaleIdele_fst_apply_ne_zero]
  have h_fin : (fun i ↦ ((0, (matrixToVec (scaleIdele E • x) i).2) : 𝔸 E)) = 0 := by
    simp [funext_iff, Units.smul_def, matrixToVec, hx, Prod.mk_zero_zero]
  rw [homSlice_eq_adapted_slice, slice_integrated (isAdapted_homSource A V'), h_real,
    h_fin, mulVec_zero, slice_zero, realSlice]

/-- Let `A` and `X` be base-adapted splittings of `W'` over `W` and of `V'` over `V` along a single
hyperbolic plane, and let `B` be the isotropic line of `X`. Then in the model `β = true`, where the
line term is the slice along `A` followed by the zero term along `Hom(W, B)`, the real part of the
line term at the real point `a` sends `v` to the following. First take the slice `realSlice A V'` of
`v` along `A` at the real point `a • X.kAdelic`, where `X.kAdelic` is the frame of `B`. Then take
the zero term of this slice along `Hom(W, B)` (`realTargetZeroTerm`). -/
lemma lineTermReal_true_eq_realTargetZeroTerm [IsBaseAdapted A] [IsBaseAdapted X]
    (a : InfinitePlace E → ℂ) (v : PairFock E s' t') :
    lineTermReal A X true a v =
      realTargetZeroTerm W X (realSlice A V' (((a, 0) : 𝔸 E) • X.kAdelic) v) := by
  -- Compute the term at the real adele `x` of a datum with real part `v` in one step (`h_one`) and
  -- in two steps, first along `A` (`h_slice`) and then along `Hom(W, B)`. The finite parts agree.
  let D : (W'.hom V').Splitting (W.hom V) (LineIndex n r) := lineTermSplitting A X true
  have h_adapted : D.IsAdapted 1 (lineTermBasis W V) := isAdapted_lineTermSplitting A X true
  refine eq_of_integrated_zeroTerm_eq h_adapted fun f ↦ ?_
  let x : 𝔸 E := (scaleIdele E).val * (a, 0)
  -- At `a = 0` the line term is the composite of the two zero terms, and the term of `D` is its
  -- zero term.
  have h_zero (f : 𝒮 (W'.hom V')) :
      D.zeroTerm f = (X.homTarget W).zeroTerm ((A.homSource V').zeroTerm f) := by
    simpa [lineTerm, homSlice, slice_zero, matrixToVec_zero, ← Pi.zero_def] using
      congr_arg (· f) (lineTerm_eq_slice A X true 0).symm
  -- The zero term of a datum with the vacuum as real part has the vacuum as real part.
  have h_vac : (A.homSource V').zeroTerm ((W'.hom V').projReal f) =
      (W.hom V').projReal ((A.homSource V').zeroTerm ((W'.hom V').projReal f)) := by
    simpa [MixedModel.slice_vac] using zeroTerm_integrated (isAdapted_homSource A V') vacVector f
  have h_one : lineTerm A X true x ((W'.hom V').integrated v f) =
      (W.hom V).integrated (lineTermReal A X true a v) (D.zeroTerm ((W'.hom V').projReal f)) := by
    let y : LineIndex n r → 𝔸 E := 0 ⊕ᵥ matrixToVec (scalar Unit x)
    have h_coord : realCoord y = fun p ↦ a p.1 * p.2.isRight.toNat := by
      ext ⟨w, i | i⟩ <;> simp [y, x, realCoord, matrixToVec, scaleIdele_fst_apply_ne_zero]
    have h_fin : (fun i ↦ ((0, (y i).2) : 𝔸 E)) = 0 := by
      simp [funext_iff, y, x, matrixToVec]
    rw [lineTerm_eq_slice, slice_integrated h_adapted, lineTermReal, h_coord, h_fin,
      mulVec_zero, slice_zero]
  have h_slice : A.homSlice V' (x • X.kAdelic) ((W'.hom V').integrated v f) =
      (W.hom V').integrated (realSlice A V' (((a, 0) : 𝔸 E) • X.kAdelic) v)
        ((A.homSource V').zeroTerm ((W'.hom V').projReal f)) := by
    -- `x • X.kAdelic` is `scaleIdele E` times a point with finite part zero.
    rw [mul_smul]
    exact homSlice_integrated_of_real A (by simp) v f
  rw [← h_one, lineTerm, ite_eq_left rfl, ContinuousLinearMap.comp_apply, h_slice,
    zeroTerm_integrated (isAdapted_homTarget W X), ← h_vac, ← h_zero, realTargetZeroTerm]

open Norms.Elementwise in
/-- Let `X` split `V'` as `V` plus one hyperbolic plane, and let it be base-adapted
(`IsBaseAdapted X`): the adelic matrix with column blocks `lAdelic`, `kAdelic`, `iAdelic` has
orthonormal columns at every infinite place and integral entries at every finite place. Then every
Schwartz vector `v` for `(W, V)` is the zero term at the real places along `Hom(W, B)`
(`realTargetZeroTerm`) of some Schwartz vector `v'` for `(W, V')`. Here a Schwartz vector is an
element of the Fock space of `Hom(W, V)` (resp. `Hom(W, V')`) at the infinite places whose weighted
norms are all finite (`IsSchwartzVector`), and `B` is the isotropic line of `X`. -/
lemma exists_realTargetZeroTerm_eq [IsBaseAdapted X] {v : PairFock E s t}
    (hv : IsSchwartzVector v) :
    ∃ v' : PairFock E s t', IsSchwartzVector v' ∧ realTargetZeroTerm W X v' = v := by
  -- Prescribe the slices `β x • v` for a bump function `β` with `β 0 = 1`.
  let β : ContDiffBump (0 : InfinitePlace E × Unit × n → ℂ) := default
  obtain ⟨v', hv', h_slice⟩ : ∃ v' : PairFock E s t', IsSchwartzVector v' ∧
      ∀ x : InfinitePlace E × Unit × n → ℂ,
        (isAdapted_homTarget W X).mixedModel.slice x v' = (β x : ℂ) • realWeil 1 v :=
    (isAdapted_homTarget W X).mixedModel.exists_isSchwartzVector_slice_eq
      (τ := fun x ↦ β x) (Complex.ofRealCLM.contDiff.comp β.contDiff)
      (β.hasCompactSupport.comp_left Complex.ofReal_zero) (u := fun _ ↦ 1) contDiff_const hv
  have h_one : β 0 = 1 := β.one_of_mem_closedBall (Metric.mem_closedBall_self β.rIn_pos.le)
  refine ⟨v', hv', ?_⟩
  calc realTargetZeroTerm W X v' = (isAdapted_homTarget W X).mixedModel.slice 0 v' := by
        rw [realTargetZeroTerm]
    _ = (β 0 : ℂ) • realWeil 1 v := h_slice 0
    _ = v := by simp [h_one]

end TargetZeroTerm

/-!
## Real points of the target group on slices and zero terms

The slice along `A` of `h v` at `x` is `h` applied to the slice of `v` at `h⁻¹ x`, for real `h`
(`realSlice_realPairWeil`). A real point that preserves the line `B` acts on the zero term along
`Hom(W, B)` through a real point of `U(V)`, a phase and a power of the modulus
(`exists_realTargetZeroTerm_realPairWeil`). Both statements are the real parts of the adelic laws of
the mixed models.
-/

section RealSliceLaws

open Matrix NumberField Fintype Fock Space Splitting WeilData

omit [WeilData E] in
/-- Changing the weight on the target group multiplies the action by powers of determinants: for a
real point `h` of `U(V)`, `realPairWeil γ 0 (1, h)` is `∏ w, det (h w) ^ (γ w - δ w)` times
`realPairWeil δ 0 (1, h)`. -/
lemma realPairWeil_target_eq_smul (γ δ : InfinitePlace E → ℤ) (h : GInf E t) (v : PairFock E s t) :
    realPairWeil γ 0 (1, h) v =
      (∏ w : InfinitePlace E, (h w : Matrix r r ℂ).det ^ (γ w - δ w)) •
        realPairWeil δ 0 (1, h) v := by
  simp [realPairWeil_apply_apply, smul_smul, ← Finset.prod_mul_distrib, ← zpow_add₀,
    GeneralLinearGroup.det_ne_zero]

/-- A real point `h` of the target group `U(V')` moves the slice at `x` to the slice at `h⁻¹ x`:
the slice at `x` of `realPairWeil (γ + 1) 0 (1, h) v` is `realPairWeil γ 0 (1, h)` of the slice of
`v` at `h⁻¹ x`. -/
lemma realSlice_realPairWeil [IsBaseAdapted A] (γ : InfinitePlace E → ℤ) (h : GInf E t')
    (x : Matrix r' Unit (𝔸 E)) (v : PairFock E s' t') :
    realSlice A V' x (realPairWeil (fun w : InfinitePlace E ↦ γ w + 1) 0 (1, h) v) =
      realPairWeil γ 0 (1, h) (realSlice A V' (G.adeleMatrix ((h, 1) : G E t')⁻¹ * x) v) := by
  -- Slices see only the real part `x₀` of `x`. The adelic law, for characters of weights `1` and
  -- `0`, gives the case `γ = 0`; other weights differ by powers of `det h` on both sides.
  let x₀ : Matrix r' Unit (𝔸 E) := x.map fun a ↦ (a.1, 0)
  let y₀ : Matrix r' Unit (𝔸 E) := G.adeleMatrix ((h, 1) : G E t')⁻¹ * x₀
  have hy₀ (i : r') (j : Unit) : (y₀ i j).2 = 0 := by simp [y₀, x₀, mul_apply, Prod.snd_sum]
  -- `realSlice` reads only the real parts of the entries of its point
  have h_real : realSlice A V' x = realSlice A V' x₀ := rfl
  have h_slice : realSlice A V' (G.adeleMatrix ((h, 1) : G E t')⁻¹ * x) = realSlice A V' y₀ := by
    simp [realSlice, y₀, x₀, matrixToVec, mul_apply, Prod.fst_sum]
  have h_one : realSlice A V' x₀ (realPairWeil 1 0 (1, h) v) =
      realPairWeil 0 0 (1, h) (realSlice A V' y₀ v) := by
    refine eq_of_integrated_zeroTerm_eq (isAdapted_homSource A V') fun f ↦ ?_
    have h_move (F : 𝒮 (W'.hom V')) :
        A.homSlice V' (scaleIdele E • x₀) (pairWeil W' V' upsilonU1 1 (1, h, 1) F) =
          pairWeil W V' 1 1 (1, h, 1) (A.homSlice V' (scaleIdele E • y₀) F) := by
      simpa [y₀, Prod.mk_one_one] using A.homSlice_levi V' 1 1 1 1 (h, 1) (scaleIdele E • x₀) F
    -- `pairWeil_integrated_right` finds the weight of the trivial character as an instance.
    have h_weight : (1 : AutChar E).HasWeight 0 1 := AutChar.HasWeight.one
    rw [← homSlice_integrated_of_real A (by simp [x₀]),
      ← pairWeil_integrated_right (a := upsilonU1) (b := 1), h_move,
      homSlice_integrated_of_real A hy₀, pairWeil_integrated_right]
  rw [realPairWeil_target_eq_smul (fun w : InfinitePlace E ↦ γ w + 1) 1,
    realPairWeil_target_eq_smul γ 0, map_smul, h_real, h_slice, h_one]
  simp only [Pi.one_apply, Pi.zero_apply, add_sub_cancel_right, sub_zero]

/-- The component at the infinite place `w` of the vector that spans the isotropic line of `X`. -/
def lineVector (w : InfinitePlace E) : r' → ℂ := fun i : r' ↦ (X.kAdelic i ()).1 w

/-- If a real point `g` of `U(V')` acts on the frame of the line `B` by `m`, its block
`X.iCoord * g * X.iAdelic` on `V` (where `X.iCoord * X.iAdelic = 1`) is a real point of `U(V)`. -/
lemma exists_real_block_of_actsOnFrame {g : GInf E t'} {m : Matrix Unit Unit (𝔸 E)}
    (h_frame : X.ActsOnFrame (g, 1) m) :
    ∃ h : GInf E t,
      X.iCoord * (G.adeleMatrix ((g, 1) : G E t') * X.iAdelic) = G.adeleMatrix
        ((h, 1) : G E t) := by
  -- The block comes from the Levi decomposition of the stabiliser of `B`.
  obtain ⟨⟨h, k⟩, h_block⟩ :
      ∃ g₀ : G E t, g₀.adeleMatrix = X.iCoord * (G.adeleMatrix ((g, 1) : G E t') * X.iAdelic) := by
    obtain ⟨-, -, -, g₀, -, -, h_block⟩ := X.exists_eq_radicalElement_mul_levi h_frame
    exact ⟨g₀, h_block⟩
  -- The finite part of the block is `X.iCoord * X.iAdelic = 1`.
  obtain rfl : k = 1 := by
    have h_coord : X.iCoord * X.iAdelic = 1 := by simp [X.coord_mul_frame]
    refine Gf.val_ext _ _ (Units.ext (Matrix.ext fun i j ↦ ?_))
    have h_entry : (G.adeleMatrix ((h, k) : G E t) i j).2 = ((X.iCoord * X.iAdelic) i j).2 := by
      simp [h_block, mul_apply, Prod.snd_sum, G.adeleMatrix_snd, one_apply]
    simpa [h_coord, G.adeleMatrix_snd, Gf.coe_one, one_apply, apply_ite Prod.snd] using h_entry
  exact ⟨h, h_block.symm⟩

/-- Let `card n` be even, and let the real point `g` of `U(V')` multiply the vector `lineVector X w`
spanning the line `B` at each infinite place `w` by a number `a w ≠ 0`. Then there is a real point
`h` of `U(V)` such that, under the zero term along `Hom(W, B)`, `g` with the weight
`targetWeight n μ` (at `w`: `card n / 2 - μ w`) acts as `h` with the same weight, times the phase
`∏ w, (a w / |a w|) ^ (-2 μ w)` and the power `card n / 2` of the idele norm of `a`. -/
lemma exists_realTargetZeroTerm_realPairWeil [IsBaseAdapted X] (hn : 2 ∣ card n)
    (μ : InfinitePlace E → ℤ) {g : GInf E t'} {a : (InfinitePlace E → ℂ)ˣ}
    (hg : ∀ w : InfinitePlace E,
      (g w : Matrix r' r' ℂ) *ᵥ lineVector X w = a.val w • lineVector X w) :
    ∃ h : GInf E t, ∀ v : PairFock E s t',
      realTargetZeroTerm W X (realPairWeil (targetWeight n μ) 0 (1, g) v) =
        ((∏ w : InfinitePlace E, (a.val w / ‖a.val w‖) ^ (-2 * μ w)) *
            √(ideleAbs (realIdele a)) ^ card n) •
          realPairWeil (targetWeight n μ) 0 (1, h) (realTargetZeroTerm W X v) := by
  -- The point `(g, 1)` acts on the frame of `B` by the idele `(a, 1)`. Its block on `V` is a real
  -- point `h`, and `det g = (a / star a) det h`. The adelic law for the zero term gives the claim
  -- in the weight `card n / 2`; the determinants give the phase for general `μ`.
  let m : GL Unit (𝔸 E) := GeneralLinearGroup.scalar Unit (realIdele a)
  have h_frame : X.ActsOnFrame (g, 1) m.val := by
    refine Matrix.ext fun i j ↦ Prod.ext (funext fun w ↦ ?_) ?_
    · simpa [m, mul_apply, Prod.fst_sum, G.adeleMatrix_fst, mulVec, dotProduct, lineVector,
        mul_comm] using congrFun (hg w) i
    · simp [m, mul_apply, Prod.snd_sum, G.adeleMatrix_snd, one_apply]
  obtain ⟨h, h_block⟩ : ∃ h : GInf E t,
      X.iCoord * (G.adeleMatrix ((g, 1) : G E t') * X.iAdelic) = G.adeleMatrix ((h, 1) : G E t) :=
    exists_real_block_of_actsOnFrame X h_frame
  let u (w : InfinitePlace E) : ℂ := a.val w / ‖a.val w‖
  have h_det (w : InfinitePlace E) :
      (g w : Matrix r' r' ℂ).det = u w ^ (2 : ℤ) * (h w : Matrix r r ℂ).det := by
    have h_adelic : G.det ((g, 1) : G E t') = divStar m.det * G.det ((h, 1) : G E t) :=
      X.det_eq_divStar_mul (g, 1) (h, 1) m h_frame h_block
    have h_div : (divStar m.det : 𝔸 E).1 w = u w ^ (2 : ℤ) := by
      have h_inv : a⁻¹.val w = (a.val w)⁻¹ := eq_inv_of_mul_eq_one_left (congrFun a.inv_mul w)
      have h_quotient : (divStar m.det : 𝔸 E).1 w = a.val w / starRingEnd ℂ (a.val w) := by
        simp [coe_divStar, m, div_eq_mul_inv, ← map_inv]
      rw [h_quotient, zpow_two, div_mul_div_comm, ← sq (‖a.val w‖ : ℂ), ← Complex.mul_conj',
        mul_div_mul_left _ _ (piUnits_val_apply_ne_zero a w)]
    calc (g w : Matrix r' r' ℂ).det = (G.det ((g, 1) : G E t') : 𝔸 E).1 w := by rw [det_fst]
      _ = (divStar m.det : 𝔸 E).1 w * (G.det ((h, 1) : G E t) : 𝔸 E).1 w := by
        rw [h_adelic, Submonoid.coe_mul, Prod.fst_mul, Pi.mul_apply]
      _ = u w ^ (2 : ℤ) * (h w : Matrix r r ℂ).det := by rw [h_div, det_fst]
  have h_phase (w : InfinitePlace E) : (g w : Matrix r' r' ℂ).det ^ (-μ w) =
      u w ^ (-2 * μ w) * (h w : Matrix r r ℂ).det ^ (-μ w) := by
    rw [h_det, mul_zpow, ← _root_.zpow_mul, mul_neg, neg_mul]
  let c : ℂ := √(ideleAbs (realIdele a)) ^ card n
  have h_zero (v : PairFock E s t') :
      realTargetZeroTerm W X
          (realPairWeil (fun _ : InfinitePlace E ↦ (card n / 2 : ℕ)) 0 (1, g) v) =
        c • realPairWeil (fun _ : InfinitePlace E ↦ (card n / 2 : ℕ)) 0 (1, h)
          (realTargetZeroTerm W X v) := by
    refine eq_of_integrated_zeroTerm_eq (isAdapted_homTarget W X) fun f ↦ ?_
    let χ : AutChar E := upsilonU1 ^ (card n / 2)
    have hχ : χ.spaceChar (card n) = 1 := by
      simpa [rankTwist] using spaceChar_rankTwist (ν := (1 : AutChar E)) hn
    -- the adelic law of the zero term for `(g, 1)`; the character in its scalar factor is trivial
    have h_move (F : 𝒮 (W.hom V')) :
        (X.homTarget W).zeroTerm (pairWeil W V' χ upsilonU1 (1, g, 1) F) =
          c • pairWeil W V χ 1 (1, h, 1) ((X.homTarget W).zeroTerm F) := by
      simpa [hχ, m, c] using X.homTarget_zeroTerm_pairWeil W χ 1 (g, 1) (h, 1) m h_frame h_block 1 F
    rw [realTargetZeroTerm, ← zeroTerm_integrated,
      ← pairWeil_integrated_right (a := χ) (b := upsilonU1), h_move,
      zeroTerm_integrated (isAdapted_homTarget W X), pairWeil_integrated_right, map_smul,
      _root_.smul_apply]
  refine ⟨h, fun v ↦ ?_⟩
  rw [realPairWeil_target_eq_smul (targetWeight n μ) fun _ : InfinitePlace E ↦ (card n / 2 : ℕ),
    map_smul, h_zero,
    realPairWeil_target_eq_smul (targetWeight n μ) fun _ : InfinitePlace E ↦ (card n / 2 : ℕ),
    smul_smul, smul_smul, mul_right_comm, ← Finset.prod_mul_distrib]
  simp only [targetWeight, add_sub_cancel_left, Pi.neg_apply, h_phase, u, c]

end RealSliceLaws

end New.Exchange

end
