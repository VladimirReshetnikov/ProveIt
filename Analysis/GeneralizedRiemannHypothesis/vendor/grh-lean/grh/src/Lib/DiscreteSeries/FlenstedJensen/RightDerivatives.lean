import Lib.DiscreteSeries.Haar.TotalMass
import Lib.DiscreteSeries.Rigidity.RepresentationsAndCasimirs
import Lib.General.Analysis.HolomorphicIntegrals

/-!
# Right derivatives and bump convolution for smooth functions on U(p,q)

The file develops differential calculus on `U(p,q) = New.USign ε = U(diag ε)`. A smooth function on
the group is by definition the restriction of a smooth function on the matrix space, so no manifold
structure is needed. Continuous functions are convolved with compactly supported smooth functions
(bumps).

## Main definitions and results

* `New.smoothMatrixFunctions`, `New.SmoothU`: smooth `E`-valued functions on matrices, and their
  restrictions.
* `New.rightDerivMatrix`, `New.rightDeriv`: `gl_n(ℂ)` acts on them by right derivatives. An element
  `Y` of the real Lie algebra `New.unitaryLie J` acts by `f ↦ (x ↦ df_x(x Y))`, and the action
  extends `ℂ`-linearly through the splitting `X = Y₁ + i Y₂` of `New.eq_unitaryLiePart_add_I_smul`.
* `New.DiscreteSeries.Bumps`, `New.DiscreteSeries.bumpDeriv`: the smooth compactly supported
  functions, and the action on them of `gl n` by right derivatives.
* `New.DiscreteSeries.smear`: for continuous `F`, the linear map `α ↦ (g ↦ ∫ y, α y⁻¹ • F (g * y))`.
* `New.DiscreteSeries.hasDerivAt_smear`, `New.DiscreteSeries.rightDeriv_smear`: a right derivative
  of the convolution falls on `α`.

Notions from other files:
* `New.USign`: for a vector of signs `ε`, the unitary group `U J` of the diagonal matrix
  `J = diag ε`, which is `New.signMatrix ε`. For `g` in the group, `g.val.val` is its matrix.
* `New.unitaryLie`: the Lie algebra of `U J`, the real vector space of complex matrices `X` with
  `Xᴴ * J + J * X = 0`.
* `New.expU`: for `X` in `New.unitaryLie J`, the matrix exponential of `X` as an element of `U J`.
* `New.GlModule`: a `gl_n(ℂ)`-module structure on a complex vector space `M`, that is, a linear map
  from `n × n` matrices to endomorphisms of `M` that respects commutators.

## Relation to the literature

They are used for the function of Flensted-Jensen, the coefficient of the lowest K-type of a
discrete series (see `Lib.DiscreteSeries.FlenstedJensen.PsiKTypes`), and for two known results:
Schur orthogonality, and the fact that coefficients of integrable discrete series are cusp forms
(see `Lib.DiscreteSeries.CuspKernel`).
-/

noncomputable section

/-! ## Right derivatives of smooth functions as a gl_n-module -/

namespace New

open Complex Matrix NormedSpace Topology U Norms.L2Operator VectorField ContDiff Ring Module

section

/-! ### Smooth functions and the exponential map -/

section SmoothMatrixFunctions

variable {n : Type} [Fintype n] [DecidableEq n] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (n E) in
/-- The space of real-smooth functions from complex `n × n` matrices to `E`. -/
def smoothMatrixFunctions : Submodule ℂ (Matrix n n ℂ → E) where
  carrier := {f : Matrix n n ℂ → E | ContDiff ℝ ∞ f}
  add_mem' := ContDiff.add (n := ∞)
  zero_mem' := contDiff_const (n := ∞)
  smul_mem' c _ := ContDiff.const_smul (n := ∞) c

theorem smoothMatrixFunctions.differentiable_coe (f : smoothMatrixFunctions n E) :
    Differentiable ℝ f.val :=
  ContDiff.differentiable (n := ∞) f.property nofun

end SmoothMatrixFunctions

open smoothMatrixFunctions IsHermitianInvolution ContinuousLinearMap

section Exponential

variable {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ}
@[simp]
theorem expU_zero : expU (0 : unitaryLie J) = (1 : U J) := by ext; simp

@[fun_prop]
theorem U.continuous_mat : Continuous fun g : U J ↦ (g.val.val : Matrix n n ℂ) := by fun_prop

@[fun_prop]
theorem continuous_expU [IsHermitianInvolution J] : Continuous (expU (J := J)) := by
  -- The topology of `U J` is induced from the matrices, where `exp` is continuous.
  let : NormedAlgebra ℚ (Matrix n n ℂ) := .restrictScalars ℚ ℂ _
  exact continuous_U_iff_matrix.2 (exp_continuous.comp continuous_subtype_val)

/-- For `g` in the unitary group `U J` and `Y` in its Lie algebra, the matrix of the curve
`s ↦ g exp(s Y)` has derivative `g exp(t Y) Y` at `t`. -/
theorem hasDerivAt_expU (Y : unitaryLie J) (g : U J) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (g * expU (s • Y)).val.val) ((g * expU (t • Y)).val.val * Y) t := by
  simpa [mul_assoc] using (hasDerivAt_exp_smul_const Y.val t).const_mul g.val.val

end Exponential

attribute [local instance] LieRing.ofAssociativeRing

section Action

variable {n : Type} [Fintype n] [DecidableEq n] (ε : n → ℤˣ)
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The restriction to the group `U(diag ε)` of a smooth function on all matrices. -/
abbrev smoothMatrixFunctions.restrictU : smoothMatrixFunctions n E →ₗ[ℂ] USign ε → E :=
  LinearMap.funLeft ℂ E (fun g : USign ε ↦ g.val.val) ∘ₗ (smoothMatrixFunctions n E).subtype

/-- Smooth functions on `U(diag ε)`: the restrictions to the group of the smooth functions on all
matrices. -/
abbrev SmoothU : Submodule ℂ (USign ε → E) := LinearMap.range (restrictU ε E)

/-! ### The action induced on the range of a linear map -/

section Range

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {N : Type*} [AddCommGroup N] [Module ℂ N]

/-- The action induced on the range of a linear map `ι` whose kernel is stable under the action,
through `M ⧸ ker ι ≃ range ι`: `X` sends `ι x` to `ι (X x)` (see `GlModule.onRange_apply`). -/
@[irreducible] def GlModule.onRange (ρ : GlModule n M) (ι : M →ₗ[ℂ] N)
    (h_ker : ∀ X : Matrix n n ℂ, ι.ker ≤ ι.ker.comap (ρ X)) :
    GlModule n ι.range where
  ρ :=
    { toFun X := ι.quotKerEquivRange.conj (ι.ker.mapQ ι.ker (ρ X) (h_ker X))
      map_add' X Y := by
        ext y
        obtain ⟨x, rfl⟩ := ι.surjective_rangeRestrict y
        simp [LinearMap.codRestrict, ι.quotKerEquivRange_symm_apply_image]
      map_smul' c X := by
        ext y
        obtain ⟨x, rfl⟩ := ι.surjective_rangeRestrict y
        simp [LinearMap.codRestrict, ι.quotKerEquivRange_symm_apply_image] }
  map_bracket X Y := by
    ext y
    obtain ⟨x, rfl⟩ := ι.surjective_rangeRestrict y
    simp [LinearMap.codRestrict, ι.quotKerEquivRange_symm_apply_image, map_bracket]

omit [DecidableEq n] in
/-- The action induced by `ρ` on the range of `ι` sends `ι x` to `ι (X x)`. -/
theorem GlModule.onRange_apply (ρ : GlModule n M) (ι : M →ₗ[ℂ] N)
    (h_ker : ∀ X : Matrix n n ℂ, ι.ker ≤ ι.ker.comap (ρ X)) (X : Matrix n n ℂ) (x : M) :
    ρ.onRange ι h_ker X (ι.rangeRestrict x) = ι.rangeRestrict (ρ X x) := by
  ext
  simp [onRange, LinearMap.codRestrict, ι.quotKerEquivRange_symm_apply_image]

omit [DecidableEq n] in
/-- If the kernel of a linear map `ι` on a `gl_n`-module `ρ` is stable under the action, the action
descends to the range of `ι`: there is a `gl_n`-module structure `σ` on the range for which `ι`
commutes with the action of every matrix. -/
theorem GlModule.exists_action_on_range (ρ : GlModule n M) (ι : M →ₗ[ℂ] N)
    (h_ker : ∀ (X : Matrix n n ℂ) (x : M), ι x = 0 → ι (ρ X x) = 0) :
    ∃ σ : GlModule n ι.range, ∀ (X : Matrix n n ℂ) (x : M),
      σ X (ι.rangeRestrict x) = ι.rangeRestrict (ρ X x) :=
  ⟨ρ.onRange ι h_ker, ρ.onRange_apply ι h_ker⟩

end Range

/-! ### The splitting of `gl_n(ℂ)` and derivatives along linear vector fields -/

/-- The component `(X - J⁻¹ Xᴴ J) / 2`, with `J = diag ε`, of a complex matrix `X` in the real Lie
algebra `𝔲` of `U(diag ε)`, for the splitting `gl_n(ℂ) = 𝔲 ⊕ i𝔲` (see
`eq_unitaryLiePart_add_I_smul`). -/
def unitaryLiePart (X : Matrix n n ℂ) : unitaryLie (signMatrix ε) :=
  ⟨(2⁻¹ : ℝ) • (X - (signMatrix ε)⁻¹ * Xᴴ * signMatrix ε), by
    simp [unitaryLie, isHermitian.inv.eq, isHermitian.eq, mul_assoc, sub_mul, det_ne_zero, mul_sub]⟩

/-- Every complex matrix `X` is `Y₁ + i Y₂`, where `Y₁ = unitaryLiePart ε X` and
`Y₂ = unitaryLiePart ε (-i X)` are the components of `X` and `-i X` in the real Lie algebra of
`U(diag ε)`. -/
theorem eq_unitaryLiePart_add_I_smul (X : Matrix n n ℂ) :
    X = unitaryLiePart ε X + I • (unitaryLiePart ε (-I • X) : Matrix n n ℂ) := by
  ext i j
  suffices h : ∀ a b : ℂ, a = 2⁻¹ * (a - b) + I * (2⁻¹ * (-(I * a) - I * b)) by
    simpa [unitaryLiePart] using h (X i j) (((signMatrix ε)⁻¹ * Xᴴ * signMatrix ε) i j)
  intro a b
  linear_combination 2⁻¹ * (a + b) * I_sq

/-- The derivative along the vector field `x ↦ x Y` on matrices: it sends a smooth function `f` to
`x ↦ df_x(x Y)`. -/
def smoothMatrixFunctions.mulRightDeriv (Y : Matrix n n ℂ) : End ℂ (smoothMatrixFunctions n E) where
  toFun f :=
    ⟨fun x ↦ fderiv ℝ f.val x ((mul ℝ (Matrix n n ℂ)).flip Y x),
      (contDiff_infty_iff_fderiv.1 f.property).right.clm_apply
        ((mul ℝ (Matrix n n ℂ)).flip Y).contDiff⟩
  map_add' f g := by
    ext x
    simp [fderiv_add (differentiable_coe f x) (differentiable_coe g x)]
  map_smul' c f := by
    ext x
    simp [fderiv_const_smul (differentiable_coe f x)]

/-! ### The action of `gl_n(ℂ)` by right derivatives -/

/-- Right derivatives on smooth functions of a matrix. For `X = Y₁ + i Y₂` with
`Y₁ = unitaryLiePart ε X` and `Y₂ = unitaryLiePart ε (-i X)` in the real Lie algebra of
`U(diag ε)`, `X` sends `f` to `x ↦ df_x(x Y₁) + i df_x(x Y₂)`. -/
def rightDerivMatrix : GlModule n (smoothMatrixFunctions n E) where
  ρ :=
    { toFun X :=
        mulRightDeriv (n := n) E (unitaryLiePart ε X) +
          I • mulRightDeriv (n := n) E (unitaryLiePart ε (-I • X))
      map_add' X Y := by
        ext f
        simp [mulRightDeriv, unitaryLiePart, smul_sub, mul_add, add_mul, mul_assoc]
        module
      map_smul' := fun ⟨a, b⟩ X ↦ by
        -- Write the scalar as `a + b * I` and expand.
        ext f
        simp [mulRightDeriv, unitaryLiePart, mk_eq_add_mul_I, add_smul, smul_sub, mul_smul,
          smul_smul I, @smul_comm ℂ, mul_add, add_mul, mul_assoc]
        module }
  map_bracket X Y := by
    -- Fold the commutator of the two operators into their Lie bracket.
    refine .trans ?_ (lie_def ..)
    ext f
    -- The commutator of two derivatives of a smooth `f` is its derivative along the bracket of the
    -- fields; what is left is an identity between the components of `X` and `Y`.
    -- `flip_apply` is removed from the simp set so that the fields keep their linear form, and
    -- `decide` proves the side condition on the degree of smoothness.
    simp +decide [mulRightDeriv, lieBracket, -flip_apply,
      ← fderiv_apply_lieBracket (contDiffAt (n := ∞) f.property)]
    simp [unitaryLiePart, smul_sub, smul_smul I, @smul_comm ℂ, mul_sub, sub_mul, mul_assoc, mul_add,
      add_mul, det_ne_zero]
    module

/-- The right derivative on matrices of a smooth function `f` along `X = Y₁ + i Y₂`, with
`Y₁ = unitaryLiePart ε X` and `Y₂ = unitaryLiePart ε (-i X)`, is `df_x(x Y₁) + i df_x(x Y₂)`
at `x`. -/
theorem rightDerivMatrix_apply_apply (X : Matrix n n ℂ) (f : smoothMatrixFunctions n E)
    (x : Matrix n n ℂ) :
    (rightDerivMatrix ε E X f).val x =
      fderiv ℝ f.val x (x * unitaryLiePart ε X) +
        I • fderiv ℝ f.val x (x * unitaryLiePart ε (-I • X)) :=
  rfl

/-- If a smooth function on matrices vanishes on the group `U(diag ε)`, then so does its right
derivative along every complex matrix `X`. -/
theorem restrictU_rightDerivMatrix_eq_zero (X : Matrix n n ℂ) (f : smoothMatrixFunctions n E)
    (hf : restrictU ε E f = 0) : restrictU ε E (rightDerivMatrix ε E X f) = 0 := by
  funext g
  -- For `Y` in the real form, differentiate the zero function `t ↦ f (g * expU (t • Y))` at `0`.
  have h_real (Y : unitaryLie (signMatrix ε)) : fderiv ℝ f.val g.val.val (g.val.val * Y) = 0 := by
    have h_chain : HasDerivAt (fun t : ℝ ↦ f.val (g * expU (t • Y)).val.val)
        (fderiv ℝ f.val g.val.val (g.val.val * Y)) 0 := by
      simpa [Function.comp_def] using
        (differentiable_coe f _).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_expU Y g 0)
    -- the composite is the zero function
    exact h_chain.unique <|
      (hasDerivAt_const 0 0).congr_of_eventuallyEq (.of_forall fun _ ↦ congrFun hf _)
  simp [rightDerivMatrix_apply_apply, h_real]

/-- The `gl_n(ℂ)`-module of smooth functions on `U(diag ε)` under complexified right derivatives:
the action that `rightDerivMatrix` induces on restrictions to the group, well defined by
`restrictU_rightDerivMatrix_eq_zero`. See `rightDeriv_restrictU` and `hasDerivAt_curve`. -/
def rightDeriv : GlModule n (SmoothU ε E) :=
  (rightDerivMatrix ε E).onRange (restrictU ε E) (restrictU_rightDerivMatrix_eq_zero ε E)

/-- The right derivative along `X` of the restriction to the group of a smooth function `F` on
matrices is the restriction of `rightDerivMatrix ε E X F`, its right derivative on matrices. -/
theorem rightDeriv_restrictU (X : Matrix n n ℂ) (F : smoothMatrixFunctions n E) :
    rightDeriv ε E X ((restrictU ε E).rangeRestrict F) =
      (restrictU ε E).rangeRestrict (rightDerivMatrix ε E X F) :=
  (rightDerivMatrix ε E).onRange_apply (restrictU ε E) (restrictU_rightDerivMatrix_eq_zero ε E) X F

end Action

section Properties

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

@[fun_prop] theorem SmoothU.continuous (f : SmoothU ε E) : Continuous f.val := by
  obtain ⟨F, rfl⟩ := (restrictU ε E).surjective_rangeRestrict f
  exact (differentiable_coe F).continuous.comp continuous_mat

/-- Chain rule along a curve `γ` in the group `USign ε = U(diag ε)`: if the matrix of `γ` satisfies
`γ'(t) = γ(t) X`, then, for a smooth function `f` on the group, the derivative of `f ∘ γ` at `t` is
the right derivative `rightDeriv ε E X f` of `f` along `X` at `γ t`. -/
theorem hasDerivAt_curve (f : SmoothU ε E) {γ : ℝ → USign ε} {t : ℝ} {X : Matrix n n ℂ}
    (hγ : HasDerivAt (fun s : ℝ ↦ (γ s).val.val) ((γ t).val.val * X) t) :
    HasDerivAt (fun s : ℝ ↦ f.val (γ s)) ((rightDeriv ε E X f).val (γ t)) t := by
  obtain ⟨F, rfl⟩ := (restrictU ε E).surjective_rangeRestrict f
  -- The curve stays in the group, so its logarithmic derivative `X` lies in the real Lie algebra.
  have h_conj : Xᴴ * signMatrix ε = -(signMatrix ε * X) := by
    simpa [logDerivU, hγ.deriv, ← mul_assoc, mem_U.1, (isHermitian (J := signMatrix ε)).eq] using
      conjTranspose_logDerivU hγ.differentiableAt 1
  have h_re : (unitaryLiePart ε X : Matrix n n ℂ) = X := by
    simp [unitaryLiePart, mul_assoc, h_conj, det_ne_zero, ← two_smul ℝ]
  have h_im : (unitaryLiePart ε (-(I • X)) : Matrix n n ℂ) = 0 := by
    simp [unitaryLiePart, mul_assoc, h_conj, det_ne_zero]
  -- So the right derivative of `F` at `γ t` is `dF (γ t X)`, and the chain rule applies.
  simpa [rightDeriv_restrictU, rightDerivMatrix_apply_apply, h_re, h_im, Function.comp_def] using
    (differentiable_coe F _).hasFDerivAt.comp_hasDerivAt t hγ

/-- For a smooth function `f` on the group `USign ε = U(diag ε)`, a point `g` of the group and `Y`
in its real Lie algebra, the derivative of `s ↦ f (g exp(s Y))` at `t` is the right derivative
`rightDeriv ε E Y f` of `f` along `Y` at `g exp(t Y)`. -/
theorem hasDerivAt_rightDeriv_expU (f : SmoothU ε E) (g : USign ε)
    (Y : unitaryLie (signMatrix ε)) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ f.val (g * expU (s • Y)))
      ((rightDeriv ε E Y f).val (g * expU (t • Y))) t :=
  hasDerivAt_curve f (hasDerivAt_expU Y g t)

/-- If a smooth function `f` on the group `USign ε = U(diag ε)` is the restriction of a function `F`
on matrices with complex derivative `D` at `g`, then the right derivative `rightDeriv ε E X f` of
`f` along a complex matrix `X` has the value `D (g X)` at `g`. -/
theorem rightDeriv_apply_eq_of_hasFDerivAt {f : SmoothU ε E} {F : Matrix n n ℂ → E} {g : USign ε}
    {D : Matrix n n ℂ →L[ℂ] E} (hF : HasFDerivAt F D g.val.val)
    (h_restrict : ∀ x : USign ε, F x.val.val = f.val x) (X : Matrix n n ℂ) :
    (rightDeriv ε E X f).val g = D (g.val.val * X) := by
  -- For `Y` in the real form, both sides are the derivative of `t ↦ F (g * expU (t • Y))` at `0`.
  have h_real (Y : unitaryLie (signMatrix ε)) : (rightDeriv ε E Y f).val g = D (g.val.val * Y) := by
    have h_chain : HasDerivAt (fun s : ℝ ↦ f.val (g * expU (s • Y))) (D (g.val.val * Y)) 0 := by
      simpa [Function.comp_def, ← h_restrict] using
        (hF.restrictScalars ℝ).comp_hasDerivAt_of_eq 0 (hasDerivAt_expU Y g 0) (by simp)
    simpa using (hasDerivAt_rightDeriv_expU f g Y 0).unique h_chain
  -- Both sides are complex linear in `X`.
  rw [eq_unitaryLiePart_add_I_smul ε X]
  simp [h_real, mul_add]

/-- Right derivatives of smooth functions on the group `USign ε = U(diag ε)` are local and commute
with continuous linear forms `L`: if `f' = L ∘ f` near `g`, then `X f' = L ∘ X f` near `g`, where
`X f = rightDeriv ε E X f` is the right derivative along the complex matrix `X`. -/
theorem rightDeriv_comp_clm {X : Matrix n n ℂ} {f : SmoothU ε E} {f' : SmoothU ε ℂ} {g : USign ε}
    (L : E →L[ℂ] ℂ) (h_germ : f'.val =ᶠ[𝓝 g] L ∘ f.val) :
    (rightDeriv ε ℂ X f').val =ᶠ[𝓝 g] L ∘ (rightDeriv ε E X f).val := by
  filter_upwards [h_germ.eventually_nhds] with y hy
  -- For `Y` in the real form, differentiate `f' = L ∘ f` along `t ↦ y * expU (t • Y)` at `0`.
  have h_real (Y : unitaryLie (signMatrix ε)) :
      (rightDeriv ε ℂ Y f').val y = L ((rightDeriv ε E Y f).val y) := by
    have h_tendsto : Filter.Tendsto (fun t : ℝ ↦ y * expU (t • Y)) (𝓝 0) (𝓝 y) :=
      Continuous.tendsto' (by fun_prop) 0 y (by simp)
    have h_deriv : HasDerivAt (fun t : ℝ ↦ f'.val (y * expU (t • Y)))
        (L ((rightDeriv ε E Y f).val (y * expU ((0 : ℝ) • Y)))) 0 :=
      ((hasDerivAt_rightDeriv_expU f y Y 0).map_clm L).congr_of_eventuallyEq
        (h_tendsto.eventually hy)
    simpa using (hasDerivAt_rightDeriv_expU f' y Y 0).unique h_deriv
  -- Both sides are complex linear in `X`.
  rw [eq_unitaryLiePart_add_I_smul ε X]
  simp [h_real]

end Properties

end

end New

/-! ## Convolution with bump functions and its right derivatives -/

section BumpConvolution

open MeasureTheory ContinuousLinearMap Set Matrix Norms.L2Operator

namespace New.DiscreteSeries

variable {n : Type} [Fintype n] [DecidableEq n] (ε : n → ℤˣ) {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℂ E]

/-- The smooth complex functions with compact support on `U(diag ε)`. -/
abbrev Bumps : Submodule ℂ (SmoothU ε ℂ) where
  carrier := {β : ↥(SmoothU ε ℂ) | HasCompactSupport β.val}
  add_mem' := HasCompactSupport.add
  zero_mem' := HasCompactSupport.zero
  smul_mem' _ _ := HasCompactSupport.smul_left

variable {ε}

/-- The `gl n`-module of smooth compactly supported functions: the restriction of
`rightDeriv ε ℂ`. A right derivative vanishes near every point outside the support. -/
def bumpDeriv : GlModule n ↥(Bumps ε) :=
  (rightDeriv ε ℂ).restrictTo (Bumps ε) fun _ f hf ↦
    -- Near a point outside the support `f` agrees with the zero functional applied to `f`, so
    -- `rightDeriv_comp_clm` shows that its derivatives vanish there.
    HasCompactSupport.intro hf fun _ hg ↦
      (rightDeriv_comp_clm (f := f) 0 (notMem_tsupport_iff_eventuallyEq.1 hg)).eq_of_nhds

open scoped Pointwise NNReal in
/-- Let `A` be a smooth extension of a bump function `α` to all matrices, let `N` be a set in
`U(diag ε)` and let `K = tsupport α * N⁻¹`. If `A` is `L`-Lipschitz on the matrices of `K * N`,
then, for `g` and `g₀` in `N`, the function `y ↦ α (y⁻¹ * g) • F y - α (y⁻¹ * g₀) • F y` is
bounded by `‖F y‖ * L * ‖y⁻¹‖ * ‖g - g₀‖` on `K⁻¹` and vanishes elsewhere. -/
theorem norm_bump_smul_sub_le_indicator (F : USign ε → E) (α : Bumps ε)
    {A : smoothMatrixFunctions n ℂ}
    (hA : smoothMatrixFunctions.restrictU ε ℂ A = α.val.val) {N : Set (USign ε)} {L : ℝ≥0}
    (hL : LipschitzOnWith L A.val
      ((fun x : USign ε ↦ x.val.val) '' (tsupport α.val.val * N⁻¹ * N)))
    (y : USign ε) {g g₀ : USign ε} (hg : g ∈ N) (hg₀ : g₀ ∈ N) :
    ‖α.val.val (y⁻¹ * g) • F y - α.val.val (y⁻¹ * g₀) • F y‖ ≤
      (tsupport α.val.val * N⁻¹)⁻¹.indicator (fun z : USign ε ↦ ‖F z‖ * L * ‖z⁻¹.val.val‖) y *
        ‖g.val.val - g₀.val.val‖ := by
  by_cases hy : y ∈ (tsupport α.val.val * N⁻¹)⁻¹
  · have hα (x : USign ε) : α.val.val x = A.val x.val.val := (congrFun hA x).symm
    have h_mem {x : USign ε} (hx : x ∈ N) : (y⁻¹ * x).val.val ∈
        (fun z : USign ε ↦ z.val.val) '' (tsupport α.val.val * N⁻¹ * N) :=
      mem_image_of_mem _ (mul_mem_mul hy hx)
    calc
      _ = ‖A.val (y⁻¹ * g).val.val - A.val (y⁻¹ * g₀).val.val‖ * ‖F y‖ := by
        rw [← sub_smul, norm_smul, hα, hα]
      _ ≤ L * ‖y⁻¹.val.val * (g.val.val - g₀.val.val)‖ * ‖F y‖ := by
          grw [hL.norm_sub_le (h_mem hg) (h_mem hg₀)]
          simp [mul_sub]
      _ ≤ L * (‖y⁻¹.val.val‖ * ‖g.val.val - g₀.val.val‖) * ‖F y‖ := by grw [norm_mul_le]
      _ = _ := by rw [indicator_of_mem hy]; ring
  · have h_zero {x : USign ε} (hx : x ∈ N) : α.val.val (y⁻¹ * x) = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun h_supp ↦ hy ?_
      simpa only [mem_inv, mul_inv_cancel_right] using mul_mem_mul h_supp (inv_mem_inv.2 hx)
    rw [indicator_of_notMem hy]
    simp [h_zero hg, h_zero hg₀]

/-- For continuous `F` and a smooth compactly supported `α`, the function `y ↦ α y⁻¹ • F y` on
`U(diag ε)` is integrable for the invariant measure. -/
theorem integrable_bump_inv_smul (F : USign ε → E) (α : Bumps ε)
    (hF : Continuous F := by fun_prop) :
    Integrable fun y : USign ε ↦ α.val.val y⁻¹ • F y :=
  (α.prop.comp_homeomorph (.inv _)).smul_right.integrable

/-- Convolution with the continuous function `F`: the linear map that sends `α` to the function
`g ↦ ∫ y, α y⁻¹ • F (g * y)`. -/
@[simps]
def smear (F : USign ε → E) (hF : Continuous F := by fun_prop) : Bumps ε →ₗ[ℂ] USign ε → E where
  toFun α g := ∫ y : USign ε, α.val.val y⁻¹ • F (g * y)
  map_add' := by
    simp [add_smul, integral_add, funext_iff,
      fun g β ↦ integrable_bump_inv_smul (fun y ↦ F (g * y)) β]
  map_smul' := by simp [mul_smul, integral_smul, funext_iff]

/-- By invariance of the measure, the convolution `smear F` of a bump function `β` at `g` is
`∫ y, β (y⁻¹ * g) • F y`, in which the variable `g` sits in `β`. -/
theorem smear_apply_eq_integral_inv_mul (F : USign ε → E) (hF : Continuous F) (β : Bumps ε)
    (g : USign ε) :
    smear F hF β g = ∫ y : USign ε, β.val.val (y⁻¹ * g) • F y := by
  rw [smear_apply F hF, ← integral_mul_left_eq_self (fun y ↦ β.val.val (y⁻¹ * g) • F y) g]
  simp

open scoped Pointwise NNReal Topology in
/-- If a curve `γ` in `U(diag ε)` has `γ'(t) = γ(t) X`, then, for continuous `F` and a smooth
compactly supported `α`, the convolution `smear F α : g ↦ ∫ y, α y⁻¹ • F (g * y)` along `γ` has at
`t` the derivative `smear F (X α) (γ t)`, where `X α = bumpDeriv X α` is the right derivative. -/
theorem hasDerivAt_smear (F : USign ε → E) (α : Bumps ε) (hF : Continuous F)
    {γ : ℝ → USign ε} {t : ℝ} {X : Matrix n n ℂ}
    (hγ : HasDerivAt (fun s : ℝ ↦ (γ s).val.val) ((γ t).val.val * X) t) :
    HasDerivAt (fun s : ℝ ↦ smear F hF α (γ s)) (smear F hF (bumpDeriv X α) (γ t)) t := by
  -- Write the convolution as `∫ y, α (y⁻¹ * g) • F y` and differentiate under the integral sign:
  -- for `γ s` in a compact neighbourhood `N` of `γ t` the integrand vanishes off the compact set
  -- `K⁻¹` and is Lipschitz in `s` at `t`.
  obtain ⟨A, hA⟩ : ∃ A, smoothMatrixFunctions.restrictU ε ℂ A = α.val.val := α.val.property
  obtain ⟨C, hC⟩ := hγ.isBigO_sub.bound
  obtain ⟨N, hN, hN_nhds⟩ := exists_compact_mem_nhds (γ t)
  let K : Set (USign ε) := tsupport α.val.val * N⁻¹
  have hK : IsCompact K := α.property.mul hN.inv
  -- The smooth extension `A` of `α` to all matrices is Lipschitz on the compact set `K * N`.
  obtain ⟨L, hL⟩ : ∃ L : ℝ≥0,
      LipschitzOnWith L A.val ((fun x : USign ε ↦ x.val.val) '' (K * N)) :=
    (contDiff_infty.1 A.property 1).locallyLipschitz.locallyLipschitzOn
      |>.exists_lipschitzOnWith_of_compact ((hK.mul hN).image_of_continuous _)
  let bound : USign ε → ℝ := K⁻¹.indicator fun y : USign ε ↦ ‖F y‖ * L * ‖y⁻¹.val.val‖
  have h_lip (y : USign ε) (s : ℝ)
      (hs : ‖(γ s).val.val - (γ t).val.val‖ ≤ C * ‖s - t‖ ∧ γ s ∈ N) :
      ‖α.val.val (y⁻¹ * γ s) • F y - α.val.val (y⁻¹ * γ t) • F y‖ ≤ bound y * C * ‖s - t‖ := by
    grw [norm_bump_smul_sub_le_indicator F α hA hL y hs.right (mem_of_mem_nhds hN_nhds), hs.left,
      mul_assoc]
    exact indicator_nonneg (fun z _ ↦ by positivity) y
  have h_diff (y : USign ε) : HasDerivAt (fun s : ℝ ↦ α.val.val (y⁻¹ * γ s) • F y)
      ((rightDeriv ε ℂ X α.val).val (y⁻¹ * γ t) • F y) t :=
    (hasDerivAt_curve (γ := fun s ↦ y⁻¹ * γ s) α.val
      (by simp [mul_assoc, hγ.const_mul])).smul_const (F y)
  have h_near : {s : ℝ | ‖(γ s).val.val - (γ t).val.val‖ ≤ C * ‖s - t‖ ∧ γ s ∈ N} ∈ 𝓝 t :=
    hC.and (isClosedEmbedding_U.continuousAt_iff.2 hγ.continuousAt hN_nhds)
  have h_int_t : Integrable fun y : USign ε ↦ α.val.val (y⁻¹ * γ t) • F y := by
    simpa using (integrable_bump_inv_smul (fun y ↦ F (γ t * y)) α).comp_mul_left (γ t)⁻¹
  have h_int_bound : Integrable fun y : USign ε ↦ bound y * C :=
    ((hK.inv.integrableOn _).integrable_indicator hK.inv.measurableSet).mul_const C
  have h_meas_deriv : AEStronglyMeasurable fun y : USign ε ↦
      toSpanSingleton ℝ ((rightDeriv ε ℂ X α.val).val (y⁻¹ * γ t) • F y) :=
    (toSpanSingletonCLE (𝕜 := ℝ)).continuous.comp_aestronglyMeasurable (by fun_prop)
  obtain ⟨h_int, h_deriv⟩ :=
    hasFDerivAt_integral_of_dominated_loc_of_lip' h_near (by fun_prop) h_int_t h_meas_deriv
      (.of_forall h_lip) h_int_bound (.of_forall h_diff)
  simp only [smear_apply_eq_integral_inv_mul]
  -- `bumpDeriv` is by definition the restriction of `rightDeriv`.
  change HasDerivAt (fun s : ℝ ↦ ∫ y : USign ε, α.val.val (y⁻¹ * γ s) • F y)
    (∫ y : USign ε, (rightDeriv ε ℂ X α.val).val (y⁻¹ * γ t) • F y) t
  simpa [integral_apply h_int] using h_deriv.hasDerivAt

/-- Suppose the convolution `smear F α` of a continuous function `F` with a bump function `α` is
the smooth function `f`. Then for every matrix `X`, the convolution with the right derivative
`bumpDeriv X α` is the right derivative of `f` along `X`. -/
theorem rightDeriv_smear (F : USign ε → E) (hF : Continuous F) {α : Bumps ε} {f : SmoothU ε E}
    (hf : smear F hF α = f.val) (X : Matrix n n ℂ) :
    smear F hF (bumpDeriv X α) = (rightDeriv ε E X f).val := by
  -- For `Y` in the Lie algebra of the group, both sides at `g` are the derivative at `0` of the
  -- same function along `g * expU (t • Y)`; then write `X = Y₁ + I • Y₂`.
  have h_real (Y : unitaryLie (signMatrix ε)) :
      smear F hF (bumpDeriv Y α) = (rightDeriv ε E Y f).val := by
    funext g
    have h_right : HasDerivAt (fun s : ℝ ↦ smear F hF α (g * expU (s • Y)))
        ((rightDeriv ε E Y f).val g) 0 := by
      simpa [hf, -smear_apply] using hasDerivAt_rightDeriv_expU f g Y 0
    simpa [-smear_apply] using (hasDerivAt_smear F α hF (hasDerivAt_expU Y g 0)).unique h_right
  rw [eq_unitaryLiePart_add_I_smul ε X]
  simp [-smear_apply, h_real]

end New.DiscreteSeries

end BumpConvolution

end
