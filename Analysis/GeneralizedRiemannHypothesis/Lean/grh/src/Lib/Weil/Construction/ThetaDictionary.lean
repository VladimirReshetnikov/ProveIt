import Lib.Shimura.Uniformisation.AdelicFrames
import Lib.Weil.Construction.ThetaJets

/-!
# The dictionary between vectors and theta functions

For rational vectors `γ` in `Eⁿ`, with real images in `ℂ^(Φ × n)`, this file defines the Riemann
form, the translations `T_γ` of functions on `ℂ^(Φ × n)` and the theta functions for a lattice.

* `New.ratShift_ratShift`, `New.mem_star_smul_idealLattice_iff`, `New.signedShift_add`: the law of
  composition of the translations `T_γ`, the duality of `δ̄ 𝔞₀ⁿ` and `δ⁻¹ 𝔞₀ⁿ` for the Riemann form,
  and the signs that make the translations a homomorphism on `𝔞₀ⁿ`.
* `New.Space.entireTheta_rho`: for a standard space, the Heisenberg translation `V.ϱ (finVec x)`,
  with `x = α⁻¹ γ` the finite image of a rational vector `γ`, acts on theta functions as `T_(-γ)`.
* `New.Space.range_apply_finVec_eq_range_ratShift_entireTheta`: for a standard space and `φ` in the
  finite part, the values of `φ` at the finite adelic vectors are the values
  `T_γ (entireTheta φ) 0`.
* `New.Space.isThetaFunction_iff`: for a standard space, the theta functions for `𝔞₀ⁿ` are the
  multiples of the theta function of the vacuum, because the Riemann form on `𝔞₀ⁿ` is unimodular.

Here `ℂ^(Φ × n)` stands for `InfinitePlace E × n → ℂ`, and `Φ w` is the embedding of `E` in `ℂ` that
the CM type chooses at the infinite place `w`.

Notions from other files:
* `realImage γ`: the entry at `(w, i)` is `Φ w (γ i)` divided by the `w`-part of the idele
  `scaleIdele E`; `finiteImage γ` is `α⁻¹ γ` in `(𝔸f E)ⁿ`, with `α` the finite part of this idele.
* `stdLattice E n`: the lattice `Ôⁿ` of integral finite adelic vectors; it is its own dual for the
  character `selfDualAddChar E`.
* `semichar x`: the value `selfDualAddChar E (traceOneAdele * half * star x ⬝ᵥ x)`, where
  `traceOneAdele` is the image of `traceOne = c₀ : E`, with `c₀ + c̄₀ = 1`.
* `𝒮 V` is the space of vectors of the Weil representation of a space `V`, with vacuum `V.vacElem`
  and Heisenberg action `V.ϱ`; `entireTheta φ` is the theta function of `φ`.
* `V.IsStd`: all signs of `V` are `+1` and its point is the identity matrix.

## Relation to the literature

Known result: the passage between the Fock model of the Weil representation and classical theta
functions. A principal polarization has one theta function up to a factor. Source: Beauville, Theta
functions, old and new, Theorem 3.5.
-/

open NumberField Complex ComplexConjugate Pointwise

namespace New

open WeilData stdLattice Space ThetaTori

section FockForm

variable (X : Type) [Fintype X]

/-- The standard Hermitian form `u* z = ∑ conj (u x) z x` on `ℂ^X`. -/
noncomputable def fockForm : RealComplexForm (X → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun u := LinearMap.toContinuousLinearMap (dotProductBilin ℂ ℂ (star u))
      map_add' u v := ContinuousLinearMap.ext fun z ↦ by simp
      map_smul' r u := ContinuousLinearMap.ext fun z ↦ by simp [star_trivial] }

variable {X}

lemma fockForm_apply (u z : X → ℂ) : fockForm X u z = star u ⬝ᵥ z := rfl

lemma re_fockForm_comm (u z : X → ℂ) : (fockForm X u z).re = (fockForm X z u).re := by
  simp [fockForm_apply, dotProduct, mul_comm]

/-- The standard Hermitian form has symmetric real part, and with the multiplier `1` it is an
Appell–Humbert datum for the zero lattice. -/
lemma isAppellHumbert_fockForm : IsAppellHumbert (L := ⊥) (fockForm X) 1 :=
  ⟨re_fockForm_comm, by simp, by simp⟩

/-- The standard Hermitian form is positive definite, so it is a positive Riemann form. -/
lemma isPosRiemann_fockForm : IsPosRiemann (fockForm X) := by
  refine isPosRiemann_of_re_pos fun u hu ↦ ?_
  obtain ⟨x, hx⟩ : ∃ x : X, u x ≠ 0 := Function.ne_iff.1 hu
  simpa [fockForm_apply, dotProduct, normSq_apply] using
    Finset.sum_pos' (fun x _ ↦ normSq_nonneg (u x)) ⟨x, Finset.mem_univ x, normSq_pos.2 hx⟩

end FockForm

section Dictionary

variable {E n : Type} [Field E] [CMType E] [WeilData E]

/-- The entry of the real image of `γ` at `(w, i)` is `Φ w (γ i)` divided by the `w`-component of
the idele `scaleIdele E`. -/
lemma realImage_apply (γ : n → E) (x : InfinitePlace E × n) :
    realImage γ x = Φ x.1 (γ x.2) / (scaleIdele E : 𝔸 E).1 x.1 := by
  simp [realImage, realCoord]

lemma scaleIdele_fst_ne_zero (w : InfinitePlace E) : (scaleIdele E : 𝔸 E).1 w ≠ 0 := fun h_zero ↦
  by simpa [h_zero] using conj_scaleIdele_mul E w

/-- The real image of rational vectors as an additive map. -/
noncomputable def realImageHom : (n → E) →+ InfinitePlace E × n → ℂ :=
  .mk' realImage fun γ γ' ↦ funext fun x ↦ by simp [realImage_apply, add_div]

lemma realImage_add (γ γ' : n → E) : realImage (γ + γ') = realImage γ + realImage γ' :=
  realImageHom.map_add γ γ'

lemma realImage_neg (γ : n → E) : realImage (-γ) = -realImage γ := realImageHom.map_neg γ

lemma realImage_zero : realImage (0 : n → E) = 0 := realImageHom.map_zero

/-- A rational vector is determined by its real image. -/
lemma injective_realImageHom : Function.Injective (realImageHom (E := E) (n := n)) := by
  refine (injective_iff_map_eq_zero _).2 fun γ hγ ↦ funext fun i ↦ ?_
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  simpa [realImageHom, realImage_apply, scaleIdele_fst_ne_zero] using congrFun hγ (w, i)

variable (E n) in
/-- The lattice `𝔞₀ⁿ` of `Eⁿ`: the vectors `γ` whose finite image `α⁻¹ γ` lies in `Ôⁿ`. -/
noncomputable def idealLattice : AddSubgroup (n → E) :=
  (stdLattice E n).comap finiteImage.toAddMonoidHom

lemma mem_idealLattice {γ : n → E} : γ ∈ idealLattice E n ↔ finiteImage γ ∈ stdLattice E n :=
  Iff.rfl

/-- The lattice `𝔞₀ⁿ` is stable under multiplication by the elements of `E` that are integral at
all finite places. -/
lemma smul_mem_idealLattice {δ : E} (hδ : ↑δ ∈ Ô E) {γ : n → E} (hγ : γ ∈ idealLattice E n) :
    δ • γ ∈ idealLattice E n := by
  rw [mem_idealLattice, map_smul, ← algebraMap_smul (𝔸f E)]
  exact smul_mem_stdLattice hδ hγ

lemma mem_inv_smul_idealLattice {δ : E} (hδ : δ ≠ 0) {y : n → E} :
    y ∈ δ⁻¹ • idealLattice E n ↔ δ • y ∈ idealLattice E n := by
  rw [AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem₀ (inv_ne_zero hδ), inv_inv]

variable [Fintype n]

/-- The translation `T_γ` of functions on `ℂ^(Φ × n)`: the translation by the real image of `γ`,
twisted by the exponential factor of the standard Hermitian form (`thetaShift`). -/
noncomputable def ratShift (γ : n → E) : Module.End ℂ ((InfinitePlace E × n → ℂ) → ℂ) :=
  (fockForm (InfinitePlace E × n)).thetaShift (realImage γ)

/-- The Riemann form `{γ, γ'} = Im (u* u') / π` of rational vectors with real images `u`, `u'`. -/
noncomputable def ratRiemannForm (γ γ' : n → E) : ℝ :=
  (fockForm (InfinitePlace E × n)).riemannForm (realImage γ) (realImage γ')

/-- The commutator `exp (2 π i {γ, γ'})` of the translations `T_γ` and `T_γ'`. -/
noncomputable def ratPhase (γ γ' : n → E) : ℂ := exp (2 * Real.pi * I * ratRiemannForm γ γ')

variable {F : (InfinitePlace E × n → ℂ) → ℂ}

lemma ratShift_zero : ratShift (0 : n → E) F = F := by
  rw [ratShift, realImage_zero, thetaShift_zero]

/-- Let `E` be a CM field with Weil data, `γ`, `γ'` vectors of `Eⁿ`, and `F` any function on
`ℂ^(Φ × n)`. The translations `T_γ = ratShift γ` (translation by the real image of `γ`, twisted by
the exponential factor of the standard Hermitian form) obey the law of composition
`T_γ T_γ' F = exp (π i {γ, γ'}) T_(γ + γ') F`. Here `{γ, γ'} = ratRiemannForm γ γ' = Im (u* u') / π`
is the Riemann form of the real images `u`, `u'`. -/
lemma ratShift_ratShift (γ γ' : n → E) :
    ratShift γ (ratShift γ' F) =
      exp (Real.pi * I * ratRiemannForm γ γ') • ratShift (γ + γ') F := by
  rw [ratShift, ratShift, ratShift, realImage_add]
  exact isAppellHumbert_fockForm.thetaShift_thetaShift _ _

lemma ratRiemannForm_swap (γ γ' : n → E) : ratRiemannForm γ' γ = -ratRiemannForm γ γ' :=
  riemannForm_swap _ _

/-- The commutator of `T_γ` and `T_γ'` is `exp (2 π i {γ, γ'})`. -/
lemma ratShift_comm (γ γ' : n → E) :
    ratShift γ (ratShift γ' F) = ratPhase γ γ' • ratShift γ' (ratShift γ F) := by
  rw [ratShift_ratShift, ratShift_ratShift, smul_smul, ratPhase, ← exp_add, add_comm γ',
    ratRiemannForm_swap γ γ']
  congr 2
  push_cast
  ring

variable [DecidableEq n]

/-- For rational vectors `γ, γ'` with finite images `x, x'`, the adelic Heisenberg cocycle, which is
the product of the real cocycle `β` of `realHeisenberg` at the real images (which is
`exp (-π i ratRiemannForm γ γ')`; see `exp_ratRiemannForm`) and of the finite character
`ψ₀ (x'* x / 2)`, is `1`. -/
lemma realHeisenberg_beta_mul_selfDualAddChar_eq_one (γ γ' : n → E) :
    (Fock.realHeisenberg fun _ : InfinitePlace E × n ↦ 1).β (realImage γ) (realImage γ') *
      selfDualAddChar E (half * star (finiteImage γ') ⬝ᵥ finiteImage γ) = 1 := by
  have h_adelic : (adelicHeisenberg E (1 : n → ℤˣ)).β ((stdSpace E n).vecAtPoint γ)
      ((stdSpace E n).vecAtPoint γ') = 1 :=
    beta_vecAtPoint_eq_one (stdSpace E n) γ γ'
  simp only [vecAtPoint_eq_adelicSum, Heisenberg.OrthogonalSum.beta_equiv] at h_adelic
  exact h_adelic

/-- The product formula for the Heisenberg cocycle: for rational vectors `γ, γ'` with finite
images `x, x'`, the value `exp (π i {γ, γ'})`, which is inverse to the real cocycle, equals
`ψ₀ (x'* x / 2)`. Here `{γ, γ'}` is `ratRiemannForm γ γ'` and `half` is the adelic `1/2`. -/
lemma exp_ratRiemannForm (γ γ' : n → E) :
    exp (Real.pi * I * ratRiemannForm γ γ') =
      selfDualAddChar E (half * star (finiteImage γ') ⬝ᵥ finiteImage γ) := by
  -- Both sides are inverse to the real cocycle `β` at the real images of `γ` and `γ'`.
  set β : ℂ := (Fock.realHeisenberg fun _ : InfinitePlace E × n ↦ 1).β (realImage γ) (realImage γ')
  have h_real : exp (Real.pi * I * ratRiemannForm γ γ') * β = 1 := by
    have h_sub : star (realImage γ) ⬝ᵥ realImage γ' - star (realImage γ') ⬝ᵥ realImage γ =
        2 * Real.pi * I * (fockForm _).riemannForm (realImage γ) (realImage γ') :=
      isAppellHumbert_fockForm.sub_eq_riemannForm (realImage γ) (realImage γ')
    have h_sign : signMatrix (fun _ : InfinitePlace E × n ↦ 1) = 1 := signMatrix_one
    simp only [β, Fock.realHeisenberg, ← exp_add, ratRiemannForm, h_sign, Matrix.one_mulVec]
    rw [← exp_zero]
    congr 1
    linear_combination (-1 / 2 : ℂ) * h_sub
  exact left_inv_eq_right_inv h_real (realHeisenberg_beta_mul_selfDualAddChar_eq_one γ γ')

/-- The commutator of `T_γ` and `T_γ'` is `ψ₀ (x'* x)` for the finite images `x`, `x'`. -/
lemma ratPhase_eq (γ γ' : n → E) :
    ratPhase γ γ' = selfDualAddChar E (star (finiteImage γ') ⬝ᵥ finiteImage γ) := by
  -- The phase is the square of `exp (π i {γ, γ'})`.
  rw [ratPhase, mul_assoc 2, mul_assoc 2, two_mul, exp_add, exp_ratRiemannForm,
    ← AddChar.map_add_eq_mul, ← two_mul, ← mul_assoc, two_mul_half, one_mul]

lemma ratPhase_add_right (γ y y' : n → E) :
    ratPhase γ (y + y') = ratPhase γ y * ratPhase γ y' := by
  simp only [ratPhase_eq, map_add, star_add, add_dotProduct, AddChar.map_add_eq_mul]

lemma ratPhase_add_left (γ γ' y : n → E) :
    ratPhase (γ + γ') y = ratPhase γ y * ratPhase γ' y := by
  simp only [ratPhase_eq, map_add, dotProduct_add, AddChar.map_add_eq_mul]

/-- For the commutator of translations, multiplication by `star δ` is adjoint to that by `δ`. -/
lemma ratPhase_smul_left (δ : E) (γ y : n → E) :
    ratPhase (star δ • γ) y = ratPhase γ (δ • y) := by
  rw [ratPhase_eq, ratPhase_eq, map_smul, map_smul, ← algebraMap_smul (𝔸f E) δ,
    ← algebraMap_smul (𝔸f E) (star δ), star_smul, smul_dotProduct, dotProduct_smul]
  simp

/-- The lattice `𝔞₀ⁿ` is self-dual for the Riemann form: `γ` lies in it exactly when
`exp (2 π i {γ, y}) = 1` for all `y` in it. -/
lemma mem_idealLattice_iff_ratPhase {γ : n → E} :
    γ ∈ idealLattice E n ↔ ∀ y ∈ idealLattice E n, ratPhase γ y = 1 := by
  simp only [ratPhase_eq, mem_idealLattice]
  refine ⟨fun hγ y hy ↦ mem_stdLattice_iff_selfDualAddChar.1 hγ _ hy, fun h ↦ ?_⟩
  -- The lattice `Ôⁿ` is open and self-dual for `ψ₀`, and rational vectors are dense.
  refine mem_stdLattice_iff_selfDualAddChar.2 fun x hx ↦ ?_
  have h_closed : IsClosed {x : n → 𝔸f E |
      x ∈ stdLattice E n → selfDualAddChar E (star x ⬝ᵥ finiteImage γ) = 1} :=
    isClosed_imp isOpen_stdLattice (isClosed_eq (by fun_prop) continuous_const)
  exact denseRange_finiteImage.induction_on x h_closed h hx

/-- For `δ ≠ 0`, the lattice `δ̄ 𝔞₀ⁿ` is dual to `δ⁻¹ 𝔞₀ⁿ` for the Riemann form: `γ` lies in it
exactly when the phase `exp (2 π i {γ, y})` is `1` for every `y` in `δ⁻¹ 𝔞₀ⁿ`. -/
lemma mem_star_smul_idealLattice_iff {δ : E} (hδ : δ ≠ 0) {γ : n → E} :
    γ ∈ star δ • idealLattice E n ↔ ∀ y ∈ δ⁻¹ • idealLattice E n, ratPhase γ y = 1 := by
  have h_star : star δ ≠ 0 := star_ne_zero.2 hδ
  -- Write γ = δ̄ • γ₀.
  obtain ⟨γ₀, rfl⟩ : ∃ γ₀ : n → E, star δ • γ₀ = γ := MulAction.surjective₀ h_star γ
  rw [AddSubgroup.smul_mem_pointwise_smul_iff₀ h_star, mem_idealLattice_iff_ratPhase]
  simpa only [ratPhase_smul_left, mem_inv_smul_idealLattice hδ] using
    -- the substitution y' = δ • y
    (MulAction.surjective₀ hδ).forall

/-- The translation `T_γ` times the value of the semicharacter at the finite image of `γ`. For `γ`
in `𝔞₀ⁿ` this value is the sign `(-1) ^ |γ|²`, where `|γ|² = ∑ |Φ w (γ i)|²`; see
`New.exists_semichar_finiteImage_eq_neg_one_zpow`. -/
noncomputable def signedShift (γ : n → E) : Module.End ℂ ((InfinitePlace E × n → ℂ) → ℂ) :=
  semichar (finiteImage γ) • ratShift γ

omit [DecidableEq n] in
lemma signedShift_apply (γ : n → E) :
    signedShift γ F = semichar (finiteImage γ) • ratShift γ F := rfl

/-- Let `E` be a CM field with Weil data. These give a finite idele `α`, an algebraic integer `c₀`
of `E` with `c₀ + c̄₀ = 1`, and the character `ψ₀ = selfDualAddChar E` of the finite adeles, for
which `Ô` is self-dual. For a rational vector `γ` in `Eⁿ` put
`χ γ = semichar x = ψ₀ (c₀ x* x / 2)`, where `x = finiteImage γ = α⁻¹ γ` is a finite adelic vector.
If `γ` and `γ'` lie in the lattice `𝔞₀ⁿ = idealLattice E n`, that is, their finite images are
integral, then `χ (γ + γ') = χ γ * χ γ' * exp (π i {γ, γ'})`. Here `{γ, γ'} = Im (u* u') / π` is
the Riemann form `ratRiemannForm γ γ'`, with `u`, `u'` the real images of `γ`, `γ'`. -/
lemma semichar_finiteImage_add {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n]
    [DecidableEq n] {γ γ' : n → E} (hγ : γ ∈ idealLattice E n) (hγ' : γ' ∈ idealLattice E n) :
    semichar (finiteImage (γ + γ')) =
      semichar (finiteImage γ) * semichar (finiteImage γ') *
        exp (Real.pi * I * ratRiemannForm γ γ') := by
  -- For integral `x`, `x'` the factor `ψ₀ (c̄₀ x'* x)` in the law `semichar_add` is `1`.
  have h_int : star traceOneAdele * star (finiteImage γ') ⬝ᵥ finiteImage γ ∈ Ô E :=
    mul_mem (star_mem_Ô traceOneAdele_mem)
      (star_dotProduct_mem (mem_idealLattice.1 hγ) (mem_idealLattice.1 hγ'))
  have h_one :
      selfDualAddChar E (star traceOneAdele * star (finiteImage γ') ⬝ᵥ finiteImage γ) = 1 :=
    selfDualAddChar_eq_one_of_mem h_int
  -- The finite cocycle is by definition `ψ₀ (x'* x / 2)`; the product formula evaluates it.
  have h_cocycle : (finHeisenberg E n).β (finiteImage γ) (finiteImage γ') =
      exp (Real.pi * I * ratRiemannForm γ γ') :=
    (exp_ratRiemannForm γ γ').symm
  calc semichar (finiteImage (γ + γ'))
      = selfDualAddChar E (star traceOneAdele * star (finiteImage γ') ⬝ᵥ finiteImage γ) *
          semichar (finiteImage γ + finiteImage γ') := by rw [h_one, one_mul, map_add]
    _ = semichar (finiteImage γ) * semichar (finiteImage γ') *
          (finHeisenberg E n).β (finiteImage γ) (finiteImage γ') := (semichar_add _ _).symm
    _ = semichar (finiteImage γ) * semichar (finiteImage γ') *
          exp (Real.pi * I * ratRiemannForm γ γ') := by rw [h_cocycle]

/-- The signed translations are a homomorphism on `𝔞₀ⁿ`. -/
lemma signedShift_add {γ γ' : n → E} (hγ : γ ∈ idealLattice E n) (hγ' : γ' ∈ idealLattice E n) :
    signedShift (γ + γ') F = signedShift γ (signedShift γ' F) := by
  simp only [signedShift_apply, map_smul, ratShift_ratShift, smul_smul,
    semichar_finiteImage_add hγ hγ', mul_comm (semichar (finiteImage γ)), mul_assoc]

/-- A theta function for a subgroup `Y` of `Eⁿ` is an entire function on `ℂ^(Φ × n)` that the
signed translations `signedShift γ`, `γ ∈ Y`, fix. -/
structure IsThetaFunction (Y : AddSubgroup (n → E)) (F : (InfinitePlace E × n → ℂ) → ℂ) :
    Prop where
  /-- The function is entire. -/
  differentiable : Differentiable ℂ F
  /-- The signed translations along `Y` fix the function. -/
  signedShift_eq : ∀ γ ∈ Y, signedShift γ F = F

omit [DecidableEq n] in
lemma semichar_neg (x : n → 𝔸f E) : semichar (-x) = semichar x := by
  simp [semichar]

/-- If `b` multiplies the coordinates at the place `w` by `conj (Φ w traceOne)`, the canonical
multiplier `exp (π i R (b u, u))`, with `R` the Riemann form, at the real image `u` of `γ` is the
inverse of the semicharacter at the finite image; `traceOne` is `c₀ : E` with `c₀ + c̄₀ = 1`. -/
lemma canonicalMultiplier_realImage
    {b : (InfinitePlace E × n → ℂ) →L[ℂ] InfinitePlace E × n → ℂ}
    (hb : ∀ (u : InfinitePlace E × n → ℂ) (x : InfinitePlace E × n),
      b u x = conj (Φ x.1 (traceOne : E)) * u x) (γ : n → E) :
    canonicalMultiplier (fockForm (InfinitePlace E × n)) b (realImage γ) =
      (semichar (finiteImage γ))⁻¹ := by
  rw [← neg_neg γ, map_neg, semichar_neg, realImage_neg,
    semichar_finiteImage (-γ) hb fockForm_apply, inv_inv]

/-- If `b` multiplies the coordinates at the place `w` by `conj (Φ w traceOne)`, the normalized
translation (the inverse of the canonical multiplier of `fockForm` times `thetaShift`) by the real
image of `γ` is the signed translation. -/
lemma normalizedShift_realImage
    {b : (InfinitePlace E × n → ℂ) →L[ℂ] InfinitePlace E × n → ℂ}
    (hb : ∀ (u : InfinitePlace E × n → ℂ) (x : InfinitePlace E × n),
      b u x = conj (Φ x.1 (traceOne : E)) * u x) (γ : n → E) :
    normalizedShift (fockForm (InfinitePlace E × n)) b (realImage γ) = signedShift γ := by
  rw [normalizedShift, canonicalMultiplier_realImage hb, inv_inv, signedShift, ratShift]

omit [Fintype n] [DecidableEq n] in
/-- For the entry `u` of the real image of `γ` at `x = (w, i)`, one has
`Im (Φ w c₀) |u|² = π |Φ w (γ i)|²`, where `c₀ = traceOne = (1 - ȷ⁻¹) / 2`. -/
lemma im_traceOne_mul_normSq_realImage (γ : n → E) (x : InfinitePlace E × n) :
    (Φ x.1 (traceOne : E)).im * normSq (realImage γ x) = Real.pi * normSq (Φ x.1 (γ x.2)) := by
  -- As `Φ w ȷ` is purely imaginary, `Im (Φ w c₀) = 1 / (2 Im (Φ w ȷ))`.
  have h_pos : 0 < (Φ x.1 (j : E)).im := im_pos x.1
  have h_conj : conj (Φ x.1 (j : E)) = -Φ x.1 (j : E) := by
    rw [← map_neg, ← star_j, map_star_complex, starRingEnd_apply]
  have h_re : (Φ x.1 (j : E)).re = 0 := by simpa [self_eq_neg] using congrArg re h_conj
  have h_im : (Φ x.1 (traceOne : E)).im = (2 * (Φ x.1 (j : E)).im)⁻¹ := by
    simp [traceOne, map_ofNat, normSq_apply, h_re, field]
  have h_scale : normSq ((scaleIdele E : 𝔸 E).1 x.1) = (2 * Real.pi * (Φ x.1 (j : E)).im)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left (ofReal_injective ?_)
    simpa [normSq_eq_conj_mul_self] using conj_scaleIdele_mul E x.1
  rw [realImage_apply, map_div₀, h_im, h_scale]
  field

/-- The semicharacter at the finite image of a rational vector `γ` is `exp (-π i |γ|²)`, where
`|γ|² = ∑ |Φ w (γ i)|²` is summed over the infinite places `w` and the coordinates `i`. -/
lemma semichar_finiteImage_eq_exp (γ : n → E) :
    semichar (finiteImage γ) =
      exp (-(Real.pi * I * (∑ x : InfinitePlace E × n, normSq (Φ x.1 (γ x.2)) : ℝ))) := by
  -- By the product formula it is the inverse of the canonical multiplier `exp (π i R (b u, u))` at
  -- the real image `u` of `γ`, and `R (b u, u) = |γ|²`.
  let b : (InfinitePlace E × n → ℂ) →L[ℂ] InfinitePlace E × n → ℂ :=
    .pi fun x ↦ conj (Φ x.1 (traceOne : E)) • .proj x
  have hb (u : InfinitePlace E × n → ℂ) (x : InfinitePlace E × n) :
      b u x = conj (Φ x.1 (traceOne : E)) * u x := rfl
  have h_form : (fockForm (InfinitePlace E × n)).riemannForm (b (realImage γ)) (realImage γ) =
      ∑ x : InfinitePlace E × n, normSq (Φ x.1 (γ x.2)) := by
    have h_sum : (fockForm (InfinitePlace E × n)).riemannForm (b (realImage γ)) (realImage γ) =
        ∑ x : InfinitePlace E × n,
          (Φ x.1 (traceOne : E)).im * normSq (realImage γ x) / Real.pi := by
      simp only [riemannForm_def, fockForm_apply, dotProduct, ← Finset.sum_sub_distrib, im_sum,
        Finset.sum_div]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      simp [hb, normSq_apply, field]
      ring
    simp only [h_sum, im_traceOne_mul_normSq_realImage, mul_div_cancel_left₀ _ Real.pi_ne_zero]
  rw [exp_neg, ← h_form, ← canonicalMultiplier, canonicalMultiplier_realImage hb, inv_inv]

/-- Let `E` be a CM field with Weil data, and let `Φ w` be the chosen complex embedding at each
infinite place `w`. For `γ` in the lattice `𝔞₀ⁿ`, the vectors of `Eⁿ` whose finite image `α⁻¹ γ`
lies in `Ôⁿ` (with `α` the idele of the Weil data), the number `|γ|² = ∑ |Φ w (γ i)|²` is an
integer. The semicharacter `semichar x = ψ₀(c₀ x* x / 2)` at `x = finiteImage γ` is the sign
`(-1) ^ |γ|²`. -/
lemma exists_semichar_finiteImage_eq_neg_one_zpow {γ : n → E} (hγ : γ ∈ idealLattice E n) :
    ∃ k : ℤ, ∑ x : InfinitePlace E × n, normSq (Φ x.1 (γ x.2)) = k ∧
      semichar (finiteImage γ) = (-1) ^ k := by
  -- The law of the semicharacter for `γ` and `-γ` shows that `exp (-π i |γ|²)` has square `1`.
  set r : ℝ := ∑ x : InfinitePlace E × n, normSq (Φ x.1 (γ x.2))
  have h_exp : semichar (finiteImage γ) = exp (-(Real.pi * I * r)) := semichar_finiteImage_eq_exp γ
  have h_sq : semichar (finiteImage γ) * semichar (finiteImage γ) = 1 := by
    simpa [semichar_neg, ratRiemannForm, realImage_neg, semichar_eq_one_of_dotProduct_self_eq_zero]
      using (semichar_finiteImage_add hγ (neg_mem hγ)).symm
  obtain ⟨k, hk⟩ : ∃ k : ℤ, -(Real.pi * I * r) + -(Real.pi * I * r) = k * (2 * Real.pi * I) := by
    rwa [h_exp, ← exp_add, exp_eq_one_iff] at h_sq
  have h_r : (r : ℂ) = (-k : ℤ) := mul_right_cancel₀ two_pi_I_ne_zero <| by
    simp only [Int.cast_neg]
    linear_combination -hk
  refine ⟨-k, mod_cast h_r, ?_⟩
  rw [h_exp, h_r, exp_neg, mul_comm, exp_int_mul, exp_pi_mul_I, ← inv_zpow, inv_neg_one]

variable (E n) in
/-- The image of `𝔞₀ⁿ` in `ℂ^(Φ × n)`. -/
noncomputable def realLattice : Submodule ℤ (InfinitePlace E × n → ℂ) :=
  ((idealLattice E n).map realImageHom).toIntSubmodule

omit [Fintype n] [DecidableEq n] in
lemma mem_realLattice {x : InfinitePlace E × n → ℂ} :
    x ∈ realLattice E n ↔ ∃ γ ∈ idealLattice E n, realImage γ = x := Iff.rfl

/-- The image of `𝔞₀ⁿ` is a lattice of full rank in `ℂ^(Φ × n)`. -/
instance : IsFullRankLattice (realLattice E n) := by
  have h_unit : IsUnit (realImage fun _ : n ↦ (1 : E)) := by
    simp [Pi.isUnit_iff, realImage_apply, scaleIdele_fst_ne_zero]
  -- The image is the lattice `Variety.classLattice` of the trivial torsion class `⊥` for the scalar
  -- matrix `α`, in the real coordinates scaled by the image of `1`.
  let Q : Variety.RealVectors E n ≃L[ℝ] (InfinitePlace E × n → ℂ) :=
    ((LinearEquiv.curry ℝ ℂ n (InfinitePlace E)).symm ≪≫ₗ
      LinearEquiv.funCongrLeft ℝ ℂ (Equiv.prodComm (InfinitePlace E) n) ≪≫ₗ
      h_unit.unit.mulLeftLinearEquiv ℝ _).toContinuousLinearEquiv
  have h_eq : realLattice E n = Variety.classLattice (.scalar n α) ⊥ Q := by
    ext x
    -- Both sides consist of images of the `γ` with `α⁻¹ γ` integral; compare the two images.
    refine exists_congr fun γ ↦ ?_
    simp [Q, Variety.frameTorsionClass, Variety.frameCoords, mem_idealLattice, mem_stdLattice,
      ← map_inv, finiteImage, realImageHom, funext_iff, realImage_apply, div_eq_inv_mul]
  rw [h_eq]
  infer_instance

end Dictionary

section StandardSpace

variable {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
  {F : (InfinitePlace E × n → ℂ) → ℂ} {ε : n → ℤˣ} (V : Space E n ε)

/-- The theta function of a vector, as a linear map. -/
noncomputable def Space.entireThetaHom : 𝒮 V →ₗ[ℂ] (InfinitePlace E × n → ℂ) → ℂ where
  toFun := entireTheta
  map_add' φ φ' := funext fun z ↦ by simp [entireTheta, add_div]
  map_smul' c φ := funext fun z ↦ by simp [entireTheta, mul_div_assoc]

lemma Space.entireThetaHom_apply (φ : 𝒮 V) : V.entireThetaHom φ = entireTheta φ := rfl

/-- A vector `φ` in the space `𝒮 V` of the Weil representation of `V` is determined by its theta
function `entireTheta φ` on `ℂ^(Φ × n)`. -/
lemma Space.injective_entireThetaHom : Function.Injective V.entireThetaHom := by
  refine (injective_iff_map_eq_zero _).2 fun φ hφ ↦ eq_zero_of_apply_realVec_eq_zero fun z ↦ ?_
  -- The denominator in the theta function is an exponential, so it does not vanish.
  simpa [entireThetaHom, entireTheta, Fock.realVac] using congrFun hφ z

/-- Let `V` be a space over a CM field `E` with Weil data. The theta function of its vacuum
`V.vacElem` (the Gaussian times the twisted lattice indicator, as a vector of `𝒮 V`) is not
identically zero. Here the theta function `entireTheta φ` of a vector `φ` sends `y` to the value of
`φ` at the real adelic vector `y` divided by the Gaussian `exp (-|y|² / 2)`. -/
lemma Space.entireTheta_vacElem_ne_zero : entireTheta V.vacElem ≠ 0 := fun h_zero ↦ by
  simpa [V.injective_entireThetaHom (h_zero.trans (map_zero _).symm)] using
    V.dataInner_vacElem_vacElem

variable [V.IsStd]

/-- Let `V` be a standard space, meaning that all its signs are `+1` and its point is the identity,
and let `γ` be a vector of `Eⁿ` with finite image `x = α⁻¹ γ`. For every vector `φ` of `𝒮 V`, the
theta function of the translate of `φ` by the adelic vector `finVec x`, with finite part `α x = γ`
and real part zero, is `ratShift (-γ)` of the theta function `entireTheta φ`, that is, its
translate by minus the real image of `γ`, twisted by the exponential factor of the standard
Hermitian form. -/
lemma Space.entireTheta_rho (γ : n → E) (φ : 𝒮 V) :
    entireTheta (V.ϱ (finVec (finiteImage γ)) φ) = ratShift (-γ) (entireTheta φ) := by
  rw [entireTheta_translate_finiteImage γ V fockForm_apply, ratShift, realImage_neg]

/-- Let `V` be a standard space and let `φ` lie in its finite part, the span of the finite
translates of the vacuum. The values of `φ` at the finite adelic vectors are the values at `0` of
the translates `T_γ = ratShift γ` of the theta function of `φ`, for the rational vectors `γ`. -/
lemma Space.range_apply_finVec_eq_range_ratShift_entireTheta {φ : 𝒮 V} (hφ : φ ∈ V.finitePart) :
    Set.range (fun x : n → 𝔸f E ↦ φ (finVec x)) =
      Set.range (fun γ : n → E ↦ ratShift γ (entireTheta φ) 0) := by
  -- The value of `φ` at `finVec (finiteImage (-γ))` is the value at `0` of the theta function of
  -- the translate of `φ`, which is `T_γ` of the theta function of `φ`. Every finite adelic vector
  -- acts on `φ` as some rational vector does.
  have h_value (γ : n → E) : ratShift γ (entireTheta φ) 0 = φ (finVec (finiteImage (-γ))) := by
    have h_shift : entireTheta (V.ϱ (finVec (finiteImage (-γ))) φ) =
        ratShift γ (entireTheta φ) := by
      rw [V.entireTheta_rho, neg_neg]
    rw [← h_shift]
    simp [entireTheta, Fock.realVac]
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    obtain ⟨γ, -, hγ⟩ : ∃ γ : n → E, finiteImage γ - x ∈ stdLattice E n ∧
        V.ϱ (finVec (finiteImage γ)) φ = V.ϱ (finVec x) φ :=
      exists_finiteImage_approx hφ x
    have h_at : φ (finVec (finiteImage γ)) = φ (finVec x) := by rw [← theta_rho, hγ, theta_rho]
    exact ⟨-γ, by simp only [h_value, neg_neg, h_at]⟩
  · rintro _ ⟨γ, rfl⟩
    exact ⟨finiteImage (-γ), (h_value γ).symm⟩

/-- Let `V` be a standard space (all signs `+1`, point the identity matrix), `φ` a vector of its
Weil representation `𝒮 V`, and `γ` any vector of `Eⁿ` with finite image `x = α⁻¹ γ`, where `α` is
the idele of the Weil data. The operator `V.finHeisenbergOp x` is the Heisenberg action `ϱ(α x)`
scaled by the semicharacter `semichar x`. It sends the theta function `entireTheta φ` to
`signedShift (-γ)` of it, namely its translate by `T_(-γ)` times the semicharacter at the finite
image of `-γ`. -/
lemma Space.entireTheta_finHeisenbergOp (γ : n → E) (φ : 𝒮 V) :
    entireTheta (V.finHeisenbergOp (finiteImage γ) φ) = signedShift (-γ) (entireTheta φ) := by
  have h_smul : entireTheta (V.finHeisenbergOp (finiteImage γ) φ) =
      semichar (finiteImage γ) • entireTheta (V.ϱ (finVec (finiteImage γ)) φ) := by
    simp only [Space.finHeisenbergOp, ← entireThetaHom_apply, _root_.smul_apply,
      map_smul]
  rw [h_smul, V.entireTheta_rho, signedShift_apply, map_neg, semichar_neg]

/-- For a standard space `V`, the theta function of the vacuum is a theta function for `𝔞₀ⁿ`. -/
lemma Space.isThetaFunction_vacElem :
    IsThetaFunction (idealLattice E n) (entireTheta V.vacElem) := by
  refine ⟨differentiable_entireTheta (IsStd.signs_eq_one V) V.projReal_vacElem, fun γ hγ ↦ ?_⟩
  rw [← neg_neg γ, ← V.entireTheta_finHeisenbergOp,
    finHeisenbergOp_vacElem (mem_idealLattice.1 (neg_mem hγ))]

/-- Suppose that the linear map `b` multiplies the coordinates at the place `w` by
`conj (Φ w traceOne)`, where `traceOne` is `c₀ : E` with `c₀ + c̄₀ = 1`. A function `G` on
`ℂ^(Φ × n)` is a theta function for the image `realLattice E n` of the lattice `𝔞₀ⁿ`, the standard
Hermitian form `fockForm` and the canonical multiplier `exp (π i R (b u, u))`, `R` the Riemann
form, if and only if `G` is entire and fixed by the signed translations along `𝔞₀ⁿ`. -/
lemma mem_thetaSpace_iff_isThetaFunction
    {b : (InfinitePlace E × n → ℂ) →L[ℂ] InfinitePlace E × n → ℂ}
    (hb : ∀ (u : InfinitePlace E × n → ℂ) (x : InfinitePlace E × n),
      b u x = conj (Φ x.1 (traceOne : E)) * u x) {G : (InfinitePlace E × n → ℂ) → ℂ} :
    G ∈ RealComplexForm.thetaSpace (L := realLattice E n)
        (canonicalMultiplier (fockForm (InfinitePlace E × n)) b)
        (fockForm (InfinitePlace E × n)) ↔
      IsThetaFunction (idealLattice E n) G := by
  rw [mem_thetaSpace_iff_normalizedShift]
  refine ⟨fun ⟨hG, h_fix⟩ ↦ ⟨hG, fun γ hγ ↦ ?_⟩, fun ⟨hG, h_fix⟩ ↦ ⟨hG, fun l hl ↦ ?_⟩⟩
  · simpa only [normalizedShift_realImage hb] using
      h_fix (realImage γ) (mem_realLattice.2 ⟨γ, hγ, rfl⟩)
  · obtain ⟨γ, hγ, rfl⟩ := mem_realLattice.1 hl
    simpa only [normalizedShift_realImage hb] using h_fix γ hγ

/-- Suppose that the linear map `b` multiplies the coordinates at the place `w` by
`conj (Φ w traceOne)`, where `traceOne` is `c₀ : E` with `c₀ + c̄₀ = 1`. The standard Hermitian
form `fockForm` and the canonical multiplier `χ u = exp (π i R (b u, u))`, with `R` the Riemann
form, are an Appell–Humbert datum for the image `L` of `𝔞₀ⁿ` in `ℂ^(Φ × n)`: the real part of the
form is symmetric and, on `L`, `|χ| = 1` and `χ (l + m) = χ l * χ m * exp (π i R (m, l))`. -/
lemma isAppellHumbert_realLattice
    {b : (InfinitePlace E × n → ℂ) →L[ℂ] InfinitePlace E × n → ℂ}
    (hb : ∀ (u : InfinitePlace E × n → ℂ) (x : InfinitePlace E × n),
      b u x = conj (Φ x.1 (traceOne : E)) * u x) :
    IsAppellHumbert (L := realLattice E n) (fockForm (InfinitePlace E × n))
      (canonicalMultiplier (fockForm (InfinitePlace E × n)) b) := by
  refine ⟨re_fockForm_comm, fun l _ ↦ by simp [canonicalMultiplier, norm_exp], ?_⟩
  intro l hl m hm
  obtain ⟨γ, hγ, rfl⟩ := mem_realLattice.1 hl
  obtain ⟨γ', hγ', rfl⟩ := mem_realLattice.1 hm
  show canonicalMultiplier (fockForm _) b (realImage γ + realImage γ') =
    _ * _ * exp (Real.pi * I * ratRiemannForm γ' γ)
  -- The canonical multiplier is the inverse of the semicharacter.
  simp only [← realImage_add, canonicalMultiplier_realImage hb, semichar_finiteImage_add hγ hγ',
    mul_inv, ratRiemannForm_swap γ γ', ofReal_neg, mul_neg, exp_neg]

/-- The image `realLattice E n` of `𝔞₀ⁿ` in `ℂ^(Φ × n)` is unimodular: if some multiplier `χ`
makes the standard Hermitian form `fockForm` an Appell–Humbert datum for it, it contains its dual
lattice, that is, every vector whose Riemann form with each element of the image is an integer. -/
lemma dualLattice_fockForm_le_realLattice {χ : (InfinitePlace E × n → ℂ) → ℂ}
    (h_AH : IsAppellHumbert (L := realLattice E n) (fockForm (InfinitePlace E × n)) χ) :
    RealComplexForm.dualLattice (L := realLattice E n) (fockForm (InfinitePlace E × n)) ≤
      realLattice E n := by
  -- A point of the dual lattice has a multiple in the lattice, so it is rational.
  intro a ha
  -- The instance needed to find the multiple.
  have h_pos : IsPosRiemann (fockForm (InfinitePlace E × n)) := isPosRiemann_fockForm
  obtain ⟨M, hM, hM_mem⟩ := h_AH.exists_nsmul_mem_of_mem_dualLattice
  obtain ⟨γ, -, hγ⟩ : ∃ γ ∈ idealLattice E n, realImage γ = M • a :=
    mem_realLattice.1 (hM_mem a ha)
  have h_rat : realImage ((M : E)⁻¹ • γ) = a := by
    funext x
    simpa [realImage_apply, mul_div_assoc, hM, inv_mul_eq_iff_eq_mul₀] using congrFun hγ x
  refine mem_realLattice.2 ⟨(M : E)⁻¹ • γ, mem_idealLattice_iff_ratPhase.2 fun y hy ↦ ?_, h_rat⟩
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (fockForm _).riemannForm a (realImage y) = k :=
    ha (realImage y) (mem_realLattice.2 ⟨y, hy, rfl⟩)
  rw [ratPhase, ratRiemannForm, h_rat, hk, exp_eq_one_iff]
  exact ⟨k, by simp [mul_comm, mul_left_comm]⟩

/-- Suppose that the linear map `b` multiplies the coordinates at the place `w` by
`conj (Φ w traceOne)`, where `traceOne` is `c₀ : E` with `c₀ + c̄₀ = 1`. The theta functions for
the image `realLattice E n` of `𝔞₀ⁿ` in `ℂ^(Φ × n)`, the standard Hermitian form and the canonical
multiplier of `b` form a space of dimension `1`, as this lattice is unimodular. -/
lemma finrank_thetaSpace_realLattice
    {b : (InfinitePlace E × n → ℂ) →L[ℂ] InfinitePlace E × n → ℂ}
    (hb : ∀ (u : InfinitePlace E × n → ℂ) (x : InfinitePlace E × n),
      b u x = conj (Φ x.1 (traceOne : E)) * u x) :
    Module.finrank ℂ (RealComplexForm.thetaSpace (L := realLattice E n)
      (canonicalMultiplier (fockForm (InfinitePlace E × n)) b)
      (fockForm (InfinitePlace E × n))) = 1 := by
  let B : LatticeForm (realLattice E n) := fockForm (InfinitePlace E × n)
  have h_AH : IsAppellHumbert B (canonicalMultiplier B b) := isAppellHumbert_realLattice hb
  -- The instance needed for Frobenius' dimension formula.
  have h_pos : IsPosRiemann B := isPosRiemann_fockForm
  obtain ⟨-, h_sq, -⟩ := h_AH.finrank_sq_eq_relIndex
  have h_one : Module.finrank ℂ (B.thetaSpace (canonicalMultiplier B b)) ^ 2 = 1 :=
    h_sq.trans (AddSubgroup.relIndex_eq_one.2 (dualLattice_fockForm_le_realLattice h_AH))
  exact (pow_eq_one_iff.1 h_one).resolve_right two_ne_zero

/-- Let `V` be a standard space over the CM field `E` (all signs `+1`, point the identity matrix).
A function `F` on `ℂ^(Φ × n)` is a theta function for the lattice `𝔞₀ⁿ` of `Eⁿ`, that is, entire
and fixed by its signed translations, exactly when it is a multiple of the theta function of the
vacuum vector of `V`. -/
theorem Space.isThetaFunction_iff :
    IsThetaFunction (idealLattice E n) F ↔ ∃ c : ℂ, c • entireTheta V.vacElem = F := by
  -- The theta functions are those of the Hermitian form `B` on `ℂ^(Φ × n)` for the image of
  -- `𝔞₀ⁿ`. As this lattice is unimodular, their space is spanned by that of the vacuum.
  let b : (InfinitePlace E × n → ℂ) →L[ℂ] InfinitePlace E × n → ℂ :=
    .pi fun x ↦ conj (Φ x.1 (traceOne : E)) • .proj x
  have hb (u : InfinitePlace E × n → ℂ) (x : InfinitePlace E × n) :
      b u x = conj (Φ x.1 (traceOne : E)) * u x := rfl
  let B : LatticeForm (realLattice E n) := fockForm (InfinitePlace E × n)
  have h_dim : Module.finrank ℂ (B.thetaSpace (canonicalMultiplier B b)) = 1 :=
    finrank_thetaSpace_realLattice hb
  have h_vac : entireTheta V.vacElem ∈ B.thetaSpace (canonicalMultiplier B b) :=
    (mem_thetaSpace_iff_isThetaFunction hb).2 V.isThetaFunction_vacElem
  refine ⟨fun hF ↦ ?_, ?_⟩
  · let θ : B.thetaSpace (canonicalMultiplier B b) := ⟨entireTheta V.vacElem, h_vac⟩
    have hθ : θ ≠ 0 := fun h ↦ V.entireTheta_vacElem_ne_zero (congrArg Subtype.val h)
    obtain ⟨c, hc⟩ : ∃ c : ℂ, c • θ = ⟨F, (mem_thetaSpace_iff_isThetaFunction hb).2 hF⟩ :=
      (finrank_eq_one_iff_of_nonzero' θ hθ).1 h_dim _
    exact ⟨c, congrArg Subtype.val hc⟩
  · rintro ⟨c, rfl⟩
    exact (mem_thetaSpace_iff_isThetaFunction hb).1 (Submodule.smul_mem _ c h_vac)

end StandardSpace

end New
