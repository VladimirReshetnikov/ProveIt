import Lib.Adelic.Unitary.RationalPoints
import Lib.Weil.Construction.FiniteCocycle
import Lib.Weil.Fock.Basic

/-!
# The adelic Weil representation on 𝒮(V) and its theta functional

The adelic Heisenberg datum β = `New.adelicHeisenberg E s` on `𝔸 ^ n`, with vacuum function e =
`New.vacuumFn`, splits into a real and a finite part. The data of the adelic Weil representation
(measure, multiplier Δ and action of the adelic unitary group `New.G E s`) are built as products of
the real and the finite data. For a hermitian space with a point `V` (`New.Space`), the space
`New.𝒮 V`, whose vectors are also called data, is the model `Model (adelicHeisenberg E s)`. It
carries the Heisenberg operators `New.Space.ϱ` (`ρ x` or `heisenbergOp x` on the model), the Weil
representation `New.Space.ω`, the inner product `New.Space.dataInner` (`⟨·, ·⟩`, conjugate linear on
the left) and the vacuum `New.Space.vacElem`. A theta functional is a bounded functional on the
model that is invariant under the rational vectors `New.Space.ratVectors` and normalised;
`New.Space.θ` is a definite choice of one. A vector `f : 𝒮 V` applied to `x` is its theta function
θ(ϱ(x) f), not the integrable function `f.1 x = ⟨ϱ(x) vac, f⟩`.

## Main definitions and results

* `New.adelicSum`: multiplication by the idele `New.WeilData.scaleIdele` identifies complex
  coordinates, indexed by pairs (infinite place, index), times finite adelic vectors with `𝔸 ^ n`.
  The bicharacter and `New.vacuumFn` become products of those of `New.Fock.realHeisenberg` and
  `New.stdLattice.finHeisenberg` (`New.Heisenberg.OrthogonalSum`). This scaling turns the adelic
  Gaussian into the standard one (`New.WeilData.conj_scaleIdele_mul`).
* `New.adelicAction`: the adelic unitary group `New.G` acts on `𝔸 ^ n` by matrices, keeping the
  bicharacter and the measure, and `Δ` satisfies the identity of `New.Heisenberg.MultiplierAction`
  with trivial cocycle.
* `New.Space.omega_rho`, `New.Space.dataInner_omega`, `New.Space.dataInner_vacElem_omega_vacElem`:
  `ω g` takes `ϱ x` to `ϱ (g x)`, keeps the inner product, and has overlap `(conj (Δ g))⁻¹` with the
  vacuum.
* `New.Space.exists_isThetaFunctional`, `New.Space.IsThetaFunctional.eq_smul`: a theta functional
  exists, and every invariant functional is a multiple of it.
* `New.Space.dataInner_eq_quotMean`, `New.Space.hasSum_dataInner`: the inner product as a mean of
  theta functions, and the product of two theta values as a sum of inner products.

Notions from other files:
* `New.adelicHeisenberg`: the Heisenberg datum on adelic n-space with bicharacter β(x,y)=ψ(½ȷ
  h(y,x)), h being the standard hermitian form of signs s and ȷ = −ȷ̄ the element `j` of the Weil
  data.
* `New.Heisenberg.OrthogonalSum`: an isomorphism W₁ × W₂ ≃ W along which the bicharacter and the
  vacuum function of W are the products of those of W₁ and W₂.
* `New.Heisenberg.MultiplierAction`: an action of a group on W that keeps β and the measure, with a
  multiplier Δ that satisfies the cocycle identity of the Weil representation.
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to diag(s) at the infinite places and 1 at the finite places; `New.Space.vecAtPoint` sends
  y in E^n to the adelic vector x⁻¹y.
* `New.Heisenberg.IsVacuum.Model`: the space of integrable v with v(x) = ∫ v(y) β(y,x) e(x−y) dμ(y),
  as a type.

## Relation to the literature

Known; see `Lib.Weil.MixedModel.ZeroTerm` for sources.
-/

noncomputable section

namespace New

/-! ## The adelic Heisenberg datum as sum of its real and finite parts -/

section AdelicSum

open NumberField Matrix WeilData Fock Finset Fintype Prod Complex stdLattice Real

variable (E : Type*) [Field E] [CMType E] [WeilData E]
  {n : Type*} [Fintype n] [DecidableEq n] (s : n → ℤˣ)

/-- At an infinite place `w`, the component κ_w of the idele κ = `scaleIdele E` satisfies
conj κ_w · κ_w · 2π Im(Φ_w ȷ) = 1, where `Φ w` is the embedding of the CM type at `w` and ȷ is the
element `j` of the Weil data. -/
lemma WeilData.conj_scaleIdele_mul (w : InfinitePlace E) :
    starRingEnd ℂ ((scaleIdele E).val.1 w) * (scaleIdele E).val.1 w * (2 * π * (Φ w j).im) = 1 := by
  -- `scaleIdele` is real at `w`, the inverse square root of `2 * π * (Φ w j).im > 0`.
  simpa [val_scaleIdele_fst, field, ← ofReal_pow, pi_pos, im_pos, le_of_lt] using (im_pos w).ne'

/-- The sign function on pairs (infinite place, coordinate) that returns the sign of the
coordinate, ignoring the place. -/
abbrev realSigns : InfinitePlace E × n → ℤˣ := fun p ↦ s p.2

open scoped Classical in
/-- The isomorphism (y,z) ↦ κ·(y,z), κ = `scaleIdele E`, from complex coordinates y (indexed by
pairs (infinite place, index)) times finite adelic vectors z onto 𝔸^n. Along it the bicharacter β of
`adelicHeisenberg E s` and `New.vacuumFn` are the products of the real ones, for the signs
`realSigns E s`, and the finite ones. -/
def adelicSum :
    (adelicHeisenberg E s).OrthogonalSum (realHeisenberg (realSigns E s))
      (stdLattice.finHeisenberg E n)
      vacuumFn where
  -- Join the archimedean and the finite coordinates into adeles, and scale by `scaleIdele`.
  equiv.toAddEquiv :=
    { toFun y i := scaleIdele E * (fun w ↦ y.1 (w, i), y.2 i)
      invFun x := (fun p ↦ ((scaleIdele E)⁻¹ * x p.2).1 p.1, fun i ↦ ((scaleIdele E)⁻¹ * x i).2)
      left_inv y := by simp [-fst_mul, -snd_mul]
      right_inv x := by simp [-fst_mul, -snd_mul]
      map_add' x y := by simp [funext_iff, ← mul_add, -fst_mul, -snd_mul] }
  beta_equiv x y := by
    have conj_j (σ : E →+* ℂ) : -σ j = starRingEnd ℂ (σ j) := by
      simpa [star_j] using map_star_complex σ j
    -- Both sides are a complex exponential times a value of `ψf`. At an infinite place `w`,
    -- `Φ w j` is purely imaginary, and `conj_scaleIdele_mul` cancels `2π Im (Φ w j)` against
    -- `|scaleIdele|²`.
    simp [adelicHeisenberg, realHeisenberg, stdLattice.finHeisenberg, stdAddChar, fourierChar,
      stdForm, signMatrix,
      ← sum_sub_distrib, map_ofNat, ← sum_neg_distrib, re_eq_add_conj, sum_mul, mul_sum, dotProduct,
      mulVec_diagonal, fst_sum, snd_sum, val_scaleIdele_snd, sum_prod_type, sum_div, half,
      selfDualAddChar_apply]
    grind [conj_scaleIdele_mul, im_eq_sub_conj, I_sq]
  vac_equiv y := by
    -- Both sides vanish unless `y.2` is integral; the Gaussians agree by `conj_scaleIdele_mul`.
    simp [vacuumFn, finVac, realVac, neg_div, mul_pow, ← conj_mul', mem_stdLattice,
      ↓sum_prod_type_right, val_scaleIdele_snd, mul_sum, dotProduct, sum_div, half,
        selfDualAddChar_apply]
    grind [conj_scaleIdele_mul, stdLattice.traceOneAdele]

variable {E s}

/-- Along `New.adelicSum` the matrix of `g` acts on the complex coordinates by the block diagonal
matrix `blockU g.1` of its infinite components `g.1 w`, and on the finite adelic vector by its
finite component `g.2`. -/
lemma adeleMatrix_mulVec_adelicSum (g : G E s) (y : (InfinitePlace E × n → ℂ) × (n → 𝔸f E)) :
    g.adeleMatrix *ᵥ (adelicSum E s).equiv y =
      (adelicSum E s).equiv ((blockU g.1).val.val *ᵥ y.1, g.2.val.val *ᵥ y.2) := by
  -- The first case is at the infinite places, the second is the finite component.
  ext <;> simp [adelicSum, mulVec, mul_left_comm, blockDiagonal, dotProduct, fst_sum, snd_sum,
    sum_prod_type, mul_sum]

end AdelicSum

/-!
## Multiplier, vacuum measure and action of the adelic unitary group

* `New.weilMultiplier`: the multiplier `Δ`, the product of the real ones `New.Fock.realMultiplier`
  and the finite one `New.finMultiplier`.
* `New.vacuumMeasure`, `New.isVacuum_vacuumFn`: a Haar measure on `𝔸 ^ n` for which
  `New.vacuumFn` is a vacuum.
* `New.adelicAction`: the action of `New.G E s` by matrices, with multiplier `Δ`.
-/

section AdelicAction

open Matrix MeasureTheory Measure U NumberField Fock Heisenberg G

variable {E : Type*} [Field E] [CMType E] [WeilData E]
  {n : Type*} [Fintype n] [DecidableEq n] {s : n → ℤˣ} (g : G E s)

/-- The multiplier Δ(g) = Δ_f(g_f) ∏_w conj(det d_w) of an element g of the adelic unitary group
`G E s`: the product runs over the infinite places w, d_w is the block of g_w on the coordinates of
sign −1, and Δ_f is `New.finMultiplier`, the multiplier of the action `finAction` on finite adelic
vectors. -/
def weilMultiplier : ℂ := (∏ w : InfinitePlace E, realMultiplier (g.1 w)) * finMultiplier g.2

set_option synthInstance.maxSize 999

/-- The Haar measure on 𝔸^n that is the image of the product of `New.Fock.normalizedVolume` and
`New.latticeMeasure` under the isomorphism `New.adelicSum` from real and finite coordinates. The
isomorphism does not depend on the signs, so the signs `1` are used. -/
def vacuumMeasure : Measure (n → 𝔸 E) :=
  ((normalizedVolume (InfinitePlace E × n)).prod (latticeMeasure E n)).map (adelicSum E 1).equiv
  deriving IsAddHaarMeasure

/-- The function `New.vacuumFn` (Gaussian at infinity times twisted lattice indicator at finite
places) is a vacuum, in the sense of `New.Heisenberg.IsVacuum`, for the bicharacter β of signs s and
the measure `New.vacuumMeasure`: it is the product of a real and a finite vacuum. -/
instance isVacuum_vacuumFn : (adelicHeisenberg E s).IsVacuum vacuumMeasure vacuumFn :=
  (adelicSum E s).isVacuum

section

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] (g : G E s)

/-- The adelic unitary group `G E s` acts on 𝔸^n through `G.toUnitary`, by its matrix. -/
instance : DistribMulAction (G E s) (n → 𝔸 E) := .compHom _ toUnitary.toMonoidHom

@[simp]
lemma smul_eq_adeleMatrix_mulVec (x : n → 𝔸 E) : g • x = g.adeleMatrix *ᵥ x := rfl

instance : ContinuousSMul (G E s) (n → 𝔸 E) := by
  refine ⟨?_⟩
  simp
  fun_prop

end

/-- The continuous, β- and measure-preserving action of the adelic unitary group on 𝔸^n by matrices.
Its multiplier is `New.weilMultiplier`, which satisfies the identity of
`New.Heisenberg.MultiplierAction` with trivial cocycle. -/
@[simps Δ]
def adelicAction : (adelicHeisenberg E s).MultiplierAction vacuumMeasure vacuumFn (G E s) where
  Δ := New.weilMultiplier
  beta_smul := by simp [adelicHeisenberg, adeleMatrix, ↓form_mulVec_mulVec]
  measurePreserving g :=
    -- Along `adelicSum` the action is the product of the real and the finite action.
    MeasurePreserving.of_semiconj ⟨by fun_prop, rfl⟩
      (MeasurePreserving.prod ((realAction (realSigns E s)).measurePreserving (blockU g.1))
        (finAction.measurePreserving g.2))
      (fun y ↦ (adeleMatrix_mulVec_adelicSum g y).symm) (by fun_prop)
  continuous_delta := Continuous.mul (by fun_prop [realMultiplier]) finAction.continuous_delta.snd'
  Δ_one := by simp [New.weilMultiplier, realMultiplier, finMultiplier_eq_one_of_mem]
  Δ_inv := by simp [New.weilMultiplier, realMultiplier, finMultiplier_inv, ← principalMinor_coe_inv]
  cocycle g h := by
    -- Multiply the cocycle identities of the real and of the finite action. Along `adelicSum` the
    -- double integral is the product of the real and the finite one.
    have h_mul := congr_arg₂ (· * ·)
      ((realAction (realSigns E s)).cocycle (blockU g.1) (blockU h.1)) (finAction.cocycle g.2 h.2)
    simpa only [New.weilMultiplier, ← realMultiplier_blockU, ← map_mul, ← map_inv,
      smul_eq_adeleMatrix_mulVec, ← map_add, OrthogonalSum.beta_equiv, realAction,
      (adelicSum E s).integral_eq_integral_prod, adeleMatrix_mulVec_adelicSum,
        OrthogonalSum.vac_equiv,
      ← integral_prod_mul, mul_mul_mul_comm _ _ (_ * _), mul_mul_mul_comm _ (realVac _),
      mul_mul_mul_comm _ (realMultiplier _)] using! h_mul.trans (one_mul 1)

/-- The multiplier of `g⁻¹` is the complex conjugate of the multiplier of `g`. -/
lemma weilMultiplier_inv : weilMultiplier g⁻¹ = starRingEnd ℂ (weilMultiplier g) :=
  adelicAction.Δ_inv g

/-- The multiplier `weilMultiplier g` = Δ_f(g_f) ∏_w conj(det d_w) of `g` in the adelic unitary
group `G E s` does not vanish. Here w runs over the infinite places, d_w is the block of g_w on the
coordinates of sign −1, and Δ_f = `finMultiplier`. It is a factor of the left side of the cocycle
identity. -/
lemma weilMultiplier_ne_zero : weilMultiplier g ≠ 0 := by
  intro h_zero
  simpa [adelicAction_Δ, h_zero] using (adelicAction (s := s)).cocycle g g

end AdelicAction

end New

/-! ## The space 𝒮(V) and its operators -/

namespace New

open NumberField Matrix WeilData Filter Finset Heisenberg Fock IsVacuum Space Equiv Circle
  Complex
open scoped Classical

variable {E : Type*} [Field E] [CMType E] [WeilData E]
  {n : Type _} [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} (V : Space E n s) (x y : n → 𝔸 E)

/-- The Banach space 𝒮(V) of integrable functions c on 𝔸^n with c(x) = ∫ c(y)β(y,x)e(x−y) dy,
under the L¹ norm; it depends only on the signs of V. -/
def 𝒮 (_ : Space E n s) : Type _ := Model (adelicHeisenberg E s)
  deriving NormedAddCommGroup, NormedSpace ℂ, CompleteSpace

namespace Space

/-- The Heisenberg representation y ↦ ϱ(y) of (𝔸^n, β) on the Banach space 𝒮(V). -/
def heisenbergRep : (adelicHeisenberg E s).Rep (𝒮 V) := IsVacuum.heisenbergRep

/-- The Heisenberg operator of an adelic vector `y` on `𝒮 V`. -/
abbrev ϱ : 𝒮 V →L[ℂ] 𝒮 V := V.heisenbergRep.ρ y

/-- The Weil representation: the homomorphism from the adelic unitary group to the bounded operators
on 𝒮(V), ω(g)c = Δ(g) ∫ c(y) ϱ(gy) vac dy, where Δ is `New.weilMultiplier`. -/
def ω : G E s →* 𝒮 V →L[ℂ] 𝒮 V := weilRep adelicAction

/-- The bounded sesquilinear form ⟨c, c′⟩ = ∫ c̄ c′ over 𝔸^n on 𝒮(V), on the underlying integrable
functions, conjugate-linear in the first variable. -/
def dataInner : 𝒮 V →L⋆[ℂ] 𝒮 V →L[ℂ] ℂ := modelInner

/-- The vacuum: the function e (Gaussian times twisted lattice indicator) as an element of 𝒮(V). -/
def vacElem : 𝒮 V := IsVacuum.vacElem

end Space

/-! ### Real and finite coordinates -/

/-- The additive map from complex vectors indexed by pairs (infinite place τ, coordinate i) to 𝔸^n
that multiplies the coordinates at τ by (2π Im τ(ȷ))^(−1/2), ȷ being the element `j` of the Weil
data, and puts zero at the finite places. -/
def realVec : (InfinitePlace E × n → ℂ) →+ n → 𝔸 E :=
  AddMonoidHom.mk' (fun y i ↦ ((scaleIdele E).1.1 * fun w ↦ y (w, i), 0)) <| by
    simp [mul_add, funext_iff]

/-- The archimedean part of an adelic vector y in Fock coordinates: the complex numbers (2π Im
τ(ȷ))^{1/2}·y_{i,τ}, indexed by infinite places τ and coordinates i. -/
def realCoord (p : InfinitePlace E × n) : ℂ := (y p.2).1 p.1 / (scaleIdele E).val.1 p.1

/-- For an adelic vector y, the finite adelic vector with coordinates α⁻¹ times the finite part
of y_i, α the finite idele of the Weil data. -/
abbrev finCoord (i : n) : 𝔸f E := α⁻¹.val * (y i).2

/-- The adelic vector with finite part αx (α the finite idele of the Weil data) and zero real part,
for a finite adelic vector x. -/
def finVec (x : n → 𝔸f E) (i : n) : (InfinitePlace E → ℂ) × 𝔸f E := ((0, α.val * x i) : 𝔸 E)

omit [Fintype n] [DecidableEq n] in
/-- An adelic vector `y` is the real vector of its archimedean coordinates plus its finite part. -/
lemma realVec_realCoord_add : realVec (realCoord y) + (fun i : n ↦ (0, (y i).2)) = y := by
  -- The real part is `κ * (y / κ)` with `κ = scaleIdele E`, and `κ ≠ 0` at every infinite place.
  have h_ne (w : InfinitePlace E) : (scaleIdele E).val.1 w ≠ 0 := by
    grind [conj_scaleIdele_mul]
  ext <;> simp [realVec, realCoord, mul_div_cancel₀ _ (h_ne _)]

/-- Along `adelicSum`, real coordinates `y` with zero finite part give the adelic vector
`realVec y`. -/
@[simp]
lemma adelicSum_real_eq_realVec (s : n → ℤˣ) (y : InfinitePlace E × n → ℂ) :
    (adelicSum E (n := n) s).equiv (y, 0) = realVec y := by
  ext i <;> simp [adelicSum, realVec]

/-- The coercion to `ℂ` of a finite product of elements of the circle is the product of their
coercions. -/
lemma _root_.Circle.coe_prod {ι : Type*} (t : Finset ι) (f : ι → Circle) :
    ((∏ i ∈ t, f i : Circle) : ℂ) = ∏ i ∈ t, (f i : ℂ) :=
  map_prod Circle.coeHom f t

/-- The bicharacter `β` of the adelic Heisenberg datum of signs `s` is the product, over the
coordinates `i`, of the bicharacters of the lines of sign `s i`. -/
lemma adelicHeisenberg_beta_eq_prod :
    (adelicHeisenberg E s).β x y =
      ∏ i : n,
        (adelicHeisenberg E fun _ : Unit ↦ s i).β (fun _ : Unit ↦ x i) fun _ : Unit ↦ y i := by
  -- The character `stdAddChar E` turns the sum over coordinates into a product.
  simp [adelicHeisenberg, stdForm, dotProduct, mulVec_diagonal, mul_sum, AddChar.map_sum_eq_prod,
    Circle.coe_prod]

omit [DecidableEq n] in
/-- The vacuum function of `𝔸^n` is the product, over the coordinates, of the vacuum functions of
the lines. -/
lemma vacuumFn_eq_prod : vacuumFn x = ∏ i : n, vacuumFn fun _ : Unit ↦ x i := by
  -- The indicator, the Gaussian and the character `ψf E` each factor over the coordinates.
  simp [vacuumFn, prod_ite_zero, ← Complex.exp_sum, mul_sum,
    prod_mul_distrib, AddChar.map_sum_eq_prod, Circle.coe_prod]

end New

/-! ## Laws of the Weil representation -/

namespace New.Space

open Matrix ComplexConjugate Heisenberg.IsVacuum

variable {E : Type _} [Field E] [CMType E] [WeilData E]
  {n : Type _} [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} (V : Space E n s) (g : G E s) (x y : n → 𝔸 E) (f f' : 𝒮 V)

lemma dataInner_apply : V.dataInner f f' = modelInner f f' := rfl

/-- Superposition: a bounded linear map `T` from `𝒮 V` to a complex Banach space is determined by
its values on the translates ϱ(y) vac of the vacuum `vacElem`. Specifically, `T f` = ∫ ⟨ϱ(y) vac, f⟩
T(ϱ(y) vac) dy, where ⟨·,·⟩ is `dataInner` and the integral over y ∈ 𝔸^n is taken against
`vacuumMeasure`. That measure is the Haar measure on 𝔸^n given by the product of the normalized
volume on the real coordinates and the lattice measure on the finite coordinates. -/
lemma map_eq_integral_dataInner {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [CompleteSpace Y] (T : 𝒮 V →L[ℂ] Y) :
    T f = ∫ y : n → 𝔸 E, V.dataInner (V.ϱ y V.vacElem) f • T (V.ϱ y V.vacElem) ∂vacuumMeasure := by
  refine (map_eq_integral f T).trans ?_
  congr with y : 1
  exact congrArg (· • T (V.ϱ y V.vacElem)) (modelInner_heisenbergOp_vacElem y f).symm

/-- The Weil representation `(g, f) ↦ ω(g) f` is jointly continuous. -/
@[fun_prop]
lemma continuous_omega : Continuous fun p : G E s × 𝒮 V ↦ V.ω p.1 p.2 := continuous_weilRep ..

/-- The Weil operators intertwine the Heisenberg operators: ω(g)ϱ(x)f = ϱ(gx)ω(g)f for g in G, x
an adelic vector and f in 𝒮(V). -/
lemma omega_rho : V.ω g (V.ϱ x f) = V.ϱ (g.adeleMatrix *ᵥ x) (V.ω g f) := weilRep_heisenbergOp ..

/-- The Heisenberg operators `ϱ x` keep the inner product. -/
lemma dataInner_rho : V.dataInner (V.ϱ x f) (V.ϱ x f') = V.dataInner f f' :=
  modelInner_heisenbergOp ..

/-- The Weil operators `ω g` keep the inner product. -/
lemma dataInner_omega : V.dataInner (V.ω g f) (V.ω g f') = V.dataInner f f' := modelInner_weilRep ..

/-- The inner product is definite: `⟨f, f⟩ = 0` forces `f = 0`. -/
lemma eq_zero_of_dataInner_self {f : 𝒮 V} : V.dataInner f f = 0 → f = 0 :=
  eq_zero_of_modelInner_self

/-- The vacuum has inner square one. -/
lemma dataInner_vacElem_vacElem : V.dataInner V.vacElem V.vacElem = 1 := by
  -- Pairing with the vacuum evaluates the vacuum function at `0`, where it is `1`.
  have h_eval : V.dataInner V.vacElem V.vacElem =
      (Heisenberg.IsVacuum.vacElem : Model (adelicHeisenberg E s)) 0 := modelInner_vacElem ..
  simp [h_eval, vacuumFn]

/-- The Heisenberg matrix coefficient of `vacElem` at `y` is the vacuum function `New.vacuumFn` at
`y`. -/
lemma dataInner_vacElem_rho_vacElem : V.dataInner V.vacElem (V.ϱ y V.vacElem) = vacuumFn y := by
  -- Conjugating swaps the arguments, the reproducing property gives the value of the vacuum
  -- function at `y`, and that function is real. `erw`: the rewrites must see through `V.dataInner`,
  -- `V.ϱ` and `V.vacElem`.
  erw [← conj_modelInner, modelInner_heisenbergOp_vacElem, (adelicSum E s).isVacuum.conj_apply]

/-- For a hermitian space `V` over a CM field `E` with Weil data, and `g` in the adelic unitary
group `G E s`, let `vacElem` be the vacuum vector of `𝒮 V` (a Gaussian times a twisted lattice
indicator). The matrix coefficient ⟨vac, ω(g) vac⟩ (`dataInner`, conjugate-linear in the first
variable) equals (conj Δ(g))⁻¹. Here Δ(g) = Δ_f(g_f) ∏_w conj(det d_w) is the multiplier
`New.weilMultiplier`, with d_w the block of g_w on the coordinates of sign −1. -/
lemma dataInner_vacElem_omega_vacElem :
    V.dataInner V.vacElem (V.ω g V.vacElem) = (conj (weilMultiplier g))⁻¹ := by
  -- Pairing with the vacuum evaluates `ω g vacElem` at `0`.
  have h_eval : V.dataInner V.vacElem (V.ω g V.vacElem) =
      weilRep adelicAction g Heisenberg.IsVacuum.vacElem 0 := modelInner_vacElem ..
  rw [h_eval]
  exact eq_inv_of_mul_eq_one_right (conj_delta_mul_weilRep_vacElem adelicAction g)

/-- The operator norm of `ω g` is at most the norm of the vacuum times `|Δ g|`. -/
lemma norm_omega_le : ‖V.ω g‖ ≤ ‖V.vacElem‖ * ‖weilMultiplier g‖ :=
  norm_weilRep_le adelicAction g

/-- For `g` in the adelic unitary group, the inner product `dataInner` of ω(g) vac with its
translate ϱ(y) ω(g) vac is `vacuumFn` evaluated at the adelic vector g⁻¹y. `vacuumFn` is the adelic
vacuum function: for x it is exp(−π ∑_{i,τ} Im(τȷ)|x_{i,τ}|²) · ψ_f(½c₀ȷ x_f*x_f) when the finite
part x_f lies in αÔ^n, and 0 otherwise. -/
lemma dataInner_omega_vacElem_rho :
    V.dataInner (V.ω g V.vacElem) (V.ϱ y (V.ω g V.vacElem)) = vacuumFn (g⁻¹.adeleMatrix *ᵥ y) := by
  have h_move : V.ϱ y (V.ω g V.vacElem) = V.ω g (V.ϱ (g⁻¹.adeleMatrix *ᵥ y) V.vacElem) := by
    rw [omega_rho, mulVec_mulVec, ← G.adeleMatrix_mul, mul_inv_cancel, G.adeleMatrix_one,
      one_mulVec]
  rw [h_move, dataInner_omega, dataInner_vacElem_rho_vacElem]

/-- The inner product of the vacuum moved by `h` with its image under `ω g` is the inverse of the
conjugate of the multiplier of `h⁻¹ g h`. -/
lemma dataInner_omega_vacElem_omega (h : G E s) :
    V.dataInner (V.ω h V.vacElem) (V.ω g (V.ω h V.vacElem)) =
      (conj (weilMultiplier (h⁻¹ * g * h)))⁻¹ := by
  have h_move : V.ω g (V.ω h V.vacElem) = V.ω h (V.ω (h⁻¹ * g * h) V.vacElem) := by
    simp [← mul_apply_eq_comp, ← map_mul, mul_assoc]
  rw [h_move, dataInner_omega, dataInner_vacElem_omega_vacElem]

/-- Two bounded linear maps from `𝒮 V` to a complex Banach space that agree on `ω g (ϱ y vacElem)`
for one `g` and all adelic `y` are equal. -/
lemma ext_of_vacElem {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    {T T' : 𝒮 V →L[ℂ] Y}
    (h_eq : ∀ y : n → 𝔸 E, T (V.ω g (V.ϱ y V.vacElem)) = T' (V.ω g (V.ϱ y V.vacElem))) :
    T = T' := by
  -- After composing with `ω g` the two maps agree on the translates of the vacuum, hence
  -- everywhere by superposition.
  have h_comp : T ∘L V.ω g = T' ∘L V.ω g := by
    ext f
    simp only [V.map_eq_integral_dataInner f (T ∘L V.ω g),
      V.map_eq_integral_dataInner f (T' ∘L V.ω g), ContinuousLinearMap.comp_apply, h_eq]
  ext f
  have h_inverse : V.ω g (V.ω g⁻¹ f) = f := by
    simp [← mul_apply_eq_comp, ← map_mul]
  have h_apply : T (V.ω g (V.ω g⁻¹ f)) = T' (V.ω g (V.ω g⁻¹ f)) :=
    DFunLike.congr_fun h_comp (V.ω g⁻¹ f)
  rwa [h_inverse] at h_apply

end New.Space

/-!
## Existence and uniqueness of theta functionals

The tool is Fourier analysis on the compact quotient of `𝔸^n` by `Λ = V.ratVectors`, whose
characters are `x ↦ β x (V.vecAtPoint γ) ^ 2`, `γ ∈ E^n` (`New.Space.isDualFamily_beta_sq`).
-/

namespace New.Space

open Matrix WeilData Function MeasureTheory ComplexConjugate ComplexOrder Heisenberg IsVacuum

variable {E : Type*} [Field E] [CMType E] [WeilData E]
  {n : Type*} [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} (V : Space E n s) (ℓ ℓ' θ : Model (adelicHeisenberg E s) →L[ℂ] ℂ)

/-- The rational points of V: the additive subgroup of 𝔸^n of the vectors x⁻¹y, y in E^n, where x is
the point `V.x` of V. -/
noncomputable def ratVectors : AddSubgroup (n → 𝔸 E) := V.vecAtPoint.toAddMonoidHom.range

omit [WeilData E] in
/-- An adelic vector `y` is a rational vector of `V` exactly when `V.x *ᵥ y` has rational
coordinates. -/
lemma mem_ratVectors_iff {y : n → 𝔸 E} : y ∈ V.ratVectors ↔ V.x *ᵥ y ∈ New.ratVectors E n :=
  exists_congr fun _ ↦ inv_smul_eq_iff (g := V.x)

instance : CompactSpace ((n → 𝔸 E) ⧸ V.ratVectors) := by
  -- Multiplication by `V.x⁻¹` carries the lattice `ratVectors E n`, which is cocompact, onto
  -- `V.ratVectors`.
  have e : ((n → 𝔸 E) ⧸ New.ratVectors E n) ≃ₜ ((n → 𝔸 E) ⧸ V.ratVectors) := by
    refine Homeomorph.Quotient.congr (.smul V.x⁻¹) ?_
    simp [QuotientAddGroup.leftRel_eq, mem_ratVectors_iff, mulVec_neg, Units.smul_def, mulVec_add]
  exact e.compactSpace

/-- The rational points of V are isotropic: the bicharacter β of `adelicHeisenberg E s` is `1` on
pairs of them. -/
lemma beta_vecAtPoint_eq_one (x y : n → E) :
    (adelicHeisenberg E s).β (V.vecAtPoint x) (V.vecAtPoint y) = 1 := by
  simp [adelicHeisenberg, stdForm_vecAtPoint, ← map_mul]

/-! ### Invariant functionals and the summation formula -/

/-- A bounded functional ℓ on `Model (adelicHeisenberg E s)` is invariant under the rational
Heisenberg operators: ℓ(ρ(γ)v) = ℓ(v) for all v and all γ in `V.ratVectors`, where ρ(γ) =
`heisenbergOp γ` is the Heisenberg operator of γ. -/
def IsRatInvariant : Prop :=
  ∀ᵉ (γ ∈ V.ratVectors) (v : Model (adelicHeisenberg E s)), ℓ (heisenbergOp γ v) = ℓ v

/-- A theta functional of V: a bounded functional θ on `Model (adelicHeisenberg E s)` such that
(1) θ is invariant under the rational Heisenberg operators (`IsRatInvariant`), and
(2) the mean of |θ(ρ(x) vac)|² over x in 𝔸^n modulo `V.ratVectors` (`quotMean`, for the Haar
probability measure of the quotient) is 1. -/
def IsThetaFunctional : Prop :=
  V.IsRatInvariant θ ∧
  quotMean V.ratVectors (fun x : n → 𝔸 E ↦
    θ (heisenbergOp x IsVacuum.vacElem) * conj (θ (heisenbergOp x IsVacuum.vacElem))) = 1

variable {V ℓ ℓ' θ}

lemma IsThetaFunctional.isRatInvariant (h : V.IsThetaFunctional θ) : V.IsRatInvariant θ := h.1

/-- For a theta functional θ, the mean of |θ(ρ(x) vac)|² over 𝔸^n modulo the rational points
is 1. -/
lemma IsThetaFunctional.quotMean_eq_one (h : V.IsThetaFunctional θ) :
    quotMean V.ratVectors (fun x : n → 𝔸 E ↦
      θ (heisenbergOp x IsVacuum.vacElem) * conj (θ (heisenbergOp x IsVacuum.vacElem))) = 1 :=
  h.2

/-- Self-duality of the rational points: let β(x, y) = ψ(½ȷ h(y, x)) be the bicharacter of
`adelicHeisenberg E s`, with h the hermitian form of matrix `stdForm E s`, and let
`V.vecAtPoint γ = x⁻¹γ` for the point `x` of V. Then `γ ↦ (x ↦ β x (V.vecAtPoint γ) ^ 2)` is an
injective homomorphism from `E^n` to the unitary characters of `𝔸^n` trivial on `V.ratVectors`, and
the common kernel of these characters lies in `V.ratVectors`. The square removes the factor `1 / 2`
in `β`. -/
lemma isDualFamily_beta_sq :
    IsDualFamily V.ratVectors fun (γ : n → E) (x : n → 𝔸 E) ↦
      (adelicHeisenberg E s).β x (V.vecAtPoint γ) ^ 2 := by
  -- Throughout, `β x y ^ 2 = stdAddChar (j * star y ⬝ᵥ stdForm *ᵥ x)`.
  have β_sq (x y : n → 𝔸 E) :
      (adelicHeisenberg E s).β x y ^ 2 = stdAddChar E (toAdele j * star y ⬝ᵥ stdForm E s *ᵥ x) := by
    simp [adelicHeisenberg, sq, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← add_mul, ← map_add]
  refine
    { periodic := fun γ ↦ ⟨(adelicHeisenberg E s).cont.curry_left.pow 2, ?_⟩
      add_left := fun γ δ x ↦ by simp [mul_pow, add_right]
      add_right := fun γ x y ↦ by simp [mul_pow, add_left]
      norm_eq_one := fun γ x ↦ by simp [norm_eq_one]
      mem_of_forall_eq_one := fun x hx ↦ ?_
      eq_zero_of_forall_eq_one := fun γ hγ ↦ ?_ }
  · -- Periodicity holds since `V.ratVectors` is isotropic for `β`.
    simp [ratVectors, beta_vecAtPoint_eq_one, add_left]
  · -- Separation: the character of `γ = J⁻¹ *ᵥ single i (star (j⁻¹ * a))` takes the value
    -- `stdAddChar (a * (V.x *ᵥ x) i)` at `x`, so every coordinate of `V.x *ᵥ x` is rational.
    refine V.mem_ratVectors_iff.mpr (mem_ratVectors.mpr fun i ↦
      mem_ratAdeles_of_stdAddChar_eq_one fun a ↦ ?_)
    have h_arg : toAdele j * star (V.vecAtPoint (V.J⁻¹ *ᵥ Pi.single i (star (j⁻¹ * a)))) ⬝ᵥ
        stdForm E s *ᵥ x = toAdele a * (V.x *ᵥ x) i := by
      -- `-mulVec_single` keeps `V.J⁻¹ *ᵥ Pi.single i _` whole, so that `map_J_inv` applies.
      simp [vecAtPoint, comp_def, ← map_mul, ← mul_assoc (toAdele j), j_ne_zero, mul_assoc,
        map_J_inv, star_mulVec_dotProduct, RingHom.map_mulVec, -mulVec_single,
        Pi.apply_single fun _ ↦ toAdele (E := E)]
    have h_test := hx (V.J⁻¹ *ᵥ Pi.single i (star (j⁻¹ * a)))
    rw [β_sq, h_arg] at h_test
    simpa [Circle.ext_iff] using h_test
  · -- Injectivity: testing on `x = stdForm *ᵥ j⁻¹ u w` gives
    -- `stdAddChar (u * star (V.vecAtPoint γ) ⬝ᵥ w) = 1` for all `u`, so `star (V.vecAtPoint γ)` is
    -- orthogonal to all `w`.
    have h_zero : star (V.vecAtPoint γ) = 0 := by
      refine dotProduct_eq_zero _ fun w ↦ eq_zero_of_forall_stdAddChar_eq_one fun u ↦ ?_
      simpa [β_sq, Circle.ext_iff, ← map_mul, ← mul_assoc (toAdele j), j_ne_zero]
        using hγ (stdForm E s *ᵥ toAdele (j⁻¹ : E) • u • w)
    exact V.vecAtPoint_injective (by simpa using h_zero)

/-- For f', f in the model, the series of ⟨f', ρ(x⁻¹γ) f⟩ over the rational vectors γ ∈ E^n is
summable. -/
lemma summable_modelInner (f' f : Model (adelicHeisenberg E s)) :
    Summable fun γ : n → E ↦ modelInner f' (heisenbergOp (V.vecAtPoint γ) f) := by
  -- Superpose `f` from translates of the vacuum; the coefficients of `f'` on these are values of
  -- `f'`, and their sums over translates of the rational points are bounded. `wiener_bound` does
  -- both steps: the sum is at most `M * ‖f‖` times the number of rational points in a compact set
  -- `B`, which is finite.
  have h_vac_ne : (IsVacuum.vacElem : Model (adelicHeisenberg E s)) 0 ≠ 0 := by simp [vacuumFn]
  have h_int : Integrable f' vacuumMeasure := f'.prop.left
  -- The coefficient of `f'` on a translate of the vacuum is a value of `f'`.
  have h_norm (z x : n → 𝔸 E) :
      ‖modelInner f' (heisenbergOp (z + ContinuousAddMonoidHom.id (n → 𝔸 E) x) IsVacuum.vacElem)‖ₑ =
        ‖f' (id z + x)‖ₑ := by
    rw [← conj_modelInner, modelInner_heisenbergOp_vacElem, RCLike.enorm_conj]
    simp only [ContinuousAddMonoidHom.id_toFun, id_eq]
  obtain ⟨B, hB, M, hM⟩ :=
    wiener_bound (modelInner f') h_vac_ne (ContinuousAddMonoidHom.id (n → 𝔸 E)) h_int id h_norm
  -- Wiener's bound, with the rational points `E ^ n` as index group, at `f`.
  have h_bound : ∑' γ : n → E, ‖modelInner f' (heisenbergOp (V.vecAtPoint γ) f)‖ₑ ≤
      (V.vecAtPoint ⁻¹' B).encard * M * ‖f‖ₑ :=
    hM V.vecAtPoint.toAddMonoidHom f
  have h_fin : (V.vecAtPoint ⁻¹' B).Finite :=
    isCovolOneLattice_ratVectors.finite_preimage (hB.preimage_smul V.x⁻¹)
  rw [← h_fin.cast_ncard_eq] at h_bound
  exact .of_enorm (ne_top_of_le_ne_top (by simp [ENNReal.mul_ne_top]) h_bound)

namespace IsRatInvariant

/-- For rationally invariant functionals ℓ', ℓ, the function x ↦ ℓ(ρ(x) f) · conj(ℓ'(ρ(x) f')) is
continuous and periodic under `V.ratVectors`. -/
lemma isContPeriodic (hℓ' : V.IsRatInvariant ℓ') (hℓ : V.IsRatInvariant ℓ)
    (f' f : Model (adelicHeisenberg E s)) :
    IsContPeriodic V.ratVectors fun x : n → 𝔸 E ↦
      ℓ (heisenbergOp x f) * conj (ℓ' (heisenbergOp x f')) := by
  refine ⟨by fun_prop, fun γ hγ x ↦ ?_⟩
  -- `heisenbergOp (γ + x)` is `heisenbergOp γ ∘ heisenbergOp x` up to a factor of modulus one,
  -- which cancels against its conjugate.
  have h_inv (v w : Model (adelicHeisenberg E s)) :
      ℓ (heisenbergOp γ v) * conj (ℓ' (heisenbergOp γ w)) = ℓ v * conj (ℓ' w) := by
    rw [hℓ γ hγ, hℓ' γ hγ]
  simpa [mul_mul_mul_comm, Rep.mul] using h_inv (heisenbergOp x f) (heisenbergOp x f')

/-- For rationally invariant functionals `ℓ'`, `ℓ`, the mean of `ℓ (ρ x f) * conj (ℓ' (ρ x f'))`
over `x` modulo the rational points is `c ⟨f', f⟩`, where `c` is the same mean for
`f' = f = vacElem`. -/
lemma quotMean_eq_mul_modelInner (hℓ' : V.IsRatInvariant ℓ') (hℓ : V.IsRatInvariant ℓ) {c : ℂ}
    (hc : quotMean V.ratVectors (fun x : n → 𝔸 E ↦
      ℓ (heisenbergOp x IsVacuum.vacElem) * conj (ℓ' (heisenbergOp x IsVacuum.vacElem))) = c)
    (f' f : Model (adelicHeisenberg E s)) :
    quotMean V.ratVectors (fun x : n → 𝔸 E ↦ ℓ (heisenbergOp x f) * conj (ℓ' (heisenbergOp x f'))) =
      c * modelInner f' f := by
  -- Apply the uniqueness of the invariant form (`integral_form_eq_mul_modelInner`) to the mean of
  -- the sesquilinear forms `(f', f) ↦ conj (ℓ' (heisenbergOp z f')) * ℓ (heisenbergOp z f)`.
  subst hc
  refine integral_form_eq_mul_modelInner
    (fun z : (n → 𝔸 E) ⧸ V.ratVectors ↦
      (innerSL ℂ).bilinearComp (ℓ' ∘L heisenbergOp z.out) (ℓ ∘L heisenbergOp z.out))
    (fun v w ↦ (hℓ'.isContPeriodic hℓ v w).integrable_out) (fun x v w ↦ ?_) f' f
  -- Invariance: the factors of β have modulus one and cancel, and the mean is translation
  -- invariant.
  simpa [quotMean, mul_mul_mul_comm, Rep.mul] using quotMean_translate (hℓ'.isContPeriodic hℓ v w) x

/-- The summation formula. For rationally invariant functionals `ℓ'`, `ℓ`, let `c` be the mean of
`ℓ (ρ x vacElem) * conj (ℓ' (ρ x vacElem))` over `x` modulo the rational points. Then the series of
`c ⟨f', ρ (V.vecAtPoint γ) f⟩` over `γ ∈ E^n` converges to `ℓ f * conj (ℓ' f')`. -/
lemma hasSum_modelInner (hℓ' : V.IsRatInvariant ℓ') (hℓ : V.IsRatInvariant ℓ) {c : ℂ}
    (hc : quotMean V.ratVectors (fun x : n → 𝔸 E ↦
      ℓ (heisenbergOp x IsVacuum.vacElem) * conj (ℓ' (heisenbergOp x IsVacuum.vacElem))) = c)
    (f' f : Model (adelicHeisenberg E s)) :
    HasSum (fun γ : n → E ↦ c * modelInner f' (heisenbergOp (V.vecAtPoint γ) f))
      (ℓ f * conj (ℓ' f')) := by
  -- Fourier inversion at `0` for the periodic function of `isContPeriodic`. Its Fourier
  -- coefficients come from `quotMean_eq_mul_modelInner` for the pair `f'`, `heisenbergOp γ f`:
  -- commuting `heisenbergOp γ` past `heisenbergOp x` gives the factor `β x γ ^ 2`, and `ℓ` absorbs
  -- `heisenbergOp γ`.
  have h_coeff (γ : n → E) :
      c * modelInner f' (heisenbergOp (V.vecAtPoint γ) f) = quotMean V.ratVectors fun x : n → 𝔸 E ↦
      (adelicHeisenberg E s).β x (V.vecAtPoint γ) ^ 2 *
        (ℓ (heisenbergOp x f) * conj (ℓ' (heisenbergOp x f'))) := by
    rw [← hℓ'.quotMean_eq_mul_modelInner hℓ hc]
    congr with x
    simp [← hℓ (V.vecAtPoint γ) ⟨γ, rfl⟩ (heisenbergOp x f), add_comm, field, mul_assoc, Rep.mul]
  simpa using
    isDualFamily_beta_sq.fourier_inversion (hℓ'.isContPeriodic hℓ f' f)
      ((summable_modelInner f' f).mul_left c) h_coeff 0

end IsRatInvariant

/-- For u in the model, the partial sums of the functionals `f ↦ ⟨u, ρ (V.vecAtPoint γ) f⟩` over
finite sets of γ ∈ E^n converge pointwise to the full series. -/
private lemma tendsto_sum_modelInner_heisenbergOp (V : Space E n s)
    (u : Model (adelicHeisenberg E s)) :
    Filter.Tendsto
      (fun (S : Finset (n → E)) (f : Model (adelicHeisenberg E s)) ↦
        (∑ γ ∈ S, modelInner u ∘L heisenbergOp (V.vecAtPoint γ)) f)
      Filter.atTop (nhds fun f : Model (adelicHeisenberg E s) ↦
        ∑' γ : n → E, modelInner u (heisenbergOp (V.vecAtPoint γ) f)) := by
  -- `HasSum` is, by definition, the convergence of the partial sums over finite sets.
  refine tendsto_pi_nhds.2 fun f ↦ ?_
  simpa [HasSum] using (summable_modelInner u f).hasSum

/-- For u in the model, the bounded functional `f ↦ ∑' γ, ⟨u, ρ (V.vecAtPoint γ) f⟩`, a sum over the
rational vectors γ ∈ E^n. -/
private noncomputable def ratSum (V : Space E n s) (u : Model (adelicHeisenberg E s)) :
    Model (adelicHeisenberg E s) →L[ℂ] ℂ :=
  continuousLinearMapOfTendsto
    (fun S : Finset (n → E) ↦ ∑ γ ∈ S, modelInner u ∘L heisenbergOp (V.vecAtPoint γ))
    (tendsto_sum_modelInner_heisenbergOp V u)

private lemma ratSum_apply (V : Space E n s) (u f : Model (adelicHeisenberg E s)) :
    V.ratSum u f = ∑' γ : n → E, modelInner u (heisenbergOp (V.vecAtPoint γ) f) :=
  rfl

/-- The functional `V.ratSum u` is rationally invariant: translating by a rational vector
reindexes the series, and the factors of β are `1` on rational vectors. -/
private lemma isRatInvariant_ratSum (V : Space E n s) (u : Model (adelicHeisenberg E s)) :
    V.IsRatInvariant (V.ratSum u) := by
  rintro _ ⟨γ, rfl⟩ f
  simpa [ratSum_apply, beta_vecAtPoint_eq_one, Rep.mul] using
    (Equiv.addRight γ).tsum_eq fun δ ↦ modelInner u (heisenbergOp (V.vecAtPoint δ) f)

/-- Every space V has a theta functional: a bounded functional θ on `Model (adelicHeisenberg E s)`,
invariant under the rational Heisenberg operators, with |θ(ρ(x)vac)|² of mean 1 over 𝔸^n modulo the
rational points. -/
lemma exists_isThetaFunctional : ∃ θ : Model (adelicHeisenberg E s) →L[ℂ] ℂ,
  V.IsThetaFunctional θ := by
  -- If no theta functional existed, no invariant functional could be normalised, so all would
  -- vanish. But summing `modelInner u` over the rational points gives an invariant functional
  -- `V.ratSum u`, and `V.ratSum u u` for `u = heisenbergOp (-a) vacElem` has mean `1` in `a`.
  by_contra! h_none
  have h_zero (ℓ : Model (adelicHeisenberg E s) →L[ℂ] ℂ) (hℓ : V.IsRatInvariant ℓ)
      (u : Model (adelicHeisenberg E s)) : ℓ u = 0 := by
    -- The mean that normalises `ℓ` is nonnegative, so it is `r * star r` for some `r`.
    have h_mean_nonneg : 0 ≤ quotMean V.ratVectors
        (fun x : n → 𝔸 E ↦ ℓ (heisenbergOp x IsVacuum.vacElem) * conj
          (ℓ (heisenbergOp x IsVacuum.vacElem))) :=
      integral_nonneg fun q ↦ mul_star_self_nonneg (ℓ (heisenbergOp q.out IsVacuum.vacElem))
    obtain ⟨r, hr⟩ := CStarAlgebra.nonneg_iff_eq_mul_star_self.mp h_mean_nonneg
    by_cases hr0 : r = 0
    · -- By the summation formula with constant `0`, `ℓ u * conj (ℓ u) = 0`.
      simpa [hr0] using ((hℓ.hasSum_modelInner hℓ hr u u).tsum_eq).symm
    · -- Otherwise `r⁻¹ • ℓ` is a theta functional.
      have h_mean_scaled :
          quotMean V.ratVectors (fun x : n → 𝔸 E ↦
            (r⁻¹ • ℓ) (heisenbergOp x IsVacuum.vacElem) *
              conj ((r⁻¹ • ℓ) (heisenbergOp x IsVacuum.vacElem))) = 1 := by
        simpa [mul_mul_mul_comm r⁻¹, hr, field] using hr0
      exact (h_none (r⁻¹ • ℓ) ⟨fun γ hγ f ↦ by simp [hℓ γ hγ f], h_mean_scaled⟩).elim
  -- `c γ` is the coefficient of the vacuum on its translate by the rational point `γ`.
  let c (γ : n → E) : ℂ :=
    modelInner (H := adelicHeisenberg E s) IsVacuum.vacElem
      (heisenbergOp (V.vecAtPoint γ) IsVacuum.vacElem)
  -- `V.ratSum u` for `u = heisenbergOp (-a) vacElem`, applied to `u`, is a Fourier series in `a`.
  have h_series (a : n → 𝔸 E) :
      ∑' γ : n → E, (adelicHeisenberg E s).β a (V.vecAtPoint γ) ^ 2 * c γ = 0 := by
    have h_term (γ : n → E) :
        (adelicHeisenberg E s).β a (V.vecAtPoint γ) ^ 2 * c γ =
          modelInner (H := adelicHeisenberg E s) (heisenbergOp (-a) IsVacuum.vacElem)
            (heisenbergOp (V.vecAtPoint γ) (heisenbergOp (-a) IsVacuum.vacElem)) := by
      simp [c, field, Rep.mul, add_right, self_eq_one]
    rw [tsum_congr h_term, ← ratSum_apply]
    exact h_zero _ (V.isRatInvariant_ratSum _) _
  -- The mean of this series over `a` is its term at `γ = 0`
  -- (`IsDualFamily.tsum_coeff_eq_quotMean`), which is `modelInner vacElem vacElem = 1`.
  have h_mean : ∑' γ : ({0} : Set (n → E)), c γ = quotMean V.ratVectors
      fun a : n → 𝔸 E ↦ ∑' γ : n → E, (adelicHeisenberg E s).β a (V.vecAtPoint γ) ^ 2 * c γ :=
    isDualFamily_beta_sq.tsum_coeff_eq_quotMean id (fun γ ↦ Set.mem_singleton_iff.symm)
      (summable_modelInner IsVacuum.vacElem IsVacuum.vacElem)
  -- So the mean is 1; but the series vanishes, so it is also 0.
  simp only [h_series, quotMean_const] at h_mean
  simp [c, vacuumFn] at h_mean

namespace IsThetaFunctional

/-! ### Uniqueness of the theta functional -/

/-- Let θ be a theta functional of V: a bounded functional on the Heisenberg model
`Model (adelicHeisenberg E s)`, invariant under the Heisenberg operators ρ(γ) for γ in
`V.ratVectors`, and normalised so that the mean of |θ(ρ(x)vac)|² over 𝔸^n modulo `V.ratVectors`
is 1. Then there is a vector u in the model such that every bounded functional ℓ invariant under the
same operators equals ℓ(u) • θ. -/
lemma exists_eq_apply_smul (hθ : V.IsThetaFunctional θ) :
    ∃ u : Model (adelicHeisenberg E s), ∀ ℓ : Model (adelicHeisenberg E s) →L[ℂ] ℂ,
      V.IsRatInvariant ℓ →
      ℓ = ℓ u • θ := by
  -- `θ` is not zero, since `|θ (heisenbergOp x vacElem)|²` has mean `1`; take `u` with `θ u = 1`.
  have h_ne : θ.toLinearMap ≠ 0 := fun h_zero ↦ by
    have h_θ_zero : ∀ v : Model (adelicHeisenberg E s), θ v = 0 := LinearMap.congr_fun h_zero
    simpa [h_θ_zero] using hθ.quotMean_eq_one
  obtain ⟨u, hu : θ u = 1⟩ := θ.toLinearMap.surjective_of_ne_zero h_ne 1
  refine ⟨u, fun ℓ hℓ ↦ ContinuousLinearMap.ext fun f ↦ ?_⟩
  -- The summation formula for the pairs `ℓ, θ` and `θ, θ` gives the same series up to the mean
  -- `c` of `ℓ (ρ x vacElem) * conj (θ (ρ x vacElem))`.
  generalize hc : quotMean V.ratVectors (fun x : n → 𝔸 E ↦
    ℓ (heisenbergOp x IsVacuum.vacElem) * conj (θ (heisenbergOp x IsVacuum.vacElem))) = c
  have h_apply_mul (g : Model (adelicHeisenberg E s)) :
      ℓ g * conj (θ u) = c * (θ g * conj (θ u)) := by
    have h_sum_θ : HasSum (fun γ : n → E ↦ c * modelInner u (heisenbergOp (V.vecAtPoint γ) g))
        (c * (θ g * conj (θ u))) := by
      simpa only [one_mul] using
        (hθ.isRatInvariant.hasSum_modelInner hθ.isRatInvariant hθ.quotMean_eq_one u g).mul_left c
    exact (hθ.isRatInvariant.hasSum_modelInner hℓ hc u g).unique h_sum_θ
  have h_c_eq : ℓ u = c := by simpa [hu] using h_apply_mul u
  calc ℓ f = c * θ f := by simpa [hu] using h_apply_mul f
    _ = (ℓ u • θ) f := by simp [h_c_eq]

/-- If θ is a theta functional of V, every bounded functional ℓ on `Model (adelicHeisenberg E s)`
invariant under the Heisenberg operators ρ(γ), γ a rational point of V, is a complex multiple of
θ. -/
lemma eq_smul (hθ : V.IsThetaFunctional θ) (hℓ : V.IsRatInvariant ℓ) : ∃ c : ℂ, ℓ = c • θ := by
  obtain ⟨u, hu⟩ := hθ.exists_eq_apply_smul
  exact ⟨ℓ u, hu ℓ hℓ⟩

/-- If θ is a theta functional of V, a vector `f` of the model is determined by its theta function
`x ↦ θ (ρ x f)` on `𝔸^n`. -/
lemma injective_apply_heisenbergOp (hθ : V.IsThetaFunctional θ) :
    Injective fun (f : Model (adelicHeisenberg E s)) (x : n → 𝔸 E) ↦ θ (heisenbergOp x f) := by
  refine fun f₁ f₂ h_eq ↦ eq_of_sub_eq_zero (eq_zero_of_modelInner_self ?_)
  -- By `IsRatInvariant.quotMean_eq_mul_modelInner` the square norm of `f₁ - f₂` is the mean of
  -- `|θ (heisenbergOp x (f₁ - f₂))|² = 0`.
  have h_vanish (x : n → 𝔸 E) : θ (heisenbergOp x (f₁ - f₂)) = 0 := by simp [congr_fun h_eq x]
  simpa only [h_vanish, zero_mul, quotMean_const, one_mul] using
    (hθ.isRatInvariant.quotMean_eq_mul_modelInner hθ.isRatInvariant hθ.quotMean_eq_one (f₁ - f₂)
      (f₁ - f₂)).symm

end IsThetaFunctional

end New.Space

/-!
## The theta functional of a space

* `New.lineTheta`, `New.exists_isThetaFunctional_signedSpace`: a theta functional of the standard
  space whose values on translates of the vacuum are products of rank one values; this fixes its
  phase.
-/

namespace New

open NumberField Matrix WeilData Filter Finset Heisenberg Fock IsVacuum Space Equiv Circle
  Complex
open scoped Classical

variable {E : Type*} [Field E] [CMType E] [WeilData E]
  {n : Type _} [Fintype n] [DecidableEq n] {s : n → ℤˣ} (V : Space E n s)

/-! ### The theta functional of the standard space -/

/-- For a sign c and an adele a, the number θ(ϱ(a)vac), θ a chosen theta functional of the
standard line of sign c. -/
def lineTheta (c : ℤˣ) (a : 𝔸 E) : ℂ :=
  (signedSpace E fun _ ↦ c).exists_isThetaFunctional.choose
    (heisenbergOp (fun () ↦ a) IsVacuum.vacElem)

/-- The standard space `signedSpace E s` has a theta functional θ with θ(ϱ(x)vac) = ∏_i
θ_i(ϱ(x_i)vac) for all x in 𝔸^n. Here θ is a bounded functional on the Heisenberg model
`Model (adelicHeisenberg E s)`, invariant under the rational Heisenberg operators and with mean of
|θ(ϱ(x)vac)|² equal to 1. Also, ϱ(x) = `heisenbergOp x`, vac is the vacuum vector, and
θ_i(ϱ(x_i)vac) = `lineTheta (s i) (x i)` for a chosen theta functional θ_i of the line of sign
s_i. -/
lemma exists_isThetaFunctional_signedSpace :
    ∃ θ : Model (adelicHeisenberg E s) →L[ℂ] ℂ,
      (signedSpace E s).IsThetaFunctional θ ∧
      ∀ x : n → 𝔸 E, θ (heisenbergOp x IsVacuum.vacElem) = ∏ i : n, lineTheta (s i) (x i) := by
  -- Take any theta functional θ. The identity θ(f) conj θ(f') = ∑_γ ⟨f', ϱ(γ) f⟩
  -- (`hasSum_modelInner`) factors over the coordinates, so θ(ϱ(x) vac) is proportional to the
  -- product; rescale θ by a factor of modulus 1.
  obtain ⟨θ, h_inv, h_mean⟩ := (signedSpace E s).exists_isThetaFunctional
  let a (x : n → 𝔸 E) : ℂ := θ (heisenbergOp x IsVacuum.vacElem)
  -- On the line of sign `s i`: `v i x = ϱ(x) vacElem`, and `t i x y γ = 1 * ⟨v i y, ϱ(γ) (v i x)⟩`
  -- is the term of the series, the factor `1` being the mean that normalises a theta functional.
  let v (i : n) (x : 𝔸 E) : Model (adelicHeisenberg E fun _ : Unit ↦ s i) :=
    heisenbergOp (fun () ↦ x) IsVacuum.vacElem
  let t (i : n) (x y : 𝔸 E) (γ : E) : ℂ :=
    1 *
      modelInner (v i y) (heisenbergOp ((signedSpace E fun _ : Unit ↦ s i).vecAtPoint fun _ ↦ γ)
        (v i x))
  have h_line (i : n) (x y : 𝔸 E) :
      HasSum (t i x y) (lineTheta (s i) x * star (lineTheta (s i) y)) := by
    obtain ⟨h_inv₁, h_mean₁⟩ :=
      (signedSpace E fun _ : Unit ↦ s i).exists_isThetaFunctional.choose_spec
    exact (piUnique _).symm.hasSum_iff.mpr
      (h_inv₁.hasSum_modelInner h_inv₁ h_mean₁ (v i y) (v i x))
  -- The term of the series of θ at `γ : n → E` is the product of the terms at the `γ i`.
  have h_term (x y : n → 𝔸 E) (γ : n → E) :
      ∏ i, t i (x i) (y i) (γ i) =
        1 * modelInner (H := adelicHeisenberg E s) (heisenbergOp y IsVacuum.vacElem)
          (heisenbergOp ((signedSpace E s).vecAtPoint γ) (heisenbergOp x IsVacuum.vacElem)) := by
    simp [t, v, adelicHeisenberg_beta_eq_prod (s := s), vacuumFn_eq_prod (n := n), signedSpace,
      ← map_inv, vecAtPoint, Rep.mul, prod_mul_distrib, mulVec_diagonal, Pi.smul_def, Pi.add_def,
      Pi.sub_def, Function.comp_def, smul_eq_mul]
  have h_all (x y : n → 𝔸 E) :
      HasSum (fun γ : n → E ↦ ∏ i, t i (x i) (y i) (γ i)) (a x * star (a y)) :=
    (h_inv.hasSum_modelInner h_inv h_mean (heisenbergOp y IsVacuum.vacElem)
      (heisenbergOp x IsVacuum.vacElem)).congr_fun (h_term x y)
  let P (x : n → 𝔸 E) : ℂ := ∏ i, lineTheta (s i) (x i)
  -- Compare the two sums along the boxes Fⁿ, F a finite subset of E.
  have h_prod_eq (x y : n → 𝔸 E) : P x * star (P y) = a x * star (a y) := by
    have h_box : Tendsto (fun F : Finset E ↦ Fintype.piFinset fun _ : n ↦ F) atTop atTop :=
      tendsto_atTop_finset_of_monotone
        (fun F G h_le ↦ Fintype.piFinset_subset _ _ fun _ ↦ h_le) fun γ ↦ ⟨univ.image γ, by simp⟩
    -- Along the boxes, the partial sums of the series of `θ` are products of those of the lines.
    have h_lim_lines : Tendsto (fun F : Finset E ↦ ∏ i, ∑ γ ∈ F, t i (x i) (y i) γ) atTop
        (nhds (∏ i, lineTheta (s i) (x i) * star (lineTheta (s i) (y i)))) :=
      tendsto_finsetProd _ fun i _ ↦ h_line i (x i) (y i)
    have h_lim_boxes : Tendsto (fun F : Finset E ↦ ∏ i, ∑ γ ∈ F, t i (x i) (y i) γ) atTop
        (nhds (a x * star (a y))) :=
      .congr (fun F ↦ sum_prod_piFinset F _) ((h_all x y).comp h_box)
    simpa [P, prod_mul_distrib] using tendsto_nhds_unique h_lim_lines h_lim_boxes
  -- As |a|² has mean 1, a does not vanish identically.
  obtain ⟨y, hy⟩ : ∃ y : n → 𝔸 E, a y ≠ 0 := by
    by_contra! h_zero
    simp_all [a]
  -- By `h_prod_eq`, c = P(y) / a(y) has modulus one (take x = y) and c · a(x) = P(x).
  let c : ℂ := P y / a y
  have hc_norm : c * star c = 1 := by
    rw [star_div₀, div_mul_div_comm, h_prod_eq, div_self (mul_ne_zero hy (star_ne_zero.mpr hy))]
  have hc_mul (x : n → 𝔸 E) : c * a x = P x := by
    -- From `h_prod_eq x y` and `h_prod_eq y y`, dividing by `star (a y) ≠ 0`.
    grind [h_prod_eq x y, h_prod_eq y y, star_ne_zero.mpr hy]
  refine ⟨c • θ, ⟨fun γ hγ f ↦ by simp [h_inv γ hγ f], ?_⟩, hc_mul⟩
  -- |c · a|² = |a|², which has mean 1.
  have h_norm (x : n → 𝔸 E) : c * a x * star (c * a x) = a x * star (a x) := by
    rw [star_mul', mul_mul_mul_comm, hc_norm, one_mul]
  exact (congrArg _ (funext h_norm)).trans h_mean

variable {n' : Type _} [Fintype n'] [DecidableEq n'] {s' : n' → ℤˣ}

namespace Space

/-- Transport of theta functionals. Let `θ` be a theta functional of `V`, and `T` a `σ`-semilinear
map that intertwines the Heisenberg operators along an isomorphism `φ` of adelic vectors. If `φ`
sends the rational vectors of `V₁` to those of `V` and `T vacElem` has inner square one, then
`σ ∘ θ ∘ T` is a theta functional of `V₁`. -/
lemma IsThetaFunctional.comp {V₁ : Space E n' s'} {θ : Model (adelicHeisenberg E s) →L[ℂ] ℂ}
    {σ : ℂ →+* ℂ} [RingHomIsometric σ] [RingHomInvPair σ σ] (h : V.IsThetaFunctional θ)
    (T : Model (adelicHeisenberg E s') →SL[σ] Model (adelicHeisenberg E s))
    (φ : (n' → 𝔸 E) ≃ₜ+ (n → 𝔸 E)) (hφ : ∀ x ∈ V₁.ratVectors, φ x ∈ V.ratVectors)
    (hρ : ∀ (x : n' → 𝔸 E) (v : Model (adelicHeisenberg E s')),
      T (heisenbergOp x v) = heisenbergOp (φ x) (T v))
    (h_norm : modelInner (T IsVacuum.vacElem) (T IsVacuum.vacElem) = 1) :
    V₁.IsThetaFunctional (σ.toSemilinearMap.mkContinuous 1 (by simp) ∘SL θ ∘SL T) := by
  obtain ⟨h_inv, h_mean⟩ := h
  -- `T` carries `heisenbergOp γ` to `heisenbergOp (φ γ)`, and `θ` is invariant under the latter.
  refine ⟨fun γ hγ v ↦ by simp [hρ, h_inv (φ γ) (hφ γ hγ) (T v)], ?_⟩
  -- σ keeps absolute values, and the surjection induced by φ on the quotients keeps means.
  let F (x : n → 𝔸 E) : ℂ :=
    θ (heisenbergOp x (T IsVacuum.vacElem)) * star (θ (heisenbergOp x (T IsVacuum.vacElem)))
  calc
    _ = quotMean V₁.ratVectors fun x ↦ F (φ x) := by simp [F, hρ, mul_conj']
    _ = quotMean V.ratVectors F :=
      quotMean_comp _ (.mk' φ (map_add φ))
        (h_inv.isContPeriodic h_inv (T IsVacuum.vacElem) (T IsVacuum.vacElem)) hφ φ.surjective
        φ.continuous
    -- By `quotMean_eq_mul_modelInner`, the mean of `F` is the inner product of `T vacElem` with
    -- itself.
    _ = 1 := (h_inv.quotMean_eq_mul_modelInner h_inv h_mean _ _).trans (by rw [h_norm, one_mul])

/-! ### The choice of the theta functional of `V` -/

/-- The functional θ₀ = θ_s ∘ ω(g) on 𝒮(V), where θ_s is the theta functional of the standard space
of signs s chosen in `New.exists_isThetaFunctional_signedSpace`, and g is a chosen element carrying
the rational vectors of V to those of the standard space. Such a g exists by Landherr's theorem
(`New.Space.exists_mapsTo_ratVectors`), so the second branch of the definition does not occur. -/
def rawTheta : 𝒮 V →L[ℂ] ℂ :=
  if h : ∃ g : G E s, ∀ γ ∈ V.ratVectors, G.adeleMatrix g *ᵥ γ ∈ (signedSpace E s).ratVectors then
    exists_isThetaFunctional_signedSpace.choose ∘L V.ω h.choose
  else
    V.exists_isThetaFunctional.choose

/-- The theta functional of `V`. It equals `New.Space.rawTheta` (`New.Space.theta_eq_rawTheta`),
since `ϱ 0` is the identity. The factor `ϱ 0` makes `V.θ f = f 0` hold by definition, where
`f x = V.rawTheta (ϱ x f)` is the theta function of `f`. -/
def θ : 𝒮 V →L[ℂ] ℂ := V.rawTheta ∘L V.ϱ 0

lemma theta_eq_rawTheta : V.θ = V.rawTheta := by
  ext
  simp [θ]

/-- The functional `V.rawTheta` is a theta functional of `V`: it is invariant under the rational
points, and |θ(ϱ(x)vac)|² has mean 1 over adelic vectors x modulo these. -/
lemma isThetaFunctional_rawTheta : V.IsThetaFunctional V.rawTheta := by
  -- In the second branch of the definition, `rawTheta` is a theta functional by choice.
  refine dite_mem (s := {θ | V.IsThetaFunctional θ}).2
    ⟨fun h_move ↦ ?_, fun _ ↦ V.exists_isThetaFunctional.choose_spec⟩
  have h_constSMul : ContinuousConstSMul (G E s) (n → 𝔸 E) := ContinuousSMul.continuousConstSMul
  -- Transport the standard theta functional along the chosen g, which acts by ω(g) on data and
  -- by its matrix on adelic vectors. As ω(g) keeps inner products, the image of the vacuum has
  -- inner square one.
  obtain ⟨h_std, -⟩ := (exists_isThetaFunctional_signedSpace (E := E) (s := s)).choose_spec
  let φ : (n → 𝔸 E) ≃ₜ+ (n → 𝔸 E) := .mk' (.smul h_move.choose) (by simp)
  have h_norm : modelInner (weilRep adelicAction h_move.choose IsVacuum.vacElem)
      (weilRep adelicAction h_move.choose IsVacuum.vacElem) = 1 := by simp [vacuumFn]
  exact h_std.comp (φ := φ) _ _ h_move.choose_spec (weilRep_heisenbergOp adelicAction _) h_norm

/-- A vector `f` is read as its theta function: `f x` is θ(ϱ(x) f). -/
instance : FunLike (𝒮 V) (n → 𝔸 E) ℂ where
  coe f x := V.rawTheta (V.ϱ x f)
  coe_injective := V.isThetaFunctional_rawTheta.injective_apply_heisenbergOp

/-! ### Local operators -/

/-- The bounded bilinear map (v, f) ↦ v ⊗ f = ∫ v(y) ϱ(y)f dy, for v in the Fock space, f in
𝒮(V), y over real vectors in Fock coordinates. -/
def integrated : Model (realHeisenberg (realSigns E s)) →L[ℂ] 𝒮 V →L[ℂ] 𝒮 V :=
  (V.heisenbergRep.left (adelicSum E s)).integrated

/-- For a finite adelic vector x, the operator ϱ_f(x) = ψ(½c₀ȷαᾱ x*x) ϱ(αx) on 𝒮(V), α the finite
idele of the Weil data, where c₀ = `traceOneAdele` is integral with c₀ + c̄₀ = 1. The scalar is
`semichar x`; with it these operators represent the lattice Ô^n. -/
def finHeisenbergOp (x : n → 𝔸f E) : 𝒮 V →L[ℂ] 𝒮 V := stdLattice.semichar x • V.ϱ (finVec x)

/-- For a set S of finite places, the operator P^S on 𝒮(V): the mean over y in Ô^n of
`New.Space.finHeisenbergOp` at the part of y above S ∪ S̄. -/
def projOn (S : Set (FinPlace E)) : 𝒮 V →L[ℂ] 𝒮 V :=
  strongIntegral ((latticeMeasure E n).restrict (stdLattice E n)) fun y ↦
    V.finHeisenbergOp (idem S.conjClosure • y)

/-- The real vacuum projection: the bounded operator f ↦ ∫ exp(−|y|²/2) ϱ(y)f dy on 𝒮(V), y over
real vectors in Fock coordinates with measure `New.Fock.normalizedVolume`. -/
abbrev projReal : 𝒮 V →L[ℂ] 𝒮 V := V.integrated Fock.vacVector

/-- For a matrix i over E and spaces V, V' with adelic frames x, x', the adelic matrix x⁻¹ i x'. -/
def ratMap (V' : Space E n' s') (i : Matrix n n' E) : Matrix n n' (𝔸 E) :=
  V.x⁻¹.val * i.map (toAdele (E := E)) * V'.x.val

end Space

end New

/-!
## Laws of theta functions

Convention: applying `f : 𝒮 V` to an adelic vector gives the theta function `f x = θ (ϱ x f)`, while
`f.1 x` is the value of the underlying integrable function.
-/

namespace New.Space

open Matrix ComplexConjugate Heisenberg.IsVacuum

variable {E : Type _} [Field E] [CMType E] [WeilData E]
  {n : Type _} [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} (V : Space E n s) (c : ℂ) (x y : n → 𝔸 E) (f f' : 𝒮 V)

/-- The value of `f : 𝒮 V` at an adelic vector `x` is its theta function at `x`: the theta
functional `V.rawTheta` (see `New.Space.rawTheta`) applied to the Heisenberg translate `V.ϱ x f`. -/
lemma apply_eq_rawTheta : f x = V.rawTheta (V.ϱ x f) := rfl

/-- The theta function of a translate: `(ϱ y f) x = β x y * f (x + y)`. -/
lemma rho_apply : V.ϱ y f x = (adelicHeisenberg E s).β x y * f (x + y) := by
  -- The value `f x` is `V.rawTheta (V.ϱ x f)`; apply `V.rawTheta` to the Heisenberg relation.
  have h_mul : V.ϱ x (V.ϱ y f) = (adelicHeisenberg E s).β x y • V.ϱ (x + y) f :=
    V.heisenbergRep.mul x y f
  simp only [apply_eq_rawTheta, h_mul, map_smul, smul_eq_mul]

lemma theta_apply : V.θ f = f 0 := rfl

lemma add_apply : (f + f') x = f x + f' x := map_add (V.rawTheta ∘L V.ϱ x) f f'

lemma smul_apply : (c • f) x = c * f x := map_smul (V.rawTheta ∘L V.ϱ x) c f

lemma zero_apply : (0 : 𝒮 V) x = 0 := map_zero (V.rawTheta ∘L V.ϱ x)

@[ext]
lemma data_ext {f f' : 𝒮 V} : (∀ x : n → 𝔸 E, f x = f' x) → f = f' := DFunLike.ext f f'

instance : ContinuousEval (𝒮 V) (n → 𝔸 E) ℂ := ⟨V.rawTheta.cont.comp (by fun_prop)⟩

/-- Quasi-periodicity under rational vectors: for γ in E^n with adelic vector γ′ = `V.vecAtPoint γ`
(that is, x⁻¹γ for the point x of `V`) and any adelic x, we have β(γ′, x) f(γ′ + x) = f(x), where
f(x) = θ(ϱ(x)f). Here β(x, y) = ψ(½ȷ h(y, x)) is the bicharacter of the Heisenberg datum
`adelicHeisenberg E s`, and h is the hermitian form with matrix `stdForm E s`. -/
lemma apply_vecAtPoint_add (γ : n → E) (x : n → 𝔸 E) :
    (adelicHeisenberg E s).β (V.vecAtPoint γ) x * f (V.vecAtPoint γ + x) = f x := by
  -- The left side is `V.rawTheta (V.ϱ (V.vecAtPoint γ) (V.ϱ x f))`, and `V.rawTheta` is invariant
  -- under the operators of rational vectors.
  obtain ⟨h_inv, -⟩ := V.isThetaFunctional_rawTheta
  rw [← rho_apply]
  exact h_inv _ ⟨γ, rfl⟩ _

/-- The form ⟨f, f'⟩ on 𝒮(V) equals the mean of conj(f(x)) f'(x) over adelic vectors x modulo
the rational vectors of V, data being read as functions by f(x) = θ(ϱ(x)f). -/
lemma dataInner_eq_quotMean :
    V.dataInner f f' = quotMean V.ratVectors fun x : n → 𝔸 E ↦ f' x * conj (f x) := by
  -- The mean is `c ⟨f, f'⟩`, where `c` is the mean for the vacuum (`quotMean_eq_mul_modelInner`);
  -- here `c = 1`.
  obtain ⟨h_inv, h_mean⟩ := V.isThetaFunctional_rawTheta
  exact ((h_inv.quotMean_eq_mul_modelInner h_inv h_mean f f').trans (one_mul _)).symm

attribute [simp] rho_apply theta_apply add_apply smul_apply zero_apply dataInner_rho dataInner_omega
  dataInner_vacElem_vacElem dataInner_vacElem_rho_vacElem dataInner_vacElem_omega_vacElem

/-- For `f : 𝒮 V` and `y : n → 𝔸 E`, the theta functional `V.θ` takes the Heisenberg translate
`V.ϱ y f` of `f` by `y` to the value `f y`. -/
lemma theta_rho : V.θ (V.ϱ y f) = f y := by simp

/-- A theta function is bounded by the norm of the theta functional times the norm of `f`. -/
lemma norm_apply_le : ‖f x‖ ≤ ‖V.θ‖ * ‖f‖ := by
  simpa [Heisenberg.Rep.norm_map] using V.θ.le_opNorm (V.ϱ x f)

/-- For f, f' in 𝒮(V), the family ⟨f', ϱ(γ)f⟩, γ running over the rational vectors of V, is summable
with sum θ(f) times the complex conjugate of θ(f').

This is Fourier inversion at 0 on the compact group of adelic vectors modulo rational vectors, for
the function x ↦ θ(ϱ(x)f)·conj(θ(ϱ(x)f')), whose Fourier coefficients, suitably indexed, are the
⟨f', ϱ(γ)f⟩. -/
lemma hasSum_dataInner :
    HasSum (fun γ : n → E ↦ V.dataInner f' (V.ϱ (V.vecAtPoint γ) f)) (V.θ f * conj (V.θ f')) := by
  -- This is the summation formula `hasSum_modelInner`, whose constant (the mean for the vacuum) is
  -- `1`.
  obtain ⟨h_inv, h_mean⟩ := V.isThetaFunctional_rawTheta
  rw [theta_eq_rawTheta]
  exact (h_inv.hasSum_modelInner h_inv h_mean f' f).congr_fun fun _ ↦ (one_mul _).symm

end New.Space

end
