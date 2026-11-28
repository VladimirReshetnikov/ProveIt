import Lib.Weil.Construction.AdelicRepresentation
import Lib.Weil.Fock.PolynomialVectors
import Lib.Weil.MixedModel.SchwartzBruhat

/-!
# Vacuum projections and the finite part of the Weil representation

This file studies the projection P^S = `New.Space.projOn` S on the vectors that are vacua above a
set S of finite places. It shows that P^S is a self-adjoint projection and relates it to the
Heisenberg operators and to the Weil representation. It defines the finite part
`New.Space.finitePart` and shows that this subspace is stable under ϱ_f, under the projections and
under the finite unitary group. It also shows that the translates of the vacuum by representatives
modulo Ô^n form an orthonormal spanning family of the finite part.

The Weil representation ω of the adelic unitary group acts on 𝒮(V) = `New.𝒮`, together with the
Heisenberg operators ϱ(y) = `New.Space.ϱ` y. The operators of finite vectors,
ϱ_f = `New.Space.finHeisenbergOp`, are normalised to represent Ô^n = `New.stdLattice`:
ϱ_f(y) = `semichar` y • ϱ(`finVec` y), where finVec y has real part 0 and finite part αy (α the
finite idele of the Weil data) and `semichar` y is a root of unity, and vac = `New.Space.vacElem` is
the vacuum; ψ₀ = `selfDualAddChar E` is a character of 𝔸f E trivial on Ô, `half` is ½, and
`traceOneAdele` t satisfies t + t̄ = 1. For a set S of finite places of E, P^S = `New.Space.projOn`
S is the mean of ϱ_f(`idem` T • y) over y ∈ Ô^n, where `idem` T is the finite adele equal to 1 above
T and 0 elsewhere, for T = S ∪ S̄ = `Set.conjClosure` S; it projects onto the vectors that are vacua
above S. The finite part `New.Space.finitePart` is the span of the ϱ_f-translates of vac.

## Main definitions and results

* `New.Space.omega_projOn`, `New.Space.projOn_omega`: ω(g) commutes with P^S if g is integral on S;
  P^S ω(g) is a scalar on the image of P^S if g is supported above S.
* The finite part is stable under ϱ_f, under the projections `New.Space.projOn` and under the finite
  unitary group (`New.Space.omega_mem_finitePart`). The real vacuum projection `New.Space.projReal`
  fixes it.
* `New.Space.dataInner_finHeisenbergOp_rep_vacElem`, `New.Space.span_finHeisenbergOp_rep_vacElem`:
  the translates of vac by representatives of the classes modulo Ô^n are orthonormal and span the
  finite part.
* `New.Space.exists_eq_smul_omega_vacElem`: a vector of the finite part fixed by the lattice `g Ô^n`
  is a multiple of `ω(g) vacElem`.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to the diagonal matrix of its signs at the infinite places and 1 at the finite places.
* `New.𝒮`: The Banach space 𝒮(V) of integrable functions c on 𝔸^n with c(x) = ∫ c(y)β(y,x)e(x−y) dy,
  under the L¹ norm; β is the adelic bicharacter and e the vacuum function `New.vacuumFn`.
* `New.Space.vacElem`: The vacuum: the function e (Gaussian times twisted lattice indicator) as an
  element of 𝒮(V).

## Relation to the literature

Known; see `Lib.Weil.MixedModel.ZeroTerm` and `Lib.Weil.Fock.OscillatorPair` for sources.
-/

noncomputable section

namespace New.Space

/-!
## Projections on vacua above a set of places and at infinity

* `New.Space.projOn_projOn`, `New.Space.dataInner_projOn`, `New.Space.projOn_val`: P^S is a
  self-adjoint projection and multiplies values by an indicator function.

`New.Space.integrated` v f = v ⊗ f = ∫ v(y) ϱ(y) f over real vectors y, for v in Fock space. In the
statements, `v` is a vector of this Fock space. So is `w`, except where it is bound as a finite
place of E (as in `∀ w ∈ S`).
-/

section Projections

open MeasureTheory Matrix Set AddChar Prod Heisenberg Rep Gf Circle Fock stdLattice _root_.Sum
  OrthogonalSum Set.Sum IsVacuum

variable {E : Type*} [Field E] [CMType E] [WeilData E] {n : Type*} [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} (V : Space E n s) {S : Set (FinPlace E)}
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
  (v : Model (realHeisenberg (realSigns E s))) (w : Model (realHeisenberg (realSigns E s)))
  (f f' : 𝒮 V) (L : 𝒮 V →L[ℂ] Y)

/-- On the real factor of the splitting `adelicSum E s` of adelic vectors into real coordinates (in
ℂ, indexed by infinite place × coordinate) and finite coordinates (n → 𝔸f E), the Heisenberg
representation acts at a real vector `y` by `ϱ (realVec y)`. -/
@[simp]
lemma heisenbergRep_left_rho (y : NumberField.InfinitePlace E × n → ℂ) :
    (V.heisenbergRep.left (adelicSum E s)).ρ y = V.ϱ (realVec y) := by
  simp [left]

/-- On the finite factor of the splitting `adelicSum E s`, the Heisenberg representation acts at a
finite vector `y` by `ϱ (finVec y)`. -/
lemma heisenbergRep_right_rho (y : n → 𝔸f E) :
    (V.heisenbergRep.right (adelicSum E s)).ρ y = V.ϱ (finVec y) :=
  -- The embedding of `(0, y)` has real part `0` and the finite part of `finVec y`.
  congrArg V.ϱ (funext fun _ ↦ Prod.ext (mul_zero _) rfl)

/-- Two Heisenberg operators at finite vectors compose to the operator at the sum, times the
character value `selfDualAddChar E (half * star y ⬝ᵥ x)`. -/
lemma rho_finVec_rho_finVec (x y : n → 𝔸f E) (f : 𝒮 V) :
    V.ϱ (finVec x) (V.ϱ (finVec y) f) =
      selfDualAddChar E (half * star y ⬝ᵥ x) • V.ϱ (finVec (x + y)) f := by
  simp [← heisenbergRep_right_rho, stdLattice.finHeisenberg, mul]

/-- The normalised finite operators `finHeisenbergOp` compose to the operator at the sum, times the
character value `selfDualAddChar E (star traceOneAdele * star y ⬝ᵥ x)`. -/
lemma finHeisenbergOp_finHeisenbergOp (x y : n → 𝔸f E) (f : 𝒮 V) :
    V.finHeisenbergOp x (V.finHeisenbergOp y f) =
      selfDualAddChar E (star traceOneAdele * star y ⬝ᵥ x) • V.finHeisenbergOp (x + y) f := by
  -- Compose with `rho_finVec_rho_finVec`; the scalars agree by `semichar_add`.
  have h_scalar : semichar y * (semichar x * selfDualAddChar E (half * star y ⬝ᵥ x)) =
      selfDualAddChar E (star traceOneAdele * star y ⬝ᵥ x) * semichar (x + y) := by
    rw [← semichar_add]
    ac_rfl
  simp only [finHeisenbergOp, _root_.smul_apply, map_smul, rho_finVec_rho_finVec,
    smul_smul,
    h_scalar]

/-- The operator `finHeisenbergOp x` preserves the inner product `dataInner` of `𝒮 V`. -/
lemma dataInner_finHeisenbergOp (x : n → 𝔸f E) (f f' : 𝒮 V) :
    V.dataInner (V.finHeisenbergOp x f) (V.finHeisenbergOp x f') = V.dataInner f f' := by
  simp [semichar, selfDualAddChar_apply, ← coe_inv_eq_conj, finHeisenbergOp]

omit [DecidableEq n] in
/-- The scalar `semichar x` that normalises `finHeisenbergOp x` is a value in the unit circle, so it
is not zero. -/
@[simp]
lemma semichar_ne_zero (x : n → 𝔸f E) : semichar x ≠ 0 := coe_ne_zero _

/-- For a finite adelic vector `y`, the finite Heisenberg operator ϱ_f(y) = `finHeisenbergOp y`
equals ζ • ϱ(`finVec y`) for some complex number ζ of finite order. Here `finVec y` is the adelic
vector with zero real part and finite part αy, where α is the finite idele in the Weil data
`WeilData E`. -/
lemma exists_isOfFinOrder_finHeisenbergOp_eq_smul_rho (y : n → 𝔸f E) :
    ∃ ζ : ℂ, IsOfFinOrder ζ ∧ V.finHeisenbergOp y = ζ • V.ϱ (finVec y) :=
  ⟨semichar y, isOfFinOrder_semichar y, rfl⟩

/-- For a finite adelic vector y with y* y = 0, the finite Heisenberg operator ϱ_f(y) on 𝒮(V) equals
the Heisenberg operator ϱ of the adelic vector `finVec y = (0, αy)`. This vector has zero real part
and finite part αy, where α is the finite idele of the Weil data. -/
lemma finHeisenbergOp_eq_rho_of_dotProduct_self_eq_zero {y : n → 𝔸f E} (hy : star y ⬝ᵥ y = 0) :
    V.finHeisenbergOp y = V.ϱ (finVec y) := by
  rw [finHeisenbergOp, semichar_eq_one_of_dotProduct_self_eq_zero hy, one_smul]

/-- Two Heisenberg operators commute up to the square of the bicharacter `β` of the adelic
Heisenberg group. -/
lemma rho_swap (x y : n → 𝔸 E) (f : 𝒮 V) :
    V.ϱ x (V.ϱ y f) = (adelicHeisenberg E s).β x y ^ 2 • V.ϱ y (V.ϱ x f) := by
  -- Both sides are multiples of `V.ϱ (x + y) f`, and `β x y * β y x = 1`.
  simp [add_comm, sq, mul_assoc, mul, smul_smul]

/-- A Heisenberg operator at a vector `y` with zero real part commutes with `integrated v`. -/
lemma rho_integrated {y : n → 𝔸 E} (hy : ∀ i : n, (y i).fst = 0) :
    V.ϱ y (V.integrated v f) = V.integrated v (V.ϱ y f) := by
  -- `ϱ y` commutes with the operators of real vectors, as the real part of `y` is zero.
  apply map_integrated
  intro z u
  simp_all [left, adelicHeisenberg, dotProduct, add_comm, stdAddChar, stdForm, realVec, mul,
    mulVec_diagonal, fst_sum, snd_sum]

/-- Acting on the Fock vector by the real Heisenberg operator at `y` is acting on `integrated v f`
by `ϱ (realVec y)`. -/
lemma integrated_realHeisenbergOp (y : NumberField.InfinitePlace E × n → ℂ)
    (v : Model (realHeisenberg (realSigns E s))) (f : 𝒮 V) :
    V.integrated (realHeisenbergOp y v) f = V.ϱ (realVec y) (V.integrated v f) := by
  simp [integrated]

/-- For `v` in the Fock space and `f` in 𝒮(V), `integrated v f` is the vector v ⊗ f = ∫ v(x) ϱ(x)f
dx, with x running over real vectors in Fock coordinates. The Heisenberg operator ϱ(y) of an adelic
vector `y` acts on it factor by factor:
ϱ(y)(v ⊗ f) = (`realHeisenbergOp (realCoord y)` v) ⊗ ϱ(0, y.snd) f. So the real coordinates
`realCoord y` act on `v` by the Fock Heisenberg operator, and the finite part of `y` acts on `f`. -/
lemma rho_integrated_realCoord (y : n → 𝔸 E) (v : Model (realHeisenberg (realSigns E s)))
    (f : 𝒮 V) :
    V.ϱ y (V.integrated v f) =
      V.integrated (realHeisenbergOp (realCoord y) v) (V.ϱ (fun i : n ↦ (0, (y i).snd)) f) := by
  rw [integrated_realHeisenbergOp, ← rho_integrated, mul, realVec_realCoord_add]
  · -- The bicharacter of the real vector `realVec (realCoord y)` and the finite vector is `1`.
    simp [adelicHeisenberg, dotProduct, stdAddChar, stdForm, mulVec_diagonal, fst_sum, snd_sum,
      realVec]
  · exact fun i ↦ rfl

/-- A Heisenberg operator ϱ(y) acts on v ⊗ f through another real datum w and the finite operator
ϱ_f(α⁻¹y_f); the datum w does not depend on f. -/
lemma exists_rho_integrated_eq (y : n → 𝔸 E) (v : Model (realHeisenberg (realSigns E s))) :
    ∃ w : Model (realHeisenberg (realSigns E s)), ∀ f : 𝒮 V,
      V.ϱ y (V.integrated v f) = V.integrated w (V.finHeisenbergOp (finCoord y) f) := by
  refine ⟨(semichar (finCoord y))⁻¹ • realHeisenbergOp (realCoord y) v, fun f ↦ ?_⟩
  simp [rho_integrated_realCoord, finVec.eq_unfold, finHeisenbergOp]

omit [Fintype n] [DecidableEq n] in
/-- A matrix over `𝔸 E` acts on the vector `finVec y` of finite adeles through its finite
components. -/
lemma _root_.New.mulVec_finVec {n₁ : Type*} [Fintype n₁] (m : Matrix n n₁ (𝔸 E)) (y : n₁ → 𝔸f E) :
    m *ᵥ finVec y = finVec ((m.map fun a : 𝔸 E ↦ a.snd) *ᵥ y) := by
  ext i <;> simp [mulVec_eq_sum, Finset.mul_sum, mul_assoc, finVec, fst_sum, snd_sum]

omit [WeilData E] in
/-- The finite components of the matrix of `g : G E s` form the matrix of its finite part. -/
private lemma adeleMatrix_map_snd (g : G E s) :
    (g.adeleMatrix.map fun a : 𝔸 E ↦ a.snd) = (g.snd : Matrix n n (𝔸f E)) :=
  rfl

/-- The Weil representation intertwines the finite Heisenberg operators:
`ω g ∘ finHeisenbergOp x = finHeisenbergOp (g_f x) ∘ ω g`, where `g_f = g.snd` is the finite
component. -/
@[simp]
lemma omega_finHeisenbergOp (g : G E s) (x : n → 𝔸f E) (f : 𝒮 V) :
    V.ω g (V.finHeisenbergOp x f) = V.finHeisenbergOp (g.snd *ᵥ x) (V.ω g f) := by
  simp [semichar, mulVec_finVec, finHeisenbergOp, omega_rho, adeleMatrix_map_snd]

omit [WeilData E] in
@[simp]
lemma idem_univ : idem univ = (1 : 𝔸f E) := by aesop

omit [WeilData E] in
/-- If the finite unitary `g` lies in `GL_n(O_w)` at every place `w` of `S`, then `g x` lies in
`integralBox n S`, the vectors that are integral at the places of `S`, exactly when `x` does. -/
lemma _root_.New.Gf.mulVec_mem_integralBox (g : Gf E n)
    (hg : ∀ w ∈ S, Gf.atPlace w g ∈ localIntGL n w) {x : n → 𝔸f E} :
    (g : Matrix n n (𝔸f E)) *ᵥ x ∈ integralBox n S ↔ x ∈ integralBox n S := by
  -- Membership of `integralBox n S` is a condition at each place of `S`, where `g` is integral.
  -- At a place `w`, integral vectors and the matrix of `atPlace w g` unfold as follows, so that
  -- `simp` brings the fact below into the goal's form, place by place.
  have h_int (w : FinPlace E) (y : n → LocField w) :
      y ∈ intVectors (LocInt w).toSubring n ↔ ∀ i, y i ∈ LocInt w := Iff.rfl
  have h_mat (w : FinPlace E) : ((Gf.atPlace w g : GL n (LocField w)) : Matrix n n (LocField w)) =
      (g : Matrix n n (𝔸f E)).map (evalAt w) := rfl
  simpa [@forall_comm n, ← evalAt_apply, RingHom.map_mulVec, mem_integralBox, idem_mul_mem_Ô,
    h_int, h_mat, mem_LocInt, Function.comp_def] using
    forall₂_congr fun w hw ↦ mulVec_mem_intVectors_iff (hg w hw)

/-- A bounded linear map `L` passes through the mean over the standard lattice that defines
`projOn S`. -/
lemma map_projOn_eq_integral (f : 𝒮 V) :
    L (V.projOn S f) =
      ∫ y : n → 𝔸f E in stdLattice E n, L (V.finHeisenbergOp (idem S.conjClosure • y) f)
        ∂latticeMeasure E n := by
  -- The orbit maps are continuous and the lattice is compact, so the strong integral converges.
  have h_int (u : 𝒮 V) :
      IntegrableOn (fun y ↦ V.finHeisenbergOp (idem S.conjClosure • y) u) (stdLattice E n)
        (latticeMeasure E n) :=
    isCompact_stdLattice.integrableOn _ (show Continuous fun y ↦
      semichar (idem S.conjClosure • y) • V.ϱ (finVec (idem S.conjClosure • y)) u by
        fun_prop [finVec, semichar])
  rw [L.integral_comp_comm (h_int f), projOn, strongIntegral_apply _ _ h_int]

/-- `projOn S f` is the mean of `finHeisenbergOp (idem S.conjClosure • y) f` over `y` in the
standard lattice. -/
lemma projOn_eq_integral (f : 𝒮 V) :
    V.projOn S f =
      ∫ y : n → 𝔸f E in stdLattice E n, V.finHeisenbergOp (idem S.conjClosure • y) f
        ∂latticeMeasure E n :=
  V.map_projOn_eq_integral 1 f

/-! ### The projection above a set of finite places -/

/-- If `L (finHeisenbergOp (idem S.conjClosure • y) f) = F y` for `y` in the standard lattice, then
`L (projOn S f)` is the mean of `F` over the lattice. -/
lemma map_projOn {f : 𝒮 V} {F : (n → 𝔸f E) → Y}
    (hF : ∀ y ∈ stdLattice E n, L (V.finHeisenbergOp (idem S.conjClosure • y) f) = F y) :
    L (V.projOn S f) = ∫ y : n → 𝔸f E in stdLattice E n, F y ∂latticeMeasure E n := by
  rw [map_projOn_eq_integral]
  exact setIntegral_congr_fun isOpen_stdLattice.measurableSet hF

/-- If `y` vanishes above `S ∪ S̄` in every coordinate, then `ϱ y` commutes with `projOn S`. -/
@[simp] lemma projOn_rho {y : n → 𝔸 E} (hy : ∀ i : n, ∀ w ∈ S.conjClosure, (y i).snd w = 0)
    (f : 𝒮 V) :
    V.projOn S (V.ϱ y f) = V.ϱ y (V.projOn S f) := by
  -- `V.ϱ y` commutes with the operators that `projOn S` averages, as `y` vanishes above
  -- `S.conjClosure`.
  have h_zero (i : n) : (y i).snd * idem S.conjClosure = 0 := by
    ext w
    by_cases hw : w ∈ S.conjClosure <;> simp [hy i w, hw]
  have h_comm (x : n → 𝔸f E) :
      V.ϱ y (V.finHeisenbergOp (idem S.conjClosure • x) f) =
        V.finHeisenbergOp (idem S.conjClosure • x) (V.ϱ y f) := by
    simp [adelicHeisenberg, rho_swap _ y, dotProduct, ← mul_rotate, h_zero, finHeisenbergOp,
      stdAddChar, stdForm, mulVec_diagonal, fst_sum, snd_sum, finVec]
  rw [projOn_eq_integral, V.map_projOn _ fun x _ ↦ h_comm x]

@[simp]
lemma projOn_integrated : V.projOn S (V.integrated v f) = V.integrated v (V.projOn S f) := by
  apply map_integrated
  intro y g
  simpa using V.projOn_rho (by simp [realVec]) g

/-! ### Real data and the vacuum -/

/-- Integrating against two real data in turn gives v ⊗ (w ⊗ f) = w(0)·(v ⊗ f). -/
@[simp]
lemma integrated_integrated : V.integrated v (V.integrated w f) = w 0 • V.integrated v f := by
  -- With the restriction `r` to the finite coordinates, `u ⊗ g` is the product of `u` and `r g`,
  -- and a product with first factor `w` restricts to `w 0` times its second factor.
  obtain ⟨r, hr_apply, hr_integrated⟩ := (adelicSum E s).exists_restriction
  have h_product (u : Model (realHeisenberg (realSigns E s))) (g : 𝒮 V) :
      V.integrated u g = (adelicSum E s).tmul u (r g) :=
    hr_integrated u g
  have h_restrict : r (V.integrated w f) = w 0 • r f := by
    ext b
    rw [h_product, hr_apply, tmul_apply, ContinuousAddEquiv.symm_apply_apply, IsVacuum.smul_apply]
  rw [h_product v, h_restrict, h_product v f]
  exact map_smul ((adelicSum E s).tmul v) (w 0) (r f)

/-- For g = (g_∞, g_f), ω(g)(v ⊗ f) = `New.Fock.realWeil`(g_∞)v ⊗ ω(g_f)f, where ⊗ is
`New.Space.integrated`, `New.Fock.realWeil` is the Weil representation on Fock space, and g_∞ is
read as a unitary matrix on the real coordinates. -/
lemma omega_integrated (g : G E s) (v : Model (realHeisenberg (realSigns E s))) (f : 𝒮 V) :
    V.ω g (V.integrated v f) = V.integrated (realWeil (blockU g.fst) v) (V.ω g.snd f) := by
  let tm (a : Model (realHeisenberg (realSigns E s))) (b : Model (finHeisenberg E n)) : 𝒮 V :=
    (adelicSum E s).tmul a b
  -- On a pure tensor `ω k` acts factor by factor, as the multiplier of `k` is a product.
  have h_tmul (k : G E s) a b :
      V.ω k (tm a b) = tm (realWeil (blockU k.fst) a) (weilRep finAction k.snd b) :=
    weilRep_tmul _ adelicAction (realAction _) finAction
      -- The multiplier of `k` is the multiplier of `blockU k.fst` times that of `k.snd`.
      (show weilMultiplier k = realMultiplier (blockU k.fst) * finMultiplier k.snd by
        rw [realMultiplier_blockU, weilMultiplier])
      (adeleMatrix_mulVec_adelicSum k) a b
  have h_pure a b :
      V.ω g (V.integrated v (tm a b)) =
        V.integrated (realWeil (blockU g.fst) v) (V.ω g.snd (tm a b)) := by
    have h_integrated_tm u a b : V.integrated u (tm a b) = a 0 • tm u b :=
      V.integrated_integrated u a _
    simp [h_integrated_tm, h_tmul]
  -- Both sides are bounded in `f`, so test on translates of the vacuum, which are pure tensors.
  suffices h_comp : V.ω g ∘L V.integrated v =
      V.integrated (realWeil (blockU g.fst) v) ∘L V.ω g.snd from DFunLike.congr_fun h_comp f
  refine V.ext_of_vacElem 1 fun y ↦ ?_
  have h_tensor : V.ω 1 (V.ϱ y V.vacElem) =
      tm (heisenbergOp ((adelicSum E s).equiv.symm y).fst IsVacuum.vacElem)
        (heisenbergOp ((adelicSum E s).equiv.symm y).snd IsVacuum.vacElem) := by
    rw [map_one, one_apply_eq_self, vacElem, ← (adelicSum E s).tmul_vacElem]
    -- `erw`: after unfolding `vacElem` the vector lies in `Model (adelicHeisenberg E s)`, which is
    -- `𝒮 V` only up to definitions.
    erw [heisenbergOp_tmul]
  rw [h_tensor]
  exact h_pure _ _

/-- The projection ⟨vac, f⟩ vac on the vacuum is the projection above all finite places followed
by the real vacuum projection. -/
lemma dataInner_vacElem_smul_vacElem :
    V.dataInner V.vacElem f • V.vacElem = V.projReal (V.projOn univ f) := by
  -- The left side is `f 0 • vacElem = ∫ vacElem y • ϱ y f`. As `vacElem` is the tensor product of
  -- the real and the finite vacuum, the integral splits, and its finite part is the mean
  -- `projOn univ`. (`erw`: `𝒮 V` and its vacuum are the model and the tensor-product vacuum only
  -- up to definitions.)
  erw [modelInner_vacElem, ← integrated_eq_smul, vacElem, ← (adelicSum E s).tmul_vacElem,
    integrated_tmul, map_projOn_eq_integral, map_integrated_eq_integral]
  -- By definition, the finite vacuum is `semichar` on the lattice and `0` off it.
  have h_finVac (y) : finVac y = (stdLattice E n : Set (n → 𝔸f E)).indicator semichar y := rfl
  simp [← integral_indicator, indicator_smul_left, ← heisenbergRep_right_rho, finHeisenbergOp,
    isOpen_stdLattice, IsOpen.measurableSet, h_finVac]
  -- What remains is the definition of `projReal`: integrating the real vacuum against the real
  -- Heisenberg operators; a rewrite lemma for it does not match the implicit arguments here.
  rfl

/-- `integrated v` commutes with the finite Heisenberg operators. -/
lemma integrated_finHeisenbergOp (y : n → 𝔸f E) (v : Model (realHeisenberg (realSigns E s)))
    (f : 𝒮 V) :
    V.integrated v (V.finHeisenbergOp y f) = V.finHeisenbergOp y (V.integrated v f) := by
  simp [rho_integrated, finVec.eq_unfold, finHeisenbergOp]

/-- Two finite Heisenberg operators commute up to the character value
`selfDualAddChar E (star y ⬝ᵥ x)`. -/
lemma finHeisenbergOp_comm (x y : n → 𝔸f E) (f : 𝒮 V) :
    V.finHeisenbergOp x (V.finHeisenbergOp y f) =
      selfDualAddChar E (Star.star y ⬝ᵥ x) • V.finHeisenbergOp y (V.finHeisenbergOp x f) := by
  -- The two scalars of `finHeisenbergOp_finHeisenbergOp` differ by this character value, as
  -- `traceOneAdele + star traceOneAdele = 1`.
  have h_arg : star traceOneAdele * star y ⬝ᵥ x =
      star y ⬝ᵥ x + -(traceOneAdele * star y ⬝ᵥ x) := by grind
  -- `-star_mul`: without it, instance search for `StarMul (𝔸f E)` loops under `← star_mul'`.
  simp [finHeisenbergOp_finHeisenbergOp, add_comm, star_dotProduct x, ← star_mul', -star_mul,
    selfDualAddChar_star, ← map_add_eq_mul, smul_smul, h_arg]

/-- The operators ϱ_f(x), x ∈ Ô^n, form a representation of the lattice Ô^n. -/
@[local simp] lemma finHeisenbergOp_add {x y : n → 𝔸f E} (hx : x ∈ stdLattice E n)
    (hy : y ∈ stdLattice E n) (f : 𝒮 V) :
    V.finHeisenbergOp (x + y) f = V.finHeisenbergOp x (V.finHeisenbergOp y f) := by
  -- The scalar of `finHeisenbergOp_finHeisenbergOp` is a value of `selfDualAddChar` at an integral
  -- adele, hence `1`.
  have h_scalar : selfDualAddChar E (star traceOneAdele * star y ⬝ᵥ x) = 1 :=
    selfDualAddChar_eq_one_of_mem (mul_mem (star_mem_Ô traceOneAdele_mem)
      (star_dotProduct_mem hx hy))
  rw [finHeisenbergOp_finHeisenbergOp, h_scalar, one_smul]

/-- If `L (finHeisenbergOp (idem S.conjClosure • y) f)` is a constant `c` for `y` in the standard
lattice, then `L (projOn S f) = c`, as the standard lattice has measure `1` for
`latticeMeasure E n`. -/
lemma map_projOn_eq_const {f : 𝒮 V} {c : Y}
    (hc : ∀ y ∈ stdLattice E n, L (V.finHeisenbergOp (idem S.conjClosure • y) f) = c) :
    L (V.projOn S f) = c := by
  simp [V.map_projOn L hc, Measure.real]

/-- For `y` in the standard lattice, `finHeisenbergOp (idem S.conjClosure • y)` fixes
`projOn S f`. -/
lemma finHeisenbergOp_projOn {y : n → 𝔸f E} (hy : y ∈ stdLattice E n) (f : 𝒮 V) :
    V.finHeisenbergOp (idem S.conjClosure • y) (V.projOn S f) = V.projOn S f := by
  -- The mean over the lattice is invariant under translation by `y`.
  let F (x : n → 𝔸f E) : 𝒮 V := V.finHeisenbergOp (idem S.conjClosure • x) f
  have h_add (x) (hx : x ∈ stdLattice E n) :
      V.finHeisenbergOp (idem S.conjClosure • y) (F x) = F (y + x) := by
    simp only [F, smul_add, V.finHeisenbergOp_add (smul_mem_stdLattice (idem_mem_Ô _) hy)
      (smul_mem_stdLattice (idem_mem_Ô _) hx)]
  calc V.finHeisenbergOp (idem S.conjClosure • y) (V.projOn S f)
      = ∫ x in stdLattice E n, F (y + x) ∂latticeMeasure E n := V.map_projOn _ h_add
    _ = ∫ x in stdLattice E n, F x ∂latticeMeasure E n := setIntegral_add_left_eq_self_of_mem F hy
    _ = V.projOn S f := (V.projOn_eq_integral f).symm

/-- For a hermitian space `V : Space E n s` over the CM field `E` and a set `S` of finite places of
`E`, let `projOn S` be the operator on 𝒮(V) that averages the finite Heisenberg operator
`finHeisenbergOp` at the components above S ∪ S̄ of y, over y ∈ Ô^n. It is self-adjoint for the
sesquilinear form `dataInner` ⟨c, c′⟩ = ∫ c̄ c′ over 𝔸^n, that is ⟨P^S f, f′⟩ = ⟨f, P^S f′⟩. -/
lemma dataInner_projOn : V.dataInner (V.projOn S f) f' = V.dataInner f (V.projOn S f') := by
  -- Projecting the second argument does not change the pairing with `projOn S u`, since
  -- `projOn S u` is fixed by the unitary operators that `projOn S` averages.
  have h_inner (u u' : 𝒮 V) :
      V.dataInner (V.projOn S u) (V.projOn S u') = V.dataInner (V.projOn S u) u' := by
    refine V.map_projOn_eq_const _ fun (y : n → 𝔸f E) (hy : y ∈ stdLattice E n) ↦ ?_
    rw [← V.dataInner_finHeisenbergOp (idem S.conjClosure • y) _ u', V.finHeisenbergOp_projOn hy]
  have h_conj (u u' : 𝒮 V) : starRingEnd ℂ (V.dataInner u u') = V.dataInner u' u :=
    conj_modelInner u u'
  calc V.dataInner (V.projOn S f) f'
      = V.dataInner (V.projOn S f) (V.projOn S f') := (h_inner f f').symm
    _ = starRingEnd ℂ (V.dataInner (V.projOn S f') f) := by rw [← h_inner f' f, h_conj]
    _ = V.dataInner f (V.projOn S f') := h_conj _ _

/-- The value of f at an adelic vector y is the pairing of the translate ϱ(y) vac with f. -/
lemma val_eq_dataInner_rho_vacElem (f : 𝒮 V) (y : n → 𝔸 E) :
    f.val y = V.dataInner (V.ϱ y V.vacElem) f :=
  (modelInner_heisenbergOp_vacElem (x := y) (v := f)).symm

open scoped Classical in
/-- The coefficient ⟨ϱ_f(y) vac, vac⟩ of the vacuum is the indicator of the standard lattice Ô^n
at y. -/
lemma dataInner_finHeisenbergOp_vacElem_vacElem (y : n → 𝔸f E) :
    V.dataInner (V.finHeisenbergOp y V.vacElem) V.vacElem =
      if y ∈ stdLattice E n then 1 else 0 := by
  -- Up to the factor `semichar y` the coefficient is the value of the vacuum at `finVec y`, which
  -- is `semichar y` on the lattice and `0` off it.
  have h_vec : finVec y = (adelicSum E s).equiv (0, y) :=
    funext fun i ↦ Prod.ext (mul_zero _).symm rfl
  have h_value : V.dataInner (V.ϱ (finVec y) V.vacElem) V.vacElem = finVac y :=
    calc V.dataInner (V.ϱ (finVec y) V.vacElem) V.vacElem
        = vacuumFn (finVec y) := (V.val_eq_dataInner_rho_vacElem V.vacElem (finVec y)).symm
      _ = realVac 0 * finVac y := by rw [h_vec, (adelicSum E s).vac_equiv]
      _ = finVac y := by simp [realVac]
  have h_unit : starRingEnd ℂ (semichar y) * semichar y = 1 := by
    simp [semichar, selfDualAddChar_apply, ← coe_inv_eq_conj]
  split_ifs with hy <;>
    simp [finHeisenbergOp, map_smulₛₗ, h_value, finVac_of_mem, finVac_of_notMem, hy, h_unit]

/-- The vacuum is fixed by `finHeisenbergOp y` for every `y` in the standard lattice `Ô^n`. -/
@[simp] lemma finHeisenbergOp_vacElem {V : Space E n s} {y : n → 𝔸f E} (hy : y ∈ stdLattice E n) :
    V.finHeisenbergOp y V.vacElem = V.vacElem := by
  -- The unit vectors `u = ϱ_f(y) vac` and `vac` have inner product `1`, so they are equal.
  set u : 𝒮 V := V.finHeisenbergOp y V.vacElem with hu
  have h_left : V.dataInner u V.vacElem = 1 := by
    rw [hu, V.dataInner_finHeisenbergOp_vacElem_vacElem, ite_eq_left hy]
  have h_conj : starRingEnd ℂ (V.dataInner u V.vacElem) = V.dataInner V.vacElem u :=
    conj_modelInner u V.vacElem
  have h_right : V.dataInner V.vacElem u = 1 := by rw [← h_conj, h_left, map_one]
  have h_self : V.dataInner u u = 1 := by simp [hu, dataInner_finHeisenbergOp]
  refine sub_eq_zero.mp (V.eq_zero_of_dataInner_self ?_)
  simp [h_left, h_right, h_self]

@[simp]
lemma projOn_vacElem : V.projOn S V.vacElem = V.vacElem :=
  V.map_projOn_eq_const 1 fun _ hy ↦
    finHeisenbergOp_vacElem (smul_mem_stdLattice (idem_mem_Ô S.conjClosure) hy)

@[simp]
lemma projReal_vacElem : V.projReal V.vacElem = V.vacElem := by
  simpa using (V.dataInner_vacElem_smul_vacElem V.vacElem).symm

/-- The adjoint of `ω g` for `dataInner` is `ω g⁻¹`. -/
lemma dataInner_omega_left (g : G E s) (f f' : 𝒮 V) :
    V.dataInner (V.ω g f) f' = V.dataInner f (V.ω g⁻¹ f') := by
  simp [← V.dataInner_omega g f, rep_apply_apply]

/-! ### Values of the projection, and the Weil operators on its image -/

omit [DecidableEq n] in
/-- The indicator of the vectors y that are integral at every place of T is the integral of the
character x ↦ ψ₀(y_T* x) over the standard lattice, where y_T = `idem T • y` is the part of y
above T. -/
private lemma boxIndicator_eq_integral_selfDualAddChar (T : Set (FinPlace E)) (y : n → 𝔸f E) :
    boxIndicator n T y = ∫ x : n → 𝔸f E in stdLattice E n,
      selfDualAddChar E (star (idem T • y) ⬝ᵥ x) ∂latticeMeasure E n := by
  rw [integral_selfDualAddChar_stdLattice, boxIndicator]
  -- `y ∈ integralBox n T` is `idem T • y ∈ stdLattice E n` by definition.
  rfl

/-- Let P^S = `New.Space.projOn` S be the projection on vacua above the finite places S ∪ S̄, and
let ϱ_f(y) = `New.Space.finHeisenbergOp` y. If P^S f = f, then P^S ϱ_f(y)f is ϱ_f(y)f when y is
integral at every place of S ∪ S̄ (`New.boxIndicator` is its indicator), and 0 otherwise. -/
lemma projOn_finHeisenbergOp {f : 𝒮 V} (hf_fix : V.projOn S f = f) (y : n → 𝔸f E) :
    V.projOn S (V.finHeisenbergOp y f) =
      boxIndicator n S.conjClosure y • V.finHeisenbergOp y f := by
  -- Moving `finHeisenbergOp y` past the operators that `projOn S` averages leaves the mean of a
  -- character of the lattice, which is `1` or `0` (`integral_selfDualAddChar_stdLattice`).
  rw [boxIndicator_eq_integral_selfDualAddChar, ← integral_smul_const, ← hf_fix]
  refine V.map_projOn 1 fun x hx ↦ ?_
  simp [finHeisenbergOp_comm, V.finHeisenbergOp_projOn hx]

/-- The translate ϱ(y) vac of the vacuum by an adelic vector y is w ⊗ ϱ_f(y') vac for a vector w of
the real Fock space, where y' = `finCoord y` is the finite coordinate of y. -/
lemma exists_rho_vacElem_eq_integrated (y : n → 𝔸 E) :
    ∃ w : Model (realHeisenberg (realSigns E s)),
      V.ϱ y V.vacElem = V.integrated w (V.finHeisenbergOp (finCoord y) V.vacElem) := by
  refine (V.exists_rho_integrated_eq y Fock.vacVector).imp fun w hw ↦ ?_
  -- The vector `integrated vacVector vacElem` is the vacuum.
  simpa using hw V.vacElem

open scoped Classical in
/-- P^S is the operator on 𝒮(V) given by the mean over y in Ô^n of the finite Heisenberg operators
ϱ_f at the part of y above S ∪ S̄. It fixes the translate ϱ_f(y) vac of the vacuum if the finite
vector y is integral at every place of S ∪ S̄ (that is, y lies in `integralBox n S.conjClosure`),
and annihilates it otherwise. -/
lemma projOn_finHeisenbergOp_vacElem (y : n → 𝔸f E) :
    V.projOn S (V.finHeisenbergOp y V.vacElem) =
      if y ∈ integralBox n S.conjClosure then V.finHeisenbergOp y V.vacElem else 0 := by
  rw [V.projOn_finHeisenbergOp V.projOn_vacElem, boxIndicator, ite_smul, one_smul, zero_smul]

/-- The translates ϱ_f(y) vac and ϱ_f(y') vac of the vacuum are orthogonal when y − y' is not in
the standard lattice Ô^n. -/
lemma dataInner_finHeisenbergOp_vacElem_eq_zero_of_sub_notMem {y y' : n → 𝔸f E}
    (h_sub : y - y' ∉ stdLattice E n) :
    V.dataInner (V.finHeisenbergOp y V.vacElem) (V.finHeisenbergOp y' V.vacElem) = 0 := by
  -- Apply the unitary `ϱ_f(-y')` to both vectors: up to scalars they become `ϱ_f(y - y') vac`
  -- and `vac`, whose inner product is `0`.
  have h_shift (z : n → 𝔸f E) : V.finHeisenbergOp (-y') (V.finHeisenbergOp z V.vacElem) =
      selfDualAddChar E (star traceOneAdele * star z ⬝ᵥ -y') •
        V.finHeisenbergOp (z - y') V.vacElem := by
    rw [V.finHeisenbergOp_finHeisenbergOp, neg_add_eq_sub]
  have h_zero : V.dataInner (V.finHeisenbergOp (y - y') V.vacElem) V.vacElem = 0 := by
    rw [V.dataInner_finHeisenbergOp_vacElem_vacElem, ite_eq_right h_sub]
  rw [← V.dataInner_finHeisenbergOp (-y'), h_shift, h_shift, sub_self,
    finHeisenbergOp_vacElem (zero_mem _)]
  simp [h_zero]

open scoped Classical in
/-- Let r choose a representative of each class of finite adelic vectors modulo the standard
lattice Ô^n. Then the translates ϱ_f(r q) vac of the vacuum are orthonormal. -/
lemma dataInner_finHeisenbergOp_rep_vacElem {r : (n → 𝔸f E) ⧸ stdLattice E n → n → 𝔸f E}
    (hr : ∀ q : (n → 𝔸f E) ⧸ stdLattice E n, (r q : (n → 𝔸f E) ⧸ stdLattice E n) = q)
    (q q' : (n → 𝔸f E) ⧸ stdLattice E n) :
    V.dataInner (V.finHeisenbergOp (r q) V.vacElem) (V.finHeisenbergOp (r q') V.vacElem) =
      if q = q' then 1 else 0 := by
  split_ifs with h_eq
  · rw [h_eq, V.dataInner_finHeisenbergOp, dataInner_vacElem_vacElem]
  · refine V.dataInner_finHeisenbergOp_vacElem_eq_zero_of_sub_notMem fun h_mem ↦ h_eq ?_
    rw [← hr q, ← hr q']
    exact QuotientAddGroup.eq_iff_sub_mem.mpr h_mem

/-- P^S = `projOn S` multiplies the value of f at an adelic vector y by the indicator of the
condition that the finite coordinate `finCoord y` of y is integral above S ∪ S̄. -/
lemma projOn_val (f : 𝒮 V) (y : n → 𝔸 E) :
    (V.projOn S f).val y = boxIndicator n S.conjClosure (finCoord y) * f.val y := by
  -- Write `f y` as the inner product of `ϱ y vacElem` with `f` and move `projOn S` to that vector,
  -- where `projOn_finHeisenbergOp` gives the indicator at the finite coordinate `finCoord y`.
  obtain ⟨w, hw⟩ := V.exists_rho_vacElem_eq_integrated y
  rw [val_eq_dataInner_rho_vacElem, V.val_eq_dataInner_rho_vacElem f, ← dataInner_projOn, hw]
  by_cases h_int : finCoord y ∈ integralBox n S.conjClosure <;>
    simp [projOn_finHeisenbergOp, h_int]

lemma projOn_empty (f : 𝒮 V) : V.projOn ∅ f = f := by
  refine IsVacuum.ext ?_
  simp [projOn_val, mem_integralBox, idem_mul_mem_Ô]

/-- The projection for S ∪ S′ is the projection for S after the projection for S′. -/
lemma projOn_union {S' : Set (FinPlace E)} (f : 𝒮 V) :
    V.projOn (S ∪ S') f = V.projOn S (V.projOn S' f) := by
  classical
  refine IsVacuum.ext ?_
  -- By `projOn_val` both sides are `f x` times indicators of integrality conditions above the
  -- places; the condition for `S ∪ S'` is the conjunction of those for `S` and for `S'`.
  -- (`grind` alone does not unfold `boxIndicator`, so `simp` first states them place by place.)
  simp [projOn_val, mem_integralBox, idem_mul_mem_Ô]
  grind

/-- P^S is the operator on 𝒮(V) given by the mean over y in Ô^n of the finite Heisenberg operators
ϱ_f at the part of y above S ∪ S̄. P^S is a projection: P^S(P^S f) = P^S f. -/
lemma projOn_projOn (f : 𝒮 V) : V.projOn S (V.projOn S f) = V.projOn S f := by
  rw [← projOn_union, union_self]

/-- For a set S of finite places, P^S = `projOn S` is the operator on 𝒮(V) that averages
ϱ_f(y) = `finHeisenbergOp y` over y in the lattice Ô^n, keeping only the components of y above S ∪
S̄. Let g be in `G E s`, and suppose that at every place w of S the component of its finite part
lies in GL_n(O_w) = `New.localIntGL`. Then the Weil operator ω(g) commutes with P^S. -/
lemma omega_projOn {g : G E s} (hg : ∀ w ∈ S, g.snd.atPlace w ∈ localIntGL n w) (f : 𝒮 V) :
    V.ω g (V.projOn S f) = V.projOn S (V.ω g f) := by
  -- `g` permutes the operators in the mean: on vectors above `S ∪ S̄` it acts as its component
  -- `k` there, which keeps the lattice and its measure.
  let k : Gf E n := componentOn n S g.snd
  let F (y : n → 𝔸f E) : 𝒮 V := V.finHeisenbergOp (idem S.conjClosure • y) (V.ω g f)
  have hk_int (w : FinPlace E) (_ : w ∈ (univ : Set (FinPlace E))) :
      k.atPlace w ∈ localIntGL n w := by
    rw [atPlace_componentOn]
    split_ifs with hw
    · -- A place of `S.conjClosure` lies in `S` or is conjugate to a place of `S`.
      exact hw.elim (hg w) fun hw_star ↦ atPlace_star_mem_iff.mp (hg (star w) hw_star)
    · exact one_mem _
  have h_lattice : (k : Matrix n n (𝔸f E)).mulVec ⁻¹' stdLattice E n = stdLattice E n := by
    ext y
    simpa [mem_integralBox, mem_stdLattice] using k.mulVec_mem_integralBox hk_int (x := y)
  have h_measure : MeasurePreserving (k : Matrix n n (𝔸f E)).mulVec (latticeMeasure E n)
      (latticeMeasure E n) := finAction.measurePreserving k
  have hk_val : (k : Matrix n n (𝔸f E)) =
      idem S.conjClosure • (g.snd : Matrix n n (𝔸f E)) + (1 - idem S.conjClosure) • 1 := rfl
  have h_move (y : n → 𝔸f E) : (g.snd : Matrix n n (𝔸f E)) *ᵥ idem S.conjClosure • y =
      idem S.conjClosure • (k : Matrix n n (𝔸f E)) *ᵥ y := by
    simp [hk_val, add_mulVec, smul_mulVec, smul_smul, mul_sub, mulVec_smul, idem_mul_self]
  calc V.ω g (V.projOn S f)
      = ∫ y in stdLattice E n, F ((k : Matrix n n (𝔸f E)) *ᵥ y) ∂latticeMeasure E n :=
        V.map_projOn _ fun y _ ↦ by rw [omega_finHeisenbergOp, h_move]
    _ = ∫ y in stdLattice E n, F y ∂latticeMeasure E n := by
        rw [← h_measure.setIntegral_preimage_emb (Homeomorph.smul k).measurableEmbedding F
          (stdLattice E n), h_lattice]
    _ = V.projOn S (V.ω g f) := (V.projOn_eq_integral (V.ω g f)).symm

/-- Let P^S = `projOn S` be the operator on 𝒮(V) that averages the finite Heisenberg operators
ϱ_f(y) = `finHeisenbergOp y` over y in Ô^n, keeping only the components of y above S ∪
S̄ = `S.conjClosure`. Let `L` be a bounded linear map from 𝒮(V) to a Banach space `Y`, and let `f`
be a vector with P^S f = f. If `L` kills every vector v_P ⊗ ϱ_f(y) e = `integrated (polyVector
(realSigns E s) P) (finHeisenbergOp y vacElem)`, then L f = 0; here `P` runs over all complex
polynomials, v_P is the polynomial vector of Fock space, ⊗ is the integrated action v ⊗ f = ∫ v(x)
ϱ(x) f dx, e = `vacElem` is the vacuum (Gaussian times twisted lattice indicator), and `y` runs over
the finite adelic vectors that vanish above S ∪ S̄. -/
lemma map_eq_zero_of_map_integrated_eq_zero {f : 𝒮 V} (hf_fix : V.projOn S f = f) {L : 𝒮 V →L[ℂ] Y}
    (hL : ∀ (P : MvPolynomial (NumberField.InfinitePlace E × n) ℂ) (y : n → 𝔸f E),
      (∀ i : n, ∀ w ∈ S.conjClosure, y i w = 0) →
      L (V.integrated (polyVector (realSigns E s) P) (V.finHeisenbergOp y V.vacElem)) = 0) :
    L f = 0 := by
  -- It suffices that `L ∘ projOn S` kills the translates `ϱ y vacElem` of the vacuum.
  suffices h_zero : L ∘L V.projOn S = 0 by simpa [hf_fix] using DFunLike.congr_fun h_zero f
  refine V.ext_of_vacElem 1 fun (y : n → 𝔸 E) ↦ ?_
  obtain ⟨w, hw⟩ := V.exists_rho_vacElem_eq_integrated y
  -- The Fock vectors `w` for which `L` vanishes form a closed set that contains the dense
  -- polynomial vectors.
  have h_dense (x : n → 𝔸f E) (hx : ∀ i : n, ∀ u ∈ S.conjClosure, x i u = 0) :
      L (V.integrated w (V.finHeisenbergOp x V.vacElem)) = 0 :=
    isClosed_property denseRange_polyVector (L ∘L V.integrated.flip _).isClosed_ker
      (fun P ↦ hL P x hx) w
  -- The projection kills the vector unless the part of `finCoord y` above `S.conjClosure` is
  -- integral. Then that part fixes `vacElem`, and removing it leaves a vector that is zero above
  -- `S.conjClosure`.
  suffices h_box : finCoord y ∈ integralBox n S.conjClosure →
      L (V.integrated w (V.finHeisenbergOp (finCoord y) V.vacElem)) = 0 by
    show L (V.projOn S (V.ω 1 (V.ϱ y V.vacElem))) = 0
    simpa [projOn_finHeisenbergOp, apply_ite, hw] using h_box
  intro hy
  have h_int : idem S.conjClosure • finCoord y ∈ stdLattice E n := hy
  have h_off :
      L (V.integrated w
        (V.finHeisenbergOp (finCoord y + -(idem S.conjClosure • finCoord y)) V.vacElem)) = 0 :=
    h_dense _ fun i u hu ↦ by simp [hu]
  rw [← finHeisenbergOp_vacElem (neg_mem h_int), finHeisenbergOp_finHeisenbergOp, map_smul,
    map_smul, h_off, smul_zero]

/-- Let S be a set of finite places and P^S = `New.Space.projOn` S, the averaging operator on 𝒮(V)
given by the mean over y ∈ Ô^n of the finite Heisenberg operator at the part of y above S ∪ S̄. If
g ∈ G_f is supported on S ∪ S̄ (its component is 1 at all other places) and P^S f = f, then P^S
ω(g)f = Δ_f(g⁻¹)⁻¹ f. Here Δ_f = `New.finMultiplier` is the `glMultiplier` of g viewed as an
invertible matrix. -/
@[local simp] lemma projOn_omega {g : Gf E n} {f : 𝒮 V} (hg : g ∈ supportedOn n S)
    (hf_fix : V.projOn S f = f) :
    V.projOn S (V.ω g f) = (finMultiplier g⁻¹)⁻¹ • f := by
  -- By `map_eq_zero_of_map_integrated_eq_zero` it is enough to take
  -- `f = integrated P (finHeisenbergOp y vacElem)` with `y` zero above `S.conjClosure`; `g` fixes
  -- such `y`.
  refine sub_eq_zero.mp
    (V.map_eq_zero_of_map_integrated_eq_zero (L := V.projOn S * V.ω g - (finMultiplier g⁻¹)⁻¹ • 1)
      hf_fix fun P y hy ↦ ?_)
  rw [_root_.sub_apply, mul_apply_eq_comp, _root_.smul_apply,
    one_apply_eq_self, sub_eq_zero]
  -- `g` is `1` off `S.conjClosure` and `y` is `0` above it.
  have hgy_eq : g *ᵥ y = y := by
    ext i w
    by_cases hw : w ∈ S.conjClosure <;>
      simp_all [Gf.atPlace, mulVec_eq_sum, ← evalAt_apply, GeneralLinearGroup.ext_iff,
        Matrix.one_apply]
  -- Split the projection on `vacElem` into the real part, the part above `S.conjClosure` and the
  -- rest.
  have h_proj : V.dataInner V.vacElem (V.ω g V.vacElem) • V.vacElem =
      V.projReal (V.projOn S (V.projOn S.conjClosureᶜ (V.ω g V.vacElem))) := by
    have h_univ : conjClosure univ = conjClosure (S ∪ S.conjClosureᶜ) := by grind
    rw [dataInner_vacElem_smul_vacElem, ← projOn_union, projOn, projOn, h_univ]
  -- `ω g vacElem` is already a vacuum at the real places and off `S.conjClosure`, so `projOn S`
  -- alone sends it to this multiple of `vacElem`. Apply `integrated P ∘ finHeisenbergOp y`, which
  -- commutes with `projOn S` and `ω g`, to both sides of `h_proj`.
  replace h_proj :=
    congrArg (fun u : 𝒮 V ↦ V.integrated (polyVector (realSigns E s) P) (V.finHeisenbergOp y u))
      h_proj
  simp_all [← omega_projOn, omega_integrated, ← integrated_finHeisenbergOp, weilMultiplier,
    realMultiplier, finMultiplier_inv]
  -- What remains: `projOn S` commutes with `finHeisenbergOp y`, as `y` is `0` above
  -- `S.conjClosure`, and the real vacuum takes the value `1` at `0`.
  show V.integrated (polyVector (realSigns E s) P)
        (V.projOn S (V.finHeisenbergOp y (V.ω (1, g) V.vacElem))) =
      realVac 0 • V.integrated (polyVector (realSigns E s) P)
        (V.finHeisenbergOp y (V.projOn S (V.ω (1, g) V.vacElem)))
  simp_all [finHeisenbergOp, realVac, finVec]

/-- Let `g` be an element of the finite adelic unitary group that lies in K_0 = G_f ∩ GL_n(Ô), the
stabiliser of the standard lattice, and has component 1 at every place outside S ∪ S̄. Let `f` in
𝒮(V) be fixed by P^S = `projOn S`, the mean over y in Ô^n of the finite Heisenberg operators ϱ_f at
the part of y above S ∪ S̄. Then ω(g)f = f. -/
lemma omega_eq_self_of_mem_stdLevel {g : Gf E n} {f : 𝒮 V} (hg : g ∈ supportedOn n S)
    (hf_fix : V.projOn S f = f) (hk : g ∈ stdLevel E n) : V.ω g f = f := by
  -- As `g` is integral at every place, ω(g) commutes with P^S; and Δ_f(g⁻¹) = 1.
  calc V.ω g f = V.ω g (V.projOn S f) := by rw [hf_fix]
    _ = V.projOn S (V.ω g f) := V.omega_projOn (fun w _ ↦ mem_stdLevel_iff.mp hk w) f
    _ = f := by
      rw [V.projOn_omega hg hf_fix, finMultiplier_eq_one_of_mem (inv_mem hk), inv_one, one_smul]

/-- For g in G_f, ω(g)vac = Δ_f(g)·ω(g)P ω(g⁻¹)vac, where P is the projection on vacua at all finite
places and Δ_f = `New.finMultiplier`. -/
lemma omega_vacElem {g : Gf E n} :
    V.ω g V.vacElem = finMultiplier g • V.ω g (V.projOn univ (V.ω ↑g⁻¹ V.vacElem)) := by
  -- `projOn_omega` for g⁻¹ and the set of all places gives P ω(g⁻¹)vac = Δ_f(g)⁻¹ vac.
  have h_proj : V.projOn univ (V.ω ↑g⁻¹ V.vacElem) = (finMultiplier g)⁻¹ • V.vacElem := by
    simp
  simp [h_proj, smul_smul, finMultiplier_ne_zero]

/-- For `x`, `y` in the standard lattice with `g y` also in the lattice, the vector
`finHeisenbergOp (g x) vacElem` does not change when `x` is replaced by `x + y`. -/
lemma finHeisenbergOp_mulVec_add_vacElem {g : Gf E n} {x y : n → 𝔸f E} (hx : x ∈ stdLattice E n)
    (hy : y ∈ stdLattice E n) (hgy : g *ᵥ y ∈ stdLattice E n) :
    V.finHeisenbergOp (g *ᵥ (x + y)) V.vacElem = V.finHeisenbergOp (g *ᵥ x) V.vacElem := by
  -- Apply `ω g` to the additivity of `finHeisenbergOp` on the lattice at the vector
  -- `ω g⁻¹ vacElem`.
  have h_add : V.ω g (V.finHeisenbergOp (x + y) (V.ω ↑g⁻¹ V.vacElem)) =
      V.ω g (V.finHeisenbergOp x (V.finHeisenbergOp y (V.ω ↑g⁻¹ V.vacElem))) := by
    rw [V.finHeisenbergOp_add hx hy]
  simpa [finHeisenbergOp_vacElem hgy, rep_apply_apply, mk_one_one] using h_add

/-- Let `g` be in the finite adelic unitary group `Gf E n`, and `q` a coset of the standard lattice
Ô^n modulo its elements x with gx in Ô^n. Then the vector `finHeisenbergOp (g *ᵥ x) vacElem`, the
operator ϱ_f(gx) applied to the vacuum of 𝒮(V), is the same for every representative `x` of `q` as
for `q.out`. This vector is the term of `omega_vacElem_sum` at `q`. -/
lemma finHeisenbergOp_mulVec_out_vacElem {g : Gf E n}
    {q : stdLattice E n ⧸
      ((stdLattice E n).comap (g : Matrix n n (𝔸f E)).mulVecLin).addSubgroupOf (stdLattice E n)}
    {x : stdLattice E n} (hx : QuotientAddGroup.mk x = q) :
    V.finHeisenbergOp (g *ᵥ q.out.val) V.vacElem = V.finHeisenbergOp (g *ᵥ x.val) V.vacElem := by
  have h_mem : g *ᵥ (-x.val + q.out.val) ∈ stdLattice E n :=
    QuotientAddGroup.eq.mp (hx.trans q.out_eq'.symm)
  rw [← V.finHeisenbergOp_mulVec_add_vacElem x.property
    (add_mem (neg_mem x.property) q.out.property) h_mem, add_neg_cancel_left]

/-- Let `Λ` be the standard lattice Ô^n, let g be in the finite adelic unitary group G_f, and let
Δ_f(g) = `finMultiplier g` be its multiplier. Then the Weil operator applied to the vacuum
e = `vacElem` (Gaussian times twisted lattice indicator) gives ω(g) e = Δ_f(g)/‖Δ_f(g)‖² times the
sum of ϱ_f(g y) e over representatives `y` of the cosets of `Λ ∩ g⁻¹ Λ` in `Λ`, where
ϱ_f = `finHeisenbergOp` is the finite Heisenberg operator. There are finitely many cosets, as `Λ` is
compact and `g⁻¹ Λ` is open, and the terms do not depend on the representatives
(`finHeisenbergOp_mulVec_out_vacElem`). -/
lemma omega_vacElem_sum {g : Gf E n} :
    V.ω g V.vacElem =
      (finMultiplier g / ‖finMultiplier g‖ ^ 2) •
        ∑ᶠ q : stdLattice E n ⧸
            ((stdLattice E n).comap (g : Matrix n n (𝔸f E)).mulVecLin).addSubgroupOf
              (stdLattice E n),
          V.finHeisenbergOp (g *ᵥ q.out.val) V.vacElem := by
  -- By `omega_vacElem` the left side is a multiple of the mean of `F` over the lattice. `F` is
  -- constant on the cosets of `Λ ∩ g⁻¹ Λ`, so the mean is the sum over the cosets times the volume
  -- of `Λ ∩ g⁻¹ Λ`, which is `‖finMultiplier g‖⁻²`.
  let Λ' : AddSubgroup (n → 𝔸f E) := (stdLattice E n).comap (g : Matrix n n (𝔸f E)).mulVecLin
  let F (y : n → 𝔸f E) : 𝒮 V := V.finHeisenbergOp (g *ᵥ y) V.vacElem
  have h_open : IsOpen (Λ' : Set (n → 𝔸f E)) :=
    isOpen_stdLattice.preimage (show Continuous (g : Matrix n n (𝔸f E)).mulVecLin by continuity)
  have h_mean : V.ω g (V.projOn univ (V.ω ↑g⁻¹ V.vacElem)) =
      ∫ y in stdLattice E n, F y ∂latticeMeasure E n := by
    refine V.map_projOn _ fun y _ ↦ ?_
    simp [F, rep_apply_apply, mk_one_one]
  have h_const (x y : stdLattice E n) (hxy : -x.val + y ∈ Λ') : F y = F x := by
    simpa only [add_neg_cancel_left] using
      V.finHeisenbergOp_mulVec_add_vacElem x.property (add_mem (neg_mem x.property) y.property) hxy
  have h_vol :
      (latticeMeasure E n).real (Λ' ∩ stdLattice E n) = (‖finMultiplier g‖ ^ 2)⁻¹ :=
    latticeMeasure_inter_eq_glMultiplier (g : GL n (𝔸f E))
  rw [omega_vacElem, h_mean, setIntegral_eq_finsum isCompact_stdLattice h_open h_const, h_vol]
  simp [F, Λ', div_eq_mul_inv, ← Complex.coe_smul, smul_smul]

end Projections

/-!
## The finite part of the Weil representation

* `New.Space.isLocallyConstant_rho_finVec`, `New.Space.eventually_omega_eq_self`: vectors of the
  finite part are smooth for the finite Heisenberg group and for the finite unitary group.

A point of the unitary group is a pair (infinite, finite), so `V.ω (1, g)` is the action of a finite
point `g`.
-/

section FinitePart

open Matrix Submodule Set stdLattice IsLocallyConstant Filter

variable {E : Type*} [Field E] [CMType E] [WeilData E]
  {n : Type*} [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} {V : Space E n s} {f : 𝒮 V} (x : n → 𝔸f E)

/-- The finite part 𝒮_f: the subspace of 𝒮(V) spanned by the translates of the vacuum under the
finite Heisenberg operators `New.Space.finHeisenbergOp`. -/
noncomputable def finitePart (V : Space E n s) : Submodule ℂ (𝒮 V) :=
  span ℂ (range fun z ↦ V.finHeisenbergOp z V.vacElem)

@[simp]
lemma vacElem_mem_finitePart : V.vacElem ∈ V.finitePart := subset_span ⟨0, by simp⟩

/-- The finite part is stable under the operators ϱ_f(x) of finite adelic vectors x. -/
lemma finHeisenbergOp_mem_finitePart (hf : f ∈ V.finitePart) :
    V.finHeisenbergOp x f ∈ V.finitePart := by
  induction hf using span_induction with
  | mem _ h_gen =>
    obtain ⟨z, rfl⟩ := h_gen
    -- ϱ_f(x) ϱ_f(z) vac is a multiple of the generator ϱ_f(x + z) vac.
    rw [finHeisenbergOp_finHeisenbergOp]
    exact smul_mem _ _ (subset_span ⟨x + z, rfl⟩)
  | zero => simp
  | add f₁ f₂ _ _ h₁ h₂ => simpa using add_mem h₁ h₂
  | smul c f₁ _ h₁ => simpa using smul_mem _ c h₁

variable (V) in
/-- Let r choose a representative of each class of finite adelic vectors modulo the standard
lattice Ô^n. Then the translates ϱ_f(r q) vac of the vacuum span the finite part 𝒮_f. They are
orthonormal by `New.Space.dataInner_finHeisenbergOp_rep_vacElem`. -/
lemma span_finHeisenbergOp_rep_vacElem {r : (n → 𝔸f E) ⧸ stdLattice E n → n → 𝔸f E}
    (hr : ∀ q : (n → 𝔸f E) ⧸ stdLattice E n, (r q : (n → 𝔸f E) ⧸ stdLattice E n) = q) :
    span ℂ (range fun q : (n → 𝔸f E) ⧸ stdLattice E n ↦ V.finHeisenbergOp (r q) V.vacElem) =
      V.finitePart := by
  refine le_antisymm (span_le.mpr ?_) (span_le.mpr ?_)
  · rintro _ ⟨q, rfl⟩
    exact finHeisenbergOp_mem_finitePart (r q) vacElem_mem_finitePart
  · -- A translate `ϱ_f(z) vac` is a multiple of the translate by the representative of `z`, as
    -- the two vectors differ by a lattice vector, which fixes the vacuum.
    rintro _ ⟨z, rfl⟩
    have h_mem : r z - z ∈ stdLattice E n := QuotientAddGroup.eq_iff_sub_mem.mp (hr z)
    have h_rep : V.finHeisenbergOp z V.vacElem =
        selfDualAddChar E (star traceOneAdele * star (r z - z) ⬝ᵥ z) •
          V.finHeisenbergOp (r z) V.vacElem := by
      nth_rw 1 [← finHeisenbergOp_vacElem h_mem]
      rw [finHeisenbergOp_finHeisenbergOp, add_sub_cancel]
    simpa only [SetLike.mem_coe, h_rep] using
      smul_mem _ _ (subset_span (mem_range_self (z : (n → 𝔸f E) ⧸ stdLattice E n)))

/-- The finite part is stable under the Heisenberg operators ϱ(x) of finite adelic vectors x. -/
lemma rho_finVec_mem_finitePart (hf : f ∈ V.finitePart) : V.ϱ (finVec x) f ∈ V.finitePart :=
  (smul_mem_iff _ (semichar_ne_zero _)).mp (finHeisenbergOp_mem_finitePart x hf)

/-- For a hermitian space `V : Space E n s` over a CM field `E` with Weil data, the real vacuum
projection `V.projReal` (the operator f ↦ ∫ exp(−|y|²/2) ϱ(y)f dy over real vectors y in Fock
coordinates) fixes every vector `f` of the finite part `V.finitePart`. The finite part is the
subspace of 𝒮(V) spanned by the translates of the vacuum under the finite Heisenberg operators. -/
@[simp]
lemma projReal_eq_self_of_mem_finitePart (hf : f ∈ V.finitePart) : V.projReal f = f := by
  induction hf using span_induction with
  | mem _ h_gen =>
    obtain ⟨z, rfl⟩ := h_gen
    -- `projReal` commutes with ϱ_f(z) and fixes the vacuum.
    rw [integrated_finHeisenbergOp, projReal_vacElem]
  | zero => simp
  | add f₁ f₂ _ _ h₁ h₂ => rw [map_add, h₁, h₂]
  | smul c f₁ _ h₁ => rw [map_smul, h₁]

/-- For f in the finite part, the map x ↦ ϱ(x)f on finite adelic vectors x is locally constant. -/
lemma isLocallyConstant_rho_finVec (hf_mem : f ∈ V.finitePart) :
    IsLocallyConstant fun x : n → 𝔸f E ↦ V.ϱ (finVec x) f := by
  induction hf_mem using span_induction with
  | zero => simp [of_constant]
  | add f₁ f₂ _ _ h₁ h₂ => simpa [map_add, Pi.add_def] using h₁.add h₂
  | smul c f₁ _ h₁ => simpa [map_smul, Function.comp_def] using h₁.comp fun v : 𝒮 V ↦ c • v
  | mem _ h_gen =>
    obtain ⟨z, rfl⟩ := h_gen
    refine (iff_eventually_eq _).mpr fun x ↦ ?_
    -- For `x - d` in the lattice, `V.finHeisenbergOp (x - d)` fixes the vacuum; composing the three
    -- Heisenberg operators gives a vector independent of `d`, times `selfDualAddChar E` of a
    -- continuous phase.
    let phase (d : n → 𝔸f E) : 𝔸f E :=
      traceOneAdele * half * star (x - d) ⬝ᵥ (x - d) + traceOneAdele * half * star z ⬝ᵥ z +
        half * star (x - d) ⬝ᵥ z + half * star (z + (x - d)) ⬝ᵥ d
    have h_rho_eq (d : n → 𝔸f E) (hd : x - d ∈ stdLattice E n) :
        V.ϱ (finVec d) (V.finHeisenbergOp z V.vacElem) =
          selfDualAddChar E (phase d) • V.ϱ (finVec (x + z)) V.vacElem := by
      nth_rw 1 [← finHeisenbergOp_vacElem hd]
      have h_sum : d + (z + (x - d)) = x + z := by ring
      simp only [finHeisenbergOp, rho_finVec_rho_finVec, semichar, map_smul, _root_.smul_apply,
        smul_smul,
        ← AddChar.map_add_eq_mul, phase, add_assoc, h_sum]
    -- The lattice is open and `selfDualAddChar E` is locally constant.
    have h_phase : IsLocallyConstant fun d : n → 𝔸f E ↦ selfDualAddChar E (phase d) :=
      isLocallyConstant_selfDualAddChar.comp_continuous (by fun_prop)
    filter_upwards [h_phase.eventually_eq x,
      (isOpen_stdLattice.preimage (continuous_sub_left x)).mem_nhds (by simp)] with d hd hd_mem
    rw [h_rho_eq d hd_mem, hd, h_rho_eq x (by simp)]

/-- The finite part is stable under the projection P^S = `projOn` S. -/
lemma projOn_mem_finitePart {S : Set (FinPlace E)} (hf : f ∈ V.finitePart) :
    V.projOn S f ∈ V.finitePart := by
  induction hf using span_induction with
  | mem _ h_gen =>
    obtain ⟨z, rfl⟩ := h_gen
    -- P^S ϱ_f(z) vac is 0 or ϱ_f(z) vac, as P^S fixes the vacuum.
    rw [V.projOn_finHeisenbergOp V.projOn_vacElem z]
    exact smul_mem _ _ (subset_span ⟨z, rfl⟩)
  | zero => simp
  | add f₁ f₂ _ _ h₁ h₂ => simpa using add_mem h₁ h₂
  | smul c f₁ _ h₁ => simpa using smul_mem _ c h₁

/-- The finite part is stable under ω(1, g) for finite adelic points g of the unitary group. -/
lemma omega_mem_finitePart (g : Gf E n) (hf : f ∈ V.finitePart) : V.ω (1, g) f ∈ V.finitePart := by
  induction hf using span_induction with
  | mem _ h_gen =>
    -- `ω (1, g)` turns `finHeisenbergOp z` into `finHeisenbergOp (g z)`, and `ω (1, g) vacElem` is
    -- a combination of generators `finHeisenbergOp (g y) vacElem` (`omega_vacElem_sum`).
    obtain ⟨z, rfl⟩ := h_gen
    have h_gen_mem (y : n → 𝔸f E) : V.finHeisenbergOp y V.vacElem ∈ V.finitePart :=
      subset_span ⟨y, rfl⟩
    rw [omega_finHeisenbergOp, omega_vacElem_sum]
    refine finHeisenbergOp_mem_finitePart _ (smul_mem _ _ ?_)
    exact finsum_induction (fun v : 𝒮 V ↦ v ∈ V.finitePart) (zero_mem _)
      (fun _ _ h₁ h₂ ↦ add_mem h₁ h₂) fun q ↦ h_gen_mem _
  | zero => simp
  | add f₁ f₂ _ _ h₁ h₂ => simpa using add_mem h₁ h₂
  | smul c f₁ _ h₁ => simpa using smul_mem _ c h₁

/-- Let g be in G_f and f in the finite part 𝒮_f. If all operators `New.Space.finHeisenbergOp` at
gy, y in Ô^n, fix f, then f is a complex multiple of ω(g)vac. -/
lemma exists_eq_smul_omega_vacElem {g : Gf E n} (hf : f ∈ V.finitePart)
    (h_fix : ∀ y ∈ stdLattice E n, V.finHeisenbergOp ((g : Matrix n n (𝔸f E)) *ᵥ y) f = f) :
    ∃ c : ℂ, f = c • V.ω (1, g) V.vacElem := by
  -- `f' = ω(g⁻¹) f` is fixed by the lattice and by `V.projReal`, so it is a multiple of the vacuum:
  -- `⟨vacElem, f'⟩ vacElem = projReal (projOn univ f')` by `dataInner_vacElem_smul_vacElem`.
  let f' : 𝒮 V := V.ω (1, g⁻¹) f
  have h_fin : V.projOn univ f' = f' := by
    refine V.map_projOn_eq_const (ContinuousLinearMap.id ℂ (𝒮 V)) fun y hy ↦ ?_
    simpa using congrArg (V.ω (1, g⁻¹)) (h_fix y hy)
  have h_real : V.projReal f' = f' := projReal_eq_self_of_mem_finitePart (omega_mem_finitePart _ hf)
  have h_vac : V.dataInner V.vacElem f' • V.vacElem = f' := by
    rw [dataInner_vacElem_smul_vacElem, h_fin, h_real]
  refine ⟨V.dataInner V.vacElem f', ?_⟩
  calc f = V.ω (1, g) f' := by simp [f', rep_apply_apply, Prod.mk_one_one]
    _ = V.ω (1, g) (V.dataInner V.vacElem f' • V.vacElem) := by rw [h_vac]
    _ = V.dataInner V.vacElem f' • V.ω (1, g) V.vacElem := by rw [map_smul]

/-- Vectors of the finite part are smooth: for f in 𝒮_f, ω(1,k)f = f for all k in a
neighbourhood of 1 in the finite adelic unitary group. -/
lemma eventually_omega_eq_self (hf : f ∈ V.finitePart) :
    ∀ᶠ k : Gf E n in nhds 1, V.ω (1, k) f = f := by
  induction hf using span_induction with
  | zero => simp
  | add f₁ f₂ _ _ h₁ h₂ =>
    filter_upwards [h₁, h₂] with k hk₁ hk₂
    rw [map_add, hk₁, hk₂]
  | smul c f₁ _ h₁ =>
    filter_upwards [h₁] with k hk₁
    rw [map_smul, hk₁]
  | mem _ h_gen =>
    obtain ⟨z, rfl⟩ := h_gen
    -- Near `1`, `k` lies in `stdLevel`, so it fixes the vacuum, and by local constancy `k z` acts
    -- on the vacuum as `z` does. As `k` is unitary, `semichar (k z) = semichar z`.
    have h_const :
        IsLocallyConstant fun k : Gf E n ↦ V.ϱ (finVec ((k : Matrix n n (𝔸f E)) *ᵥ z)) V.vacElem :=
      (isLocallyConstant_rho_finVec V.vacElem_mem_finitePart).comp_continuous (by fun_prop)
    filter_upwards [h_const.eventually_eq 1, isOpen_stdLevel.mem_nhds (by simp)] with k hk_z hk_mem
    have h_supp : k ∈ Gf.supportedOn n (⊤ : Set (FinPlace E)) := by simp
    have h_vac : V.ω (1, k) V.vacElem = V.vacElem :=
      V.omega_eq_self_of_mem_stdLevel h_supp V.projOn_vacElem hk_mem
    rw [omega_finHeisenbergOp, h_vac]
    simp [finHeisenbergOp, semichar, star_mulVec_dotProduct_mulVec, hk_z]

attribute [irreducible] finitePart

end FinitePart

end New.Space

namespace New

end New

end
