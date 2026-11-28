import Lib.Adelic.AutomorphicForms.Basic
import Lib.Adelic.AutomorphicForms.SmoothAlgebraicForms
import Lib.Adelic.Witt.IwasawaDecomposition
import Lib.Weil.Fock.OscillatorPair
import Lib.Weil.MixedModel.ThetaInvariance
import Lib.Weil.Periods.Grading

/-!
# Laws of the Weil action of a pair: translations, real points, levels, rational maps

Let `S`, `T` be hermitian spaces (`New.Space`). A pair `p = (g, h)` of adelic points of their
unitary groups acts on `Hom(S, T)` by `x ↦ h x g⁻¹` (`New.G.onHom`). It acts on the Weil
representation of `Hom(S, T)` by `New.pairWeil S T a b p`, the Weil operator times
`New.pairChar a b p = a (det h) / b (det g)`. The file proves that this action preserves the inner
product. It also describes the action of the real points `(x, y)` of the two unitary groups of signs
`s`, `s'` on the Fock space. It then writes maps, the Heisenberg cocycle and the Heisenberg
operators of `Hom(V, V')` in rational coordinates and defines theta lifts.

## Main definitions and results

* `New.pairWeil_of_mem_Gamma`: rational points (`New.Space.Γ`) act by `f ↦ f (h⁻¹ · g)`.
* `New.pairTheta_mul`, `New.continuous_pairTheta`: the theta kernel `New.pairTheta` satisfies
  `pairTheta S T a b f (p * q) = pairTheta S T a b (pairWeil S T a b q f) p`, and it is continuous.
* `New.realPairWeil γ γ'`: the representation on the Fock space `New.PairFock E s s'` of
  `Hom(S, T)`. It is the oscillator operator of `z ↦ y z x⁻¹` times `det y ^ γ * det x ^ (-γ')` at
  each place.
* `New.pairWeil_integrated`, `New.pairWeil_integrated_all`: on `New.Space.integrated _ v f`, the
  vector `f` with its real vacuum replaced by `v`, real points act on `v` by `New.realPairWeil` and
  finite points act on `f`.
* `New.exists_level_pairWeil`: a datum in the finite part `New.Space.finitePart` of `Hom(S, T)` (the
  span of finite Heisenberg translates of the vacuum) is fixed under `New.pairWeil` by a product of
  open subgroups of the two finite adelic unitary groups.
* `New.Space.IsThetaLift`: a family of maps between spaces of forms computes the theta integrals
  between standard positive spaces.

Notions from other files:
* `New.G`: The adelic unitary group G = G_∞ × G_f for signs s at the infinite places and the
  identity matrix at the finite places.
* `New.GInf E s`: the real points, one complex unitary group `U(diag s)` for each infinite place;
  `New.homSigns s s'` is the sign vector `(i, j) ↦ s' i * s j` of `Hom(S, T)`, and `New.realSigns`
  repeats a sign vector at every infinite place.
* `New.Fock.realWeil`: The Weil representation of U(ε) on the Fock space `𝓕 ε`; its multiplier
  `New.Fock.realMultiplier u` is the conjugate of the determinant of the negative block of u.
* `New.blockDiagAlg ε`: the complex matrices that commute with `diag ε`, that is, the block
  diagonal matrices for the partition of the indices by sign; `New.principalMinor y p` is the
  determinant of the block of `y` on the indices that satisfy `p`.
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to diag(s) at the infinite places and 1 at the finite places; `New.Space.Γ` is the group
  of rational points of its unitary group, inside `New.G`.
* `New.AutChar E`: the continuous characters of the norm-one adeles `U(1)(𝔸)` that are trivial on
  rational points; `a`, `b` are such characters.
* `New.Space.hom`: The space `Hom(S, T)` of `n' × n` matrices, indexed by pairs (row, column);
  `New.matrixToVec` reads a matrix as a vector on these pairs.

## Relation to the literature

Known; see `Lib.Weil.DualPair.ThetaLiftConvergence`, `Lib.Weil.Fock.OscillatorPair`,
`Lib.Weil.CompactLift.DefiniteThetaLift` and `Lib.Weil.Periods.Unfolding` for sources.
-/

noncomputable section

namespace New

/-!
## Basic laws, translation law and continuity of theta kernels

* `New.G.onHom_mulVec`, `New.G.det_onHom`, `New.G.onHom_mem_Gamma`: matrix, determinant and
  rationality of `New.G.onHom p`.
-/

section PairBasic

open Fintype Matrix Prod Kronecker RingHom Space G

variable {E m m' l l' R : Type*} [Field E] [CMType E]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {s : n → ℤˣ} {s' : n' → ℤˣ} (S : Space E n s) (T : Space E n' s') (a b : AutChar E)
  (p : G E s × G E s') (g : G E s)

/-! ### Matrices as vectors on pairs of indices -/

@[simp]
lemma vecToMatrix_matrixToVec (x : Matrix m' m R) : vecToMatrix (matrixToVec x) = x := rfl

@[simp]
lemma matrixToVec_vecToMatrix (y : m' × m → R) : matrixToVec (vecToMatrix y) = y := rfl

@[simp]
lemma matrixToVec_add [Add R] (x y : Matrix m' m R) :
  matrixToVec (x + y) = matrixToVec x + matrixToVec y := rfl

@[simp]
lemma matrixToVec_zero [Zero R] : matrixToVec (0 : Matrix m' m R) = 0 := rfl

@[simp]
lemma matrixToVec_smul {M : Type*} [SMul M R] (c : M) (x : Matrix m' m R) :
    matrixToVec (c • x) = c • matrixToVec x := rfl

/-- For matrices x and y, the dot product of the conjugate of the vector of x with the vector of y
is tr(xᴴy). -/
@[simp]
lemma star_matrixToVec_dotProduct_matrixToVec [Semiring R] [StarRing R] [Fintype m] [Fintype m']
    (x y : Matrix m' m R) :
    star (matrixToVec x) ⬝ᵥ matrixToVec y = trace (xᴴ * y) := by
  -- both sides are `∑ j, ∑ i, star (x i j) * y i j`
  simp only [dotProduct, trace, diag_apply, mul_apply, conjTranspose_apply, Pi.star_apply,
    matrixToVec]
  exact Fintype.sum_prod_type_right _

private lemma matrixToVec_eq_vec_transpose (M : Matrix m' m R) : matrixToVec M = vec Mᵀ := rfl

/-- On vectors indexed by pairs, `A ⊗ₖ Bᵀ` is the map `x ↦ A x B`. -/
@[local simp]
lemma kronecker_mulVec_eq_matrixToVec [CommSemiring R] [Fintype m] [Fintype m'] (A : Matrix l' m' R)
    (B : Matrix m l R) (x : m' × m → R) :
    A ⊗ₖ Bᵀ *ᵥ x = matrixToVec (A * vecToMatrix x * B) := by
  -- Mathlib's `kronecker_mulVec_vec`, for the transpose of `vecToMatrix x`
  have h_transpose : Bᵀ * (vecToMatrix x)ᵀ * Aᵀ = (A * vecToMatrix x * B)ᵀ := by
    rw [← transpose_mul, ← transpose_mul, Matrix.mul_assoc]
  calc A ⊗ₖ Bᵀ *ᵥ x = A ⊗ₖ Bᵀ *ᵥ vec (vecToMatrix x)ᵀ := by
        rw [← matrixToVec_eq_vec_transpose, matrixToVec_vecToMatrix]
    _ = vec (Bᵀ * (vecToMatrix x)ᵀ * Aᵀ) := kronecker_mulVec_vec Bᵀ (vecToMatrix x)ᵀ A
    _ = matrixToVec (A * vecToMatrix x * B) := by rw [h_transpose, matrixToVec_eq_vec_transpose]

section

/-! ### The homomorphism to the group of Hom(S, T), and determinants -/

section

variable {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E] (p : G E s × G E s')
  (g : G E s)

@[simp]
lemma G.adeleMatrix_onHom : (onHom p).adeleMatrix = p.2.adeleMatrix ⊗ₖ p.1⁻¹.adeleMatrixᵀ := rfl

/-- The image of a pair (g, h) in the unitary group of Hom(S,T) acts on an adelic vector x, read
as an n′ × n matrix, by x ↦ hxg⁻¹. -/
lemma G.onHom_mulVec (x : n' × n → 𝔸 E) :
    (onHom p).adeleMatrix *ᵥ x =
      matrixToVec (p.2.adeleMatrix * vecToMatrix x * p.1⁻¹.adeleMatrix) := by simp

@[fun_prop]
lemma G.continuous_onHom : Continuous (onHom : G E s × G E s' → G E (homSigns s s')) := by
  rw [continuous_iff]
  simp only [adeleMatrix_onHom]
  fun_prop [kroneckerMap]

/-- The real components of `onHom p` are `Fock.pairHom`, the finite one is `U.kroneckerHom`. Here
`p.1.1 w`, `p.2.1 w` are the components of `g` and `h` at the infinite place `w`, and `p.1.2`,
`p.2.2` their finite components. -/
lemma G.onHom_eq :
    onHom p = (fun w : NumberField.InfinitePlace E ↦ Fock.pairHom s' s (p.1.1 w, p.2.1 w),
      U.kroneckerHom (one_mul 1) (by simp) (p.1.2, p.2.2)) := rfl

/-- The finite component of `onHom (g, h)` is `h_f ⊗ₖ (g_f⁻¹)ᵀ`. -/
lemma G.onHom_snd :
    ((onHom p).2 : Matrix (n' × n) (n' × n) (𝔸f E)) =
      (p.2.2 : Matrix n' n' (𝔸f E)) ⊗ₖ ((p.1.2⁻¹ : Gf E n) : Matrix n n (𝔸f E))ᵀ := rfl

@[simp]
lemma G.coe_det : g.det.val = g.adeleMatrix.det := rfl

/-- For finite points `g`, `h`, the image of the pair `((1, g), (1, h))` under `onHom` has
infinite component `1`. -/
lemma G.onHom_fin (g : Gf E n) (h : Gf E n') :
    let k : G E (homSigns s s') := onHom ((1, g), 1, h)
    k = (1, k.2) := by
  simp [onHom_eq, mk_one_one, ← Pi.one_def]

@[simp↓]
lemma G.det_snd : (g.det : 𝔸 E).2 = (g.2 : Matrix n n (𝔸f E)).det :=
  map_det (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E)) g.adeleMatrix

@[fun_prop]
lemma G.continuous_det : Continuous (det : G E s → unitary (𝔸 E)) :=
  continuous_adeleMatrix.matrix_det.subtype_mk fun g : G E s ↦ (det g).property

/-- For (g, h) in the unitary groups of ranks n and n', the determinant of x ↦ hxg⁻¹ on
Hom(S,T) is (det h)^n (det g)^(−n'). -/
lemma G.det_onHom : (onHom p).det = p.2.det ^ card n * p.1.det⁻¹ ^ card n' := by
  ext1
  simp [← map_inv, det_kronecker]

/-- The infinite component of `det g` is, at each infinite place `w`, the determinant of the
component of `g` at `w`. -/
@[simp↓]
lemma det_fst : (g.det : 𝔸 E).1 =
    fun w : NumberField.InfinitePlace E ↦ ((g.1 w : GL n ℂ) : Matrix n n ℂ).det :=
  funext fun w ↦ (evalInf w).map_det g.adeleMatrix

/-- The component of `det g` at a finite place `w` is the determinant of the component of `g`
at `w`. -/
@[simp↓]
lemma det_atPlace (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) :
    g.det.val.2 w = (g.2.atPlace w).val.det := by
  rw [g.det_snd]
  exact (evalAt w).map_det _

end

end

/-- For a rational n′ × n matrix x, the adelic vector attached to it in the space Hom(S,T) is
the matrix x_T⁻¹ x x_S, with x_S, x_T the points of S and T. -/
lemma Space.vecAtPoint_hom (x : Matrix n' n E) :
    (S.hom T).vecAtPoint (matrixToVec x) = matrixToVec (T.ratMap S x) :=
  -- the inverse of the point of `Hom(S, T)` is `x_T⁻¹ ⊗ₖ x_Sᵀ`, which acts by `y ↦ x_T⁻¹ y x_S`;
  -- the arguments are left to unification, since written out they make elaboration time out
  kronecker_mulVec_eq_matrixToVec ..

/-- If `g` and `h` are rational points of the unitary groups of `S` and `T`, then the point of the
unitary group of `Hom(S, T)` given by `x ↦ h x g⁻¹` is rational. -/
lemma G.onHom_mem_Gamma {g : G E s} {h : G E s'} (hg : g ∈ S.Γ) (hh : h ∈ T.Γ) :
    onHom (g, h) ∈ (S.hom T).Γ := by
  -- conjugated by the points of `T` and `S`, the matrices of `h` and `g⁻¹` are rational, and the
  -- entries of their Kronecker product are products of their entries
  rw [← inv_mem_iff] at hg
  -- `↓` rewrites the memberships by entries before `simp` turns `g⁻¹ ∈ S.Γ` back into `g ∈ S.Γ`
  simp_all [↓mem_Gamma_iff_range, Space.hom, mul_assoc, mul_mem, ← mul_kronecker_mul,
    ← transpose_mul]

@[simp]
lemma pairChar_apply : pairChar a b p = a.val p.2.det * (b.val p.1.det : ℂ)⁻¹ := mul_comm ..

/-- A character of `[U(1)]` is trivial on the determinants of rational points. -/
@[simp]
lemma AutChar.apply_det_ratEmbed (γ : U S.J) : a.val (S.ratEmbed γ).det = 1 := by
  -- `det (x⁻¹ γ x) = det γ` is rational
  have h_det : toAdele ((γ : GL n E) : Matrix n n E).det = ((S.ratEmbed γ).det : 𝔸 E) :=
    (map_det ..).trans (det_units_conj ..).symm
  exact a.property (S.ratEmbed γ).det ⟨_, h_det⟩

variable [WeilData E]

/-! ### The Weil action of the pair and the theta kernel -/

/-- For p = (g, h) in G(s) × G(s′), `New.pairWeil S T a b p` is the Weil representation ω of
`S.hom T` at the element x ↦ hxg⁻¹ (`New.G.onHom p`), multiplied by the scalar
`pairChar a b p` = a(det h) b(det g)⁻¹. -/
@[local simp]
lemma pairWeil_apply (f : 𝒮 (S.hom T)) :
    pairWeil S T a b p f = pairChar a b p • ω (S.hom T) (G.onHom p) f := rfl

@[fun_prop]
lemma continuous_pairWeil :
    Continuous fun q : (G E s × G E s') × 𝒮 (S.hom T) ↦ pairWeil S T a b q.1 q.2 := by
  -- `pairChar a b q` is `a (det h) * (b (det g))⁻¹`, and `b (det g)` lies on the unit circle, so
  -- it is not zero
  simp only [pairWeil_apply, pairChar_apply]
  fun_prop (disch := simp)

/-- The Weil action `pairWeil S T a b p` of a pair preserves the inner product `dataInner` on data
for `Hom(S, T)`. -/
@[simp]
lemma dataInner_pairWeil (f f' : 𝒮 (S.hom T)) :
    dataInner (S.hom T) (pairWeil S T a b p f) (pairWeil S T a b p f') =
      dataInner (S.hom T) f f' := by
  -- `ω` preserves `dataInner`, and the factor `pairChar a b p` lies on the unit circle
  simp [field, RCLike.mul_conj, Circle.norm_coe]

/-- Let `S` and `T` be spaces over the CM field `E` (with Weil data) and `a`, `b` characters of its
norm-one adeles. Rational points `g` of `U(S)` and `h` of `U(T)` act by substitution: the value of
`pairWeil S T a b (g, h) f` at `x` is `f (h⁻¹ x g)`. Here `x` is a matrix read as a vector on pairs
of indices, on which `x ↦ h⁻¹ x g` is multiplication by the Kronecker product `h⁻¹ ⊗ₖ gᵀ`. -/
lemma pairWeil_of_mem_Gamma {g : G E s} {h : G E s'} (hg : g ∈ S.Γ) (hh : h ∈ T.Γ)
    (f : 𝒮 (S.hom T)) (x : n' × n → 𝔸 E) :
    pairWeil S T a b (g, h) f x = f (h⁻¹.adeleMatrix ⊗ₖ g.adeleMatrixᵀ *ᵥ x) := by
  -- The point `onHom (g, h)` is rational, so it acts by substitution.
  obtain ⟨u, rfl⟩ := hg
  obtain ⟨v, rfl⟩ := hh
  obtain ⟨γ, hγ⟩ : G.onHom (S.ratEmbed u, T.ratEmbed v) ∈ (S.hom T).Γ :=
    onHom_mem_Gamma S T ⟨u, rfl⟩ ⟨v, rfl⟩
  rw [pairWeil_apply, Space.smul_apply, ← hγ, omega_ratEmbed_apply, hγ, ← map_inv]
  -- the character `pairChar` is trivial at rational points
  simp

/-- The translation law of the theta kernel: translating the point by `q` on the right is acting
on the datum by `q`. -/
lemma pairTheta_mul (f : 𝒮 (S.hom T)) (p q : G E s × G E s') :
    pairTheta S T a b f (p * q) = pairTheta S T a b (pairWeil S T a b q f) p := by
  simp [pairTheta]

/-- For a CM field `E` with Weil data, pointed hermitian spaces `S` and `T` over `E`, and
automorphic characters `a`, `b` of U(1)(𝔸), consider the theta kernel
(f, (g, h)) ↦ θ(ω_{a,b}(g,h)f). Here f is a Schwartz function in 𝒮(Hom(S,T)), g lies in `G E s`,
h lies in `G E s'`, ω_{a,b} is the Weil representation attached to `a` and `b`, and θ is the theta
functional of Hom(S,T). This kernel is jointly continuous in the datum f and the point (g, h). -/
@[fun_prop]
lemma continuous_pairTheta : Continuous ↿(pairTheta S T a b) := by fun_prop [pairTheta]

end PairBasic

/-!
## The real Weil action of a pair and the kernel property

Real points `(x, y)` of a pair of unitary groups of signs `s`, `s'` act on the Fock space of
`Hom(S, T)`.

* `New.realPairWeil_polyVector`: block diagonal points (`New.blockDiagAlg`) act on the vector
  `New.Fock.polyVector _ P` of a polynomial `P` by a substitution and a character.
* `New.realPairWeil_vacVector`: they act on the vacuum by that character.
-/

section PairReal

section

variable {E : Type} [Field E] [NumberField E]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {s : n → ℤˣ} {s' : n' → ℤˣ} (γ γ' : NumberField.InfinitePlace E → ℤ)

open Matrix Kronecker
  Fock Fintype Finset Space MvPolynomial Heisenberg.IsVacuum AutChar

/-- The Fock space for the signs s′_i s_j of Hom(S,T), repeated at every infinite place. -/
abbrev PairFock (E : Type) [Field E] [NumberField E] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] (s : n → ℤˣ) (s' : n' → ℤˣ) : Type :=
  fockSpace (realSigns E (homSigns s s'))

/-- The homomorphism sending real points (x, y) to the action z ↦ y_w z x_w⁻¹ on matrices at each
infinite place w, as one block diagonal unitary matrix (`blockU`), in `USign` for the signs of
`Hom(S, T)` repeated at every infinite place. -/
def pairHomInf :
    GInf E s × GInf E s' →*
      USign fun (p : NumberField.InfinitePlace E × n' × n) ↦ homSigns s s' p.2 :=
  blockU.comp
    (MonoidHom.pi fun w ↦
      (pairHom s' s).comp ((Pi.evalMonoidHom _ w).prodMap (Pi.evalMonoidHom _ w)) :
      GInf E s × GInf E s' →* GInf E (homSigns s s'))

/-- The real Weil representation of the pair with weights γ, γ′: (x, y) acts by
∏_w (det y_w)^{γ_w} (det x_w)^{−γ′_w} times the Fock operator of z ↦ y z x⁻¹. -/
@[simps! -isSimp apply_apply]
def realPairWeil : GInf E s × GInf E s' →* PairFock E s s' →L[ℂ] PairFock E s s' where
  toFun p :=
    (∏ w : NumberField.InfinitePlace E, (p.2 w).1.1.det ^ γ w * (p.1 w).1.1.det ^ (-γ' w)) •
      realWeil (pairHomInf p)
  map_one' := by simp
  map_mul' p q := by
    simp [mul_zpow, prod_mul_distrib]
    module

/-- The real Weil action `New.realPairWeil γ γ'` is jointly continuous in the real point and the
Fock vector. -/
@[fun_prop]
lemma continuous_realPairWeil :
    Continuous fun q : (GInf E s × GInf E s') × PairFock E s s' ↦ realPairWeil γ γ' q.1 q.2 := by
  have h_pairHomInf : Continuous (pairHomInf : GInf E s × GInf E s' →
      USign fun (p : NumberField.InfinitePlace E × n' × n) ↦ homSigns s s' p.2) := by
    simp [continuous_U_iff_matrix, pairHomInf]
    fun_prop [kroneckerMap]
  simp [realPairWeil]
  fun_prop (disch := simp [GeneralLinearGroup.det_ne_zero, zpow_ne_zero])

/-- The principal minor of `y` on the indices of sign `σ` is the determinant of the diagonal block
of `y` for `σ` in the partition of the indices by sign. -/
private lemma principalMinor_eq_det_toSquareBlock {ι : Type} [Fintype ι] [DecidableEq ι]
    (y : Matrix ι ι ℂ) (ε : ι → ℤˣ) (σ : ℤˣ) :
    principalMinor y (ε · = σ) = (y.toSquareBlock ε σ).det := rfl

/-- Let the isometry `u` of signs `s` be block diagonal for the partition of the indices by sign
(it lies in `New.blockDiagAlg s`, the matrices that commute with the sign matrix). Then its
determinant is the product, over the signs `σ`, of its principal minors on the indices of
sign `σ`. -/
lemma det_eq_prod_principalMinor {u : USign s}
    (hu : (u : Matrix n n ℂ) ∈ blockDiagAlg s) :
    (u : Matrix n n ℂ).det = ∏ σ : ℤˣ, principalMinor u (s · = σ) := by
  -- `u` is block diagonal, hence block triangular, for the partition of the indices by sign.
  have h_tri : BlockTriangular (u : Matrix n n ℂ) s :=
    fun i j h_lt ↦ mem_blockDiagAlg.mp hu i j h_lt.ne'
  simp only [h_tri.det_fintype, principalMinor_eq_det_toSquareBlock]

/-- For a block diagonal isometry `u = diag(γ, z)` of the form with signs `ε` (`z` is the block on
the negative coordinates), the multiplier of the real Weil representation is `det z⁻¹`. -/
lemma Fock.realMultiplier_of_mem_blockDiagAlg {ι : Type} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ}
    {u : USign ε} (hu : (u : Matrix ι ι ℂ) ∈ blockDiagAlg ε) :
    realMultiplier u = (principalMinor (u : Matrix ι ι ℂ) fun i : ι ↦ ε i = -1)⁻¹ := by
  -- The multiplier is the negative minor of `u⁻¹`, and minors of block diagonal matrices multiply.
  have h_mul : principalMinor ((↑u⁻¹ : Matrix ι ι ℂ) * (u : Matrix ι ι ℂ)) (fun i : ι ↦ ε i = -1) =
      principalMinor (↑u⁻¹ : Matrix ι ι ℂ) (fun i : ι ↦ ε i = -1) *
        principalMinor (u : Matrix ι ι ℂ) fun i : ι ↦ ε i = -1 :=
    principalMinor_mul fun i j k _ hj hk ↦
      .inr (mem_blockDiagAlg.1 hu j k fun h_sign ↦ hj (h_sign.trans hk))
  rw [show (↑u⁻¹ : Matrix ι ι ℂ) * (u : Matrix ι ι ℂ) = 1 from u.val.inv_mul,
    principalMinor_one] at h_mul
  rw [realMultiplier, ← U.principalMinor_coe_inv]
  exact eq_inv_of_mul_eq_one_left h_mul.symm

/-- A block diagonal isometry is a unitary matrix, so it preserves the Gaussian `realVac`, which
depends on `y` only through `star y ⬝ᵥ y`. -/
lemma Fock.realVac_mulVec_of_mem_blockDiagAlg {ι : Type} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ}
    {u : USign ε} (hu : (u : Matrix ι ι ℂ) ∈ blockDiagAlg ε) (y : ι → ℂ) :
    realVac ((u : Matrix ι ι ℂ) *ᵥ y) = realVac y := by
  have h_unitary : (u : Matrix ι ι ℂ)ᴴ * 1 * (u : Matrix ι ι ℂ) = 1 := mem_maxCompactU.2 hu
  rw [mul_one] at h_unitary
  rw [realVac, realVac, star_mulVec, dotProduct_mulVec, vecMul_vecMul, h_unitary, vecMul_one]

/-- An element `k` of the maximal compact subgroup (unitary matrices at the infinite places,
integral at the finite places) preserves the vacuum function. -/
lemma vacuumFn_mulVec_of_mem_maxCompact {E : Type} [Field E] [CMType E]
    [WeilData E] {k : G E s} (hk : k ∈ maxCompact E s) (x : n → 𝔸 E) :
    vacuumFn (k.adeleMatrix *ᵥ x) = vacuumFn x := by
  -- In real and finite coordinates the vacuum is a Gaussian times the finite vacuum.
  obtain ⟨h_real, h_fin⟩ : (∀ w ∈ Set.univ, k.1 w ∈ maxCompactU s) ∧ k.2 ∈ stdLevel E n := hk
  obtain ⟨⟨y, z⟩, rfl⟩ := (adelicSum E s).equiv.surjective x
  have h_block : (blockU k.1).val.val ∈ blockDiagAlg (realSigns E s) := by
    refine mem_blockDiagAlg.2 fun ⟨w, i⟩ ⟨w', j⟩ h_sign ↦ ?_
    have h_zero : (k.1 w).val.val i j = 0 :=
      mem_blockDiagAlg.1 (mem_maxCompactU.1 (h_real w (Set.mem_univ w))) i j h_sign
    simp [blockDiagonal_apply, h_zero]
  have h_lattice : k.2.val.val *ᵥ z ∈ stdLattice E n ↔ z ∈ stdLattice E n := by
    refine ⟨fun hz ↦ ?_, IsIntMatrix.mulVec (mem_stdLevel.1 h_fin)⟩
    have h_inv : k.2⁻¹.val.val *ᵥ k.2.val.val *ᵥ z ∈ stdLattice E n :=
      IsIntMatrix.mulVec (mem_stdLevel.1 (inv_mem h_fin)) hz
    simpa using h_inv
  rw [adeleMatrix_mulVec_adelicSum, (adelicSum E s).vac_equiv, (adelicSum E s).vac_equiv,
    realVac_mulVec_of_mem_blockDiagAlg h_block]
  -- The finite vacuum depends only on membership in the lattice.
  rw [stdLattice.finVac, stdLattice.finVac, stdLattice.star_mulVec_dotProduct_mulVec, h_lattice]

/-- The multiplier `Δ` of the Weil representation (`New.weilMultiplier`) is multiplicative for
factors from the maximal compact subgroup: `Δ(k g k') = Δ(k) Δ(g) Δ(k')` for `k`, `k'` in it. -/
lemma weilMultiplier_mul_of_mem_maxCompact {E : Type} [Field E] [CMType E] [WeilData E]
    {k k' : G E s} (hk : k ∈ maxCompact E s) (g : G E s) (hk' : k' ∈ maxCompact E s) :
    weilMultiplier (k * g * k') = weilMultiplier k * weilMultiplier g * weilMultiplier k' := by
  obtain ⟨hk_real, hk_fin⟩ : (∀ w ∈ Set.univ, k.1 w ∈ maxCompactU s) ∧ k.2 ∈ stdLevel E n := hk
  obtain ⟨hk'_real, hk'_fin⟩ := hk'
  -- At an infinite place `k` and `k'` are block diagonal, so the negative minors multiply.
  have h_real (w : NumberField.InfinitePlace E) : realMultiplier (k.1 w * g.1 w * k'.1 w) =
      realMultiplier (k.1 w) * realMultiplier (g.1 w) * realMultiplier (k'.1 w) := by
    have h_zero {x : USign s} (hx : x ∈ maxCompactU s) {i j : n} (hij : s i ≠ s j) :
        x.val.val i j = 0 :=
      mem_blockDiagAlg.1 (mem_maxCompactU.1 hx) i j hij
    have h_left (y : Matrix n n ℂ) : principalMinor ((k.1 w).val.val * y) (s · = -1) =
        principalMinor (k.1 w).val.val (s · = -1) * principalMinor y (s · = -1) :=
      principalMinor_mul fun i j _ hi hj _ ↦
        .inl (h_zero (hk_real w (Set.mem_univ w)) fun h_sign ↦ hj (h_sign.symm.trans hi))
    have h_right (y : Matrix n n ℂ) : principalMinor (y * (k'.1 w).val.val) (s · = -1) =
        principalMinor y (s · = -1) * principalMinor (k'.1 w).val.val (s · = -1) :=
      principalMinor_mul fun _ j l _ hj hl ↦
        .inr (h_zero (hk'_real w (Set.mem_univ w)) fun h_sign ↦ hj (h_sign.trans hl))
    simp only [realMultiplier, Subgroup.coe_mul, Units.val_mul, h_left, h_right, map_mul]
  -- The finite multiplier is bi-invariant under integral points and `1` on them.
  have h_fin : finMultiplier (k.2 * g.2 * k'.2) = finMultiplier g.2 :=
    glMultiplier_mul_of_mem g.2.val hk_fin hk'_fin
  simp only [weilMultiplier, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, h_real, h_fin,
    finMultiplier_eq_one_of_mem hk_fin, finMultiplier_eq_one_of_mem hk'_fin,
    Finset.prod_mul_distrib]
  ring

/-- The maximal compact subgroup acts on data by substitution: for `k` in it, the coefficient
`⟨ϱ(x) vac, ω(k) f⟩` is the multiplier of `k` times the coefficient `⟨ϱ(k⁻¹ x) vac, f⟩`. These
coefficients are the values at `x` and `k⁻¹ x` of the functions underlying `ω(k) f` and `f`. -/
lemma Space.dataInner_omega_of_mem_maxCompact {E : Type} [Field E] [CMType E] [WeilData E]
    (V : Space E n s) {k : G E s} (hk : k ∈ maxCompact E s) (f : 𝒮 V) (x : n → 𝔸 E) :
    V.dataInner (V.ϱ x V.vacElem) (V.ω k f) =
      weilMultiplier k * V.dataInner (V.ϱ (k⁻¹.adeleMatrix *ᵥ x) V.vacElem) f := by
  rw [← V.val_eq_dataInner_rho_vacElem, ← V.val_eq_dataInner_rho_vacElem]
  exact weilRep_apply_of_vacuum_smul adelicAction k f (vacuumFn_mulVec_of_mem_maxCompact hk) x

/-- Let `u = diag(γ, z)` be a block diagonal isometry of the form with signs `ε`, with `γ` on the
positive and `z` on the negative coordinates. The real Weil representation of `u` acts on the Fock
vector `polyVector ε P` of a polynomial `P` by `det z⁻¹` times the substitution
`X i ↦ ∑ j, γ j i • X j` on the positive and `X i ↦ ∑ j, z⁻¹ i j • X j` on the negative variables.
This is the standard action of the maximal compact subgroup of `U(p, q)` in the Fock model (Folland,
*Harmonic Analysis in Phase Space*). -/
lemma Fock.realWeil_polyVector_of_mem_blockDiagAlg {ι : Type} [Fintype ι] [DecidableEq ι]
    {ε : ι → ℤˣ} {u : USign ε} (hu : (u : Matrix ι ι ℂ) ∈ blockDiagAlg ε) (P : MvPolynomial ι ℂ) :
    realWeil u (polyVector ε P) =
      (principalMinor (u : Matrix ι ι ℂ) fun i : ι ↦ ε i = -1)⁻¹ •
        polyVector ε (aeval (fun i : ι ↦ ∑ j : ι,
          (if ε i = 1 then (u : Matrix ι ι ℂ) j i else (↑u⁻¹ : Matrix ι ι ℂ) i j) • X j) P) := by
  -- The isometry `u` preserves the Gaussian, so it acts by its multiplier times the substitution
  -- `y ↦ u⁻¹ y`; compare the values at `y`.
  let A (i j : ι) : ℂ := if ε i = 1 then (u : Matrix ι ι ℂ) j i else (↑u⁻¹ : Matrix ι ι ℂ) i j
  have h_inv : (↑u⁻¹ : Matrix ι ι ℂ) = (u : Matrix ι ι ℂ)ᴴ :=
    (Matrix.coe_units_inv u.val).trans (maxCompactU.coe_inv ⟨u, mem_maxCompactU.2 hu⟩)
  have h_gauss (y : ι → ℂ) : realVac (u • y) = realVac y :=
    realVac_mulVec_of_mem_blockDiagAlg hu y
  -- The coordinate of `u⁻¹ y` is conjugated at a positive index, where `conj uᴴ = uᵀ`.
  have h_coord (y : ι → ℂ) (i : ι) :
      holomorphicCoord ε (u⁻¹ • y) i = ∑ j : ι, A i j * holomorphicCoord ε y j := by
    have h_term (j : ι) : A i j * holomorphicCoord ε y j =
        if ε i = 1 then star ((↑u⁻¹ : Matrix ι ι ℂ) i j * y j)
        else (↑u⁻¹ : Matrix ι ι ℂ) i j * y j := by
      simp only [A, h_inv]
      by_cases h_sign : ε j = ε i
      · by_cases hi : ε i = 1 <;> simp [holomorphicCoord_eq, h_sign, hi]
      · simp [mem_blockDiagAlg.1 hu j i h_sign]
    have h_smul : (u⁻¹ • y) i = ∑ j : ι, (↑u⁻¹ : Matrix ι ι ℂ) i j * y j := rfl
    simp only [h_term, Finset.sum_ite_irrel, ← star_sum, ← h_smul]
    simp only [holomorphicCoord_eq, Pi.star_apply]
  have h_value (y : ι → ℂ) : polyVector ε P (u⁻¹ • y) =
      polyVector ε (aeval (fun i : ι ↦ ∑ j : ι, A i j • X j) P) y := by
    rw [polyVector_apply, polyVector_apply, ← h_gauss (u⁻¹ • y), smul_inv_smul, funext (h_coord y),
      ← aeval_eq_eval, ← aeval_eq_eval, comp_aeval_apply]
    simp only [map_sum, map_smul, aeval_X, smul_eq_mul]
  have h_delta : (realAction ε).Δ u = realMultiplier u := rfl
  ext y
  rw [weilRep_apply_of_vacuum_smul _ _ _ h_gauss, h_delta, Heisenberg.IsVacuum.smul_apply,
    ← realMultiplier_of_mem_blockDiagAlg hu, h_value]

/-- The Kronecker product of matrices that are block diagonal for the signs `s'` and `s` is block
diagonal for the product signs `New.homSigns s s'`. -/
private lemma kronecker_mem_blockDiagAlg {A : Matrix n' n' ℂ} {B : Matrix n n ℂ}
    (hA : A ∈ blockDiagAlg s') (hB : B ∈ blockDiagAlg s) :
    A ⊗ₖ B ∈ blockDiagAlg (homSigns s s') := by
  refine mem_blockDiagAlg.2 fun ⟨a, b⟩ ⟨i, j⟩ h_sign ↦ ?_
  by_cases h_row : s' a = s' i
  · have h_col : s b ≠ s j := fun h_col ↦ h_sign (by simp [pairSign, h_row, h_col])
    simp [mem_blockDiagAlg.1 hB b j h_col]
  · simp [mem_blockDiagAlg.1 hA a i h_row]

/-- The maximal compact subgroups act by a substitution and the character of the vacuum. Let `x`,
`y` be block diagonal for the signs `s`, `s'` of signatures `(p, q)`, `(p', q')`. The scalar
is the product over the places of
`(det y⁺) ^ (γ - q) (det y⁻) ^ (γ - p) (det x⁺) ^ (q' - γ') (det x⁻) ^ (p' - γ')`.
At each place, the variable `X a b` goes to `∑ y i a * x⁻¹ b j * X i j` if `s' a = s b`, and to
`∑ y⁻¹ a i * x j b * X i j` otherwise, with the sums over the variables of that place.

A special case of the standard action of the maximal compact subgroup in the Bargmann–Fock model,
for a unitary dual pair. -/
lemma realPairWeil_polyVector {x : GInf E s} {y : GInf E s'}
    (hx : ∀ w : NumberField.InfinitePlace E, (x w : Matrix n n ℂ) ∈ blockDiagAlg s)
    (hy : ∀ w : NumberField.InfinitePlace E, (y w : Matrix n' n' ℂ) ∈ blockDiagAlg s')
    (P : MvPolynomial (NumberField.InfinitePlace E × n' × n) ℂ) :
    realPairWeil γ γ' (x, y) (polyVector (realSigns E (homSigns s s')) P) =
      -- the character of the vacuum
      (∏ w : NumberField.InfinitePlace E, ∏ σ ∈ ({1, -1} : Finset ℤˣ),
        principalMinor (y w) (s' · = σ) ^ (γ w - Nat.card {i : n // s i = -σ}) *
          principalMinor (x w) (s · = σ) ^ (Nat.card {i : n' // s' i = -σ} - γ' w)) •
      -- the linear substitution of the variables
      polyVector (realSigns E (homSigns s s'))
        (aeval (fun ((w, a, b) : NumberField.InfinitePlace E × n' × n) ↦ ∑ i : n', ∑ j : n,
          (if s' a = s b then (y w : Matrix n' n' ℂ) i a * (↑(x w)⁻¹ : Matrix n n ℂ) b j
            else (↑(y w)⁻¹ : Matrix n' n' ℂ) a i * (x w : Matrix n n ℂ) j b) • X (w, i, j)) P) := by
  -- The point `pairHomInf (x, y)` is block diagonal, so it acts by its multiplier times a
  -- substitution (`realWeil_polyVector_of_mem_blockDiagAlg`). Compute both from `x` and `y`.
  have h_place (w : NumberField.InfinitePlace E) :
      (y w : Matrix n' n' ℂ) ⊗ₖ (x w : Matrix n n ℂ)⁻¹ᵀ ∈ blockDiagAlg (homSigns s s') :=
    kronecker_mem_blockDiagAlg (hy w) (mem_blockDiagAlg.2 fun i j h_sign ↦
      mem_blockDiagAlg.1 (blockDiagAlg.inv_mem (hx w)) j i h_sign.symm)
  have h_mem : ↑(pairHomInf (x, y)) ∈ blockDiagAlg (realSigns E (homSigns s s')) := by
    refine mem_blockDiagAlg.2 fun ⟨w, c⟩ ⟨w', c'⟩ h_sign ↦ ?_
    have h_zero : ((y w : Matrix n' n' ℂ) ⊗ₖ (x w : Matrix n n ℂ)⁻¹ᵀ) c c' = 0 :=
      mem_blockDiagAlg.1 (h_place w) c c' h_sign
    simpa [pairHomInf, pairHom, blockDiagonal_apply] using fun _ ↦ mul_eq_zero.1 h_zero
  -- `realMultiplier` is the negative minor of `(y ⊗ₖ x⁻¹ᵀ)⁻¹`, that of `1 ⊗ₖ xᵀ` divided by that of
  -- `y ⊗ₖ 1`.
  have hΔ (w : NumberField.InfinitePlace E) : realMultiplier (pairHom s' s (x w, y w)) =
      principalMinor (x w) (s · = -1) ^ card {i : n' // s' i = 1} *
        principalMinor (x w) (s · = 1) ^ card {i : n' // s' i = -1} /
        (principalMinor (y w) (s' · = -1) ^ card {i : n // s i = 1} *
          principalMinor (y w) (s' · = 1) ^ card {i : n // s i = -1}) := by
    have hy_mem : (y w : Matrix n' n' ℂ) ⊗ₖ 1 ∈ blockDiagAlg (homSigns s s') :=
      kronecker_mem_blockDiagAlg (hy w) (one_mem _)
    have hy_ne : principalMinor ((y w : Matrix n' n' ℂ) ⊗ₖ 1) (homSigns s s' · = -1) ≠ 0 := by
      simpa [pairHom] using U.principalMinor_sign_ne_zero (-1) (pairHom s' s (1, y w))
    have h_split (M : Matrix (n' × n) (n' × n) ℂ) :
        principalMinor (M * (y w : Matrix n' n' ℂ) ⊗ₖ 1) (homSigns s s' · = -1) =
          principalMinor M (homSigns s s' · = -1) *
            principalMinor ((y w : Matrix n' n' ℂ) ⊗ₖ 1) (homSigns s s' · = -1) :=
      principalMinor_mul fun _ j k _ hj hk ↦
        .inr (mem_blockDiagAlg.1 hy_mem j k fun h_sign ↦ hj (h_sign.trans hk))
    rw [realMultiplier, ← U.principalMinor_coe_inv, eq_div_of_mul_eq hy_ne (h_split _).symm]
    -- Group the rows and the columns by their sign.
    simp [← map_inv, ← mul_kronecker_mul, principalMinor_kronecker_one, one_kronecker,
      principalMinor_blockDiagonal, pairHom, pairSign,
      ← prod_fiberwise' s fun c ↦ principalMinor (y w) (s' · * c = -1),
      ← prod_fiberwise' s' fun c ↦ principalMinor (x w) (c * s · = -1)]
  -- The multiplier of `pairHomInf (x, y)` is the product of those at the places.
  have h_multiplier : realMultiplier (pairHomInf (x, y)) =
      ∏ w : NumberField.InfinitePlace E, realMultiplier (pairHom s' s (x w, y w)) :=
    realMultiplier_blockU _
  have h_twist (v : PairFock E s s') : realPairWeil γ γ' (x, y) v =
      (∏ w : NumberField.InfinitePlace E, (y w : Matrix n' n' ℂ).det ^ γ w *
        (x w : Matrix n n ℂ).det ^ (-γ' w)) • realWeil (pairHomInf (x, y)) v := rfl
  rw [h_twist, realWeil_polyVector_of_mem_blockDiagAlg h_mem,
    ← realMultiplier_of_mem_blockDiagAlg h_mem, h_multiplier, smul_smul, ← prod_mul_distrib]
  congrm (∏ w, ?_) • polyVector _ (aeval (fun c ↦ ?_) P)
  · -- The determinants of `x w` and `y w` are products of their two principal minors.
    rw [hΔ]
    simp [det_eq_prod_principalMinor, hx, hy, mul_zpow, zpow_sub₀, U.principalMinor_sign_ne_zero]
    ring
  · -- Only the variables at the place of `c` occur; there the entries are those of `y ⊗ₖ x⁻¹ᵀ`
    -- and of its inverse.
    rw [← map_inv]
    simp [pairHom, pairHomInf, pairSign, blockDiagonal_apply, sum_prod_type, mul_eq_one_iff_eq_inv]

/-- Block diagonal points `x` of the source (signs `s`) and `y` of the target (signs `s'`) act on
the real vacuum by a character. At the place `w`, the determinant of the block of sign `σ` of `y`
has the exponent `γ w` minus the number of signs `-σ` in `s`; that of `x` has the number of signs
`-σ` in `s'` minus `γ' w`. This is the case `P = 1` of `New.realPairWeil_polyVector`. -/
lemma realPairWeil_vacVector {x : GInf E s} {y : GInf E s'}
    (hx : ∀ w : NumberField.InfinitePlace E, (x w : Matrix n n ℂ) ∈ blockDiagAlg s)
    (hy : ∀ w : NumberField.InfinitePlace E, (y w : Matrix n' n' ℂ) ∈ blockDiagAlg s') :
    realPairWeil γ γ' (x, y) vacVector =
      (∏ w : NumberField.InfinitePlace E, ∏ σ ∈ ({1, -1} : Finset ℤˣ),
        principalMinor (y w) (s' · = σ) ^ (γ w - Nat.card {i : n // s i = -σ}) *
          principalMinor (x w) (s · = σ) ^ (Nat.card {i : n' // s' i = -σ} - γ' w)) •
        (vacVector : PairFock E s s') := by
  rw [← polyVector_one, realPairWeil_polyVector γ γ' hx hy, map_one]

end

open Matrix Kronecker
  Fock Fintype Finset Space MvPolynomial Heisenberg.IsVacuum AutChar

variable {E : Type} [Field E] [CMType E] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {s : n → ℤˣ} {s' : n' → ℤˣ} {γ γ' : NumberField.InfinitePlace E → ℤ} [WeilData E]
  (S : Space E n s) (T : Space E n' s') (a b : AutChar E)
  {ψ ψ' : (w : FinPlace E) → MulChar (ResField w) ℂ}

/-- The theta kernel of the pair: the action `New.pairWeil S T a b` with the theta functional. It is
continuous and left invariant under the rational points of both groups. -/
@[simps]
abbrev pairThetaKer : ThetaKernel (𝒮 (S.hom T)) S T where
  ω := pairWeil S T a b
  θ := θ (S.hom T)
  continuous := by fun_prop
  rat_mul := by simp_all [← Prod.mk_mul_mk, pairWeil_of_mem_Gamma]

/-- Let `a` have weight `γ` and `b` weight `γ'` (`HasWeight`, tame parts `ψ`, `ψ'`): at a real point
`z` of U(1), `a z = ∏_w z_w ^ γ w`, and likewise `b` with `γ'`. For a Fock vector `v` and `f` in
𝒮(`S.hom T`), write v ⊗ f = ∫ v(y) ϱ(y)f dy for the integrated Heisenberg action
(`New.Space.integrated`). Then for archimedean points x ∈ G_∞(s), y ∈ G_∞(s′), taken as adelic
elements with trivial finite part, ω_{a,b}(x,y)(v ⊗ f) = (Ω(x,y)v) ⊗ f, where ω_{a,b} is
`New.pairWeil S T a b` and Ω is `New.realPairWeil γ γ'`. -/
lemma pairWeil_integrated [HasWeight a γ ψ] [HasWeight b γ' ψ'] (x : GInf E s) (y : GInf E s')
    (v : Model (realHeisenberg (realSigns E (homSigns s s')))) (f : 𝒮 (S.hom T)) :
    pairWeil S T a b ((x, 1), y, 1) (integrated (S.hom T) v f) =
      integrated (S.hom T) (realPairWeil γ γ' (x, y) v) f := by
  -- At a real point the characters act through their weights (`HasWeight.apply_eq`), and `ω`
  -- splits into the real action on `v` and the finite action on `f` (`omega_integrated`).
  simp [← Submonoid.one_def, pairWeil, G.onHom_eq, HasWeight.apply_eq, Prod.mk_one_one,
    omega_integrated, realPairWeil, prod_mul_distrib, pairHomInf, MonoidHom.pi]

/-- Finite points `(k, k')` act on `v ⊗ f` (`New.Space.integrated`, `v` a vector of the Fock space
`New.PairFock E s s'`) through `f`. -/
@[simp]
lemma pairWeil_integrated_fin (k : Gf E n) (k' : Gf E n')
    (v : Model (realHeisenberg (realSigns E (homSigns s s')))) (f : 𝒮 (S.hom T)) :
    pairWeil S T a b ((1, k), 1, k') (integrated (S.hom T) v f) =
      integrated (S.hom T) v (pairWeil S T a b ((1, k), 1, k') f) := by
  simp [← Pi.one_def, pairWeil, G.onHom_eq, Prod.mk_one_one, omega_integrated]

/-- Let the character `a` have weight `γ` (with tame part `ψ`). For a Fock vector `v` and `f` in
𝒮(`S.hom T`), let v ⊗ f = ∫ v(y) ϱ(y)f dy be the integrated Heisenberg action
(`New.Space.integrated`). For an archimedean point h ∈ G_∞(s′), taken with trivial finite part and
paired with 1 in the first group, `New.pairWeil S T a b` sends v ⊗ f to (Ω(1,h)v) ⊗ f with
Ω = `New.realPairWeil γ 0`; no weight of `b` is needed. -/
lemma pairWeil_integrated_right {S : Space E n s} {T : Space E n' s'} (a b : AutChar E)
    {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ} {f : 𝒮 (S.hom T)} [ha : HasWeight a γ ψ]
    (h : GInf E s') (v : Model (realHeisenberg (realSigns E (homSigns s s')))) :
    pairWeil S T a b (1, h, 1) (integrated (S.hom T) v f) =
      integrated (S.hom T) (realPairWeil γ 0 (1, h) v) f := by
  simp [← Submonoid.one_def, pairWeil, G.onHom_eq, HasWeight.apply_eq, Prod.mk_one_one,
    omega_integrated, realPairWeil, pairHomInf, MonoidHom.pi]

/-- On `v ⊗ f`, for spaces `S`, `T` and characters `a`, `b` of weights `γ`, `γ'` (with tame parts
`ψ`, `ψ'`), the real part `(x, y)` of a pair acts on the Fock vector `v` by
`New.realPairWeil γ γ'`, and the finite part `(k, k')` acts on `f`. -/
lemma pairWeil_integrated_all {S : Space E n s} {T : Space E n' s'}
    {ψ ψ' : (w : FinPlace E) → MulChar (ResField w) ℂ} {a b : AutChar E} [HasWeight a γ ψ]
    [HasWeight b γ' ψ'] (x : GInf E s) (k : Gf E n) (y : GInf E s') (k' : Gf E n')
    (v : Model (realHeisenberg (realSigns E (homSigns s s')))) (f : 𝒮 (S.hom T)) :
    pairWeil S T a b ((x, k), y, k') (integrated (S.hom T) v f) =
      integrated (S.hom T) (realPairWeil γ γ' (x, y) v) (pairWeil S T a b (k, k') f) := by
  -- Split the point into its real and its finite part.
  rw [← pairWeil_integrated_fin, ← pairWeil_integrated S T a b, rep_apply_apply]
  simp

end PairReal

/-! ## Open levels fixing finite data -/

/-- Let `E` be a CM field with Weil data, `S`, `T` hermitian spaces with points, and `a`, `b`
characters of U(1)(𝔸) trivial on its rational (norm-one) points. Suppose `f` lies in the finite
part of 𝒮(Hom(S, T)), which is the span of the translates of the vacuum under the finite Heisenberg
operators. Then there are open subgroups `K`, `K'` of the finite adelic unitary groups `Gf E n`,
`Gf E n'` such that `pairWeil S T a b` fixes `f` at every `((1, k), 1, k')` with `k ∈ K` and
`k' ∈ K'` (these elements are trivial at the infinite places). -/
lemma exists_level_pairWeil {E : Type*} {n n' : Type} {s : n → ℤˣ} {s' : n' → ℤˣ} [Field E]
    [CMType E] [WeilData E] [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {S : Space E n s} {T : Space E n' s'} (a b : AutChar E) {f : 𝒮 (S.hom T)}
    (hf : f ∈ (S.hom T).finitePart) :
    ∃ (K : OpenSubgroup (Gf E n)) (K' : OpenSubgroup (Gf E n')), ∀ k ∈ K, ∀ k' ∈ K',
      pairWeil S T a b ((1, k), 1, k') f = f := by
  -- Near `1` the character `pairChar a b` is trivial and the Weil representation fixes `f`; such a
  -- neighbourhood contains a product of open subgroups.
  -- `embed` sends the two finite groups to the points with trivial real parts.
  let embed : Gf E n × Gf E n' →ₜ* G E s × G E s' :=
    (ContinuousMonoidHom.inr (GInf E s) (Gf E n)).prodMap
      (ContinuousMonoidHom.inr (GInf E s') (Gf E n'))
  -- No small subgroups: a continuous character to the circle is trivial near `1`. Here `χ` is
  -- `pairChar a b ∘ embed` with values in the circle.
  let χ : Gf E n × Gf E n' →* Circle :=
    (((b⁻¹).val.toMonoidHom.comp G.det).coprod (a.val.toMonoidHom.comp G.det)).comp
      embed.toMonoidHom
  have h_χ_cont : Continuous χ := by
    simp [χ, Function.comp_def]
    fun_prop
  have h_char : ∀ᶠ k in nhds 1, pairChar a b (embed k) = 1 :=
    (char_eventually_eq_one χ h_χ_cont).mono fun k hk ↦
      show ((χ k : Circle) : ℂ) = 1 by rw [hk, Circle.coe_one]
  have h_fix : ∀ᶠ k in nhds 1, (S.hom T).ω (1, (G.onHom (embed k)).2) f = f :=
    ((G.continuous_onHom.comp embed.continuous).snd.tendsto' 1 1 (by simp)).eventually
      (Space.eventually_omega_eq_self hf)
  obtain ⟨K, K', hK_subset⟩ : ∃ (K : OpenSubgroup (Gf E n)) (K' : OpenSubgroup (Gf E n')),
      (K : Set (Gf E n)) ×ˢ (K' : Set (Gf E n')) ⊆
        {k | pairChar a b (embed k) = 1 ∧ (S.hom T).ω (1, (G.onHom (embed k)).2) f = f} :=
    NonarchimedeanGroup.prod_subset (h_char.and h_fix)
  refine ⟨K, K', fun k hk k' hk' ↦ ?_⟩
  obtain ⟨h_char_k, h_fix_k⟩ :
      pairChar a b (embed (k, k')) = 1 ∧ (S.hom T).ω (1, (G.onHom (embed (k, k'))).2) f = f :=
    hK_subset (Set.mk_mem_prod hk hk')
  have h_embed : embed (k, k') = ((1, k), 1, k') := rfl
  rw [h_embed] at h_char_k h_fix_k
  -- `G.onHom` of a finite point has trivial archimedean part.
  rw [pairWeil_apply, G.onHom_fin k k', h_char_k, h_fix_k, one_smul]

end New

/-!
## Maps in rational coordinates, Heisenberg cocycle and theta lifts

A space (`New.Space`) has a Gram matrix `J` over `E` and an adelic point `x`. The Weil
representation of `Hom(V, V')` is written in the adelic coordinates that the points give.

* `New.Space.homAtPoint`: passes from a matrix `w` in rational coordinates to `x'⁻¹ w x`.
* `New.Space.homBicharacter_eq`: the Heisenberg bicharacter in rational coordinates is the
  standard character of a trace.
* `New.Space.homHeisenbergOp`: the Heisenberg operator of a matrix in rational coordinates.
-/

namespace New.Space

open Matrix Prod

section HomAtPoint

variable {E ι ι' : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι'] {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} (V : Space E ι ε)
  (V' : Space E ι' ε') [A : WeilData E] (x y : Matrix ι' ι (𝔸 E))

/-- The additive map sending an adelic matrix w : V → V' in rational coordinates to x'⁻¹wx, its
vector in the adelic coordinates of Hom(V,V'); here x = `V.x` and x' = `V'.x` are the points. -/
def homAtPoint : Matrix ι' ι (𝔸 E) →+ ι' × ι → 𝔸 E :=
  show Matrix ι' ι (𝔸 E) →+ ι' × ι → 𝔸 E from AddMonoidHom.mk'
    (matrixToVec <| V'.x⁻¹.val * · * V.x.val) (by simp [Matrix.mul_add, Matrix.add_mul])

/-- The Heisenberg bicharacter β of Hom(V,V') evaluated at two adelic matrices x, y given in
rational coordinates. -/
abbrev homBicharacter : ℂ :=
  (adelicHeisenberg E (homSigns ε ε')).β (V.homAtPoint V' x) (V.homAtPoint V' y)

end HomAtPoint

variable {E ι ι' : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι'] {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {V : Space E ι ε}
  {V' : Space E ι' ε'} [A : WeilData E]
  (x y : Matrix ι' ι (𝔸 E)) (a : ∀ (n : Type) [Fintype n], AutChar E)

/-- The representation `New.pairWeil` of U(V) × U(V′) on 𝒮(Hom(V, V′)) with the characters `a ι` and
`a ι′`, where ι, ι′ index the bases of V, V′. -/
abbrev twistedPairWeil : G E ε × G E ε' →* 𝒮 (V.hom V') →L[ℂ] 𝒮 (V.hom V') :=
  pairWeil V V' (a ι) (a ι')

/-- The Heisenberg bicharacter of `Hom(V, V')` at two adelic matrices `x`, `y` in rational
coordinates is the standard additive character of `ȷ / 2` times the trace of `y^* x`. Here `y^*`
(`New.Space.formAdjoint`) is the adjoint of `y` for the hermitian forms of `V` and `V'`, and `ȷ`
is the element of the Weil data. -/
lemma homBicharacter_eq :
    V.homBicharacter V' x y =
      stdAddChar E (toAdele (A.j / 2) * (V.formAdjoint V' y * x).trace) := by
  simp [homBicharacter, adelicHeisenberg, homAtPoint, kronecker_mulVec_eq_matrixToVec, formAdjoint,
    map_J_inv, map_J, V.x.val.trace_mul_cycle', Matrix.mul_assoc]

/-- The finite coordinates (`New.finCoord`) of `New.Space.homAtPoint` of `x` form the matrix
`α⁻¹ x'_f⁻¹ x_fin x_f`. Here `x_fin` is the finite part of `x`, `x_f` and `x'_f` are the finite
parts of the points of `V` and `V'` (`New.Space.xFin`), and `α` is the finite idele of the Weil
data. -/
lemma finCoord_homAtPoint :
    finCoord (V.homAtPoint V' x) =
      matrixToVec (A.α⁻¹.val • (V'.xFin⁻¹.val * x.map snd * V.xFin.val)) := by
  funext c
  simp [homAtPoint, matrixToVec, xFin, mul_apply, snd_sum, ← map_inv]

/-- The Heisenberg operator ϱ on 𝒮(Hom(V, V′)) at `New.Space.homAtPoint` of an adelic matrix x :
V → V′ given in rational coordinates. -/
abbrev homHeisenbergOp : 𝒮 (V.hom V') →L[ℂ] 𝒮 (V.hom V') := (V.hom V').ϱ (V.homAtPoint V' x)

/-- A family of maps `k`, indexed by `O`, computes the theta lifts between the standard positive
spaces on ι and ι′. For every polynomial `P` and every linear functional `t` on `WeylIndex ι κ → ℂ`,
there is a linear functional `t'` on `WeylIndex ι' κ → ℂ` with the following property. For every
`o`, `Φ`, `φ` and `h`, take the integral over `g` of θ of `twistedPairWeil (a o) (g, h)` applied to
`P` tensored with `Φ`, times the coefficient of `φ` at `g` taken with `t`. This integral is the
coefficient of `k o Φ φ` at `h` taken with `t'`. -/
def IsThetaLift {O : Type*} (κ : NumberField.InfinitePlace E → ℕ → ℕ)
    (e e' : NumberField.InfinitePlace E → ℤ) (a : O → (n : Type) → [Fintype n] → AutChar E)
    (k : O → ((stdSpace E ι).hom (stdSpace E ι')).finitePart →ₗ[ℂ]
        AlgForm (E := E) ι κ e →ₗ[ℂ] AlgForm ι' κ e') : Prop :=
  ∀ (P : MvPolynomial (NumberField.InfinitePlace E × ι' × ι) ℂ) (t : (WeylIndex ι κ → ℂ) →ₗ[ℂ] ℂ),
    ∃ t' : (WeylIndex ι' κ → ℂ) →ₗ[ℂ] ℂ,
    ∀ (o : O) (Φ : ↥((stdSpace E ι).hom (stdSpace E ι')).finitePart)
      (φ : ↥(AlgForm ι κ e)) (h : G E 1),
    ∫ g : G E 1, θ ((stdSpace E ι).hom (stdSpace E ι'))
          (twistedPairWeil (a o) (g, h)
            (integrated ((stdSpace E ι).hom (stdSpace E ι'))
              (Fock.polyVector (realSigns E (homSigns 1 1)) P) Φ.val)) *
        algFormCoeff 1 t φ g ∂(stdSpace E ι).quotMeasure =
      algFormCoeff 1 t' (k o Φ φ) h

end New.Space

end
