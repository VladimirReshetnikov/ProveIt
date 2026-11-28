import Lib.Weil.DualPair.FiniteAction

/-!
# Theta kernels of unitary pairs modulo an ideal: formal laws and seesaw identities

This file proves the formal laws of the theta kernel θ^{S,T}_{a,b}[Ψ,P](g,h) =
`New.modKernel` S T a b 𝔪 Ψ P g h. Here S and T are spaces of ranks n and n′, and a and b are
characters of [U(1)]. Ψ is a function on n′ × n matrices over O_E/𝔪, and P is a polynomial whose
variables are indexed by an infinite place and a matrix position (row, column). The kernel is
`New.pairTheta` of the datum `New.modDatum`; the laws cover bilinearity, twisting, integral
translations, seesaw identities, negation, passing to a smaller ideal and relabelling.

## Main definitions and results

* `New.exists_conj_modKernel_eq_mul_modKernel_neg`, `New.exists_stdKernel_neg_left`: the complex
  conjugate of a kernel is a kernel for the negated first space, up to a factor of modulus one.
* `New.modKernel_mul_stdLevel_left`, `New.modKernel_mul_stdLevel_right`: right translation by the
  lattice stabiliser `New.stdLevel` acts on Ψ through its reduction `New.Modulus.reductionGL`, up to
  a scalar; `New.modDatum_factor`, `New.modKernel_factor`: passing to a smaller ideal.
* `New.modKernel_block_right`, `New.modKernel_sum_right`, `New.modKernel_sum_left`,
  `New.Rows.modKernelStdSpace_block`: seesaw identities, the kernel of a direct sum at block
  diagonal elements is a product; `New.stdKernel_sum_right`, `New.stdKernel_sum_left`: the same with
  standard characters; `New.stdKernel` S T 𝔪 is `New.modKernel` S T (stdChar s) (stdChar s') 𝔪, with
  s, s′ the signs of S, T.

Notions from other files:
* `New.pairWeil`: The representation ω_{a,b}(g, h) = a(det h) b(det g)⁻¹ ω(`onHom` (g, h)); the
  scalar is `New.pairChar a b (g, h)`.
* `New.Modulus`: a nonzero ideal of O_E prime to its complex conjugate, that is, never divisible by
  both w and w̄; `𝔪.ResidueRing` is O_E/𝔪 and `𝔪.places` the set of primes dividing 𝔪.
* `New.Space.boxProd`: the product f₁ ⊠ f₂ of data on two blocks of coordinates.
* `New.negSource` (`Lib.Weil.DualPair.FiniteAction`): the change of coordinates x ↦ (1, u⁻¹) x from
  Hom(S⁻,T) to Hom(S,T); `negSource.map` pulls data on Hom(S,T) back to data on Hom(S⁻,T).

## Relation to the literature

Known; see `Lib.Weil.DualPair.GaloisLaw` for sources.

See also `Lib.Weil.DualPair.ThetaLiftConvergence`.
-/

noncomputable section

section KernelLaws

namespace New

open NumberField Matrix MvPolynomial ComplexConjugate WeilData Space Fock Weil CoordChange Modulus
  Fintype Function Pi Ideal.Quotient

variable {E : Type} [Field E] [CMType E]
  {n n' n₁ n₂ : Type _} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n₁]
  [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] [WeilData E] {s : n → ℤˣ} {s' : n' → ℤˣ}
  {s₁ : n₁ → ℤˣ} {s₂ : n₂ → ℤˣ} (S : Space E n s) (T : Space E n' s') (a b : AutChar E)
  (𝔪 : Modulus E) (V : Space E n₁ s₁)

/-- Reduction modulo 𝔪, as a homomorphism from the stabiliser of Ô^n in the finite adelic
unitary group to GL_n(O_E/𝔪). -/
def Modulus.reductionGL {E : Type} [Field E] [NumberField E] [IsCMField E] (𝔪 : Modulus E) :
    stdLevel E n →* GL n 𝔪.ResidueRing := stdLevel.map n 𝔪.reduction

omit [WeilData E] in
@[simp]
lemma Modulus.factor_reductionGL {𝔪 𝔫 : Modulus E} {h : 𝔫.ideal ≤ 𝔪.ideal} {k : stdLevel E n} :
    (reductionGL 𝔫 k).val.map (factor h) = (reductionGL 𝔪 k).val :=
  Matrix.ext fun i j ↦ by simp [reductionGL]

/-- The theta kernel θ^{S,I}_{a,b}[Ψ, P](g, (1, h)), where I is the standard space I_{n′} of rank n′
and h lies in its finite adelic unitary group. -/
abbrev modKernelStdSpace (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) (g : G E s) (h : Gf E n') : ℂ :=
  modKernel S (stdSpace E n') a b 𝔪 Ψ P g (1, h)

/-- The datum on Hom(S, T) with the function Ψ on matrices modulo 𝔪 at the places dividing 𝔪 and the
vacuum at the other finite places, as an element of the finite part of the space of data. -/
def vacuumDatum (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ) : (S.hom T).finitePart :=
  ⟨(S.hom T).schrodingerOp 𝔪.places (𝔪.liftFn (Ψ ∘ vecToMatrix)) (vacElem (S.hom T)),
    schrodingerOp_mem_finitePart ..⟩

/-- For maps e, f of row and column indices, the ℂ-algebra map of polynomial rings sending the
variable X_(i,r,c) to X_(i,e(r),f(c)). -/
abbrev renameRowsCols {ι a b c d : Type*} (e : a → c) (f : b → d) :
    MvPolynomial (ι × a × b) ℂ →ₐ[ℂ] MvPolynomial (ι × c × d) ℂ :=
  rename (R := ℂ) (Prod.map (id (α := ι)) (Prod.map e f))

/-! ### Bilinearity, twisting, integral translations and seesaw identities -/

/-- The value θ^{S,T}_{a,b}[Ψ, P](g, h) of the theta kernel as a complex bilinear form in the
function Ψ modulo 𝔪 and the polynomial P. -/
def modKernelBilin (g : G E s) (h : G E s') :
    (Matrix n' n 𝔪.ResidueRing → ℂ) →ₗ[ℂ] MvPolynomial (InfinitePlace E × n' × n) ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun Ψ P ↦ modKernel S T a b 𝔪 Ψ P g h)
    (fun Ψ Ψ' P ↦ by simp [modKernel, pairTheta, modDatum, Pi.add_comp])
    (fun c Ψ P ↦ by simp [modKernel, pairTheta, modDatum, Pi.smul_comp])
    (fun Ψ P P' ↦ by simp [modKernel, pairTheta, modDatum])
    (fun c Ψ P ↦ by simp [modKernel, pairTheta, modDatum])

@[simp]
lemma modKernelBilin_apply (g : G E s) (h : G E s') (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) :
    modKernelBilin S T a b 𝔪 g h Ψ P = modKernel S T a b 𝔪 Ψ P g h :=
  rfl

/-- Multiplying the characters `a`, `b` of the Weil representation of a pair by characters `μ`, `μ'`
of `[U(1)]` multiplies the operator `ω_{a,b}(g, h)` by `μ (det h) / μ' (det g)`. -/
lemma pairWeil_twist (μ μ' : AutChar E) (g : G E s) (h : G E s') :
    pairWeil S T (a * μ) (b * μ') (g, h) =
      ((μ.val h.det : ℂ) / (μ'.val g.det : ℂ)) • pairWeil S T a b (g, h) := by
  have h_char : pairChar (a * μ) (b * μ') (g, h) =
      μ.val h.det / μ'.val g.det * pairChar a b (g, h) := by
    simp [field]
  ext f
  simp [pairWeil_apply, h_char, mul_smul]

/-- For hermitian spaces `S` and `T`, characters `a`, `b`, `μ`, `μ'` in `AutChar E`, a test
function `f` in `𝒮 (S.hom T)`, and unitary group elements `g : G E s` and `h : G E s'`:
replacing the characters `a`, `b` of the theta kernel `pairTheta S T a b f` by `a * μ` and `b * μ'`
multiplies its value at `(g, h)` by `μ (det h) / μ' (det g)`. -/
lemma pairTheta_twist (μ μ' : AutChar E) (f : 𝒮 (S.hom T)) (g : G E s) (h : G E s') :
    pairTheta S T (a * μ) (b * μ') f (g, h) =
      μ.val h.det / μ'.val g.det * pairTheta S T a b f (g, h) := by
  simp [pairTheta, pairWeil_twist]

/-- Twisting the characters: for characters μ, μ′ of [U(1)], θ_{aμ,bμ′}[Ψ,P](g,h) = μ(det h)
μ′(det g)⁻¹ θ_{a,b}[Ψ,P](g,h), for all Ψ modulo 𝔪, polynomials P, and g, h. -/
lemma modKernel_twist (μ μ' : AutChar E) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) (g : G E s) (h : G E s') :
    modKernel S T (a * μ) (b * μ') 𝔪 Ψ P g h =
      μ.val h.det / μ'.val g.det * modKernel S T a b 𝔪 Ψ P g h :=
  pairTheta_twist S T a b μ μ' _ g h

/-- For integral finite k in U(S) and k′ in U(T), ω_{a,b}(k, k′) sends the datum `New.modDatum` of
Ψ mod 𝔪 and a real Fock vector v to a(det k′) b(det k)⁻¹ times the datum of x ↦ Ψ(k′⁻¹xk) and v,
with k, k′ reduced modulo 𝔪 and `New.detFin` the finite determinant. -/
lemma pairWeil_modDatum_stdLevel (k : stdLevel E n) (k' : stdLevel E n')
    (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (v : Heisenberg.IsVacuum.Model (realHeisenberg (realSigns E (homSigns s s')))) :
    pairWeil S T a b ((1, k.val), 1, k'.val) (modDatum S T 𝔪 Ψ v) =
      (a.val (detFin s' k'.val) * (b.val (detFin s k.val))⁻¹).val •
        modDatum S T 𝔪 (fun x : Matrix n' n 𝔪.ResidueRing ↦
          Ψ ((𝔪.reductionGL k')⁻¹.val * x * (𝔪.reductionGL k).val)) v := by
  classical
  -- The pair is integral, so it acts on the vacuum by the stated character value.
  have h_vac : pairWeil S T a b ((1, k.val), 1, k'.val) (S.hom T).vacElem =
      (a.val (detFin s' k'.val) * (b.val (detFin s k.val))⁻¹).val • (S.hom T).vacElem :=
    pairWeil_eq_smul_of_projOn_eq ⊤ (by simp) (by simp) (by simp)
  -- Reduction modulo `𝔪` commutes with `x ↦ k'⁻¹ x k`.
  have h_lift : (fun x : n' × n → 𝔸f E ↦ 𝔪.liftFn (Ψ ∘ vecToMatrix)
        (matrixToVec ((k'.val⁻¹ : Gf E n').val.val * vecToMatrix x * k.val.val.val))) =
      𝔪.liftFn ((fun X : Matrix n' n 𝔪.ResidueRing ↦
        Ψ ((𝔪.reductionGL k')⁻¹.val * X * (𝔪.reductionGL k).val)) ∘ vecToMatrix) := by
    funext x
    -- `using!`: identifying the matrices with `stdLevel.map (RingHom.id _)` unfolds `stdLevel.map`.
    simpa [↓ liftFn_apply] using!
      liftIntegralFn_mul (M := idem 𝔪.places • vecToMatrix x) _ _ (stdLevel.map _ (.id _) k)
        (stdLevel.map _ (.id _) k'⁻¹)
  -- The pair is trivial at infinity, so it acts only on the finite datum: it replaces the lift of
  -- `Ψ` by its translate under `x ↦ k'⁻¹ x k` and scales the vacuum.
  rw [modDatum, pairWeil_integrated_fin,
    pairWeil_schrodingerOp_of_mem 𝔪.isConjDisjoint_places k.2 k'.2, h_vac, map_smul, map_smul,
    h_lift, modDatum]

/-- Let `modKernel S T a b 𝔪 Ψ P` be the theta kernel (g, h) ↦ θ(ω_{a,b}(g, h) f) on the adelic
unitary groups of `S` and `T`, where the datum f is built from a function `Ψ` on n′ × n matrices
modulo `𝔪` and the Fock vector of the polynomial `P`. For `k` in the stabiliser of Ô^n in the finite
unitary group, the kernel at (g·(1, k), h) equals the kernel at (g, h) with `Ψ` replaced by
x ↦ b(det k)⁻¹ Ψ(x k̄). Here k̄ is the reduction of `k` modulo `𝔪`. -/
lemma modKernel_mul_stdLevel_left (k : stdLevel E n) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) (g : G E s) (h : G E s') :
    modKernel S T a b 𝔪 Ψ P (g * (1, k.val)) h =
      modKernel S T a b 𝔪 ((b.val (detFin s k.val) : ℂ)⁻¹ •
        fun x : Matrix n' n 𝔪.ResidueRing ↦ Ψ (x * (𝔪.reductionGL k).val)) P g h := by
  -- The pair `((1, k), 1)` acts on the datum of `Ψ` as stated.
  have h_act (v : Heisenberg.IsVacuum.Model (realHeisenberg (realSigns E (homSigns s s')))) :
      pairWeil S T a b ((1, k.val), 1) (modDatum S T 𝔪 Ψ v) = modDatum S T 𝔪
        ((b.val (detFin s k.val) : ℂ)⁻¹ • fun x ↦ Ψ (x * (𝔪.reductionGL k).val)) v := by
    simpa [Prod.mk_one_one, modDatum, Pi.smul_comp] using pairWeil_modDatum_stdLevel S T a b 𝔪 k 1 Ψ
      v
  rw [modKernel, modKernel, ← h_act, ← pairTheta_mul]
  simp

/-- Let `modKernel S T a b 𝔪 Ψ P` be the theta kernel (g, h) ↦ θ(ω_{a,b}(g, h) f) on the adelic
unitary groups of `S` and `T`, where the datum f is built from a function `Ψ` on n′ × n matrices
modulo `𝔪` and the Fock vector of the polynomial `P`. For `k` in the stabiliser of Ô^{n′} in the
finite unitary group, the kernel at (g, (x, h k)) equals the kernel at (g, (x, h)) with `Ψ` replaced
by y ↦ a(det k) Ψ(k̄⁻¹ y). Here k̄ is the reduction of `k` modulo `𝔪`. -/
lemma modKernel_mul_stdLevel_right (k : stdLevel E n') (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) (g : G E s) (x : GInf E s') (h : Gf E n') :
    modKernel S T a b 𝔪 Ψ P g (x, h * k.val) =
      modKernel S T a b 𝔪 ((a.val (detFin s' k.val) : ℂ) •
        fun y : Matrix n' n 𝔪.ResidueRing ↦ Ψ ((𝔪.reductionGL k)⁻¹.val * y)) P g (x, h) := by
  -- The pair `(1, (1, k))` acts on the datum of `Ψ` as stated.
  have h_act (v : Heisenberg.IsVacuum.Model (realHeisenberg (realSigns E (homSigns s s')))) :
      pairWeil S T a b (1, 1, k.val) (modDatum S T 𝔪 Ψ v) = modDatum S T 𝔪
        ((a.val (detFin s' k.val) : ℂ) • fun y ↦ Ψ ((𝔪.reductionGL k)⁻¹.val * y)) v := by
    simpa [Prod.mk_one_one, modDatum, Pi.smul_comp] using pairWeil_modDatum_stdLevel S T a b 𝔪 1 k Ψ
      v
  rw [modKernel, modKernel, ← h_act, ← pairTheta_mul]
  simp

omit [DecidableEq n] [DecidableEq n₁] [DecidableEq n₂] [WeilData E] in
/-- Along a splitting `e` of the coordinates, the lift `liftFn` to finite adelic vectors (Φ of the
reduction mod 𝔪 of the components at the places dividing 𝔪 if these are integral, 0 otherwise) of a
product of functions modulo `𝔪` of the two blocks is the product of their lifts. -/
lemma Modulus.liftFn_mul_blocks (e : n₁ ⊕ n₂ ≃ n) (Φ₁ : (n₁ → 𝔪.ResidueRing) → ℂ)
    (Φ₂ : (n₂ → 𝔪.ResidueRing) → ℂ) :
    𝔪.liftFn (fun y : n → 𝔪.ResidueRing ↦ Φ₁ (y ∘ e ∘ Sum.inl) * Φ₂ (y ∘ e ∘ Sum.inr)) =
      fun x : n → 𝔸f E ↦ 𝔪.liftFn Φ₁ (x ∘ e ∘ Sum.inl) * 𝔪.liftFn Φ₂ (x ∘ e ∘ Sum.inr) := by
  funext x
  -- `x` is integral at `𝔪.places` exactly when both blocks are
  have h_int : (∀ i : n, idem 𝔪.places * x i ∈ Ô E) ↔
      (∀ i : n₁, idem 𝔪.places * x (e (.inl i)) ∈ Ô E) ∧
        ∀ i : n₂, idem 𝔪.places * x (e (.inr i)) ∈ Ô E := by rw [← e.forall_congr_right, Sum.forall]
  simp only [liftFn_apply, comp_def]
  split_ifs <;> simp_all

/-- Let `e` split the coordinates of `S` into those of `V₁` and `V₂`, compatibly with the signs.
Take on each `Vᵢ` the datum given by the Fock vector of a polynomial `Pᵢ`, a function `Φᵢ` modulo
`𝔪` at the primes dividing `𝔪`, and the vacuum elsewhere. The product `boxProd` of these data is
the datum on `S` given by `P₁ P₂` and `Φ₁ Φ₂`, read on the two blocks of coordinates. -/
lemma boxProd_integrated_schrodingerOp_liftFn {e : n₁ ⊕ n₂ ≃ n} (hs : s ∘ e = s₁ ⊕ᵥ s₂)
    (V₁ : Space E n₁ s₁) (V₂ : Space E n₂ s₂) (Φ₁ : (n₁ → 𝔪.ResidueRing) → ℂ)
    (Φ₂ : (n₂ → 𝔪.ResidueRing) → ℂ) (P₁ : MvPolynomial (InfinitePlace E × n₁) ℂ)
    (P₂ : MvPolynomial (InfinitePlace E × n₂) ℂ) :
    boxProd hs
      (V₁.integrated (polyVector (realSigns E s₁) P₁)
        (V₁.schrodingerOp 𝔪.places (𝔪.liftFn Φ₁) V₁.vacElem))
      (V₂.integrated (polyVector (realSigns E s₂) P₂)
        (V₂.schrodingerOp 𝔪.places (𝔪.liftFn Φ₂) V₂.vacElem)) =
      S.integrated
        (polyVector (realSigns E s)
          (rename (Prod.map id (e ∘ Sum.inl)) P₁ * rename (Prod.map id (e ∘ Sum.inr)) P₂))
        (S.schrodingerOp 𝔪.places
          (𝔪.liftFn fun y : n → 𝔪.ResidueRing ↦ Φ₁ (y ∘ e ∘ Sum.inl) * Φ₂ (y ∘ e ∘ Sum.inr))
          S.vacElem) := by
  rw [boxProd_integrated, realBoxProd_polyVector,
    boxProd_schrodingerOp hs 𝔪.isConjDisjoint_places (𝔪.liftFn_mul_blocks e Φ₁ Φ₂)]
  rfl

/-- Seesaw identity in the second space, along a sign-compatible splitting `e` of the coordinates
of `T` into those of `V₁` and `V₂`. Let the point of `T` be block diagonal with blocks the points
of `V₁` and `V₂`, and let `h` be block diagonal with blocks `h₁` and `h₂`. With Ψ₁, P₁ and Ψ₂, P₂
read on the two blocks of rows, θ^{S,T}_{a,bb′}[Ψ₁Ψ₂, P₁P₂](g, h) is
θ^{S,V₁}_{a,b}[Ψ₁,P₁](g,h₁) · θ^{S,V₂}_{a,b′}[Ψ₂,P₂](g,h₂). -/
lemma modKernel_block_right {e : n₁ ⊕ n₂ ≃ n'} (hs : s' ∘ e = s₁ ⊕ᵥ s₂) {V₁ : Space E n₁ s₁}
    {V₂ : Space E n₂ s₂} (h_point : T.x.val.submatrix e e = fromBlocks V₁.x 0 0 V₂.x)
    {h : G E s'} {h₁ : G E s₁} {h₂ : G E s₂}
    (h_group : h.adeleMatrix.submatrix e e = fromBlocks h₁.adeleMatrix 0 0 h₂.adeleMatrix)
    (b' : AutChar E) (Ψ₁ : Matrix n₁ n 𝔪.ResidueRing → ℂ) (Ψ₂ : Matrix n₂ n 𝔪.ResidueRing → ℂ)
    (P₁ : MvPolynomial (InfinitePlace E × n₁ × n) ℂ)
    (P₂ : MvPolynomial (InfinitePlace E × n₂ × n) ℂ) (g : G E s) :
    modKernel S T a (b * b') 𝔪
        (fun x : Matrix n' n 𝔪.ResidueRing ↦
          Ψ₁ (x.submatrix (e ∘ Sum.inl) id) * Ψ₂ (x.submatrix (e ∘ Sum.inr) id))
        (renameRowsCols (e ∘ Sum.inl) id P₁ * renameRowsCols (e ∘ Sum.inr) id P₂) g h =
      modKernel S V₁ a b 𝔪 Ψ₁ P₁ g h₁ * modKernel S V₂ a b' 𝔪 Ψ₂ P₂ g h₂ := by
  -- The product of the two data is the datum of the product function and the product polynomial.
  have h_datum : boxProd (homSigns_sum_target hs)
        (modDatum S V₁ 𝔪 Ψ₁ (polyVector (realSigns E (homSigns s s₁)) P₁))
        (modDatum S V₂ 𝔪 Ψ₂ (polyVector (realSigns E (homSigns s s₂)) P₂)) =
      modDatum S T 𝔪 (fun x : Matrix n' n 𝔪.ResidueRing ↦
          Ψ₁ (x.submatrix (e ∘ Sum.inl) id) * Ψ₂ (x.submatrix (e ∘ Sum.inr) id))
        (polyVector (realSigns E (homSigns s s'))
          (renameRowsCols (e ∘ Sum.inl) id P₁ * renameRowsCols (e ∘ Sum.inr) id P₂)) :=
    boxProd_integrated_schrodingerOp_liftFn (S.hom T) 𝔪 (homSigns_sum_target hs) (S.hom V₁)
      (S.hom V₂) (Ψ₁ ∘ vecToMatrix) (Ψ₂ ∘ vecToMatrix) P₁ P₂
  -- `θ` and `pairWeil` are multiplicative for `boxProd`.
  simp only [modKernel, pairTheta]
  rw [← h_datum, pairWeil_boxProd_target hs S a b b' h_group, theta_boxProd_target hs S h_point]

/-- Seesaw identity in the second space: the kernel of (S, T ⊕ V) for characters a, bb′, the product
ΨΨ′ on the two row blocks and PP′ (P, P′ read in the variables of the two row blocks), at (g, h ⊕
h′), is θ^{S,T}_{a,b}[Ψ,P](g,h) · θ^{S,V}_{a,b′}[Ψ′,P′](g,h′). -/
lemma modKernel_sum_right (b' : AutChar E) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (Ψ' : Matrix n₁ n 𝔪.ResidueRing → ℂ) (P : MvPolynomial (InfinitePlace E × n' × n) ℂ)
    (P' : MvPolynomial (InfinitePlace E × n₁ × n) ℂ) (g : G E s) (h : G E s') (h' : G E s₁) :
    modKernel S (T.sum V) a (b * b') 𝔪
        (fun x : Matrix (n' ⊕ n₁) n 𝔪.ResidueRing ↦ Ψ x.toRows₁ * Ψ' x.toRows₂)
        (renameRowsCols Sum.inl id P * renameRowsCols Sum.inr id P') g (G.sum (h, h')) =
      modKernel S T a b 𝔪 Ψ P g h * modKernel S V a b' 𝔪 Ψ' P' g h' :=
  -- The point of `T.sum V` and `G.sum (h, h')` are block diagonal along the identity splitting.
  modKernel_block_right S (T.sum V) a b 𝔪 signs_comp_refl (by aesop) (by aesop) b' Ψ Ψ' P P' g

/-- For a modulus 𝔪, a function Ψ on `n' × n` matrices over O_E/𝔪 and a polynomial P in variables
indexed by (infinite place, row, column), the theta kernel θ^{S,T}_{a,b}[Ψ,P](g,h) = θ(ω_{a,b}(g,h)
f) (`modKernel`) is built from the datum f given by Ψ and the Fock vector of P. Seesaw identity in
the first space: the kernel of (S ⊕ V, T) for characters aa′, b, the product ΨΨ′ on the two column
blocks and PP′ (P, P′ read in the variables of the two column blocks), at (g ⊕ g′, h), is
θ^{S,T}_{a,b}[Ψ,P](g,h) · θ^{V,T}_{a′,b}[Ψ′,P′](g′,h). -/
lemma modKernel_sum_left (a' : AutChar E) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (Ψ' : Matrix n' n₁ 𝔪.ResidueRing → ℂ) (P : MvPolynomial (InfinitePlace E × n' × n) ℂ)
    (P' : MvPolynomial (InfinitePlace E × n' × n₁) ℂ) (g : G E s) (g' : G E s₁) (h : G E s') :
    modKernel (S.sum V) T (a * a') b 𝔪
        (fun x : Matrix n' (n ⊕ n₁) 𝔪.ResidueRing ↦ Ψ x.toCols₁ * Ψ' x.toCols₂)
        (renameRowsCols id Sum.inl P * renameRowsCols id Sum.inr P') (G.sum (g, g')) h =
      modKernel S T a b 𝔪 Ψ P g h * modKernel V T a' b 𝔪 Ψ' P' g' h := by
  -- The product of the two data is the datum of the product function and the product polynomial.
  have h_datum : boxProd homSigns_sum_source
        (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s s')) P))
        (modDatum V T 𝔪 Ψ' (polyVector (realSigns E (homSigns s₁ s')) P')) =
      modDatum (S.sum V) T 𝔪 (fun x : Matrix n' (n ⊕ n₁) 𝔪.ResidueRing ↦ Ψ x.toCols₁ * Ψ' x.toCols₂)
        (polyVector (realSigns E (homSigns (s ⊕ᵥ s₁) s'))
          (renameRowsCols id Sum.inl P * renameRowsCols id Sum.inr P')) :=
    boxProd_integrated_schrodingerOp_liftFn ((S.sum V).hom T) 𝔪 homSigns_sum_source (S.hom T)
      (V.hom T) (Ψ ∘ vecToMatrix) (Ψ' ∘ vecToMatrix) P P'
  -- `θ` and `pairWeil` are multiplicative for `boxProd`.
  simp only [modKernel, pairTheta]
  rw [← h_datum, pairWeil_boxProd_source, theta_boxProd_source]

/-- Sums in the second space, with standard characters (`New.stdKernel`): the kernel of (S, T ⊕ V)
for the product ΨΨ′ on the two row blocks and PP′, at (g, h ⊕ h′), is
θ^{S,T}[Ψ,P](g,h) · θ^{S,V}[Ψ′,P′](g,h′). This is a special case of `New.modKernel_sum_right`. -/
lemma stdKernel_sum_right (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ) (Ψ' : Matrix n₁ n 𝔪.ResidueRing → ℂ)
    (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) (P' : MvPolynomial (InfinitePlace E × n₁ × n) ℂ)
    (g : G E s) (h : G E s') (h' : G E s₁) :
    stdKernel S (T.sum V) 𝔪 (fun x : Matrix (n' ⊕ n₁) n 𝔪.ResidueRing ↦ Ψ x.toRows₁ * Ψ' x.toRows₂)
        (renameRowsCols Sum.inl id P * renameRowsCols Sum.inr id P') g (G.sum (h, h')) =
      stdKernel S T 𝔪 Ψ P g h * stdKernel S V 𝔪 Ψ' P' g h' := by
  rw [stdKernel, stdChar_sum, modKernel_sum_right]

/-- Sums in the first space, with standard characters (`New.stdKernel`): the kernel of (S ⊕ V, T)
for the product ΨΨ′ on the two column blocks and PP′, at (g ⊕ g′, h), is
θ^{S,T}[Ψ,P](g,h) · θ^{V,T}[Ψ′,P′](g′,h). This is a special case of `New.modKernel_sum_left`. -/
lemma stdKernel_sum_left (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ) (Ψ' : Matrix n' n₁ 𝔪.ResidueRing → ℂ)
    (P : MvPolynomial (InfinitePlace E × n' × n) ℂ)
    (P' : MvPolynomial (InfinitePlace E × n' × n₁) ℂ) (g : G E s) (g' : G E s₁) (h : G E s') :
    stdKernel (S.sum V) T 𝔪 (fun x : Matrix n' (n ⊕ n₁) 𝔪.ResidueRing ↦ Ψ x.toCols₁ * Ψ' x.toCols₂)
        (renameRowsCols id Sum.inl P * renameRowsCols id Sum.inr P') (G.sum (g, g')) h =
      stdKernel S T 𝔪 Ψ P g h * stdKernel V T 𝔪 Ψ' P' g' h := by
  rw [stdKernel, stdChar_sum, modKernel_sum_left]

/-! ### Negation -/

/-- The unit of O_E/𝔪 that is the reduction of the chosen element of norm −1 of Ô. -/
def Modulus.normNegOne : 𝔪.ResidueRingˣ := Weil.normNegOne.map 𝔪.reduction.toMonoidHom

/-- Let Ψ be a function on n′ × n matrices over O_E/𝔪 and P a complex polynomial. The antilinear map
`negSource.map`, from data on Hom(S,T) to data on Hom(S⁻,T), sends the datum `modDatum` of v_P and Ψ
to the datum of v_{P̄} and x ↦ conj(Ψ(u⁻¹x)). Here P̄ is P with conjugated coefficients, the
polynomial vectors use the signs s′s and s′(−s) respectively, and u = `𝔪.normNegOne` is the unit of
O_E/𝔪 obtained by reducing the chosen ε ∈ Ô with εε̄ = −1. -/
lemma map_negSource_modDatum (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) :
    negSource.map (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s s')) P)) =
      modDatum S.neg T 𝔪 (fun x : Matrix n' n 𝔪.ResidueRing ↦ conj (Ψ (𝔪.normNegOne⁻¹ • x)))
        (polyVector (realSigns E (homSigns (-s) s')) (MvPolynomial.map conj P)) := by
  have h_idem (R : Set (FinPlace E)) (x : n' × n → 𝔸f E) :
      (negSource (s := s) (s' := s')).finEquiv (idem R • x) =
        idem R • (negSource (s := s) (s' := s')).finEquiv x :=
    smul_comm (Weil.normNegOne (E := E))⁻¹ (idem R) x
  -- The real part: negating the signs conjugates the holomorphic coordinates.
  have h_real : negSource.realMap (polyVector (realSigns E (homSigns s s')) P) =
      polyVector (realSigns E (homSigns (-s) s')) (MvPolynomial.map conj P) := by
    ext x
    have h_coord : conj ∘ holomorphicCoord (realSigns E (homSigns s s')) x =
        holomorphicCoord (realSigns E (homSigns (-s) s')) x := funext fun i ↦ by
      rcases Int.units_eq_one_or (realSigns E (homSigns s s') i) with h_sign | h_sign <;>
        simp_all [holomorphicCoord_eq, pairSign]
    simp [CoordChange.realMap, negSource, (isVacuum_realVac (ε := 1)).conj_apply x, map_eval,
      h_coord]
  -- The finite part: `negSource` scales by the unit `normNegOne⁻¹` of `Ô`, which keeps integrality
  -- and reduces to `𝔪.normNegOne⁻¹`.
  have h_fin : (fun x : n' × n → 𝔸f E ↦
        conj (𝔪.liftFn (Ψ ∘ vecToMatrix) ((negSource (s := s) (s' := s')).finEquiv x))) =
      𝔪.liftFn ((fun X : Matrix n' n 𝔪.ResidueRing ↦ conj (Ψ (𝔪.normNegOne⁻¹ • X))) ∘
        vecToMatrix) := by
    funext x
    let c : (Ô E)ˣ := Weil.normNegOne⁻¹
    have h_int (i : n' × n) : idem 𝔪.places * (c • x) i ∈ Ô E ↔ idem 𝔪.places * x i ∈ Ô E := by
      simp [Units.smul_def, Subring.smul_def, mem_Ô, isUnit_Ô.1]
    change conj (𝔪.liftFn (Ψ ∘ vecToMatrix) (c • x)) = _
    rw [liftFn_apply, liftFn_apply]
    by_cases hx : ∀ i : n' × n, idem 𝔪.places * x i ∈ Ô E
    · simp only [dite_eq_left hx, dite_eq_left fun i ↦ (h_int i).2 (hx i), Function.comp_apply]
      congr 2 with i j
      simp only [vecToMatrix, of_apply, Pi.smul_apply, mul_smul_comm]
      exact map_mul 𝔪.reduction c.val ⟨idem 𝔪.places * x (i, j), hx (i, j)⟩
    · rw [dite_eq_right hx, dite_eq_right fun h ↦ hx fun i ↦ (h_int i).1 (h i), map_zero]
  rw [modDatum, map_integrated, h_real, CoordChange.map_schrodingerOp _ (h_idem _) (h_idem _)
    𝔪.isConjDisjoint_places 𝔪.isConjDisjoint_places, h_fin, modDatum]

/-- Negating S conjugates theta kernels: for some c of modulus one depending only on S and T, the
conjugate of θ^{S,T}_{a,b}[Ψ,P](g,h) (`New.modKernel`, the theta kernel of the datum built from Ψ on
matrices mod 𝔪 and the Fock vector of P, with a, b twisting the action) is c
θ^{S⁻,T}_{a⁻¹υⁿ,b⁻¹υ^{n′}}[Ψ′,P̄](g,h) for all a, b, 𝔪, Ψ, P, g, h, where n, n′ are the sizes. Here
S⁻ is `New.Space.neg` S, and Ψ′(x) is the conjugate of Ψ(u⁻¹x), with u the unit of O_E/𝔪 reducing
the chosen element of norm −1 of Ô. P̄ has the conjugate coefficients, and υ is the splitting
character of the Weil data restricted to the norm-one ideles. On the right, `New.G.neg` moves g to
the group of S⁻. -/
lemma exists_conj_modKernel_eq_mul_modKernel_neg :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ∀ (a b : AutChar E) (𝔪 : Modulus E) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
          (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) (g : G E s) (h : G E s'),
        conj (modKernel S T a b 𝔪 Ψ P g h) =
          c * modKernel S.neg T (a⁻¹ * upsilonU1 ^ card n) (b⁻¹ * upsilonU1 ^ card n') 𝔪
            (fun x : Matrix n' n 𝔪.ResidueRing ↦ conj (Ψ (𝔪.normNegOne⁻¹ • x)))
            (MvPolynomial.map conj P) (G.neg g) h := by
  -- The map `negSource` conjugates `θ` up to the phase `c` and intertwines the actions `pairWeil`.
  obtain ⟨c, hc, hθ⟩ := exists_theta_negSource S T
  refine ⟨c, hc, fun a b 𝔪 Ψ P g h ↦ ?_⟩
  simp only [modKernel, pairTheta]
  rw [← hθ, map_smul, ← pairWeil_negSource, map_negSource_modDatum, smul_eq_mul]

/-- Negating S conjugates kernels with standard characters (`New.stdKernel`): for some c of modulus
one depending only on S and T, the complex conjugate of θ^{S,T}[Ψ,P](g,h) is c υ(det g)^{−(n₊ − n₋)}
θ^{S⁻,T}[Ψ′,P̄](g,h) for all 𝔪, Ψ, P, g, h. Here υ is `New.WeilData.upsilonU1`, the splitting
character of the Weil data restricted to the norm-one ideles (a character of U(1)(𝔸) trivial on
U(1)(E)). n₊ = `negCount (-s')` and n₋ = `negCount s'` count the signs 1 and −1 of T, so that
n₊ − n₋ is its signature. S⁻ is `New.Space.neg` S, and Ψ′(x) is the conjugate of Ψ(u⁻¹x), where
u = `New.Modulus.normNegOne` is the reduction mod 𝔪 of the chosen ε in Ô with ε̄ε = −1. P̄ has the
conjugate coefficients. On the right, `New.G.neg` moves g to the group of S⁻. This is a corollary of
`New.exists_conj_modKernel_eq_mul_modKernel_neg`. -/
lemma exists_stdKernel_neg_left :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ∀ (𝔪 : Modulus E) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
          (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) (g : G E s) (h : G E s'),
        conj (stdKernel S T 𝔪 Ψ P g h) =
          c * (upsilonU1.val g.det : ℂ) ^
              (-((Exchange.negCount (-s') : ℤ) - Exchange.negCount s')) *
            stdKernel S.neg T 𝔪 (fun x : Matrix n' n 𝔪.ResidueRing ↦ conj (Ψ (𝔪.normNegOne⁻¹ • x)))
              (MvPolynomial.map conj P) (G.neg g) h := by
  -- The rule for general characters gives S⁻ its standard character and T that of T⁻, which is the
  -- standard character of T times μ = υ^{n₊ − n₋}; the twist rule takes out μ(det g)⁻¹.
  obtain ⟨c, hc_norm, h_conj⟩ := exists_conj_modKernel_eq_mul_modKernel_neg S T
  refine ⟨c, hc_norm, fun 𝔪 Ψ P g h ↦ ?_⟩
  let μ : AutChar E := stdChar (-s') / stdChar s'
  have h_char_S : (stdChar s)⁻¹ * upsilonU1 ^ card n = (stdChar (-s) * 1 : AutChar E) := by
    simp [stdChar_neg]
  have h_char_T : (stdChar s')⁻¹ * upsilonU1 ^ card n' = stdChar s' * μ := by simp [μ, stdChar_neg]
  have h_factor : ((1 : AutChar E).val h.det : ℂ) / μ.val (G.neg g).det =
      (upsilonU1.val g.det : ℂ) ^ (-((Exchange.negCount (-s') : ℤ) - Exchange.negCount s')) := by
    simp [μ, stdChar, zpow_sub₀, div_eq_mul_inv]
  rw [h_conj, h_char_S, h_char_T, modKernel_twist, h_factor, mul_assoc]

/-! ### Passing to a smaller ideal -/

variable {S T a b 𝔪}

/-- If the ideal 𝔪′ is contained in 𝔪, the datum modulo 𝔪′ given by the pullback of Ψ under
reduction to O_E/𝔪 and by the real Fock vector v equals the datum modulo 𝔪 given by Ψ and v. -/
lemma modDatum_factor {𝔪' : Modulus E} (h : 𝔪'.ideal ≤ 𝔪.ideal) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (v : Heisenberg.IsVacuum.Model (realHeisenberg (realSigns E (homSigns s s')))) :
    modDatum S T 𝔪' (fun x : Matrix n' n 𝔪'.ResidueRing ↦ Ψ (x.map (factor h))) v =
      modDatum S T 𝔪 Ψ v := by
  -- The box function at the new places `R` names a projection that fixes the vacuum, so by
  -- `schrodingerOp_union` the right side is named at `𝔪'.places` by `𝔪.liftFn _` times this box
  -- function.
  let R : Set (FinPlace E) := 𝔪'.places \ 𝔪.places
  have h_sub : 𝔪.places ⊆ 𝔪'.places := fun w hw ↦ h.trans hw
  have h_union : 𝔪.places ∪ R = 𝔪'.places := Set.union_sdiff_cancel h_sub
  have h_conj : (𝔪.places ∪ R).IsConjDisjoint := by simpa [h_union] using 𝔪'.isConjDisjoint_places
  have h_diff : R.IsConjDisjoint :=
    𝔪'.isConjDisjoint_places.mono Set.sdiff_subset (Set.preimage_mono Set.sdiff_subset)
  have h_lift : 𝔪.liftFn (Ψ ∘ vecToMatrix) * boxIndicator (n' × n) R =
      𝔪'.liftFn ((fun X : Matrix n' n 𝔪'.ResidueRing ↦ Ψ (X.map (factor h))) ∘ vecToMatrix) := by
    funext x
    have h_int : (∀ i : n' × n, idem 𝔪'.places * x i ∈ Ô E) ↔
        (∀ i : n' × n, idem 𝔪.places * x i ∈ Ô E) ∧ x ∈ integralBox (n' × n) R := by
      simp [← h_union, idem_mul_mem_Ô, mem_integralBox, or_imp, forall_and]
    simp only [Pi.mul_apply, liftFn_apply, boxIndicator_apply]
    by_cases hx : ∀ i : n' × n, idem 𝔪'.places * x i ∈ Ô E
    · obtain ⟨hx_old, hx_new⟩ := h_int.1 hx
      -- The parts of `x` at the two sets of places agree modulo `𝔪`.
      have h_red (i : n' × n) : 𝔪.reduction ⟨idem 𝔪.places * x i, hx_old i⟩ =
          factor h (𝔪'.reduction ⟨idem 𝔪'.places * x i, hx i⟩) := by
        simpa using 𝔪.reduction_congr fun w hw ↦ by simp [hw, h_sub hw]
      simp [dite_eq_left hx, dite_eq_left hx_old, ite_eq_left hx_new, h_red, vecToMatrix,
        Matrix.map]
    · -- Either `x` is not integral at `𝔪.places`, or it lies outside the box at `R`.
      obtain hx_old | hx_new := not_and_or.1 (mt h_int.2 hx)
      · rw [dite_eq_right hx, dite_eq_right hx_old, zero_mul]
      · rw [dite_eq_right hx, ite_eq_right hx_new, mul_zero]
  rw [modDatum, modDatum, ← h_lift, ← h_union,
    schrodingerOp_union _ h_conj disjoint_sdiff_self_right,
    schrodingerOp_boxIndicator h_diff, projOn_vacElem]

/-- Change of modulus: if the ideal 𝔪′ is contained in 𝔪, a function Ψ on matrices modulo 𝔪, read
modulo 𝔪′ through the reduction O_E/𝔪′ → O_E/𝔪, has the same theta kernel as Ψ, for all characters
a, b of [U(1)], polynomials P and points g, h. -/
lemma modKernel_factor {𝔪' : Modulus E} (h_le : 𝔪'.ideal ≤ 𝔪.ideal)
    (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ) (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) (g : G E s)
    (h : G E s') :
    modKernel S T a b 𝔪' (fun x : Matrix n' n 𝔪'.ResidueRing ↦ Ψ (x.map (factor h_le))) P g h =
      modKernel S T a b 𝔪 Ψ P g h := by
  rw [modKernel, modKernel, modDatum_factor h_le]

/-! ### Relabelling, and the seesaw identity for a standard space split into blocks -/

/-- The theta kernel θ[Ψ, P](g, h) is unchanged when the coordinates of S and T are relabelled
by sign-compatible bijections e, e′ and Ψ, P, g, h are relabelled accordingly. -/
lemma modKernel_reindex (e : n ≃ n₁) (he : s ∘ e.symm = s₁) (e' : n' ≃ n₂) (he' : s' ∘ e'.symm = s₂)
    (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ) (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) (g : G E s)
    (h : G E s') :
    modKernel (S.reindex (t := s₁) e he) (T.reindex (t := s₂) e' he') a b 𝔪
        (fun x : Matrix n₂ n₁ 𝔪.ResidueRing ↦ Ψ (x.submatrix e' e)) (renameRowsCols e' e P)
        (G.reindex e he g) (G.reindex e' he' h) =
      modKernel S T a b 𝔪 Ψ P g h := by
  subst he he'
  -- View the relabelled space as the sum of `S.hom T` and the zero space `V₀`, on which the
  -- trivial datum has theta value `1`; then `θ`, `ω` and the data are multiplicative.
  let S' : Space E n₁ (s ∘ e.symm) := S.reindex e rfl
  let T' : Space E n₂ (s' ∘ e'.symm) := T.reindex e' rfl
  let g' : G E (s ∘ e.symm) := G.reindex e rfl g
  let h' : G E (s' ∘ e'.symm) := G.reindex e' rfl h
  let ε : (n' × n) ⊕ Empty ≃ n₂ × n₁ := .trans (.sumEmpty ..) (e'.prodCongr e)
  let V₀ : Space E Empty 1 := stdSpace E Empty
  let f₀ : 𝒮 V₀ :=
    V₀.integrated (polyVector (realSigns E 1) 1) (V₀.schrodingerOp 𝔪.places (𝔪.liftFn 1) V₀.vacElem)
  have h_one : V₀.θ (V₀.ω 1 f₀) = 1 := by
    simp [f₀, liftFn_one, schrodingerOp_boxIndicator 𝔪.isConjDisjoint_places, theta_apply,
      vacElem_apply_eq_prod_lineTheta, funext_iff]
  have h_signs : homSigns (s ∘ e.symm) (s' ∘ e'.symm) ∘ ε = homSigns s s' ⊕ᵥ 1 := by
    simp [ε, funext_iff, pairSign]
  have h_point : (S'.hom T').x.val.submatrix ε ε = fromBlocks (S.hom T).x 0 0 V₀.x := by
    simp [S', T', ε, ← ext_iff, hom, Space.reindex]
  have h_group : (G.onHom (g', h')).adeleMatrix.submatrix ε ε =
      fromBlocks (G.onHom (g, h)).adeleMatrix 0 0 (1 : G E (1 : Empty → ℤˣ)).adeleMatrix := by
    simp [g', h', ε, ← ext_iff, ← map_inv]
  -- The product of the datum with the trivial one is the relabelled datum.
  have h_datum : boxProd (V := S'.hom T') h_signs
        (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s s')) P)) f₀ =
      modDatum S' T' 𝔪 (fun x : Matrix n₂ n₁ 𝔪.ResidueRing ↦ Ψ (x.submatrix e' e))
        (polyVector (realSigns E (homSigns (s ∘ e.symm) (s' ∘ e'.symm)))
          (renameRowsCols e' e P)) := by
    simp only [modDatum, f₀, boxProd_integrated_schrodingerOp_liftFn, map_one, Pi.one_apply,
      mul_one]
    rfl
  have h_char : pairChar a b (g', h') = pairChar a b (g, h) := by
    simp [g', h', G.det, U.det, ← G.adeleMatrix.eq_1]
  simp only [modKernel, pairTheta, pairWeil_apply, map_smul]
  rw [h_char, ← h_datum, omega_boxProd _ h_group, theta_boxProd _ h_point, h_one, mul_one]

/-- Seesaw identity for the standard space I_n = `New.stdSpace E n`, split as I_{n₁} ⊕ I_{n₂} along
a bijection ε, with `U.block ε` the block diagonal embedding of the unitary groups. Here
`New.modKernelStdSpace` is the theta kernel with a standard second space and finite second argument.
With Ψ, P read on the n₁ rows and Ψ′, P′ on the n₂ rows, θ^{T,I_n}_{a,bb′}[ΨΨ′, PP′](g, h ⊕ h′) =
θ^{T,I_{n₁}}_{a,b}[Ψ,P](g,h) · θ^{T,I_{n₂}}_{a,b′}[Ψ′,P′](g,h′) for finite adelic h, h′. The
polynomials are read on the blocks by `renameRowsCols`, which renames the rows of the variables. -/
lemma Rows.modKernelStdSpace_block {T : Space E n' s'} {a b : AutChar E} {𝔪 : Modulus E}
    (ε : n₁ ⊕ n₂ ≃ n) (b' : AutChar E) (Ψ : Matrix n₁ n' 𝔪.ResidueRing → ℂ)
    (Ψ' : Matrix n₂ n' 𝔪.ResidueRing → ℂ) (P : MvPolynomial (InfinitePlace E × n₁ × n') ℂ)
    (P' : MvPolynomial (InfinitePlace E × n₂ × n') ℂ) (g : G E s')
    (h : U (1 : Matrix n₁ n₁ (𝔸f E))) (h' : U (1 : Matrix n₂ n₂ (𝔸f E))) :
    modKernelStdSpace T a (b * b') 𝔪
        (fun x : Matrix n n' 𝔪.ResidueRing ↦
          Ψ (x.submatrix (ε ∘ Sum.inl) id) * Ψ' (x.submatrix (ε ∘ Sum.inr) id))
        (renameRowsCols (ε ∘ Sum.inl) id P * renameRowsCols (ε ∘ Sum.inr) id P') g
        (U.block ε (h, h')) =
      modKernelStdSpace T a b 𝔪 Ψ P g h * modKernelStdSpace T a b' 𝔪 Ψ' P' g h' := by
  -- The signs, the point of `stdSpace E n` and the matrix of `U.block ε (h, h')` split along `ε`.
  have h_signs : (1 : n → ℤˣ) ∘ ε = (1 : n₁ → ℤˣ) ⊕ᵥ (1 : n₂ → ℤˣ) := by aesop
  refine modKernel_block_right T (stdSpace E n) a b 𝔪 h_signs ?_ ?_ b' Ψ Ψ' P P' g
  · simp
  · aesop (add simp (reindex_equiv ε)) (add simp [Matrix.one_apply])

end New

end KernelLaws

end
