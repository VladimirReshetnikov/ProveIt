import Lib.General.LinearAlgebra.TensorChains
import Lib.Weil.CompactLift.ThetaKernelDefs
import Lib.Weil.DualPair.Flip

/-!
# Two edges V → V′ → V″ joined into one datum of the pair (V′, V⁻ ⊕ V″)

This file joins data on two consecutive edges V → V′ → V″ into one datum of the pair
(V′, V⁻ ⊕ V″), where V⁻ ⊕ V″ is `New.Seesaw.flipSum`. A datum on `Hom(V, V′)` is carried by the
adjoint to `Hom(V′, V⁻)` and multiplied with a datum on `Hom(V′, V″)`. The joining map is
compatible with the theta functional `New.Space.θ`, with translations and with the Weil actions,
which become `New.Seesaw.tripleWeil`. On the finite parts `New.Space.finitePart`, the spans of the
finite translates of the vacuum, it induces an injective map from the tensor product onto the
finite part.

## Main definitions and results

* `New.Seesaw.arrowProduct`: for two consecutive edges V → V′ → V″, the bounded bilinear map that
  joins data on Hom(V, V′) and Hom(V′, V″) into one datum of the pair (V′, V⁻ ⊕ V″). It is
  compatible with the theta functional up to a nonzero constant (`New.Seesaw.theta_arrowProduct`)
  and with the Weil actions (`New.Seesaw.arrowProduct_twistedPairWeil`).
* `New.Seesaw.homHeisenbergOp_arrowProduct`, `New.Seesaw.finHeisenbergOp_arrowProduct`: the
  joining map is compatible with translations.
* `New.Seesaw.arrowTensor`: the induced map on the tensor product of the finite parts. It is
  injective (`New.Seesaw.injective_arrowTensor`), with a left inverse
  (`New.Seesaw.leftInverse_arrowTensor`), and its range is the finite part
  (`New.Seesaw.range_arrowTensor`).
* `New.Seesaw.theta_tripleWeil_rat_mul`: `θ` of `New.Seesaw.tripleWeil` is invariant under rational
  points in the first two groups.

Notions from other files:
* `New.WeilData`: Weil data on a stably unramified E. They consist of ȷ in E with ȷ = −ȷ̄, Im τȷ > 0
  for every τ in the CM type and (1 − ȷ⁻¹)/2 integral; a finite idele α for which the completed
  integers Ô are self-dual under (z, u) ↦ ψ_f(ȷαᾱzu); and a splitting character υ equal to −1 at
  uniformisers of the places w with w = w̄; its restriction to the norm-one ideles is
  `New.WeilData.upsilonU1`.
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to the diagonal matrix of its signs at the infinite places and 1 at the finite places.
* `New.𝒮`: The Banach space 𝒮(V) of integrable functions c on 𝔸^n with c(x) = ∫ c(y)β(y,x)e(x−y) dy,
  under the L¹ norm; β is the adelic bicharacter and e the vacuum function `New.vacuumFn`.
* `New.pairWeil`: The action ω_{a,b}(g, h) = χ_{a,b}(g, h) ω(x ↦ hxg⁻¹) on 𝒮(Hom(S, T)), where
  χ_{a,b}(g, h) = a(det h) b(det g)⁻¹ is `New.pairChar`. The theta kernel `New.pairTheta` S T a b f
  (g, h) is θ(ω_{a,b}(g, h) f), where θ is the theta functional `New.Space.θ`.
* `New.Seesaw.flipSpace` (in `Lib.Weil.DualPair.Flip`): the opposite space V⁻ of V, with matrix −J
  and the opposite signs.

## Relation to the literature

Known; see `Lib.Weil.DualPair.ThetaLiftConvergence` for sources.
-/

noncomputable section

namespace New.Seesaw

open Prod Matrix TensorProduct Space WeilData Submodule Fintype LinearMap Weil

variable {E ι ι' ι'' : Type} [Field E] [CMType E] [WeilData E] [Fintype ι] [DecidableEq ι]
  [Fintype ι'] [DecidableEq ι'] [Fintype ι''] [DecidableEq ι'']
  {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {ε'' : ι'' → ℤˣ} {V : Space E ι ε} {V' : Space E ι' ε'}
  {V'' : Space E ι'' ε''} (f : 𝒮 (V.hom V')) (f' : 𝒮 (V'.hom V'')) (a b : AutChar E) (g : G E ε)
  (t : (V.hom V').finitePart ⊗[ℂ] (V'.hom V'').finitePart)

/-- For hermitian spaces V and V'', the orthogonal sum V⁻ ⊕ V'' of the opposite space
V⁻ = `New.Seesaw.flipSpace V` and V''. -/
abbrev flipSum (V : Space E ι ε) (V'' : Space E ι'' ε'') : Space E (ι ⊕ ι'') (-ε ⊕ᵥ ε'') :=
  (flipSpace V).sum V''

/-- The bounded bilinear map combining data on Hom(V,V') and Hom(V',V'') into one datum on
Hom(V', V⁻ ⊕ V''), the first being carried to Hom(V', V⁻) by a scaled adjoint. -/
def arrowProduct : 𝒮 (V.hom V') →L[ℂ] 𝒮 (V'.hom V'') →L[ℂ] 𝒮 (V'.hom (flipSum V V'')) :=
  (V'.hom (flipSum V V'')).boxProd (homSigns_sum_target signs_comp_refl) (V₂ := V'.hom V'') ∘L
    (flipCoords star_normNegOne_mul_self rfl).map (V₁ := V.hom V') (V := V'.hom (flipSpace V))

/-- For g = (g₁,g₂,g₃), the Weil operator of (g₂, g₁ ⊕ g₃) on Hom(V', V⁻ ⊕ V''), times the product
of `pairChar` for `rankTwist a` at (g₁,g₂), `pairChar` for `rankTwist b` at (g₂,g₃) and `pairChar`
for (υ^{rk V'}, υ^{rk V}) at (g₂,g₁). -/
def tripleWeil (g : G E ε × G E ε' × G E ε'') :
    𝒮 (V'.hom (flipSum V V'')) →L[ℂ] 𝒮 (V'.hom (flipSum V V'')) :=
  (pairChar (rankTwist a ι) (rankTwist a ι') (Prod.fst g, g.2.1) *
      pairChar (rankTwist b ι') (rankTwist b ι'') g.2 *
      pairChar (upsilonU1 ^ card ι') (upsilonU1 ^ card ι) (g.2.1, g.1)) •
    (V'.hom (flipSum V V'')).ω (G.onHom (g.2.1, G.sum (g.1.neg, g.2.2)))

/-- The linear map induced by `New.Seesaw.arrowProduct` from the tensor product of the finite parts
𝒮_f of Hom(V,V') and Hom(V',V'') to the data on Hom(V', V⁻ ⊕ V''). -/
def arrowTensor :
    (V.hom V').finitePart ⊗[ℂ] (V'.hom V'').finitePart →ₗ[ℂ] 𝒮 (V'.hom (flipSum V V'')) :=
  TensorProduct.lift arrowProduct.toLinearMap₁₂ ∘ₗ
    mapIncl (V.hom V').finitePart (V'.hom V'').finitePart

/-- The Weil representation of the finite adelic U(V) × U(V') on finite data for Hom(V,V'),
normalised by the characters `rankTwist a` for the ranks of V and V'. -/
abbrev liftWeilFin : Gf E ι × Gf E ι' →* Module.End ℂ ↥(V.hom V').finitePart :=
  pairWeilFinite V V' (rankTwist a ι) (rankTwist a ι')

/-- `New.Seesaw.arrowProduct` applied: the product of the flip of f with f'. -/
private lemma arrowProduct_apply :
    arrowProduct f f' =
      (V'.hom (flipSum V V'')).boxProd (homSigns_sum_target signs_comp_refl) (V₂ := V'.hom V'')
        ((flipCoords star_normNegOne_mul_self rfl).map (V₁ := V.hom V') (V := V'.hom (flipSpace V))
          f)
        f' :=
  rfl

/-- The entries of a block matrix `fromRows A B` over the first block of rows are those of A. -/
private lemma matrixToVec_fromRows_comp_inl {R m₁ m₂ k : Type*} (A : Matrix m₁ k R)
    (B : Matrix m₂ k R) :
    matrixToVec (fromRows A B) ∘ (Equiv.sumProdDistrib m₁ m₂ k).symm ∘ Sum.inl = matrixToVec A :=
  rfl

/-- The entries of a block matrix `fromRows A B` over the second block of rows are those of B. -/
private lemma matrixToVec_fromRows_comp_inr {R m₁ m₂ k : Type*} (A : Matrix m₁ k R)
    (B : Matrix m₂ k R) :
    matrixToVec (fromRows A B) ∘ (Equiv.sumProdDistrib m₁ m₂ k).symm ∘ Sum.inr = matrixToVec B :=
  rfl

@[simp]
lemma ratCoordMatrix_flipSpace : (flipSpace V).ratCoordMatrix g.neg = V.ratCoordMatrix g := by
  simp [ratCoordMatrix_eq, ← star_mul, flipSpace_x, ← smul_eq_diagonal_mul, ← map_inv,
    ← smul_eq_mul_diagonal, Matrix.mul_assoc, ← mul_smul]

/-! ### Compatibility of the joining map with `θ`, translations and the Weil action -/

variable (V V' V'') in
/-- There is a constant `z ≠ 0` such that the theta functional of the joined datum
`New.Seesaw.arrowProduct f f'` is `z` times the product of the theta functionals of `f` and `f'`. -/
lemma theta_arrowProduct :
    ∃ z ≠ (0 : ℂ), ∀ (f : 𝒮 (V.hom V')) (f' : 𝒮 (V'.hom V'')),
      (V'.hom (flipSum V V'')).θ (arrowProduct f f') =
        z * ((V.hom V').θ f * (V'.hom V'').θ f') := by
  -- `arrowProduct f f'` is the product of the flip of `f` with `f'`; `θ` is multiplicative on such
  -- products, and the flip multiplies `θ f` by a constant `z` of modulus one.
  obtain ⟨z, hz, h_flip⟩ := exists_pairTheta_flip star_normNegOne_mul_self rfl V V' (flipSpace V) 1
    (by simp [flipSpace_x, ← smul_eq_diagonal_mul]) 1
  refine ⟨z, fun hz_zero ↦ by simp [hz_zero] at hz, fun f f' ↦ ?_⟩
  -- At the identity the theta kernels are the values of `θ`.
  have h_one :
      (V'.hom (flipSpace V)).θ
          ((flipCoords star_normNegOne_mul_self rfl).map (V := V'.hom (flipSpace V)) f) =
        z * (V.hom V').θ f := by
    simpa [pairTheta, mk_one_one] using h_flip 1 f 1 1 1 (by simp)
  rw [arrowProduct_apply, theta_boxProd_target rfl _ rfl, h_one, mul_assoc]

/-- Translating the joined datum by the block matrix with rows `w*` (the adjoint of `w`) and `w'`
is the same as translating `f` by `w` and `f'` by `w'` before joining. -/
lemma homHeisenbergOp_arrowProduct (w : Matrix ι' ι (𝔸 E)) (w' : Matrix ι'' ι' (𝔸 E)) :
    homHeisenbergOp (fromRows (V.formAdjoint V' w) w') (arrowProduct f f') =
      arrowProduct (homHeisenbergOp w f) (homHeisenbergOp w' f') := by
  -- The action passes through the product and the flip; the second blocks agree at once. On the
  -- first block the flip takes the adjoint again, which undoes `formAdjoint`.
  simp [homHeisenbergOp, homAtPoint, sum, flipSpace_x, ← map_inv, ← smul_eq_mul_diagonal,
    Matrix.mul_assoc, fromBlocks_mul_fromRows, arrowProduct, rho_boxProd, ← CoordChange.map_rho,
    matrixToVec_fromRows_comp_inl, matrixToVec_fromRows_comp_inr, formAdjoint, map_J_inv, V'.map_J,
    ← mul_smul, flipCoords_apply, vecToMatrix_matrixToVec, -matrixToVec_smul]

private lemma finVec_comp {m k : Type*} (x : m → 𝔸f E) (e : k → m) :
    finVec x ∘ e = finVec (x ∘ e) :=
  rfl

/-- The finite Heisenberg operator of `y` on the joined datum acts on `f'` by the second block of
`y` and on `f` by `normNegOne` (the fixed unit u of Ô with ūu = −1) times the conjugate transpose of
the first block. The scalar is `stdLattice.semichar` of the first block, squared. -/
lemma finHeisenbergOp_arrowProduct (y : (ι ⊕ ι'') × ι' → 𝔸f E) :
    finHeisenbergOp (V'.hom (flipSum V V'')) y (arrowProduct f f') =
      stdLattice.semichar (fun q : ι' × ι ↦ y (Sum.inl q.2, q.1)) ^ 2 •
        arrowProduct
          (finHeisenbergOp (V.hom V')
            (fun q : ι' × ι ↦ ((normNegOne : (Ô E)ˣ) : 𝔸f E) * star (y (Sum.inl q.2, q.1))) f)
          (finHeisenbergOp (V'.hom V'') (fun q : ι'' × ι' ↦ y (Sum.inr q.1, q.2)) f') := by
  -- `stdLattice.semichar y` is an additive character at a multiple of the norm form `y* y`, the sum
  -- over the two blocks. The flip changes the sign of the first block; the square corrects it.
  have h_scalar :
      stdLattice.semichar y =
        (stdLattice.semichar fun q : ι' × ι ↦ y (Sum.inl q.2, q.1)) ^ 2 *
          ((stdLattice.semichar fun q : ι'' × ι' ↦ y (Sum.inr q.1, q.2)) *
            stdLattice.semichar fun q : ι' × ι ↦
              ((normNegOne : (Ô E)ˣ) : 𝔸f E) * star (y (Sum.inl q.2, q.1))) := by
    simp [stdLattice.semichar, dotProduct, sum_prod_type, sq, ← AddChar.map_add_eq_mul,
      mul_mul_mul_comm _ (y _), Finset.sum_comm (γ := ι)]
    -- Without -two_mul_half, grind rewrites 2 * half = 1 first and misses the ring identity.
    grind [-stdLattice.two_mul_half]
  -- The action passes through the product and the flip; it remains to compare the scalars.
  simp [finHeisenbergOp, arrowProduct, rho_boxProd, ← CoordChange.map_rho, ← mul_smul]
  rw [finVec_comp, CoordChange.apply_finVec, h_scalar]
  rfl -- The vectors agree by the definitions of `finEquiv` and `finVec`.

@[simp]
lemma arrowProduct_vacElem :
    arrowProduct (V.hom V').vacElem (V'.hom V'').vacElem = (V'.hom (flipSum V V'')).vacElem := by
  simp [arrowProduct]

/-- Acting on `f` by `(g, g')` and on `f'` by `(g', g'')` and then joining is the same as joining
and then acting by `New.Seesaw.tripleWeil` at `(g, g', g'')`. -/
lemma arrowProduct_twistedPairWeil (g' : G E ε') (g'' : G E ε'') :
    arrowProduct (twistedPairWeil (rankTwist a) (g, g') f)
        (twistedPairWeil (rankTwist b) (g', g'') f') =
      tripleWeil a b (g, g', g'') (arrowProduct f f') := by
  -- `flipCoords_map_omega` moves the first action through the flip; `omega_boxProd` joins the two
  -- Weil actions.
  simp [pairWeil, flipCoords_map_omega, arrowProduct, ← mul_smul, tripleWeil]
  rw [omega_boxProd (g₁ := .onHom (g', g.neg)) (g₂ := .onHom (g', g''))]
  · -- The scalars on the two sides are the same product of character values.
    module
  · -- The matrix of `(g', g.neg ⊕ g'')` on `Hom(V', V⁻ ⊕ V'')` is block diagonal.
    aesop

/-! ### The joining map on finite parts -/

/-- The point evaluations separate the finite part: a vector u of the finite part of the data on
Hom(V, V′) with θ(ϱ(x) u) = 0 for every point x is zero. -/
private lemma eq_zero_of_forall_theta_rho_eq_zero {u : (V.hom V').finitePart}
    (h : ∀ x : ι' × ι → 𝔸 E, (V.hom V').θ ((V.hom V').ϱ x u) = 0) : u = 0 :=
  -- `θ (ϱ x f)` is the value `f x` (`theta_rho`), and data are determined by their values.
  Subtype.ext ((V.hom V').data_ext fun x ↦ by simpa [theta_rho] using h x)

/-- The induced map `New.Seesaw.arrowTensor` on the tensor product of the finite parts is
injective. -/
lemma injective_arrowTensor :
    Function.Injective (arrowTensor (V := V) (V' := V') (V'' := V'')) := by
  -- The value of `arrowTensor t` at a point `(x, x')` is, up to the constant of
  -- `theta_arrowProduct`, the value at `x'` of `t` contracted with the evaluation at the flip of
  -- `x`; the point evaluations separate, so contract with each.
  refine LinearMap.ker_eq_bot.mp (ker_eq_bot'.mpr fun t ht ↦ ?_)
  obtain ⟨z, hz_ne, hz⟩ := theta_arrowProduct V V' V''
  refine tensor_eq_zero_of_separating
    (f := fun x ↦ ((V.hom V').θ ∘L (V.hom V').ϱ x).toLinearMap.domRestrict (V.hom V').finitePart)
    (fun h ↦ eq_zero_of_forall_theta_rho_eq_zero fun x ↦ h x) t fun x ↦ ?_
  -- Write the point `x` as the flip of a point `y`.
  obtain ⟨y, rfl⟩ := (flipCoords star_normNegOne_mul_self rfl (t := ε) (s := ε')).φ.surjective x
  ext x'
  replace ht : arrowTensor t ((y ⊕ᵥ x') ∘ Equiv.sumProdDistrib ι ι'' ι') = 0 := by simp [ht]
  obtain ⟨S, rfl⟩ := t.exists_finset
  rw [← theta_rho] at ht ⊢
  simp_all [Function.comp_def, ← Finset.mul_sum, arrowProduct, arrowTensor, rho_boxProd,
    ← CoordChange.map_rho]

lemma leftInverse_arrowTensor : arrowTensor.leftInverse (arrowTensor t) = t :=
  leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr injective_arrowTensor) t

/-- The range of `arrowTensor`, the linear map induced by `arrowProduct` from 𝒮_f(Hom(V,
V')) ⊗ 𝒮_f(Hom(V', V'')) to 𝒮(Hom(V', V⁻ ⊕ V'')), is exactly the finite part 𝒮_f of the target. Here
V⁻ ⊕ V'' = `flipSum V V''`, with V⁻ the opposite space of V. -/
lemma range_arrowTensor : arrowTensor.range = (V'.hom (flipSum V V'')).finitePart := by
  -- Both sides are spans. By `finHeisenbergOp_arrowProduct` each generator
  -- `finHeisenbergOp _ y vacElem` of `finitePart` is a nonzero multiple of `arrowProduct` of two
  -- generators; what is left is that every pair of generators arises from some `y`.
  simp [← map₂_eq_range_lift_comp_mapIncl, finitePart, map₂_span_span, ← arrowProduct_vacElem,
    finHeisenbergOp_arrowProduct, le_antisymm_iff, span_le, smul_mem, mem_span_of_mem,
    arrowTensor, Set.range_subset_iff]
  show ∀ (x : ι' × ι → 𝔸f E) (x' : ι'' × ι' → 𝔸f E),
    arrowProduct ((V.hom V').finHeisenbergOp x (V.hom V').vacElem)
        ((V'.hom V'').finHeisenbergOp x' (V'.hom V'').vacElem) ∈
      span ℂ (Set.range fun z : (ι ⊕ ι'') × ι' → 𝔸f E ↦
        (stdLattice.semichar fun q : ι' × ι ↦ z (Sum.inl q.2, q.1)) ^ 2 •
          arrowProduct
            ((V.hom V').finHeisenbergOp
              (fun q : ι' × ι ↦ ((normNegOne : (Ô E)ˣ) : 𝔸f E) * star (z (Sum.inl q.2, q.1)))
              (V.hom V').vacElem)
            ((V'.hom V'').finHeisenbergOp (fun q : ι'' × ι' ↦ z (Sum.inr q.1, q.2))
              (V'.hom V'').vacElem))
  intro x x'
  -- Conjugation followed by multiplication by the unit `normNegOne` is onto.
  obtain ⟨y, rfl⟩ :
      ∃ y : ι' × ι → 𝔸f E, (fun q ↦ ((normNegOne : (Ô E)ˣ) : 𝔸f E) * star (y q)) = x :=
    (starMulAut.toEquiv.trans
      (normNegOne.map (Ô E).subtype.toMonoidHom).mulLeft).surjective.comp_left x
  -- The witness has blocks `y` and `x'`; its generator is the given product times a nonzero scalar.
  let z₀ : (ι ⊕ ι'') × ι' → 𝔸f E := matrixToVec (flip y.curry ⊕ᵥ vecToMatrix x')
  exact (smul_mem_iff _ (by simp)).mp (subset_span ⟨z₀, rfl⟩)

/-- `New.Seesaw.arrowTensor` intertwines the normalised Weil representations
`New.Seesaw.liftWeilFin` of finite adelic points on the two factors with `New.Seesaw.tripleWeil`
at the same points, for characters `a` and `b`. -/
lemma arrowTensor_map_liftWeilFin (p : Gf E ι) (q : Gf E ι') (r : Gf E ι'') :
    arrowTensor (TensorProduct.map (liftWeilFin a (p, q)) (liftWeilFin b (q, r)) t) =
      tripleWeil a b ((1, p), (1, q), 1, r) (arrowTensor t) := by
  -- Both sides are linear in `t`; on pure tensors this is `arrowProduct_twistedPairWeil`.
  induction t with
  | tmul u u' => simp [arrowProduct_twistedPairWeil, arrowTensor, tripleWeil]
  | add u u' hu hu' => simp_all [arrowTensor]

/-- The theta functional of `tripleWeil a b (g, g', k) f` is unchanged when `g` is multiplied on the
left by a rational point `γ` of `U(V)` and `g'` by a rational point `δ` of `U(V')`. -/
lemma theta_tripleWeil_mul_mul_eq_of_mem_Gamma (f : 𝒮 (V'.hom (flipSum V V''))) {γ : G E ε}
    (hγ : γ ∈ V.Γ) {δ : G E ε'} (hδ : δ ∈ V'.Γ) (g : G E ε) (g' : G E ε') (k : G E ε'') :
    (V'.hom (flipSum V V'')).θ (tripleWeil a b (γ * g, δ * g', k) f) =
      (V'.hom (flipSum V V'')).θ (tripleWeil a b (g, g', k) f) := by
  -- Automorphy of the theta kernel of `V'` and `flipSum V V''` with trivial characters.
  have hγ_sum : G.sum (γ.neg, 1) ∈ (flipSum V V'').Γ :=
    (sum_mem_Gamma _ _).mpr ⟨by simpa [mem_Gamma_iff_ratCoordMatrix] using hγ, one_mem _⟩
  have h_aut : pairTheta V' (flipSum V V'') 1 1 f (δ * g', .sum (γ.neg, 1) * .sum (g.neg, k)) =
      pairTheta V' (flipSum V V'') 1 1 f (g', .sum (g.neg, k)) :=
    (pairThetaKer V' (flipSum V V'') 1 1).rat_mul hδ hγ_sum g' _ f
  -- The characters in `tripleWeil` are trivial on the determinants of rational points.
  obtain ⟨γ, rfl⟩ := hγ
  obtain ⟨δ, rfl⟩ := hδ
  simpa [pairTheta, pairWeil, ← G.sum.map_mul, tripleWeil] using h_aut

/-- The function `F x = θ (tripleWeil a b x f)` of a triple of adelic points is unchanged when the
first point is multiplied on the left by a rational point `γ` of `U(V)` and the second by a rational
point `δ` of `U(V')`. -/
lemma theta_tripleWeil_rat_mul (f : 𝒮 (V'.hom (flipSum V V''))) :
    let F (x : G E ε × G E ε' × G E ε'') := (V'.hom (flipSum V V'')).θ (tripleWeil a b x f)
    ∀ γ ∈ V.Γ, ∀ δ ∈ V'.Γ, ∀ (g : G E ε) (g' : G E ε') (k : G E ε''),
      F (γ * g, δ * g', k) = F (g, g', k) :=
  fun _ hγ _ hδ g g' k ↦ theta_tripleWeil_mul_mul_eq_of_mem_Gamma a b f hγ hδ g g' k

end New.Seesaw

end
