import New.Determinant.AuxiliaryForms.PathData
import New.Determinant.Exchange.RemovingPlanes

/-!
# Theta lifts as a triangle of arrows: spaces, lifts, descents and the first lift

This file arranges the theta lifts between the hermitian spaces `D.gridSpace i z 0 n` in a triangle
of positions `(i, n)`. The flag `z` selects one of two chains of spaces; see
`New.Determinant.Chain.ChainNorms`. The lift and the transposed lift of forms along an edge
(`New.Exchange.IsEdgeFamily`) with a finite datum modulo a modulus are `New.Exchange.modLift` and
`New.Exchange.modTransposedLift`, and this file writes them as integrals and treats the opposite
space. It defines the spaces and lifts of the triangle, and it proves, for `i < m`, the injectivity
and the norm of the first lift of row `i` on the subspace of fixed level. It also defines the left
and reversed pairs, the descents `New.Data.triangleTransposedLift` from `(i, n + 1)` to `(i + 1, n)`
along a left pair, and the ascents `New.Data.triangleReversedLift` from `(i + 1, n)` to `(i, n + 1)`
along the reversed pair.

## Main definitions and results

* `New.Data.TriangleForm`, `New.Data.triangleLift`, `New.Data.triangleNegEquiv`,
  `New.Data.triangleBase`, `New.Data.triangleEmbedding`: the forms at `(i, n)`, the lift to
  `(i, n + 1)`, the copies at `(i, 0)` of the forms at `(0, 0)`, the subspace of fixed level, and
  its embedding at `(i, 0)`.
* `New.Data.triangleFirstLift`, `New.Data.exists_hasSum_inner_triangleFirstLift`: the first lift of
  a row, read on forms at `(0, 0)`; for `i < m`, its injectivity and norm on the subspace of fixed
  level, by Rallis' formula `New.SiegelWeil.rallis_inner_product_cosetTerm`.

Notions from other files:
* `New.Data.gridSpace`: The hermitian space at the node (i, j) of grid z with offset o, for the
  signs `New.Data.gridSigns`.
* `New.Data.chosenLevel`: The level J_M consists of the elements of K₀ = `New.stdLevel` that are 1
  modulo the chosen places `New.Data.chosenPlace`.
* `New.Data.triangleModulus`, `New.Data.triangleGLCard`: the modulus 𝔪 of the triangle, and the
  order of the general linear group of a node modulo 𝔪. A lift times this order is the lift for the
  measure that gives the principal level of 𝔪 the volume 1.

## Relation to the literature

See `New.Determinant.Chain.ChainNorms` for related work.
-/

noncomputable section

section TriangleArrows

open MeasureTheory Matrix Complex ComplexConjugate Fintype LinearMap

namespace New

open Rows Exchange WeilData Space Modulus SiegelWeil ComplexInnerProductSpace

variable {E N N' : Type} [Field E] [CMType E] [WeilData E] [Fintype N] [DecidableEq N] [Fintype N']
  [DecidableEq N'] {s : N → ℤˣ} {s' : N' → ℤˣ} (S : Space E N s) (T : Space E N' s') {I : Type*}

/-! ### The opposite space; lifts and transposed lifts as integrals -/

/-- An integral over the automorphic quotient of the opposite space `S.neg` is the integral over
that of `S`, after pull-back along the identification `G.neg` of the two unitary groups. -/
lemma integral_neg_quotMeasure (F : G E (-s) → ℂ) :
    ∫ g : G E (-s), F g ∂S.neg.quotMeasure = ∫ g : G E s, F (G.neg g) ∂S.quotMeasure :=
  (isForm_neg_iff_and_integral_neg S S.neg (neg_mem_neg_Gamma_iff S)).right F

/-- The linear isometry from forms of parameter `l` on `S` to forms of parameter `l` on the opposite
space `S.neg`, by the identification `G.neg` of the two unitary groups. -/
def formNegEquiv (l : NumberField.InfinitePlace E → N → ℤ) :
    S.Form (typeKernel l s) ≃ₗᵢ[ℂ] S.neg.Form (typeKernel l (-s)) :=
  -- the inverse map is the pull-back of functions along `G.neg`
  LinearIsometryEquiv.symm <| LinearEquiv.isometryOfInner
    -- a function is a form on `S.neg` if and only if its pull-back is a form on `S`
    (LinearEquiv.ofEq _ _ (Submodule.ext fun F ↦ by
        exact ((isForm_neg_iff_and_integral_neg S S.neg (neg_mem_neg_Gamma_iff S)).left l F).symm)
          ≪≫ₗ
      LinearEquiv.ofSubmodule' (LinearEquiv.funCongrLeft ℂ ℂ G.neg.toEquiv) _)
    -- the integrals defining the two inner products agree under the pull-back
    fun F F' : S.neg.Form (typeKernel l (-s)) ↦
      (integral_neg_quotMeasure S fun g : G E (-s) ↦ conj (F.val g) * F'.val g).symm

lemma formNegEquiv_apply_neg (l : NumberField.InfinitePlace E → N → ℤ)
    (y : S.Form (typeKernel l s)) (g : G E s) :
    (formNegEquiv S l y).val (G.neg g) = y.val g := by
  have h_symm (F : S.neg.Form (typeKernel l (-s))) :
      ((formNegEquiv S l).symm F).val g = F.val (G.neg g) := rfl
  rw [← h_symm, LinearIsometryEquiv.symm_apply_apply]

/-- The isometry `formNegEquiv` commutes with right translation by the finite adelic group. -/
lemma formNegEquiv_formRep (l : NumberField.InfinitePlace E → N → ℤ) (k : Gf E N)
    (y : S.Form (typeKernel l s)) :
    formNegEquiv S l (S.formRep (typeKernel l s) k y) =
      S.neg.formRep (typeKernel l (-s)) k (formNegEquiv S l y) :=
  rfl

/-- The transposed lift `modTransposedLift S T α Φ Ψ e' e y` is linear in `Ψ`: it is the sum over
matrices `x` of `Ψ x` times the transposed lift for the indicator function `Pi.single x 1` of
`x`. -/
lemma Exchange.modTransposedLift_eq_sum (α : ∀ (M : Type) [Fintype M], AutChar E) {𝔪 : Modulus E}
    (Φ : MvPolynomial (NumberField.InfinitePlace E × N' × N) ℂ) (Ψ : Matrix N' N 𝔪.ResidueRing → ℂ)
    (e' : GInf E s' → ℂ) (e : GInf E s → ℂ) (y : T.Form e') :
    modTransposedLift S T α Φ Ψ e' e y =
      ∑ x : Matrix N' N 𝔪.ResidueRing, Ψ x • modTransposedLift S T α Φ (Pi.single x 1) e' e y := by
  rw [modTransposedLift, modDatum_eq_sum]
  simp

/-- The theta lift of a function `y`, with finite datum `Ψ` modulo `𝔪` and polynomial `Φ` at
infinity, is the integral of `y` against the theta kernel `modKernel`. -/
lemma Exchange.lift_modDatum_apply (α β : AutChar E) {𝔪 : Modulus E}
    (Φ : MvPolynomial (NumberField.InfinitePlace E × N' × N) ℂ) (Ψ : Matrix N' N 𝔪.ResidueRing → ℂ)
    (y : G E s → ℂ) (h : G E s') :
    Space.lift (pairThetaKer S T α β)
        (modDatum S T 𝔪 Ψ (Fock.polyVector (realSigns E (homSigns s s')) Φ)) y h =
      ∫ g : G E s, modKernel S T α β 𝔪 Ψ Φ g h * y g ∂S.quotMeasure :=
  rfl

/-- Let `Φ` make an edge (`IsEdgeFamily`) with types `k` on `S`, `k'` on `T` and flag `d`. The
transposed lift to `S` of a form `x` on `T` of the conjugate type `k' !d` is the integral of `x`
over the quotient of `T` against the theta kernel `modKernel`. -/
lemma Exchange.IsEdgeFamily.modTransposedLift_apply {α : I → ∀ (M : Type) [Fintype M], AutChar E}
    {k : Bool → GInf E s → ℂ} {k' : Bool → GInf E s' → ℂ} {d : Bool}
    {Φ : MvPolynomial (NumberField.InfinitePlace E × N' × N) ℂ} (h_edge : IsEdgeFamily α k k' d Φ)
    (j : I) {𝔪 : Modulus E} (Ψ : Matrix N' N 𝔪.ResidueRing → ℂ) (x : T.Form (k' !d)) (g : G E s) :
    (modTransposedLift S T (α j) Φ Ψ (k' !d) (k !d) x).val g =
      ∫ h : G E s', modKernel S T (α j N) (α j N') 𝔪 Ψ Φ g h * x.val h ∂T.quotMeasure :=
  congrFun ((h_edge.isArrow_swap S T Ψ j).coe_formLift x) g

/-- Let the polynomial `Φ` make an edge (`IsEdgeFamily`) for the characters `α j`, `j : I`, and the
pairs `k`, `k'` of conjugate cuspidal types: its Fock vector matches the types `k d` and `k' d` in
the real Weil representation. Fix `j`, a function `Ψ` on matrices modulo `𝔪`, a finite adelic point
`u` of the group of `T` and a form `x` on `T` of type `k' !d`. The transposed lift to `S` of the
right translate (`formRep`) of `x` by `u⁻¹` is the integral of `x` over the automorphic quotient of
`T` against the right translate by `u` of `modKernel`, the theta kernel with characters `α j N`,
`α j N'` of the Schwartz function that is `Φ` at infinity, `Ψ` at `𝔪` and the vacuum elsewhere. -/
lemma Exchange.IsEdgeFamily.modTransposedLift_formRep_inv_apply
    {α : I → ∀ (M : Type) [Fintype M], AutChar E}
    {k : Bool → GInf E s → ℂ} {k' : Bool → GInf E s' → ℂ} {d : Bool}
    {Φ : MvPolynomial (NumberField.InfinitePlace E × N' × N) ℂ} (h_edge : IsEdgeFamily α k k' d Φ)
    (j : I) {𝔪 : Modulus E} (Ψ : Matrix N' N 𝔪.ResidueRing → ℂ) (u : Gf E N') (x : T.Form (k' !d))
    (g : G E s) :
    (modTransposedLift S T (α j) Φ Ψ (k' !d) (k !d) (T.formRep (k' !d) u⁻¹ x)).val g =
      ∫ h : G E s', modKernel S T (α j N) (α j N') 𝔪 Ψ Φ g (h * (1, u)) * x.val h
        ∂T.quotMeasure := by
  rw [(h_edge.isArrow_swap S T Ψ j).coe_formLift,
    show (T.formRep (k' !d) u⁻¹ x).val = fun h ↦ x.val (h * (1, u)⁻¹) from
      funext fun h ↦ by simp [formRep_apply],
    ← ThetaKernel.lift_omega_left _ x.prop.toIsAutomorphic (1, u)]
  simp [Space.lift, modKernel, pairTheta, rep_apply_apply]

/-- The pair of central elements `𝔪.flipScalar` of the unitary groups of `S` and `T` acts on a datum
`φ`, in the Weil representation `pairWeil`, by the value of the character `pairChar`. -/
lemma pairWeil_flipScalar (α β : AutChar E) (𝔪 : Modulus E) (φ : 𝒮 (S.hom T)) :
    pairWeil S T α β ((1, 𝔪.flipScalar N), 1, 𝔪.flipScalar N') φ =
      pairChar (s := s) (s' := s') α β ((1, 𝔪.flipScalar N), 1, 𝔪.flipScalar N') • φ := by
  rw [pairWeil_apply, Modulus.flipScalar, Modulus.flipScalar, G.onHom_scalarFin]
  simp [Prod.mk_one_one]

/-- The character `(α M)⁻¹ υⁿ` on a space with index type `M` of cardinality `n`, where
`υ = upsilonU1` is the splitting character of the Weil data, restricted to the norm-one ideles. The
conjugate of a theta kernel with characters `α` is a multiple of a kernel from the opposite space
with these characters (`New.exists_conj_modKernel_eq_mul_modKernel_neg`). -/
abbrev oppositeChar (α : ∀ (M : Type) [Fintype M], AutChar E) (M : Type) [Fintype M] : AutChar E :=
  (α M)⁻¹ * upsilonU1 ^ card M

/-- Let `Φ` make an edge from `S` to `T` with characters `a j`, `j : I`, and flag `false`, and `Φ'`
an edge from the opposite space `S.neg` to `T` with the characters `oppositeChar (a j)` and flag
`true`. The pair on `S` and `S.neg` is `kernelPair l`, the discrete series kernels `typeKernel` of
the parameters `l` (at `false`) and `-l` (at `true`); the pair on `T` is `k'`. For every function
`Ψ` on matrices modulo `𝔪` there is a `Ψ'` such that the transposed theta lift `modTransposedLift`
from `T` to `S.neg` with `Φ'`, `Ψ'` is the adjoint of the theta lift `modLift` from `S` to `T` with
`Φ`, `Ψ`, once forms on `S` and on `S.neg` are identified by `formNegEquiv`. -/
theorem Exchange.IsEdgeFamily.exists_inner_modLift_eq_inner_modTransposedLift
    {l : NumberField.InfinitePlace E → N → ℤ} {a : I → ∀ (M : Type) [Fintype M], AutChar E}
    {k' : Bool → GInf E s' → ℂ} {Φ Φ' : MvPolynomial (NumberField.InfinitePlace E × N' × N) ℂ}
    (h_edge : IsEdgeFamily a (kernelPair l s) k' false Φ)
    (h_neg_edge : IsEdgeFamily (fun j : I ↦ oppositeChar (a j)) (kernelPair l (-s)) k' true Φ')
    (j : I) {𝔪 : Modulus E} (Ψ : Matrix N' N 𝔪.ResidueRing → ℂ) :
    ∃ Ψ' : Matrix N' N 𝔪.ResidueRing → ℂ, ∀ (y : S.Form (typeKernel l s)) (x : T.Form (k' false)),
      ⟪x, modLift S T (a j) Φ Ψ (typeKernel l s) (k' false) y⟫ =
        ⟪modTransposedLift S.neg T (oppositeChar (a j)) Φ' Ψ' (k' false) (typeKernel l (-s)) x,
          formNegEquiv S l y⟫ := by
  -- Negating `S` conjugates the theta kernel up to a factor `c`, at the price of replacing `Ψ` by
  -- `Ψ₀` and `Φ` by its conjugate; that polynomial is traded for `Φ'` and a factor `κ`.
  let b : ∀ (M : Type) [Fintype M], AutChar E := oppositeChar (a j)
  obtain ⟨c, -, h_neg⟩ := exists_conj_modKernel_eq_mul_modKernel_neg S T
  obtain ⟨κ, hκ⟩ := h_neg_edge.petersson_lift_eq_mul_inner_modTransposedLift (Φ.map conj)
  let Ψ₀ (x : Matrix N' N 𝔪.ResidueRing) : ℂ := conj (Ψ (𝔪.normNegOne⁻¹ • x))
  refine ⟨c • conj κ • Ψ₀, fun y x ↦ ?_⟩
  let y' : S.neg.Form (typeKernel l (-s)) := formNegEquiv S l y
  -- `L` is the lift of the conjugate of `y'` from `S.neg`, with `Ψ₀` and the conjugate of `Φ`
  let L : G E s' → ℂ := Space.lift (pairThetaKer S.neg T (b N) (b N'))
    (modDatum S.neg T 𝔪 Ψ₀ (Fock.polyVector (realSigns E (homSigns (-s) s')) (Φ.map conj)))
    (star y'.val)
  have h_conj (g : G E s') :
      conj ((modLift S T (a j) Φ Ψ (typeKernel l s) (k' false) y).val g) = c * L g := by
    have h_kernel : (modLift S T (a j) Φ Ψ (typeKernel l s) (k' false) y).val g =
        ∫ g' : G E s, modKernel S T (a j N) (a j N') 𝔪 Ψ Φ g' g * y.val g' ∂S.quotMeasure :=
      congrFun ((h_edge.isArrow_lift S T Ψ j).coe_formLift y) g
    rw [h_kernel]
    simp [L, b, Ψ₀, y', lift_modDatum_apply, integral_neg_quotMeasure, formNegEquiv_apply_neg,
      ← integral_conj, h_neg, mul_assoc, integral_const_mul]
  have h_trade : T.petersson x.val (star L) =
      κ * ⟪modTransposedLift S.neg T b Φ' Ψ₀ (k' false) (typeKernel l (-s)) x, y'⟫ :=
    hκ j S.neg T 𝔪 Ψ₀ y' x
  calc ⟪x, modLift S T (a j) Φ Ψ (typeKernel l s) (k' false) y⟫
      = conj c * T.petersson x.val (star L) := by
        rw [← inner_conj_symm, ← conj_petersson, ← map_mul]
        simp [inner_eq_petersson, petersson, h_conj, mul_assoc, integral_const_mul]
    _ = ⟪(c * conj κ) • modTransposedLift S.neg T b Φ' Ψ₀ (k' false) (typeKernel l (-s)) x,
      y'⟫ := by
        rw [h_trade, inner_smul_left, map_mul, conj_conj, mul_assoc]
    _ = _ := by simp [b, y', modTransposedLift, modDatum, Pi.smul_comp, smul_smul]

namespace Data

section Nodes

variable {P : Parameters} (D : Data P) (z : Bool) (ϑ : D.MFoldTwist) (i n : ℕ)

/-! ### The spaces and lifts of the triangle -/

/-- The space of forms on the hermitian space `D.gridSpace i z 0 n` at position `(i, n)` of the
triangle. Their type at infinity is `typeKernel`, the product over the infinite places of the
discrete series kernels, for `D.gridParam z i 0 n`, which is twice the discrete series parameter. -/
abbrev TriangleForm : Type :=
  (D.gridSpace i z 0 n).Form (typeKernel (D.gridParam z i 0 n) (D.gridSigns z i 0 n))

/-- The action of the finite adelic unitary group by right translation on the forms at position
`(i, n)` of the triangle. -/
abbrev triangleRep : Representation ℂ (Gf D.E (D.GridIndex z 0 n)) (D.TriangleForm z i n) :=
  formRep (D.gridSpace i z 0 n) (typeKernel (D.gridParam z i 0 n) (D.gridSigns z i 0 n))

/-- The theta lift from the forms at position `(i, n)` of the triangle to those at `(i, n + 1)`,
for the twist `ϑ`. It adds the block `n + i + 1`. Its character `gridChar ϑ (!z) (n + i)` is the
character `liftChar` of index `n + i + 1`, twisted by `ϑ ^ (n + i + 1)` if `z` is false, times a
power of `upsilonU1`. Its polynomial at infinity `gridHarmonic` is the joint harmonic for the
weights of this character and the parameters of the two nodes, not negated (flag `false`). Its
finite datum is the point datum `New.Exchange.pointDatum` modulo `New.Data.triangleModulus`. -/
def triangleLift : D.TriangleForm z i n →ₗ[ℂ] D.TriangleForm z i (n + 1) :=
  modLift (D.gridSpace i z 0 n) (D.gridSpace i z 0 (n + 1)) (D.gridChar ϑ (!z) (n + i))
    (D.gridHarmonic i false (!z) (n + i) z 0 n 0 (n + 1))
    (pointDatum (triangleModulus z ϑ).ResidueRing)
    (typeKernel (D.gridParam z i 0 n) (D.gridSigns z i 0 n))
    (typeKernel (D.gridParam z i 0 (n + 1)) (D.gridSigns z i 0 (n + 1)))

/-- For each `i`, the linear isometric isomorphism from forms at `(0, 0)` to forms at `(i, 0)`,
composed of `i` passages `New.formNegEquiv` to the opposite hermitian space. -/
def triangleNegEquiv : ∀ i : ℕ, D.TriangleForm z 0 0 ≃ₗᵢ[ℂ] D.TriangleForm z i 0
  | 0 => LinearIsometryEquiv.refl ℂ (D.TriangleForm z 0 0)
  -- each row is the opposite space of the row before it
  | i + 1 => (triangleNegEquiv i).trans (formNegEquiv (D.gridSpace i z 0 0) (D.gridParam z i 0 0))

/-- The isometry to row `i + 1` is the one to row `i` followed by passage to the opposite space. -/
lemma triangleNegEquiv_succ_apply (y : D.TriangleForm z 0 0) :
    D.triangleNegEquiv z (i + 1) y =
      formNegEquiv (D.gridSpace i z 0 0) (D.gridParam z i 0 0) (D.triangleNegEquiv z i y) :=
  rfl

/-- The level at the base corner of the triangle: the level `D.chosenLevel` on Y₀ if `z` is false;
if `z` is true, the principal level of `D.gridLevelGen`, the power `ϖ ^ D.natB` of the generator `ϖ`
of the product of the chosen places. -/
abbrev triangleBaseLevel : ∀ z : Bool, Subgroup (Gf D.E (D.GridIndex z 0 0))
  | false => D.chosenLevel
  | true => principalLevel (D.GridIndex true 0 0) D.gridLevelGen

/-- The space of forms at the base corner of the triangle that are fixed by the level
`New.Data.triangleBaseLevel`. -/
def triangleBase : Submodule ℂ (D.TriangleForm z 0 0) :=
  levelSpace (D.triangleRep z 0 0) (D.triangleBaseLevel z)

lemma mem_triangleBase_iff (v : D.TriangleForm z 0 0) :
    v ∈ D.triangleBase z ↔ ∀ u ∈ D.triangleBaseLevel z, D.triangleRep z 0 0 u v = v := by
  change (∀ u : D.triangleBaseLevel z, D.triangleRep z 0 0 u.val v = (1 : ℂ) • v) ↔ _
  simp

/-- The isometric embedding of `New.Data.triangleBase` in the forms at `(i, 0)`, through
`New.Data.triangleNegEquiv`. -/
abbrev triangleEmbedding : D.triangleBase z →ₗᵢ[ℂ] D.TriangleForm z i 0 :=
  (D.triangleNegEquiv z i).toLinearIsometry.comp (D.triangleBase z).subtypeₗᵢ

/-- The isometries `New.Data.triangleNegEquiv` commute with right translation by the finite adelic
group. -/
theorem triangleNegEquiv_triangleRep (k : Gf D.E (D.GridIndex z 0 0)) (y : D.TriangleForm z 0 0)
    (i : ℕ) :
    D.triangleNegEquiv z i (D.triangleRep z 0 0 k y) = D.triangleRep z i 0 k
      (D.triangleNegEquiv z i y) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [triangleNegEquiv_succ_apply, triangleNegEquiv_succ_apply, ih]
    exact formNegEquiv_formRep (D.gridSpace i z 0 0) (D.gridParam z i 0 0) k
      (D.triangleNegEquiv z i y)

/-! ### The first lift -/

lemma triangleBaseLevel_le_stdLevel : D.triangleBaseLevel z ≤ stdLevel D.E (D.GridIndex z 0 0) := by
  cases z
  · exact levelOf_le_stdLevel
  · exact principalLevel_le_stdLevel

/-- For a form `y` of `New.Data.triangleBase`, its image `D.triangleNegEquiv z i y` in row `i` is
fixed by `D.triangleRep z i 0 u` for every `u` in `New.Data.triangleBaseLevel`. -/
lemma triangleRep_triangleNegEquiv_of_mem_triangleBaseLevel (y : D.triangleBase z)
    {u : Gf D.E (D.GridIndex z 0 0)} (hu : u ∈ D.triangleBaseLevel z) :
    D.triangleRep z i 0 u (D.triangleNegEquiv z i y) = D.triangleNegEquiv z i y := by
  rw [← triangleNegEquiv_triangleRep, (D.mem_triangleBase_iff z y).mp y.prop u hu]

/-- The principal level of the modulus of the triangle is contained in the base level. -/
lemma levelOfSubgroup_bot_le_triangleBaseLevel :
    (triangleModulus z ϑ).levelOfSubgroup ⊥ ≤ D.triangleBaseLevel z := by
  rintro _ ⟨u, hu_one : (triangleModulus z ϑ).reductionGL u = 1, rfl⟩
  cases z
  · exact D.levelY_le_chosenLevel ϑ 0 ⟨u, (LevelPlaces.ker_reductionGL_eq _).le hu_one, rfl⟩
  · exact (mem_principalLevel_iff gridModulus_one_ideal _).mpr hu_one

/-- The copy in row `i` of a form of `New.Data.triangleBase` is fixed by the principal level of the
modulus `New.Data.triangleModulus z ϑ`. -/
lemma hasLevel_triangleNegEquiv (y : D.triangleBase z) :
    HasLevel (D.triangleNegEquiv z i y).val ((triangleModulus z ϑ).levelOfSubgroup ⊥) :=
  fun _ hu ↦ congrFun <| congrArg Subtype.val <|
    D.triangleRep_triangleNegEquiv_of_mem_triangleBaseLevel z i y
    (D.levelOfSubgroup_bot_le_triangleBaseLevel z ϑ hu)

end Nodes

/-- Let `i < D.m`, the number of lifts of the data `D`, and let `triangleLift z ϑ i 0` be the theta
lift, for the twist `ϑ`, from forms at the node `(i, 0)` of the triangle `z` to forms at `(i, 1)`.
For an integral point `u` (`stdLevel`) of the finite adelic unitary group at `(i, 0)` there is a
finite adelic point `g` at `(i, 1)` such that the lift intertwines the right translations
`triangleRep` by `u` and `g` up to a scalar `c` of absolute value `1`. -/
lemma exists_triangleRep_triangleLift_eq_smul {P : Parameters} (D : Data P) (z : Bool)
    (ϑ : D.MFoldTwist) (i : ℕ) (hi : i < D.m) (u : stdLevel D.E (D.GridIndex z 0 0)) :
    ∃ (g : Gf D.E (D.GridIndex z 0 (0 + 1))) (c : ℂ), ‖c‖ = 1 ∧ ∀ f : D.TriangleForm z i 0,
      D.triangleRep z i (0 + 1) g (D.triangleLift z ϑ i 0 f) =
        c • D.triangleLift z ϑ i 0 (D.triangleRep z i 0 u.val f) := by
  -- Choose `g` integral with reduction `u ⊕ 1`. The pair `(u, g)` fixes the inclusion matrix `x₀`,
  -- the support of `pointDatum`, so it acts on the datum through the character `pairChar`.
  let 𝔪 : Modulus D.E := triangleModulus z ϑ
  let B : Type := Fin (D.t - z.toNat)
  obtain ⟨g, hg⟩ : ∃ g : stdLevel D.E (D.GridIndex z 0 0 ⊕ B),
      𝔪.reductionGL g = blockGL (𝔪.reductionGL u, (1 : GL B 𝔪.ResidueRing)) :=
    reductionGL_surjective _
  let x₀ : Matrix (D.GridIndex z 0 0 ⊕ B) (D.GridIndex z 0 0) 𝔪.ResidueRing := inclMatrix _ .inl
  have h_fix : x₀ = (𝔪.reductionGL g)⁻¹.val * x₀ * (𝔪.reductionGL u).val := by
    rw [hg, ← map_inv]
    simp [x₀, inclMatrix_inl, fromBlocks_mul_fromRows]
  -- the data of the lift form an edge, because the parameters at its two ends correspond
  have h_edge := isEdgeFamily_of_paramsCorrespond (fun ϑ : D.MFoldTwist ↦ D.gridChar ϑ (!z) (0 + i))
    false (fun ϑ ↦ gridChar_hasWeight ϑ (!z) (0 + i) _)
    (fun ϑ ↦ gridChar_hasWeight ϑ (!z) (0 + i) _)
    (D.paramsCorrespond_grid_succ_right z i 0 0 D.m.zero_le (by omega) (.inr rfl))
  exact ⟨g.val, pairChar _ _ _, Circle.norm_coe _, (h_edge.isArrow_lift _ _ (pointDatum _)
    ϑ).formRep_formLift_of_eq_smul (pairWeil_modDatum_single u g h_fix)⟩

/-- Let `F` be the finite datum of the theta lift from the hermitian space `gridSpace` at the node
`(i, 0)` of the triangle `z` to that at `(i, 1)`: the indicator function `pointDatum` of the
inclusion matrix modulo `𝔪 = triangleModulus z ϑ`, and the vacuum off `𝔪` (`vacuumDatum`). For the
character `gridChar` of the lift on the target, `F` is sharp for the principal level
`J = 𝔪.levelOfSubgroup ⊥`: at the places of `𝔪` its matrix coefficient is `⟨F, F⟩` times the
indicator function of `J`. Its mass `⟨F, F⟩ / [K₀ : J]`, with `K₀ = stdLevel` the integral points,
is the inverse of the number of matrices of this size modulo `𝔪`, divided by `triangleGLCard z ϑ 0`,
the order of the general linear group of the source modulo `𝔪`. -/
lemma isSharp_pointDatum {P : Parameters} (D : Data P) (z : Bool) (ϑ : D.MFoldTwist) (i : ℕ) :
    IsSharp (D.gridChar ϑ (!z) (0 + i) (D.GridIndex z 0 (0 + 1)))
      (triangleModulus z ϑ).places.conjClosure
      (vacuumDatum (D.gridSpace i z 0 0) (D.gridSpace i z 0 (0 + 1)) (triangleModulus z ϑ)
        (pointDatum (triangleModulus z ϑ).ResidueRing)).val
      ((triangleModulus z ϑ).levelOfSubgroup ⊥)
      (1 / card (D.GridIndex z 0 (0 + 1) × D.GridIndex z 0 0 → (triangleModulus z ϑ).ResidueRing) /
        triangleGLCard z ϑ 0) := by
  let 𝔪 : Modulus D.E := triangleModulus z ϑ
  let M : Type := Matrix (D.GridIndex z 0 0 ⊕ Fin (D.t - z.toNat)) (D.GridIndex z 0 0) 𝔪.ResidueRing
  let x₀ : M := inclMatrix _ .inl
  let F : M → ℂ := Pi.single x₀ 1
  -- on the support of the datum, the transpose of the inclusion is a left inverse
  have h_left_inv (x : M) (hx : F x ≠ 0) : x₀ᵀ * x = 1 := by
    obtain rfl : x = x₀ := by simpa [F, Pi.single_apply] using hx
    exact inclMatrix_transpose_mul_self .inl
  have h_norm : star F ⬝ᵥ F = 1 := by simp [F]
  rw [← h_norm]
  refine isSharp_vacuumDatum_of_mul_eq_one (D.gridSpace i z 0 (0 + 1)) _
    (.inr nonempty_modulus_places) x₀ᵀ
    h_left_inv (fun w hw ↦ ?_) (h_norm.trans_ne one_ne_zero)
  -- the character has trivial tame part off the modulus
  cases z <;> exact (descentPair ..).tame_eq_one w fun hw' ↦ hw (places_levelModulus.ge hw')

/-- The first lift of row `i`, read on forms at the base corner: the copy of `y` at `(i, 0)`
(`New.Data.triangleNegEquiv`) is lifted to `(i, 1)`. -/
abbrev triangleFirstLift {P : Parameters} (D : Data P) (z : Bool) (ϑ : D.MFoldTwist) (i : ℕ)
    (y : D.TriangleForm z 0 0) : D.TriangleForm z i (0 + 1) :=
  D.triangleLift z ϑ i 0 (D.triangleNegEquiv z i y)

/-- The cosets, in the finite adelic group at the base corner, of the points that are integral off
the places of `New.Data.triangleModulus z ϑ` and their conjugates. -/
abbrev TriangleCoset {P : Parameters} (D : Data P) (z : Bool) (ϑ : D.MFoldTwist) : Type :=
  Gf D.E (D.GridIndex z 0 0) ⧸
    localLevel (D.GridIndex z 0 0) (triangleModulus z ϑ).places.conjClosureᶜ

/-- The term at the coset `γ` of the series for the inner product of two first lifts of row `i`.
It is `New.SiegelWeil.cosetTerm M b`, the number `⟪x, g y⟫` times `vacuumCoeff M b g` at the
representative `g` of `γ`, for the rank `M` and the character `b` of the target of the lift, divided
by the number of maps from `GridIndex z 0 1 × GridIndex z 0 0` to the residue ring of the
modulus. -/
abbrev triangleRallisTerm {P : Parameters} (D : Data P) (z : Bool) (ϑ : D.MFoldTwist) (i : ℕ)
    (x y : D.TriangleForm z 0 0) (γ : D.TriangleCoset z ϑ) : ℂ :=
  cosetTerm (card (D.GridIndex z 0 1)) (D.gridChar ϑ (!z) i (D.GridIndex z 0 1))
      (triangleModulus z ϑ).places.conjClosureᶜ x y γ /
    card (D.GridIndex z 0 1 × D.GridIndex z 0 0 → (triangleModulus z ϑ).ResidueRing)

/-- For either grid `z`, the index set `D.GridIndex z 0 1` of the node `(0, 1)` has more than twice
as many elements as the index set of the node `(0, 0)`, so Rallis' formula applies to the first lift
of each row. -/
lemma two_mul_card_gridIndex_zero_lt {P : Parameters} (D : Data P) (z : Bool) :
    2 * card (D.GridIndex z 0 0) < card (D.GridIndex z 0 1) := by
  rw [card_gridIndex, card_gridIndex]
  grind [Bool.toNat_le]

/-- Let `i < D.m`, the number of lifts of the data `D`. Let `a = triangleFirstLift z ϑ i` copy a
form from the corner `(0, 0)` of the triangle `z` to `(i, 0)` and lift it to `(i, 1)`, and let `y`
lie in `triangleBase`, the forms at the corner fixed by `triangleBaseLevel`. A form `v` at the
corner with `⟪v, x⟫ = ⟪a y, a x⟫` for all `x` lies in `triangleBase`. -/
lemma mem_triangleBase_of_inner_eq_inner_triangleFirstLift {P : Parameters} (D : Data P) (z : Bool)
    (ϑ : D.MFoldTwist) (i : ℕ) (hi : i < D.m) (y : D.triangleBase z) {v : D.TriangleForm z 0 0}
    (hv : ∀ x : D.TriangleForm z 0 0, ⟪v, x⟫ = ⟪D.triangleFirstLift z ϑ i y,
      D.triangleFirstLift z ϑ i x⟫) :
    v ∈ D.triangleBase z := by
  -- Test `u v = v` against all translates `u x`, and move `u` across the lift.
  refine (D.mem_triangleBase_iff z v).mpr fun u hu ↦ ?_
  obtain ⟨g, c, hc, h_law⟩ :=
    D.exists_triangleRep_triangleLift_eq_smul z ϑ i hi ⟨u, D.triangleBaseLevel_le_stdLevel z hu⟩
  let a : D.TriangleForm z 0 0 → D.TriangleForm z i (0 + 1) := D.triangleFirstLift z ϑ i
  let π : Representation ℂ (Gf D.E (D.GridIndex z 0 0)) (D.TriangleForm z 0 0) :=
    D.triangleRep z 0 0
  have h_move (x : D.TriangleForm z 0 0) : D.triangleRep z i (0 + 1) g (a x) = c • a (π u x) := by
    rw [h_law, ← triangleNegEquiv_triangleRep]
  have h_fixed : π u y = y := (D.mem_triangleBase_iff z y).mp y.prop u hu
  -- `π u` is surjective, so it is enough to test against the translates `π u x`
  refine ext_inner_right ℂ ((π.apply_bijective u).surjective.forall.mpr fun x ↦ ?_)
  calc ⟪π u v, π u x⟫ = ⟪a y, a x⟫ := by rw [inner_formRep, hv]
    _ = ⟪c • a (π u y), c • a (π u x)⟫ := by rw [← h_move, ← h_move, inner_formRep]
    _ = ⟪a y, a (π u x)⟫ := by
      simp [h_fixed, mul_comm _ (conj c), ← mul_assoc, conj_mul', hc]
    _ = ⟪v, π u x⟫ := (hv _).symm

/-- For `i < D.m`, the first lift of row `i` is injective on `New.Data.triangleBase`. -/
lemma eq_zero_of_triangleFirstLift_eq_zero {P : Parameters} (D : Data P) (z : Bool)
    (ϑ : D.MFoldTwist) (i : ℕ) (hi : i < D.m) (y : D.triangleBase z)
    (hy : D.triangleFirstLift z ϑ i y = 0) : y = 0 := by
  -- The point datum `pointDatum` is sharp for a level that fixes the copy of `y`.
  obtain ⟨C, -, h_rallis⟩ :=
    rallis_inner_product_cosetTerm (S := D.gridSpace i z 0 0) (T := D.gridSpace i z 0 (0 + 1))
      (D.paramsCorrespond_grid_succ_right z i 0 0 D.m.zero_le (by omega)
        (.inr rfl)).isEdge_jointHarmonic
      (D.two_mul_card_gridIndex_zero_lt z)
  have h_copy : D.triangleNegEquiv z i y = 0 :=
    (h_rallis _ _ (D.isSharp_pointDatum z ϑ i) _ (D.hasLevel_triangleNegEquiv z ϑ i y)).1 hy
  simpa using h_copy

/-- The inner product formula for `a = triangleFirstLift z ϑ i`, which copies a form from the corner
`(0, 0)` of the triangle `z` to `(i, 0)` and lifts it to `(i, 1)`. Here `i < D.m`, the number of
lifts of the data `D`. There is a constant `C` such that for every twist `ϑ`, every form `y` at the
corner fixed by the base level (`triangleBase`) and every form `x` at the corner, the series of the
terms `C * triangleRallisTerm` converges to `triangleGLCard z ϑ 0 * ⟪a x, a y⟫`; the first factor is
the order of the general linear group of the corner modulo `𝔪 = triangleModulus z ϑ`. -/
lemma exists_hasSum_triangleRallisTerm {P : Parameters} (D : Data P) (z : Bool) (i : ℕ)
    (hi : i < D.m) :
    ∃ C : ℂ, ∀ (ϑ : D.MFoldTwist) (y : D.triangleBase z) (x : D.TriangleForm z 0 0),
      HasSum (fun γ : D.TriangleCoset z ϑ ↦ C * D.triangleRallisTerm z ϑ i x y γ)
        (triangleGLCard z ϑ 0 * ⟪D.triangleFirstLift z ϑ i x, D.triangleFirstLift z ϑ i y⟫) := by
  -- Apply Rallis' inner product formula to the first edge of row `i` with the point datum
  -- `pointDatum`, which is sharp for a level that fixes the copy of `y`.
  obtain ⟨C, -, h_rallis⟩ :=
    rallis_inner_product_cosetTerm (S := D.gridSpace i z 0 0) (T := D.gridSpace i z 0 (0 + 1))
      (D.paramsCorrespond_grid_succ_right z i 0 0 D.m.zero_le (by omega)
        (.inr rfl)).isEdge_jointHarmonic
      (D.two_mul_card_gridIndex_zero_lt z)
  refine ⟨C, fun ϑ y x ↦ ?_⟩
  let term (γ : D.TriangleCoset z ϑ) : ℂ :=
    cosetTerm (card (D.GridIndex z 0 (0 + 1))) (D.gridChar ϑ (!z) (0 + i) (D.GridIndex z 0 (0 + 1)))
      (triangleModulus z ϑ).places.conjClosureᶜ (D.triangleNegEquiv z i x)
        (D.triangleNegEquiv z i y) γ
  have h_sum : HasSum
      (fun γ : D.TriangleCoset z ϑ ↦ C * (1 / card (D.GridIndex z 0 (0 + 1) × D.GridIndex z 0 0 →
        (triangleModulus z ϑ).ResidueRing) / triangleGLCard z ϑ 0) * term γ)
      ⟪D.triangleFirstLift z ϑ i x, D.triangleFirstLift z ϑ i y⟫ :=
    (h_rallis _ _ (D.isSharp_pointDatum z ϑ i) _ (D.hasLevel_triangleNegEquiv z ϑ i y)).2 _
  -- multiply by `triangleGLCard z ϑ 0`, which cancels against the mass of the datum
  refine (h_sum.mul_left (triangleGLCard z ϑ 0 : ℂ)).congr_fun fun γ ↦ ?_
  simp [term, cosetTerm, ← triangleNegEquiv_triangleRep, field, -Bool.cond_eq_ite]

/-- Injectivity and inner product formula for `a = triangleFirstLift z ϑ i`, which copies a form
from the corner `(0, 0)` of the triangle `z` to `(i, 0)` and lifts it to `(i, 1)`. Here `i < D.m`,
the number of lifts of the data `D`. There is a constant `C` such that for every twist `ϑ` and every
form `y` at the corner fixed by `triangleBaseLevel` (`triangleBase`) two statements hold. (a) If `v`
satisfies `⟪v, x⟫ = ⟪a y, a x⟫` for all `x`, then `v` lies in `triangleBase`, and `v = 0` implies
`y = 0`. (b) For every form `x` at the corner, the series of the terms `C * triangleRallisTerm`,
multiples of `⟪x, g y⟫`, over the cosets `TriangleCoset` of the finite points `g` modulo those
integral off `𝔪 = triangleModulus z ϑ` and its conjugate, converges to
`triangleGLCard z ϑ 0 * ⟪a x, a y⟫`; the first factor is the order of the general linear group of
the corner modulo `𝔪`. -/
theorem exists_hasSum_inner_triangleFirstLift {P : Parameters} (D : Data P) (z : Bool) (i : ℕ)
    (hi : i < D.m) :
    ∃ C : ℂ, ∀ (ϑ : D.MFoldTwist) (y : D.triangleBase z),
      (∀ v : D.TriangleForm z 0 0,
        (∀ x : D.TriangleForm z 0 0, ⟪v, x⟫ = ⟪D.triangleFirstLift z ϑ i y,
          D.triangleFirstLift z ϑ i x⟫) →
          v ∈ D.triangleBase z ∧ (v = 0 → y = 0)) ∧
      ∀ x : D.TriangleForm z 0 0,
        HasSum (fun γ : D.TriangleCoset z ϑ ↦ C * D.triangleRallisTerm z ϑ i x y γ)
          (triangleGLCard z ϑ 0 * ⟪D.triangleFirstLift z ϑ i x, D.triangleFirstLift z ϑ i y⟫) := by
  obtain ⟨C, h_sum⟩ := D.exists_hasSum_triangleRallisTerm z i hi
  refine ⟨C, fun ϑ y ↦ ⟨fun v hv ↦ ⟨?_, fun hv_zero ↦ ?_⟩, h_sum ϑ y⟩⟩
  · exact D.mem_triangleBase_of_inner_eq_inner_triangleFirstLift z ϑ i hi y hv
  · -- if `v = 0` then the lift of `y` has norm zero
    apply D.eq_zero_of_triangleFirstLift_eq_zero z ϑ i hi y
    rw [← inner_self_eq_zero (𝕜 := ℂ), ← hv, hv_zero, inner_zero_left]

-- The index type of the node `(i, n + 1)` unfolds to a sum type, and `kernelPair l s false` to
-- `typeKernel l s`; rewriting below has to see through both.
attribute [local implicit_reducible] Data.GridIndex BlockIndex kernelPair

omit [CMType E] [WeilData E] [Fintype N] [DecidableEq N] [Fintype N'] [DecidableEq N'] in
/-- Every polynomial `P` is the signed transpose `flipPoly s t` of the polynomial obtained from some
`Q` by conjugating the coefficients. -/
lemma exists_flipPoly_map_conj_eq (s : N → ℤˣ) (t : N' → ℤˣ)
    (P : MvPolynomial (NumberField.InfinitePlace E × N × N') ℂ) :
    ∃ Q : MvPolynomial (NumberField.InfinitePlace E × N' × N) ℂ,
      flipPoly s t (MvPolynomial.map conj Q) = P := by
  -- The same map with the two sign vectors exchanged undoes it, because the signs square to `1`.
  refine ⟨flipPoly t s (P.map conj), ?_⟩
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    have h_var : flipPoly s t (.map conj (flipPoly t s (.map conj (.X v)))) = .X v := by
      -- `zsmul_eq_mul` is excluded so that the two signs meet in one scalar
      simp [flipPoly, Int.cast_smul_eq_zsmul, pairSign, -zsmul_eq_mul, smul_smul, ← Units.val_mul,
        mul_comm (t _)]
    simp only [map_mul, hp, h_var]

/-! ### Left and reversed pairs, descents and ascents -/

variable {P : Parameters} (D : Data P) (z : Bool) (ϑ : D.MFoldTwist) (i n : ℕ)

/-- The kernels at infinity of the node `(i, n)` of the triangle: that of the parameter `gridParam`
for `b = false`, and that of its negative for `b = true`. -/
abbrev triangleKernel (b : Bool) : GInf D.E (D.gridSigns z i 0 n) → ℂ :=
  kernelPair (D.gridParam z i 0 n) (D.gridSigns z i 0 n) b

/-- The character of the left pairs that add the block `i + 1`, on a space with index type `M`: the
inverse of the character `gridChar ϑ (!z) (0 + i)` of the first lift `triangleLift z ϑ i 0` of row
`i`, times `upsilonU1` (the splitting character on the norm-one ideles) to the rank of the space. -/
abbrev leftPairChar (M : Type) [Fintype M] : AutChar D.E :=
  (D.gridChar ϑ (!z) (0 + i) M)⁻¹ * upsilonU1 ^ card M

/-- Polynomial data at infinity for an edge from a node in column `n` to a node in column `n'`. -/
abbrev EdgePoly (n' : ℕ) : Type :=
  MvPolynomial (NumberField.InfinitePlace D.E × D.GridIndex z 0 n' × D.GridIndex z 0 n) ℂ

/-- Finite data for an edge from a node in column `n` to a node in column `n'`. -/
abbrev EdgeDatum (n' : ℕ) : Type :=
  Matrix (D.GridIndex z 0 n') (D.GridIndex z 0 n) (triangleModulus z ϑ).ResidueRing → ℂ

/-- The polynomial `Φ` makes an edge (`IsEdgeFamily`) along the left pair, from the node
`(i + 1, n)` to the node `(i, n + 1)`, with the characters `leftPairChar` of row `i`. -/
abbrev IsLeftPair (Φ : D.EdgePoly z n (n + 1)) : Prop :=
  IsEdgeFamily (fun ϑ : D.MFoldTwist ↦ D.leftPairChar z ϑ i) (D.triangleKernel z (i + 1) n)
    (D.triangleKernel z i (n + 1)) true Φ

/-- The polynomial `Φ` makes an edge along the reversed pair, from the node `(i, n + 1)` to the
node `(i + 1, n)`, each space with its character in `IsLeftPair`. -/
abbrev IsReversedPair (Φ : D.EdgePoly z (n + 1) n) : Prop :=
  IsEdgeFamily (fun ϑ : D.MFoldTwist ↦ D.leftPairChar z ϑ i) (D.triangleKernel z i (n + 1))
    (D.triangleKernel z (i + 1) n) true Φ

/-- The transposed lift along the left pair, from forms at the node `(i, n + 1)` to forms at the
node `(i + 1, n)`, with polynomial `Φ` and finite datum `Ψ`. -/
abbrev triangleTransposedLift (Φ : D.EdgePoly z n (n + 1)) (Ψ : D.EdgeDatum z ϑ n (n + 1)) :
    D.TriangleForm z i (n + 1) →ₗ[ℂ] D.TriangleForm z (i + 1) n :=
  modTransposedLift (D.gridSpace (i + 1) z 0 n) (D.gridSpace i z 0 (n + 1)) (D.leftPairChar z ϑ i) Φ
    Ψ
    (typeKernel (D.gridParam z i 0 (n + 1)) (D.gridSigns z i 0 (n + 1)))
    (typeKernel (D.gridParam z (i + 1) 0 n) (D.gridSigns z (i + 1) 0 n))

/-- The transposed lift along the reversed pair, from forms at the node `(i + 1, n)` to forms at the
node `(i, n + 1)`, with polynomial `Φ` and finite datum `Ψ`. -/
abbrev triangleReversedLift (Φ : D.EdgePoly z (n + 1) n) (Ψ : D.EdgeDatum z ϑ (n + 1) n) :
    D.TriangleForm z (i + 1) n →ₗ[ℂ] D.TriangleForm z i (n + 1) :=
  modTransposedLift (D.gridSpace i z 0 (n + 1)) (D.gridSpace (i + 1) z 0 n) (D.leftPairChar z ϑ i) Φ
    Ψ
    (typeKernel (D.gridParam z (i + 1) 0 n) (D.gridSigns z (i + 1) 0 n))
    (typeKernel (D.gridParam z i 0 (n + 1)) (D.gridSigns z i 0 (n + 1)))

/-- The theta lift from the node `(i, n)` to the node `(i, n + 1)` with an arbitrary finite datum
`Ψ`; `triangleLift` is the case of the point datum `pointDatum`. -/
abbrev triangleDatumLift (Ψ : D.EdgeDatum z ϑ n (n + 1)) :
    D.TriangleForm z i n →ₗ[ℂ] D.TriangleForm z i (n + 1) :=
  modLift (D.gridSpace i z 0 n) (D.gridSpace i z 0 (n + 1)) (gridChar ϑ (!z) (n + i))
    (D.gridHarmonic i false (!z) (n + i) z 0 n 0 (n + 1)) Ψ
    (typeKernel (D.gridParam z i 0 n) (D.gridSigns z i 0 n))
    (typeKernel (D.gridParam z i 0 (n + 1)) (D.gridSigns z i 0 (n + 1)))

lemma triangleLift_eq_triangleDatumLift :
    D.triangleLift z ϑ i n = D.triangleDatumLift z ϑ i n
      (pointDatum (triangleModulus z ϑ).ResidueRing) :=
  rfl

variable {i n}

/-- The transposed lift `triangleTransposedLift` with finite datum `Ψ` equals the sum, over matrices
`η` modulo `triangleModulus z ϑ`, of `Ψ η` times the lift with the datum `Pi.single η 1`. -/
lemma triangleTransposedLift_eq_sum (Φ : D.EdgePoly z n (n + 1)) (Ψ : D.EdgeDatum z ϑ n (n + 1))
    (y : D.TriangleForm z i (n + 1)) :
    D.triangleTransposedLift z ϑ i n Φ Ψ y =
      ∑ η : Matrix (D.GridIndex z 0 (n + 1)) (D.GridIndex z 0 n) (triangleModulus z ϑ).ResidueRing,
        Ψ η • D.triangleTransposedLift z ϑ i n Φ (Pi.single η 1) y := by
  apply modTransposedLift_eq_sum

/-- The reversed lift `triangleReversedLift` with finite datum `Ψ` equals the sum, over matrices `η`
modulo `triangleModulus z ϑ`, of `Ψ η` times the lift with the datum `Pi.single η 1`. -/
lemma triangleReversedLift_eq_sum (Φ : D.EdgePoly z (n + 1) n) (Ψ : D.EdgeDatum z ϑ (n + 1) n)
    (y : D.TriangleForm z (i + 1) n) :
    D.triangleReversedLift z ϑ i n Φ Ψ y =
      ∑ η : Matrix (D.GridIndex z 0 n) (D.GridIndex z 0 (n + 1)) (triangleModulus z ϑ).ResidueRing,
        Ψ η • D.triangleReversedLift z ϑ i n Φ (Pi.single η 1) y := by
  apply modTransposedLift_eq_sum

/-- The Fourier transform of the complex conjugate of a finite datum, a datum for the edge read
backwards. -/
abbrev fourierDatum {n' : ℕ} (Ψ : D.EdgeDatum z ϑ n n') : D.EdgeDatum z ϑ n' n :=
  matrixFourier (triangleModulus z ϑ).primAddChar (star Ψ)

/-- For `i + n < D.m`, the kernels, characters and polynomial of the lift from the node `(i, n)` to
the node `(i, n + 1)` form an edge (`IsEdgeFamily`). -/
lemma isEdgeFamily_triangleKernel (h_lt : i + n < D.m) :
    IsEdgeFamily (fun ϑ : D.MFoldTwist ↦ D.gridChar ϑ (!z) (n + i)) (D.triangleKernel z i n)
      (D.triangleKernel z i (n + 1)) false (D.gridHarmonic i false (!z) (n + i) z 0 n 0 (n + 1)) :=
  isEdgeFamily_of_paramsCorrespond _ false (fun ϑ ↦ gridChar_hasWeight ϑ (!z) (n + i) _)
    (fun ϑ ↦ gridChar_hasWeight ϑ (!z) (n + i) _)
    (D.paramsCorrespond_grid_succ_right z i 0 n D.m.zero_le (by omega) (.inr rfl))

lemma exists_isLeftPair (h_lt : i + n < D.m) :
    ∃ Φ : D.EdgePoly z n (n + 1), D.IsLeftPair z i n Φ := by
  refine ⟨_, isEdgeFamily_of_paramsCorrespond _ true (fun _ ↦ inferInstance)
    (fun _ ↦ inferInstance) ?_⟩
  rw [zero_add]
  exact (D.paramsCorrespond_leftPair z h_lt).1

lemma exists_isReversedPair (h_lt : i + n < D.m) :
    ∃ Φ : D.EdgePoly z (n + 1) n, D.IsReversedPair z i n Φ := by
  refine ⟨_, isEdgeFamily_of_paramsCorrespond _ true (fun _ ↦ inferInstance)
    (fun _ ↦ inferInstance) ?_⟩
  rw [zero_add]
  exact (D.paramsCorrespond_leftPair z h_lt).2

end Data

end New

end TriangleArrows

end
