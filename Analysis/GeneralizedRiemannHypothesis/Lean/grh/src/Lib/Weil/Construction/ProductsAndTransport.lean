import Lib.Weil.Construction.VacuumProjections

/-!
# Products of data along a splitting of coordinates, and changes of coordinates

This file forms the product f₁ ⊠ f₂ = `New.Space.boxProd` of data along a splitting of the
coordinates that is compatible with the signs. It also defines the block diagonal embedding
`New.G.blockEmb` of the two unitary groups. It shows that the product is compatible with the
Heisenberg operators, the vacua, the inner products, the insertion of real Fock vectors and the
Weil representation of block diagonal elements. It defines the changes of coordinates
`New.CoordChange` that keep the vacuum, and the transport `New.CoordChange.map` of data along them.
It shows that the transport preserves norms and respects the Heisenberg operators, the vacuum,
the insertion of a real vector, and the Weil representation up to a scalar.

## Main definitions and results

* `New.Space.rho_boxProd`, `New.Space.boxProd_vacElem`, `New.Space.dataInner_boxProd`,
  `New.Space.omega_boxProd`, `New.Space.boxProd_integrated`: the product respects the Heisenberg
  operators, the vacua, the inner products, the Weil representation of block diagonal elements and
  the insertion of real Fock vectors.
* `New.CoordChange.map_rho`, `New.CoordChange.map_vacElem`, `New.CoordChange.map_omega`,
  `New.CoordChange.map_integrated`: transport respects the Heisenberg operators, the vacuum, the
  Weil representation (up to a scalar) and the insertion of a real vector.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to the diagonal matrix of its signs at the infinite places and 1 at the finite places.
* `New.𝒮`: The Banach space 𝒮(V) of integrable functions c on 𝔸^n with c(x) = ∫ c(y)β(y,x)e(x−y) dy,
  under the L¹ norm; β is the adelic bicharacter and e the vacuum function `New.vacuumFn`.
* `New.Space.vacElem`: The vacuum: the function e (Gaussian times twisted lattice indicator) as an
  element of 𝒮(V).

## Relation to the literature

Known; see `Lib.Weil.Construction.VacuumProjections` for sources.
-/

noncomputable section

namespace New

/-!
## Products of data along a splitting of the coordinates

The coordinates split by a bijection e : n₁ ⊕ n₂ ≃ n under which the signs `s` become `s₁` followed
by `s₂`.

* `New.G.blockEmb`: the block diagonal embedding of the two unitary groups; it is a closed embedding
  and, for the definite spaces `New.stdSpace`, detects rational points.
* `New.Space.boxProd`: the bounded bilinear product f₁ ⊠ f₂ of data, the product of the underlying
  functions. It respects the Heisenberg operators, the vacua, the inner products, the insertion of
  real Fock vectors and the Weil representation of block diagonal elements. A renaming of the
  coordinates is the case of an empty second summand.
* `New.weilMultiplier_fromBlocks`: the multiplier `New.weilMultiplier` of the Weil representation is
  multiplicative on block diagonal elements.

Throughout, the hypothesis `hs : s ∘ e = s₁ ⊕ᵥ s₂` says that e carries the signs s to s₁ followed by
s₂, and V, V₁, V₂ are spaces with the signs s, s₁, s₂.
-/

section DataProduct

open NumberField Matrix Fock Function Heisenberg Rep Sum OrthogonalSum G

variable {E : Type*} [Field E] [CMType E]
  {n : Type*} [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  {n₂ : Type*} [Fintype n₂] [DecidableEq n₂] {s₂ : n₂ → ℤˣ}
  {n₁ : Type*} [Fintype n₁] [DecidableEq n₁] {s₁ : n₁ → ℤˣ}
  {e : n₁ ⊕ n₂ ≃ n} (hs : s ∘ e = s₁ ⊕ᵥ s₂) {V : Space E n s} {V₁ : Space E n₁ s₁}
  {V₂ : Space E n₂ s₂}

/-! ### Block diagonal elements -/

/-- The homomorphism sending a pair of elements of the adelic unitary groups of signs s₁, s₂ to
their block-diagonal matrix, reindexed into the unitary group of signs s. -/
def G.blockEmb {E : Type*} [Field E] [NumberField E] [IsCMField E] (hs : s ∘ e = s₁ ⊕ᵥ s₂) :
    G E s₁ × G E s₂ →* G E s :=
  (reindex e (by simp [← hs, comp_assoc])).toMonoidHom.comp sum

/-- For the definite spaces `stdSpace` (all signs `1`; `hs` records that `e` keeps these signs), the
block diagonal element `blockEmb hs g` of a pair `g` lies in the rational points `Γ` of
`stdSpace E n` exactly when `g.fst` and `g.snd` lie in those of `stdSpace E n₁` and
`stdSpace E n₂`. -/
@[simp]
lemma SiegelWeil.blockEmb_mem_Gamma_iff (hs : (1 : n → ℤˣ) ∘ e = (1 : n₁ → ℤˣ) ⊕ᵥ (1 : n₂ → ℤˣ))
    {g : G E 1 × G E 1} :
    blockEmb (e := e) hs g ∈ (stdSpace E n).Γ ↔
      g.fst ∈ (stdSpace E n₁).Γ ∧ g.snd ∈ (stdSpace E n₂).Γ := by
  simp [Space.mem_Gamma_iff_range, blockEmb, reindex_equiv e]

/-- The block diagonal embedding `blockEmb hs` of `G E s₁ × G E s₂` into `G E s` is a closed
embedding. -/
@[fun_prop]
lemma G.isClosedEmbedding_blockEmb : Topology.IsClosedEmbedding (blockEmb (E := E) hs) := by
  -- Reindexing along `e` has the continuous left inverse `reindex e.symm hs`, so it is a closed
  -- embedding; so is the block sum.
  have h_signs : (s₁ ⊕ᵥ s₂) ∘ e.symm = s := by simp [← hs, comp_assoc]
  have h_reindex : Topology.IsClosedEmbedding (reindex (E := E) e.symm hs).symm :=
    (reindex e.symm hs).toEquiv.right_inv.isClosedEmbedding (continuous_reindex e.symm hs)
      (continuous_reindex e h_signs)
  have h_sum : Topology.IsClosedEmbedding (sum : G E s₁ × G E s₂ →* G E (s₁ ⊕ᵥ s₂)) := by
    fun_prop
  exact h_reindex.comp h_sum

variable [WeilData E]

include hs

/-! ### The product of data -/

omit [CMType E] [Fintype n] [DecidableEq n] [Fintype n₂] [DecidableEq n₂] [Fintype n₁]
  [DecidableEq n₁] [WeilData E] in
/-- The splitting of the coordinates induces a sign-compatible splitting of the real coordinates,
which are indexed by pairs (infinite place, coordinate). -/
lemma realSigns_comp_split :
    realSigns E s ∘
        (Equiv.prodSumDistrib (InfinitePlace E) n₁ n₂).symm.trans
          (Equiv.prodCongr (Equiv.refl (InfinitePlace E)) e) =
      realSigns E s₁ ⊕ᵥ realSigns E s₂ := by simp_all [funext_iff]

namespace Space

/-- For a sign-compatible splitting of the coordinates, the bounded bilinear map 𝒮(V₁) × 𝒮(V₂) →
𝒮(V), c₁ ⊠ c₂ = ∬ c₁(y₁)c₂(y₂) ϱ(y₁,0)ϱ(0,y₂)vac dy₁dy₂, where ϱ(y)c(x) = β(y,x)c(x−y). It is the
product of the underlying functions, see `New.Space.boxProd_val`. -/
def boxProd : 𝒮 V₁ →L[ℂ] 𝒮 V₂ →L[ℂ] 𝒮 V :=
  tmul
    { -- Join two vectors into one on `n₁ ⊕ n₂`, then relabel the coordinates along `e`.
      equiv :=
        ContinuousAddEquiv.trans
          (ContinuousAddEquiv.symm
            (ContinuousAddEquiv.mk' Homeomorph.sumArrowHomeomorphProdArrow (by simp [funext_iff])))
          { toFun x := x ∘ e.symm
            invFun x := x ∘ e
            left_inv := by cat_disch
            right_inv := by cat_disch
            map_add' := by cat_disch }
      -- Both `β` and the vacuum are products over the coordinates.
      beta_equiv := by
        simp +singlePass [adelicHeisenberg_beta_eq_prod]
        simp_all [funext_iff, reindex_equiv e]
        -- What is left differs only by unfolding the joining of two vectors.
        exact fun _ _ _ _ ↦ rfl
      vac_equiv := by
        simp +singlePass [vacuumFn_eq_prod]
        simp_all [funext_iff, reindex_equiv e]
        -- As for `beta_equiv`.
        exact fun _ _ ↦ rfl }

/-- On the underlying integrable functions, (f₁ ⊠ f₂)(x) = f₁(x₁) f₂(x₂), where x₁ and x₂ are the
two parts of the vector x. -/
lemma boxProd_val (f₁ : 𝒮 V₁) (f₂ : 𝒮 V₂) (x : n → 𝔸 E) :
    (boxProd (V := V) hs f₁ f₂).val x = f₁.val (x ∘ e ∘ inl) * f₂.val (x ∘ e ∘ inr) :=
  tmul_apply _ f₁ f₂ x

/-- Let the coordinates of V split along e : n₁ ⊕ n₂ ≃ n into those of V₁ and V₂, with compatible
signs (`hs`), and let f₁ ⊠ f₂ be the box product 𝒮(V₁) × 𝒮(V₂) → 𝒮(V). For an adelic vector x, the
Heisenberg operator satisfies ϱ(x)(f₁ ⊠ f₂) = ϱ(x₁)f₁ ⊠ ϱ(x₂)f₂, where x₁ = x ∘ e ∘ inl and x₂ = x ∘
e ∘ inr are the two parts of x. -/
lemma rho_boxProd (x : n → 𝔸 E) (f₁ : 𝒮 V₁) (f₂ : 𝒮 V₂) :
    V.ϱ x (boxProd hs f₁ f₂) = boxProd hs (V₁.ϱ (x ∘ e ∘ inl) f₁) (V₂.ϱ (x ∘ e ∘ inr) f₂) :=
  heisenbergOp_tmul _ f₁ f₂ x

/-- When the coordinates and signs of V split into those of V₁ and V₂, ϱ(y₁)f₁ ⊠ ϱ(y₂)f₂ = ϱ(y)(f₁ ⊠
f₂), where y is the vector with parts y₁ and y₂. -/
lemma boxProd_rho (y₁ : n₁ → 𝔸 E) (y₂ : n₂ → 𝔸 E) (f₁ : 𝒮 V₁) (f₂ : 𝒮 V₂) :
    boxProd hs (V₁.ϱ y₁ f₁) (V₂.ϱ y₂ f₂) = V.ϱ ((y₁ ⊕ᵥ y₂) ∘ e.symm) (boxProd hs f₁ f₂) := by
  simp [rho_boxProd, comp_def]

/-- Let `e` split the coordinates of `V` into those of `V₁` and `V₂`, compatibly with the signs
(`hs`). The bilinear map `boxProd hs` : 𝒮(V₁) × 𝒮(V₂) → 𝒮(V) is the product of the underlying
functions. It sends the pair of vacua of `V₁` and `V₂` (each a Gaussian times a twisted lattice
indicator) to the vacuum `V.vacElem` of `V`. -/
@[simp]
lemma boxProd_vacElem : boxProd hs V₁.vacElem V₂.vacElem = V.vacElem := tmul_vacElem _

/-- For a splitting of the coordinates of V into those of V₁ and V₂ compatible with the signs,
the product of data is multiplicative for the inner products:
⟨f₁ ⊠ f₂, f₁′ ⊠ f₂′⟩ = ⟨f₁, f₁′⟩ ⟨f₂, f₂′⟩. -/
lemma dataInner_boxProd (f₁ f₁' : 𝒮 V₁) (f₂ f₂' : 𝒮 V₂) :
    V.dataInner (boxProd hs f₁ f₂) (boxProd hs f₁' f₂') =
      V₁.dataInner f₁ f₁' * V₂.dataInner f₂ f₂' :=
  modelInner_tmul _ f₁ f₁' f₂ f₂'

/-- The product respects the insertion of real vectors:
(v₁ ⊗ f₁) ⊠ (v₂ ⊗ f₂) = (v₁ ⊠ v₂) ⊗ (f₁ ⊠ f₂). Here v ⊗ f = `New.Space.integrated` v f inserts a
vector v of the Fock space of the real coordinates, and v₁ ⊠ v₂ = `New.Fock.realBoxProd` is the
product of Fock vectors along the splitting of the real coordinates given by
`realSigns_comp_split`. -/
lemma boxProd_integrated (v₁ : IsVacuum.Model (realHeisenberg (realSigns E s₁)))
    (v₂ : IsVacuum.Model (realHeisenberg (realSigns E s₂))) (f₁ : 𝒮 V₁) (f₂ : 𝒮 V₂) :
    boxProd hs (V₁.integrated v₁ f₁) (V₂.integrated v₂ f₂) =
      V.integrated (realBoxProd (realSigns_comp_split hs) v₁ v₂) (boxProd hs f₁ f₂) := by
  -- `integrated_tmul` writes the right side as an integral against `v₁` of an integral against
  -- `v₂`. By `map_integrated` an intertwining map commutes with such an integral, so each one
  -- passes out of its factor. The two goals left are the intertwining properties: a real vector of
  -- one summand acts on the product through that factor only. (`erw`: `integrated` matches the
  -- integral of `map_integrated` only after unfolding the Heisenberg representation.)
  erw [map_integrated _ ((boxProd hs).flip _), map_integrated _ (boxProd hs _), eq_comm,
      integrated_tmul]
  · -- a real vector of the second summand acts on `f₁ ⊠ f` through `f`
    simp [left, right, rho_boxProd, realVec, realCoordSum, comp_def, ← Pi.zero_def,
      ← Prod.zero_eq_mk]
  · -- a real vector of the first summand acts on `f ⊠ (v₂ ⊗ f₂)` through `f`
    simp [left, rho_boxProd, realVec, realCoordSum, comp_def, ← Pi.zero_def,
      ← Prod.zero_eq_mk]

variable {g : G E s} {g₁ : G E s₁} {g₂ : G E s₂}

/-- If the matrix of g is block diagonal with blocks g₁, g₂ along a sign-compatible splitting e of
the coordinates (`h_blocks`: relabelling rows and columns of `g.adeleMatrix` by `e` gives
`fromBlocks g₁.adeleMatrix 0 0 g₂.adeleMatrix`), then Δ(g) = Δ(g₁)Δ(g₂) for Δ =
`New.weilMultiplier`. -/
lemma _root_.New.weilMultiplier_fromBlocks
    (h_blocks : g.adeleMatrix.submatrix e e = fromBlocks g₁.adeleMatrix 0 0 g₂.adeleMatrix) :
    weilMultiplier g = weilMultiplier g₁ * weilMultiplier g₂ := by
  -- The real factors: a principal minor of a block diagonal matrix is the product of two minors.
  have h_real (w : InfinitePlace E) :
      realMultiplier (g.fst w) = realMultiplier (g₁.fst w) * realMultiplier (g₂.fst w) := by
    have h_block : ((g.fst w : GL n ℂ) : Matrix n n ℂ).submatrix e e =
        fromBlocks ((g₁.fst w : GL n₁ ℂ) : Matrix n₁ n₁ ℂ) 0 0
          ((g₂.fst w : GL n₂ ℂ) : Matrix n₂ n₂ ℂ) := by
      simp_all [← ext_iff, Prod.ext_iff, funext_iff]
    simp_all [realMultiplier, ← principalMinor_submatrix e, principalMinor_fromBlocks, funext_iff]
  -- The finite factors: the finite part of `g` is block diagonal after relabelling by `e.symm`.
  have h_fin_block : ((g.snd : GL n (𝔸f E)) : Matrix n n (𝔸f E)) =
      (fromBlocks ((g₁.snd : GL n₁ (𝔸f E)) : Matrix n₁ n₁ (𝔸f E)) 0 0
        ((g₂.snd : GL n₂ (𝔸f E)) : Matrix n₂ n₂ (𝔸f E))).submatrix e.symm e.symm := by
    simp_all [← ext_iff, Prod.ext_iff, reindex_equiv e]
  have h_fin : finMultiplier g.snd = finMultiplier g₁.snd * finMultiplier g₂.snd :=
    glMultiplier_fromBlocks _ _ e.symm h_fin_block
  simp only [weilMultiplier, h_real, h_fin, Finset.prod_mul_distrib, mul_mul_mul_comm]

/-- If the matrix of g is block diagonal with blocks g₁, g₂ for a sign-compatible splitting of
the coordinates (`h_blocks`, as in `New.weilMultiplier_fromBlocks`), then
ω(g)(f₁ ⊠ f₂) = ω(g₁)f₁ ⊠ ω(g₂)f₂. When `n₂` is empty, e is a renaming of the coordinates, and this
is the rule that a renaming carries ω(g₁) to ω of the renamed element g. -/
lemma omega_boxProd
    (h_blocks : g.adeleMatrix.submatrix e e = fromBlocks g₁.adeleMatrix 0 0 g₂.adeleMatrix)
    (f₁ : 𝒮 V₁) (f₂ : 𝒮 V₂) :
    V.ω g (boxProd hs f₁ f₂) = boxProd hs (V₁.ω g₁ f₁) (V₂.ω g₂ f₂) := by
  -- The multiplier `weilMultiplier` is multiplicative on blocks, and `g` acts on the two summands
  -- by `g₁`, `g₂`.
  refine weilRep_tmul _ _ _ _ (weilMultiplier_fromBlocks hs h_blocks) (fun x ↦ ?_) f₁ f₂
  -- The action on the joined coordinates is that of `g.adeleMatrix` on
  -- `Sum.elim x.fst x.snd ∘ e.symm`.
  show g.adeleMatrix *ᵥ ((x.fst ⊕ᵥ x.snd) ∘ e.symm) = ((g₁ • x.fst) ⊕ᵥ (g₂ • x.snd)) ∘ e.symm
  rw [e.eq_comp_symm, ← submatrix_mulVec_equiv, h_blocks, fromBlocks_mulVec]
  simp only [zero_mulVec, add_zero, zero_add, elim_comp_inl, elim_comp_inr]
  rfl

end Space

end DataProduct

/-!
## Changes of coordinates that keep the vacuum

A change of coordinates `New.CoordChange` is a map φ = A × B of adelic vectors whose finite part B
keeps the standard lattice and turns x*x into −x*x, that keeps the vacuum and keeps the bicharacter
β up to an isometric ring endomorphism σ of ℂ (in the uses, the identity or conjugation). The
examples negate a space or move it to the other side of a dual pair. A plain renaming of the
coordinates keeps x*x; it is covered by `New.Space.boxProd`.

* `New.CoordChange.map`, `New.CoordChange.realMap`: the σ-semilinear transport of data and of real
  Fock vectors.
-/

section CoordChange

open Matrix Heisenberg Rep stdLattice Complex Fock IsVacuum

variable (E : Type*) [Field E] [CMType E] [WeilData E]
  {n : Type*} [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  {n₁ : Type*} [Fintype n₁] [DecidableEq n₁]

/-- For signs `s` on `n` and `s₁` on `n₁` and a ring endomorphism `σ` of ℂ, a change of adelic
coordinates φ = A × B keeping the adelic bicharacter β of the Heisenberg group up to σ, where the
real part A keeps the Gaussian and the finite part B keeps Ô^n and turns x*x into −x*x. -/
structure CoordChange (σ : ℂ →+* ℂ) (s₁ : n₁ → ℤˣ) (s : n → ℤˣ) where
  /-- The change of coordinates: a bicontinuous additive bijection of adelic vectors. -/
  φ : (n → 𝔸 E) ≃ₜ+ (n₁ → 𝔸 E)
  /-- The real part `A`, acting on complex coordinates indexed by (infinite place, coordinate). -/
  realEquiv : (NumberField.InfinitePlace E × n → ℂ) ≃ₜ+ (NumberField.InfinitePlace E × n₁ → ℂ)
  /-- The finite part `B`, acting on finite adelic vectors. -/
  finEquiv : (n → 𝔸f E) ≃ₜ+ (n₁ → 𝔸f E)
  /-- In the coordinates `adelicSum`, the map `φ` is the product `A × B`. -/
  apply_adelicSum (y : (NumberField.InfinitePlace E × n → ℂ) × (n → 𝔸f E)) :
      φ ((adelicSum E s).equiv y) = (adelicSum E s₁).equiv (realEquiv y.fst, finEquiv y.snd)
  /-- `A` carries the real bicharacter of signs `s` to `σ` of that of signs `s₁`. -/
  beta_realEquiv (x y : NumberField.InfinitePlace E × n → ℂ) :
      σ ((realHeisenberg (realSigns E s₁)).β (realEquiv x) (realEquiv y)) =
        (realHeisenberg (realSigns E s)).β x y
  /-- `A` keeps the Gaussian exp(−|x|²/2). -/
  vac_realEquiv (x : NumberField.InfinitePlace E × n → ℂ) : realVac (realEquiv x) = realVac x
  /-- `B` keeps the finite bicharacter, `selfDualAddChar E` of ½ y*x, up to `σ`. -/
  selfDualAddChar_finEquiv (x y : n → 𝔸f E) :
      σ (selfDualAddChar E (half * Star.star (finEquiv y) ⬝ᵥ finEquiv x)) =
        selfDualAddChar E (half * Star.star y ⬝ᵥ x)
  /-- `B` turns x*x into −x*x. -/
  dot_finEquiv (x : n → 𝔸f E) : Star.star (finEquiv x) ⬝ᵥ finEquiv x = -Star.star x ⬝ᵥ x
  /-- `B` maps the standard lattice Ô^n onto the standard lattice Ô^{n₁}. -/
  finEquiv_mem (x : n → 𝔸f E) : finEquiv x ∈ stdLattice E n₁ ↔ x ∈ stdLattice E n

end CoordChange

namespace CoordChange

open Matrix Heisenberg Rep stdLattice Complex Fock IsVacuum

variable {E : Type*} [Field E] [CMType E] [WeilData E]
  {n : Type*} [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  {n₁ : Type*} [Fintype n₁] [DecidableEq n₁] {s₁ : n₁ → ℤˣ}
  {σ : ℂ →+* ℂ} [RingHomIsometric σ]
  (D : CoordChange E σ s₁ s) {V : Space E n s} {V₁ : Space E n₁ s₁}

omit [RingHomIsometric σ] in
/-- A change of coordinates φ with twist σ keeps the adelic bicharacter up to σ: σ(β₁(φx,
φy)) = β(x, y), where β₁ and β belong to the signs `s₁` and `s`. -/
lemma beta_phi :
    ∀ x y : n → 𝔸 E, σ ((adelicHeisenberg E s₁).β (D.φ x) (D.φ y)) =
      (adelicHeisenberg E s).β x y := by
  -- in the coordinates `adelicSum` both sides split into a real and a finite factor
  simp [reindex_equiv (adelicSum E s).equiv, OrthogonalSum.beta_equiv, stdLattice.finHeisenberg,
    apply_adelicSum, beta_realEquiv, selfDualAddChar_finEquiv]

omit [RingHomIsometric σ] in
/-- A change of coordinates keeps the vacuum function: e(φx) = e(x) for e = `New.vacuumFn`. -/
lemma vacuumFn_apply : ∀ x : n → 𝔸 E, vacuumFn (D.φ x) = vacuumFn x := by
  -- `D.finEquiv` keeps the lattice and changes the sign of `x*x`, so it conjugates the finite
  -- vacuum, which is real.
  have h_fin (x : n → 𝔸f E) : stdLattice.finVac (D.finEquiv x) = stdLattice.finVac x := by
    rw [← isVacuum_finVac.conj_apply x]
    aesop (add simp [stdLattice.finVac, dot_finEquiv, finEquiv_mem, inv_eq_conj,
      AddChar.map_neg_eq_inv])
  simp [reindex_equiv (adelicSum E s).equiv, OrthogonalSum.vac_equiv, apply_adelicSum,
    vac_realEquiv, h_fin]

/-- In the coordinates `adelicSum`, the vector with real part `0` and finite part `z` is
`finVec z`. -/
private lemma adelicSum_equiv_zero_fst {m : Type*} [Fintype m] [DecidableEq m] (r : m → ℤˣ)
    (z : m → 𝔸f E) : (adelicSum E r).equiv (0, z) = finVec z := by
  aesop (add simp adelicSum)

omit [RingHomIsometric σ] in
lemma apply_finVec (x : n → 𝔸f E) : D.φ (finVec x) = finVec (D.finEquiv x) := by
  -- `apply_adelicSum` at a vector with zero real part; `realEquiv` keeps `0`.
  rw [← adelicSum_equiv_zero_fst s x, D.apply_adelicSum, map_zero, adelicSum_equiv_zero_fst]

/-! ### Transport of data -/

/-- For a change of coordinates φ with twist σ, the continuous σ-semilinear map from 𝒮(V₁) to
𝒮(V) sending the coefficient function c to σ∘c∘φ. -/
def map : 𝒮 V₁ →SL[σ] 𝒮 V := IsVacuum.transport D.beta_phi D.vacuumFn_apply

/-- For a vacuum-preserving change of coordinates D with underlying map φ, the induced map from
𝒮(V₁) to 𝒮(V) intertwines the Heisenberg operators: it sends ϱ(φx)f to ϱ(x) applied to the
image of f, for all x and f. -/
lemma map_rho (x : n → 𝔸 E) (f : 𝒮 V₁) : D.map (V₁.ϱ (D.φ x) f) = V.ϱ x (D.map f) := by
  -- At a point `z` both sides are `β x z` times `σ` of the value of `f` at `D.φ (z - x)`. `erw`:
  -- elements of `𝒮 V` are those of the Heisenberg model only after unfolding, so
  -- `heisenbergOp_apply` and `transport_apply` do not apply by `rw`; they fire on both sides.
  refine ext fun _ ↦ ?_
  repeat erw [heisenbergOp_apply, transport_apply]
  simp [beta_phi]

/-- Let D be a change of adelic coordinates from signs `s₁` to `s` that keeps the Heisenberg
bicharacter up to the isometric ring endomorphism σ of ℂ. The map `D.map` : 𝒮(V₁) → 𝒮(V) induced by
D preserves norms. -/
lemma norm_map (f : 𝒮 V₁) : ‖D.map (V := V) f‖ = ‖f‖ :=
  norm_transport D.beta_phi D.vacuumFn_apply f

/-- For a change of adelic coordinates `D` from signs `s₁` to signs `s` (a map φ = A × B that keeps
the Heisenberg bicharacter β up to `σ`, where A keeps the Gaussian and B keeps Ô^n), the induced map
`D.map` from 𝒮(V₁) to 𝒮(V) sends the vacuum `V₁.vacElem` to the vacuum `V.vacElem`. Here `V` and
`V₁` are hermitian spaces with a point, and the vacuum is the Gaussian times the twisted lattice
indicator. -/
@[simp]
lemma map_vacElem : D.map V₁.vacElem = V.vacElem :=
  ext (map_integral_and_map_vacuum D.beta_phi D.vacuumFn_apply).2

/-- Let φ be a vacuum-preserving change of coordinates with twist σ. If φ(gx) = g₁φ(x) for all x and
σ(Δ(g₁)) = c·Δ(g), then (ω(g₁)f)^φ = c·ω(g)(f^φ) for all f in 𝒮(V₁), where f^φ = `D.map f` and
Δ = `New.weilMultiplier`. -/
lemma map_omega {g : G E s} {g₁ : G E s₁}
    (h_phi_mulVec : ∀ x : n → 𝔸 E, D.φ (g.adeleMatrix *ᵥ x) = g₁.adeleMatrix *ᵥ D.φ x)
    {c : ℂ} (hc : σ (weilMultiplier g₁) = c * weilMultiplier g) (f : 𝒮 V₁) :
    D.map (V₁.ω g₁ f) = c • V.ω g (D.map f) := by
  -- The left side at `x` is `σ` of the value of `ω(g₁) f` at `D.φ x`, the right side `c` times
  -- the value of `ω(g) (D.map f)` at `x`. (`erw`: as in `map_rho`, the lemmas about the Heisenberg
  -- model apply to `𝒮 V` only after unfolding.)
  refine ext fun x ↦ ?_
  show σ ((V₁.ω g₁ f).val (D.φ x)) = c * (V.ω g (D.map f)).val x
  -- write both values at `x` as `weilMultiplier` times an integral
  repeat erw [Space.ω, weilRep, IsVacuum.smul_apply, integrated_apply_eq_integral]
  -- substitute `D.φ` in the integral on the left: `σ (∫ F) = ∫ σ ∘ F ∘ D.φ` for every `F`, and
  -- `σ (e (D.φ x)) = e x` for the vacuum `e`
  have h_val (y : n → 𝔸 E) : (D.map (V := V) f).val y = σ (f.val (D.φ y)) := transport_apply ..
  simp [hc, ← h_phi_mulVec, ← map_sub, beta_phi, mul_assoc, h_val,
    map_integral_and_map_vacuum D.beta_phi D.vacuumFn_apply]

/-- For a change of coordinates with archimedean part A and twist σ, the continuous σ-semilinear
map from the Fock space of signs s₁ to that of signs s sending v to σ∘v∘A. -/
def realMap :
    Model (realHeisenberg (realSigns E s₁)) →SL[σ] Model (realHeisenberg (realSigns E s)) :=
  IsVacuum.transport D.beta_realEquiv D.vac_realEquiv

/-- Transport respects the insertion of a real vector: the transport of v ⊗ f is the transported
Fock vector `D.realMap v` inserted into the transport of f. -/
lemma map_integrated (v : Model (realHeisenberg (realSigns E s₁))) (f : 𝒮 V₁) :
    D.map (V₁.integrated v f) = V.integrated (D.realMap v) (D.map f) := by
  refine ext fun x ↦ ?_
  -- write both values at `x` as integrals over real vectors and substitute `A = D.realEquiv` on the
  -- left: `σ (∫ F) = ∫ σ ∘ F ∘ A` for every `F` (`erw` as in `map_rho`)
  erw [transport_apply, ← valueAt_apply, map_integrated_eq_integral,
    (map_integral_and_map_vacuum D.beta_realEquiv D.vac_realEquiv).1, ← valueAt_apply,
    map_integrated_eq_integral]
  -- the integrands agree: `D.φ` acts on a real vector `y` by `A`, and `D.map` respects `ϱ`
  congr! 2 with y
  erw [← map_rho, apply_adelicSum]
  -- both sides are `σ (v (A y))` times `σ` of the value of `ϱ(A y) f` at `D.φ x`
  aesop

/-- For a bijection e, units u_i of a topological ring R and a continuous involution `star`,
the topological additive isomorphism sending x to (u_i · star x_{e(i)})_i. -/
def starCoordEquiv {ι κ R : Type*} [Ring R] [TopologicalSpace R] [ContinuousMul R] [StarRing R]
    [ContinuousStar R] (e : κ ≃ ι) (u : κ → Rˣ) :
    (ι → R) ≃ₜ+ (κ → R) where
  toFun x i := u i * Star.star x (e i)
  invFun x := Star.star (fun i ↦ (u i)⁻¹ * x i) ∘ e.symm
  left_inv x := by aesop
  right_inv x := by aesop
  map_add' x y := by aesop

end CoordChange

end New

end
