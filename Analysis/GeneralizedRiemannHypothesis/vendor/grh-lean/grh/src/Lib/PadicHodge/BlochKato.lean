import Lib.PadicHodge.Crystalline.FixedRatios
import Lib.PadicHodge.Crystalline.HodgeTateJumps

/-!
# Bloch–Kato crystalline cocycles: reduction modulo p^m, rank and vanishing

Let `T` be a finite free `ℤ_[p]`-module of rank d with an action `ρ` of a group Γ, and let
j = `𝒥.toGp`, given by the structure `𝒥 : New.Period.OverGp Γ p`, map Γ with open image of index n
to the absolute Galois group `New.Gp` of ℚ_p. The Bloch–Kato cocycles
Z_f(T) = `New.Period.crysCocycles ρ` are the maps Γ → T that become coboundaries over the period
ring B = `New.Period.Bmax`. χ = `New.Period.χ` is the cyclotomic character `New.cyclotomicGp`
composed with j. The file proves basic properties of Z_f(T), builds admissible extensions from
crystalline cocycles of potentially crystalline representations, studies reduction modulo p^m, and
computes the rank of Z_f(T) and its vanishing.

## Main definitions and results

* `New.Period.IsPotentiallyCrystalline.exists_hodge_basis`: for potentially crystalline T, in a
  ℤ_p-basis of T, an automorphism of B_dR^ι that makes the action of Γ coordinatewise and carries
  (B_dR^+)^ι to the lattice given by the jumps of T.
* `New.Period.extensionRep`, `New.Period.isAdmissible_extensionRep`: the extension of a trivial
  module by T given by cocycles in `New.Period.crysCocycles` is admissible along the same filter as
  T (`New.Period.IsAdmissible`).
* `New.Period.IsPotentiallyCrystalline.reducedCocycle`: for an equivariant additive map `q` from `T`
  to a discrete module `V` with kernel `p ^ m T`, the map sending a crystalline cocycle `c` to the
  continuous cocycle `q ∘ c`.
* `New.Period.crysCocycles.finrank_eq`: for potentially crystalline T, Z_f(T) is finitely generated
  over ℤ_p of rank d + n·(number of negative Hodge–Tate jumps).
* `New.Period.IsPotentiallyCrystalline.exists_coboundary_eq_smul`: for potentially crystalline T
  with positive jumps, Z_f(T) is torsion modulo coboundaries.
* `New.Period.crysCocycles.apply_eq_zero_of_cyclotomicGp`: let Γ act through χ^(−a) with a ≥ 0. Then
  crystalline cocycles vanish where the action is trivial. When a = 0 we also need j(s) to lie in
  inertia.

Notions from other files:
* `New.Period.IsPotentiallyCrystalline`: the elements of Bmax ⊗ T fixed by all g with j(g) near 1
  span Bmax ⊗ T over Bmax.
* `New.DiscreteModule`: A discrete Γ-module over R: an R-module with the discrete topology and a
  continuous R-linear action of the topological group Γ.
* `New.DiscreteModule.HoldsCorestrictions`: for a discrete Γ-module V, an open subgroup U of Γ and
  groups of cocycles Y′ ≤ Z¹(U, V) and Y ≤ Z¹(Γ, V), the group Y contains every coboundary and a
  corestriction of each y in Y′: there is a cocycle F with values in the functions Γ/U → V whose
  Shapiro image is y and whose sum over Γ/U lies in Y.
* `New.Period.jump`: The multiplicity of the Hodge–Tate jump u at γ: the dimension over Q̄_p (zero
  if infinite) of the γ-semilinear f : T → ℂ_p with f(gx) = χ(g)^(−u)·g f(x) for g near 1.

## Relation to the literature

Known result: Bloch–Kato finite local condition, rank formula. Here it is treated on cocycles of a
lattice in a potentially crystalline representation. The rank is counted from the fundamental exact
sequence. Local duality is not treated in this file, only the reduction of crystalline cocycles
modulo p^m. Source: S. Bloch, K. Kato, L-functions and Tamagawa numbers of motives, Grothendieck
Festschrift I (1990), Prop. 3.8, Cor. 3.8.4; J. Bellaïche, An introduction to the conjecture of
Bloch and Kato, Clay Summer School notes (2009), Prop. 2.8, Thm 2.1.
-/

noncomputable section

/-!
## Crystalline cocycles: functoriality, coboundaries and saturation

* `New.Period.crysCocycles.comp_mem`: an equivariant map carries crystalline cocycles to crystalline
  cocycles.
* `New.Period.crysCocycles.coboundary_mem`, `New.Period.crysCocycles.apply_mul`: `crysCocycles ρ`
  contains the coboundaries and, for `T` free over `ℤ_p`, consists of cocycles.
* `New.Period.crysCocycles.mem_of_smul_mem`: `crysCocycles ρ` is saturated in the maps Γ → T.
-/

namespace New.Period.crysCocycles

open Module TensorProduct

variable {p : ℕ} {Γ R R' T T' : Type*}
  {c : Γ → T} [ThePrime p] [Group Γ] [CommRing R] [Algebra ℤ_[p] R] [CommRing R'] [Algebra ℤ_[p] R']
  [AddCommGroup T] [Module R T] [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [AddCommGroup T']
  [Module R' T'] [Module ℤ_[p] T'] [IsScalarTower ℤ_[p] R' T'] [OverGp Γ p]
  {ρ : Representation R Γ T} {σ : Representation R' Γ T'}

/-- Functoriality: a ℤ_p-linear map `f : T → T'` with `f (ρ g x) = σ g (f x)` carries a crystalline
cocycle `c` of `ρ` to the crystalline cocycle `f ∘ c` of `σ`. -/
lemma comp_mem (hc : c ∈ crysCocycles ρ) (f : T →ₗ[ℤ_[p]] T')
    (hf : ∀ (g : Γ) (x : T), f (ρ g x) = σ g (f x)) : f ∘ c ∈ crysCocycles σ := by
  -- The witness is the image under `b ⊗ x ↦ b ⊗ f x` of the witness for `c`.
  obtain ⟨y, hy⟩ :
      ∃ y : Bmax ⊗[ℤ_[p]] T, ∀ g : Γ, 1 ⊗ₜ c g = tensorAction Bmax (toGp g) (ρ g) y - y := hc
  refine ⟨periodTensorMap Bmax Bmax f y, fun g ↦ ?_⟩
  rw [tensorAction_periodTensorMap (hf g), ← map_sub, ← hy]
  simp [periodTensorMap]

/-- The coboundary `g ↦ g x - x` of an element `x` of T is a crystalline cocycle. -/
lemma coboundary_mem (x : T) : (fun g : Γ ↦ ρ g x - x) ∈ crysCocycles ρ :=
  ⟨1 ⊗ₜ x, by simp [tensorAction, tmul_sub]⟩

/-- If T is free over Z_p, every c in `crysCocycles ρ` is a cocycle: c(gh) = c(g) + g·c(h) for all
g, h. -/
lemma apply_mul [Free ℤ_[p] T] (hc : c ∈ crysCocycles ρ) :
    ∀ g h : Γ, c (g * h) = c g + ρ g (c h) := by
  intro g h
  obtain ⟨y, hy⟩ :
      ∃ y : Bmax ⊗[ℤ_[p]] T, ∀ g : Γ, 1 ⊗ₜ c g = tensorAction Bmax (toGp g) (ρ g) y - y := hc
  -- `x ↦ 1 ⊗ x` is injective, so it suffices to check the identity in `Bmax ⊗ T`, where it reads
  -- `g h y - y = (g y - y) + g (h y - y)`.
  refine Flat.tensorProduct_mk_injective ℤ_[p] _ Bmax ?_
  calc (1 : Bmax) ⊗ₜ[ℤ_[p]] c (g * h)
      = tensorAction Bmax (toGp (g * h)) (ρ (g * h)) y - y := hy (g * h)
    _ = (tensorAction Bmax (toGp g) (ρ g) y - y) +
          tensorAction Bmax (toGp g) (ρ g) (tensorAction Bmax (toGp h) (ρ h) y - y) := by
        rw [map_sub, tensorAction_tensorAction, ← map_mul, ← map_mul]
        abel
    _ = 1 ⊗ₜ c g + tensorAction Bmax (toGp g) (ρ g) (1 ⊗ₜ c h) := by rw [hy g, hy h]
    _ = 1 ⊗ₜ (c g + ρ g (c h)) := by simp [tensorAction, tmul_add]

/-- Saturation of Z_f(T) = `crysCocycles ρ`, the maps c : Γ → T that become coboundaries in Bmax ⊗ T
(1 ⊗ c g = (j(g) ⊗ ρ(g)) y − y for some y and all g, j : Γ → Gal(Q̄_p/Q_p) from `OverGp`): if a is a
non-zero element of ℤ_p and a·c lies in Z_f(T), then c lies in Z_f(T). -/
lemma mem_of_smul_mem {a : ℤ_[p]} (ha : a ≠ 0) : a • c ∈ crysCocycles ρ → c ∈ crysCocycles ρ := by
  -- `a` is invertible in `Bmax` and its inverse is Galois invariant: divide the witness by `a`.
  intro h_smul_mem
  obtain ⟨y, hy⟩ :
      ∃ y : Bmax ⊗[ℤ_[p]] T, ∀ g : Γ, 1 ⊗ₜ (a • c) g = tensorAction Bmax (toGp g) (ρ g) y - y :=
    h_smul_mem
  refine ⟨algebraMap ℚ_[p] Bmax a⁻¹ • y, fun g ↦ ?_⟩
  calc (1 : Bmax) ⊗ₜ[ℤ_[p]] c g
      = algebraMap ℚ_[p] Bmax (a : ℚ_[p])⁻¹ • (1 ⊗ₜ[ℤ_[p]] (a • c) g) := by
        simp [← algebraMap_smul ℚ_[p] a, ha]
    _ = algebraMap ℚ_[p] Bmax (a : ℚ_[p])⁻¹ • (tensorAction Bmax (toGp g) (ρ g) y - y) := by
        rw [hy g]
    _ = tensorAction Bmax (toGp g) (ρ g) (algebraMap ℚ_[p] Bmax (a : ℚ_[p])⁻¹ • y) -
          algebraMap ℚ_[p] Bmax (a : ℚ_[p])⁻¹ • y := by
        rw [tensorAction_smul, smul_algebraMap, smul_sub]

end New.Period.crysCocycles

namespace New.Period

/-!
## Hodge bases and cocycle extensions of potentially crystalline representations

* `New.Period.IsPotentiallyCrystalline.exists_hodge_basis`: a basis of B_dR ⊗ T adapted to the Hodge
  filtration in which the action of Γ is coordinatewise.
* `New.Period.extensionRep`, `New.Period.isAdmissible_extensionRep`,
  `New.Period.jump_extensionRep_le`: the extension of a trivial module by T given by crystalline
  cocycles is admissible, and its Hodge–Tate jumps u ≠ 0 are at most those of T.
* `New.Period.crysCocycles.eventually_eq_pow_smul`: a crystalline cocycle is divisible by p^m near
  1, for every m.
-/

section CocycleContinuity

variable {p : ℕ} [ThePrime p]
  {Γ R T C : Type} [Group Γ] [CommRing R] [Algebra ℤ_[p] R] [AddCommGroup T] [Module R T]
  [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [AddCommGroup C] [Module R C] [Module ℤ_[p] C]
  [IsScalarTower ℤ_[p] R C] [OverGp Γ p] {ρ : Representation R Γ T}

open Algebra Submodule Matrix IsScalarTower Finset Function NonarchimedeanGroup algebraMap
/-- Hodge basis over B_dR. Let `j = toGp : Γ → Gal(Q̄_p/Q_p)` have open image, and let T be
potentially crystalline with a finite ℤ_p-basis e indexed by ι. There are integers k_i and a
ℤ_p-linear automorphism N of B_dR^ι such that: (a) the k_i, with multiplicity, are the Hodge–Tate
jumps of T over ℤ_p at the inclusion ℤ_p → ℂ_p; (b) N carries the action `coordAction ρ e g` of each
g on B_dR^ι (the matrix `repMatrix ρ e g` of ρ(g) in e, with j(g) acting on the entries), read
through e, to the coordinatewise action of j(g); (c) a vector b is the image under N of a vector
with coordinates in B_dR^+ if and only if each b_i lies in the Hodge filtration step t^(−k_i)
B_dR^+; (d) for some invertible matrix W over B_dR^+, with `hodgeMatrix W k` = W·diag(t^(k_i)) and t
the period `tUnit`, the matrix of ρ(g) in e times j(g) applied to `hodgeMatrix W k` equals
`hodgeMatrix W k`, for all g.

This is a case of the existence of bases adapted to the Hodge filtration (Brinon–Conrad 6.3.7). -/
lemma IsPotentiallyCrystalline.exists_hodge_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : IsPotentiallyCrystalline ρ) (e : Module.Basis ι ℤ_[p] T) :
    ∃ (k : ι → ℤ) (N : (ι → BdR) ≃ₗ[ℤ_[p]] ι → BdR),
      -- (a)
      HasJumps (overZp ρ) (ofId ℤ_[p] ℂ_[p]) (univ.val.map k) ∧
      -- (b)
      (∀ (g : Γ) (y : ι → BdR), N (coordAction ρ e g y) = toGp g • N y) ∧
      -- (c)
      (∀ b : ι → BdR, (∃ x : ι → BdRPlus, N ((↑) ∘ x) = b) ↔ ∀ i : ι, b i ∈ hodgeFil (-k i)) ∧
      -- (d)
      ∃ W : (Matrix ι ι BdRPlus)ˣ, ∀ g : Γ,
        (repMatrix ρ e g).map (↑) * toGp g • hodgeMatrix W k = hodgeMatrix W k := by
  -- Galois descent turns periods fixed near `1` into an invertible matrix `U` of periods fixed by
  -- all of `Γ`. Its Hodge form `hodgeMatrix W k = W · diag (t ^ k i)`, with `W` invertible over
  -- `BdRPlus`, is again invariant, and `N` is the inverse of multiplication by it.
  have h_descent (v : ι → BdR) (hv : ∀ᶠ g in nearOne Γ, coordAction ρ e g v = v) :
      v ∈ span BdR {v | ∀ g, coordAction ρ e g v = v} := by
    obtain ⟨t, ht_nhds, ht_sub⟩ := Filter.mem_comap.mp hv
    -- `v` is fixed by all `g` with `toGp g` in an open subgroup `V`. Being closed, `V` is the
    -- fixer of its fixed field in `PadicAlgCl p`, over which the descent takes place.
    obtain ⟨V, hV⟩ := is_nonarchimedean t ht_nhds
    have h_semilinear (g : Γ) (a : PadicAlgCl p) (x : ι → BdR) :
        coordAction ρ e g (a • x) = (toGp g • a) • coordAction ρ e g x := by
      simp [coordAction, funext_iff, mulVec_eq_sum, mul_sum, mul_left_comm, Algebra.smul_def]
    exact span_subset_span (PadicAlgCl p) BdR _ (mem_span_fixed toGp _ h_semilinear
      (fun g hg ↦ ht_sub (hV hg)) (InfiniteGalois.fixingSubgroup_fixedField ⟨_, V.isClosed⟩).le)
  have h_span : ⊤ ≤ span BdR {v : ι → BdR | ∀ g, coordAction ρ e g v = v} := by
    refine (top_le_span_fixed (ρ := overZp ρ) e h (ofId ℤ_[p] (PadicAlgCl p))).trans
      (span_le.mpr fun v hv ↦ h_descent v ?_)
    -- The matrix of `ρ g` in `hv` (`toMatrix`) and in `coordAction` (`toMatrixAlgEquiv`) agree only
    -- by unfolding.
    simpa [comp_def, ← algebraMap_apply] using! hv
  obtain ⟨U, hU⟩ : ∃ U : GL ι BdR, ∀ (i : ι) (g : Γ),
      coordAction ρ e g ((U : Matrix ι ι BdR).col i) = (U : Matrix ι ι BdR).col i :=
    exists_GL_col_mem_of_span _ h_span
  -- The filter is `⊤`: the frame is invariant under all of `Γ`.
  obtain ⟨Y, W, k, h_frame⟩ := Period.exists_isHodgeFrame Γ le_top U.isUnit
      (Filter.eventually_top.mpr fun g ↦ ext_col fun i ↦ hU i g)
  have hW : IsUnit W := h_frame.isUnit
  have h_inv (g : Γ) : (repMatrix ρ e g).map (↑) * toGp g • hodgeMatrix W k = hodgeMatrix W k :=
    Filter.eventually_top.mp h_frame.eventually_mul_smul_eq g
  have h_unit : IsUnit (hodgeMatrix W k) := ⟨U * Y.toGL.map _, h_frame.mul_map_eq⟩
  let L : (ι → BdR) ≃ₗ[ℤ_[p]] ι → BdR := DistribMulAction.toLinearEquiv _ _ h_unit.unit
  have hL (b : ι → BdR) : L b = hodgeMatrix W k *ᵥ b := rfl
  -- Reducing `W` by `thetaBdR` gives a Hodge–Tate frame over `ℂ_[p]` of weights `k`.
  have h_jumps : HasJumps (overZp ρ) (ofId ℤ_[p] ℂ_[p]) (univ.val.map k) :=
    And.left <| hasJumps_of_rows e (.map _ hW.unit)⁻¹ k (.of_forall fun g ↦
      inv_mul_apply_of_isHodgeTateFrame (isHodgeTateFrame_of_hodgeMatrix (h_inv g)))
  -- In the frame `hodgeMatrix W k` the action is coordinatewise.
  have h_act (g : Γ) (b : ι → BdR) : coordAction ρ e g (L b) = L (toGp g • b) := by
    have h_inv_mulVec :
        ((repMatrix ρ e g).map (↑) * toGp g • hodgeMatrix W k) *ᵥ (toGp g • b) =
          hodgeMatrix W k *ᵥ (toGp g • b) := by rw [h_inv g]
    simpa [hL, funext_iff, coordAction, ← mulVec_mulVec, mulVec_apply_eq_sum, smul_sum]
      using h_inv_mulVec
  refine ⟨k, L.symm, h_jumps, ?_, ?_, hW.unit, h_inv⟩
  · -- Clause (b): it suffices to test on the vectors `L b`.
    exact fun g ↦ L.surjective.forall.mpr fun b ↦ by simp [h_act]
  · -- Clause (c). Since `W` is invertible over `BdRPlus`, the vectors over `BdRPlus` are the
    -- `W x`, and `W x = W t ^ k b` says `b i = x i * t ^ (-k i)`.
    intro b
    refine hW.smul_bijective.surjective.exists.trans ?_
    simp [L.symm_apply_eq, mem_hodgeFil, Classical.skolem, ← funext_iff,
      ← h_unit.smul_left_cancel (y := b)]
    show (∃ x : ι → BdRPlus, (fun i ↦ ((W *ᵥ x) i : BdR)) = L b) ↔
      ∃ f : ι → BdRPlus,
        (hodgeMatrix W k *ᵥ fun i ↦ (f i : BdR) * ((tUnit : BdR) ^ k i)⁻¹) = hodgeMatrix W k *ᵥ b
    simp [hL, funext_iff, hodgeMatrix, mulVec_apply_eq_sum]
    field_simp

open Filter Module LinearMap PadicInt crysCocycles

variable (a : C →ₗ[R] crysCocycles ρ) [Free ℤ_[p] T]

/-- The representation g(y, c) = (ρ(g)y + a(c)(g), c) on T × C: the extension of the trivial
module C by T given by the crystalline cocycles a(c). Here `proj g` evaluates a map Γ → T at g. -/
@[local simp]
noncomputable def extensionRep : Representation R Γ (T × C) where
  toFun g := ((ρ g).coprod (proj g ∘ₗ (crysCocycles ρ).subtype ∘ₗ a)).prod (LinearMap.snd R T C)
  map_one' := by
    have h_one (c : C) : (a c : Γ → T) 1 = 0 := by simpa using apply_mul (a c).prop 1 1
    ext <;> simp [h_one]
  map_mul' g h := by ext <;> simp [apply_mul (a _).prop, add_comm]

/-- Let `F` be a filter on `Γ`, and suppose `ρ` is admissible for `F`: the elements of `Bmax ⊗ T`
fixed by `j(g) ⊗ ρ(g)` for `F`-almost all `g` span `Bmax ⊗ T` over `Bmax`. Then the same holds, with
the same `F`, for `extensionRep a`, the representation `g(y, c) = (ρ(g) y + a(c)(g), c)` on `T × C`
given by an `R`-linear family `a` of crystalline cocycles. -/
lemma isAdmissible_extensionRep {F : Filter Γ} (h : IsAdmissible ρ F) :
    IsAdmissible (extensionRep a) F := by
  refine isAdmissible_of_one_tmul_mem_span ?_
  rintro ⟨l, x⟩
  obtain ⟨y, hy⟩ : ∃ y : TensorProduct ℤ_[p] Bmax T,
      ∀ g : Γ, 1 ⊗ₜ (a x : Γ → T) g = tensorAction Bmax (toGp g) (ρ g) y - y :=
    (a x).prop
  -- Let `i` be the equivariant inclusion of `Bmax ⊗ T` in `Bmax ⊗ (T × C)`, and `y` a period
  -- whose coboundary is `1 ⊗ a x`. Then `1 ⊗ (l, x)` is the sum of `i (1 ⊗ l + y)`, which lies in
  -- the span of the invariants because `ρ` is admissible, and an element fixed by all of `Γ`.
  have h_inl (g : Γ) (t : T) : inl ℤ_[p] T C (ρ g t) = extensionRep a g (inl ℤ_[p] T C t) := by
    simp
  let i : TensorProduct ℤ_[p] Bmax T →ₗ[Bmax] TensorProduct ℤ_[p] Bmax (T × C) :=
    periodTensorMap Bmax Bmax (inl ℤ_[p] T C)
  have h_image : i (1 ⊗ₜ l + y) ∈ span Bmax (fixedPeriods (extensionRep a) Bmax F) :=
    h.periodTensorMap_mem_span_fixedPeriods (.of_forall h_inl) _
  have h_fixed : 1 ⊗ₜ (l, x) - i (1 ⊗ₜ l + y) ∈ fixedPeriods (extensionRep a) Bmax F := by
    refine .of_forall fun g ↦ ?_
    -- `g • y = 1 ⊗ a x g + y`, and the term `a x g` cancels the one in `g • (l, x)`.
    rw [map_sub, tensorAction_periodTensorMap (g := ρ g) (h_inl g), map_add,
      ← add_eq_of_eq_sub (hy g)]
    simp [i, tensorAction, periodTensorMap, ← sub_sub, ← TensorProduct.tmul_sub]
  exact (sub_mem_iff_left _ h_image).1 (subset_span h_fixed)

omit [Module ℤ_[p] C] [IsScalarTower ℤ_[p] R C] in
/-- Let T be free over ℤ_p and finite over R, let `a` be an R-linear family of crystalline cocycles,
and let γ : R → ℂ_p be a ℤ_p-algebra map. For every integer u ≠ 0, the multiplicity
`jump (extensionRep a) γ u` of the jump u of the extension of C by T is at most `jump ρ γ u`.

This is one inequality of the additivity of Hodge–Tate weights in exact sequences. -/
lemma jump_extensionRep_le [Module.Finite R T] {γ : R →ₐ[ℤ_[p]] ℂ_[p]} {u : ℤ} (hu : u ≠ 0) :
    jump (extensionRep a) γ u ≤ jump ρ γ u := by
  -- Restriction of forms from `T × C` to `T` is injective in weight `u ≠ 0`.
  let res : hodgeTateMaps (extensionRep a) γ u →ₗ[PadicAlgCl p] hodgeTateMaps ρ γ u :=
    hodgeTateMaps.pull (inl R T C) (by simp)
  refine finrank_le_finrank_of_injective (f := res) ((injective_iff_map_eq_zero _).2 fun f hf ↦ ?_)
  ext y
  -- The map `res f` is `f` composed with `inl`, so `f` vanishes on `T`. The difference `g y - y`
  -- lies in `T`, so `f y = χ(g) ^ (-u) • g • f y` near `1`, and by Tate's theorem `f y = 0`.
  have h_vanish (t : T) : f.val (inl R T C t) = 0 :=
    LinearMap.congr_fun (congrArg Subtype.val hf) t
  have h_fix (g : Γ) : f.val (extensionRep a g y) = f.val y := by
    have h_diff : extensionRep a g y - y = inl R T C (extensionRep a g y - y).fst := by
      ext <;> simp
    rw [← sub_eq_zero, ← map_sub, h_diff, h_vanish]
  -- Near `1`, `f y` is therefore fixed by the twisted Galois action of weight `u`.
  have h_twist : ∀ᶠ g : Γ in nearOne Γ, (cyclotomicGp (toGp g) ^ (-u)).val • toGp g • f.val y =
      f.val y := (f.prop y).mono fun g hg ↦ by simpa using hg.symm.trans (h_fix g)
  exact tate_eq_zero_of_cyclotomicGp_twist (neg_ne_zero.2 hu)
    (nhds_one_le_map_nearOne Γ (h_twist.mono fun g hg ↦ by simpa using hg))

/-- Let `ρ` be a potentially crystalline representation of `Γ` on `T`, with `T` finite free over
ℤ_p, and let `c : Γ → T` lie in `crysCocycles ρ`, i.e. become a coboundary in `Bmax ⊗ T`. Then for
every `m`, `c g` lies in `p ^ m • T` for all `g` whose image under the structure map `j : Γ → Gp p`
is close enough to `1` (the filter `nearOne Γ`). -/
lemma crysCocycles.eventually_eq_pow_smul [Module.Finite ℤ_[p] T] (h : IsPotentiallyCrystalline ρ)
    {c : Γ → T} (hc : c ∈ crysCocycles ρ) (m : ℕ) :
    ∀ᶠ g : Γ in nearOne Γ, ∃ y : T, c g = p ^ m • y := by
  have e : Module.Basis (Fin (finrank ℤ_[p] T)) ℤ_[p] T := finBasis ℤ_[p] T
  have h_chi : Continuous cyclotomicGp := continuous_cyclotomicChar p
  -- `ℤ_[p]` acts on `ℂ_[p]` through `ℚ_[p]`, so the norm is multiplicative.
  have inst_normSMul : NormSMulClass ℤ_[p] ℂ_[p] := ⟨fun r ↦ norm_smul (r : ℚ_[p])⟩
  -- A Hodge–Tate frame `P` for the extension of `ℤ_[p]` by `T` defined by `c`: near `1` the matrix
  -- of `g` is `P χ(g) ^ (-k) g(P⁻¹)`, with `χ` the cyclotomic character.
  obtain ⟨P, k, h_frame, -⟩ := IsPotentiallyCrystalline.exists_isHodgeTateFrame
    (e.prod (.singleton Unit _))
    (isAdmissible_extensionRep (ρ := overZp ρ) (id.smulRight ⟨c, hc⟩) h) (ofId ℤ_[p] ℂ_[p])
  -- The entries of the last column of this product are continuous in `g : Gp p`, and those
  -- in the rows of `T` vanish at `g = 1`.
  let entry (i : Fin (finrank ℤ_[p] T)) (g : Gp p) : ℂ_[p] :=
    ∑ l, P (.inl i) l * (cyclotomicGp g ^ (-k l)).val • g • P⁻¹ l (.inr ())
  have h_small (i : Fin (finrank ℤ_[p] T)) :
      ∀ᶠ g in nhds 1, ‖entry i g‖ ≤ (p : ℝ) ^ (-m : ℤ) := by
    -- At `g = 1` the entry is the entry `(inl i, inr ())` of `P * P⁻¹ = 1`.
    have h_entry_one : entry i 1 = 0 := by
      unfold entry
      simp [← Matrix.mul_apply]
    refine Tendsto.eventually_le_const ?_ (show ContinuousAt (‖entry i ·‖) 1 by fun_prop)
    simp [h_entry_one, NeZero.pos]
  filter_upwards [h_frame, eventually_all.mpr fun i ↦ (h_small i).comap toGp] with g hg hg_small
  -- The last column of the matrix of `g` holds the coordinates of `c g`.
  have h_entry (i : Fin (finrank ℤ_[p] T)) :
      entry i (toGp g) = algebraMap ℤ_[p] ℂ_[p] (e.repr (c g) i) := by
    simp_rw [entry, ← inv_mul_apply_of_isHodgeTateFrame hg]
    simp [← Matrix.mul_apply, toMatrix_apply]
  have h_dvd (i : Fin (finrank ℤ_[p] T)) : (p : ℤ_[p]) ^ m ∣ e.repr (c g) i := by
    -- `-zpow_neg` keeps the bound in the form `p ^ (-m)` used by `norm_le_pow_iff_mem_span_pow`.
    simpa [h_entry, algebraMap_eq_smul_one, norm_smul, -_root_.zpow_neg,
      norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] using hg_small i
  choose y hy using h_dvd
  exact ⟨e.equivFun.symm y, e.ext_elem fun i ↦ by simp [hy, Finsupp.single_apply]⟩

end CocycleContinuity

/-!
## Crystalline cocycles modulo p^m: continuity and corestriction

In the main results of this section, `𝒥.toGp` is an open embedding and `T` is potentially
crystalline.
-/

section CocycleReduction

open Module Nat crysCocycles PadicInt LinearMap LE DiscreteModule Function AddSubgroup
  Topology
variable {p : ℕ} [ThePrime p]
  {Γ R T μ : Type} [Group Γ] [CommRing R] [Algebra ℤ_[p] R] [AddCommGroup T] [Module R T]
  [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [AddCommGroup μ] [𝒥 : OverGp Γ p]
  {ρ : Representation R Γ T} [Free ℤ_[p] T] [Module.Finite ℤ_[p] T] [TopologicalSpace Γ]
  [IsTopologicalGroup Γ] (hj : IsOpenEmbedding 𝒥.toGp)

variable (T) in
/-- For a natural number m, the additive subgroup p^m T of T, the image of multiplication by p^m. -/
abbrev pPowMultiples (m : ℕ) : AddSubgroup T := (lsmul ℤ_[p] T (p ^ m)).range.toAddSubgroup

/-- If T is free of rank d over ℤ_p, the subgroup p^m T has index p^(md). -/
@[simp]
lemma index_pPowMultiples (m : ℕ) : (pPowMultiples T m).index = (p ^ m) ^ finrank ℤ_[p] T := by
  -- `T / p ^ m T` is the base change of `T` to `ℤ_[p] / p ^ m`, a ring with `p ^ m` elements.
  have h_card_quot : Nat.card (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ m}) = p ^ m := by
    rw [← ker_toZModPow,
      card_congr (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective _)).toEquiv]
    simp
  rw [index_eq_card]
  -- `erw` is needed because the quotient by `pPowMultiples T m` is `QuotSMulTop` only after
  -- unfolding.
  erw [pPowMultiples, range_eq_map, card_congr (QuotSMulTop.equivQuotTensor ..).toEquiv,
    card_congr ((finBasis ..).baseChange _).equivFun.toEquiv, card_pi]
  simp [h_card_quot]

/-- The additive homomorphism from ℤ_p/p^m to the multiplicative group of Q̄_p, written additively,
that sends the class of a to ζ^a, where ζ is the primitive p^m-th root of unity chosen in
`New.rootPowHom`. -/
def zmodPowToUnits (m : ℕ) : QuotSpan (p ^ m : ℤ_[p]) →+ DiscreteUnits (PadicAlgCl p) :=
  (rootPowHom (PadicAlgCl p) (p ^ m)).val.comp
    (Ideal.Quotient.lift (Ideal.span {(p : ℤ_[p]) ^ m}) (toZModPow m)
      (by simp [← ker_toZModPow])).toAddMonoidHom

/-- An additive map `f` from a `ℤ_[p]`-module to the `p ^ n`-th roots of unity turns multiplication
by the cyclotomic character of `g` into the Galois action of `g`. -/
lemma map_cyclotomicGp_smul [Module ℤ_[p] μ] (f : μ →+ DiscreteUnits (PadicAlgCl p)) {n : ℕ}
    (h : ∀ x : μ, p ^ n • f x = 0) (x : μ) (g : Gp p) :
    f ((cyclotomicGp g).val • x) = unitsRep g (f x) := by
  -- On `p ^ n`-torsion both sides are multiplication by the cyclotomic character modulo `p ^ n`.
  calc _ = (cyclotomicCharMod (PadicAlgCl p) (p ^ n) g).1.val • f x :=
         map_cyclotomicChar_smul f n h x
    _ = unitsRep g (f x) := (cyclotomicCharMod_eq_iff_unitsRep.1 zmod_eq_natCast_val (h x)).symm

variable (h : IsPotentiallyCrystalline ρ) {S : Type} [CommRing S] {V : DiscreteModule S Γ}
  {q : T →+ V} {m : ℕ}

lemma nsmul_zmodPowToUnits (x : QuotSpan ((p : ℤ_[p]) ^ m)) : p ^ m • zmodPowToUnits m x = 0 := by
  rw [← map_nsmul, Selmer.nsmul_quot_eq_zero, map_zero]
  exact dvd_rfl

include hj h

/-- Let j: Γ → G_p be an open embedding and T potentially crystalline, finite free over ℤ_p. For an
additive map q from T to an additive group with any topology, with values killed by p^m, and x in
`crysCocycles ρ`, the map q∘x is continuous. -/
lemma crysCocycles.continuous_comp [TopologicalSpace μ] (q : T →+ μ) (hq : ∀ y : T, p ^ m • q y = 0)
    {x : Γ → T} (hx : x ∈ crysCocycles ρ) :
    Continuous (q ∘ x) := by
  -- For `u` near `1`, `p ^ m` divides `x u` (`eventually_eq_pow_smul`), so `q` kills
  -- `x (g * u) - x g = ρ g (x u)`: the function `q ∘ x` is locally constant.
  refine (isLocallyConstant_of_eventually_mul ?_).continuous
  rw [← nearOne_eq_nhds_one hj]
  filter_upwards [eventually_eq_pow_smul h hx m] with u ⟨y, hy⟩ g
  simp [apply_mul hx, hy, hq]

variable (e : ∀ (g : Γ) (x : T), q (ρ g x) = V.ρ g (q x))
  (k : q.ker = pPowMultiples T m)

include e k in
/-- For an additive map `q : T → V` that is equivariant (`e`) and has kernel `p ^ m T` (`k`), the
reduction `q ∘ c` of a crystalline cocycle `c` is a continuous cocycle of `V`. Here `𝒥.toGp` is an
open embedding (`hj`) and `T` is potentially crystalline (`h`). -/
lemma IsPotentiallyCrystalline.comp_mem_Z1 {c : Γ → T} (hc : c ∈ crysCocycles ρ) :
    q ∘ c ∈ Z1 V.ρ := by
  -- `p ^ m` kills the image of `q`, as the kernel of `q` is `p ^ m T`.
  have h_kill : ∀ y : T, p ^ m • q y = 0 := by
    simpa [le, ← map_nsmul, ← cast_smul_eq_nsmul ℤ_[p]] using k.ge
  refine ⟨crysCocycles.continuous_comp hj h q h_kill hc, ?_⟩
  -- The cocycle identity of `c`, pushed forward by the equivariant `q`.
  intro g g'
  simp [apply_mul hc, e]

/-- For an additive map q: T → V that is equivariant (`e`) and has kernel p^m T (`k`), the additive
map sending a crystalline cocycle c to the continuous cocycle q∘c in Z¹(V). Here `𝒥.toGp` is an
open embedding (`hj`) and `T` is potentially crystalline (`h`). -/
abbrev IsPotentiallyCrystalline.reducedCocycle : crysCocycles ρ →+ Z1 V.ρ :=
  AddMonoidHom.codRestrict ((q.compLeft Γ).domRestrict (crysCocycles ρ)) (Z1 V.ρ) fun ⟨_, hx⟩ ↦
    h.comp_mem_Z1 hj e k hx

/-- The kernel of `New.Period.IsPotentiallyCrystalline.reducedCocycle` is `p ^ m` times the
crystalline cocycles: a crystalline cocycle that is `p ^ m` times a function is `p ^ m` times a
crystalline cocycle. Here `ρ` is the action of `Γ` on `T`, `q : T →+ V` maps to a discrete
`Γ`-module `V` over `S`, and it is equivariant (`e`) with kernel `p ^ m T` (`k`), `hj` says that
`𝒥.toGp` is an open embedding and `h` that `T` is potentially crystalline. -/
lemma IsPotentiallyCrystalline.ker_reducedCocycle :
    (h.reducedCocycle hj e k).ker = pPowMultiples ↥(crysCocycles ρ) m := by
  ext ⟨c, hc⟩
  -- `q ∘ c = 0` says that `c` is `p ^ m` times a function `b`, which lies in `crysCocycles ρ` by
  -- saturation.
  suffices h_iff : (∃ b : Γ → T, ∀ g : Γ, (p ^ m : ℤ_[p]) • b g = c g) ↔
      ∃ b ∈ crysCocycles ρ, ∀ g : Γ, (p ^ m : ℤ_[p]) • b g = c g by
    simpa [funext_iff, ← q.mem_ker, k, Classical.skolem] using h_iff
  constructor
  · rintro ⟨b, hb⟩
    have h_smul_eq : (p ^ m : ℤ_[p]) • b = c := funext hb
    have h_smul_mem : (p ^ m : ℤ_[p]) • b ∈ crysCocycles ρ := by rwa [h_smul_eq]
    have h_ne : (p ^ m : ℤ_[p]) ≠ 0 := NeZero.out
    exact ⟨b, mem_of_smul_mem h_ne h_smul_mem, hb⟩
  · exact fun ⟨b, _, hb⟩ ↦ ⟨b, hb⟩

/-- Let `𝒥.toGp` be an open embedding, `T` potentially crystalline, `Γ` compact, `q : T → V`
equivariant and surjective with kernel `p ^ m T` and `U` an open subgroup of `Γ`. The reductions of
the crystalline cocycles of `Γ` contain all coboundaries of `V` and a corestriction of each
reduction of a crystalline cocycle of `U` (`New.DiscreteModule.HoldsCorestrictions`). -/
lemma IsPotentiallyCrystalline.holdsCorestrictions
    (q_equivariant : ∀ (g : Γ) (x : T), q (ρ g x) = V.ρ g (q x))
    (q_ker : q.ker = pPowMultiples T m) [CompactSpace Γ] (q_surj : Surjective q)
    {U : OpenSubgroup Γ} (hU : IsOpenEmbedding (toGp.comp U.subtype)) :
    V.HoldsCorestrictions U
      (reducedCocycle (𝒥 := ⟨toGp.comp U.subtype, ⟨hU.isOpen_range⟩⟩) hU (h.comp U.subtype)
        (fun g : (U : Subgroup Γ) ↦ q_equivariant g) q_ker).range
      (h.reducedCocycle hj q_equivariant q_ker).range := by
  -- `s` picks coset representatives, `1` for the trivial coset.
  obtain ⟨s, s_one, -, s_mem⟩ := exists_coset_section U
  -- A coboundary of `V` is the image of a coboundary of `T`.
  have h_cob (x : T) : V.coboundary (q x) ∈ (h.reducedCocycle hj q_equivariant q_ker).range :=
    ⟨⟨fun g : Γ ↦ ρ g x - x, coboundary_mem x⟩, by aesop⟩
  refine ⟨q_surj.forall.2 h_cob, ?_⟩
  -- Let `y = q ∘ z` on `U`, with `1 ⊗ z g = g Y - Y`. With `u x g = (s x)⁻¹ g s (g⁻¹ x) ∈ U`, the
  -- Shapiro lift of `y` is `g ↦ (x ↦ s x • y (u x g))`, and its sum over `x` is the reduction of
  -- `g ↦ ∑ x, s x • z (u x g)`, whose period is `∑ x, s x • Y`.
  rintro ⟨y, y_cont, y_coc⟩ ⟨⟨z, Y, hY⟩, hz⟩
  let := Fintype.ofFinite (Γ ⧸ (U : Subgroup Γ))
  let u (x : Γ ⧸ (U : Subgroup Γ)) (g : Γ) : (U : Subgroup Γ) :=
    ⟨(s x)⁻¹ * g * s (g⁻¹ • x), s_mem x g⟩
  refine ⟨⟨fun g x ↦ V.ρ (s x) (y (u x g)), by fun_prop, fun g g' ↦ ?_⟩, ?_,
    ⟨fun g ↦ ∑ x, ρ (s x) (z (u x g)), ∑ x, tensorAction _ (toGp (s x)) (ρ (s x)) Y, fun g ↦ ?_⟩,
    ?_⟩
  · -- It is a cocycle, as `u x (g * g') = u x g * u (g⁻¹ • x) g'`.
    have h_coc (x : Γ ⧸ (U : Subgroup Γ)) : V.ρ (s x) (y (u x g * u (g⁻¹ • x) g')) =
        V.ρ (s x) (y (u x g) + (V.restrictTo U).ρ (u x g) (y (u (g⁻¹ • x) g'))) := by
      rw [y_coc]
    simpa [u, mul_assoc, mul_smul, subgroupIncl, -ContinuousMonoidHom.coe_toMonoidHom] using!
      funext h_coc
  · -- It restricts to `y`, as `s` is `1` on the trivial coset.
    ext g
    change V.ρ _ (y (u _ g)) = _
    simp [u, s_one]
  · -- Its sum over `x` lifts to `T`, where it is the coboundary of `∑ x, s x • Y`: apply `s x` to
    -- `hY (u x g)`, sum over `x` and reindex by `x ↦ g⁻¹ • x`.
    have h_sum : ∑ x, tensorAction Bmax (toGp (s x)) (ρ (s x)) (1 ⊗ₜ[ℤ_[p]] z (u x g)) =
        ∑ x, tensorAction Bmax (toGp (s x)) (ρ (s x))
          (tensorAction Bmax (toGp (u x g : Γ)) (ρ (u x g : Γ)) Y - Y) :=
      Finset.sum_congr rfl fun x _ ↦ congrArg _ (hY (u x g))
    rw [map_sum, ← (MulAction.bijective g⁻¹).sum_comp, TensorProduct.tmul_sum]
    simpa [u, ↓tensorAction_tensorAction, ↓map_sub, tensorAction, ← map_mul, ← mul_assoc]
      using h_sum
  · -- `q` is additive and equivariant, so it maps this lift to the sum over `x`.
    cases hz
    ext
    simp [sum, q_equivariant]

end CocycleReduction

end New.Period

/-!
## Bloch–Kato cocycles: rank, finiteness and vanishing

The rank comes from the fundamental exact sequence of p-adic periods.
-/

section BlochKato
namespace New.Period

open Function Module IsScalarTower Submodule Multiset Bmax crysCocycles Algebra IsFractionRing
  LinearMap QuotientAddGroup NeZero algebraMap PadicInt Matrix
variable {p : ℕ} [ThePrime p]
  {Γ R T T' : Type} [Group Γ] [CommRing R] [Algebra ℤ_[p] R] [AddCommGroup T] [Module R T]
  [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [AddCommGroup T'] [𝒥 : OverGp Γ p]
  {ρ : Representation R Γ T} [Free ℤ_[p] T] [Module.Finite ℤ_[p] T]

/-- Rank–nullity for preimages: for a linear map e of modules over a domain and a submodule N of
the target, rk e⁻¹(N) = rk (N ∩ im e) + rk ker e. -/
lemma rank_comap_eq_add [IsDomain R] [Module R T'] {e : T →ₗ[R] T'} {N : Submodule R T'} :
    Module.rank R (N.comap e) = Module.rank R ↥(N ⊓ e.range) + Module.rank R e.ker := by
  rw [← (e.domRestrict _).rank_range_add_rank_ker, range_domRestrict, N.map_comap_eq, inf_comm,
    ker_domRestrict, (comapSubtypeEquivOfLe e.ker_le_comap).rank_eq]

/-- If the submodule A lies in B and every element of B has a nonzero multiple in A, then A and B
have the same rank. -/
lemma rank_eq_of_le_of_torsion [IsDomain R] [Module R T'] {A B : Submodule R T'} (hAB : A ≤ B)
    (h_tors : ∀ y ∈ B, ∃ t ≠ (0 : R), t • y ∈ A) :
    Module.rank R A = Module.rank R B := by
  have h_quot : Module.rank R (B ⧸ A.submoduleOf B) = 0 :=
    rank_eq_zero_iff.mpr <| (mkQ_surjective _).forall.mpr fun ⟨y, hy⟩ ↦
      (h_tors y hy).imp fun t ⟨ht, h_mem⟩ ↦ ⟨ht, (ker_mkQ _).ge h_mem⟩
  simp [← (A.submoduleOf B).rank_quotient_add_rank, h_quot, (submoduleOfEquivOfLe hAB).rank_eq]

omit [Free ℤ_[p] T] [Module.Finite ℤ_[p] T] in
/-- If the coboundary `coboundaryMap (coordAction ρ ε) x` (g ↦ g x − x, with Γ acting on
`ι → BdRPlus` through the basis `ε` of `T`) of a vector `x` over `BdRPlus` has entries in `ℚ_[p]`,
one power of `p` makes all of them integral. -/
lemma exists_pow_mul_coboundary_integral {ι : Type} [Fintype ι] [DecidableEq ι]
    {ε : Basis ι ℤ_[p] T} {x : ι → BdRPlus} {c : Γ → ι → ℚ_[p]}
    (hc : ∀ (g : Γ) (i : ι), (c g i : BdRPlus) = coboundaryMap (coordAction ρ ε) x g i) :
    ∃ s : ℕ, ∀ (g : Γ) (i : ι), ‖(p : ℚ_[p]) ^ s * c g i‖ ≤ 1 := by
  -- The map `thetaBdR` to `ℂ_[p]` bounds the entries in terms of `x` alone, as `Γ` acts by
  -- isometries and integral matrices.
  set M : ℝ := ∑ i : ι, ‖thetaBdR (x i)‖ + ‖thetaBdR ∘ x‖
  have hc_norm (g : Γ) (i : ι) : ‖c g i‖ ≤ M := by
    have h_norm : ‖c g i‖ = ‖∑ j : ι, algebraMap ℤ_[p] ℂ_[p] (repMatrix ρ ε g i j) *
        toGp g • thetaBdR (x j) - thetaBdR (x i)‖ := by
      simpa [coordAction, mulVec.eq_unfold, dotProduct] using
        congrArg (fun b : BdRPlus ↦ ‖thetaBdR b‖) (hc g i)
    unfold M
    grw [h_norm, norm_sub_le, norm_sum_le, ← norm_le_pi_norm _ i]
    gcongr
    all_goals simp [mul_le_of_le_one_left, algebraMap_apply _ ℚ_[p] ℂ_[p], norm_le_one]
  obtain ⟨s, hs⟩ : ∃ n : ℕ, M < p ^ n := pow_unbounded_of_one_lt M (p.one_lt_cast.mpr Fact.out)
  exact ⟨s, fun g i ↦ by simpa [field, pos] using (hc_norm g i).trans hs.le⟩

/-- If the crystalline cocycles have rank `n` over ℤ_p, they form a finite ℤ_p-module of finite rank
`n`: the module is separated and torsion free, so a bound on its rank gives finite generation. -/
lemma crysCocycles.finite_and_finrank_eq_of_rank_eq {n : ℕ}
    (h_rank : Module.rank ℤ_[p] (crysCocycles ρ) = n) :
    Module.Finite ℤ_[p] (crysCocycles ρ) ∧ finrank ℤ_[p] (crysCocycles ρ) = n := by
  have h_sep : IsHausdorff (IsLocalRing.maximalIdeal ℤ_[p]) (crysCocycles (overZp ρ)) :=
    isHausdorff_of_injective_pi _ _ (crysCocycles (overZp ρ)).injective_subtype
  obtain ⟨-, h_finite⟩ := free_finite_of_rank_le
    (maximalIdeal_eq_span_p.trans span_insert_zero.symm) h_sep (by simp [ne]) _ h_rank.le (by simp)
  exact ⟨h_finite, finrank_eq_of_rank_eq h_rank⟩

/-- The Frobenius `φ` of `Bmax` fixes the `p`-adic integers. -/
lemma frobEnd_algebraMap_padicInt (a : ℤ_[p]) :
    frobEnd (algebraMap ℤ_[p] Bmax a) = algebraMap ℤ_[p] Bmax a := by simp [frobEnd]

omit [Free ℤ_[p] T] [Module.Finite ℤ_[p] T] in
/-- Bounded denominators. Let `Dy : Γ → ι → Bmax` have entries fixed by `φ` that, read in `BdR`,
are the coboundary of a vector `x` over `BdRPlus`. Then one power `p ^ s` makes all entries of
`Dy` integral `p`-adic numbers. -/
lemma exists_padicInt_eq_pow_smul_of_frobEnd_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    {ε : Basis ι ℤ_[p] T} {x : ι → BdRPlus} {Dy : Γ → ι → Bmax}
    (h_fixed : ∀ (g : Γ) (i : ι), frobEnd (Dy g i) = Dy g i)
    (h_coboundary : ∀ (g : Γ) (i : ι), (Dy g i : BdR) = coboundaryMap (coordAction ρ ε) x g i) :
    ∃ s : ℕ, ∀ (g : Γ) (i : ι), ∃ t : ℤ_[p], (t : Bmax) = (p : ℤ_[p]) ^ s • Dy g i := by
  -- The entries are `p`-adic numbers `c g i`, with bounded denominators by
  -- `exists_pow_mul_coboundary_integral`.
  have h_padic (g : Γ) (i : ι) : ∃ a : ℚ_[p], (a : Bmax) = Dy g i :=
    exists_padic_eq_of_frobEnd_fixed (h_fixed g i) (h_coboundary g i)
  choose c hc using h_padic
  have hc_coboundary (g : Γ) (i : ι) : (c g i : BdRPlus) = coboundaryMap (coordAction ρ ε) x g i :=
    coe_inj.1 (.trans (by simp [← hc, ← IsScalarTower.algebraMap_apply]) (h_coboundary g i))
  obtain ⟨s, hs⟩ := exists_pow_mul_coboundary_integral hc_coboundary
  refine ⟨s, fun g i ↦ ⟨⟨p ^ s * c g i, hs g i⟩, ?_⟩⟩
  -- `(p ^ s * c g i : ℤ_[p])` and `p ^ s • c g i` agree in `Bmax` through `ℚ_[p]`. `erw` is needed
  -- because the coercion of `ℤ_[p]` into `Bmax` matches the one through `ℚ_[p]` only after
  -- unfolding.
  erw [← hc, ← algebraMap.coe_smul]
  exact algebraMap_apply ..

omit [Free ℤ_[p] T] [Module.Finite ℤ_[p] T] in
/-- The side of the coboundaries in the rank count of `New.Period.crysCocycles.finrank_eq`. In the
coordinates of a basis `ε` of `T`, let `D y = (g ↦ g y - y)` be the coboundary map on vectors over
`Bmax` and `incl` the map from functions `Γ → T` to functions `Γ → ι → Bmax`. The vectors `y` whose
coboundary `D y` comes from a function `Γ → T` form a module of rank `rk Z_f(T) + rk ker D`. -/
lemma rank_comap_coboundary_eq {ι : Type} [Fintype ι] [DecidableEq ι] (ε : Basis ι ℤ_[p] T) :
    let D : (ι → Bmax) →ₗ[ℤ_[p]] Γ → ι → Bmax := coboundaryMap (coordAction (B := Bmax) ρ ε)
    let incl : (Γ → T) →ₗ[ℤ_[p]] Γ → ι → Bmax :=
      ((Algebra.linearMap ℤ_[p] Bmax).compLeft ι ∘ₗ ε.equivFun.toLinearMap).compLeft Γ
    Module.rank ℤ_[p] (incl.range.comap D) =
      Module.rank ℤ_[p] (crysCocycles ρ) + Module.rank ℤ_[p] D.ker := by
  intro D incl
  -- `D` maps the module onto `crysCocycles ρ`, read in coordinates, with kernel `ker D`.
  have hZ : (crysCocycles ρ).restrictScalars ℤ_[p] = D.range.comap incl := by
    ext
    simp [crysCocycles, D, incl, reindex_equiv (ε.baseChange _).equivFun, ↓← equivFun_tensorAction,
      (ε.baseChange _).ext_elem_iff, eq_comm, Algebra.smul_def, funext_iff]
  rw [rank_comap_eq_add, ← D.range.map_comap_eq, ← hZ,
    rank_map_eq fun _ ↦ by simp [incl, ε.ext_elem_iff, funext_iff]]
  rfl

/-- The side of the fundamental exact sequence in the rank count of
`New.Period.crysCocycles.finrank_eq`. Let `k : ι → ℤ` and let `N` be a ℤ_p-linear automorphism of
`ι → BdR` that carries the vectors with entries in `BdRPlus` exactly onto the `b` with each `b i` in
`hodgeFil (-k i)`, as in (c) of `New.Period.IsPotentiallyCrystalline.exists_hodge_basis`; let `P` be
this image, `u` the map sending a vector over `Bmax` to `N` of its image in `ι → BdR`, and `w` the
inclusion of vectors over `K = localFieldOf Γ` into `ι → BdR`. For a ℤ_p-submodule `Z` of
`ι → Bmax`, the preimage of `Z × (range of w mod P)` under `Φ y = (φ y - y, u y mod P)`, with `φ`
the Frobenius acting entrywise, has ℤ_p-rank `rk Z + rk (K ^ d⁻) + rk (ℚ_p ^ ι)`, where `d⁻` is the
number of `i` with `k i < 0`. -/
lemma rank_comap_frob_sub_prod_eq {ι : Type} [Fintype ι] [DecidableEq ι] {k : ι → ℤ}
    {N : (ι → BdR) ≃ₗ[ℤ_[p]] ι → BdR}
    (hP : ∀ b : ι → BdR, (∃ x : ι → BdRPlus, N ((↑) ∘ x) = b) ↔ ∀ i : ι, b i ∈ hodgeFil (-k i))
    (Z : Submodule ℤ_[p] (ι → Bmax)) :
    let P : Submodule ℤ_[p] (ι → BdR) :=
      (N.toLinearMap ∘ₗ (toAlgHom ℤ_[p] BdRPlus BdR).toLinearMap.compLeft ι).range
    let u : (ι → Bmax) →ₗ[ℤ_[p]] ι → BdR :=
      N.toLinearMap ∘ₗ (toAlgHom ℤ_[p] Bmax BdR).toLinearMap.compLeft ι
    let w : (ι → localFieldOf Γ) →ₗ[ℤ_[p]] ι → BdR :=
      ((toAlgHom ℤ_[p] (PadicAlgCl p) BdR).comp
        ((localFieldOf Γ).val.restrictScalars ℤ_[p])).toLinearMap.compLeft ι
    let Φ : (ι → Bmax) →ₗ[ℤ_[p]] (ι → Bmax) × ((ι → BdR) ⧸ P) :=
      (actionRep ℤ_[p] (ι → Bmax) (.id FrobGal) ⟨.ofAdd 1, 1⟩ - 1).prod (P.mkQ ∘ₗ u)
    Module.rank ℤ_[p] ((Z.prod (P.mkQ ∘ₗ w).range).comap Φ) =
      Module.rank ℤ_[p] Z + Module.rank ℤ_[p] ({i // k i < 0} → localFieldOf Γ) +
        Module.rank ℤ_[p] (ι → ℚ_[p]) := by
  intro P u w Φ
  -- The fundamental exact sequence: `Φ` is onto with kernel `ι → ℚ_[p]`.
  have hΦ_range : Φ.range = ⊤ := by
    refine range_eq_top.2 ?_
    rintro ⟨c, ⟨b⟩⟩
    simpa [Φ, P, u, Classical.skolem, forall_and, range_comp, ↓Quotient.quot_mk_eq_mk,
      Submodule.Quotient.eq,
      N.symm_apply_eq, funext_iff] using! fun i ↦ fundamental_sequence_surjective (c i) (N.symm b i)
  have hΦ_ker : Φ.ker = ((toAlgHom ℤ_[p] ℚ_[p] Bmax).toLinearMap.compLeft ι).range := by
    ext y
    simp [Φ, P, u, range_comp, range_compLeft, ← forall_and, sub_eq_zero, funext_iff]
    refine forall_congr' fun i ↦ ⟨fun ⟨h_phi, x, hx⟩ ↦ ?_, fun ⟨c, hc⟩ ↦ ?_⟩
    · exact exists_padic_eq_of_frobEnd_fixed h_phi hx.symm
    · exact ⟨by simp [← hc], c, by simp [← hc, ← IsScalarTower.algebraMap_apply]⟩
  -- Modulo `P`, the map `w` remembers exactly the coordinates with a negative jump.
  let neg : Z × (ι → localFieldOf Γ) →ₗ[ℤ_[p]] Z × ({i // k i < 0} → localFieldOf Γ) :=
    id.prodMap (funLeft _ _ Subtype.val)
  have h_ker : (Z.subtype.prodMap (P.mkQ ∘ₗ w)).ker = neg.ker := by
    ext
    simpa [neg, P, w, coe_mem_hodgeFil_iff, funext_iff] using! fun _ ↦ hP (w _)
  have h_prod : Module.rank ℤ_[p] (Z.prod (P.mkQ ∘ₗ w).range) =
      Module.rank ℤ_[p] (Z × ({i // k i < 0} → localFieldOf Γ)) := by
    rw [← (neg.quotKerEquivOfSurjective _).rank_eq, ← h_ker, (quotKerEquivRange _).rank_eq,
      range_prodMap, Z.range_subtype]
    simp [neg, surjective_id, coe_prodMap, funLeft_surjective_of_injective]
  rw [rank_comap_eq_add, hΦ_range, inf_top_eq, hΦ_ker,
    rank_range_of_injective _ fun _ ↦ by simp [funext_iff], h_prod,
    rank_eq_of_surjective fst_surjective, ker_fst, rank_range_of_injective _ inr_injective]

/-- Bloch–Kato: for a potentially crystalline lattice `T` with Hodge–Tate jumps `J` (`hJ`: the jumps
with multiplicity of `T` over ℤ_p, `overZp ρ`, at the inclusion `ofId ℤ_[p] ℂ_[p]`), the crystalline
cocycles are finitely generated over ℤ_p of rank `d + n d⁻`. Here `d` is the rank of `T`, `n` is the
index of the image of `𝒥.toGp`, and `d⁻` is the number of negative jumps. -/
lemma crysCocycles.finrank_eq (h : IsPotentiallyCrystalline ρ) {J : Multiset ℤ}
    (hJ : HasJumps (overZp ρ) (ofId ℤ_[p] ℂ_[p]) J) :
    Module.Finite ℤ_[p] (crysCocycles ρ) ∧
      finrank ℤ_[p] (crysCocycles ρ) = finrank ℤ_[p] T + 𝒥.toGp.range.index * J.countP (· < 0) := by
  refine finite_and_finrank_eq_of_rank_eq ?_
  -- Hodge coordinates: `k` lists the jumps, `N` turns the action on `ι → BdR` into the plain Galois
  -- action (`hN`) and the vectors over `BdRPlus` into `P = ∏ hodgeFil (-k i)` (`hP`).
  let ι : Type := Fin (finrank ℤ_[p] T)
  let ε : Basis ι ℤ_[p] T := finBasis ℤ_[p] T
  obtain ⟨k, N, hk, hN, hP, -⟩ := h.exists_hodge_basis ε
  have hN_coord : ∀ (g : Γ) (y : ι → BdR) (i : ι),
      N (fun j : ι ↦ ∑ l : ι, algebraMap ℤ_[p] BdR (repMatrix ρ ε g j l) * toGp g • y l) i =
        toGp g • N y i := by
    simpa [coordAction, mulVec.eq_unfold, dotProduct, funext_iff] using hN
  let P : Submodule ℤ_[p] (ι → BdR) :=
    (N.toLinearMap ∘ₗ (toAlgHom ℤ_[p] BdRPlus BdR).toLinearMap.compLeft ι).range
  -- `D` is the coboundary map on `ι → Bmax`, `u` reads a vector in Hodge coordinates, `w` includes
  -- the vectors over `K = localFieldOf Γ`, and `Φ y = (φ y - y, u y mod P)`. We compare `A`, the
  -- `y` with `D y` over `ℤ_[p]`, with `B`, the `y` with `φ y - y` invariant and `u y` over `K`
  -- modulo `P`. They have the same rank; rk A = rk Z_f + rk ker D and rk B = rk ker D + n d⁻ + d.
  let D : (ι → Bmax) →ₗ[ℤ_[p]] Γ → ι → Bmax := coboundaryMap (coordAction (B := Bmax) ρ ε)
  let u : (ι → Bmax) →ₗ[ℤ_[p]] ι → BdR :=
    N.toLinearMap ∘ₗ (toAlgHom ℤ_[p] Bmax BdR).toLinearMap.compLeft ι
  let w : (ι → localFieldOf Γ) →ₗ[ℤ_[p]] ι → BdR :=
    ((toAlgHom _ _ BdR).comp ((localFieldOf Γ).val.restrictScalars ℤ_[p])).toLinearMap.compLeft ι
  let incl : (Γ → T) →ₗ[ℤ_[p]] Γ → ι → Bmax :=
    ((Algebra.linearMap ℤ_[p] Bmax).compLeft ι ∘ₗ ε.equivFun.toLinearMap).compLeft Γ
  let Φ : (ι → Bmax) →ₗ[ℤ_[p]] (ι → Bmax) × ((ι → BdR) ⧸ P) :=
    (actionRep ℤ_[p] (ι → Bmax) (.id FrobGal) ⟨.ofAdd 1, 1⟩ - 1).prod (P.mkQ ∘ₗ u)
  let A : Submodule ℤ_[p] (ι → Bmax) := incl.range.comap D
  let B : Submodule ℤ_[p] (ι → Bmax) := (D.ker.prod (P.mkQ ∘ₗ w).range).comap Φ
  have hu (y : ι → Bmax) (g : Γ) : u (D y g) = toGp g • u y - u y := by
    simp [D, u, LinearMap.compLeft, ← smul_algebraMap_eq_algebraMap_smul, hN_coord, comp_def,
      coordAction, mulVec.eq_unfold, dotProduct, ← IsScalarTower.algebraMap_apply, ← Pi.sub_def,
      funext_iff]
  -- A vector that is invariant modulo `∏ S i` lies over `K` modulo `∏ S i`.
  have h_fil (y : ι → Bmax) (S : ι → Submodule BdRPlus BdR)
      (hy : ∀ (g : Γ) (i : ι), u (D y g) i ∈ S i) :
      ∃ a : ι → localFieldOf Γ, ∀ i : ι, (u y - w a) i ∈ S i :=
    Classical.skolem.1 fun i ↦ BdR.exists_sub_mem_of_smul_sub_mem Γ (S i) fun g ↦ by
      simpa [hu] using hy g i
  -- `D` commutes with `φ`, so `φ y - y` is invariant iff `φ` fixes the entries of `D y`.
  have hφ (y : ι → Bmax) : frobEnd ∘ y - y ∈ D.ker ↔ (fun g ↦ frobEnd ∘ D y g) = D y := by
    -- In coordinates; `φ` fixes the entries of `repMatrix`, which lie in `ℤ_[p]`.
    simp [D, sub_eq_zero, frobEnd_algebraMap_padicInt, coordAction, funext_iff, mulVec.eq_unfold,
      dotProduct]
  have hAB : A ≤ B := by
    -- Entries in `ℤ_[p]` are fixed by `φ` and lie in `BdRPlus`, so `h_fil` applies to `y`.
    rintro y ⟨c, hc⟩
    have h_fixed : (fun g ↦ frobEnd ∘ D y g) = D y := by simp [← hc, incl, frobEnd, funext_iff]
    obtain ⟨a, ha⟩ := h_fil y _ fun g ↦ (hP _).1 ⟨fun i ↦ ε.repr (c g) i, by
      simp [← hc, incl, u, ← IsScalarTower.algebraMap_apply, funext_iff]⟩
    exact ⟨(hφ y).2 h_fixed, a, (eq_iff_sub_mem.2 ((hP _).2 ha)).symm⟩
  -- Conversely `B / A` is torsion, so `A` and `B` have the same rank.
  have h_tors (y : ι → Bmax) (hy : y ∈ B) : ∃ t ≠ (0 : ℤ_[p]), t • y ∈ A := by
    -- Write `u y = w a + N x` with `x` over `BdRPlus`. The entries of `D y` are fixed by `φ` and
    -- lie in `BdRPlus`, so they are `p`-adic numbers with bounded denominators.
    obtain ⟨hy_inv, a, ha⟩ := hy
    obtain ⟨x, hx⟩ := eq_iff_sub_mem.1 ha.symm
    have h_eq (g : Γ) : u (D y g) = N ((↑) ∘ coboundaryMap (coordAction ρ ε) x g) := by
      simpa [D, u, w, hN_coord, ← smul_algebraMap_eq_algebraMap_smul, LinearMap.compLeft,
        mem_localFieldOf.1, comp_def, coordAction, mulVec.eq_unfold, dotProduct,
        ← IsScalarTower.algebraMap_apply, ← Pi.sub_def, funext_iff, smul_sub] using
        (congrArg (fun b : ι → BdR ↦ toGp g • b - b) hx).symm
    have hD (g : Γ) (i : ι) : (D y g i : BdR) = coboundaryMap (coordAction ρ ε) x g i :=
      congrFun (N.injective (h_eq g)) i
    have h_fixed (g : Γ) (i : ι) : frobEnd (D y g i) = D y g i :=
      congrFun (congrFun ((hφ y).1 hy_inv) g) i
    obtain ⟨s, h_int⟩ := exists_padicInt_eq_pow_smul_of_frobEnd_eq h_fixed hD
    exact ⟨p ^ s, NeZero.ne _, by simpa [A, incl, range_compLeft, ↓map_smul] using h_int⟩
  -- `A` contains `D.ker`, and its image under `D` is `crysCocycles ρ` in coordinates.
  have h_rank_A : Module.rank ℤ_[p] A =
      Module.rank ℤ_[p] (crysCocycles ρ) + Module.rank ℤ_[p] D.ker := rank_comap_coboundary_eq ε
  -- `B` is a preimage under `Φ`, whose rank the fundamental exact sequence gives.
  have h_rank_B : Module.rank ℤ_[p] B = Module.rank ℤ_[p] D.ker +
      Module.rank ℤ_[p] ({i // k i < 0} → localFieldOf Γ) + Module.rank ℤ_[p] (ι → ℚ_[p]) :=
    rank_comap_frob_sub_prod_eq hP D.ker
  -- The invariants `D.ker` embed in the image of `w`; their rank is finite and cancels.
  have h_fin : Module.rank ℤ_[p] D.ker < Cardinal.aleph0 := by
    have h_le : D.ker.map u ≤ w.range := by
      rintro _ ⟨y, hy : D y = 0, rfl⟩
      obtain ⟨a, ha⟩ := h_fil y ⊥ (by simp [hy])
      exact ⟨a, funext fun i ↦ (sub_eq_zero.1 (ha i)).symm⟩
    grw [← rank_map_eq (f := u) fun _ ↦ by simp [u, funext_iff],
      (rank_mono h_le).trans (rank_range_le w), ← rank_right_eq _ ℚ_[p], rank_lt_aleph0]
  have hJ_eq : J = Finset.univ.val.map k := ext' fun u ↦ (hJ u).symm.trans (hk u)
  refine Cardinal.eq_of_add_eq_add_right ?_ h_fin
  rw [← h_rank_A, rank_eq_of_le_of_torsion hAB h_tors, h_rank_B]
  -- `localFieldOf Γ` has degree `n = toGp.range.index` over `ℚ_[p]`, and `d⁻` jumps are negative.
  simp [-Fin.univ_val_map, hJ_eq, ι, countP_map, ← rank_right_eq _ ℚ_[p], finrank_fixedFieldOf,
    ← finrank_eq_rank, Fintype.card_subtype, Module.finrank_pi_fintype]
  ring!

/-- If j: Γ → G_p is a homomorphism with open image and the R[Γ]-module T is finite free over
Z_p and potentially crystalline, then the R-module Z_f(T) of crystalline cocycles is
finitely generated. -/
lemma crysCocycles.fg (h : IsPotentiallyCrystalline ρ) : Module.Finite R (crysCocycles ρ) := by
  obtain ⟨J, -, hJ⟩ := IsPotentiallyCrystalline.exists_hasJumps (ρ := overZp ρ) h (ofId ℤ_[p] ℂ_[p])
  exact (finrank_eq h hJ).1.of_restrictScalars_finite ℤ_[p] R (crysCocycles ρ)

/-- If `ρ` is potentially crystalline and all Hodge–Tate jumps of `ρ` (read over ℤ_p) are positive,
a crystalline cocycle `c` is torsion modulo coboundaries: there are `t ≠ 0` in ℤ_p and `x` in `T`
with `ρ g x - x = t • c g` for all `g`. -/
lemma IsPotentiallyCrystalline.exists_coboundary_eq_smul (h : IsPotentiallyCrystalline ρ)
    (h_pos : ∀ u : ℤ, jump (overZp ρ) (ofId ℤ_[p] ℂ_[p]) u ≠ 0 → 0 < u) {c : Γ → T}
    (hc : c ∈ crysCocycles ρ) :
    ∃ t ≠ (0 : ℤ_[p]), ∃ x : T, (fun g : Γ ↦ ρ g x - x) = t • c := by
  -- There are no negative jumps, so `crysCocycles ρ` has the rank of `T`. The coboundary map `d` is
  -- injective, so its image has the same rank and the quotient is torsion.
  change IsPotentiallyCrystalline (overZp ρ) at h
  obtain ⟨J, -, hJ⟩ := h.exists_hasJumps (ofId ℤ_[p] ℂ_[p])
  obtain ⟨h_fin, h_rank⟩ := finrank_eq h hJ
  have h_nonneg : J.countP (· < 0) = 0 := by simp_all [HasJumps, countP_eq_zero, le_of_lt]
  let d : T →ₗ[ℤ_[p]] crysCocycles (overZp ρ) :=
    (coboundaryMap (overZp ρ)).codRestrict _ coboundary_mem
  have hd : Injective d := by
    refine (injective_iff_map_eq_zero d).2 fun x hx ↦ ?_
    by_contra hx_ne
    -- A nonzero invariant `x` embeds the trivial representation: its jump `0` violates `h_pos`.
    have h_jump : ∃ _ : Unit, jump (overZp ρ) (ofId ℤ_[p] ℂ_[p]) 0 ≠ 0 :=
      exists_jump_of_jointly_injective (fun _ ↦ h) (ρ := 1) (γ := ofId ..) (u := 0)
        (fun () ↦ toSpanSingleton _ _ x) ?_ ?_ ?_
    · exact h_jump.elim fun _ h_jump_zero ↦ (h_pos 0 h_jump_zero).false
    · -- `x` is invariant, so `a ↦ a • x` is equivariant from the trivial representation
      simp_all [d, coboundaryMap, Subtype.ext_iff, funext_iff, sub_eq_zero]
    · -- `T` is torsion free and `x ≠ 0`
      aesop
    · -- the trivial representation has the jump `0`
      simp [hasJumps_of_cyclotomicGp_zpow 0 ..]
  have h_quot : finrank ℤ_[p] (crysCocycles (overZp ρ) ⧸ d.range) = 0 := by
    simp [finrank_quotient, finrank_range_of_inj hd, h_rank, h_nonneg]
  -- The quotient by the image of `d` has rank `0`, so the class of `c` is torsion.
  have h_torsion : ∃ t ≠ (0 : ℤ_[p]), t • d.range.mkQ ⟨c, hc⟩ = 0 :=
    finrank_eq_zero_iff.1 h_quot (d.range.mkQ ⟨c, hc⟩)
  simpa [← Quotient.mk_smul, Subtype.ext_iff] using! h_torsion

/-- Let Γ act on T, finite free over ℤ_p, through χ^(−a) with a ≥ 0, where χ is the cyclotomic
character of Γ. A crystalline cocycle vanishes at every s with ρ(s) = 1, provided that, when a = 0,
j(s) = `toGp s` lies in inertia (`IsWeilPair (toGp s) 0`).

This is a consequence, on cocycles, of the Bloch–Kato computation of H¹_f of Tate twists. -/
lemma crysCocycles.apply_eq_zero_of_cyclotomicGp {a : ℕ}
    (h_twist : ∀ (g : Γ) (x : T), ρ g x = (χ g ^ (-a : ℤ)).val • x) {c : Γ → T}
    (hc : c ∈ crysCocycles ρ) {s : Γ} (hρs : ρ s = 1)
    (hs_mem_inertia : a = 0 → IsWeilPair (toGp s) 0) :
    c s = 0 := by
  rcases a with _ | a
  · -- Trivial action: test against a linear form `l`; then `l (c g) = g y - y` for a period `y`.
    refine (forall_dual_apply_eq_zero_iff ℤ_[p] _).1 fun l ↦ ?_
    have h_l_equivariant (g : Γ) (x : T) :
        l (ρ g x) = Representation.trivial ℤ_[p] Γ ℤ_[p] g (l x) := by simp [h_twist]
    obtain ⟨y, hy⟩ : ∃ y : Bmax, ∀ g : Γ, algebraMap ℤ_[p] _ (l (c g)) + y = toGp g • y := by
      simpa [reindex_equiv (TensorProduct.rid ..).symm, tensorAction, crysCocycles,
        ← (TensorProduct.rid ..).apply_eq_iff_eq, Algebra.smul_def, eq_sub_iff_add_eq] using
        comp_mem hc (σ := .trivial ℤ_[p] ..) l h_l_equivariant
    -- `φ y - y` is invariant, so `p ^ n` times it is a Witt vector `w` over the field with `p ^ f`
    -- elements, and `w = φ x - x` has a solution `x` in `Ainf`.
    have h_inv (g : Γ) : toGp g • (frobEnd y - y) = frobEnd y - y := by
      simp [← hy, smul_sub, frobEnd_algebraMap_padicInt]
    obtain ⟨f, n, w, hw⟩ := exists_witt_ratio (a := frobEnd y - y) (ne 1)
      (nhds_one_le_map_nearOne Γ (by simp [h_inv]))
    obtain ⟨x, hx⟩ := Ainf.exists_frobEnd_sub_xi_pow_mul_eq 0 w
    -- `y` is invariant modulo `BdRPlus`, so `y = z + b` with `z` in `BdRPlus` and `b` algebraic.
    obtain ⟨b, z, hz⟩ : ∃ (b : PadicAlgCl p) (z : BdRPlus), (y : BdR) = z + b := by
      obtain ⟨b, z, hz⟩ := BdR.exists_sub_mem_of_smul_sub_mem Γ 1 (x := y) fun g ↦
        ⟨l (c g), by simp [← hy, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]⟩
      exact ⟨b, z, eq_add_of_sub_eq (by simpa [eq_comm, Algebra.smul_def] using hz)⟩
    -- Thus `p ^ n * y - x` is fixed by `φ` and lies in `BdRPlus`: it is a `p`-adic number `r`.
    have h_phi : frobEnd (p ^ n * y - x : Bmax) = p ^ n * y - x := by
      suffices (p ^ n * frobEnd y : Bmax) - ↑(frobEnd x) + x = p ^ n * y by
        simpa [eq_sub_iff_add_eq]
      grind
    obtain ⟨r, hr⟩ : ∃ r : ℚ_[p], (r : Bmax) = p ^ n * y - x :=
      exists_padic_eq_of_frobEnd_fixed h_phi (x := p ^ n * (z + b) - x)
        (by simp [hz, ← IsScalarTower.algebraMap_apply])
    -- As `toGp s` fixes `r`, it moves `x` by `p ^ n * l (c s)`, in `Bmax` and so in `Ainf`.
    have h_move : ↑(p ^ n * l (c s)) + x = toGp s • x := by
      refine (algebraMap.coe_inj ..).1 (injective_BPlus_Bmax ?_)
      have h_r_moved :
          toGp s • (p ^ n * y - x : Bmax) - (p ^ n * y - x) = toGp s • (r : Bmax) - r := by rw [hr]
      simpa [← hy, mul_add, sub_sub_sub_comm, smul_sub, sub_eq_zero, eq_sub_iff_add_eq,
        ← IsScalarTower.algebraMap_apply] using h_r_moved
    -- Inertia acts trivially after reduction to the Witt vectors of the residue field.
    have h_residue : toWittResidue (↑(p ^ n * l (c s)) + x) = toWittResidue x :=
      (congrArg _ h_move).trans (toWittResidue_smul_of_isFrob (hs_mem_inertia rfl) x)
    simpa [-map_mul, ne] using h_residue
  · -- Every jump equals `a + 1 > 0`, so some `t • c` is a coboundary, which vanishes at `s`.
    have h_pos : ∀ u : ℤ, jump (overZp ρ) (ofId ℤ_[p] ℂ_[p]) u ≠ 0 → 0 < u := by
      simp [mem_replicate, hasJumps_of_cyclotomicGp_zpow (ρ := overZp ρ) _ h_twist _]
    obtain ⟨t, ht, x, hx⟩ := IsPotentiallyCrystalline.exists_coboundary_eq_smul
      (isAdmissible_of_cyclotomicGp_zpow _ h_twist) h_pos hc
    simpa [hρs, ht] using (congrFun hx s).symm

end New.Period

end BlochKato

end
