import Lib.Base

/-!
# Level spaces, Hecke operators, stabilisers and class sums

For an abstract group `G` with subgroups `Γ`, `K`, `H` and a representation `π` over a commutative
semiring, this file defines the level space of `K`, Hecke operators and weighted class sums over
`Γ \ G / K`. The Hecke operator `New.heckeFun π K f = ∑ f(g) π(g)` sums over chosen representatives
`g` of `G ⧸ K` and is applied to vectors fixed by `K`. When `f (g * k) = f g` for `k ∈ K` and `v` is
such a vector, the term `f g • π g v` depends only on the coset `g K`. The file proves that, under
this condition, the value at `v` does not depend on the choice of representatives.

## Main definitions and results

* `New.levelSpace`: the vectors on which `K` acts through a character `χ`.
* `New.heckeFun`, `New.heckeCoset`: the operator `∑ f(g) π(g)` over chosen representatives of
  `G / K`, and its value on the indicator function of a double coset `K g K`.
* `New.classAut`, `New.classSum`: the stabiliser `Γ ∩ g K g⁻¹`, and the sum over `Γ \ G / K`
  weighted by the inverse orders of the stabilisers.
* `New.relIndex_mul_measure_inf`, `New.measure_inter_eq_inv_relIndex`: for `K` compact and `H` open,
  the volume of `H ∩ K` times the index `[K : H ∩ K]` is the volume of `K`.
* `New.heckeFun_eq_sum`, `New.heckeFun_eq_sum_pullback`: on a vector fixed by `K`, the sum over any
  other system of representatives.
* `New.heckeFun_heckeFun`: on a vector fixed by `K`, the composite of two operators is the operator
  of a convolution.

## Relation to the literature

Known; see `Lib.Adelic.Hecke.ClassSums` for sources.
-/

noncomputable section

namespace New

/-!
## Level spaces, Hecke operators, class sums and volumes

The sums are Mathlib's `finsum`, which is zero when the support is infinite. Since `Nat.card` of an
infinite group is zero, a class with infinite stabiliser has weight zero.
-/

section HeckeDefs

open DoubleCoset MeasureTheory Subgroup IsLocallyConstant

variable (A G W : Type*) [Group G] [CommSemiring A] [AddCommMonoid W] [Module A W]

/-- A representation in `Rep A G` may be applied to a group element as a function. -/
scoped instance : CoeFun (Rep A G) (G → Module.End A ·) := ⟨(·.ρ)⟩

/-- The right regular representation of G on functions G → W: (g·F)(x) = F(xg). -/
@[simps! apply_apply]
def rightRegular : Representation A G (G → W) where
  toFun g := LinearMap.funLeft A W fun x ↦ x * g
  map_one' := LinearMap.ext fun F ↦ funext fun x ↦ by simp
  map_mul' g h := LinearMap.ext fun F ↦ funext fun x ↦ by simp [mul_assoc]

variable {A G W} (π : Representation A G W) (Γ K H : Subgroup G)

/-- For a representation π of G, a subgroup K and a character χ of K, the submodule of vectors v
with π(k)v = χ(k)v for all k in K. -/
def levelSpace (χ : K →* A := 1) : Submodule A W where
  carrier := {v : W | ∀ k : K, π k v = χ k • v}
  add_mem' hv hw k := by rw [map_add, hv k, hw k, smul_add]
  zero_mem' k := by rw [map_zero, smul_zero]
  smul_mem' a v hv k := by rw [map_smul, hv k, smul_comm]

/-- For a function f on G, the operator ∑ f(g)π(g), summed over chosen representatives g of G/K
(zero if infinitely many terms are nonzero). Let f be right K-invariant and supported on finitely
many cosets gK. On a vector fixed by K the value does not depend on the representatives
(`New.heckeFun_eq_sum`), and it is the action of f for the measure with vol K = 1. -/
def heckeFun (f : G → A) : Module.End A W := ∑ᶠ q : G ⧸ K, f q.out • π q.out

/-- The Hecke operator of the double coset KgK: the sum of π(h) over chosen representatives h of
the cosets hK in KgK (zero if there are infinitely many). -/
def heckeCoset (g : G) : Module.End A W := heckeFun π K ((doubleCoset g K K).indicator 1)

/-- The subgroup Γ ∩ gKg⁻¹, the stabiliser in Γ of the coset gK. -/
def classAut (g : G) : Subgroup G := Γ ⊓ K.comap (MulAut.conj g⁻¹).toMonoidHom

/-- The set Γ\G/K of double cosets of a group G with respect to subgroups Γ and K. -/
abbrev DoubleCosets : Type _ := DoubleCoset.Quotient (Γ : Set G) K

variable {π Γ K H} {Δ : Type*} [Group Δ]

@[simp]
lemma mem_levelSpace {χ : K →* A} {v : W} : v ∈ levelSpace π K χ ↔ ∀ k : K, π k v = χ k • v :=
  .rfl

/-- If `π k v = χ k • v` for all `k ∈ K` and the linear map `a` commutes with every `π k`, then
`a v` satisfies the same equations: it lies in the level space of `(K, χ)`. -/
lemma map_mem_levelSpace_of_commute {χ : K →* A} {v : W} {a : W →ₗ[A] W}
    (hv : v ∈ levelSpace π K χ) (h_comm : ∀ k : K, Commute (π k) a) :
    a v ∈ levelSpace π K χ := by
  intro k
  rw [show π k (a v) = a (π k v) from LinearMap.congr_fun (h_comm k).eq v, hv k, map_smul]

@[simp]
lemma mem_classAut {g γ : G} : γ ∈ classAut Γ K g ↔ γ ∈ Γ ∧ g⁻¹ * γ * g ∈ K := by simp [classAut]

/-- If `r` is a system of representatives of the double cosets `e(Δ) \ G / K`, every `g` is
`e γ * r c * k` with `γ ∈ Δ`, `c` a double coset and `k ∈ K`. -/
lemma exists_eq_map_mul_rep_mul (e : Δ →* G) (K : Subgroup G)
    {r : DoubleCoset.Quotient (e.range : Set G) K → G}
    (hr : ∀ c : DoubleCoset.Quotient (e.range : Set G) (K : Set G),
      DoubleCoset.mk e.range K (r c) = c) (g : G) :
    ∃ (c : DoubleCoset.Quotient (e.range : Set G) (K : Set G)) (γ : Δ), ∃ k : K,
      g = e γ * r c * k := by
  -- `g` and the representative of its class lie in the same double coset
  obtain ⟨_, ⟨γ, rfl⟩, k, hk, hg⟩ := DoubleCoset.eq.1 (hr ⟦g⟧)
  exact ⟨⟦g⟧, γ, ⟨k, hk⟩, hg⟩

/-- Let e : Δ → G be a homomorphism and r a system of representatives of e(Δ)\G/K, and let Δ act
freely at the point r(d)K of G/K. Then e(γ) r(d)K = r(c)K only for c = d and γ = 1. -/
lemma eq_and_eq_one_of_doubleCoset_rep {e : Δ →* G}
    {r : DoubleCoset.Quotient (e.range : Set G) K → G}
    (hr : ∀ c : DoubleCoset.Quotient (e.range : Set G) (K : Set G),
      DoubleCoset.mk e.range K (r c) = c)
    {c d : DoubleCoset.Quotient (e.range : Set G) (K : Set G)}
    (h_free : ∀ γ : Δ, (r d)⁻¹ * e γ * r d ∈ K → γ = 1) (γ : Δ) (hγ : (r c)⁻¹ * e γ * r d ∈ K) :
    c = d ∧ γ = 1 := by
  -- `r c` lies in the double coset of `r d`, so `c = d`; then freeness gives `γ = 1`.
  have h_same : mk e.range K (r d) = mk e.range K (r c) :=
    DoubleCoset.eq.2 ⟨e γ, ⟨γ, rfl⟩, _, inv_mem hγ, by group⟩
  obtain rfl : c = d := by rw [← hr c, ← h_same, hr d]
  exact ⟨rfl, h_free γ hγ⟩

/-- The class sum of f: the sum over the double cosets c in Γ\G/K of f(g_c)/#(Γ ∩ g_c K g_c⁻¹), g_c
a chosen representative. For f left invariant under Γ and right invariant under K the choice of
representatives does not matter (`New.classSum_eq_finsum_of_rep`). -/
def classSum [Module ℚ W] (Γ K : Subgroup G) (f : G → W) : W :=
  ∑ᶠ c : DoubleCoset.Quotient (Γ : Set G) K, (Nat.card (classAut Γ K c.out) : ℚ)⁻¹ • f c.out

/-- The order of the stabiliser Γ ∩ gKg⁻¹ depends only on the double coset ΓgK. -/
lemma card_classAut_mul_mul {γ k : G} (hγ : γ ∈ Γ) (hk : k ∈ K) (g : G) :
    Nat.card (classAut Γ K (γ * g * k)) = Nat.card (classAut Γ K g) := by
  -- Conjugation `δ ↦ γ⁻¹ * δ * γ` carries the first stabiliser onto the second.
  refine Nat.card_congr ((MulAut.conj γ⁻¹).toEquiv.subtypeEquiv fun δ ↦ ?_)
  change δ ∈ classAut Γ K (γ * g * k) ↔ γ⁻¹ * δ * γ⁻¹⁻¹ ∈ classAut Γ K g
  have h_left : γ⁻¹ * δ * γ ∈ Γ ↔ δ ∈ Γ := by
    rw [mul_mem_cancel_right hγ, mul_mem_cancel_left (inv_mem hγ)]
  have h_conj : (γ * g * k)⁻¹ * δ * (γ * g * k) = k⁻¹ * (g⁻¹ * (γ⁻¹ * δ * γ) * g) * k := by group
  rw [inv_inv, mem_classAut, mem_classAut, h_left, h_conj, mul_mem_cancel_right hk,
    mul_mem_cancel_left (inv_mem hk)]

/-- For f left invariant under Γ and right invariant under K, the class sum can be computed with
any system of representatives r of Γ\G/K. -/
lemma classSum_eq_finsum_of_rep [Module ℚ W] {f : G → W}
    (hf_left : ∀ γ ∈ Γ, ∀ g : G, f (γ * g) = f g) (hf_right : ∀ k ∈ K, ∀ g : G, f (g * k) = f g)
    {r : DoubleCoset.Quotient (Γ : Set G) K → G}
    (hr : ∀ c : DoubleCoset.Quotient (Γ : Set G) K, DoubleCoset.mk Γ K (r c) = c) :
    classSum Γ K f = ∑ᶠ c : DoubleCoset.Quotient (Γ : Set G) K,
      (Nat.card (classAut Γ K (r c)) : ℚ)⁻¹ • f (r c) := by
  refine finsum_congr fun c ↦ ?_
  -- The chosen representative of `c` lies in the double coset of `r c`.
  obtain ⟨γ, hγ, k, hk, h_out⟩ : ∃ γ ∈ Γ, ∃ k ∈ K, c.out = γ * r c * k :=
    (DoubleCoset.eq ..).1 (by rw [hr c, out_eq'])
  rw [h_out, card_classAut_mul_mul hγ hk, hf_right k hk, hf_left γ hγ]

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### Open and compact subgroups of a topological group -/

/-- A function on a topological group that is invariant under right translation by all elements
of a neighbourhood of 1 is locally constant. -/
@[to_additive]
lemma isLocallyConstant_of_eventually_mul {X : Type*} {f : G → X}
    (h_fix : ∀ᶠ k : G in nhds 1, ∀ x : G, f (x * k) = f x) :
    IsLocallyConstant f :=
  -- The neighbourhoods of `x` are the left translates by `x` of those of `1`.
  (iff_eventually_eq f).2 fun x ↦ by
    rw [← map_mul_left_nhds_one x, Filter.eventually_map]
    filter_upwards [h_fix] with k hk using hk x

/-- For an open subgroup `H` of a topological group `G`, a compact subset `C` of `G` meets only
finitely many cosets `g H`. -/
lemma finite_quotient_image_of_isCompact (hH : IsOpen (H : Set G)) {C : Set G} (hC : IsCompact C) :
    ((↑) '' C : Set (G ⧸ H)).Finite := by
  have : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  exact (hC.image continuous_quotient_mk').finite_of_discrete

/-- For a compact subgroup `K` and an open subgroup `H` of a topological group, the index
`[K : H ∩ K]` is finite, so it is nonzero as a natural number. -/
@[to_additive relIndex_ne_zero_add]
lemma _root_.IsCompact.relIndex_ne_zero (hK : IsCompact (K : Set G))
    (hH : IsOpen (H : Set G)) : H.relIndex K ≠ 0 := by
  -- An open subgroup of a compact group has finite index.
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  exact (quotient_finite_of_isOpen (H.subgroupOf K) hH.preimage_val).card_pos.ne'

/-- For `K` compact, `H` open and `μ` left invariant, `[K : H ∩ K] · μ (H ∩ K) = μ K`. -/
@[to_additive]
lemma relIndex_mul_measure_inf (hK : IsCompact (K : Set G)) (hH : IsOpen (H : Set G))
    [MeasurableSpace G] [BorelSpace G] [T2Space G] (μ : Measure G) [μ.IsMulLeftInvariant] :
    H.relIndex K * μ ↑(H ⊓ K) = μ K := by
  -- Pull `μ` back to the group `K`; there `H ⊓ K` is a measurable subgroup of finite index,
  -- and its cosets, all of the same measure, partition `K`.
  have h_emb : MeasurableEmbedding K.subtype := .subtype_coe hK.measurableSet
  have : (H.subgroupOf K).FiniteIndex := ⟨hK.relIndex_ne_zero hH⟩
  have : (μ.comap K.subtype).IsMulLeftInvariant := .comap _ h_emb
  have h_index :
      (H.subgroupOf K).index * μ.comap K.subtype (H.subgroupOf K) = μ.comap K.subtype Set.univ :=
    index_mul_measure _ (h_emb.measurable hH.measurableSet) _
  -- Push the identity forward: `μ.comap` of a subset of `K` is `μ` of its image in `G`.
  have h_image : K.subtype '' (H.subgroupOf K) = ↑(H ⊓ K) := by
    rw [← coe_map, subgroupOf_map_subtype]
  rwa [h_emb.comap_apply, h_emb.comap_apply, h_image, Set.image_univ, coe_subtype,
    Subtype.range_coe] at h_index

/-- For `K` compact of mass one, `H` open and `μ` left invariant, `H ∩ K` has mass
`1 / [K : H ∩ K]`. -/
@[to_additive measure_inter_eq_inv_relIndex_add]
lemma measure_inter_eq_inv_relIndex (hK : IsCompact (K : Set G)) (hH : IsOpen (H : Set G))
    [MeasurableSpace G] [BorelSpace G] [T2Space G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (hμ : μ K = 1) : μ (H ∩ K) = (↑(H.relIndex K))⁻¹ := by
  have h_mul : H.relIndex K * μ ↑(H ⊓ K) = 1 := (relIndex_mul_measure_inf hK hH μ).trans hμ
  simp [ENNReal.eq_inv_of_mul_eq_one_left h_mul]

end HeckeDefs

/-!
## Coset sums, transport and composition of Hecke operators

* `New.heckeFun_comp`, `New.heckeFun_comp_inv_mul`: transport of `New.heckeFun` along a group
  homomorphism, and its behaviour under left translation.
* `New.heckeFun_mem_levelSpace`: when the image under an operator lies in a level space.
-/

section HeckeBasic

open Set Function HasFiniteSupport DoubleCoset QuotientGroup Finset

variable {A : Type*}
  {G W W' : Type*} [Group G] [CommSemiring A] [AddCommMonoid W] [Module A W] [AddCommMonoid W']
  [Module A W'] {π : Representation A G W} (K K' : Subgroup G) {χ' : K' →* A} (f : G → A) {v : W}
  {G' : Type*} [Group G']

/-- The function f on G is nonzero at the chosen representatives of only finitely many cosets
gK. -/
abbrev HasFiniteCosets : Prop := (support fun q : G ⧸ K ↦ f q.out).Finite

/-- The function f on G is left and right K-invariant and supported on finitely many cosets gK. -/
abbrev IsHeckeFunction : Prop :=
  HasFiniteCosets K f ∧ ∀ᵉ (g : G) (k ∈ K), f (g * k) = f g ∧ f (k * g) = f g

variable {K K' f}

/-- If `f` lives on finitely many cosets, its operator is the finite sum over those cosets. -/
lemma heckeFun_eq_sum_toFinset (h : HasFiniteCosets K f) (v : W) :
    heckeFun π K f v = ∑ q ∈ h.toFinset, f q.out • π q.out v := by
  have h_support : support (fun q : G ⧸ K ↦ f q.out • π q.out) ⊆ h.toFinset :=
    fun q hq ↦ by simpa using left_ne_zero_of_smul hq
  simp [heckeFun, finsum_eq_sum_of_support_subset _ h_support]

/-- Let `f` live on finitely many cosets `g K`. A linear map `L` that intertwines `π g` and `π' g`
at `v` for all `g` intertwines the two operators of `f` at `v`. -/
lemma map_heckeFun (L : W →ₗ[A] W') (h : HasFiniteCosets K f)
    {π' : Representation A G W'} (hL : ∀ g : G, L (π g v) = π' g (L v)) :
    L (heckeFun π K f v) = heckeFun π' K f (L v) := by simp [heckeFun_eq_sum_toFinset h, hL]

lemma levelSpace_anti (hK : K ≤ K') : levelSpace π K' ≤ levelSpace π K :=
  fun v hv k ↦ by simpa using hv ⟨k, hK k.2⟩

/-- For a compact open subgroup K of a topological group G and g in G, the indicator function of KgK
is K-invariant on both sides and supported on finitely many left cosets of K. -/
lemma isHeckeFunction_doubleCoset [TopologicalSpace G] [IsTopologicalGroup G]
    (hK : IsOpen (K : Set G)) [CompactSpace K] (g : G) :
    IsHeckeFunction K (indicator (doubleCoset g K K) (1 : G → A)) := by
  classical
  have hK_compact : IsCompact (K : Set G) := isCompact_iff_compactSpace.2 inferInstance
  have h_compact : IsCompact (doubleCoset g K K) :=
    (hK_compact.mul isCompact_singleton).mul hK_compact
  refine ⟨(finite_quotient_image_of_isCompact hK h_compact).subset fun q hq ↦ ?_,
    fun x k hk ↦ ⟨?_, ?_⟩⟩
  · exact ⟨q.out, support_indicator_subset hq, q.out_eq⟩
  · -- `x * k` and `x` lie in the double coset together: absorb `k` in the right factor
    simp [← inv_mul_eq_iff_eq_mul, mul_mem_cancel_right hk, indicator, mem_doubleCoset, ← mul_assoc]
  · -- likewise with the left factor
    simp [← mul_inv_eq_iff_eq_mul, mul_assoc, mul_mem_cancel_left hk, indicator, mem_doubleCoset]

/-- Any representatives serve. Let `f (g * k) = f g` for `k ∈ K`, and let `v` be fixed by `K`.
Suppose the cosets `r i • K`, `i ∈ s`, are distinct and cover the support of `f`. Then (a) `f` lives
on finitely many cosets, and (b) its operator sends `v` to `∑ i ∈ s, f (r i) • π (r i) v`. -/
lemma heckeFun_eq_sum (hf : ∀ (g : G) (k : K), f (g * k) = f g)
    (hv : v ∈ levelSpace (A := A) π K) {ι : Type*} {s : Finset ι} {r : ι → G}
    (hr : InjOn (fun i : ι ↦ (r i : G ⧸ K)) (SetLike.coe s))
    (hs : ∀ g : G, f g ≠ 0 → ∃ i ∈ s, (r i : G ⧸ K) = g) :
    HasFiniteCosets K f ∧ heckeFun π K f v = ∑ i ∈ s, f (r i) • π (r i) v := by
  classical
  have support_subset (q : G ⧸ K) (hq : f q.out ≠ 0) : q ∈ s.image fun i ↦ (r i : G ⧸ K) := by
    simpa using hs _ hq
  refine ⟨(toFinite _).subset support_subset, ?_⟩
  -- The chosen representative of `g K` is some `g * k`, and `k` does not change `f g • π g v`.
  have term (g : G) : f (g : G ⧸ K).out • π (g : G ⧸ K).out v = f g • π g v := by
    obtain ⟨k, hk⟩ := mk_out_eq_mul K g
    rw [hk, hf, map_mul, Module.End.mul_apply, mem_levelSpace.1 hv k, MonoidHom.one_apply, one_smul]
  have h_support : support (fun q : G ⧸ K ↦ f q.out • π q.out) ⊆
      s.image fun i ↦ (r i : G ⧸ K) :=
    fun q hq ↦ support_subset q (left_ne_zero_of_smul hq)
  simp [heckeFun, finsum_eq_sum_of_support_subset _ h_support, sum_image hr, term]

/-- Let f(gk) = f(g) for k ∈ K, let v be fixed by K, and let θ : G' → G induce an injection
G'/J → G/K covering the support of f. Suppose f(θ x) = 0 for the chosen representative x of every
coset outside a finite set s. Then f lives on finitely many cosets, and its operator sends v to
∑ f(θ x)π(θ x)v, over the representatives x of the cosets in s. -/
lemma heckeFun_eq_sum_pullback {J : Subgroup G'} (hf : ∀ (g : G) (k : K), f (g * k) = f g)
    (hv : v ∈ levelSpace (A := A) π K) (s : Finset (G' ⧸ J)) (θ : G' → G)
    (hθ : ∀ g : G, f g ≠ 0 → ∃ x : G', (θ x : G ⧸ K) = g)
    (h_inj : ∀ a b : G', (θ a)⁻¹ * θ b ∈ K ↔ a⁻¹ * b ∈ J)
    (hs : ∀ q : G' ⧸ J, q ∉ s → f (θ q.out) = 0) :
    HasFiniteCosets K f ∧ heckeFun π K f v = ∑ q ∈ s, f (θ q.out) • π (θ q.out) v := by
  have h_coset (a b : G') : (θ a : G ⧸ K) = θ b ↔ (a : G' ⧸ J) = b := by
    simp [QuotientGroup.eq, h_inj]
  have h_injOn : InjOn (fun q : G' ⧸ J ↦ (θ q.out : G ⧸ K)) (SetLike.coe s) := by
    simp [InjOn, h_coset]
  refine heckeFun_eq_sum hf hv h_injOn fun g hg ↦ ?_
  obtain ⟨x, hx⟩ := hθ g hg
  have h_out : (θ (x : G' ⧸ J).out : G ⧸ K) = g := by simp [← hx, h_coset]
  refine ⟨x, ?_, h_out⟩
  by_contra h_not
  -- `θ x.out = g * k` with `k ∈ K`, so `f g = f (θ x.out)`, which `hs` would make `0`
  have h_mem : g⁻¹ * θ (x : G' ⧸ J).out ∈ K := QuotientGroup.eq.1 h_out.symm
  apply hg
  rw [← hf g ⟨_, h_mem⟩, mul_inv_cancel_left, hs _ h_not]

/-- Let the homomorphism a : G' → G be surjective with a⁻¹(K) = J. Let f(gk) = f(g) and π(k)v = v
for k ∈ K, and let F = f∘a be nonzero on finitely many cosets gJ. If ρ(g)v = π(a(g))v for all g,
then the operator of F in ρ and the operator of f in π send v to the same vector. -/
lemma heckeFun_comp {J : Subgroup G'} {F : G' → A} (a : G' →* G)
    (hf : ∀ (g : G) (k : K), f (g * k) = f g) (hv : v ∈ levelSpace (A := A) π K)
    (hF : HasFiniteCosets J F) (ha : Surjective a) (hK : ∀ g : G', a g ∈ K ↔ g ∈ J)
    {ρ : Representation A G' W} (hρ : ∀ g : G', ρ g v = π (a g) v)
    (hF_eq : ∀ g : G', F g = f (a g)) :
    heckeFun ρ J F v = heckeFun π K f v := by
  -- `a` induces a bijection of the coset spaces
  have h_cover (g : G) (_ : f g ≠ 0) : ∃ x : G', (a x : G ⧸ K) = g :=
    (ha g).imp fun x hx ↦ congrArg QuotientGroup.mk hx
  have h_inj (x y : G') : (a x)⁻¹ * a y ∈ K ↔ x⁻¹ * y ∈ J := by simp [← hK]
  have h_zero (q : G' ⧸ J) (hq : q ∉ hF.toFinset) : f (a q.out) = 0 := by
    simpa [← hF_eq] using hq
  obtain ⟨-, h_sum⟩ := heckeFun_eq_sum_pullback hf hv hF.toFinset a h_cover h_inj h_zero
  rw [h_sum, heckeFun_eq_sum_toFinset hF]
  simp [hρ, hF_eq]

/-- Let `f (g * k) = f g` for `k ∈ K`. If `f` lives on finitely many cosets `g K`, so does its left
translate `g ↦ f (x⁻¹ * g)`. -/
lemma HasFiniteCosets.comp_inv_mul (hf_fin : HasFiniteCosets K f)
    (hf : ∀ (g : G) (k : K), f (g * k) = f g) (x : G) :
    HasFiniteCosets K (fun g : G ↦ f (x⁻¹ * g)) := by
  -- The cosets where the translate lives are carried by `x⁻¹` to cosets where `f` lives.
  have h_value (q : G ⧸ K) : f (x⁻¹ • q).out = f (x⁻¹ * q.out) := by
    obtain ⟨k, hk⟩ := mk_out_eq_mul K (x⁻¹ * q.out)
    rw [← MulAction.Quotient.mk_smul_out, smul_eq_mul, hk, hf]
  refine (hf_fin.preimage (MulAction.injective x⁻¹).injOn).subset fun q hq ↦ ?_
  simpa [h_value] using hq

/-- Let `f (g * k) = f g` for `k ∈ K`, let `f` live on finitely many cosets, and let `v` be fixed by
`K`. The operator of the left translate `g ↦ f (x⁻¹ * g)` sends `v` to `π x` of the image of `v`
under the operator of `f`. -/
lemma heckeFun_comp_inv_mul (hf_fin : HasFiniteCosets K f)
    (hf : ∀ (g : G) (k : K), f (g * k) = f g) (hv : v ∈ levelSpace (A := A) π K) (x : G) :
    heckeFun π K (fun g : G ↦ f (x⁻¹ * g)) v = π x (heckeFun π K f v) := by
  -- the representatives of the cosets for the translate are `x * q.out`
  have h_right (g : G) (k : K) : f (x⁻¹ * (g * k)) = f (x⁻¹ * g) := by rw [← mul_assoc, hf]
  have h_cover (g : G) (_ : f (x⁻¹ * g) ≠ 0) : ∃ y : G, ((x * y : G) : G ⧸ K) = g :=
    ⟨x⁻¹ * g, by simp⟩
  have h_zero (q : G ⧸ K) (hq : q ∉ hf_fin.toFinset) : f (x⁻¹ * (x * q.out)) = 0 := by
    simpa using hq
  obtain ⟨-, h_sum⟩ := heckeFun_eq_sum_pullback (f := fun g : G ↦ f (x⁻¹ * g)) h_right hv
    hf_fin.toFinset (x * ·) h_cover (fun a b ↦ by simp) h_zero
  simp [h_sum, heckeFun_eq_sum_toFinset hf_fin]

/-- Let `f` and `f'` live on finitely many cosets `g K`, let `f` be right `K`-invariant, and let `v`
be fixed by `K`. Applying the operator of `f` and then that of `f'` to `v` is the same as applying
the operator of `x ↦ ∑ f' g * f (g⁻¹ * x)`. The sum runs over the chosen representatives `g` of the
cosets where `f'` is nonzero. -/
lemma heckeFun_heckeFun (hf_fin : HasFiniteCosets K f) (hf : ∀ (g : G) (k : K), f (g * k) = f g)
    (hv : v ∈ levelSpace (A := A) π K) {f' : G → A} (h' : HasFiniteCosets K f') :
    heckeFun π K f' (heckeFun π K f v) =
      heckeFun π K (fun x : G ↦ ∑ q ∈ h'.toFinset, f' q.out * f (q.out⁻¹ * x)) v := by
  -- Each `π q.out (heckeFun π K f v)` is the operator of a left translate of `f` applied to `v`;
  -- then exchange the two sums.

  have h_linear : heckeFun π K (fun x : G ↦ ∑ q ∈ h'.toFinset, f' q.out * f (q.out⁻¹ * x)) =
      ∑ q ∈ h'.toFinset, f' q.out • heckeFun π K (fun x : G ↦ f (q.out⁻¹ * x)) := by
    simp [heckeFun, sum_smul, finsum_sum_comm, fun_smul_left (hf_fin.comp_inv_mul hf _),
      fun_smul_right, ← smul_smul, ← smul_finsum']
  rw [heckeFun_eq_sum_toFinset h', h_linear]
  simp [heckeFun_comp_inv_mul hf_fin hf hv]

/-- Let `f` live on finitely many cosets `g K` with `f (g * k) = f g` for `k ∈ K` and
`χ' k * f (k * g) = f g` for `k ∈ K'`. The operator of `f` sends a vector fixed by `K` into the
level space of `(K', χ')`, where each `k ∈ K'` acts as the scalar `χ' k`. -/
lemma heckeFun_mem_levelSpace (hf_fin : HasFiniteCosets K f)
    (hf : ∀ (g : G) (k : K), f (g * k) = f g)
    (hf_left : ∀ (g : G) (k : K'), χ' k * f (k * g) = f g)
    (hv : v ∈ levelSpace (A := A) π K) :
    heckeFun π K f v ∈ levelSpace π K' χ' := by
  -- `π k` replaces `f` by `f (k⁻¹ * ·)`, which is `χ' k` times `f`
  refine mem_levelSpace.2 fun k ↦ ?_
  have h_translate (g : G) : f ((k : G)⁻¹ * g) = χ' k * f g := by
    simp [← hf_left ((k : G)⁻¹ * g) k]
  have h_scale : heckeFun π K (fun g : G ↦ f ((k : G)⁻¹ * g)) = χ' k • heckeFun π K f := by
    simp [heckeFun, h_translate, ← smul_smul, ← smul_finsum', fun_smul_left hf_fin]
  rw [← heckeFun_comp_inv_mul hf_fin hf hv k, h_scale, LinearMap.smul_apply]

/-- The operator of a `K`-bi-invariant function on finitely many cosets preserves the space of
vectors fixed by `K`. -/
lemma IsHeckeFunction.heckeFun_mem (hv : v ∈ levelSpace (A := A) π K) (hb : IsHeckeFunction K f) :
    heckeFun π K f v ∈ levelSpace π K := by
  obtain ⟨h_finite, h_inv⟩ := hb
  exact heckeFun_mem_levelSpace h_finite (fun g k ↦ (h_inv g k k.2).1)
    (fun g k ↦ by simp [(h_inv g k k.2).2]) hv

end HeckeBasic

end New

end
