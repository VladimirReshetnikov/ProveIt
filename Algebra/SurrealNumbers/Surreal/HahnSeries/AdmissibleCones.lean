import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Submonoid.Pointwise
import Mathlib.Algebra.Module.Rat
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.MulAntidiagonal
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Nat.Nth
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Order.WellFoundedSet

/-!
# Admissible weight cones and semilinear supports

This file formalizes `ent:mv:def:adm`, `ent:mv:prop:cone`, `ent:mv:def:semilinear`,
the period-inequality criterion `ent:mv:thm:semilinear`, and the order cores of
`ent:mv:cor:onevar` and `ent:mv:thm:nonclosed` of
`docs/surcomplex/entire-functions-at-arbitrary-rank/article.tex`.

For a support `S ⊆ ℕ^ι` (with `ι` a finite index type, `ι = Fin d` in the
source) and an ordered abelian group `G`, `adm S` is the set of weight vectors
`δ ∈ G^ι` whose weight set `⟨S, δ⟩ = {∑ⱼ αⱼ δⱼ : α ∈ S}` is well ordered.

Proved here, over an arbitrary linearly ordered abelian group `G`:

* `ent:mv:prop:cone`: `adm S` contains `G_{≥0}^ι`, is closed under addition,
  under multiplication by natural numbers, and is upward closed in the
  coordinatewise order. Rational scaling is proved in the strongest form: if
  `n • δ' = m • δ` with `n ≠ 0` and `δ` is admissible then so is `δ'`; for a
  divisible group presented as a `ℚ`-module this gives closure under
  nonnegative rational scaling. For any ordered scalar ring acting
  monotonically (in particular `G = ℝ`), `adm S` is closed under nonnegative
  scaling, convex, and a (pointed) convex cone. The set is not necessarily
  closed: for the parabola support `{(n, n²) : n ≥ 1}` of
  `ent:mv:thm:nonclosed` the admissible points `(-1, 1/(m+1))` tend to the
  nonadmissible point `(-1, 0)`. Finally `adm` is antitone in `S`, and a
  finite change of `S` does not change `adm S`.
* `ent:mv:thm:semilinear` (order-theoretic statement): for a semilinear support
  `⋃ₗ (bₗ + ℕ pₗ₁ + ⋯ + ℕ pₗ_{rₗ})` with finitely many components and
  finitely many periods in each, `δ` is admissible if and only if
  `⟨pₗⱼ, δ⟩ ≥ 0` for every period, so `adm` is the intersection of these
  finitely many weak half-spaces. The offsets impose no inequalities.
  Components and periods are indexed by arbitrary finite types, which covers
  the source's `Fin s` and `Fin rₗ`, empty unions and period-free components.
* The order core of `ent:mv:cor:onevar`: for an infinite `T ⊆ ℕ` the set
  `{n δ : n ∈ T}` is well ordered if and only if `δ ≥ 0`; equivalently
  `Adm_S(G) = G_{≥0}` for every infinite support `S ⊆ ℕ^1`.
* The order core of `ent:mv:thm:nonclosed`, used as the witness above:
  `Adm_{parabola}(ℝ) = {(u, w) : w > 0} ∪ {(u, 0) : u ≥ 0}`, which is convex but
  not closed and not an intersection of weak affine half-spaces; and the growth
  estimate `{n : n⁴ + (n + n²) γ ≤ b}` finite, in any Archimedean ordered field.

Pending: the interpretive sentence of `ent:mv:thm:semilinear`, that the
strong extension domain of an entire series with semilinear support is
decided by these inequalities, needs the identification of `adm` with the
strong domain (`ent:mv:thm:domain`), which is not formalized here. The
domain statement of `ent:mv:cor:onevar` and its cofinal-enlargement consequence
need the same identification and are pending. For
`ent:mv:thm:nonclosed`, the entireness of `F_par` (which needs
`ent:thm:multi-criterion`) and the identification of the computed set with
its strong domain (`ent:mv:thm:domain`) are likewise pending.
-/

namespace Surreal.AdmissibleCone

open Filter Topology
open scoped Pointwise

section Definitions

variable {ι G : Type*} [Fintype ι] [AddCommMonoid G]

/-- The quotient weight `⟨α, δ⟩ = ∑ⱼ αⱼ δⱼ` of a multi-index `α ∈ ℕ^ι` at a
weight vector `δ ∈ G^ι`. -/
def pairing (α : ι → ℕ) (δ : ι → G) : G :=
  ∑ j, α j • δ j

/-- The weight set `⟨S, δ⟩ = {⟨α, δ⟩ : α ∈ S}` of a support `S ⊆ ℕ^ι`. -/
def weightSet (S : Set (ι → ℕ)) (δ : ι → G) : Set G :=
  (fun α => pairing α δ) '' S

/-- `ent:mv:def:adm`: the admissible weights `Adm_S(G)`, the weight vectors whose
weight set is well ordered. It depends only on the set `S`. -/
def adm [Preorder G] (S : Set (ι → ℕ)) : Set (ι → G) :=
  {δ | (weightSet S δ).IsWF}

theorem mem_adm_iff [Preorder G] {S : Set (ι → ℕ)} {δ : ι → G} :
    δ ∈ adm S ↔ (weightSet S δ).IsWF :=
  Iff.rfl

/-- The pairing with a fixed weight vector, as an additive homomorphism in the
multi-index. -/
def pairingHom (δ : ι → G) : (ι → ℕ) →+ G where
  toFun α := pairing α δ
  map_zero' := by simp [pairing]
  map_add' α β := by simp only [pairing, Pi.add_apply, add_nsmul, Finset.sum_add_distrib]

@[simp] theorem pairingHom_apply (δ : ι → G) (α : ι → ℕ) : pairingHom δ α = pairing α δ :=
  rfl

theorem pairing_add_left (α β : ι → ℕ) (δ : ι → G) :
    pairing (α + β) δ = pairing α δ + pairing β δ :=
  map_add (pairingHom δ) α β

theorem pairing_nsmul_left (n : ℕ) (α : ι → ℕ) (δ : ι → G) :
    pairing (n • α) δ = n • pairing α δ :=
  map_nsmul (pairingHom δ) n α

theorem pairing_sum_nsmul_left {J : Type*} [Fintype J] (k : J → ℕ) (p : J → ι → ℕ)
    (δ : ι → G) : pairing (∑ j, k j • p j) δ = ∑ j, k j • pairing (p j) δ := by
  rw [← pairingHom_apply, map_sum]
  simp only [map_nsmul, pairingHom_apply]

theorem pairing_add_right (α : ι → ℕ) (δ ε : ι → G) :
    pairing α (δ + ε) = pairing α δ + pairing α ε := by
  simp only [pairing, Pi.add_apply, nsmul_add, Finset.sum_add_distrib]

theorem pairing_smul_right {R : Type*} [Monoid R] [DistribMulAction R G] (c : R)
    (α : ι → ℕ) (δ : ι → G) : pairing α (c • δ) = c • pairing α δ := by
  simp only [pairing, Pi.smul_apply, Finset.smul_sum, smul_comm (α _) c]

end Definitions

/-- A set in which every lower interval `{x ≤ b}` is finite is well founded. -/
theorem isWF_of_finite_inter_Iic {α : Type*} [Preorder α] {s : Set α}
    (h : ∀ b, (s ∩ Set.Iic b).Finite) : s.IsWF := by
  rw [Set.isWF_iff_no_descending_seq]
  intro f hf hmem
  refine Set.infinite_range_of_injective hf.injective ((h (f 0)).subset ?_)
  rintro _ ⟨n, rfl⟩
  exact ⟨hmem n, hf.antitone (Nat.zero_le n)⟩

/-- A finite union of well-founded sets is well founded. -/
theorem isWF_iUnion_of_finite {L α : Type*} [Finite L] [Preorder α] {s : L → Set α}
    (h : ∀ l, (s l).IsWF) : (⋃ l, s l).IsWF := by
  cases nonempty_fintype L
  have hsup := (Finset.isWF_sup Finset.univ (f := s)).2 fun l _ => h l
  rw [Finset.sup_univ_eq_iSup] at hsup
  exact hsup

section Transport

variable {ι G H : Type*} [Fintype ι] [AddCommMonoid G] [AddCommMonoid H]
  {S S₁ S₂ : Set (ι → ℕ)} {δ : ι → G}

/-- Transport of admissibility along a monotone map of weights. -/
theorem mem_adm_of_monotone [LinearOrder G] [LinearOrder H] {δ' : ι → H} {f : G → H}
    (hf : Monotone f) (h : ∀ α, pairing α δ' = f (pairing α δ)) (hδ : δ ∈ adm S) :
    δ' ∈ adm S := by
  have hset : weightSet S δ' = f '' weightSet S δ := by
    simp only [weightSet, Set.image_image, h]
  rw [mem_adm_iff, hset, ← Set.isPWO_iff_isWF]
  exact (Set.isPWO_iff_isWF.2 hδ).image_of_monotone hf

/-- Reflection of admissibility along a strictly monotone map of weights. -/
theorem mem_adm_of_strictMono [Preorder G] [Preorder H] {δ' : ι → H} {f : H → G}
    (hf : StrictMono f) (h : ∀ α, f (pairing α δ') = pairing α δ) (hδ : δ ∈ adm S) :
    δ' ∈ adm S := by
  rw [mem_adm_iff, Set.isWF_iff_no_descending_seq] at hδ ⊢
  intro g hg hmem
  refine hδ (f ∘ g) (hf.comp_strictAnti hg) fun n => ?_
  obtain ⟨α, hα, hαg⟩ := hmem n
  refine ⟨α, hα, ?_⟩
  change pairing α δ' = g n at hαg
  change pairing α δ = f (g n)
  rw [← hαg, h]

variable [Preorder G]

/-- `ent:mv:prop:cone`: `Adm_S(G)` is antitone in the support. -/
theorem adm_anti (h : S₁ ⊆ S₂) : adm (G := G) S₂ ⊆ adm S₁ :=
  fun _ hδ => Set.IsWF.mono hδ (Set.image_mono h)

/-- Removing finitely many points from a larger support does not lose
admissibility: if `S₁ \ S₂` is finite then `Adm_{S₂} ⊆ Adm_{S₁}`. -/
theorem adm_subset_of_finite_sdiff (h : (S₁ \ S₂).Finite) : adm (G := G) S₂ ⊆ adm S₁ := by
  intro δ hδ
  have hsub : weightSet S₁ δ ⊆ weightSet S₂ δ ∪ weightSet (S₁ \ S₂) δ := by
    rintro _ ⟨α, hα, rfl⟩
    by_cases h2 : α ∈ S₂
    · exact Or.inl ⟨α, h2, rfl⟩
    · exact Or.inr ⟨α, ⟨hα, h2⟩, rfl⟩
  exact (Set.IsWF.union hδ (h.image _).isWF).mono hsub

/-- `ent:mv:prop:cone`: a finite change of the support does not change
`Adm_S(G)`. -/
theorem adm_eq_of_finite_symmDiff (h : (symmDiff S₁ S₂).Finite) : adm (G := G) S₁ = adm S₂ := by
  rw [Set.symmDiff_def, Set.finite_union] at h
  exact (adm_subset_of_finite_sdiff h.2).antisymm (adm_subset_of_finite_sdiff h.1)

end Transport

section OrderedGroup

variable {ι G : Type*} [Fintype ι] [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  {S : Set (ι → ℕ)} {δ ε : ι → G}

/-- `ent:mv:prop:cone`: nonnegative weight vectors are admissible, since every
weight lies in the monoid generated by the finitely many nonnegative
coordinates. -/
theorem mem_adm_of_nonneg (S : Set (ι → ℕ)) (hδ : 0 ≤ δ) : δ ∈ adm S := by
  have hsub : weightSet S δ ⊆ (AddSubmonoid.closure (Set.range δ) : Set G) := by
    rintro _ ⟨α, -, rfl⟩
    exact AddSubmonoid.sum_mem _ fun j _ =>
      AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure (Set.mem_range_self j)) _
  refine Set.IsPWO.isWF (Set.IsPWO.mono ?_ hsub)
  exact Set.IsPWO.addSubmonoid_closure (by rintro _ ⟨j, rfl⟩; exact hδ j)
    (Set.finite_range δ).isPWO

theorem zero_mem_adm (S : Set (ι → ℕ)) : (0 : ι → G) ∈ adm S :=
  mem_adm_of_nonneg S le_rfl

/-- `ent:mv:prop:cone`: `G_{≥0}^ι ⊆ Adm_S(G)`. -/
theorem nonneg_subset_adm (S : Set (ι → ℕ)) : {δ : ι → G | 0 ≤ δ} ⊆ adm S :=
  fun _ hδ => mem_adm_of_nonneg S hδ

/-- `ent:mv:prop:cone`: `Adm_S(G)` is closed under addition, because
`⟨S, δ + ε⟩ ⊆ ⟨S, δ⟩ + ⟨S, ε⟩`. -/
theorem add_mem_adm (hδ : δ ∈ adm S) (hε : ε ∈ adm S) : δ + ε ∈ adm S := by
  have hsub : weightSet S (δ + ε) ⊆ weightSet S δ + weightSet S ε := by
    rintro _ ⟨α, hα, rfl⟩
    exact ⟨_, ⟨α, hα, rfl⟩, _, ⟨α, hα, rfl⟩, (pairing_add_right α δ ε).symm⟩
  exact (Set.IsWF.add hδ hε).mono hsub

/-- `ent:mv:prop:cone`: `Adm_S(G)` is closed under multiplication by natural
numbers (including zero). -/
theorem nsmul_mem_adm (n : ℕ) (hδ : δ ∈ adm S) : n • δ ∈ adm S :=
  mem_adm_of_monotone (f := fun x : G => n • x) (fun _ _ h => nsmul_le_nsmul_right h n)
    (fun α => pairing_smul_right n α δ) hδ

/-- `ent:mv:prop:cone`: `Adm_S(G)` is upward closed in the coordinatewise order. -/
theorem mem_adm_of_le (hδ : δ ∈ adm S) (h : δ ≤ ε) : ε ∈ adm S := by
  have hsum := add_mem_adm hδ (mem_adm_of_nonneg S (δ := ε - δ) fun i => sub_nonneg.2 (h i))
  rwa [add_sub_cancel] at hsum

/-- `ent:mv:prop:cone`, rational scaling in its strongest form: if
`n • δ' = m • δ` with `n ≠ 0`, i.e. `δ' = (m / n) δ`, and `δ` is admissible,
then so is `δ'`. In a divisible group such a `δ'` always exists. -/
theorem mem_adm_of_nsmul_eq_nsmul {δ' : ι → G} {m n : ℕ} (hn : n ≠ 0)
    (h : n • δ' = m • δ) (hδ : δ ∈ adm S) : δ' ∈ adm S :=
  mem_adm_of_strictMono (f := fun x : G => n • x) (nsmul_right_strictMono hn)
    (fun α => by rw [← pairing_smul_right, h, pairing_smul_right]) (nsmul_mem_adm m hδ)

/-- `ent:mv:prop:cone`: if `G` is divisible (presented as a `ℚ`-module), then
`Adm_S(G)` is closed under nonnegative rational scaling. -/
theorem qsmul_mem_adm [Module ℚ G] {q : ℚ} (hq : 0 ≤ q) (hδ : δ ∈ adm S) :
    q • δ ∈ adm S := by
  refine mem_adm_of_nsmul_eq_nsmul (m := q.num.toNat) (n := q.den) q.den_ne_zero ?_ hδ
  rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, Rat.den_mul_eq_num,
    ← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.2 hq)]

section Scalars

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [Module 𝕜 G] [PosSMulMono 𝕜 G]

omit [IsOrderedAddMonoid G] in
/-- `ent:mv:prop:cone`: for an ordered scalar ring acting monotonically on `G`
(for instance `G = ℝ`), `Adm_S(G)` is closed under nonnegative scaling. -/
theorem smul_mem_adm {c : 𝕜} (hc : 0 ≤ c) (hδ : δ ∈ adm S) : c • δ ∈ adm S :=
  mem_adm_of_monotone (f := fun x : G => c • x)
    (fun _ _ h => smul_le_smul_of_nonneg_left h hc) (fun α => pairing_smul_right c α δ) hδ

/-- `ent:mv:prop:cone`: `Adm_S(G)` is convex. -/
theorem convex_adm (S : Set (ι → ℕ)) : Convex 𝕜 (adm (G := G) S) := by
  intro x hx y hy a b ha hb _
  exact add_mem_adm (smul_mem_adm ha hx) (smul_mem_adm hb hy)

/-- `ent:mv:prop:cone`: `Adm_S(G)` as a convex cone. -/
def admConvexCone (S : Set (ι → ℕ)) : ConvexCone 𝕜 (ι → G) where
  carrier := adm S
  smul_mem' _ hc _ hx := smul_mem_adm hc.le hx
  add_mem' _ hx _ hy := add_mem_adm hx hy

@[simp] theorem coe_admConvexCone (S : Set (ι → ℕ)) :
    (admConvexCone (𝕜 := 𝕜) (G := G) S : Set (ι → G)) = adm S :=
  rfl

/-- `ent:mv:prop:cone`: `Adm_S(G)` as a pointed cone (a submodule over the
nonnegative scalars). -/
def admPointedCone [IsOrderedRing 𝕜] (S : Set (ι → ℕ)) : PointedCone 𝕜 (ι → G) where
  carrier := adm S
  add_mem' hx hy := add_mem_adm hx hy
  zero_mem' := zero_mem_adm S
  smul_mem' c _ hx := smul_mem_adm (𝕜 := 𝕜) c.2 hx

@[simp] theorem coe_admPointedCone [IsOrderedRing 𝕜] (S : Set (ι → ℕ)) :
    (admPointedCone (𝕜 := 𝕜) (G := G) S : Set (ι → G)) = adm S :=
  rfl

end Scalars

/-! ### Semilinear supports -/

section Semilinear

/-- The linear set `b + ℕ p₁ + ⋯ + ℕ p_r` with periods indexed by a finite type. -/
def linearSet {J : Type*} [Fintype J] (b : ι → ℕ) (p : J → ι → ℕ) : Set (ι → ℕ) :=
  {x | ∃ k : J → ℕ, x = b + ∑ j, k j • p j}

/-- `ent:mv:def:semilinear`: the semilinear set `⋃ₗ (bₗ + ℕ pₗ₁ + ⋯ + ℕ pₗ_{rₗ})`. -/
def semilinearSet {L : Type*} {J : L → Type*} [∀ l, Fintype (J l)] (b : L → ι → ℕ)
    (p : (l : L) → J l → ι → ℕ) : Set (ι → ℕ) :=
  ⋃ l, linearSet (b l) (p l)

/-- `ent:mv:thm:semilinear` for one component: `δ` is admissible for
`b + ℕ p₁ + ⋯ + ℕ p_r` if and only if every period has nonnegative weight. -/
theorem mem_adm_linearSet_iff {J : Type*} [Fintype J] (b : ι → ℕ) (p : J → ι → ℕ)
    (δ : ι → G) : δ ∈ adm (linearSet b p) ↔ ∀ j, 0 ≤ pairing (p j) δ := by
  constructor
  · intro hδ j
    by_contra hneg
    rw [not_le] at hneg
    rw [mem_adm_iff, Set.isWF_iff_no_descending_seq] at hδ
    refine hδ (fun n : ℕ => pairing b δ + n • pairing (p j) δ) ?_ fun n => ?_
    · refine strictAnti_nat_of_succ_lt fun n => ?_
      rw [succ_nsmul, ← add_assoc]
      exact add_lt_of_neg_right _ hneg
    · classical
      refine ⟨b + n • p j, ⟨Pi.single j n, ?_⟩, ?_⟩
      · rw [Finset.sum_eq_single j (fun i _ hi => by rw [Pi.single_eq_of_ne hi, zero_smul])
          (by simp), Pi.single_eq_same]
      · change pairing (b + n • p j) δ = _
        rw [pairing_add_left, pairing_nsmul_left]
  · intro hp
    have hsub : weightSet (linearSet b p) δ ⊆
        {pairing b δ} + (AddSubmonoid.closure (Set.range fun j => pairing (p j) δ) : Set G) := by
      rintro _ ⟨x, ⟨k, rfl⟩, rfl⟩
      refine ⟨pairing b δ, rfl, _, ?_, (pairing_add_left _ _ _).symm⟩
      rw [pairing_sum_nsmul_left]
      exact AddSubmonoid.sum_mem _ fun j _ =>
        AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure (Set.mem_range_self j)) _
    refine (Set.IsWF.add Set.isWF_singleton ?_).mono hsub
    exact (Set.IsPWO.addSubmonoid_closure (by rintro _ ⟨j, rfl⟩; exact hp j)
      (Set.finite_range _).isPWO).isWF

variable {L : Type*} {J : L → Type*} [∀ l, Fintype (J l)]

/-- `ent:mv:thm:semilinear`, the period-inequality criterion: for a semilinear
support with finitely many components, `δ ∈ Adm_S(G)` if and only if every period
vector has nonnegative weight `⟨pₗⱼ, δ⟩ ≥ 0`. -/
theorem mem_adm_semilinearSet_iff [Finite L] (b : L → ι → ℕ) (p : (l : L) → J l → ι → ℕ)
    (δ : ι → G) : δ ∈ adm (semilinearSet b p) ↔ ∀ l j, 0 ≤ pairing (p l j) δ := by
  constructor
  · intro hδ l
    exact (mem_adm_linearSet_iff (b l) (p l) δ).1 (adm_anti (Set.subset_iUnion _ l) hδ)
  · intro hp
    rw [mem_adm_iff, weightSet, semilinearSet, Set.image_iUnion]
    exact isWF_iUnion_of_finite fun l => (mem_adm_linearSet_iff (b l) (p l) δ).2 (hp l)

/-- `ent:mv:thm:semilinear`: the admissible set of a semilinear support is the
intersection of the finitely many weak half-spaces `⟨pₗⱼ, δ⟩ ≥ 0`. -/
theorem adm_semilinearSet [Finite L] (b : L → ι → ℕ) (p : (l : L) → J l → ι → ℕ) :
    adm (G := G) (semilinearSet b p) = ⋂ l, ⋂ j, {δ | 0 ≤ pairing (p l j) δ} := by
  ext δ
  simp only [mem_adm_semilinearSet_iff, Set.mem_iInter, Set.mem_setOf_eq]

/-- `ent:mv:thm:semilinear`: the offsets impose no inequalities; replacing them
does not change the admissible set. -/
theorem adm_semilinearSet_eq_of_offsets [Finite L] (b b' : L → ι → ℕ)
    (p : (l : L) → J l → ι → ℕ) :
    adm (G := G) (semilinearSet b p) = adm (semilinearSet b' p) := by
  rw [adm_semilinearSet, adm_semilinearSet]

end Semilinear

end OrderedGroup

/-! ### One variable -/

section OneVariable

variable {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

/-- The order core of `ent:mv:cor:onevar`: for an infinite `T ⊆ ℕ`, the set
`{n δ : n ∈ T}` is well ordered if and only if `δ ≥ 0`. -/
theorem isWF_image_nsmul_iff_of_infinite {T : Set ℕ} (hT : T.Infinite) (δ : G) :
    ((fun n : ℕ => n • δ) '' T).IsWF ↔ 0 ≤ δ := by
  refine ⟨fun h => ?_, fun hδ =>
    ((Set.IsPWO.of_linearOrder T).image_of_monotone (nsmul_left_monotone hδ)).isWF⟩
  by_contra hneg
  rw [not_le] at hneg
  rw [Set.isWF_iff_no_descending_seq] at h
  have hanti : StrictAnti fun n : ℕ => n • δ := strictAnti_nat_of_succ_lt fun n => by
    rw [succ_nsmul]
    exact add_lt_of_neg_right _ hneg
  exact h _ (hanti.comp_strictMono (Nat.nth_strictMono (p := (· ∈ T)) hT)) fun k =>
    ⟨_, Nat.nth_mem_of_infinite (p := (· ∈ T)) hT k, rfl⟩

/-- The order core of `ent:mv:cor:onevar` in the notation of `ent:mv:def:adm`: for an
infinite support `S ⊆ ℕ^1`, `Adm_S(G) = G_{≥0}`. -/
theorem mem_adm_iff_nonneg_of_infinite {S : Set (Fin 1 → ℕ)} (hS : S.Infinite)
    {δ : Fin 1 → G} : δ ∈ adm S ↔ 0 ≤ δ := by
  have hinj : Set.InjOn (fun α : Fin 1 → ℕ => α 0) S := fun α _ β _ h =>
    funext fun i => by rw [Subsingleton.elim i 0]; exact h
  have hset : weightSet S δ =
      (fun n : ℕ => n • δ 0) '' ((fun α : Fin 1 → ℕ => α 0) '' S) := by
    simp only [weightSet, Set.image_image, pairing, Fin.sum_univ_one]
  rw [mem_adm_iff, hset, isWF_image_nsmul_iff_of_infinite (hS.image hinj)]
  exact ⟨fun h i => by rw [Subsingleton.elim i 0]; exact h, fun h => h 0⟩

end OneVariable

/-! ### The parabola support: `Adm_S(ℝ)` need not be closed -/

section Parabola

/-- A set containing an eventually strictly decreasing sequence is not well
founded. -/
theorem not_isWF_of_eventually_strictAnti {α : Type*} [Preorder α] {s : Set α} (g : ℕ → α)
    (N : ℕ) (hg : ∀ n, N ≤ n → g (n + 1) < g n) (hs : ∀ n, N ≤ n → g n ∈ s) : ¬ s.IsWF := by
  rw [Set.isWF_iff_no_descending_seq]
  intro h
  refine h (fun k => g (k + N)) (strictAnti_nat_of_succ_lt fun k => ?_) fun k =>
    hs _ (Nat.le_add_left N k)
  have hk := hg (k + N) (Nat.le_add_left N k)
  rw [Nat.add_right_comm] at hk
  exact hk

/-- The support `{(n, n²) : n ≥ 1}` of the series `F_par` of `ent:mv:thm:nonclosed`. -/
def parabola : Set (Fin 2 → ℕ) :=
  {α | ∃ n : ℕ, 1 ≤ n ∧ α = ![n, n ^ 2]}

theorem pairing_parabola (n : ℕ) (δ : Fin 2 → ℝ) :
    pairing ![n, n ^ 2] δ = n * δ 0 + (n : ℝ) ^ 2 * δ 1 := by
  simp [pairing, Fin.sum_univ_two, nsmul_eq_mul]

theorem pairing_mem_weightSet_parabola {n : ℕ} (hn : 1 ≤ n) (δ : Fin 2 → ℝ) :
    (n : ℝ) * δ 0 + (n : ℝ) ^ 2 * δ 1 ∈ weightSet parabola δ :=
  ⟨![n, n ^ 2], ⟨n, hn, rfl⟩, pairing_parabola n δ⟩

/-- For `δ₁ > 0` the weight vector `δ` is admissible for the parabola: the weights
`n δ₀ + n² δ₁` tend to `+∞`. -/
theorem mem_adm_parabola_of_pos {δ : Fin 2 → ℝ} (hw : 0 < δ 1) : δ ∈ adm parabola := by
  apply isWF_of_finite_inter_Iic
  intro b
  set A : ℝ := |δ 0| + |b| + 1
  have hN : ∀ n : ℕ, ⌈A / δ 1⌉₊ < n → b < n * δ 0 + (n : ℝ) ^ 2 * δ 1 := by
    intro n hn
    have hn' : A / δ 1 < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn)
    have hnw : A < n * δ 1 := by rwa [div_lt_iff₀ hw] at hn'
    have hn1 : (1 : ℝ) ≤ n := by
      have : 1 ≤ n := by omega
      exact_mod_cast this
    have h1 : n * A ≤ n * (n * δ 1) := mul_le_mul_of_nonneg_left hnw.le (by positivity)
    have h2 : |b| ≤ n * |b| := le_mul_of_one_le_left (abs_nonneg b) hn1
    have h3 : -(n * δ 0) ≤ n * |δ 0| := by
      rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs (δ 0)) (by positivity)
    have h4 : b ≤ |b| := le_abs_self b
    simp only [A] at h1
    nlinarith
  refine ((Set.finite_Iic ⌈A / δ 1⌉₊).image
    fun n : ℕ => pairing ![n, n ^ 2] δ).subset ?_
  rintro _ ⟨⟨α, ⟨n, -, rfl⟩, rfl⟩, hle⟩
  refine ⟨n, ?_, rfl⟩
  by_contra hlt
  rw [Set.mem_Iic, not_le] at hlt
  change pairing ![n, n ^ 2] δ ≤ b at hle
  rw [pairing_parabola] at hle
  exact absurd hle (not_le.2 (hN n hlt))

/-- For `δ₁ < 0` the weight vector `δ` is not admissible for the parabola: the
successive differences `δ₀ + (2n + 1) δ₁` are eventually negative. -/
theorem not_mem_adm_parabola_of_neg {δ : Fin 2 → ℝ} (hw : δ 1 < 0) : δ ∉ adm parabola := by
  obtain ⟨N, hN⟩ := exists_nat_gt (|δ 0| / -δ 1)
  have hN' : |δ 0| < N * -δ 1 := by rwa [div_lt_iff₀ (neg_pos.2 hw)] at hN
  refine not_isWF_of_eventually_strictAnti (fun n : ℕ => (n : ℝ) * δ 0 + (n : ℝ) ^ 2 * δ 1)
    (N + 1) (fun n hn => ?_) fun n hn => pairing_mem_weightSet_parabola (by omega) δ
  have hnN : (N : ℝ) ≤ 2 * n + 1 := by
    have : N ≤ 2 * n + 1 := by omega
    exact_mod_cast this
  have h1 : ((2 * n + 1 : ℝ) - N) * δ 1 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) hw.le
  have h2 : δ 0 ≤ |δ 0| := le_abs_self (δ 0)
  push_cast
  nlinarith

/-- For `δ₁ = 0` and `δ₀ < 0` the weight vector `δ` is not admissible for the
parabola: the weights `n δ₀` strictly decrease. -/
theorem not_mem_adm_parabola_of_eq_zero_of_neg {δ : Fin 2 → ℝ} (hw : δ 1 = 0) (hu : δ 0 < 0) :
    δ ∉ adm parabola := by
  refine not_isWF_of_eventually_strictAnti (fun n : ℕ => (n : ℝ) * δ 0 + (n : ℝ) ^ 2 * δ 1)
    1 (fun n _ => ?_) fun n hn => pairing_mem_weightSet_parabola hn δ
  rw [hw]
  push_cast
  linarith

/-- The order core of `ent:mv:thm:nonclosed`:
`Adm_{parabola}(ℝ) = {(u, w) : w > 0} ∪ {(u, 0) : u ≥ 0}`. -/
theorem adm_parabola :
    adm (G := ℝ) parabola = {δ | 0 < δ 1} ∪ {δ | δ 1 = 0 ∧ 0 ≤ δ 0} := by
  ext δ
  simp only [Set.mem_union, Set.mem_setOf_eq]
  constructor
  · intro h
    rcases lt_trichotomy (δ 1) 0 with hw | hw | hw
    · exact absurd h (not_mem_adm_parabola_of_neg hw)
    · refine Or.inr ⟨hw, ?_⟩
      by_contra hu
      exact not_mem_adm_parabola_of_eq_zero_of_neg hw (lt_of_not_ge hu) h
    · exact Or.inl hw
  · rintro (hw | ⟨hw, hu⟩)
    · exact mem_adm_parabola_of_pos hw
    · exact mem_adm_of_nonneg _ fun i => by fin_cases i <;> simp [hu, hw]

/-- `ent:mv:prop:cone`, "not necessarily closed" (from `ent:mv:thm:nonclosed`): the
admissible points `(-1, 1/(m+1))` of the parabola support converge to the
nonadmissible point `(-1, 0)`, so `Adm_S(ℝ)` is not closed. -/
theorem not_isClosed_adm_parabola : ¬ IsClosed (adm (G := ℝ) parabola) := by
  intro hcl
  have hlim : Tendsto (fun m : ℕ => ![(-1 : ℝ), 1 / ((m : ℝ) + 1)]) atTop
      (𝓝 ![(-1 : ℝ), 0]) := by
    rw [tendsto_pi_nhds]
    intro i
    fin_cases i
    · simp
    · simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  refine not_mem_adm_parabola_of_eq_zero_of_neg (δ := ![(-1 : ℝ), 0]) (by simp) (by simp)
    (hcl.mem_of_tendsto hlim (Eventually.of_forall fun m => mem_adm_parabola_of_pos ?_))
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  positivity

/-- `ent:mv:thm:nonclosed`: the admissible set of the parabola support is not an
intersection of weak affine half-spaces (of any cardinality, in particular not of
finitely many), since such an intersection is closed. -/
theorem adm_parabola_ne_iInter_halfSpaces {K : Type*} (a : K → Fin 2 → ℝ) (c : K → ℝ) :
    adm (G := ℝ) parabola ≠ ⋂ k, {δ : Fin 2 → ℝ | c k ≤ ∑ i, a k i * δ i} := by
  intro h
  apply not_isClosed_adm_parabola
  rw [h]
  exact isClosed_iInter fun k => isClosed_le continuous_const (by fun_prop)

/-- The growth estimate in the proof of `ent:mv:thm:nonclosed`: for the coefficients
`t^{n⁴}` of `F_par`, of total degree `n + n²`, the set
`{n : n⁴ + (n + n²) γ ≤ b}` is finite for all `γ, b` in any Archimedean ordered
field (condition `ent:mv:eq:growth` for `F_par`, where `ent:mv:thm:nonclosed` takes
`Γ = ℚ`). The set ranges over all `n : ℕ`, a superset of the support indices
`n ≥ 1`, so its finiteness is at least as strong. -/
theorem parabola_growth {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Archimedean K] (γ b : K) :
    {n : ℕ | (n : K) ^ 4 + ((n : K) + (n : K) ^ 2) * γ ≤ b}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * |γ| + |b| + 1)
  refine (Set.finite_Iic N).subset fun n hn => ?_
  rw [Set.mem_setOf_eq] at hn
  rw [Set.mem_Iic]
  by_contra hlt
  rw [not_le] at hlt
  have hx : 2 * |γ| + |b| + 1 < (n : K) := hN.trans (by exact_mod_cast hlt)
  have hγ0 : 0 ≤ |γ| := abs_nonneg γ
  have hb0 : 0 ≤ |b| := abs_nonneg b
  have hx1 : (1 : K) ≤ n := by linarith
  have hsq : (n : K) ≤ (n : K) ^ 2 := by nlinarith
  have hsq1 : (1 : K) ≤ (n : K) ^ 2 := hx1.trans hsq
  have h1 : ((n : K) + (n : K) ^ 2) * -|γ| ≤ ((n : K) + (n : K) ^ 2) * γ :=
    mul_le_mul_of_nonneg_left (neg_abs_le γ) (by positivity)
  have h2 : (n : K) ^ 2 * (2 * |γ| + |b| + 1) ≤ (n : K) ^ 2 * (n : K) ^ 2 :=
    mul_le_mul_of_nonneg_left (hx.le.trans hsq) (sq_nonneg _)
  have h3 : (n : K) * |γ| ≤ (n : K) ^ 2 * |γ| := mul_le_mul_of_nonneg_right hsq hγ0
  have h4 : |b| + 1 ≤ (n : K) ^ 2 * (|b| + 1) := le_mul_of_one_le_left (by positivity) hsq1
  have h5 : b ≤ |b| := le_abs_self b
  nlinarith

/-- `ent:mv:prop:cone`: for `G = ℝ`, `Adm_S(ℝ)` is a convex cone (convex and closed
under nonnegative scaling, containing `0`). That it is not necessarily closed is
`exists_not_isClosed_adm_real`. -/
theorem adm_real_convexCone {ι : Type*} [Fintype ι] (S : Set (ι → ℕ)) :
    Convex ℝ (adm (G := ℝ) S) ∧ (0 : ι → ℝ) ∈ adm S ∧
      ∀ c : ℝ, 0 ≤ c → ∀ δ ∈ adm (G := ℝ) S, c • δ ∈ adm S :=
  ⟨convex_adm S, zero_mem_adm S, fun _ hc _ hδ => smul_mem_adm hc hδ⟩

/-- `ent:mv:prop:cone`: the real admissible cone is not closed in general. -/
theorem exists_not_isClosed_adm_real : ∃ S : Set (Fin 2 → ℕ), ¬ IsClosed (adm (G := ℝ) S) :=
  ⟨parabola, not_isClosed_adm_parabola⟩

end Parabola

end Surreal.AdmissibleCone
