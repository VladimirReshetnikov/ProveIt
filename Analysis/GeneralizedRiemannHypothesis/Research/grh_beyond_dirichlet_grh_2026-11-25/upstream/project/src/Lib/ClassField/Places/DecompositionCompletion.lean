import Lib.ClassField.Places.LocalFields
import Lib.PadicHodge.PeriodRings.AxTheorem

/-!
# Decomposition groups of places above p as Galois groups of local fields in ℚ̄_p

Let `Ω` be an algebraic closure of a number field `K` and `Γ` its Galois group. A place of `Ω` is a
valuation subring `A` of `Ω` (the type `ClosurePlace`), and `New.IsPlaceOver A v` says that it lies
over the prime `v` of `K`.

`New.decompGroup Γ A` is the stabiliser of `A`, `New.Gp p` is `Gal(ℚ̄_p/ℚ_p)`, and `New.intQpBar p`
is the valuation ring of `ℚ̄_p`. Every place above `p` is induced by an embedding `Ω → ℚ̄_p`, and
the decomposition group then embeds as an open subgroup of `New.Gp p`, acting as the Galois group
over the completion at `v`.

## Main definitions and results

* `New.Period.isLocalGalois_of_isOpenEmbedding`: let `j` be an open embedding of a group in
  `Gal(ℚ̄_p/ℚ_p)`. Then the group is the absolute Galois group of the subfield of `ℚ̄_p` fixed by
  the image of `j`.
* `New.exists_comap_intQpBar_eq`: every place of an algebraic closure of `ℚ` above `p` is induced by
  an embedding in `ℚ̄_p`.
* `New.IsCompletionEmb`: the decomposition group of `A` acts on `ℚ̄_p` as the Galois group over the
  completion at `v`, compatibly with an embedding `j : Ω → ℚ̄_p` that induces `A`.
* `New.IsPlaceOver.exists_isCompletionEmb`: such data exist for every place `A` of `Ω` over `v`.
* `New.IsPlaceOver.isLocalGalois_and_residueCard_eq_and_isUniformiser`: the fixed field is local
  (`New.IsLocalGalois`), with the same residue order, and uniformisers of `K` remain uniformisers.
* `New.IsPlaceOver.ramification_in_tower`: ramification index and residue degree in a finite
  extension of `K`.

Notions from other files:
* `New.IsLocalGalois Γ K A`: `Γ` acts as the profinite Galois group of the algebraically closed
  field `Ω` over `K` and stabilises the valuation ring `A`, and `A ∩ K` (`New.valRingBelow`) is a
  discrete valuation ring with finite residue field.
* `New.PadicField F p`: a normed field `F` that is a normed algebra over `ℚ_p`, not necessarily
  complete.
* `New.residueCard K A`: the number of elements of the residue field of the valuation ring of `K`
  induced by `A` (zero if infinite).
* `New.IsProGalois`: a profinite group acts on the Galois extension Ω/K as its Galois group, with
  open stabilisers.
* `New.ordRat K A`: the order normalised on `K`: a chosen additive f : Ω^× → ℚ with n f(x) = a
  exactly when x^n and π^a have equal valuation, for uniformisers π of `K`.

## Relation to the literature

Known; see `Lib.ClassField.Places.LocalFields` for sources.
-/

namespace New

/-!
## Decomposition groups above p as open subgroups of the Galois group of ℚ_p
-/

section PadicDecomposition

open Set Subtype PadicInt decompGroup IntermediateField UniformSpace.Completion Topology Nat
  MulSemiringAction Selmer

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K]
  {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
  (e : K →+* PadicAlgCl p) (j : Γ →* Gp p) (ι : Ω →+* PadicAlgCl p)

/-! ### The local field `ℚ_p` -/

/-- The place of `Ω` induced by `ι : Ω → ℚ̄_p` lies above `p`. -/
lemma valuation_comap_intQpBar_lt_one : ((intQpBar p).comap ι) p < 1 := by
  simp [comap_apply_lt_one_iff, norm_p_lt_one]

/-- The valuation ring that `ℚ̄_p` induces on `ℚ_p` is `ℤ_p`: both consist of the elements of norm
at most `1`. -/
private lemma toSubring_valRingBelow_intQpBar :
    (valRingBelow ℚ_[p] (intQpBar p)).toSubring = subring p := by
  aesop

/-- The valuation ring that `ℚ̄_p` induces on `ℚ_p`, identified with `ℤ_p`. -/
private noncomputable def valRingBelowEquivPadicInt : valRingBelow ℚ_[p] (intQpBar p) ≃+* ℤ_[p] :=
  .subringCongr toSubring_valRingBelow_intQpBar

/-- The residue field of `ℚ_p` for the valuation ring that `ℚ̄_p` induces on it (which is `ℤ_p`) has
`p` elements. -/
lemma Selmer.residueCard_padic : residueCard ℚ_[p] (intQpBar p) = p := by
  -- The residue field of `ℤ_[p]` is `ZMod p`.
  exact (card_congr ((IsLocalRing.ResidueField.mapEquiv valRingBelowEquivPadicInt).trans
    residueField).toEquiv).trans (Nat.card_zmod p)

/-- `Gal(ℚ̄_p/ℚ_p)` is the absolute Galois group of the local field `ℚ_p`: it maps the valuation
ring of `ℚ̄_p` to itself, and this ring meets `ℚ_p` in `ℤ_p`, a discrete valuation ring with
finite residue field. -/
instance isLocalGalois_padic : IsLocalGalois (Gp p) ℚ_[p] (intQpBar p) where
  mem_decompGroup g := by
    -- The Galois group acts by isometries, so it maps the valuation ring to itself.
    exact mem_decompGroup_iff.mpr fun x ↦ by simp [← nndist_zero_right, ← nndist_smul g x]
  isDiscreteValuationRing :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing valRingBelowEquivPadicInt.symm
  finite_residue := finite_of_card_ne_zero (residueCard_padic.trans_ne NeZero.out)

/-- In a normed field F over ℚ_p, the topological closure of any subfield contains the image of
ℚ_p. -/
lemma padic_mem_topologicalClosure {F : Type*} [NormedField F] [PadicField F p] (S : Subfield F)
    (x : ℚ_[p]) : algebraMap ℚ_[p] F x ∈ S.topologicalClosure :=
  map_mem_closure (by fun_prop) (Padic.denseRange_ratCast p x) (by simp)

/-- A ring homomorphism `ι` from the algebraic closure `Ω` of `ℚ` to `ℚ̄_p` has dense image. -/
lemma denseRange_emb_padicAlgCl : DenseRange ι := by
  -- The closure `L` of the image of `ι` in the completion `ℂ_p` is a complete field in which the
  -- algebraically closed field `Ω` is dense, so it is algebraically closed. It contains `ℚ_p`,
  -- hence every element that is algebraic over `ℚ_p`.
  let L : IntermediateField ℚ_[p] ℂ_[p] :=
    Subfield.toIntermediateField _ (padic_mem_topologicalClosure (coeRingHom.comp ι).fieldRange)
  let ιL : Ω →+* L := (coeRingHom.comp ι).codRestrict L fun x ↦ subset_closure ⟨x, rfl⟩
  have h_dense : DenseRange ιL := by
    rw [DenseRange, dense_iff, ← range_comp]
    exact le_rfl
  have h_closed : IsAlgClosed L := by
    have hL_complete : CompleteSpace L := isClosed_closure.completeSpace_coe
    let alg : Algebra Ω L := ιL.toAlgebra
    exact IsAlgClosed.of_denseRange (K := Ω) h_dense
  -- Density in `ℚ̄_p` may be tested in the completion.
  refine isDenseInducing_coe.dense_iff.mpr fun x ↦ ?_
  -- `x` is algebraic over `ℚ_p` and its minimal polynomial splits in `L`, so `x` lies in `L`.
  have h_mem : algebraMap (PadicAlgCl p) ℂ_[p] x ∈ L :=
    (IsGalois.integral ℚ_[p] x).algebraMap.mem_intermediateField_of_minpoly_splits
      (IsAlgClosed.splits _)
  -- `L` is by definition the closure of the image of `ι` in `ℂ_p`.
  rw [← range_comp]
  exact h_mem

/-! ### Open subgroups of the Galois group of `ℚ_p` -/

/-- For an embedding `e : K → ℚ̄_p` of a field `K` and a homomorphism `j : Γ → Gal(ℚ̄_p/ℚ_p)` from
the topological group `Γ`: `j` is an open embedding whose image consists of the elements fixing
`e(K)` pointwise. -/
def Selmer.IsCompletionGroup : Prop :=
  IsOpenEmbedding j ∧ ∀ g : Gp p, g ∈ j.range ↔ ∀ x : K, g (e x) = e x

/-- If `j` is an open embedding of the topological group `Γ` into `Gal(ℚ̄_p/ℚ_p)`, then `Γ`, acting
on `ℚ̄_p` through `j` (the `let` in the statement), is the absolute Galois group of the fixed field
of `j(Γ)`, in the sense of `New.IsLocalGalois` for the integers of `ℚ̄_p`. -/
lemma Period.isLocalGalois_of_isOpenEmbedding {j : Γ →* Gp p} (hj : IsOpenEmbedding j) :
    let : MulSemiringAction Γ (PadicAlgCl p) := compHom (PadicAlgCl p) j
    IsLocalGalois Γ (fixedFieldOf j.range) (intQpBar p) := by
  -- The image of `j` is an open subgroup of `Gp p`, so it is the Galois group of a finite extension
  -- of `ℚ_p`, a local field (`IsLocalGalois.of_finite`); the structure is carried to `Γ` along the
  -- isomorphism onto the image.
  intro action
  -- `id` keeps the open subgroup folded, as instance search needs it.
  have h_range : IsLocalGalois j.range (fixedFieldOf j.range) (intQpBar p) :=
    (isLocalGalois_padic.of_finite (id ⟨j.range, hj.isOpen_range⟩)).isLocalGalois
  have h_compact : CompactSpace Γ := IsClosedEmbedding.compactSpace
    ⟨hj.isEmbedding, j.range.isClosed_of_isOpen hj.isOpen_range⟩
  have h_disconnected : TotallyDisconnectedSpace Γ := hj.toHomeomorph.symm.totallyDisconnectedSpace
  have h_galois : IsGaloisGroup Γ (fixedFieldOf j.range) (PadicAlgCl p) :=
    .of_mulEquiv (j.ofInjective hj.injective) fun g x ↦ rfl
  exact { h_compact, hj.isTopologicalGroup, h_disconnected, h_galois, h_range with
    mem_decompGroup g := isLocalGalois_padic.mem_decompGroup (j g)
    isOpen_stabilizer x := (isLocalGalois_padic.isOpen_stabilizer x).preimage hj.continuous }

variable [Algebra K Ω] [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω]

/-- `j` is the map from the decomposition group of `A` to `Gal(ℚ̄_p/ℚ_p)` that goes with the
embedding `e : Ω → ℚ̄_p`: (a) `A` is the preimage under `e` of the valuation ring of `ℚ̄_p`,
(b) `j g` acts on the image of `e` as `g` acts on `Ω`, and (c) `j` is an open embedding whose
image consists of the automorphisms that fix `e K` pointwise. The bracketing is
`((a) ∧ (b)) ∧ (c)`. -/
def GaloisRep.InducesPlace (K : Type*) [Field K] [Algebra K Ω] (A : ClosurePlace)
    (e : Ω →+* PadicAlgCl p) (j : decompGroup Γ A →* Gp p) : Prop :=
  -- (a) `e` induces `A`
  ((intQpBar p).comap e = A ∧
   -- (b) `e` is equivariant along `j`
   ∀ (g : decompGroup Γ A) (x : Ω), j g (e x) = e ((g : Γ) • x)) ∧
  -- (c) `j` is an open embedding onto the elements that fix `e K` pointwise
  IsCompletionGroup (e.comp (algebraMap K Ω)) j

/-- Let `Γ` act on `Ω` as the Galois group over `K`, let `ι : Ω → ℚ̄_p`, and let `σ` lie in the
decomposition group of the place that `ι` induces on `Ω`. If `ι x` lies in the closure of `ι(K)`,
then `σ` fixes `x`. -/
lemma smul_eq_self_of_mem_decompGroup_of_mem_closure (ι : Ω →+* PadicAlgCl p) {σ : Γ}
    (hσ : σ ∈ decompGroup Γ ((intQpBar p).comap ι)) {x : Ω}
    (hx : ι x ∈ closure (range (ι.comp (algebraMap K Ω)))) :
    σ • x = x := by
  -- `σ` preserves the valuation and fixes `K`, so `ι (σ x)` and `ι x` are equally far from each
  -- point of `ι(K)`; by continuity also from `ι x`, so they are equal.
  let k : K →+* PadicAlgCl p := ι.comp (algebraMap K Ω)
  have h_dist : EqOn (nndist (ι (σ • x))) (nndist (ι x)) (range k) := by
    rintro _ ⟨a, rfl⟩
    have h_val : ((intQpBar p).comap ι) (σ • (x - algebraMap K Ω a)) =
        ((intQpBar p).comap ι) (x - algebraMap K Ω a) :=
      decompGroup.val_smul hσ (x - algebraMap K Ω a)
    simpa [nndist_eq_nnnorm, smul_sub, k] using
      ((PadicAlgCl.valued p).v.comap ι).isEquiv_valuation_valuationSubring.eq_iff.mpr h_val
  have h_dist_self : nndist (ι (σ • x)) (ι x) = nndist (ι x) (ι x) :=
    h_dist.closure (by fun_prop) (by fun_prop) hx
  exact ι.injective (by simpa using h_dist_self)

variable (K Γ)

/-- Let `Ω` be `New.Ω`, the fixed algebraic closure of `ℚ`, and let `K` be a number field inside
`Ω`, with `Γ` acting as the Galois group of `Ω/K` (`IsProGalois`). An embedding
`ι : Ω → ℚ̄_p` that pulls the integers of `ℚ̄_p` back to the place `A` induces an open embedding `j`
of the decomposition group of `A` in `Gal(ℚ̄_p/ℚ_p)`, with `j(g)(ι x) = ι(g x)`, whose image
consists of the automorphisms fixing `ι(K)` pointwise (`GaloisRep.InducesPlace`). -/
lemma exists_inducesPlace [NumberField K] {ι : Ω →+* PadicAlgCl p} {A : ValuationSubring Ω}
    (h_comap : (intQpBar p).comap ι = A) :
    ∃ j : decompGroup Γ A →* Gp p, GaloisRep.InducesPlace (Γ := Γ) K A ι j := by
  subst h_comap
  -- Let `U` be the open subgroup of `Gp p` fixing `ℚ_p (ι K)`. Restriction along `ι` is an
  -- isomorphism `res` from `U` to the decomposition group, and `j` is its inverse.
  let k : K →+* PadicAlgCl p := ι.comp (algebraMap K Ω)
  -- `id` keeps the open subgroup folded, as instance search needs it.
  let U : OpenSubgroup (Gp p) := id ⟨_, (adjoin ℚ_[p] (range k)).fixingSubgroup_isOpen⟩
  -- `U` fixes `ι K`, which lies in `ℚ_p (ι K)`, so restriction along `ι` is defined.
  have hU_fixes (g : (U : Subgroup (Gp p))) (x : K) :
      g • ι (algebraMap K Ω x) = ι (algebraMap K Ω x) :=
    (mem_fixingSubgroup_iff (Gp p)).mp g.prop _ (subset_adjoin _ _ ⟨x, rfl⟩)
  obtain ⟨⟨f, hf_cont⟩, hf : ∀ (g : (U : Subgroup (Gp p))) (x : Ω), ι (f g • x) = g • ι x⟩ :=
    exists_galois_restrict Γ (U : Subgroup (Gp p)) ι hU_fixes
  have h_dec (g : (U : Subgroup (Gp p))) : f g ∈ decompGroup Γ ((intQpBar p).comap ι) :=
    decompGroup.map hf (isLocalGalois_padic.mem_decompGroup (g : Gp p))
  -- Injective: two continuous automorphisms that agree on the dense image of `ι` agree.
  have h_inj (g g' : (U : Subgroup (Gp p))) (h_eq : f g = f g') : g = g' := by
    have h_agree (x : Ω) : (g : Gp p) • ι x = (g' : Gp p) • ι x :=
      calc (g : Gp p) • ι x = ι (f g • x) := (hf g x).symm
        _ = ι (f g' • x) := by rw [h_eq]
        _ = (g' : Gp p) • ι x := hf g' x
    have h_agree_all : ∀ y : PadicAlgCl p, (g : Gp p) • y = (g' : Gp p) • y :=
      (denseRange_emb_padicAlgCl ι).eq h_agree
    exact Subtype.coe_injective (eq_of_smul_eq_smul h_agree_all)
  -- Surjective: the range of `f` is closed, so it suffices that `σ` fixes every `x` fixed by it
  -- (`fixingSubgroup_fixedFieldOf`).
  have h_surj (σ : Γ) (hσ : σ ∈ decompGroup Γ ((intQpBar p).comap ι)) : σ ∈ f.range := by
    have hf_closed : IsClosed (X := Γ) f.range := (isCompact_range hf_cont).isClosed
    refine (fixingSubgroup_fixedFieldOf f.range).le fun ⟨x, hx⟩ ↦ ?_
    -- `ι x` is fixed by `U`, so it lies in `ℚ_p (ι K)`, which is inside the closure of `ι K`.
    have h_fixed_by_U (g : (U : Subgroup (Gp p))) : (g : Gp p) • ι x = ι x := by
      have hx_g : f g • x = x := hx ⟨f g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩
      calc (g : Gp p) • ι x = ι (f g • x) := (hf g x).symm
        _ = ι x := by rw [hx_g]
    have h_adjoin : ι x ∈ adjoin ℚ_[p] (range k) :=
      (fixedFieldOf_fixingSubgroup (Γ := Gp p) (adjoin ℚ_[p] (range k))).le h_fixed_by_U
    let T : IntermediateField ℚ_[p] (PadicAlgCl p) :=
      Subfield.toIntermediateField _ (padic_mem_topologicalClosure k.fieldRange)
    have h_closure : ι x ∈ closure (range k) :=
      (adjoin_le_iff (T := T)).mpr subset_closure h_adjoin
    exact smul_eq_self_of_mem_decompGroup_of_mem_closure ι hσ h_closure
  have h_bij : Function.Bijective (f.codRestrict _ h_dec) := by
    refine ⟨fun g g' h_eq ↦ h_inj g g' (congrArg Subtype.val h_eq), fun σ ↦ ?_⟩
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (h_surj σ σ.prop)
    exact ⟨g, Subtype.ext hg⟩
  let res : (U : Subgroup (Gp p)) ≃* decompGroup Γ ((intQpBar p).comap ι) :=
    .ofBijective (f.codRestrict _ h_dec) h_bij
  refine ⟨(U : Subgroup (Gp p)).subtype.comp res.symm, ⟨rfl, ?_⟩, ?_, ?_⟩
  · -- Write `g` as `res u`: it acts on `Ω` as `f u`, which matches `u` along `ι`.
    intro g x
    obtain ⟨u, rfl⟩ := res.surjective g
    calc ((U : Subgroup (Gp p)).subtype.comp res.symm) (res u) (ι x) = (u : Gp p) • ι x := by
          simp [AlgEquiv.smul_def]
      _ = ι (f u • x) := (hf u x).symm
  · -- a continuous bijection from a compact space to a Hausdorff space is a homeomorphism
    exact U.isOpen.isOpenEmbedding_subtypeVal.comp
      ((hf_cont.subtype_mk h_dec).homeoOfEquivCompactToT2 (f := res.toEquiv)).symm.isOpenEmbedding
  · -- The image is `U`, and fixing `ℚ_p (ι K)` is the same as fixing `ι K`.
    intro g
    have h_range :
        g ∈ ((U : Subgroup (Gp p)).subtype.comp res.symm.toMonoidHom).range ↔
          g ∈ (U : Subgroup (Gp p)) := by
      constructor
      · rintro ⟨σ, rfl⟩
        exact (res.symm σ).prop
      · intro hg
        exact ⟨res ⟨g, hg⟩, by simp⟩
    have h_fix :
        g ∈ (U : Subgroup (Gp p)) ↔ ∀ x : K, g (ι (algebraMap K Ω x)) = ι (algebraMap K Ω x) := by
      simp [U, ← AlgEquiv.smul_def, forall_mem_adjoin_smul_eq_self_iff, k]
    exact h_range.trans h_fix

end PadicDecomposition

/-!
## Places of number fields from p-adic embeddings

`New.placeOfEmb σ` is the prime induced by an embedding `σ`, and `New.LocField v` is the completion
at `v`.
-/

section CompletionEmbedding

open Valued Valuation Cohomology MulSemiringAction Fact

/-- A number field K together with a chosen embedding into the fixed algebraic closure `New.Ω`
of ℚ, given as an algebra structure. -/
class EmbeddedNumberField (K : Type*) [Field K] extends NumberField K, Algebra K Ω

/-- A number field with an algebra map into `Ω` is an embedded number field. -/
instance {K : Type*} [Field K] [NumberField K] [Algebra K Ω] : EmbeddedNumberField K where

variable {K : Type*} [Field K] [EmbeddedNumberField K] (v : FinPlace K)
  (p : ℕ) [f : Fact (Nat.Prime p)]
  (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω]

-- The instance binders `f` and `a` are named so that they can be passed to `IsCompletionEmb`.
variable (A : ClosurePlace) [a : Algebra (LocField v) (PadicAlgCl p)] (j : Ω →+* PadicAlgCl p)

/-- An embedding of the completion `K_v = LocField v` in `ℚ̄_p` (the algebra structure) and an
embedding `j : Ω → ℚ̄_p` that fit together: the first is continuous and induces the integers of
`K_v`, `j` agrees with it on `K`, and `j` pulls the integers of `ℚ̄_p` back to `A`. -/
structure IsPadicAt : Prop where
  /-- The map from `K_v` to `ℚ̄_p` is continuous. -/
  continuous : Continuous (algebraMap (LocField v) (PadicAlgCl p))
  /-- The integers of `ℚ̄_p` meet `K_v` (the `_`) in its ring of integers `LocInt v`. -/
  valRingBelow_eq : valRingBelow _ (intQpBar p) = LocInt v
  /-- The integers of `ℚ̄_p` pull back under `j` to `A`. -/
  comap_eq : (intQpBar p).comap j = A
  /-- On `K`, the embedding `j` agrees with the map through `K_v`. -/
  map_algebraMap (x : K) :
      j (algebraMap K Ω x) = algebraMap (LocField v) (PadicAlgCl p) (algebraMap K (LocField v) x)

/-- The decomposition group of `A` acts on `ℚ̄_p` as its Galois group over the completion
`LocField v`. The embedding of `LocField v` in `ℚ̄_p` is continuous and induces the integers
`LocInt v`. The map `j : Ω → ℚ̄_p` is an equivariant `K`-embedding that induces `A`. -/
class IsCompletionEmb extends MulSemiringAction (decompGroup Γ A) (PadicAlgCl p),
  IsLocalGalois (decompGroup Γ A) (LocField v) (intQpBar p), IsPadicAt v p A j where
  /-- The embedding `j` commutes with the action of the decomposition group. -/
  equivariant (g : decompGroup Γ A) (x : Ω) : j (g • x) = g • j x

variable {v p A}

/-- The place of `Ω` induced by an embedding `j` in `ℚ̄_p` lies over the prime of `K` induced by the
restriction of `j`. -/
lemma isPlaceOver_placeOfEmb :
    IsPlaceOver ((intQpBar p).comap j) (placeOfEmb (j.comp (algebraMap K Ω))) := by
  simp [IsPlaceOver, comap_apply_lt_one_iff]

open Pointwise in
/-- For `Ω` an algebraic closure of `ℚ`, every valuation subring `A` of `Ω` in which `p` has
valuation below `1` (`A p` is the valuation of `p` at `A`) is the preimage of the integers of
`ℚ̄_p` under some embedding `Ω → ℚ̄_p`. -/
lemma exists_comap_intQpBar_eq (h_val_lt_one : A p < 1) :
    ∃ e : Ω →+* PadicAlgCl p, (intQpBar p).comap e = A := by
  -- `A` and the place induced by any embedding `ι` both lie over the prime of `ℚ` above `p`, so
  -- they are conjugate under `Gal(Ω/ℚ)`, and a twist of `ι` induces `A`.
  obtain ⟨v, -, -, h_over : ∀ B : ClosurePlace, B.valuation p < 1 → IsPlaceOver B v⟩ :=
    exists_rat_place_of_prime (out : p.Prime)
  let ι : Ω →+* PadicAlgCl p := Classical.ofNonempty
  obtain ⟨g, hg⟩ : ∃ g : Gal(Ω/ℚ), g • (intQpBar p).comap ι = A :=
    (h_over _ (valuation_comap_intQpBar_lt_one ι)).exists_smul Gal(Ω/ℚ) (h_over A h_val_lt_one)
  exact ⟨ι.comp (toRingHom Gal(Ω/ℚ) Ω g⁻¹), smul_eq_comap.symm.trans hg⟩

/-- Let `Ω` be `New.Ω`, the algebraic closure of `ℚ`, let `Γ` be the Galois group of `Ω` over the
number field `K`, and let `A` be a place of `Ω`. Suppose the completion `LocField v` embeds
continuously in `ℚ̄_p` (the algebra instance `a`), and the integers of `ℚ̄_p` pull back to
`LocInt v`. Suppose also that `j : Ω → ℚ̄_p` agrees with this embedding on `K` and induces `A`
(together: `IsPadicAt`). Then the decomposition group of `A` acts on `ℚ̄_p`, compatibly with `j`,
as the Galois group of `ℚ̄_p` over `LocField v` (`IsCompletionEmb`). -/
lemma nonempty_isCompletionEmb_of_isPadicAt (h_at : IsPadicAt v p A j) :
    Nonempty (IsCompletionEmb v p Γ A j) := by
  -- The decomposition group acts through the open embedding `J` into the Galois group of `ℚ_p`. Its
  -- fixed field is local (`Period.isLocalGalois_of_isOpenEmbedding`); it remains to identify it
  -- with `LocField v`.
  have h_smul_cont : ContinuousSMul (LocField v) (PadicAlgCl p) :=
    continuousSMul_of_algebraMap _ _ h_at.continuous
  obtain ⟨J, ⟨-, hJ_equivariant : ∀ (g : decompGroup Γ A) (x : Ω), J g (j x) = j ((g : Γ) • x)⟩,
      hJ_open, hJ_range⟩ := exists_inducesPlace K Γ h_at.comap_eq
  let action : MulSemiringAction (decompGroup Γ A) (PadicAlgCl p) := compHom (PadicAlgCl p) J
  -- The image `C` of `LocField v` is a line over `LocField v`, so it is closed; a closed subfield
  -- contains `ℚ_p` (`padic_mem_topologicalClosure`).
  have h_image_closed :
      IsClosed (SetLike.coe (Algebra.linearMap (LocField v) (PadicAlgCl p)).range) :=
    Submodule.closed_of_finiteDimensional _
  have h_padic_mem (x : ℚ_[p]) :
      algebraMap ℚ_[p] (PadicAlgCl p) x ∈ (algebraMap (LocField v) (PadicAlgCl p)).fieldRange :=
    h_image_closed.closure_subset
      (padic_mem_topologicalClosure (algebraMap (LocField v) (PadicAlgCl p)).fieldRange x)
  let C : IntermediateField ℚ_[p] (PadicAlgCl p) :=
    (algebraMap (LocField v) (PadicAlgCl p)).fieldRange.toIntermediateField h_padic_mem
  -- `PadicAlgCl p` is Galois over `ℚ_p`, so over the intermediate field `C`, a copy of
  -- `LocField v`.
  have h_galois : IsGalois (LocField v) (PadicAlgCl p) :=
    isGalois_iff_isGalois_bot.mp (.tower_top_intermediateField C)
  -- The group fixes `K`, which is dense in `LocField v`.
  have h_smul_algebraMap (g : decompGroup Γ A) (y : LocField v) :
      g • algebraMap (LocField v) (PadicAlgCl p) y = algebraMap (LocField v) (PadicAlgCl p) y := by
    refine (v.denseRange_algebraMap K).induction_on y
      (isClosed_eq (h_at.continuous.const_smul (J g)) h_at.continuous) fun x ↦ ?_
    -- On `K` the map to `ℚ̄_p` is `j`, and `J g` moves `j x` as `g` moves `x`, which it fixes.
    show J g (algebraMap (LocField v) (PadicAlgCl p) (algebraMap K (LocField v) x)) = _
    simp [← h_at.map_algebraMap, hJ_equivariant]
  -- An automorphism fixing `C` fixes `K`, so it comes from the group; thus invariants lie in `C`.
  have h_invariant_mem (x : PadicAlgCl p) (hx : ∀ g : decompGroup Γ A, g • x = x) : x ∈ C := by
    refine (fixedFieldOf_fixingSubgroup (Γ := Gp p) C).le fun ⟨g, hg⟩ ↦ ?_
    have hg_fixes_K (y : K) : g (j (algebraMap K Ω y)) = j (algebraMap K Ω y) := by
      rw [h_at.map_algebraMap y]
      exact hg ⟨_, algebraMap K (LocField v) y, rfl⟩
    obtain ⟨g', rfl⟩ := MonoidHom.mem_range.mp ((hJ_range g).mpr hg_fixes_K)
    exact hx g'
  exact ⟨{ action, h_at, h_galois, Period.isLocalGalois_of_isOpenEmbedding hJ_open with
    commutes := ⟨fun g y z ↦ by simp [Algebra.smul_def, h_smul_algebraMap]⟩
    isInvariant := ⟨h_invariant_mem⟩
    isDiscreteValuationRing := by
      rw [h_at.valRingBelow_eq]
      infer_instance
    finite_residue := by
      rw [h_at.valRingBelow_eq]
      infer_instance
    equivariant g x := (hJ_equivariant g x).symm }⟩

/-- If the embedding of `LocField v` in `ℚ̄_p` and `j` fit together as in `IsPadicAt`, then the
residue field of `LocField v` for the integers of `ℚ̄_p` has `v.q` elements, the norm of `v`. -/
lemma IsPadicAt.residueCard_eq (h_at : IsPadicAt v p A j) :
    residueCard (LocField v) (intQpBar p) = v.q := by
  -- `rw!`: the ring also sits in the instance arguments, where plain `rw` cannot rewrite it.
  rw! [New.residueCard, h_at.valRingBelow_eq]
  exact card_ResField v

/-- Suppose the embedding of `LocField v` in `ℚ̄_p` and `j` fit together as in `IsPadicAt`. Then an
element of the completion at `v` is a uniformiser for the integers of `ℚ̄_p` exactly when its
`v`-adic valuation (written multiplicatively) is `exp (-1)`. -/
lemma IsPadicAt.isUniformiser_iff {π : LocField v} (h_at : IsPadicAt v p A j) :
    IsUniformiser (intQpBar p) π ↔ Valued.v π = WithZero.exp (-1) :=
  isUniformiser_iff_of_isEquiv ((isEquiv_iff_valuationSubring _ _).mpr h_at.valRingBelow_eq)
    ⟨(uniformizer v).val, v_uniformizer v⟩

/-- If the place `A` of `Ω` lies over the prime `v` of `K`, then for some prime `p` there are
embeddings of `K_v = LocField v` and of `Ω` in `ℚ̄_p`, the second inducing `A`, that make the
decomposition group of `A` the absolute Galois group of `K_v` (`IsCompletionEmb`). -/
lemma IsPlaceOver.exists_isCompletionEmb (h_over : IsPlaceOver A v) :
    ∃ (p : ℕ) (hp_prime : Fact (Nat.Prime p)) (h_algebra : Algebra (LocField v) (PadicAlgCl p))
        (j : Ω →+* PadicAlgCl p),
      Nonempty (IsCompletionEmb (f := hp_prime) (a := h_algebra) v p Γ A j) := by
  -- `v` lies over a prime `p`, so `A` is induced by an embedding `j` of `Ω` in `ℚ̄_p`, and `v` by
  -- the restriction of `j` to `K`.
  obtain ⟨p, -, -, hp_mem : (p : NumberField.RingOfIntegers K) ∈ v.asIdeal, hp : p.Prime, -⟩ :=
    v.asIdeal.exists_prime_and_absNorm_eq_pow
  have hp_fact : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, rfl⟩ : ∃ j : Ω →+* PadicAlgCl p, (intQpBar p).comap j = A :=
    exists_comap_intQpBar_eq (h_over.valuation_natCast_lt_one_iff.mpr hp_mem)
  obtain rfl : placeOfEmb (j.comp (algebraMap K Ω)) = v := (isPlaceOver_placeOfEmb j).unique h_over
  -- That restriction extends to a continuous `φ` on the completion inducing its valuation.
  obtain ⟨φ, hφ_cont,
      hφ_ext : ∀ x : K,
        φ (algebraMap K (LocField (placeOfEmb (j.comp (algebraMap K Ω)))) x) = j (algebraMap K Ω x),
      -, hφ_val⟩ := exists_placeOfEmb_extension (j.comp (algebraMap K Ω))
  algebraize [φ]
  -- Both rings consist of the elements of valuation at most `1`, for equivalent valuations.
  have h_ring : valRingBelow (LocField (placeOfEmb (j.comp (algebraMap K Ω)))) (intQpBar p) =
      LocInt (placeOfEmb (j.comp (algebraMap K Ω))) := by
    ext x
    simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      RingHom.algebraMap_toAlgebra] using hφ_val x 1
  have h_at : IsPadicAt (placeOfEmb (j.comp (algebraMap K Ω))) p ((intQpBar p).comap j) j :=
    ⟨hφ_cont, h_ring, rfl, fun x ↦ (hφ_ext x).symm⟩
  exact ⟨p, hp_fact, φ.toAlgebra, j, nonempty_isCompletionEmb_of_isPadicAt Γ j h_at⟩

end CompletionEmbedding

/-!
## The decomposition group as a local Galois group; orders and towers

For a map `x : G → M` with `x(gk) = x(g) + a(g)x(k)`, the zero set of `x` is a subgroup when `a` is
a monoid homomorphism (`New.cocycleKer`).

For a place `A` of `Ω` over the prime `v` of `K`, the field fixed by `decompGroup Γ A` is a local
field with the residue field of `v`.
-/

section DecompositionLocal

/-! ### Maps with the cocycle relation -/

variable {G : Type*} {R : Type*} {M : Type*} [Group G] [AddCommGroup M] {a : G → R} {x : G → M}

/-- For x : G → M with the cocycle relation c : x(gk) = x(g) + a(g)x(k), where a : G → R is a
monoid homomorphism, the subgroup of the g with x(g) = 0. -/
def cocycleKer [Monoid R] [DistribMulAction R M] (a : G →* R)
    (c : ∀ g k : G, x (g * k) = x g + a g • x k) : Subgroup G :=
  Subgroup.ofDiv (x ⁻¹' {0})
    -- `x 1 = x 1 + x 1` gives `x 1 = 0`
    ⟨1, by simpa using c 1 1⟩
    -- `x g = x (g * k⁻¹) + a (g * k⁻¹) • x k`, with `x g = 0` and `x k = 0`
    (fun g (hg : x g = 0) k (hk : x k = 0) ↦ by simpa [hg, hk, eq_comm] using c (g * k⁻¹) k)

variable [Ring R] [Module R M]

/-- Sah's lemma. Let x : G → M satisfy the cocycle relation c : x(gk) = x(g) + a(g)x(k), with
scalars a(g) in the ring R. If x vanishes at (γg)⁻¹(gγ), then (a(γ) − 1)x(g) = (a(g) − 1)x(γ). -/
lemma sah (c : ∀ g k : G, x (g * k) = x g + a g • x k) (γ g : G)
    (h_zero : x ((γ * g)⁻¹ * (g * γ)) = 0) : (a γ - 1) • x g = (a g - 1) • x γ := by
  -- The hypothesis gives `x (g * γ) = x (γ * g)`; expand both sides by the cocycle rule.
  have h_comm : x (g * γ) = x (γ * g) := by
    rw [← mul_inv_cancel_left (γ * g) (g * γ), c, h_zero, smul_zero, add_zero]
  have h_expand : x g + a g • x γ = x γ + a γ • x g := by
    rw [← c g γ, ← c γ g, h_comm]
  rw [sub_smul, sub_smul, one_smul, one_smul, sub_eq_sub_iff_add_eq_add]
  simpa only [add_comm] using h_expand.symm

/-- Let x : G → M satisfy the cocycle relation c : x(gk) = x(g) + a(g)x(k), with scalars a(g) in
the ring R. If a(g) fixes x(γ⁻¹), then x(γgγ⁻¹) = a(γ)x(g). -/
lemma cocycle_conj_eq_smul (c : ∀ g k : G, x (g * k) = x g + a g • x k) {g γ : G}
    (h_fix : a g • x γ⁻¹ = x γ⁻¹) : x (γ * g * γ⁻¹) = a γ • x g := by
  -- Expand `x (γ * (g * γ⁻¹))` by the cocycle relation twice; `a g` fixes `x γ⁻¹`.
  have h_expand : x (γ * g * γ⁻¹) = x γ + a γ • x g + a γ • x γ⁻¹ := by
    rw [mul_assoc, c γ (g * γ⁻¹), c g γ⁻¹, h_fix, smul_add, add_assoc]
  -- `x γ + a γ • x γ⁻¹ = x (γ * γ⁻¹) = x 1`, which vanishes.
  have h_one : x γ + a γ • x γ⁻¹ = 0 := by
    grind [smul_add, mul_assoc, mul_inv_cancel, c 1 g, c 1 γ⁻¹, c γ γ⁻¹]
  rw [h_expand, add_right_comm, h_one, zero_add]

namespace IsPlaceOver

open NumberField Pointwise Rat Units DiscreteUnits Ideal WithZero Cohomology IsLocalRing RingHom
  Valuation

variable (Γ : Type*)
  {K : Type*} [Group Γ] [TopologicalSpace Γ] [Field K] [EmbeddedNumberField K]
  [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω]
  {A : ClosurePlace} {v : FinPlace K}

/-! ### The decomposition field -/

/-- Let the place A of Ω lie over the prime v of K (an integer of K is in the maximal ideal of A
exactly when it lies in v), and let F be the field fixed by the decomposition group of A, its
stabiliser in Γ. Then F is a henselian local field for A (`IsLocalGalois`), whose residue field has
`v.q` elements, the norm of v, and uniformisers of K (`IsUniformiser A`: uniformisers of the
valuation ring `A ∩ K`) stay uniformisers of `A ∩ F`. -/
lemma isLocalGalois_and_residueCard_eq_and_isUniformiser (h : IsPlaceOver A v) :
    IsLocalGalois (decompGroup Γ A) (fixedFieldOf (decompGroup Γ A)) A ∧
    residueCard (fixedFieldOf (decompGroup Γ A)) A = v.q ∧
    ∀ {π : Kˣ}, IsUniformiser A π.val →
      IsUniformiser A (π.map (algebraMap K (fixedFieldOf (decompGroup Γ A))).toMonoidHom).val := by
  -- Embed `Ω` in `ℚ̄_p` by an equivariant `j` inducing `A`, such that the decomposition group acts
  -- on `ℚ̄_p` as its Galois group over the completion `LocField v` (`IsCompletionEmb`). The fixed
  -- field `F` then maps into `LocField v`, and everything is read off from the valuation of
  -- `LocField v`.
  obtain ⟨p, hp_prime, h_algebra, j, ⟨hj⟩⟩ := h.exists_isCompletionEmb Γ
  let F : IntermediateField K Ω := fixedFieldOf (decompGroup Γ A)
  -- `j` sends `F` to the elements fixed by `decompGroup Γ A`, which form a copy of `LocField v`.
  have h_fixed (x : Ω) (hx : x ∈ F) :
      j x ∈ FixedPoints.subsemiring (PadicAlgCl p) (decompGroup Γ A) :=
    fun g ↦ by simp [← hj.equivariant, hx g]
  let φ : F →+* LocField v := comp hj.ringEquivFixedPoints.symm.toRingHom (j.restrict F _ h_fixed)
  have hφ (x : K) : φ (algebraMap K F x) = algebraMap K (LocField v) x := by
    -- In `ℚ̄_p` both sides are `j x`.
    have h_image :
        algebraMap (LocField v) (PadicAlgCl p) (φ (algebraMap K F x)) = j (algebraMap K Ω x) := by
      aesop
    exact RingHom.injective _ (h_image.trans (hj.map_algebraMap x))
  have h_val (x : K) : Valued.v.comap φ (algebraMap K F x) = v.valuation K x := by
    rw [comap_apply, hφ, v_algebraMap_eq_valuation]
  -- The valuation ring `A ∩ F` is the preimage of `LocInt v` under `φ`.
  have h_ring : valRingBelow F A = (Valued.v.comap φ).valuationSubring := by
    ext x
    have h_mem : φ x ∈ valRingBelow (LocField v) (intQpBar p) ↔ φ x ∈ LocInt v := by
      rw [hj.valRingBelow_eq]
    simpa [← hj.comap_eq, φ, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      using h_mem
  -- The residue fields agree, since integers of `K` already give every residue of `LocInt v`.
  let ψ : valRingBelow F A →+* ResField v := comp (residue _) (φ.restrict _ _ h_ring.le)
  have hψ : Function.Surjective ψ := by
    -- Every residue of `LocInt v` is that of an integer `x` of `K`, and `x` lies in `A ∩ F`.
    refine (algebraMap_ResField_surjective v).forall.mpr fun x ↦
      ⟨⟨algebraMap K F x, algebraMap_ringOfIntegers_mem _ x⟩, ?_⟩
    exact congrArg (residue (LocInt v)) (Subtype.ext (hφ x))
  have res_equiv : (valRingBelow F A ⧸ maximalIdeal (valRingBelow F A)) ≃ ResField v := by
    rw [← ker_eq_maximalIdeal ψ hψ]
    exact (quotientKerEquivOfSurjective hψ).toEquiv
  -- A uniformiser `π₀` at `v` makes the valuation of `F` nontrivial; hence `A ∩ F` is discrete.
  obtain ⟨π₀, hπ₀⟩ := v.valuation_exists_uniformizer K
  have h_nontrivial : (Valued.v.comap φ).IsNontrivial := ⟨algebraMap K F π₀, by simp [h_val, hπ₀]⟩
  have h_local : IsLocalGalois (decompGroup Γ A) F A :=
    { mem_decompGroup := fun g ↦ g.property
      isDiscreteValuationRing := by
        rw [h_ring]
        infer_instance
      finite_residue := .of_equiv _ res_equiv.symm }
  have h_card : residueCard F A = v.q := (Nat.card_congr res_equiv).trans (card_ResField v)
  refine ⟨h_local, h_card, fun {π} hπ ↦ ?_⟩
  -- In `K` and in `F` alike, a uniformiser is an element of `v`-adic valuation `exp (-1)`.
  have hπ_val : Valued.v.comap φ (algebraMap K F π) = exp (-1) :=
    (h_val π).trans (h.isUniformiser_iff.mp hπ)
  have h_equiv : (A.valuation.comap (algebraMap F Ω)).IsEquiv (Valued.v.comap φ) :=
    (isEquiv_iff_valuationSubring _ _).mpr h_ring
  exact (isUniformiser_iff_of_isEquiv h_equiv ⟨_, hπ_val⟩).mpr hπ_val

/-- If A lies over v, the decomposition group of A is the Galois group of Ω over its fixed field F,
and F is a henselian local field for A: A ∩ F is a discrete valuation ring with finite residue
field. -/
lemma isLocalGalois_decompGroup (h : IsPlaceOver A v) :
    IsLocalGalois (decompGroup Γ A) (fixedFieldOf (decompGroup Γ A)) A := by
  exact (h.isLocalGalois_and_residueCard_eq_and_isUniformiser Γ).left

/-- If A lies over v, the residue field of the field fixed by the decomposition group of A has
`v.q` elements, as many as that of v. -/
lemma residueCard_fixedFieldOf_decompGroup (h : IsPlaceOver A v) :
    residueCard (fixedFieldOf (decompGroup Γ A)) A = v.q := by
  obtain ⟨-, h_card, -⟩ := h.isLocalGalois_and_residueCard_eq_and_isUniformiser Γ
  exact h_card

/-- If A lies over v, an element of K that is a uniformiser for A is still a uniformiser in the
field fixed by the decomposition group of A. -/
lemma isUniformiser_map_fixedFieldOf_decompGroup (h : IsPlaceOver A v) {π : Kˣ}
    (hπ : IsUniformiser A π.val) :
    IsUniformiser A (π.map (algebraMap K (fixedFieldOf (decompGroup Γ A))).toMonoidHom).val := by
  obtain ⟨-, -, h_unif⟩ := h.isLocalGalois_and_residueCard_eq_and_isUniformiser Γ
  exact h_unif hπ

/-- If A lies over v, some π in Kˣ has v-adic valuation `exp (-1)` and is a uniformiser for A in
the field fixed by the decomposition group of A. -/
lemma exists_uniformiser (h : IsPlaceOver A v) :
    ∃ π : Kˣ,
      v.valuation K π = exp (-1) ∧
      IsUniformiser A (π.map (algebraMap K (fixedFieldOf (decompGroup Γ A))).toMonoidHom).val := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hπ_ne : π ≠ 0 := by grind [exp_pos]
  exact ⟨mk0 π hπ_ne, hπ,
    h.isUniformiser_map_fixedFieldOf_decompGroup Γ (h.isUniformiser_iff.mpr hπ)⟩

/-- If A lies over v, the order on Ωˣ normalised on the field fixed by the decomposition group of A
agrees with the order normalised on K. -/
lemma ordRat_fixedFieldOf_decompGroup (h : IsPlaceOver A v) :
    ordRat (fixedFieldOf (decompGroup Γ A)) A = ordRat K A := by
  -- Both sides are chosen by a property quantified over uniformisers; the two properties agree.
  obtain ⟨π₀, hπ₀_val, hπ₀⟩ := h.exists_uniformiser Γ
  unfold ordRat
  congr! with f
  constructor
  · -- A uniformiser of `K` stays a uniformiser in the fixed field.
    exact fun hf π hπ ↦ hf _ (h.isUniformiser_map_fixedFieldOf_decompGroup Γ hπ)
  · -- A uniformiser `π` of the fixed field has the same valuation as the uniformiser `π₀` of `K`.
    intro hf π hπ
    have h_val : valuationVia K A π₀ = valuationVia (fixedFieldOf (decompGroup Γ A)) A π :=
      ((hπ _).mp hπ₀.valuationVia_lt_one).antisymm ((hπ₀ _).mp hπ.valuationVia_lt_one)
    rw [← h_val]
    exact hf π₀ (h.isUniformiser_iff.mpr hπ₀_val)

/-- If A lies over v, then Γ contains an arithmetic Frobenius at A: an element that stabilises A
and acts as x ↦ x ^ v.q modulo the maximal ideal of A (`IsFrob`). -/
lemma exists_isFrob (h : IsPlaceOver A v) : ∃ φ : Γ, IsFrob A v.q φ := by
  -- A Frobenius of the decomposition field, for its residue order `v.q`, is one in `Γ`.
  obtain ⟨φ, hφ⟩ :
      ∃ φ : decompGroup Γ A, IsFrob A (residueCard (fixedFieldOf (decompGroup Γ A)) A) φ :=
    (h.isLocalGalois_decompGroup Γ).frobenius_spec.left
  rw [h.residueCard_fixedFieldOf_decompGroup Γ] at hφ
  exact ⟨φ, hφ⟩

/-! ### The normalised order -/

/-- If A lies over v, an element x of Ωˣ (written additively) has order 0 at A, for the order
normalised on K, exactly when its valuation at A is 1. -/
lemma ordRat_eq_zero_iff (h : IsPlaceOver A v) {x : DiscreteUnits Ω} :
    ordRat K A x = 0 ↔ A x.toMul = 1 := by
  rw [← h.ordRat_fixedFieldOf_decompGroup Gal(Ω/K)]
  exact (h.isLocalGalois_decompGroup Gal(Ω/K)).ordRat_eq_zero

/-- If A lies over v, an element x of Ωˣ (written additively) has nonnegative order at A, for the
order normalised on K, exactly when x lies in the valuation ring A. -/
lemma ordRat_nonneg_iff (h : IsPlaceOver A v) (x : DiscreteUnits Ω) :
    0 ≤ ordRat K A x ↔ ↑x.toMul ∈ A := by
  obtain ⟨π, -, hπ⟩ := h.exists_uniformiser Gal(Ω/K)
  -- Write the order of `x` as `r.num / r.den`; then `x ^ r.den` has the valuation of `π ^ r.num`.
  set r : ℚ := ordRat K A x
  have h_pow : A x.toMul ^ r.den = valuationVia K A π ^ r.num :=
    (hπ.valuation_pow_eq_zpow_iff_mul_ordRat_eq (h.isLocalGalois_decompGroup Gal(Ω/K)) r.den
      r.num).mpr <|
      by rw [h.ordRat_fixedFieldOf_decompGroup Gal(Ω/K), den_mul_eq_num]
  -- As the valuation of `π` lies in `(0, 1)`, this valuation is `≤ 1` iff `0 ≤ r.num`.
  have h_le : A x.toMul ^ r.den ≤ 1 ↔ 0 ≤ r.num := by
    rw [h_pow]
    exact zpow_le_one_iff_right_of_lt_one₀ (by simp [pos_iff]) hπ.valuationVia_lt_one
  -- Finally `0 ≤ r ↔ 0 ≤ r.num`, and `A x ^ r.den ≤ 1 ↔ A x ≤ 1`, which says `x ∈ A`.
  rw [← Rat.num_nonneg, ← h_le, pow_le_one_iff r.den_nz]
  exact A.valuation_le_one_iff _

variable {Γ}

/-- Let `K` be a number field inside the field `Ω` (the fixed algebraic closure of ℚ), `Γ` the
Galois group of `Ω/K`, and `A` a place of `Ω` over the prime `v` of `K`. For x in Kˣ, the order
at A, normalised on K, of the image `ofBase` of x in Ωˣ is minus the logarithm of the v-adic
valuation of x. -/
lemma ordRat_ofBase (h : IsPlaceOver A v) (x : Kˣ) :
    ordRat K A (ofBase Γ Ω (Additive.ofMul x)) = -(v.valuation K x).log := by
  -- With `π` a uniformiser and `a = -log (v x)`, the elements `x` and `π ^ a` have equal valuation.
  obtain ⟨π, hπ, h_unif⟩ := h.exists_uniformiser Γ
  set a : ℤ := -(v.valuation K x).log
  -- `v (π ^ a) = exp (-1) ^ a = exp (-a) = exp (log (v x)) = v x`.
  have h_val : v.valuation K x = v.valuation K (π ^ a) := by
    rw [map_zpow₀, hπ, ← exp_zsmul, _root_.smul_eq_mul, mul_neg_one]
    simp [a, exp_log]
  -- By `IsUniformiser.valuation_pow_eq_zpow_iff_mul_ordRat_eq` with exponent `1`, the order of `x`
  -- is `a`.
  have h_ord_eq :
      ((1 : ℕ) : ℚ) * ordRat (fixedFieldOf (decompGroup Γ A)) A (ofBase Γ Ω (.ofMul x)) = a := by
    apply (h_unif.valuation_pow_eq_zpow_iff_mul_ordRat_eq (h.isLocalGalois_decompGroup Γ) 1 a).mp
    -- `ofBase` is the map `K → Ω` on units, and the fixed field sits between `K` and `Ω`.
    have h_image : ((ofBase Γ Ω (.ofMul x) : DiscreteUnits Ω).toMul : Ω) = algebraMap K Ω x := rfl
    simpa [h_image, valuationVia, ← IsScalarTower.algebraMap_apply] using
      h.isEquiv.eq_iff.mpr h_val
  simpa [a, h.ordRat_fixedFieldOf_decompGroup Γ] using h_ord_eq

/-- Let A lie over v. For g ∈ Γ and x ∈ Ωˣ, the order (normalised on K) of gx (`unitsRep g x`) at
the place gA equals the order of x at A. -/
lemma ordRat_smul (h : IsPlaceOver A v) (g : Γ) (x : DiscreteUnits Ω) :
    ordRat K (g • A) (unitsRep g x) = ordRat K A x := by
  -- Compare both sides with each rational `q`: the inequality `q ≤ ord x` says that
  -- `y = x ^ q.den / π ^ q.num` has nonnegative order, for a uniformiser `π` of `K`.
  obtain ⟨π, hπ, -⟩ := h.exists_uniformiser Γ
  refine eq_of_forall_le_iff fun q ↦ ?_
  let y : DiscreteUnits Ω := q.den • x - q.num • ofBase Γ Ω (.ofMul π)
  -- By `ordRat_nonneg_iff` this is integrality, and `g y ∈ g • A` exactly when `y ∈ A`.
  have h_int : 0 ≤ ordRat K (g • A) (unitsRep g y) ↔ 0 ≤ ordRat K A y := by
    rw [(h.smul g).ordRat_nonneg_iff, h.ordRat_nonneg_iff]
    exact A.smul_mem_pointwise_smul_iff
  -- Expand: `g` fixes `π`, which has order `1` at `A` and at `g • A`; then cancel `q.den`.
  have h_fix_π : unitsRep g (ofBase Γ Ω (.ofMul π) : DiscreteUnits Ω) = ofBase Γ Ω (.ofMul π) :=
    (ofBase Γ Ω (.ofMul π)).property g
  have h_ord_y : ordRat K A y = q.den * ordRat K A x - q.num := by
    simp [y, h.ordRat_ofBase, hπ]
  have h_ord_gy :
      ordRat K (g • A) (unitsRep g y) = q.den * ordRat K (g • A) (unitsRep g x) - q.num := by
    simp [y, h_fix_π, (h.smul g).ordRat_ofBase, hπ]
  rw [h_ord_gy, h_ord_y] at h_int
  -- Cancel `q.den > 0`: `q ≤ t` exactly when `0 ≤ q.den * t - q.num`.
  simpa [pos, ← den_mul_eq_num] using h_int

/-- Let A lie over v. If x in Ωˣ is fixed by every element of the inertia group of A, then the
order of x at A, normalised on K, is an integer. -/
lemma exists_ordRat_eq_intCast (h : IsPlaceOver A v) {x : DiscreteUnits Ω}
    (hx : ∀ g ∈ inertiaGroup Γ A, unitsRep g x = x) : ∃ n : ℤ, ordRat K A x = n := by
  rw [← h.ordRat_fixedFieldOf_decompGroup Γ]
  -- Inertia of `A` inside the decomposition group is inertia of `A` in `Γ`.
  exact (h.isLocalGalois_decompGroup Γ).exists_ordRat_eq_intCast fun g hg ↦ hx g hg

/-! ### Towers and generation of the decomposition group -/

/-- Let `L / K` be number fields embedded in `Ω` (`EmbeddedNumberField`), with `U`, open in `Γ`, the
Galois group of `Ω / L`; let `A` lie over `v` in `K` and over `w` in `L`; `e` and `f = inertiaDeg`
are the ramification index and residue degree of `w` over `K`. If the decomposition group lies in
`U`, the residue fields have the same order and `ordRat L A = ordRat K A`, where `ordRat K A` is a
chosen additive order `Ωˣ → ℚ` for the valuation of `A`, normalised so that uniformisers of `K` have
order 1. If inertia lies in `U`, then `e = 1`. The index of `U ⊓ decompGroup Γ A` in
`decompGroup Γ A` is `e * f`. -/
lemma ramification_in_tower (h : IsPlaceOver A v) (U : Subgroup Γ) [hU_open : Fact U.IsOpen]
    {L : Type*} [Field L] [EmbeddedNumberField L] [IsProGalois U L Ω] [Algebra K L]
    [IsScalarTower K L Ω] {w : FinPlace L} (hw : IsPlaceOver A w) :
    let e := w.asIdeal.ramificationIdx (𝓞 K)
    (decompGroup Γ A ≤ U → w.q = v.q ∧ ordRat L A = ordRat K A) ∧
    (inertiaGroup Γ A ≤ U → e = 1) ∧
    U.relIndex (decompGroup Γ A) = e * w.asIdeal.inertiaDeg (𝓞 K) := by
  -- Pass to the decomposition fields, which are local. For the open subgroup
  -- `V = U ∩ decompGroup Γ A`, `IsLocalGalois.of_finite` gives `e`, `f` with `e * f = V.index`,
  -- `q' = q ^ f`, `ord' = e • ord`, and `e = 1` if inertia lies in `V`; then identify `e` and
  -- `f` with the ramification index and the residue degree of `w`.
  -- `A` lies over the prime of `K` below `w`, which is therefore `v`.
  have h_below : v = w.below K := h.unique hw.isPlaceOver_below
  have h_lies : w.asIdeal.LiesOver v.asIdeal := by
    rw [h_below]
    exact ⟨rfl⟩
  obtain ⟨π, hπ, -⟩ := h.exists_uniformiser Γ
  -- `id` keeps `V` folded, so that instance search finds the Galois structure over its fixed field.
  let V : OpenSubgroup (decompGroup Γ A) := id ⟨U.subgroupOf _, hU_open.out.preimage_val⟩
  obtain ⟨-, ⟨e, f, ⟨h_ef, hq, h_ord⟩, h_unram⟩, -⟩ :=
    (h.isLocalGalois_decompGroup Γ).of_finite V
  -- The fixed field of `V` is the decomposition field of `A` over `L`.
  have h_same_set : (fixedFieldOf (decompGroup U A) : Set Ω) =
      fixedFieldOf (U.subgroupOf (decompGroup Γ A)) := by aesop
  -- `erw` here and in the next two steps: the two fields are equal as sets only, so the rewrites
  -- go through a copy of the field, equal to it by definition.
  erw [← (fixedFieldOf (U.subgroupOf _)).copy_eq (fixedFieldOf (decompGroup U A)) h_same_set]
    at hq h_ord
  have h_q : w.q = v.q ^ f := by
    erw [← h.residueCard_fixedFieldOf_decompGroup Γ, ← hw.residueCard_fixedFieldOf_decompGroup U,
      hq]
  have h_ord_L : ordRat L A = e • ordRat K A := by
    erw [← h.ordRat_fixedFieldOf_decompGroup Γ, ← hw.ordRat_fixedFieldOf_decompGroup U, h_ord]
  have h_norm : v.q ^ w.asIdeal.inertiaDeg (𝓞 K) = w.q :=
    absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
  obtain rfl : w.asIdeal.inertiaDeg (𝓞 K) = f :=
    Nat.pow_right_injective v.one_lt_q (h_norm.trans h_q)
  -- The order in `L` of the uniformiser `π` of `K` is `e`, and is the ramification index.
  have hπ_image : (ofBase Γ Ω (.ofMul π) : DiscreteUnits Ω) =
      ofBase U Ω (.ofMul (π.map (algebraMap K L).toMonoidHom)) :=
    ext (IsScalarTower.algebraMap_apply K L Ω π)
  have hπL : ordRat L A (ofBase Γ Ω (.ofMul π)) = -(w.valuation L (algebraMap K L π)).log := by
    simpa [hπ_image] using hw.ordRat_ofBase (π.map (algebraMap K L).toMonoidHom)
  have h_ord_π_L : ordRat L A (ofBase Γ Ω (.ofMul π)) = e := by
    simp [h_ord_L, h.ordRat_ofBase, hπ]
  have h_log :
      -((w.valuation L (algebraMap K L π)).log : ℚ) = w.asIdeal.ramificationIdx (𝓞 K) := by
    simp [← v.valuation_liesOver L, hπ]
  obtain rfl : e = w.asIdeal.ramificationIdx (𝓞 K) := by
    exact_mod_cast h_ord_π_L.symm.trans (hπL.trans h_log)
  -- If `U` contains inertia, so does `V`, and then `e = 1`.
  refine ⟨fun hU ↦ ?_, fun hI ↦ h_unram fun g hg ↦ hI hg, h_ef.symm⟩
  -- If `decompGroup Γ A ≤ U`, the index `e * f` is `1`, so `e = f = 1`.
  obtain ⟨h_e, h_f⟩ := mul_eq_one.mp (h_ef.trans (U.relIndex_eq_one.mpr hU))
  simp [h_q, h_ord_L, h_e, h_f]

/-- Let `A` lie over `v` in `K` and over `w` in `L`, where `U`, open in `Γ`, is the Galois group of
`Ω / L`. If `U` contains the inertia group of `A`, then `w` is unramified over `K`. -/
lemma ramificationIdx_eq_one_of_inertiaGroup_le (h : IsPlaceOver A v) (U : Subgroup Γ)
    [Fact U.IsOpen] {L : Type*} [Field L] [EmbeddedNumberField L] [IsProGalois U L Ω] [Algebra K L]
    [IsScalarTower K L Ω] {w : FinPlace L} (hw : IsPlaceOver A w) (hI : inertiaGroup Γ A ≤ U) :
    w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  obtain ⟨-, h_unram, -⟩ := h.ramification_in_tower U hw
  exact h_unram hI

/-- Let `A` lie over `v` in `K` and over `w` in `L`, where `U`, open in `Γ`, is the Galois group of
`Ω / L`. The index of `U ⊓ decompGroup Γ A` in `decompGroup Γ A` is the ramification index times
the residue degree of `w` over `K`. -/
lemma relIndex_decompGroup_eq (h : IsPlaceOver A v) (U : Subgroup Γ) [Fact U.IsOpen] {L : Type*}
    [Field L] [EmbeddedNumberField L] [IsProGalois U L Ω] [Algebra K L] [IsScalarTower K L Ω]
    {w : FinPlace L} (hw : IsPlaceOver A w) :
    U.relIndex (decompGroup Γ A) =
      w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) := by
  obtain ⟨-, -, h_index⟩ := h.ramification_in_tower U hw
  exact h_index

/-- Let A lie over v. An open subgroup of `Γ` that contains the inertia group of `A` and a
Frobenius element `φ` at `v` (`IsFrob A v.q φ`: `φ` stabilises `A` and acts as x ↦ x ^ v.q modulo
its maximal ideal) contains the whole decomposition group. -/
lemma decompGroup_le (h : IsPlaceOver A v) {φ : Γ} (hφ : IsFrob A v.q φ) {U : Subgroup Γ}
    (hU : U.IsOpen) (hI : inertiaGroup Γ A ≤ U) (hφU : φ ∈ U) : decompGroup Γ A ≤ U := by
  -- The products `φ ^ n * i` with `i` in inertia lie in `U` and are dense in `decompGroup Γ A`, and
  -- the open subgroup `U` is closed.
  -- `φ` as an element of the decomposition group, where it is a Frobenius for the residue order.
  let φ' : decompGroup Γ A := ⟨φ, hφ.left⟩
  have hφ' : IsFrob A (residueCard (fixedFieldOf (decompGroup Γ A)) A) φ' := by
    rwa [h.residueCard_fixedFieldOf_decompGroup Γ]
  obtain ⟨-, h_gen, -⟩ := (h.isLocalGalois_decompGroup Γ).frobenius_spec
  have h_dense : DenseRange fun p : ℕ × inertiaGroup (decompGroup Γ A) A ↦
      φ' ^ p.fst * (p.snd : decompGroup Γ A) :=
    h_gen hφ'
  have h_closed : IsClosed {g : decompGroup Γ A | (g : Γ) ∈ U} :=
    (U.isClosed_of_isOpen hU).preimage_val
  have h_mem (p : ℕ × inertiaGroup (decompGroup Γ A) A) :
      ((φ' ^ p.fst * p.snd : decompGroup Γ A) : Γ) ∈ U := by
    simpa using U.mul_mem (U.pow_mem hφU p.fst) (hI p.snd.property)
  intro g hg
  exact isClosed_property h_dense h_closed h_mem ⟨g, hg⟩

end IsPlaceOver

end DecompositionLocal

end New
