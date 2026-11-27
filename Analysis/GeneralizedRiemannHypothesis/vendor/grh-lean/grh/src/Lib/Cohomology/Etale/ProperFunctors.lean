import Lib.Cohomology.Etale.EllAdicCohomology
import Lib.Cohomology.Etale.RelativeChains
import Lib.General.Geometry.GeometricPoints
import Lib.General.Geometry.PointsOfProperSchemes

/-!
# Local-to-global principle, density criteria and proper functors for cohomology on test rings

This file studies the cohomology `Hⁿ(Y) = Extⁿ(ℤ[Y], F)` of set-valued functors `Y` on rings,
computed on test rings, with `F = New.Variety.locConstCoeff Λ` the locally constant `Λ`-valued
functions. Two criteria for density, for affine maps and for finitely many affine subfunctors, are
tested on points in valuation rings of algebraically closed fields.

## Main definitions and results

* `New.Variety.IsTestCohomEquiv.of_connected`: the local-to-global principle. A map
  `u : X ⟶ Y` that induces isomorphisms on cohomology (`New.Variety.IsTestCohomEquiv`) over every
  connected piece of `Y` induces them over `Y`. This needs `X` and `Y` cohomologically continuous
  (`New.Variety.IsCohomContinuous`). The pieces are loci `U a` of a zero-locus family `U` with
  `U (span {e}) ⊔ U (span {1 - e})` dense for every idempotent `e`.
* `New.Variety.IsRelAffine.hasCohomDenseImage_of_lifts`: an affine map that is onto on such points
  has dense image.
* `New.Variety.IsCohomDense.of_affine_cover`: `U` is dense if each such point lies in one of
  finitely many affine subfunctors whose points in test rings belong to `U`.
* `New.Variety.IsProperOver.hasCohomDenseImage_of_surjective`: a map of proper functors, onto on
  geometric points, has dense image (`New.Variety.IsCohomDense`) for locally constant coefficients
  `New.Variety.locConstCoeff Λ`.
* A density criterion for finitely many maps `P i : Y ⟶ Z` into a proper functor:
  `New.Variety.IsProperOver.isCohomDense_of_coincidences`. It is
  `New.Variety.IsCohomDense.of_affine_cover` for the closed loci on which prescribed pairs of the
  maps agree.
* `New.Variety.ellAdicCohom.transfer`: let `c : W ⟶ Y` be a Galois covering of proper schemes with
  finite group `Δ`. Then the `ℓ`-adic cohomology of `Y` embeds in that of `W` and reaches all
  `Δ`-invariant classes.

Notions from other files:
* `New.Variety.IsRelAffine`: The property of a map X → Y of set-valued functors on rings that its
  pull-back along every point h_A → Y is representable, of the form h_B → h_A.
* `New.Variety.IsCohomDense`: The subfunctor U of Y is dense for F: for every point h_A → Y, the
  inclusion of the preimage of U in h_A is an equivalence for F.
* `New.Variety.reprBy`: The functor h_A = Hom(A,−) represented by the object A.
* `New.Variety.IsTest`: a test ring A is reduced and absolutely integrally closed, and any a, b ∈ A
  admit an idempotent e with a ∣ eb and b ∣ (1 − e)a.
* `New.Variety.IsProperOver`: The functor Z on rings is proper over D: its diagonal is closed, and
  it satisfies a valuative criterion for valuation rings of algebraically closed fields.
* `New.Variety.locConstCoeff`: For an abelian group Λ, the coefficient functor on test rings sending
  A to the group of locally constant functions Spec A → Λ.

## Relation to the literature

Known; see `Lib.Cohomology.Etale.FilteredLimits` and `Lib.Cohomology.ProperBaseChange.Theorem` for
sources.
-/

/-!
## Zorn's lemma, Mayer–Vietoris and reduction to connected pieces

The local-to-global principle is proved by Zorn's lemma over the ideals of a ring `R` and by
Mayer–Vietoris for subfunctors `U, V ≤ W` of a set-valued functor `Y` with `U ⊔ V` dense in `W`.
Here `U.whisker testIncl` is `U` restricted to test rings, `homOfLe h` is the inclusion map given
by `h : U ≤ W`, and `TestCohomology.map Λ f n` is the pull-back `Hⁿ(W) → Hⁿ(U)` along `f`.
-/

namespace New.Variety

open CategoryTheory Subfunctor Function Ideal Abelian.Ext LongExactSeq

variable {Λ : Ab.{0}} {R : Type} [CommRing R] {X Y : PointFunctor} {U V W : Subfunctor Y}

/-- If the inclusion of the subfunctor `U` into `Y` is relatively affine (`New.Variety.IsRelAffine`:
its pull-back along every point is representable), so is the inclusion of its preimage under any
`f : X ⟶ Y`. -/
lemma IsRelAffine.preimage (h : IsRelAffine U.ι) (f : X ⟶ Y) : IsRelAffine (U.preimage f).ι := by
  -- the preimage of `U` is its pull-back along `f`
  refine h.baseChange (?_ : IsPullback (fromPreimage U f) (U.preimage f).ι U.ι f)
  rw [isPullback_iff]
  aesop (add simp [ExistsUnique, toFunctor])

/-- Pull-back along `(f, -g) : M ⟶ N ⊞ N'` sends the class with components `x`, `y` to
`f^* x - g^* y`. -/
private lemma map_biprod_lift_neg_biprodAddEquiv_symm {F M N N' : AbFunctor TestRing} (f : M ⟶ N)
    (g : M ⟶ N') {n : ℕ} (x : H N F n) (y : H N' F n) :
    H.map F (Limits.biprod.lift f (-g)) n (biprodAddEquiv.symm (x, y)) =
      H.map F f n x - H.map F g n y := by
  simp [biprodAddEquiv, H.map, sub_eq_add_neg]

/-- On test rings, let `U ⊔ V ≤ W` (this is `h_le`), and let `U ⊔ V`, seen as a subfunctor of `W`,
be dense in `W` for the locally constant `Λ`-valued coefficients. Then the inclusion `U ⊔ V → W`
induces isomorphisms `Hⁿ(W) → Hⁿ(U ⊔ V)` in every degree. -/
lemma TestCohomology.isCohomEquiv_sup_of_isCohomDense
    (h_dense : IsCohomDense (locConstCoeff Λ) (((U ⊔ V).preimage W.ι).whisker testIncl))
    (h_le : U.whisker testIncl ⊔ V.whisker testIncl ≤ W.whisker testIncl) :
    IsCohomEquiv (locConstCoeff Λ) (freeAb.map (homOfLe h_le)) := by
  have h_range : Subfunctor.range (homOfLe h_le) = ((U ⊔ V).preimage W.ι).whisker testIncl := by
    aesop (add simp [homOfLe, toFunctor])
  exact (isCohomEquiv_iff_range h_range).2 h_dense.isCohomEquiv

/-- The restriction `Hⁿ(W) → Hⁿ(U) × Hⁿ(V)` on test rings is the restriction to `U ⊔ V`, followed by
the pull-back along `ℤ[U] ⊞ ℤ[V] → ℤ[U ⊔ V]` and the splitting of the cohomology of the sum. -/
private lemma TestCohomology.prod_map_homOfLe_eq_comp (hUW : U ≤ W) (hVW : V ≤ W)
    (h_le : U.whisker testIncl ⊔ V.whisker testIncl ≤ W.whisker testIncl) (n : ℕ) :
    ⇑((map Λ (homOfLe hUW) n).prod (map Λ (homOfLe hVW) n)) =
      biprodAddEquiv ∘
        H.map (locConstCoeff Λ) (Limits.biprod.desc (freeAb.map (homOfLe le_sup_left))
          (freeAb.map (homOfLe le_sup_right))) n ∘
        H.map (locConstCoeff Λ) (freeAb.map (homOfLe h_le)) n := by
  symm
  funext x
  simp [biprodAddEquiv, H.map, ← Functor.map_comp]
  rfl

/-- Mayer–Vietoris for subfunctors `U, V ≤ W` of `Y`, in the cohomology `H` of the free abelian
functors `ℤ[−]` restricted to test rings (`testIncl`), with coefficients `locConstCoeff Λ`
(A ↦ locally constant functions Spec A → Λ). Assume `U ⊔ V` is dense in `W` for these coefficients
(`IsCohomDense`: for every point h_A → W on test rings, the inclusion of the preimage of `U ⊔ V`
into h_A induces bijections on all `Ext^n(−, locConstCoeff Λ)`). If in each degree `m < n` every
class on `U ⊓ V` is a difference of restrictions of classes on `U` and on `V`, then the restriction
`Hⁿ(W) → Hⁿ(U) × Hⁿ(V)` is injective. -/
lemma TestCohomology.mayer_vietoris_injective_of_sub_surjective (hUW : U ≤ W) (hVW : V ≤ W)
    (h_dense : IsCohomDense (locConstCoeff Λ) (((U ⊔ V).preimage W.ι).whisker testIncl)) (n : ℕ)
    (h_surj : ∀ m < n, ∀ z : H (freeAb.obj (testIncl ⋙ (U ⊓ V).toFunctor)) (locConstCoeff Λ) m,
      ∃ (x : H (freeAb.obj (testIncl ⋙ U.toFunctor)) (locConstCoeff Λ) m)
        (y : H (freeAb.obj (testIncl ⋙ V.toFunctor)) (locConstCoeff Λ) m),
        map Λ (homOfLe inf_le_left) m x - map Λ (homOfLe inf_le_right) m y = z) :
    Injective ((map Λ (homOfLe hUW) n).prod (map Λ (homOfLe hVW) n)) := by
  -- In the long exact sequence of `0 → ℤ[U ⊓ V] → ℤ[U] ⊞ ℤ[V] → ℤ[U ⊔ V] → 0`, split the middle
  -- term by `biprodAddEquiv`; density lets `W` replace the union.
  have h_le : U.whisker testIncl ⊔ V.whisker testIncl ≤ W.whisker testIncl :=
    sup_le (fun A ↦ hUW (testIncl.obj A)) fun A ↦ hVW (testIncl.obj A)
  obtain ⟨w, h_exact⟩ :=
    mayer_vietoris_shortExact (U := U.whisker testIncl) (V := V.whisker testIncl)
  -- `Hⁿ(U ⊔ V) → Hⁿ(U) × Hⁿ(V)` is injective, as the next map is onto in lower degrees
  have h_inj : Injective ((contravariant h_exact (locConstCoeff Λ)).f n) := by
    refine (contravariant h_exact _).f_injective_of_g_surjective fun m hm z ↦ ?_
    obtain ⟨x, y, hxy⟩ := h_surj m hm z
    exact ⟨biprodAddEquiv.symm (x, y), (map_biprod_lift_neg_biprodAddEquiv_symm ..).trans hxy⟩
  rw [prod_map_homOfLe_eq_comp hUW hVW h_le]
  exact biprodAddEquiv.injective.comp
    (h_inj.comp (isCohomEquiv_sup_of_isCohomDense h_dense h_le n).injective)

/-- Mayer–Vietoris for subfunctors `U, V ≤ W` of `Y` with `U ⊔ V` dense in `W`, on test rings with
locally constant `Λ`-valued coefficients: if `U ⊓ V` has points only over the zero ring, then the
restriction `Hⁿ(W) → Hⁿ(U) × Hⁿ(V)` is bijective. -/
lemma TestCohomology.mayer_vietoris_bijective (hUW : U ≤ W) (hVW : V ≤ W)
    (h_dense : IsCohomDense (locConstCoeff Λ) (((U ⊔ V).preimage W.ι).whisker testIncl)) (n : ℕ)
    (h_zero : ∀ B : CommRingCat, (U ⊓ V).toFunctor.obj B → (0 : B) = 1) :
    Bijective ((map Λ (homOfLe hUW) n).prod (map Λ (homOfLe hVW) n)) := by
  have h_le : U.whisker testIncl ⊔ V.whisker testIncl ≤ W.whisker testIncl :=
    sup_le (fun A ↦ hUW (testIncl.obj A)) fun A ↦ hVW (testIncl.obj A)
  -- the short exact sequence `0 → ℤ[U ⊓ V] → ℤ[U] ⊞ ℤ[V] → ℤ[U ⊔ V] → 0` on test rings
  obtain ⟨w, h_exact⟩ :=
    mayer_vietoris_shortExact (U := U.whisker testIncl) (V := V.whisker testIncl)
  -- `U ⊓ V` is acyclic, so `U ⊔ V` has the cohomology of the middle term `ℤ[U] ⊞ ℤ[V]`
  have h_acyclic (m : ℕ)
      (x : H (freeAb.obj (U.whisker testIncl ⊓ V.whisker testIncl).toFunctor) (locConstCoeff Λ) m) :
      x = 0 :=
    hasPartitions_locConstCoeff.eq_zero_of_zero_ring (fun (A : TestRing) ↦ h_zero A.obj) m x
  rw [prod_map_homOfLe_eq_comp hUW hVW h_le]
  exact biprodAddEquiv.bijective.comp ((isCohomEquiv_quotient_of_acyclic h_exact h_acyclic n).comp
    (isCohomEquiv_sup_of_isCohomDense h_dense h_le n))

/-- Mayer–Vietoris for `U, V ≤ W` with `U ⊔ V` dense in `W`, on test rings with coefficients `Λ`,
with `U ⊓ V` given as `T` and `hT`: `Hⁿ(W) → Hⁿ(U) × Hⁿ(V)` is injective if in each degree `m < n`
every class on `T` is a difference of restrictions from `U` and `V`, and bijective if `T` has
points only over the zero ring. The two halves are `mayer_vietoris_injective_of_sub_surjective`
and `mayer_vietoris_bijective`. -/
lemma TestCohomology.mayer_vietoris_injective (hUW : U ≤ W) (hVW : V ≤ W)
    (h_dense : IsCohomDense (locConstCoeff Λ) (((U ⊔ V).preimage W.ι).whisker testIncl)) (n : ℕ)
    {T : Subfunctor Y} (hT : T = U ⊓ V) :
    ((∀ m < n, ∀ z : H (freeAb.obj (testIncl ⋙ T.toFunctor)) (locConstCoeff Λ) m,
        ∃ (x : H (freeAb.obj (testIncl ⋙ U.toFunctor)) (locConstCoeff Λ) m)
          (y : H (freeAb.obj (testIncl ⋙ V.toFunctor)) (locConstCoeff Λ) m),
          map Λ (homOfLe (hT.le.trans inf_le_left)) m x -
            map Λ (homOfLe (hT.le.trans inf_le_right)) m y = z) →
      Injective ((map Λ (homOfLe hUW) n).prod (map Λ (homOfLe hVW) n))) ∧
    ((∀ B : CommRingCat, T.toFunctor.obj B → (0 : B) = 1) →
      Bijective ((map Λ (homOfLe hUW) n).prod (map Λ (homOfLe hVW) n))) := by
  subst hT
  exact ⟨mayer_vietoris_injective_of_sub_surjective hUW hVW h_dense n,
    mayer_vietoris_bijective hUW hVW h_dense n⟩

/-- Downward induction by Zorn's lemma. Let `P` be a property of the elements above `a`. If every
nonempty chain of counterexamples has an upper bound that is a counterexample, and `P` holds at `m`
as soon as it holds strictly above `m`, then `P` holds everywhere above `a`. -/
lemma forall_gt_of_chain_counterexample {α : Type*} [PartialOrder α] {a : α}
    {P : ∀ b : α, a < b → Prop}
    (h_chain : ∀ c : Set α,
      (∀ b ∈ c, ∃ h : a < b, ¬P b h) →
      IsChain (· ≤ ·) c → c.Nonempty →
      ∃ (m : α) (h : a < m), ¬P m h ∧ ∀ b ∈ c, b ≤ m)
    (h_step : ∀ (m : α) (h : a < m), (∀ (b : α) (hb : m < b), P b (h.trans hb)) → P m h) (b : α)
    (hb : a < b) :
    P b hb := by
  by_contra h_fail
  -- A maximal counterexample `m` contradicts `h_step`.
  obtain ⟨m, -, h_max⟩ : ∃ m : α, b ≤ m ∧ Maximal (· ∈ {b : α | ∃ h : a < b, ¬P b h}) m := by
    refine zorn_le_nonempty₀ _ (fun c hc_sub hc_chain z hz ↦ ?_) b ⟨hb, h_fail⟩
    obtain ⟨ub, ha_ub, hub_fail, h_le_ub⟩ := h_chain c hc_sub hc_chain ⟨z, hz⟩
    exact ⟨ub, ⟨ha_ub, hub_fail⟩, h_le_ub⟩
  obtain ⟨ha_m, hm_fail⟩ := h_max.prop
  refine hm_fail (h_step m ha_m fun d hd ↦ ?_)
  by_contra hd_fail
  exact h_max.not_gt ⟨ha_m.trans hd, hd_fail⟩ hd

/-- Downward induction, injective half. Let `π` be a natural map (`h_nat`) between functors `G`, `K`
from a partial order `α` to abelian groups, such that every nonempty directed subset has a cocone
whose images under `G` and `K` are filtered colimits (`h_colim`). If each element of the kernel of
any `π a` that dies at all `b > a` is zero (`h_step`), then `π a` is injective. -/
lemma injective_of_isFilteredColimit_of_map_eq_zero {α : Type} [PartialOrder α]
    {G K : α ⥤ Ab} {π : ∀ a : α, G.obj a →+ K.obj a}
    (h_nat : ∀ {a b : α} (f : a ⟶ b) (x : G.obj a), K.map f (π a x) = π b (G.map f x))
    (h_colim : ∀ {c : Set α} [IsDirectedOrder c] [Nonempty c],
      ∃ m : Limits.Cocone (Subtype.mono_coe fun a : α ↦ a ∈ c).functor,
        IsFilteredColimit (G.mapCocone m) ∧ IsFilteredColimit (K.mapCocone m))
    (h_step : ∀ (a : α) (x : G.obj a), π a x = 0 →
      (∀ (b : α) (hab : a < b), G.map hab.le.hom x = 0) → x = 0)
    (a : α) :
    Injective (π a) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ h_step a x hx ?_
  -- Downward induction: a chain of indices at which `x` survives is bounded by the vertex of a
  -- colimit cocone, and `x` survives there too.
  refine forall_gt_of_chain_counterexample (P := fun b hab ↦ G.map hab.le.hom x = 0) ?_ ?_
  · intro c hc_sub h_chain ⟨z, hz⟩
    have hc_directed : IsDirectedOrder c := ⟨h_chain.directed⟩
    have hc_nonempty : Nonempty c := ⟨⟨z, hz⟩⟩
    -- `hG_ker`: an element that maps to `0` at the vertex dies at a later member of `c`
    obtain ⟨t, ⟨hG_ker, -⟩, -⟩ := h_colim (c := c)
    obtain ⟨haz, -⟩ := hc_sub z hz
    have h_le_vertex : ∀ b ∈ c, b ≤ t.pt := fun b hb ↦ leOfHom (t.ι.app ⟨b, hb⟩)
    refine ⟨t.pt, haz.trans_le (h_le_vertex z hz), fun h_zero ↦ ?_, h_le_vertex⟩
    -- if `x` dies at the vertex, it dies at some member `b` of the chain
    have h_zero_vertex : (G.mapCocone t).ι.app ⟨z, hz⟩ (G.map haz.le.hom x) = 0 :=
      (G.map_comp_apply haz.le.hom (t.ι.app ⟨z, hz⟩) x).symm.trans h_zero
    obtain ⟨b, f, hb⟩ := hG_ker ⟨z, hz⟩ (G.map haz.le.hom x) h_zero_vertex
    obtain ⟨hab, hb_survives⟩ := hc_sub b b.property
    exact hb_survives ((G.map_comp_apply haz.le.hom (homOfLE (leOfHom f)) x).trans hb)
  · -- if `x` dies at every `b > m`, its image at `m` is in the kernel of `π m` and dies above `m`
    intro m ham hm
    refine h_step m (G.map ham.le.hom x) (by rw [← h_nat, hx, map_zero]) fun b hb ↦ ?_
    rw [← G.map_comp_apply]
    exact hm b hb

/-- Downward induction, surjective half. Let `G, K : α ⥤ Ab` be functors on a partial order `α`,
with homomorphisms `π a : G a → K a` natural in `a` (`h_nat`). Suppose that every nonempty directed
subset of `α` has a cocone in `α` that both `G` and `K` send to filtered colimits in the elementwise
sense, where every element of the vertex comes from some stage and an element vanishing in the
vertex already vanishes at a later stage (`h_colim`). If every `y ∈ K a` whose images in `K b` lift
along `π b` for all `b > a` itself lifts along `π a` (`h_step`), then `π a` is surjective. -/
lemma surjective_of_isFilteredColimit_of_exists_lift {α : Type} [PartialOrder α]
    {G K : α ⥤ Ab} {π : ∀ a : α, G.obj a →+ K.obj a}
    (h_nat : ∀ {a b : α} (f : a ⟶ b) (x : G.obj a), K.map f (π a x) = π b (G.map f x))
    (h_colim : ∀ {c : Set α} [IsDirectedOrder c] [Nonempty c],
      ∃ m : Limits.Cocone (Subtype.mono_coe fun a : α ↦ a ∈ c).functor,
        IsFilteredColimit (G.mapCocone m) ∧ IsFilteredColimit (K.mapCocone m))
    (h_step : ∀ (a : α) (y : K.obj a),
      (∀ (b : α) (hab : a < b), ∃ x : G.obj b, π b x = K.map hab.le.hom y) →
      ∃ x : G.obj a, π a x = y)
    (a : α) :
    Surjective (π a) := by
  refine fun y ↦ h_step a y ?_
  -- Downward induction: a chain of indices at which the image of `y` has no lift is bounded by
  -- the vertex of a colimit cocone, and it has no lift there either.
  refine forall_gt_of_chain_counterexample
    (P := fun b hab ↦ ∃ x : G.obj b, π b x = K.map hab.le.hom y) ?_ ?_
  · intro c hc_sub h_chain ⟨z, hz⟩
    have hc_directed : IsDirectedOrder c := ⟨h_chain.directed⟩
    have hc_nonempty : Nonempty c := ⟨⟨z, hz⟩⟩
    -- `hG_surj`: every element at the vertex comes from a member of `c`; `hK_ker`: an element
    -- that maps to `0` at the vertex dies at a later member of `c`
    obtain ⟨t, ⟨-, hG_surj⟩, ⟨hK_ker, -⟩⟩ := h_colim (c := c)
    obtain ⟨haz, -⟩ := hc_sub z hz
    have h_le_vertex : ∀ b ∈ c, b ≤ t.pt := fun b hb ↦ leOfHom (t.ι.app ⟨b, hb⟩)
    refine ⟨t.pt, haz.trans_le (h_le_vertex z hz), ?_, h_le_vertex⟩
    -- A lift `x₀` at the vertex comes from some `x` at a member `b` of the chain. The difference
    -- of `π b x` and the image of `y` dies at the vertex, so at a later member `d`.
    rintro ⟨x₀, hx₀⟩
    obtain ⟨b, x, rfl⟩ := hG_surj x₀
    obtain ⟨hab, -⟩ := hc_sub b b.property
    have h_diff_vertex : (K.mapCocone t).ι.app b (π b x - K.map hab.le.hom y) = 0 := by
      change K.map (homOfLE (h_le_vertex b b.property)) (π b x - K.map hab.le.hom y) = 0
      rw [map_sub, ← K.map_comp_apply, sub_eq_zero]
      exact (h_nat _ x).trans hx₀
    obtain ⟨d, f, hd⟩ := hK_ker b (π b x - K.map hab.le.hom y) h_diff_vertex
    obtain ⟨had, hd_no_lift⟩ := hc_sub d d.property
    have h_bd : (b : α) ≤ d := leOfHom f
    have h_diff_d : K.map (homOfLE h_bd) (π b x - K.map hab.le.hom y) = 0 := hd
    rw [map_sub, ← K.map_comp_apply, sub_eq_zero] at h_diff_d
    exact hd_no_lift ⟨G.map (homOfLE h_bd) x, (h_nat _ x).symm.trans h_diff_d⟩
  · -- if the images of `y` lift at every `b > m`, the image of `y` at `m` satisfies `h_step`
    refine fun m ham hm ↦ h_step m (K.map ham.le.hom y) fun b hb ↦ ?_
    rw [← K.map_comp_apply]
    exact hm b hb

/-- The subfunctors `U a ⊆ Y`, for ideals `a` of `R`, behave like the zero loci `V(a)` of the
ideals in `Spec R`. -/
structure IsZeroLocusFamily (U : Ideal R → Subfunctor Y) : Prop where
  /-- Each inclusion `U a ⊆ Y` is relatively affine. -/
  isRelAffine (a : Ideal R) : IsRelAffine (U a).ι
  /-- The zero locus of a sum of ideals is the intersection of their zero loci. -/
  mem_sSup_iff {A : CommRingCat} {x : Y.obj A} {c : Set (Ideal R)} :
    x ∈ (U (sSup c)).obj A ↔ ∀ a ∈ c, x ∈ (U a).obj A
  /-- The zero locus of the unit ideal has points only over the zero ring. -/
  subsingleton_of_mem_top {A : CommRingCat} {x : Y.obj A} (hx : x ∈ (U ⊤).obj A) : Subsingleton A

namespace IsZeroLocusFamily

variable {U : Ideal R → Subfunctor Y} {A : CommRingCat} {x : Y.obj A}

/-- Every point lies in the zero locus of the zero ideal. -/
lemma mem_bot (hU : IsZeroLocusFamily U) : x ∈ (U ⊥).obj A := by
  rw [← sSup_empty, hU.mem_sSup_iff]
  simp

/-- The zero locus of `a ⊔ b` is the intersection of the zero loci of `a` and `b`. -/
lemma mem_sup_iff (hU : IsZeroLocusFamily U) {a b : Ideal R} :
    x ∈ (U (a ⊔ b)).obj A ↔ x ∈ (U a).obj A ∧ x ∈ (U b).obj A := by
  rw [← sSup_pair, hU.mem_sSup_iff]
  simp

/-- Larger ideals have smaller zero loci. -/
lemma antitone (hU : IsZeroLocusFamily U) : Antitone U := by
  intro a b hab A x hx
  rw [← sup_eq_right.mpr hab] at hx
  exact (hU.mem_sup_iff.mp hx).left

/-- The preimages of the zero loci under `p : Z ⟶ Y` also shrink as the ideal grows. -/
lemma antitone_preimage (hU : IsZeroLocusFamily U) {Z : PointFunctor} (p : Z ⟶ Y) :
    Antitone fun a : Ideal R ↦ (U a).preimage p :=
  fun _ _ hab A _ hz ↦ hU.antitone hab A hz

/-- The zero loci of `(e)` and `(1 - e)` meet only over the zero ring. -/
lemma subsingleton_of_mem_span_of_mem_span_one_sub (hU : IsZeroLocusFamily U) {e : R}
    (hx : x ∈ (U (span {e})).obj A) (hx' : x ∈ (U (span {1 - e})).obj A) : Subsingleton A := by
  have h_top : span {e} ⊔ span {1 - e} = (⊤ : Ideal R) :=
    (sup_eq_top_iff_isCoprime e (1 - e)).2 ⟨1, 1, by simp⟩
  refine hU.subsingleton_of_mem_top (x := x) ?_
  rw [← h_top, hU.mem_sup_iff]
  exact ⟨hx, hx'⟩

end IsZeroLocusFamily

/-- Let `s : X ⟶ reprBy S` be a map to the functor `h_S` represented by the ring `S`. The
subfunctors `zeroPoints s J` of points whose ring map `S → A` kills the ideal `J` form a family
of zero loci (`New.Variety.IsZeroLocusFamily`). -/
lemma isZeroLocusFamily_zeroPoints {S : CommRingCat} (s : X ⟶ reprBy S) :
    IsZeroLocusFamily fun J : Ideal S ↦ zeroPoints s J where
  isRelAffine J := isRelAffine_zeroPoints s J
  mem_sSup_iff {A x c} :=
    -- `x` lies in `zeroPoints s J` iff `J` is contained in the kernel of its ring map
    sSup_le_iff (a := RingHom.ker (baseRingMap s x).hom)
  subsingleton_of_mem_top {A x} hx := by
    have h_one : baseRingMap s x 1 = 0 := hx 1 Submodule.mem_top
    exact subsingleton_of_zero_eq_one (by simpa using h_one.symm)

/-- Mayer–Vietoris for the two pieces that an element `e` cuts out of a zero locus `U a`, pulled
back along `p : Z ⟶ Y`. If `U (e) ⊔ U (1 - e)` is dense in `Y` on test rings, then the restriction
`Hⁿ(U a) → Hⁿ(U (a ⊔ (e))) × Hⁿ(U (a ⊔ (1 - e)))` of the preimages is bijective: the union of the
two pieces is dense in `U a`, and they meet only over the zero ring. -/
private lemma bijective_prod_map_sup_span_of_isCohomDense {U : Ideal R → Subfunctor Y}
    (hU : IsZeroLocusFamily U) {e : R}
    (h_dense : IsCohomDense (locConstCoeff Λ) ((U (span {e}) ⊔ U (span {1 - e})).whisker testIncl))
    {Z : PointFunctor} (p : Z ⟶ Y) (a : Ideal R) (n : ℕ) :
    Bijective
      ((TestCohomology.map Λ
          (homOfLe (hU.antitone_preimage p (le_sup_left : a ≤ a ⊔ span {e}))) n).prod
        (TestCohomology.map Λ
          (homOfLe (hU.antitone_preimage p (le_sup_left : a ≤ a ⊔ span {1 - e}))) n)) := by
  refine TestCohomology.mayer_vietoris_bijective _ _ ?_ n ?_
  · -- a point over `U a` and over `U (e)` or `U (1 - e)` lies over one of the two pieces
    refine h_dense.of_preimage_le (mapOnTests (Subfunctor.ι _ ≫ p)) fun A z hz ↦ ?_
    exact hz.imp (fun hz_e ↦ hU.mem_sup_iff.mpr ⟨z.property, hz_e⟩)
      fun hz_e' ↦ hU.mem_sup_iff.mpr ⟨z.property, hz_e'⟩
  · -- the two pieces meet only over the zero ring
    rintro B ⟨z, hz_e, hz_e'⟩
    have h_subsingleton : Subsingleton B := hU.subsingleton_of_mem_span_of_mem_span_one_sub
      (hU.mem_sup_iff.mp hz_e).right (hU.mem_sup_iff.mp hz_e').right
    exact Subsingleton.elim 0 1

/-- Over a zero locus `U a`, either the pull-back `Hⁿ(U a) → Hⁿ(u⁻¹(U a))` along `u : X ⟶ Y` is
bijective, or an idempotent `e` splits `a`: neither `e` nor `1 - e` lies in `a`. The first case
holds for `a = ⊤`, where both groups vanish, and, by `h_conn`, for proper `a` that no idempotent
splits. -/
private lemma bijective_map_fromPreimage_or_exists_isIdempotentElem {U : Ideal R → Subfunctor Y}
    (hU : IsZeroLocusFamily U) (u : X ⟶ Y)
    (h_conn : ∀ a : Ideal R, a ≠ ⊤ → (∀ e : R, IsIdempotentElem e → e ∈ a ∨ 1 - e ∈ a) →
      IsTestCohomEquiv Λ (fromPreimage (U a) u))
    (a : Ideal R) (n : ℕ) :
    Bijective (TestCohomology.map Λ (fromPreimage (U a) u) n) ∨
      ∃ e : R, IsIdempotentElem e ∧ e ∉ a ∧ 1 - e ∉ a := by
  refine or_iff_not_imp_right.mpr fun h_no_split ↦ ?_
  obtain rfl | ha := eq_or_ne a ⊤
  · -- all points of `U ⊤` and of its preimages lie over the zero ring, so both groups vanish
    have h_vanish {Z : PointFunctor} (p : Z ⟶ Y)
        (x : H (freeAb.obj (testIncl ⋙ ((U ⊤).preimage p).toFunctor)) (locConstCoeff Λ) n) :
        x = 0 := by
      refine hasPartitions_locConstCoeff.eq_zero_of_zero_ring (fun B z ↦ ?_) n x
      exact (hU.subsingleton_of_mem_top z.property).elim 0 1
    -- the preimage of `U ⊤` along `𝟙 Y` is `U ⊤` itself
    exact ⟨fun x y _ ↦ (h_vanish (𝟙 Y) x).trans (h_vanish (𝟙 Y) y).symm,
      fun y ↦ ⟨0, (h_vanish u _).trans (h_vanish u y).symm⟩⟩
  · -- `a` is proper and no idempotent splits it
    refine h_conn a ha (fun e he ↦ ?_) n
    by_contra h_not
    exact h_no_split ⟨e, he, not_or.mp h_not⟩

/-- Local-to-global principle. Let `X`, `Y` have continuous cohomology with coefficients `Λ`
(`IsCohomContinuous`), and let the `U a ⊆ Y`, `a` an ideal of `R`, be zero loci
(`IsZeroLocusFamily`). Assume that for every idempotent `e`, `U (e) ⊔ U (1 - e)` is dense for
locally constant `Λ`-coefficients (`IsCohomDense`): for each point `h_A → Y` with `A` a test ring
(`testIncl`), the inclusion of its preimage in `h_A` is a cohomology equivalence. If `u : X ⟶ Y`
induces isomorphisms on cohomology (`IsTestCohomEquiv`) over `U a` for each proper ideal `a`
containing `e` or `1 - e` for every idempotent `e` (each connected piece), then so does `u`. -/
lemma IsTestCohomEquiv.of_connected (hX : IsCohomContinuous Λ X)
    (hY : IsCohomContinuous Λ Y) (u : X ⟶ Y) {U : Ideal R → Subfunctor Y} (hU : IsZeroLocusFamily U)
    (h_dense : ∀ e : R, IsIdempotentElem e →
      IsCohomDense (locConstCoeff Λ) ((U (span {e}) ⊔ U (span {1 - e})).whisker testIncl))
    (h_conn : ∀ a : Ideal R, a ≠ ⊤ → (∀ e : R, IsIdempotentElem e → e ∈ a ∨ 1 - e ∈ a) →
      IsTestCohomEquiv Λ (fromPreimage (U a) u)) :
    IsTestCohomEquiv Λ u := by
  -- By Zorn's lemma, using continuity along chains, it is enough to prove bijectivity over `U a`
  -- from bijectivity over all `U b`, `a < b`. If `a` is not connected, an idempotent `e` splits
  -- `U a` into `U (a + (e))` and `U (a + (1 - e))`.
  -- First replace `Y` by `U ⊥`, which is all of `Y`.
  have h_bot : IsCohomDense (locConstCoeff Λ) ((U ⊥).whisker testIncl) :=
    .of_top_le fun A y _ ↦ hU.mem_bot
  refine h_bot.isCohomEquiv_of_fromPreimage fun n ↦ ?_
  -- `G a = Hⁿ(U a)` and `K a = Hⁿ(u⁻¹(U a))`, with restriction maps, and `π a : G a → K a` is the
  -- pull-back along `u`; the goal is that `π ⊥` is bijective.
  let G : Ideal R ⥤ AddCommGrpCat := TestCohomology.antitoneFamily hU.antitone Λ n
  let K : Ideal R ⥤ AddCommGrpCat := TestCohomology.antitoneFamily (hU.antitone_preimage u) Λ n
  let π (a : Ideal R) : G.obj a →+ K.obj a := TestCohomology.map Λ (fromPreimage (U a) u) n
  show Bijective (π ⊥)
  have h_nat {a b : Ideal R} (f : a ⟶ b) (x : G.obj a) : K.map f (π a x) = π b (G.map f x) :=
    -- both sides are the pull-back along the composite `u⁻¹(U b) → U a`
    calc K.map f (π a x)
      _ = TestCohomology.map Λ
            (homOfLe (hU.antitone_preimage u f.le) ≫ fromPreimage (U a) u) n x :=
        (TestCohomology.map_comp ..).symm
      _ = TestCohomology.map Λ (fromPreimage (U b) u ≫ homOfLe (hU.antitone f.le)) n x := rfl
      _ = π b (G.map f x) := TestCohomology.map_comp ..
  -- For directed `c`, the vertex is `sSup c`: `U (sSup c)` contains the intersection of the
  -- `U a`, so continuity makes the cohomology over it the colimit.
  have h_colim : ∀ {c : Set (Ideal R)} [IsDirectedOrder c] [Nonempty c],
      ∃ t : Limits.Cocone (Subtype.mono_coe fun a : Ideal R ↦ a ∈ c).functor,
        IsFilteredColimit (G.mapCocone t) ∧ IsFilteredColimit (K.mapCocone t) := by
    intro c hc_directed hc_nonempty
    have h_inter {A : CommRingCat} {y : Y.obj A} (hy : ∀ j : c, y ∈ (U j).obj A) :
        y ∈ (U (sSup c)).obj A := by
      simpa [hU.mem_sSup_iff] using hy
    exact ⟨⟨sSup c, { app a := homOfLE (le_sSup a.property) }⟩,
      hY.isFilteredColimit_antitoneFamily hU.antitone hU.isRelAffine h_inter,
      hX.isFilteredColimit_antitoneFamily (hU.antitone_preimage u)
        (fun a ↦ (hU.isRelAffine a).preimage u) h_inter⟩
  constructor
  · refine injective_of_isFilteredColimit_of_map_eq_zero h_nat h_colim (fun a x hx h_later ↦ ?_) ⊥
    obtain h_bij | ⟨e, he_idem, he_notMem, he'_notMem⟩ :=
      bijective_map_fromPreimage_or_exists_isIdempotentElem hU u h_conn a n
    · exact (map_eq_zero_iff (π a) h_bij.injective).mp hx
    · -- `x` dies on both pieces, whose ideals are strictly larger than `a`; the preimage of
      -- `U a` along `𝟙 Y` is `U a` itself
      have h_lt_e : a < a ⊔ span {e} := by simpa using he_notMem
      have h_lt_e' : a < a ⊔ span {1 - e} := by simpa using he'_notMem
      have h_restrict_zero : (G.map h_lt_e.le.hom x, G.map h_lt_e'.le.hom x) = 0 :=
        Prod.ext (h_later _ h_lt_e) (h_later _ h_lt_e')
      exact (map_eq_zero_iff _
        (bijective_prod_map_sup_span_of_isCohomDense hU (h_dense e he_idem) (𝟙 Y) a n).injective
        (x := x)).mp h_restrict_zero
  · refine surjective_of_isFilteredColimit_of_exists_lift h_nat h_colim (fun a y h_later ↦ ?_) ⊥
    obtain h_bij | ⟨e, he_idem, he_notMem, he'_notMem⟩ :=
      bijective_map_fromPreimage_or_exists_isIdempotentElem hU u h_conn a n
    · exact h_bij.surjective y
    · -- Lift the restrictions of `y` to the two pieces, glue the lifts on `U a`, and compare the
      -- image of the glued class with `y` on the pieces.
      have h_lt_e : a < a ⊔ span {e} := by simpa using he_notMem
      have h_lt_e' : a < a ⊔ span {1 - e} := by simpa using he'_notMem
      obtain ⟨x₁, hx₁⟩ : ∃ x₁ : G.obj (a ⊔ span {e}), π _ x₁ = K.map h_lt_e.le.hom y :=
        h_later _ h_lt_e
      obtain ⟨x₂, hx₂⟩ : ∃ x₂ : G.obj (a ⊔ span {1 - e}), π _ x₂ = K.map h_lt_e'.le.hom y :=
        h_later _ h_lt_e'
      obtain ⟨x, hx⟩ : ∃ x : G.obj a, (G.map h_lt_e.le.hom x, G.map h_lt_e'.le.hom x) = (x₁, x₂) :=
        (bijective_prod_map_sup_span_of_isCohomDense hU (h_dense e he_idem) (𝟙 Y) a n).surjective
          (x₁, x₂)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
      refine ⟨x,
        (bijective_prod_map_sup_span_of_isCohomDense hU (h_dense e he_idem) u a n).injective ?_⟩
      exact Prod.ext ((h_nat le_sup_left.hom x).trans hx₁) ((h_nat le_sup_left.hom x).trans hx₂)

end New.Variety

/-!
## Density criteria tested on points in valuation rings

Each local ring of a test ring is a valuation ring of an algebraically closed field
(`New.Variety.IsTest.exists_valuationSubring_atPrime`). This is why it suffices to test the
criteria on points in such valuation rings.
-/

section ValuativeDensity

open CategoryTheory CommRingCat Ideal Subfunctor Function Pi RingHom

namespace New.Variety

/-- Let `p : X ⟶ Y` be a map of functors on rings that is relatively representable (`IsRelAffine`:
its pull-back along every point `reprBy A ⟶ Y` is representable). Suppose that `p` is onto on
`O`-points for every valuation subring `O` of every algebraically closed field. Then the image of
`p`, restricted to test rings, is cohomologically dense in `Y` (`HasCohomDenseImage`) for the
coefficients sending `A` to the locally constant functions `Spec A → Λ`: over every point
`reprBy A ⟶ Y`, the inclusion of the preimage of the image into `reprBy A` is an equivalence for
these coefficients. -/
lemma IsRelAffine.hasCohomDenseImage_of_lifts {X Y : PointFunctor} {p : X ⟶ Y} {Λ : Ab}
    (hp : IsRelAffine p)
    (h_lift : ∀ {K : Type} [Field K] [IsAlgClosed K] (O : ValuationSubring K),
      Surjective (p.app (of O))) :
    HasCohomDenseImage Λ p := by
  -- Let `U` be the preimage in `reprBy A.obj` of the image of `p`. By
  -- `IsTestCohomEquiv.of_connected` it is enough to compare `U` and `reprBy A.obj`
  -- over the zero locus of a proper ideal `J` that contains `e` or `1 - e` for every idempotent
  -- `e`. There every point factors through a local ring of `A`, a valuation ring, over which `p`
  -- is onto.
  intro A y
  let U : Subfunctor (reprBy A.obj) := (range p).preimage (pointMap y)
  -- The functor that `A` represents on test rings is the restriction of `reprBy A.obj`, so it
  -- suffices that `U` and `reprBy A.obj` have the same cohomology on test rings.
  suffices h_eqv : IsTestCohomEquiv Λ U.ι from
    ((Comparison.isBijective_congr (p' := fromPreimage (U.whisker _) _) rfl
        (.of_bijective (pointMap_id_bijective_of_fullyFaithful testIncl A))
      (.of_bijective fun B ↦ (pointMap_id_bijective_of_fullyFaithful testIncl A B).restrictPreimage
        _)).mp h_eqv.bij).eqv
  -- The pull-back of `p` along `y` is a map `reprFunctor.map π` of representable functors with
  -- image `U`: an atlas of `U`, which makes cohomology continuous over `U`.
  have h_cont : IsCohomContinuous Λ U.toFunctor := by
    obtain ⟨⟨T⟩, π, p', h_pb⟩ := hp (pointMap y)
    have h_range : range (𝟙 _ ≫ reprFunctor.map π) ≤ U := by
      rintro B _ ⟨x, rfl⟩
      -- the square `h_pb` commutes at `x`, so `p' x` lies over the image of `x`
      exact ⟨p'.app B x, congr($h_pb.w.1 _ x)⟩
    obtain ⟨-, h_glue⟩ := isPullback_iff.mp h_pb
    refine .of_hasCohomDenseImage
      ((hp.baseChange h_pb).baseChange (.of_horiz_isIso_mono ⟨(U.lift_ι _ h_range).symm⟩))
      (.of_top_le fun _ ⟨_, _, e⟩ _ ↦ ?_)
    -- the point of the pull-back over the pair that `e` glues is a preimage
    exact (h_glue _ _ _ e).imp fun t ⟨⟨h_val, _⟩, _⟩ ↦ Subtype.ext h_val
  refine IsTestCohomEquiv.of_connected h_cont
    (.of_hasCohomDenseImage (IsRelAffine.id_mem _) (.of_top_le fun _ x _ ↦ ⟨x, rfl⟩))
    U.ι (isZeroLocusFamily_zeroPoints (𝟙 (reprBy A.obj))) (fun e he ↦ ?_) fun J hJ h_conn ↦ ?_
  · -- The points that kill `e` or `1 - e` are dense.
    exact .of_preimage_le (hasPartitions_locConstCoeff.isCohomDense_partition _ he)
      (by exact {app _ := ↾fun x ↦ ⟨⟨x.1⟩⟩}) fun _ _ ↦
      .imp (span_singleton_le_iff_mem (ker _)).mpr (span_singleton_le_iff_mem (ker _)).mpr
  · -- The local ring of `A` at a maximal ideal `q ⊇ J` is a valuation ring `O`. We show that every
    -- point `f` that kills `J` lies in `U`, so that the inclusion is bijective on points.
    obtain ⟨q, hq, hJq⟩ := J.exists_le_maximal hJ
    obtain ⟨-, -, K, _, _, O, _, hO⟩ := A.property.exists_valuationSubring_atPrime q
    refine .of_bijective fun B ↦ ⟨fun x₁ x₂ h_eq ↦ Subtype.ext (Subtype.ext congr($h_eq.1)),
      fun ⟨f, hf⟩ ↦ ?_⟩
    -- An element `b ∉ q` divides an idempotent `e ∉ q`. Then `e ∉ J`, so `1 - e ∈ J` is killed by
    -- `f`, and `f e = 1` makes `f b` a unit.
    have h_unit : f ∈ (unitPoints (𝟙 (reprBy A.obj)) q.primeCompl).obj B.obj := by
      intro b hb
      obtain ⟨e, he_q, he, h_dvd⟩ :=
        exists_dvd_idempotent_of_notMem A.property.isComparableRing hq hb
      have h_one : baseRingMap (𝟙 _) f 1 = baseRingMap (𝟙 _) f e :=
        (sub_mem_ker_iff _).mp (hf _ ((h_conn e he).resolve_left fun h ↦ he_q (hJq h)))
      exact isUnit_of_dvd_unit (map_dvd _ h_dvd) (by simp [← h_one])
    -- So `f` factors through `O`, and the `O`-point `A → O` lies in `U` by hypothesis.
    obtain ⟨g, rfl⟩ := unitPoints_le_range_reprMap O q.primeCompl _ h_unit
    exact ⟨⟨⟨_, U.map _ (h_lift O _)⟩, hf⟩, rfl⟩

/-- Let `V i`, for `i` in a finite type `J`, be subfunctors of a functor `Y` on rings whose
inclusions are relatively representable, and let `U` be a subfunctor of the restriction
`testIncl ⋙ Y` of `Y` to test rings. Suppose that every point of `Y` in a valuation ring of an
algebraically closed field lies in some `V i` whose restriction to test rings is contained in `U`.
Then `U` is dense (`IsCohomDense`) for `locConstCoeff Λ` (`A ↦` locally constant functions
`Spec A → Λ`): for every point `reprBy A ⟶ Y` with `A` a test ring, the inclusion of the preimage of
`U` into `reprBy A` is an equivalence for these coefficients. -/
lemma IsCohomDense.of_affine_cover {Y : CommRingCat ⥤ Type 1} {Λ : Ab}
    {U : Subfunctor (testIncl ⋙ Y)} {J : Type} [Finite J] {V : J → Subfunctor Y}
    (hV_rep : ∀ i : J, IsRelAffine (V i).ι)
    (h_cover : ∀ {K : Type} [Field K] [IsAlgClosed K] (O : ValuationSubring K) (y : Y.obj (of O)),
      ∃ i : J, (V i).whisker testIncl ≤ U ∧ y ∈ (V i).obj (of O)) :
    IsCohomDense (Y := testIncl ⋙ Y) (locConstCoeff Λ) U := by
  classical
  -- Fix a point `y` over a test ring `A`. The pull-back of `V i` along `y` is represented by a ring
  -- map `φ i : A ⟶ R i`: a map `f` out of `A` carries `y` into `V i` iff it factors through `φ i`.
  intro A y
  have h_rep (i : J) : ∃ (R : CommRingCat) (φ : A.obj ⟶ R), ∀ (B : CommRingCat) (f : A.obj ⟶ B),
      Y.map f y ∈ (V i).obj B ↔ ∃ u : R ⟶ B, φ ≫ u = f := by
    obtain ⟨h_comm, h_lift⟩ := isPullback_iff.mp ((hV_rep i).isPullback (pointMap (A := A.obj) y))
    refine ⟨_, ((hV_rep i).snd (pointMap y)).unop, fun B f ↦ ⟨fun hf ↦ ?_, ?_⟩⟩
    · obtain ⟨z, ⟨hz, -⟩, -⟩ := h_lift B ⟨f⟩ ⟨_, hf⟩ rfl
      exact ⟨z.down, congr(($hz).down)⟩
    · rintro ⟨u, rfl⟩
      exact (h_comm B ⟨u⟩).subst (Subtype.mem _)
  choose R φ hφ using h_rep
  -- Map `A` to the product of the `R i` over the pieces `V i` that lie in `U`. By `h_cover` every
  -- point in a valuation ring lifts to one factor, so `reprMap π` has dense image.
  let I : Type := {i : J // (V i).whisker testIncl ≤ U}
  let π : A.obj ⟶ of (∀ i : I, R i) := ofHom (.pi fun i ↦ (φ i).hom)
  have h_dense : HasCohomDenseImage Λ (reprMap π) := by
    refine IsRelAffine.hasCohomDenseImage_of_lifts (.map uliftCoyoneda _) fun O ⟨f⟩ ↦ ?_
    obtain ⟨i, hi_le, hi_mem⟩ := h_cover O (Y.map f y)
    obtain ⟨u, rfl⟩ := (hφ i _ f).mp hi_mem
    exact ⟨⟨ofHom (evalRingHom _ (⟨i, hi_le⟩ : I)) ≫ u⟩, rfl⟩
  -- Density is transitive (`IsCohomDense.trans`) and Zariski local (`h_zar`), so it suffices that
  -- points of this image carry `y` into `U` Zariski locally. Let `f : A ⟶ C` factor through
  -- `g : ∏ R i ⟶ C`, and let `m` be a maximal ideal of `C`.
  have h_zar : HasZariskiDescent testIncl (locConstCoeff Λ) :=
    hasPartitions_locConstCoeff.hasZariskiDescent (𝟙 _) (by simp) fun C ↦
      C.property.isComparableRing
  refine h_dense.trans (U := U.preimage (mapOnTests (pointMap y)))
    (h_zar fun C ⟨⟨f⟩, ⟨g⟩, hfg⟩ m hm_max ↦ ?_) A ⟨𝟙 _⟩
  replace hfg : π ≫ g = f := congr(($hfg).down)
  -- The idempotents `single i 1` generate the unit ideal, so the image of one of them avoids `m`.
  obtain ⟨i, hi⟩ : ∃ i : I, g.hom (single i 1) ∉ m := by
    by_contra! h_mem
    exact comap_ne_top g.hom hm_max.ne_top
      (eq_top_mono (span_le.mpr (Set.range_subset_iff.mpr h_mem)) (span_single_eq_top _))
  -- Where it is inverted, `g` factors through the factor `R i`, so `y` lands in `V i ≤ U`.
  refine ⟨_, hi, fun D ⟨l⟩ hl ↦ i.property D ((hφ i _ (f ≫ l)).mpr ?_)⟩
  have h_ker : ker (evalRingHom (fun i : I ↦ R i) i) ≤ ker (g ≫ l).hom := fun x hx ↦ by
    -- `x` with `x i = 0` is killed by `single i 1`, which becomes a unit along `g ≫ l`
    have h_single : (single i 1 : (i : I) → R i) * x = 0 := by
      simp [← single_mul_left, show x i = 0 from hx]
    exact hl.mul_right_eq_zero.mp (by simp [← map_mul, h_single])
  obtain ⟨u, hu⟩ : ∃ u : R i →+* D.obj, u.comp (evalRingHom _ i) = (g ≫ l).hom :=
    ⟨_, liftOfSurjective_comp _ (Function.surjective_eval i) ⟨_, h_ker⟩⟩
  refine ⟨ofHom u, ?_⟩
  rw [← hfg]
  -- the component of `π` at `i` is `φ i`
  exact congr(π ≫ ofHom $hu)

end New.Variety

end ValuativeDensity

/-!
## Proper functors on rings: base change, dense images, continuity

Formal properties of proper functors on rings. `New.Variety.IsProperOver s`, for `s : Z ⟶ reprBy D`,
says that equality of two points is cut out by an ideal (`diagonal_closed`), and that one point of
`Z` specialises to every geometric point whose structure map lands in a valuation ring, through that
ring (`valuative_cover`).
-/

namespace New.Variety.IsProperOver

open CategoryTheory CartesianMonoidalCategory CommRingCat Functor ResiduePlace Pi Limits

variable {Y Z : PointFunctor} {D T : CommRingCat.{0}} {s : Z ⟶ reprBy D} {Λ : Ab.{0}} {c : Y ⟶ Z}

/-- Let `Z` be proper over `D` and `y ∈ Z(T)` a point. The map `reprBy T ⟶ Z` given by `y` is
relatively representable (`IsRelAffine`): its pull-back along every point `reprBy A ⟶ Z` is
representable. -/
lemma isRelAffine_pointMap (h : IsProperOver s) (y : Z.obj T) :
    IsRelAffine (pointMap y : reprBy T ⟶ Z) := by
  -- It suffices that the diagonal of `Z` is relatively representable. It is isomorphic to the
  -- inclusion of its image, which `h.diagonal_closed` cuts out by the vanishing of an ideal.
  have h_image : IsRelAffine (Subfunctor.range (lift (𝟙 Z) (𝟙 Z))).ι := by
    refine isRelAffine_ι_of_forall_map_mem_iff fun x ↦ ?_
    obtain ⟨I, hI⟩ := h.diagonal_closed _ x.1 x.2
    refine ⟨I, ∅, fun C f ↦ (Set.ext_iff.1 Set.range_diag _).trans ?_⟩
    -- membership in the diagonal says that the two components agree
    change Z.map f x.1 = Z.map f x.2 ↔ _
    simpa [IsConcreteLE.le_iff] using hI C f
  refine .of_diag (F := uliftCoyoneda) (h_image.baseChange
    (v := Subfunctor.toRange (lift (𝟙 Z) (𝟙 Z))) (u := (tensorLeftIsoProd Z).inv.app Z) ?_) _
  exact .of_horiz_isIso ⟨hom_ext _ _ (prod.lift_fst ..).symm (prod.lift_snd ..).symm⟩

/-- Let `V` be the fibre product of `u : Z ⟶ W` and `p : Y ⟶ W`, with projections `q : V ⟶ Z` and
`v : V ⟶ Y`. Let `Z` be proper over `D` (through `s`), `W` proper over `T` (through `b`) and `Y`
proper over `T` (through `p ≫ b`). If `u` is compatible with the structure maps along a ring map
`ψ : T ⟶ D`, then `V` is proper over `D` (through `q ≫ s`). -/
lemma of_isPullback (h : IsProperOver s) {V W : PointFunctor} {b : W ⟶ reprBy T} {v : V ⟶ Y}
    {q : V ⟶ Z} {p : Y ⟶ W} {u : Z ⟶ W} (hW : IsProperOver b) (h_pb : IsPullback q v u p)
    (hY : IsProperOver (p ≫ b)) (ψ : T ⟶ D) (hψ : u ≫ b = s ≫ reprMap ψ) :
    IsProperOver (q ≫ s) := by
  obtain ⟨h_comm, h_glue⟩ := isPullback_iff.mp h_pb
  have h_ext (C : CommRingCat) (x y : V.obj C) :
      x = y ↔ v.app C x = v.app C y ∧ q.app C x = q.app C y :=
    ⟨fun hxy ↦ by simp [hxy], fun hxy ↦ (h_glue C _ _ (h_comm C y)).unique hxy ⟨rfl, rfl⟩⟩
  refine ⟨fun C x y ↦ ?_, ?_⟩
  · -- two points of `V` agree iff their images in `Z` and in `Y` agree: add the two ideals
    obtain ⟨I, hI⟩ := h.diagonal_closed C (q.app C x) (q.app C y)
    obtain ⟨I', hI'⟩ := hY.diagonal_closed C (v.app C x) (v.app C y)
    refine ⟨I' ⊔ I, fun C' f ↦ ?_⟩
    simp only [h_ext, NatTrans.naturality_apply, hI, hI', sup_le_iff]
  -- Let `a ∈ Z(P)`, `c ∈ Y(Q)` be the points through which valuative points factor. The fibre
  -- product of `reprBy P` and `reprBy Q` over `W` is some `reprBy R`, and `a`, `c` glue to a point
  -- `x ∈ V(R)`.
  obtain ⟨P, a, ha⟩ := h.valuative_cover
  obtain ⟨Q, c, hc⟩ := hY.valuative_cover
  obtain ⟨⟨R⟩, ⟨g⟩, hR⟩ := hW.isRelAffine_pointMap (u.app P a) (pointMap (p.app Q c))
  obtain ⟨⟨φ⟩, hR⟩ := uliftCoyoneda.map_surjective.exists.mp hR
  obtain ⟨hR_comm, hR_glue⟩ := isPullback_iff.mp hR
  have h_agree : u.app R (Z.map φ a) = p.app R (Y.map g c) := by
    -- the square `hR` commutes at the identity of `R`; then use naturality of `u` and `p`
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    exact hR_comm R ⟨𝟙 R⟩
  obtain ⟨x, ⟨hx_snd, hx_fst⟩, -⟩ := h_glue R (Y.map g c) (Z.map φ a) h_agree
  refine ⟨R, x, fun {K} _ _ O z hz ↦ ?_⟩
  -- the images of `z` in `Z` and `Y` have integral structure maps, so they lift to `O`
  obtain ⟨f, hf⟩ := ha O (q.app (of K) z) hz
  have h_base : baseRingMap (p ≫ b) (v.app (of K) z) = ψ ≫ baseRingMap (q ≫ s) z :=
    calc baseRingMap (p ≫ b) (v.app (of K) z)
      _ = baseRingMap (u ≫ b) (q.app (of K) z) := congr(baseRingMap b $(h_comm _ z)).symm
      _ = ψ ≫ baseRingMap (q ≫ s) z := by rw [hψ]; rfl
  obtain ⟨l, hl⟩ := hc O (v.app (of K) z) fun d ↦ by simpa [h_base] using hz (ψ d)
  -- the lifts agree in `W` over the field, hence over `O`, so they come from one map `R ⟶ O`
  have h_generic : W.map (ofHom O.subtype) (W.map f (u.app P a)) =
      W.map (ofHom O.subtype) (W.map l (p.app Q c)) := by
    simpa only [← map_comp_apply, ← NatTrans.naturality_apply, hf, hl] using h_comm _ z
  obtain ⟨⟨k⟩, ⟨⟨⟩, ⟨⟩⟩, -⟩ :=
    hR_glue (of O) ⟨l⟩ ⟨f⟩ (hW.injective_map_valuationSubring O h_generic)
  exact ⟨k, (h_ext _ _ _).2 ⟨by simpa [hx_snd] using hl, by simpa [hx_fst] using hf⟩⟩

/-- The functor represented by a ring `R` is proper over `R`, through the identity map. -/
lemma _root_.New.Variety.isProperOver_id_reprBy {R : CommRingCat.{0}} :
    IsProperOver (𝟙 (reprBy R)) := by
  refine ⟨fun C x y ↦ ⟨⨆ d : R, .span {x.down.hom d - y.down.hom d}, fun C' f ↦ ?_⟩, R, ⟨𝟙 R⟩,
    fun O z hz ↦ ⟨ofHom (z.down.hom.codRestrict O hz), rfl⟩⟩
  -- two ring maps `x y : R ⟶ C` agree after `f` iff `f` kills all their differences
  have h_iff : x.down ≫ f = y.down ≫ f ↔
      ⨆ d : R, .span {x.down.hom d - y.down.hom d} ≤ RingHom.ker f.hom := by
    simp [ConcreteCategory.hom_ext_iff, sub_eq_zero]
  exact ULift.up_inj.trans h_iff

/-- The base change of a proper functor along a ring map `φ : D ⟶ T` is proper over `T`. -/
lemma baseChange (h : IsProperOver s) (φ : D ⟶ T) : IsProperOver (fibreProd.snd s (reprMap φ)) := by
  -- `reprBy T` is proper over itself; apply `of_isPullback` to the fibre product.
  exact isProperOver_id_reprBy.of_isPullback isProperOver_id_reprBy isPullback_fibreProd h φ rfl

/-- Let `c : Y ⟶ Z` be a map over `D`, with `Y` and `Z` proper over `D`, that is onto on points in
every algebraically closed field. Then `c` has dense image, for locally constant `Λ`-valued
coefficients. -/
lemma hasCohomDenseImage_of_surjective (h : IsProperOver s) (hY : IsProperOver (c ≫ s))
    (h_surj : ∀ (k : Type) [Field k] [IsAlgClosed k], Function.Surjective (c.app (of k))) :
    HasCohomDenseImage Λ c := by
  -- Let `a` be the universal point of `Y` given by properness. Its image in `Z` is again an atlas:
  -- a point `y` of `Z` in a valuation ring lifts generically to `Y`, that lift comes from `a`, and
  -- `Z` is separated. The atlas has dense image and factors through `c`.
  obtain ⟨T, a, ha⟩ := hY.valuative_cover
  have h_dense : HasCohomDenseImage Λ (pointMap (c.app T a)) := by
    refine (h.isRelAffine_pointMap _).hasCohomDenseImage_of_lifts fun {K} _ _ O y ↦ ?_
    obtain ⟨x, hx⟩ := h_surj K (Z.map (ofHom O.subtype) y)
    have hx_mem (d : D) : baseRingMap (c ≫ s) x d ∈ O := by
      have h_base : baseRingMap (c ≫ s) x = baseRingMap s y ≫ ofHom O.subtype :=
        calc baseRingMap (c ≫ s) x
          _ = baseRingMap s (c.app (of K) x) := rfl
          _ = baseRingMap s (Z.map (ofHom O.subtype) y) := by rw [hx]
          _ = baseRingMap s y ≫ ofHom O.subtype := baseRingMap_map ..
      simp [h_base]
    obtain ⟨u, hu⟩ := ha O x hx_mem
    have h_generic : Z.map (ofHom O.subtype) (Z.map u (c.app T a)) = Z.map (ofHom O.subtype) y := by
      rw [← hx, ← hu, NatTrans.naturality_apply, map_comp_apply]
    exact ⟨⟨u⟩, h.injective_map_valuationSubring O h_generic⟩
  exact h_dense.mono fun A _ ⟨u, hu⟩ ↦ ⟨_, (c.naturality_apply _ a).trans hu⟩

/-- Let `Z` be proper over `D` via `s`. Then there are a ring `P`, a point `ξ ∈ Z(P)` and a
valuative lift `z` of `ξ`, meaning a point of `Z` over the product of the valuation rings of all
places of `P` (a place is a prime of `P` with a valuation ring of its residue field containing the
image of `D` under `baseRingMap s ξ`) that agrees with `ξ` over the product of their residue fields.
For these, `placeSpaceMap z` has cohomologically dense image (`HasCohomDenseImage`) for the
coefficients sending `A` to the locally constant functions `Spec A → Λ`; this is the map to `Z` from
the space of places of `z`, sending the class of `f` to `f z`, and dense image means that its image,
restricted to test rings, is dense in `Z`. -/
lemma exists_valuativeLift_hasCohomDenseImage (h : IsProperOver s) :
    ∃ (P : CommRingCat) (ξ : Z.obj P) (z : ValuativeLift s ξ),
      HasCohomDenseImage Λ (placeSpaceMap z) := by
  -- With `a` the universal point of `Z`, over `T`, take for `P` the product of the algebraic
  -- closures of the residue fields of `T` and for `ξ` the image of `a`.
  obtain ⟨T, a, ha⟩ := h.valuative_cover
  let K (j : PrimeSpectrum T) : Type := AlgebraicClosure j.asIdeal.ResidueField
  let P : CommRingCat := of (∀ j, K j)
  let ξ : Z.obj P := Z.map (ofHom (algebraMap T P)) a
  have h_flat (x : ∀ j, K j) : ∃ y : ∀ j, K j, y * x * x = x := ⟨x⁻¹, funext fun _ ↦ by simp⟩
  have h_closed (q : Ideal P) [q.IsPrime] : IsAlgClosed q.ResidueField := by
    -- `P` is a test ring, so its local ring at `q` is absolutely integrally closed
    obtain ⟨h_aic, -⟩ :=
      (IsTest.pi fun _ ↦ isTest_of_preValuationRing : IsTest P).exists_valuationSubring_atPrime q
    infer_instance
  -- At each place `j` the point `ξ` comes from `a` by a map `u j` into the valuation ring.
  have h_lift (j : ResiduePlace (baseRingMap s ξ)) : ∃ u : T ⟶ of j.valuationSubring,
      Z.map (u ≫ ofHom j.valuationSubring.subtype) a = Z.map (ofHom (algebraMap T j.PlaceField))
        a := by
    have h_mem (d : D) :
        baseRingMap s (Z.map (ofHom (algebraMap T j.PlaceField)) a) d ∈ j.valuationSubring := by
      simpa [ξ, IsScalarTower.algebraMap_apply T P j.PlaceField] using j.base_mem d
    exact ha _ _ h_mem
  choose u hu using h_lift
  let z : Z.obj (prodValuationRing (baseRingMap s ξ)) := Z.map (ofHom (.pi fun j ↦ (u j).hom)) a
  have hz : Z.map toFieldProd z = Z.map (ofHom (algebraMap P _)) ξ := by
    refine h.ext_of_jointly_injective (fun j ↦ ofHom (evalRingHom _ j))
      (fun _ h_zero ↦ funext h_zero) fun j ↦ ?_
    -- at the place `j`, both sides are the image of `a` under `T ⟶ κ(j)`
    calc Z.map (ofHom (evalRingHom _ j)) (Z.map toFieldProd z)
      _ = Z.map (u j ≫ ofHom j.valuationSubring.subtype) a := by
        simp only [z, ← map_comp_apply]
        rfl
      _ = Z.map (ofHom (algebraMap T j.PlaceField)) a := hu j
      _ = Z.map (ofHom (evalRingHom _ j)) (Z.map (ofHom (algebraMap P _)) ξ) := by
        simp only [ξ, ← map_comp_apply]
        rfl
  -- By `hasCohomDenseImage_of_surjective` it is enough that every point `y` of `Z` in an
  -- algebraically closed field `L` comes from a place. It comes from a map `T → L`, which extends
  -- to `P` through the factor `K q`, where `q` is its kernel.
  refine ⟨P, ξ, ⟨z, hz, h, h_flat, h_closed⟩,
    h.hasCohomDenseImage_of_surjective isProperOver_placeSpace fun L _ _ y ↦ ?_⟩
  choose v hv using ha ⊤ y (by simp)
  choose q l hl using exists_algebraMap_residueField_comp_eq
    (v ≫ ofHom (ValuationSubring.subtype _))
  algebraize [l.hom]
  -- `k` extends the map `l` from the residue field at `q` to its algebraic closure `K q`
  let k : K q →ₐ[_] L := IsAlgClosed.lift (R := q.asIdeal.ResidueField)
  choose p m hm using
    exists_algebraMap_residueField_comp_eq (P := P) (ofHom (k.toRingHom.comp (evalRingHom K q)))
  -- The place is the kernel `p` of that extension, with the trivial valuation ring.
  let j : ResiduePlace (baseRingMap s ξ) := ⟨p, ⊤, by simp⟩
  let π : of (∀ i : ResiduePlace (baseRingMap s ξ), i.PlaceField) ⟶ of L :=
    ofHom (evalRingHom PlaceField j) ≫ m
  refine ⟨⟨⟦toFieldProd ≫ π⟧⟩, ?_⟩
  calc Z.map (toFieldProd ≫ π) z
    _ = Z.map π (Z.map (ofHom (algebraMap P _)) ξ) := by rw [map_comp_apply, hz]
    _ = y := by
      simp_rw [ξ, ← hv, ← map_comp_apply, ← hl]
      congr 3 with x
      exact congr($hm _).trans (k.commutes _)

/-- A functor of points that is proper over `D` has the continuity property `IsCohomContinuous`
for filtered limits, with locally constant `Λ`-valued coefficients. -/
lemma isCohomContinuous (h : IsProperOver s) : IsCohomContinuous Λ Z := by
  -- The universal point `a` given by properness is an atlas with dense image: a point `y` in a
  -- valuation ring comes from `a` generically, hence integrally since `Z` is separated.
  obtain ⟨T, a, ha⟩ := h.valuative_cover
  have h_dense : HasCohomDenseImage Λ (pointMap a) := by
    refine (h.isRelAffine_pointMap a).hasCohomDenseImage_of_lifts fun O y ↦ ?_
    obtain ⟨u, hu⟩ := ha O (Z.map (ofHom O.subtype) y) (by simp)
    have h_generic : Z.map (ofHom O.subtype) (Z.map u a) = Z.map (ofHom O.subtype) y := by
      rwa [← map_comp_apply]
    exact ⟨⟨u⟩, h.injective_map_valuationSubring O h_generic⟩
  exact .of_hasCohomDenseImage (h.isRelAffine_pointMap a) h_dense

end New.Variety.IsProperOver

/-! ## Density of subfunctors holding the points that keep the coincidences at a geometric point -/

open CategoryTheory in
/-- Let `Z` be proper over `D` via `s` (`IsProperOver`: closed diagonal plus a uniform valuative
criterion), let `P i : Y ⟶ Z` be finitely many maps, and let `U` be a subfunctor of `Y` restricted
to test rings (`TestRing`, via `testIncl`). Suppose that for every point `z` of `Y` over an
algebraically closed field, `U` contains every point `x` of `Y` over a test ring that keeps the
coincidences of `z`: whenever `P i` and `P j` agree at `z` they agree at `x`. Then `U` is dense
(`IsCohomDense`) for the coefficients `locConstCoeff Λ` (A ↦ locally constant functions Spec A → Λ):
for every point h_A → Y, the inclusion of the preimage of `U` into h_A induces bijections on all
`Ext^n(−, locConstCoeff Λ)`. -/
lemma New.Variety.IsProperOver.isCohomDense_of_coincidences {Λ : Ab}
    {Y Z : CommRingCat ⥤ Type 1} {D : CommRingCat} {s : Z ⟶ reprBy D}
    (h : IsProperOver s) {U : Subfunctor (testIncl ⋙ Y)}
    {J : Type} [Finite J] (P : J → (Y ⟶ Z))
    (h_pattern :
      ∀ {k : Type} [Field k] [IsAlgClosed k] (z : Y.obj (CommRingCat.of k)) (B : TestRing)
        (x : (testIncl ⋙ Y).obj B),
        (∀ i j : J, (P i).app (CommRingCat.of k) z = (P j).app (CommRingCat.of k) z →
          (P i).app B.obj x = (P j).app B.obj x) →
        x ∈ U.obj B) :
    IsCohomDense (Y := testIncl ⋙ Y) (locConstCoeff Λ) U := by
  -- Cover `Y` by the loci `V ε` where `P i` and `P j` agree for all `j ∈ ε i`; there are finitely
  -- many patterns `ε`. By `IsCohomDense.of_affine_cover` it suffices that each `V ε` is relatively
  -- affine and that each point over a valuation ring `O` of an algebraically closed field lies in
  -- some `V ε` contained in `U`.
  let V (ε : J → Set J) : Subfunctor Y :=
    ⟨fun A ↦ {y | ∀ i, ∀ j ∈ ε i, P i A y = P j A y},
      fun f y hy i j hij ↦ by simpa using congrArg (Z.map f) (hy i j hij)⟩
  refine .of_affine_cover (V := V) (fun ε ↦ isRelAffine_ι_of_forall_map_mem_iff fun {R} y ↦ ?_)
    fun {K} _ _ O y ↦ ?_
  · -- `Z` is separated, so `V ε` is cut out by the ideals `I` of the coincidences.
    choose I hI using h.diagonal_closed
    refine ⟨⋃ (i) (j ∈ ε i), I _ (P i _ y) (P j _ y), ∅, fun B f ↦ ?_⟩
    -- by naturality, `P i` and `P j` agree at `f y` iff `f` kills the ideal of their values at `y`
    have h_pair (i j : J) : Z.map f ((P i).app R y) = Z.map f ((P j).app R y) ↔
        ∀ a ∈ I R ((P i).app R y) ((P j).app R y), f a = 0 :=
      (hI R _ _ B f).trans IsConcreteLE.le_iff
    -- both sides say that `f` kills `I (P i y) (P j y)` whenever `j ∈ ε i`
    aesop (add simp [V, h_pair])
  · -- A point `y` over `O` has the coincidences of its generic point `z`, as points of `Z` over `O`
    -- inject into points over the field; the locus of this pattern lies in `U` by `h_pattern`.
    let z : Y.obj (CommRingCat.of K) := Y.map (CommRingCat.ofHom O.subtype) y
    refine ⟨fun i ↦ {j | P i _ z = P j _ z}, h_pattern z, fun i j hij ↦ ?_⟩
    have h_generic : Z.map (CommRingCat.ofHom O.subtype) ((P i).app _ y) =
        Z.map (CommRingCat.ofHom O.subtype) ((P j).app _ y) := by
      simpa [z, CategoryTheory.NatTrans.naturality_apply] using hij
    exact h.injective_map_valuationSubring O h_generic

/-! ## Transfer for Galois coverings -/

section Transfer

open CategoryTheory AlgebraicGeometry Fintype Set

attribute [local instance low] Fintype.ofFinite

/-- Let `c : W ⟶ Y` be a Galois covering of proper `R`-schemes (`IsGaloisCovering`: `Δ` acts on `W`
over `Y` through `a`, `c` is onto, and `Δ` acts simply transitively on fibres over fields of
characteristic zero), and `Ω` the fixed algebraic closure of `ℚ` as an `R`-algebra. After base
change to `Ω` (`geomPoints`), `c` has dense image for locally constant `Λ`-valued coefficients. -/
lemma New.Variety.IsGaloisCovering.hasCohomDenseImage_geomPoints {R : CommRingCat}
    [Algebra R Ω] {W Y : Over (Spec R)} {c : W ⟶ Y} {Δ : FiniteGrp.{0}} {a : Δ →* End W}
    [IsProper W.hom] [IsProper Y.hom] (h : IsGaloisCovering c a) (Λ : Ab.{0}) :
    HasCohomDenseImage Λ ((geomPoints R Ω).map c) := by
  -- `W`, `Y` are proper, so it suffices that `c` is onto on geometric points.
  refine ((isProperOver_pointsToBase _).baseChange _).hasCohomDenseImage_of_surjective
    ((isProperOver_pointsToBase _).baseChange _) fun k _ _ ⟨⟨⟨y_pt⟩, ω⟩, hy⟩ ↦ ?_
  -- lift the scheme point `y_pt` of `Y` to a point `x` of `W`, and keep the map `ω` out of `Ω`
  obtain ⟨x, hx⟩ : ∃ x : Spec (CommRingCat.of k) ⟶ W.left, x ≫ c.left = y_pt :=
    exists_point_over _ (h.surjective.surj _)
  have h_over : x ≫ W.hom = y_pt ≫ Y.hom := by simp [← hx]
  have h_base : (pointsToBase W.hom).app (CommRingCat.of k) ⟨x⟩ =
      (pointsToBase Y.hom).app (CommRingCat.of k) ⟨y_pt⟩ :=
    congr(ULift.up (Spec.preimage $h_over))
  exact ⟨⟨(⟨x⟩, ω), h_base.trans hy⟩, Subtype.ext (Prod.ext (congrArg ULift.up hx) rfl)⟩

/-- Let `c : W ⟶ Y` be a Galois covering of `R`-schemes with finite group `Δ` and `W` proper. After
base change to `Ω` (`geomPoints`), the pairs in `W ×_Y W` whose `Δ`-orbits agree up to a permutation
of `Δ` (`permutedPairs`) are dense, for locally constant `Λ`-valued coefficients. -/
lemma New.Variety.IsGaloisCovering.isCohomDense_permutedPairs {R : CommRingCat}
    [Algebra R Ω] {W Y : Over (Spec R)} {c : W ⟶ Y} {Δ : FiniteGrp.{0}} {a : Δ →* End W}
    [IsProper W.hom] (h : IsGaloisCovering c a) (Λ : Ab.{0}) :
    IsCohomDense (locConstCoeff Λ)
      (permutedPairs (fun g : Δ ↦ mapOnTests ((geomPoints R Ω).map (a g).asHom))
        (mapOnTests ((geomPoints R Ω).map c))) := by
  -- It suffices to treat points `x` in which the `g (x i)` keep the coincidences of the
  -- `g (z i)` for a geometric point `z` of `W ×_Y W`. Now `z 1 = d (z 0)` for some `d ∈ Δ`,
  -- so `g (z 1) = (g * d) (z 0)`, the same holds for `x`, and `· * d` permutes `Δ`.
  refine ((isProperOver_pointsToBase _).baseChange _).isCohomDense_of_coincidences
    (fun g : Fin 2 × Δ ↦
      cech.proj ((geomPoints R Ω).map c) 1 g.fst ≫ (geomPoints R Ω).map (a g.snd).asHom)
    fun {k} _ _ z B x hx ↦ ?_
  -- the scheme points `z₀ z₁` of `W` of the two components of `z`, which lie over one point of
  -- `Y` and carry the same map out of `Ω`
  set z₀ : Spec (CommRingCat.of k) ⟶ W.left := (z.val 0).val.fst.down
  set z₁ : Spec (CommRingCat.of k) ⟶ W.left := (z.val 1).val.fst.down
  have h_over : z₀ ≫ c.left = z₁ ≫ c.left := congr($(z.property 0 1).val.fst.down)
  have h_ω : (z.val 0).val.snd = (z.val 1).val.snd := congr($(z.property 0 1).val.snd)
  have h_charZero : CharZero k := (z.val 0).val.snd.down.hom.toAlgebra.charZero_of_charZero
  obtain ⟨d, hd, -⟩ : ∃! d : Δ, z₀ ≫ (a d).asHom.left = z₁ := h.torsor k z₀ z₁ h_over
  have h_mul (g : Δ) : z₀ ≫ (a (g * d)).asHom.left = z₁ ≫ (a g).asHom.left := by
    rw [map_mul, End.mul_asHom, Over.comp_left, ← Category.assoc, hd]
  refine ⟨Equiv.mulRight d, fun g ↦ ?_⟩
  -- at `z`, the maps indexed by `(0, g * d)` and `(1, g)` agree, hence also at `x`
  have h_z : ((geomPoints R Ω).map (a (g * d)).asHom).app _ (z.val 0) =
      ((geomPoints R Ω).map (a g).asHom).app _ (z.val 1) :=
    Subtype.ext (Prod.ext (congrArg ULift.up (h_mul g)) h_ω)
  exact (hx (0, g * d) (1, g) h_z).symm

open TensorProduct in
/-- Let `c : W ⟶ Y` be a Galois covering of proper `R`-schemes with finite group `Δ` acting through
`a` (`IsGaloisCovering`: `Δ` acts over `Y`, `c` is onto, and `Δ` acts simply transitively on the
fibres over fields of characteristic zero), `Ω` the fixed algebraic closure of `ℚ` as an `R`-algebra
and `ℓ` a prime. Then pull-back along `c` on `ℓ`-adic cohomology `ellAdicCohom R Ω n` is (a)
injective, and (b) every class on `W` fixed by `Δ` lies in its image. -/
lemma New.Variety.ellAdicCohom.transfer {R : CommRingCat} [Algebra R.carrier Ω]
    {W Y : Over (Spec R)} {c : W ⟶ Y} {Δ : FiniteGrp.{0}} {a : Δ.toGrp →* End W} [IsProper W.hom]
    [IsProper Y.hom] (h : IsGaloisCovering c a) (ℓ : ℕ) [ThePrime ℓ] (n : ℕ) :
    Function.Injective ((ellAdicCohom (ℓ := ℓ) R Ω n).map c.op) ∧
    ∀ y : (ellAdicCohom (ℓ := ℓ) R Ω n).obj (Opposite.op W),
      (∀ g : Δ.toGrp, (ellAdicCohom (ℓ := ℓ) R Ω n).map (a g).asHom.op y = y) →
        y ∈ range ((ellAdicCohom (ℓ := ℓ) R Ω n).map c.op) := by
  -- On the free abelian functors of points, `exists_transfer_map` factors `c = m ≫ l` and
  -- `∑ g = m ≫ ν` with `ν ≫ c = |Δ| • l`. Two density conditions make `l^*` bijective; then
  -- `N = |Δ|⁻¹ ν^*` has `N ∘ c^* = l^*`, and `m^* ∘ N` is the average over `Δ`.
  -- each element of `Δ` acts over `Y`
  have h_comm (g : Δ.toGrp) :
      (geomPoints R Ω ⋙ onTests).map (a g).asHom ≫ (geomPoints R Ω ⋙ onTests).map c =
        (geomPoints R Ω ⋙ onTests).map c := by
    rw [← Functor.map_comp, h.comp_eq g]
  obtain ⟨Q, m, l, ν, h_ml, h_mν, h_νc, h_eqv⟩ := exists_transfer_map h_comm
  dsimp [ellAdicCohom] at *
  -- By `h_eqv`, `l` is an equivalence for `𝔽_ℓ`-coefficients, as two subfunctors are dense: the
  -- image of `c`, and the pairs in `W ×_Y W` whose `Δ`-orbits agree up to a permutation.
  have h_bij : Function.Bijective (ellAdicPull (ℓ := ℓ) n l) :=
    (h_eqv (locConstCoeff ⟨ZMod ℓ⟩) (h.hasCohomDenseImage_geomPoints _)
      (h.isCohomDense_permutedPairs _)).bijective_ellAdicPull
  let N : ℚ_[ℓ] ⊗[ℤ_[ℓ]] H (freeAb.obj (testIncl ⋙ (geomPoints R Ω).obj W)) ellAdicCoeff n →ₗ[ℚ_[ℓ]]
      ℚ_[ℓ] ⊗[ℤ_[ℓ]] H Q ellAdicCoeff n :=
    (card Δ : ℚ)⁻¹ • ellAdicPull n ν
  have h_left
      (x : ℚ_[ℓ] ⊗[ℤ_[ℓ]] H (freeAb.obj (testIncl ⋙ (geomPoints R Ω).obj Y)) ellAdicCoeff n) :
      N (ellAdicPull n (freeAb.map (mapOnTests ((geomPoints R Ω).map c))) x) =
        ellAdicPull n l x := by
    simp [N, ellAdicPull.comp, ← Nat.cast_smul_eq_nsmul ℚ, h_νc]
  refine ⟨fun x x' hx ↦ h_bij.injective ?_, fun y hy ↦ ?_⟩
  · -- `l^* x = N (c^* x) = N (c^* x') = l^* x'`
    exact (h_left x).symm.trans ((congrArg N hx).trans (h_left x'))
  obtain ⟨x, hx⟩ : N y ∈ range (ellAdicPull n l) := h_bij.surjective (N y)
  -- `c^* x = m^* (l^* x) = m^* (N y)` is the average of the `g^* y = y`
  have h_pull : ellAdicPull n m (ellAdicPull n l x) = ellAdicPull n (m ≫ l) x :=
    ellAdicPull.comp m l x
  rw [h_ml] at h_pull
  refine ⟨x, h_pull.symm.trans ?_⟩
  have hy_fixed : ∀ g : Δ.toGrp,
      ellAdicPull n (freeAb.map (testIncl.whiskerLeft ((geomPoints R Ω).map (a g).asHom))) y =
        y := hy
  simp [N, ellAdicPull.comp, ← Nat.cast_smul_eq_nsmul ℚ, hx, h_mν, hy_fixed]

end Transfer
