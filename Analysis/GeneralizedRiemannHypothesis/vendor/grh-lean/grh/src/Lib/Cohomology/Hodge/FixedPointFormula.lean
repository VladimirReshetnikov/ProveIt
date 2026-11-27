import Lib.Adelic.Unitary.Defs
import Lib.Cohomology.Hodge.DiagonalClass
import Lib.Cohomology.Hodge.Kunneth
import Lib.General.Algebra.MultivariatePolynomials

/-!
# Reduced coincidences and the fixed point formula in Hodge cohomology

Let `W`, `X` be functors from `k`-algebras to sets (`New.Variety.CommAlg k ⥤ Type 1`), standing for
schemes, and let `u c : W ⟶ X` be two maps. A coincidence is a point `x` of `W` with `c x = u x`.
The file proves the fixed point formula in Hodge cohomology `Hdg^d(W)`, that is
`HodgeH (freeAb.obj W) d`, computed on square-zero extensions `A ⊕ M`: a pulled-back diagonal class
is a sum of point classes `New.Variety.pointClass d w` over the coincidences, weighted by Jacobian
determinants. If `k` is algebraically closed, `X` is separated, every `k[ε]`-valued coincidence is
constant and finitely many charts of `W` contain all field-valued coincidences, then the
coincidences form a finite set of rational points, which carry these local terms.

## Main definitions and results

* `New.Variety.ConstIfCoincident`, `New.Variety.IsCoincidenceSet`: reduced coincidences, and a
  finite set of rational points that lists them all.
* `New.Variety.HasJacobianRatio`: the local term, the determinant of `(t du - dc) (du - dc)⁻¹`.
* `New.Variety.IsTangentPoly.hasJacobianRatio_eval_div`: a tangent polynomial `P` with `P 1 ≠ 0`
  gives this term as `P t / P 1`; by `New.Variety.IsTangentPoly.constIfCoincident` the coincidences
  at that point are then reduced.
* `New.Variety.scaledGraph`: the graph of `(u, c)` twisted by the scaling of `M` by `t` in the first
  factor.
* `New.Variety.exists_diagonal_local_terms`: the class `δ` of the diagonal, pulled back along this
  twisted graph, is `∑ n w • pointClass d w` over the coincidences `w` of `u` and `c`, where `n w`
  is the determinant of a matrix `N` with `t du - dc = N (du - dc)` at `w`
  (`New.Variety.HasJacobianRatio`).
* `New.Variety.IsPointSum.cup_pointClass`: the external product of the class of a point of `X` and
  the class of a point of a curve is the class of the product point.

Notions from other files:
* `New.Variety.HodgeH`: Hodge cohomology: for a functor N from k-algebras to abelian groups, Ext^q
  from (A, M) ↦ N(A ⊕ M) to (A, M) ↦ ⋀_A M, in functors on pairs.
* `New.Variety.symbolClass`: The Grothendieck symbol [dT/T] in Hdg^d(𝔸^d, 𝔸^d ∖ 0); its pull-back
  along a tuple f of functions is the symbol [df/f].
* `New.Variety.IsPointSum`: A relative class has multiplicity n z at each z in s: on some chart
  containing z it restricts to n z times the symbol [dg / g] of functions g that cut out z.
* `New.Variety.IsTangentPoly`: at a point `y ∈ W(k)`, the tangent map `dc` on the tangent space of
  dimension `d` is injective, `du = dc ∘ B`, and `P t = P 0 * det (1 - t B)`.
* `New.Variety.HasAtlas`: X is separated and has finitely many charts, each with exactly d étale
  coordinates, that contain every field-valued point.
* `New.Variety.offPoints`: for a set s of k-points of X, the subfunctor of the points none of whose
  values in fields comes from s.
* `New.Variety.exteriorAlg`, `CategoryTheory.Functor.mulPairing`: the exterior algebra ⋀_A M of a
  pair (A, M), and the pairing given by its multiplication (the wedge product of coefficients in the
  cup product).
* `New.Variety.freeAb.prod`: for set-valued functors X, Y, the map ℤ[X × Y] → ℤ[X] ⊗ ℤ[Y], [(x,
  y)] ↦ [x] ⊗ [y].

## Relation to the literature

Known result: the fixed point formula in Hodge cohomology, with local terms computed by
Grothendieck symbols. Here the setting is characteristic 0 and smooth separated varieties with a
finite atlas, with cohomology taken as Ext of functors. The class of the diagonal and Künneth
surjectivity for X×X are not proved here; they come from `exists_diagonal_class` and `kunneth` in
other files. Here the point classes are multiplied for a product with a curve, and the pull-back of
the diagonal class along reduced coincidences is given as a weighted sum of point classes. Source:
Stacks Project, tags 0BEC (Künneth) and 0G82 (Gysin maps); A. Chatzistamatiou, K. Rülling, Higher
direct images of the structure sheaf in positive characteristic, Algebra & Number Theory 5 (2011)
693-775, sections 2-3; V. Srinivas, Gysin maps and cycle classes for Hodge cohomology, Proc. Indian
Acad. Sci. Math. Sci. 103 (1993) 209-247; Hartshorne, Residues and Duality (1966) III.9 for the
symbol.

See also `Lib.Cohomology.WoodsHole` and `Lib.Cohomology.PointClass.LinearIndependence`.
-/

namespace New.Variety

/-!
## Reduced coincidences and their Jacobian determinants

A chart `New.Variety.EtaleChart d X` is an affine open of `X` with `d` étale coordinates, given by a
ring `R` and a point of `X` in `R`; its locus `New.Variety.EtaleChart.locus` is the open subfunctor
of the points that come from `R`. Tangent vectors are `k[ε]`-points; `New.Variety.SqZeroExt.fst` is
the map `k ⊕ M → k` (so `k[ε] → k`) and `New.Variety.structureMap` the structure map of a
`k`-algebra.
-/

section IsolatedCoincidences

open CategoryTheory Ideal CommAlgCat Algebra TrivSqZeroExt Matrix Set SqZeroExt NatTrans DualNumber
  Module

variable {k E : Type} {d : ℕ} [Field k] {W X : CommAlg k ⥤ Type 1} [Field E] [Algebra E k]

/-- For two maps `u c : W ⟶ X`: if the `k[ε]`-valued point `x` of `W` is a coincidence of `u` and
`c`, then it is constant, that is, the image of its base point under `k → k[ε]`. -/
abbrev ConstIfCoincident (u c : W ⟶ X) (x : W.obj (CommAlgCat.of k k[ε])) : Prop :=
  c.app (CommAlgCat.of k k[ε]) x = u.app (CommAlgCat.of k k[ε]) x →
    x = W.map (SqZeroExt.fst ≫ structureMap) x

/-- The finite set `s` of `k`-points of `W` is the set of coincidences of the maps `u c : W ⟶ X`,
and these are reduced: every `k[ε]`-valued coincidence is constant, every point of `s` is a
coincidence, and every field-valued coincidence comes from a point of `s`. -/
def IsCoincidenceSet (u c : W ⟶ X) (s : Finset (W.obj (CommAlgCat.of k k))) : Prop :=
  (∀ x : W.obj (CommAlgCat.of k k[ε]), ConstIfCoincident u c x) ∧
  (∀ w ∈ s, c.app (CommAlgCat.of k k) w = u.app (CommAlgCat.of k k) w) ∧
  ∀ K : CommAlg k, IsField K → ∀ x : W.obj K, c.app K x = u.app K x →
    ∃ w ∈ s, x = W.map structureMap w

/-- Let `k` be algebraically closed, `X` separated (`IsSeparatedFunctor X`) and `u c : W ⟶ X` two
maps. Suppose that every `k[ε]`-valued coincidence of `u` and `c` is constant (`h_red`) and that
finitely many charts `a i` of `W`, affine opens with `d` étale coordinates, contain all
field-valued coincidences (`h_cover`). Then there is a finite set `s` of `k`-points of `W` with
`IsCoincidenceSet u c s`: the coincidences are the points of `s`, and they are reduced. -/
lemma exists_isCoincidenceSet (u c : W ⟶ X) [IsAlgClosed k] [hX : IsSeparatedFunctor X]
    (h_red : ∀ x : W.obj (CommAlgCat.of k k[ε]), ConstIfCoincident u c x)
    {ι : Sort*} [Finite ι] (a : ι → EtaleChart d W)
    (h_cover : ∀ K : CommAlg k, IsField K → ∀ x : W.obj K, c.app K x = u.app K x →
      ∃ i : ι, x ∈ (a i).locus.obj K) :
    ∃ s : Finset (W.obj (CommAlgCat.of k k)), IsCoincidenceSet u c s := by
  -- In each chart the coincidences are cut out by an ideal `J i`. Choose a rational point on each
  -- of its finitely many components; as the coincidences have no nonzero tangent vectors
  -- (`h_red`), a component is that point.
  have h_ideal (i : ι) : ∃ J : Ideal (a i).coordRing, ∀ (B : CommAlg k) (φ : (a i).coordRing ⟶ B),
      c.app B (W.map φ (a i).point) = u.app B (W.map φ (a i).point) ↔ J ≤ RingHom.ker φ.hom := by
    simpa [← naturality_apply] using
      hX.exists_ideal (a i).coordRing (c.app (a i).coordRing (a i).point)
        (u.app (a i).coordRing (a i).point)
  choose J hJ using h_ideal
  have h_point ⦃i : ι⦄ ⦃p : Ideal (a i).coordRing⦄ (hp : p ∈ (J i).minimalPrimes) :
      ∃ o : (a i).coordRing →ₐ[k] k, p ≤ RingHom.ker o :=
        nullstellensatz_exists_le_ker hp.isPrime.ne_top
  choose o ho using h_point
  have h_fin (i : ι) : (J i).minimalPrimes.Finite :=
    have : IsNoetherianRing (a i).coordRing := FiniteType.isNoetherianRing k (a i).coordRing
    finite_minimalPrimes_of_isNoetherianRing (a i).coordRing (J i)
  -- `s` is the finite set of these points, over all charts and all minimal primes.
  let s : Finset (W.obj (CommAlgCat.of k k)) := (finite_iUnion fun i ↦
    (h_fin i).dependent_image fun p hp ↦ W.map (ofHom (o hp)) (a i).point).toFinset
  have h_mem (w : W.obj (CommAlgCat.of k k)) : w ∈ s ↔ ∃ (i : ι) (p : Ideal (a i).coordRing)
      (hp : p ∈ (J i).minimalPrimes), W.map (ofHom (o hp)) (a i).point = w := by
    simp [s]
  refine ⟨s, h_red, ?_, ?_⟩
  · -- The point `o hp` kills `J i`, so it is a coincidence.
    intro w hw
    obtain ⟨i, p, hp, rfl⟩ := (h_mem w).mp hw
    exact (hJ i (CommAlgCat.of k k) (ofHom (o hp))).mpr (hp.le.trans (ho hp))
  · -- A coincidence `x` with values in a field comes from a map `φ` out of the ring of a chart.
    intro K hK x hx
    obtain ⟨i, ⟨φ : (a i).coordRing ⟶ K⟩, (rfl : W.map φ (a i).point = x)⟩ := h_cover K hK x hx
    -- The kernel of `φ` is a prime containing `J i`, so it contains a minimal prime `p` of `J i`.
    have : IsDomain K := hK.isDomain
    have : (RingHom.ker φ.hom).IsPrime := RingHom.ker_isPrime φ.hom
    obtain ⟨p, hp, hp_ker⟩ := exists_minimalPrimes_le ((hJ i K φ).mp hx)
    -- A tangent vector at the point `o hp` that kills `J i` is a coincidence, hence constant: its
    -- `ε`-coordinates vanish.
    have h_tangent : ∀ v : (a i).coordRing →ₐ[k] k[ε], (∀ r : (a i).coordRing, (v r).fst = o hp r) →
        J i ≤ RingHom.ker v → ∀ r : (a i).coordRing, (v r).snd = 0 := by
      rintro v - hv_ker r
      have h_const : ofHom v = ofHom v ≫ SqZeroExt.fst ≫ structureMap :=
        (a i).eq_comp_of_map_point_eq _ (h_red _ ((hJ i _ (ofHom v)).mpr hv_ker))
      have h_const_r : v r = algebraMap k k[ε] (v r).fst := ConcreteCategory.congr_hom h_const r
      rw [h_const_r, algebraMap_eq_inl', snd_inl]
    -- So by Nakayama some `b` with `o hp b ≠ 0` multiplies the ideal of that point into `J i`.
    obtain ⟨b, hb, hb_ne⟩ : ∃ b ∈ (J i).colon (RingHom.ker (o hp)), o hp b ≠ 0 :=
      exists_mem_colon_of_tangent (k := k) rfl (hp.le.trans (ho hp)) h_tangent
    -- Since `b ∉ p`, that ideal lies in `p`, so `φ` factors through the point.
    have h_ker : RingHom.ker (o hp) ≤ p := fun r hr ↦
      (hp.isPrime.mem_or_mem (hp.le (Submodule.mem_colon.mp hb r hr))).resolve_left
        fun hb_mem ↦ hb_ne (RingHom.mem_ker.mp (ho hp hb_mem))
    obtain rfl : φ = ofHom (o hp) ≫ structureMap :=
      eq_comp_structureMap_of_ker_le (h_ker.trans hp_ker)
    exact ⟨_, (h_mem _).mpr ⟨i, p, hp, rfl⟩, W.map_comp_apply (ofHom (o hp)) structureMap _⟩

/-- For a scalar `t` of `k`, the number `n` is `det ((t du - dc) (du - dc)⁻¹)` at `w`: in every
chart `A` of `X` that contains `c w` there is a matrix `N` of determinant `n` with
`t du v - dc v = N (du v - dc v)` for all tangent vectors `v` at `w`, where `ξ` gives the
coordinates of a tangent vector in `A`. Here `X` is a functor on `E`-algebras, and `u`, `c` map
`W` to `X` read on `k`-algebras (`restrictAlg E k ⋙ X`). -/
def HasJacobianRatio {X : CommAlg E ⥤ Type 1} (u c : W ⟶ restrictAlg E k ⋙ X) (d : ℕ) (t n : k)
    (w : W.obj (CommAlgCat.of k k)) : Prop :=
  ∀ A : EtaleChart d X,
    c.app (CommAlgCat.of k k) w ∈ A.locus.obj ((restrictAlg E k).obj (CommAlgCat.of k k)) →
    let ξ (γ : A.coordRing ⟶ (restrictAlg E k).obj (CommAlgCat.of k k[ε])) (i : Fin d) : k :=
      (γ (A.coordinate i)).snd
    ∃ N : Matrix (Fin d) (Fin d) k, N.det = n ∧
      ∀ (v : W.obj (CommAlgCat.of k k[ε]))
        (α γ : A.coordRing ⟶ (restrictAlg E k).obj (CommAlgCat.of k k[ε])),
        W.map SqZeroExt.fst v = w →
        X.map α A.point = u.app (CommAlgCat.of k k[ε]) v →
        X.map γ A.point = c.app (CommAlgCat.of k k[ε]) v →
        t • ξ α - ξ γ = N *ᵥ (ξ α - ξ γ)

/-- The tangent vector of a jet `v`, a point of `W` with values in `k ⊕ T*`, in the direction
`φ ∈ T`: the image of `v` under the map `k ⊕ T* → k[ε]` given by evaluation at `φ`. -/
abbrev jetTangent {T : FGModuleCat k} (v : W.obj (CommAlgCat.of k (TrivSqZeroExt k (Dual k T))))
    (φ : T) : W.obj (CommAlgCat.of k k[ε]) :=
  W.map (ofHom (TrivSqZeroExt.map (Dual.eval k T φ))) v

/-- Let `v` be a jet of `X` with values in `k ⊕ T*`, where `T` has dimension `d`, whose base point
lies in a chart `A` with `d` coordinates, and whose tangent vectors in distinct directions are
distinct. Then every tangent vector at the base point is one of these, and the coordinates of the
tangent vector in the direction `φ` are `D φ` for a linear isomorphism `D : T ≃ kᵈ`. Here `X` is
a functor on `E`-algebras, read on `k`-algebras through `restrictAlg E k`. -/
lemma EtaleChart.tangent_mem_range_of_jet {X : CommAlg E ⥤ Type 1} (A : EtaleChart d X)
    {T : FGModuleCat k} (hT : finrank k T = d)
    (v : (restrictAlg E k ⋙ X).obj (CommAlgCat.of k (TrivSqZeroExt k (Dual k T))))
    (hv : (restrictAlg E k ⋙ X).map SqZeroExt.fst v ∈
      A.locus.obj ((restrictAlg E k).obj (CommAlgCat.of k k)))
    (h_inj : Function.Injective (jetTangent v)) :
    (∀ w : (restrictAlg E k ⋙ X).obj (CommAlgCat.of k k[ε]),
      (restrictAlg E k ⋙ X).map SqZeroExt.fst w = (restrictAlg E k ⋙ X).map SqZeroExt.fst v →
        w ∈ range (jetTangent v)) ∧
    ∃ D : T ≃ₗ[k] (Fin d → k), ∀ (φ : T) (α :
      A.coordRing ⟶ (restrictAlg E k).obj (CommAlgCat.of k k[ε])),
      X.map α A.point = jetTangent v φ → (fun i : Fin d ↦ (α (A.coordinate i)).snd) = D φ := by
  -- By definition, `IsSquareZero` of the projection `k ⊕ M → k` is the statement of
  -- `fst_surjective_and_kerIdeal_sq_eq_bot`.
  have h_sq {M : Type} [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M] :
      IsSquareZero ((restrictAlg E k).map (fst (M := M))) :=
    fst_surjective_and_kerIdeal_sq_eq_bot (k := k) (M := M)
  -- The chart is open and contains the base point of `v`, so it contains `v`: `v` is given by a
  -- map `γ` from the ring of the chart.
  obtain ⟨⟨γ : A.coordRing ⟶ (restrictAlg E k).obj (.of k (TrivSqZeroExt k (Dual k T)))⟩,
    (rfl : X.map γ A.point = v)⟩ := A.isOpenSubfunctor.mem_of_isSquareZero _ h_sq v hv
  -- The coordinates being étale, a tangent vector is determined by its base point and its
  -- coordinates.
  have h_uniq {α β : A.coordRing ⟶ (restrictAlg E k).obj (.of k k[ε])}
      (h_base : α ≫ (restrictAlg E k).map fst = β ≫ (restrictAlg E k).map fst)
      (h_coord : (fun i : Fin d ↦ (α (A.coordinate i)).snd) =
        fun i : Fin d ↦ (β (A.coordinate i)).snd) :
      α = β := by
    exact A.lift_unique h_sq h_base fun i ↦
      TrivSqZeroExt.ext (ConcreteCategory.congr_hom h_base (A.coordinate i)) (congrFun h_coord i)
  -- The tangent vector of `v` in the direction `φ` is given by the map `g φ`; all of them have the
  -- base point of `v`.
  let g (φ : T) : A.coordRing ⟶ (restrictAlg E k).obj (.of k k[ε]) :=
    γ ≫ (restrictAlg E k).map (ofHom (map (Dual.eval k T φ)))
  have h_jet_eq (φ : T) :
      jetTangent (W := restrictAlg E k ⋙ X) (X.map γ A.point) φ = X.map (g φ) A.point :=
    (X.map_comp_apply γ _ _).symm
  have hg_base (φ : T) : g φ ≫ (restrictAlg E k).map fst = γ ≫ (restrictAlg E k).map fst := by
    have h_fst_map : ofHom (map (Dual.eval k T φ)) ≫ SqZeroExt.fst = SqZeroExt.fst := by
      ext r
      simp [SqZeroExt.fst]
    simp only [g, Category.assoc, ← Functor.map_comp, h_fst_map]
  -- The coordinates of the tangent vector in the direction `φ` are linear in `φ` and
  -- injective, hence bijective by dimension.
  let L : T →ₗ[k] Fin d → k := .pi fun i ↦ (γ (A.coordinate i)).snd
  have hL_coord (φ : T) : (fun i : Fin d ↦ (g φ (A.coordinate i)).snd) = L φ := by
    ext i
    show (TrivSqZeroExt.map (Dual.eval k T φ) (γ (A.coordinate i))).snd = (γ (A.coordinate i)).snd φ
    exact snd_map (Dual.eval k T φ) _
  have hL : Function.Injective L := by
    intro φ ψ h_eq
    have hg : g φ = g ψ := h_uniq ((hg_base φ).trans (hg_base ψ).symm)
      (by rw [hL_coord, hL_coord, h_eq])
    apply h_inj
    rw [h_jet_eq φ, h_jet_eq ψ, hg]
  let D : T ≃ₗ[k] (Fin d → k) :=
    L.linearEquivOfInjective hL (hT.trans (Module.finrank_fin_fun k).symm)
  refine ⟨fun w hw ↦ ?_, D, fun φ α hα ↦ ?_⟩
  · -- A tangent vector `w` at the base point is given by a map `α`; it is `g φ` for the `φ` with
    -- the coordinates of `α`.
    obtain ⟨⟨α : A.coordRing ⟶ (restrictAlg E k).obj (.of k k[ε])⟩, (rfl : X.map α A.point = w)⟩ :=
      A.isOpenSubfunctor.mem_of_isSquareZero _ h_sq w (mem_of_eq_of_mem hw hv)
    obtain ⟨φ, hφ⟩ := D.surjective fun i : Fin d ↦ (α (A.coordinate i)).snd
    have h_base_eq : α ≫ (restrictAlg E k).map fst = γ ≫ (restrictAlg E k).map fst := by
      apply A.injective
      show X.map (α ≫ (restrictAlg E k).map fst) A.point =
        X.map (γ ≫ (restrictAlg E k).map fst) A.point
      rw [X.map_comp_apply, X.map_comp_apply]
      exact hw
    obtain rfl : g φ = α := h_uniq ((hg_base φ).trans h_base_eq.symm) ((hL_coord φ).trans hφ)
    exact ⟨φ, h_jet_eq φ⟩
  · obtain rfl : α = g φ := A.injective _ (hα.trans (h_jet_eq φ))
    exact hL_coord φ

/-- Let `v` be a jet of `X` with values in `k ⊕ T*`, where `T` has dimension `d`, whose base point
lies in a chart `A` and whose tangent vectors in distinct directions are distinct. Then every
`k[ε]`-point `w` of `X` with the base point of `v` is a tangent vector `jetTangent v φ` of `v`. -/
lemma EtaleChart.mem_range_jetTangent_of_injective {X : CommAlg E ⥤ Type 1} (A : EtaleChart d X)
    {T : FGModuleCat k} (hT : finrank k T = d)
    (v : (restrictAlg E k ⋙ X).obj (CommAlgCat.of k (TrivSqZeroExt k (Dual k T))))
    (hv : (restrictAlg E k ⋙ X).map SqZeroExt.fst v ∈
      A.locus.obj ((restrictAlg E k).obj (CommAlgCat.of k k)))
    (h_inj : Function.Injective (jetTangent v))
    (w : (restrictAlg E k ⋙ X).obj (CommAlgCat.of k k[ε]))
    (hw : (restrictAlg E k ⋙ X).map SqZeroExt.fst w = (restrictAlg E k ⋙ X).map SqZeroExt.fst v) :
    w ∈ range (jetTangent v) := by
  exact (A.tangent_mem_range_of_jet hT v hv h_inj).left w hw

/-- Let `v` be a jet of `X` with values in `k ⊕ T*`, where `T` has dimension `d`, whose base point
lies in a chart `A` and whose tangent vectors in distinct directions are distinct. Then there is a
linear isomorphism `D : T ≃ kᵈ` such that every `α` representing `jetTangent v φ` in the chart has
`ε`-parts of its coordinates equal to `D φ`. -/
lemma EtaleChart.exists_linearEquiv_coordinate_jetTangent {X : CommAlg E ⥤ Type 1}
    (A : EtaleChart d X) {T : FGModuleCat k} (hT : finrank k T = d)
    (v : (restrictAlg E k ⋙ X).obj (CommAlgCat.of k (TrivSqZeroExt k (Dual k T))))
    (hv : (restrictAlg E k ⋙ X).map SqZeroExt.fst v ∈
      A.locus.obj ((restrictAlg E k).obj (CommAlgCat.of k k)))
    (h_inj : Function.Injective (jetTangent v)) :
    ∃ D : T ≃ₗ[k] (Fin d → k), ∀ (φ : T) (α :
      A.coordRing ⟶ (restrictAlg E k).obj (CommAlgCat.of k k[ε])),
      X.map α A.point = jetTangent v φ → (fun i : Fin d ↦ (α (A.coordinate i)).snd) = D φ := by
  exact (A.tangent_mem_range_of_jet hT v hv h_inj).right

/-- Let every field-valued point of `W` lie in a chart with `d` coordinates. Let `P` be a tangent
polynomial of `c`, `u` at `w`, that is `P t = P 0 * det (1 - t (dc)⁻¹ du)`, with `P 1 ≠ 0`. Then for
every `t : k`, `HasJacobianRatio u c d t (P t / P 1) w` holds: in every chart of `X` containing
`c w` there is a matrix `N` of determinant `P t / P 1` with `t du v - dc v = N (du v - dc v)` for
all tangent vectors `v` at `w`. -/
lemma IsTangentPoly.hasJacobianRatio_eval_div {X : CommAlg E ⥤ Type 1}
    {c u : W ⟶ restrictAlg E k ⋙ X} {w : W.obj (CommAlgCat.of k k)} {P : Polynomial k}
    (hP : IsTangentPoly d c u w P) (hW : IsChartCovered d W) (hP_one : P.eval 1 ≠ 0) (t : k) :
    HasJacobianRatio u c d t (P.eval t / P.eval 1) w := by
  -- The tangent vectors at `w` are the `jetTangent v φ`, `φ ∈ T`, with `dc` injective and
  -- `du = dc ∘ B`. As `P 1 ≠ 0`, `S = 1 - B` is invertible, and
  -- `t du - dc = (1 - t B) S⁻¹ (du - dc)` when `dc` identifies `T` with the coordinates of a chart.
  obtain ⟨T, v, B, hT, rfl, hc_inj, hu, hP_eval⟩ := hP
  have hB_det : (1 - B).det ≠ 0 := fun h_zero ↦
    hP_one (by rw [hP_eval 1, one_smul, h_zero, mul_zero])
  obtain ⟨S, rfl⟩ : ∃ S : T ≃ₗ[k] T, 1 - S.toLinearMap = B :=
    ⟨(1 - B).equivOfDetNeZero hB_det, by simp⟩
  have hu_sub (φ : T) : u.app _ (jetTangent v φ) = c.app _ (jetTangent v (φ - S φ)) := hu φ
  have h_tangent : ∀ x : W.obj (CommAlgCat.of k k[ε]), W.map fst x = W.map fst v →
      x ∈ range (jetTangent v) := by
    obtain ⟨A, hA⟩ := hW.exists_chart _ (Field.toIsField k) (W.map fst v)
    exact EtaleChart.mem_range_jetTangent_of_injective (E := k) A hT v hA hc_inj.of_comp
  -- In a chart `A` around `c w` the tangent vector `c (jetTangent v φ)` has coordinates `D φ`.
  intro A hw ξ
  have hc_nat (φ : T) : jetTangent (c.app _ v) φ = c.app _ (jetTangent v φ) :=
    (naturality_apply c _ v).symm
  have hv_chart : (restrictAlg E k ⋙ X).map fst (c.app _ v) ∈ A.locus.obj _ :=
    mem_of_eq_of_mem (naturality_apply c _ v).symm hw
  have hcv_inj : Function.Injective (jetTangent (c.app _ v)) := fun φ ψ h_eq ↦
    hc_inj (((hc_nat φ).symm.trans h_eq).trans (hc_nat ψ))
  obtain ⟨D, hD⟩ : ∃ D : T ≃ₗ[k] (Fin d → k), ∀ (φ : T)
      (α : A.coordRing ⟶ (restrictAlg E k).obj (CommAlgCat.of k k[ε])),
      X.map α A.point = jetTangent (c.app _ v) φ → ξ α = D φ :=
    A.exists_linearEquiv_coordinate_jetTangent hT (c.app _ v) hv_chart hcv_inj
  let N : Module.End k T := (1 - t • (1 - S.toLinearMap)) ∘ₗ S.symm.toLinearMap
  refine ⟨(D.toLinearMap ∘ₗ N ∘ₗ D.symm.toLinearMap).toMatrix', ?_, fun x α γ hx hα hγ ↦ ?_⟩
  · -- The determinant is `det (1 - t B) / det S = P t / P 1`.
    have hP_one_eq : P.eval 1 = P.eval 0 * S.toLinearMap.det := by
      rw [hP_eval 1, one_smul, sub_sub_cancel]
    have hP_zero : P.eval 0 ≠ 0 := left_ne_zero_of_mul (hP_one_eq.symm.trans_ne hP_one)
    have hN_det : N.det = (1 - t • (1 - S.toLinearMap)).det / S.toLinearMap.det := by
      rw [LinearMap.det_comp, S.det_coe_symm, div_eq_mul_inv]
    rw [LinearMap.det_toMatrix', LinearMap.det_conj, hN_det, hP_eval t, hP_one_eq,
      mul_div_mul_left _ _ hP_zero]
  · -- For `x = jetTangent v φ` the coordinates of `u x` and `c x` are `D (φ - S φ)` and `D φ`.
    obtain ⟨φ, rfl⟩ := h_tangent x hx
    have hγ_coord : ξ γ = D φ := hD φ γ (hγ.trans (hc_nat φ).symm)
    have hα_coord : ξ α = D (φ - S φ) := hD _ α (hα.trans ((hu_sub φ).trans (hc_nat _).symm))
    have h_N : N (-S φ) = t • (φ - S φ) - φ := by
      simp only [N, LinearMap.comp_apply, LinearEquiv.coe_coe, map_neg,
        LinearEquiv.symm_apply_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply]
      module
    calc
      t • ξ α - ξ γ = D (t • (φ - S φ) - φ) := by
        rw [hα_coord, hγ_coord, map_sub D (t • (φ - S φ)) φ, map_smul]
      _ = D (N (-S φ)) := by rw [h_N]
      _ = (D.toLinearMap ∘ₗ N ∘ₗ D.symm.toLinearMap).toMatrix' *ᵥ (ξ α - ξ γ) := by
        rw [LinearMap.toMatrix'_mulVec, hα_coord, hγ_coord, ← map_sub, sub_sub_cancel_left]
        simp

/-- Let every field-valued point of `W` lie in a chart with `d` étale coordinates. Let `P` be a
tangent polynomial of `c`, `u` at the `k`-point `w`, that is, the algebraic form of
`P t = P 0 * det (1 - t (dc)⁻¹ du)` on the tangent space at `w`, and suppose `P 1 ≠ 0`. Then every
`k[ε]`-valued point `x` of `W` above `w` that is a coincidence of `u` and `c` is constant. -/
lemma IsTangentPoly.constIfCoincident {c u : W ⟶ X} {w : W.obj (CommAlgCat.of k k)}
    {P : Polynomial k} (hP : IsTangentPoly d c u w P) (hW : IsChartCovered d W)
    (hP_one : P.eval 1 ≠ 0) {x : W.obj (CommAlgCat.of k k[ε])} (hx : W.map SqZeroExt.fst x = w) :
    ConstIfCoincident u c x := by
  -- The tangent vectors at `w` are the `jetTangent v φ`, `φ ∈ T`, with `dc` injective and
  -- `du = dc ∘ B`. As `P 1 ≠ 0`, the map `1 - B` is injective.
  obtain ⟨T, v, B, hT, rfl, hc_inj, hu, hP_eval⟩ := hP
  have hB_det : (1 - B).det ≠ 0 := fun h_zero ↦
    hP_one (by rw [hP_eval 1, one_smul, h_zero, mul_zero])
  have hB_inj : Function.Injective (1 - B : Module.End k T) :=
    ((1 - B).equivOfDetNeZero hB_det).injective
  obtain ⟨A, hA⟩ := hW.exists_chart _ (Field.toIsField k) (W.map fst v)
  obtain ⟨φ, rfl⟩ := EtaleChart.mem_range_jetTangent_of_injective (E := k) A hT v hA hc_inj.of_comp
    x hx
  -- A coincidence `jetTangent v φ` has `φ = B φ` by injectivity of `dc`, so `φ = 0`.
  intro (h_coin : c.app _ (jetTangent v φ) = u.app _ (jetTangent v φ))
  have h_fixed : φ = B φ := hc_inj (h_coin.trans (hu φ))
  have h_ker : (1 - B) φ = (1 - B) 0 := by simpa [sub_eq_zero] using h_fixed
  obtain rfl : φ = 0 := hB_inj h_ker
  -- `jetTangent v 0` is constant: both sides are images of `v` under the same map
  -- `k ⊕ T* → k → k[ε]`.
  have h_map : ofHom (TrivSqZeroExt.map (Dual.eval k T 0)) =
      ofHom (TrivSqZeroExt.map (Dual.eval k T 0)) ≫ SqZeroExt.fst ≫ structureMap := by
    ext r <;> simp
  show W.map (ofHom (TrivSqZeroExt.map (Dual.eval k T 0))) v =
    W.map (SqZeroExt.fst ≫ structureMap) (W.map (ofHom (TrivSqZeroExt.map (Dual.eval k T 0))) v)
  rw [← W.map_comp_apply, ← h_map]

end IsolatedCoincidences

/-!
## Local terms of the diagonal class at simple coincidences

The pull-back of the diagonal class along the twisted graph `scaledGraph t u c` is a sum of point
classes over the coincidences of `u` and `c`. Near one coincidence the computation is the
transformation law `New.Variety.symbolClass_transformation` for Grothendieck symbols.
-/

section FixedPointFormula

open CategoryTheory MonoidalCategory CartesianMonoidalCategory RingHom Ideal TrivSqZeroExt
  CommAlgCat Abelian.Ext H HodgeTest Field

variable {k : Type} [Field k] [CharZero k] {d : ℕ} {W X : CommAlg k ⥤ Type 1}

/-- The graph of the pair `(u, c)` twisted by `t` in the first factor. For a scalar `t` of `k`
and maps `u c : W ⟶ X`, it is the natural map `W(A ⊕ M) → X(A ⊕ M) × X(A ⊕ M)` on square-zero
extensions, `w ↦ (u (s_t w), c w)`, where `s_t : A ⊕ M → A ⊕ M` is `(a, m) ↦ (a, t m)`. -/
def scaledGraph (t : k) (u c : W ⟶ X) : sqZeroExt ⋙ W ⟶ sqZeroExt ⋙ X ⊗ sqZeroExt ⋙ X :=
  CartesianMonoidalCategory.lift (scaleModule t (HodgeTest.sqZeroExt ⋙ W) ≫ sqZeroExt.whiskerLeft u)
    (sqZeroExt.whiskerLeft c)

/-- For a `k`-point `z` of `X`, the constant map `W ⟶ X` that sends every `A`-point of `W` to
the image of `z` in `X(A)`. -/
def constMap (z : X (of k k)) : W ⟶ X where
  app A := ↾fun _ ↦ X.map structureMap z

omit [CharZero k] in
/-- The universal symbol `symbolClass` in degree `d` is compatible with a change of the base
field: for a field `E` of characteristic `0` over `k`, the base change to `E` of the symbol over
`k` is the symbol over `E`. -/
lemma symbolClass_baseChange {E : Type} [Field E] [CharZero E] [Algebra k E] :
    (symbolClass (k := k) (d := d)).baseChange (k := E) = symbolClass := by
  -- Both classes are given by the same determinant cocycle on the same relation; the three
  -- compatibilities hold by unfolding the identity maps.
  refine witnessed.pull_cocycleClass exists_jouanolouRel_of_unimodular
    exists_jouanolouRel_of_unimodular _ (𝟙 _) { app _ := ↾Prod.snd } ?_ ?_ ?_
  · -- the relation over `E` maps into the relation over `k`
    tauto
  · -- the two determinant cocycles agree
    tauto
  · -- the map of relative chains is the identity
    tauto

omit [CharZero k] in
/-- Let `U` be an open subfunctor of `X × X` and `x` a point of `W` with values in a square-zero
extension `A ⊕ M`. If `(u x, c x)` lies in `U`, then so does `scaledGraph t u c x`: the two pairs
agree modulo `M`, and membership in an open subfunctor is decided modulo a square-zero ideal. -/
lemma preimage_lift_le_preimage_scaledGraph (t : k) (u c : W ⟶ X) {U : Subfunctor (X ⊗ X)}
    (hU : IsOpenSubfunctor U) :
    (U.preimage (CartesianMonoidalCategory.lift u c)).whisker HodgeTest.sqZeroExt ≤
      (U.whisker HodgeTest.sqZeroExt).preimage (scaledGraph t u c) := by
  intro C x hx
  -- Modulo `M` the pairs `scaledGraph t u c x` and `(u x, c x)` agree, and the latter lies in `U`.
  have base_eq : (X ⊗ X).map C.baseProj ((scaledGraph t u c).app C x) =
      (X ⊗ X).map C.baseProj ((CartesianMonoidalCategory.lift u c).app (sqZeroExt.obj C) x) := by
    refine Prod.ext ?_ rfl
    show X.map C.baseProj (u.app _ (W.map ((scaleModule t sqZeroExt).app C) x)) = _
    rw [u.naturality_apply]
    exact (X.map_comp_apply ((scaleModule t sqZeroExt).app C) C.baseProj _).symm
  refine hU.mem_of_isSquareZero C.baseProj fst_surjective_and_kerIdeal_sq_eq_bot _ ?_
  exact (congrArg (fun p ↦ p ∈ U.obj C.baseAlg) base_eq).mpr (U.map C.baseProj hx)

omit [CharZero k] in
/-- Let `s` be the set of coincidences of `u` and `c` (`IsCoincidenceSet`), `a` a chart of `W`
with ring `a.coordRing`, and `ζ : a.coordRing ⟶ k` a `k`-point of `a` that lies in `s` and is the
only point of `s` in `a`. Let `I` be an ideal of `a.coordRing` that cuts out the coincidences in
`a`: a map `α` from `a.coordRing` kills `I` exactly when the point `α` of `W` is a coincidence. Then
`I` contains the ideal `ker ζ` of the point `ζ`. -/
lemma ker_le_of_cuts_out_coincidences {u c : W ⟶ X} {s : Finset (W.obj (of k k))}
    (hs : IsCoincidenceSet u c s) (a : EtaleChart d W) (ζ : a.coordRing ⟶ of k k)
    (hw : W.map ζ a.point ∈ s)
    (ha_off : a.point ∈ (offPoints (s \ {W.map ζ a.point} : Set (W.obj (of k k)))).obj a.coordRing)
    {I : Ideal a.coordRing}
    (h_cut : ∀ {C : CommAlg k} (α : a.coordRing ⟶ C),
      I ≤ ker α.hom ↔ c.app C (W.map α a.point) = u.app C (W.map α a.point)) :
    ker ζ.hom ≤ I := by
  obtain ⟨h_red, h_coin, h_field⟩ := hs
  -- Nakayama: a tangent vector that kills `I` is a coincidence, hence constant, so `I` generates
  -- `ker ζ` near `ζ`.
  have h_tangent : ∀ p : a.coordRing →ₐ[k] DualNumber k, (∀ r : a.coordRing, (p r).fst = ζ r) →
      I ≤ ker p → ∀ r : a.coordRing, (p r).snd = 0 := by
    rintro p - hp r
    have h_const : ofHom p = ofHom p ≫ SqZeroExt.fst ≫ structureMap :=
      a.eq_comp_of_map_point_eq _ (h_red _ ((h_cut (ofHom p)).mp hp))
    have h_const_r : p r = algebraMap k (DualNumber k) (p r).fst :=
      ConcreteCategory.congr_hom h_const r
    rw [h_const_r, algebraMap_eq_inl', snd_inl]
  obtain ⟨b, hb_colon, hb_ne⟩ : ∃ b ∈ I.colon (ker ζ.hom), ζ b ≠ 0 :=
    exists_mem_colon_of_tangent (k := k) rfl ((h_cut ζ).mpr (h_coin _ hw)) h_tangent
  -- A field point `κ` that kills the colon ideal is a coincidence in the chart `a`, so it comes
  -- from `ζ`, against `ζ b ≠ 0`. Hence the colon ideal is `⊤`.
  have colon_top : (I.colon (ker ζ.hom)).map (𝟙 a.coordRing :).hom = ⊤ := by
    refine (map_eq_top_iff_forall_isField _ (𝟙 _)).mpr fun K κ hK h_le ↦ ?_
    obtain ⟨z, hz, hκz⟩ : ∃ z ∈ s, W.map (𝟙 a.coordRing ≫ κ) a.point = W.map structureMap z :=
      h_field K hK _ ((h_cut _).mp (le_colon.trans h_le))
    refine ha_off K κ hK ⟨z, ⟨hz, fun hzw ↦ hb_ne ?_⟩, hκz⟩
    have hκ : 𝟙 a.coordRing ≫ κ = ζ ≫ structureMap :=
      a.eq_comp_of_map_point_eq _ (by rw [hκz, Set.mem_singleton_iff.mp hzw])
    simpa [hκ, hK.nontrivial] using h_le hb_colon
  exact (Submodule.colon_eq_top_iff_subset _).mp (by simpa using colon_top)

omit [CharZero k] in
/-- Carrying a chart expression along a map of algebras. Let `A` be a chart of `X` and `v` a map
from `W` to `X`. If `χ` expresses the point `v y` in the coordinates of `A`, then `χ` followed by
`α : B ⟶ C` expresses the point `v (α y)`. -/
private lemma map_comp_map_point_eq_app_map_of_map_point_eq {E : Type} [Field E] [Algebra k E]
    {W : CommAlg E ⥤ Type 1} {A : EtaleChart d X} {v : W ⟶ restrictAlg k E ⋙ X} {B C : CommAlg E}
    {χ : A.coordRing ⟶ (restrictAlg k E).obj B} {y : W.obj B}
    (h_map : X.map χ A.point = v.app B y) (α : B ⟶ C) :
    X.map (χ ≫ (restrictAlg k E).map α) A.point = v.app C (W.map α y) := by
  rw [v.naturality_apply, ← h_map]
  exact X.map_comp_apply ..

omit [CharZero k] in
/-- Off the coincidences, the twisted graph avoids the diagonal. Let every field-valued coincidence
of `u` and `c` come from a point of the finite set `s`. Then `scaledGraph t u c` maps the
square-zero points of the complement `offPoints s` of `s` into the complement `offDiagonal X` of
the diagonal. -/
private lemma offPoints_whisker_le_preimage_scaledGraph [IsSeparatedFunctor X] {E : Type} [Field E]
    [CharZero E] [Algebra k E] {W : CommAlg E ⥤ Type 1} (u c : W ⟶ restrictAlg k E ⋙ X)
    (s : Finset (W.obj (of E E))) (t : E)
    (h_field : ∀ K : CommAlg E, IsField K → ∀ x : W.obj K, c.app K x = u.app K x →
      ∃ w ∈ s, x = W.map structureMap w) :
    (offPoints (s : Set (W.obj (of E E)))).whisker sqZeroExt ≤
      (((offDiagonal X).whisker (restrictAlg k E)).whisker sqZeroExt).preimage
        (scaledGraph t u c) := by
  have off_open : IsOpenSubfunctor ((offDiagonal X).whisker (restrictAlg k E)) :=
    (isOpenSubfunctor_offDiagonal (X := X)).whisker_restrictAlg
  intro C x hx
  -- It is enough that `(u x, c x)` avoids the diagonal, and this is checked at field-valued
  -- points, where a point of the diagonal is a coincidence and so comes from `s`.
  refine preimage_lift_le_preimage_scaledGraph t u c off_open C ?_
  refine (off_open.preimage _).fieldLocus_le _ fun K α hK ↦ ?_
  exact mem_offDiagonal_of_ne (X := X) hK fun h_eq ↦ hx K α hK (h_field K hK _ h_eq.symm)

omit [CharZero k] in
/-- The tangent step of the transformation law. `φ`, `ψ` write `u`, `c` on the chart `a` in the
coordinates `xᵢ` of `A`, `f` is their difference, `ν` a section of
`a.coordRing ⊕ a.coordRing ^ d → a.coordRing`, and `t du - dc = Q (du - dc)` at
`w = W.map ζ a.point` (as in `HasJacobianRatio`). Then `ζ` kills
`t (ν (φ xᵢ))ⱼ - (ν (ψ xᵢ))ⱼ - ∑ l, Q i l (ν (f l))ⱼ` for all `i`, `j`. -/
private lemma apply_tangent_sub_sum_eq_zero {E : Type} [Field E] [Algebra k E]
    {W : CommAlg E ⥤ Type 1} {u c : W ⟶ restrictAlg k E ⋙ X} {t : E} {A : EtaleChart d X}
    {a : EtaleChart d W} {ζ : a.coordRing ⟶ of E E}
    {φ ψ : A.coordRing ⟶ (restrictAlg k E).obj a.coordRing}
    (hφ : X.map φ A.point = u.app a.coordRing a.point)
    (hψ : X.map ψ A.point = c.app a.coordRing a.point) {f : Fin d → a.coordRing}
    (hf : f = (φ ∘ A.coordinate : Fin d → a.coordRing) - (ψ ∘ A.coordinate : Fin d → a.coordRing))
    (ν : a.coordRing ⟶ sqZeroExt.obj (⟨a.coordRing, Fin d⟩ : HodgeTest E))
    (ν_fst : Function.LeftInverse TrivSqZeroExt.fst ν) {Q : Matrix (Fin d) (Fin d) E}
    (hQ_tan : ∀ (v : W.obj (of E (DualNumber E)))
      (α γ : A.coordRing ⟶ (restrictAlg k E).obj (of E (DualNumber E))),
      W.map SqZeroExt.fst v = W.map ζ a.point → X.map α A.point = u.app (of E (DualNumber E)) v →
        X.map γ A.point = c.app (of E (DualNumber E)) v →
          t • (fun i : Fin d ↦ (α (A.coordinate i)).snd) -
              (fun i : Fin d ↦ (γ (A.coordinate i)).snd) =
            Q.mulVec ((fun i : Fin d ↦ (α (A.coordinate i)).snd) -
              (fun i : Fin d ↦ (γ (A.coordinate i)).snd)))
    (i j : Fin d) :
    ζ (t • (ν (φ (A.coordinate i))).snd j - (ν (ψ (A.coordinate i))).snd j -
      ∑ l : Fin d, Q.map (algebraMap E a.coordRing) i l * (ν (f l)).snd j) = 0 := by
  -- Apply `hQ_tan` to the `j`-th coordinate tangent vector `ν ≫ μ` at `w`.
  let P : HodgeTest E := ⟨a.coordRing, Fin d⟩
  let μ := (withIndex _ ⋙ sqZeroExt).map ζ ≫ ofHom (TrivSqZeroExt.map (.proj j))
  have μ_snd (x : sqZeroExt.obj P) : (μ x).2 = ζ (x.snd j) := zero_add _
  have h_base : W.map SqZeroExt.fst (W.map (ν ≫ μ) a.point) = W.map ζ a.point := by
    refine (W.map_comp_apply (_ ≫ μ) ..).symm.trans ?_
    congr with x
    exact (add_zero _).trans (congrArg ζ (ν_fst x))
  have h_tan := congrFun (hQ_tan _ _ _ h_base
    (map_comp_map_point_eq_app_map_of_map_point_eq hφ _)
    (map_comp_map_point_eq_app_map_of_map_point_eq hψ _)) i
  -- `using!` lets `simpa` unfold `P`, `μ` and the components of `TrivSqZeroExt.map`.
  simpa [sub_eq_zero, ← μ_snd, hf, P] using! h_tan

/-- The multiplicity at one coincidence. On `O`, the class `δ` (relative to the complement of the
diagonal) is the symbol of the coordinate differences of the chart `A`; `lift u c` maps the chart
`a` of `W`, with a point `ζ`, into `O`; `φ`, `ψ` write `u`, `c` on `a`; their difference `f` cuts
out `w = W.map ζ a.point` and generates `ker ζ`; `m` is the Jacobian ratio at `w`. Then on `a`,
relative to the complement of `w`, `δ.baseChange` (`δ` read on `E`-algebras through
`restrictAlg k E`) pulls back along `scaledGraph t u c` to `m • [df / f]`. -/
private lemma map_pointMap_map_scaledGraph_eq_smul_symbolClass [IsSeparatedFunctor X] {E : Type}
    [Field E] [CharZero E] [Algebra k E] {W : CommAlg E ⥤ Type 1} {u c : W ⟶ restrictAlg k E ⋙ X}
    {s : Finset (W.obj (of E E))} {t m : E} {δ : HodgeH (relFreeAb (offDiagonal X)) d}
    {A : EtaleChart d X} {O : Subfunctor (X ⊗ X)} (hO : IsOpenSubfunctor O)
    (h_near : IsDiagonalSymbolOn δ A O)
    (off_le : (offPoints (s : Set (W.obj (of E E)))).whisker sqZeroExt ≤
      (((offDiagonal X).whisker (restrictAlg k E)).whisker sqZeroExt).preimage (scaledGraph t u c))
    {a : EtaleChart d W} {ζ : a.coordRing ⟶ of E E}
    (ha_O : a.point ∈
      ((O.whisker (restrictAlg k E)).preimage (CartesianMonoidalCategory.lift u c)).obj a.coordRing)
    {φ ψ : A.coordRing ⟶ (restrictAlg k E).obj a.coordRing}
    (hφ : X.map φ A.point = u.app a.coordRing a.point)
    (hψ : X.map ψ A.point = c.app a.coordRing a.point) {f : Fin d → a.coordRing}
    (hf : f = (φ ∘ A.coordinate : Fin d → a.coordRing) - (ψ ∘ A.coordinate : Fin d → a.coordRing))
    (ker_le : ker ζ.hom ≤ span (.range f))
    (f_cut : CutsOutLocus W (ComesFromPoints {W.map ζ a.point}) a.point f)
    (V_le : (offPoints {W.map ζ a.point}).preimage (pointMap a.point) ≤
      (offPoints (s : Set (W.obj (of E E)))).preimage (pointMap a.point))
    (hJ : HasJacobianRatio u c d t m (W.map ζ a.point))
    (hc_mem_O : (c.app (of E E) (W.map ζ a.point), c.app (of E E) (W.map ζ a.point)) ∈
      O.obj ((restrictAlg k E).obj (of E E))) :
    HodgeH.map (relFreeAb.map (pointMap a.point) V_le)
        (H.map hodgeCoeff ((relFreeAb.map (scaledGraph t u c) off_le :) :
          sqZeroExt ⋙ relFreeAb (offPoints (s : Set (W.obj (of E E)))) ⟶
            sqZeroExt ⋙ restrictAlg k E ⋙ relFreeAb (offDiagonal X)) d δ.baseChange) =
      m • HodgeH.map (relFreeAb.map (U := unimodular) (pointMap (A := a.coordRing) ⟨f⟩)
        f_cut.preimage_fieldLocus_not.le) symbolClass := by
  let r : CommAlg E ⥤ CommAlg k := restrictAlg k E
  let q : sqZeroExt ⋙ relFreeAb (offPoints (s : Set (W.obj (of E E)))) ⟶
      sqZeroExt ⋙ r ⋙ relFreeAb (offDiagonal X) := (relFreeAb.map (scaledGraph t u c) off_le :)
  let V := (offPoints {W.map ζ a.point}).preimage (pointMap a.point)
  obtain ⟨Q, hQ_det, hQ_tan⟩ := hJ A (h_near.fst_mem_locus hc_mem_O)
  -- The two classes on the chart are compared at its universal point
  -- `ν : a.coordRing → a.coordRing ⊕ a.coordRing ^ d`: pull-back along `e` is injective on
  -- cohomology.
  obtain ⟨ν, ν_fst, hν⟩ := a.exists_section_isCohomEquiv
  obtain ⟨h_unit, h_eqv⟩ := hν f_cut.preimage_fieldLocus_not
  refine (h_eqv d).injective ?_
  let P : HodgeTest E := ⟨a.coordRing, Fin d⟩
  let e : relFreeAb (someUnitLocus (c := P) f) ⟶ sqZeroExt ⋙ relFreeAb V :=
    (relFreeAb.map (𝟙 _) h_unit ≫
      relFreeAb.map (U := V.whisker sqZeroExt) (pointMap ⟨ν⟩) le_rfl :)
  let ρ := relFreeAb.map (U := offPoints s) (pointMap a.point) V_le
  let τ := relFreeAb.map (U := unimodular) (pointMap (A := a.coordRing) ⟨f⟩)
    f_cut.preimage_fieldLocus_not.le
  -- At the image `y` of the universal point, `δ` is the symbol of `F`, which lifts `f`.
  let S : CommAlg k := r.obj (sqZeroExt.obj P)
  let y : (X ⊗ X).obj S := (scaledGraph t u c).app P (W.map ν a.point)
  let φ' : A.coordRing ⟶ S := (φ ≫ r.map ν) ≫ r.map ((scaleModule t sqZeroExt).app P)
  let ψ' : A.coordRing ⟶ S := ψ ≫ r.map ν
  let F : Fin d → S := fun i ↦ φ' (A.coordinate i) - ψ' (A.coordinate i)
  have hy_O : y ∈ O.obj S :=
    preimage_lift_le_preimage_scaledGraph t u c hO.whisker_restrictAlg _ (Subfunctor.map _ ν ha_O)
  obtain ⟨F_cut, h_refl, δ_eq⟩ : IsLocalSymbol δ y (fun _ x ↦ x.1 = x.2) F 1 :=
    h_near.isLocalSymbol hy_O
      (map_comp_map_point_eq_app_map_of_map_point_eq
        (map_comp_map_point_eq_app_map_of_map_point_eq hφ _) _)
      (map_comp_map_point_eq_app_map_of_map_point_eq hψ _)
  have F_fst (i : Fin d) : TrivSqZeroExt.fst (F i) = f i := by
    rw [hf]
    exact congrArg₂ Sub.sub (ν_fst (φ (A.coordinate i))) (ν_fst (ψ (A.coordinate i)))
  let V' := (offDiagonal X).preimage (pointMap y)
  have unit_le : someUnitLocus (c := P) f ≤
      ((V'.whisker r).whisker sqZeroExt).preimage (pointMap (A := P) ⟨𝟙 S⟩) := by
    intro C σ ⟨i, hi⟩
    rw [← F_fst i] at hi
    exact F_cut.preimage_fieldLocus_not.ge _
      (projSpace.span_eq_top_of_isUnit i (isUnit_iff_isUnit_fst.2 hi))
  let β : relFreeAb (someUnitLocus (c := P) f) ⟶ sqZeroExt ⋙ r ⋙ relFreeAb V' :=
    (relFreeAb.map _ unit_le :)
  let γ := relFreeAb.map (U := offDiagonal X) (pointMap y) h_refl
  let γ' := relFreeAb.map (U := unimodular) (pointMap (A := S) ⟨F⟩)
    F_cut.preimage_fieldLocus_not.le
  have h_square : (e ≫ sqZeroExt.whiskerLeft ρ) ≫ q =
      β ≫ sqZeroExt.whiskerLeft (r.whiskerLeft γ) := by
    refine relFreeAb.hom_ext fun C σ ↦ congrArg (relFreeAb.mk _) ?_
    exact (congrArg _ (W.map_comp_apply ν (sqZeroExt.map σ.down) a.point)).trans
      ((scaledGraph t u c).naturality_apply σ.down (W.map ν a.point))
  have δ_bc : HodgeH.map (r.whiskerLeft γ) δ.baseChange =
      HodgeH.map (r.whiskerLeft γ') symbolClass :=
    calc _ = HodgeH.baseChange (k := E) (δ.map γ) := (HodgeH.baseChange_map ..).symm
      _ = HodgeH.baseChange (symbolClass.map γ') := congrArg _ (δ_eq.trans (one_smul ..))
      _ = _ := (HodgeH.baseChange_map ..).trans (congrArg _ symbolClass_baseChange)
  -- The transformation law: `F = (f, t du - dc)`, `ν ∘ f = (f, du - dc)`, and modulo `f` the
  -- second components are related by `Q`, whose determinant is `m`.
  have h_symbol : H.map _ (β ≫ sqZeroExt.whiskerLeft (r.whiskerLeft γ')) d symbolClass =
      m • H.map _ (e ≫ sqZeroExt.whiskerLeft τ) d symbolClass := by
    refine symbolClass_transformation (f := F) (g := fun l ↦ ν (f l)) (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl) (funext F_fst) 1 (Q.map (algebraMap ..)) _ ?_ (fun i j ↦ ker_le ?_) ?_
    · rw [Matrix.one_mulVec]
      exact funext fun l ↦ (ν_fst (f l)).symm
    · change ζ (t • (ν _).snd j - (ν _).snd j - _) = 0
      exact apply_tangent_sub_sum_eq_zero hφ hψ hf ν ν_fst hQ_tan i j
    · simp [← hQ_det, map_det]
  calc H.map _ e d (HodgeH.map ρ (H.map _ q d δ.baseChange))
    _ = H.map _ ((e ≫ sqZeroExt.whiskerLeft ρ) ≫ q) d δ.baseChange :=
      (map_comp ..).symm.trans (map_comp ..).symm
    _ = H.map _ (β ≫ sqZeroExt.whiskerLeft (r.whiskerLeft γ)) d δ.baseChange := by rw [h_square]
    _ = H.map _ (β ≫ sqZeroExt.whiskerLeft (r.whiskerLeft γ')) d symbolClass :=
      (map_comp ..).trans ((congrArg _ δ_bc).trans (map_comp ..).symm)
    _ = m • H.map _ (e ≫ sqZeroExt.whiskerLeft τ) d symbolClass := h_symbol
    _ = H.map _ e d (m • HodgeH.map τ symbolClass) :=
      (congrArg _ (map_comp ..)).trans (map_push ..).symm

/-- The local terms of the diagonal class. If `X` has an atlas of dimension `d`, some `δ` in
`Hdg^d(X × X)` works for every field `E` of characteristic `0` over `k`, every separated `W` over
`E` with field points in charts of dimension `d`, every `t : E` and all `u c : W ⟶ X` with reduced
coincidences `s` and `n w = det((t du − dc)(du − dc)⁻¹)` at `w ∈ s`. (a) Some class relative to
`offPoints s` (points avoiding `s`) is `n w • [dg/g]` near each `w`, where the functions `g` cut out
`w`. (b) `δ.baseChange`, the class `δ` over `k` read on `E`-algebras through `restrictAlg k E`,
pulls back to `∑ n w • pointClass d w` along `scaledGraph t u c`, the map `w ↦ (u (s_t w), c w)` on
square-zero extensions, where `s_t(a, m) = (a, t m)`. -/
lemma exists_diagonal_local_terms (hX : HasAtlas d X) :
    ∃ δ : HodgeH (freeAb.obj (X ⊗ X)) d,
      ∀ {E : Type} [Field E] [CharZero E] [Algebra k E] {W : CommAlg E ⥤ Type 1}
        [IsSeparatedFunctor W] [IsChartCovered d W] (u c : W ⟶ restrictAlg k E ⋙ X)
        (s : Finset (W.obj (of E E))) (t : E) (n : W.obj (of E E) → E),
        IsCoincidenceSet u c s → (∀ w ∈ s, HasJacobianRatio u c d t (n w) w) →
          -- (a)
          (∃ ξ : HodgeH (relFreeAb (offPoints s)) d, IsPointSum s n ξ) ∧
          -- (b)
          H.map hodgeCoeff (freeAb.map (scaledGraph t u c)) d δ.baseChange =
            ∑ w ∈ s, n w • pointClass d w := by
  -- Take the class `δ` of the diagonal with supports (`exists_diagonal_class`) and forget the
  -- supports. Its pull-back along `scaledGraph t u c` has supports in `s`, so it is enough to find
  -- its multiplicity at each `w ∈ s` (`IsPointSum.map_eq_sum_pointClass`). Near `w` the differences
  -- `f` of the coordinates of `u` and `c` cut out `w`, and the transformation law
  -- `symbolClass_transformation` gives the multiplicity `n w`.
  obtain ⟨δ, hδ⟩ := exists_diagonal_class hX
  refine ⟨.map (relFreeAb.π _) δ, ?_⟩
  intro E hE_field hE_char hE_alg W hW_sep hW_cov u c s t n hs hJ
  obtain ⟨h_red, h_coin, h_field⟩ := hs
  let r : CommAlg E ⥤ CommAlg k := restrictAlg k E
  -- Off `s` there is no coincidence, so `scaledGraph t u c` maps into the complement of the
  -- diagonal.
  have off_le : (offPoints s).whisker sqZeroExt ≤
      (((offDiagonal X).whisker r).whisker sqZeroExt).preimage (scaledGraph t u c) :=
    offPoints_whisker_le_preimage_scaledGraph u c s t h_field
  let q : sqZeroExt ⋙ relFreeAb (offPoints (X := W) s) ⟶
      sqZeroExt ⋙ r ⋙ relFreeAb (offDiagonal X) := (relFreeAb.map (scaledGraph t u c) off_le :)
  suffices h_loc : IsPointSum s n (U := offPoints s) (H.map _ q d δ.baseChange) by
    refine ⟨⟨_, h_loc⟩, ?_⟩
    rw [← h_loc.map_eq_sum_pointClass rfl]
    -- Forgetting supports commutes with base change and with the pull-back.
    have forget_bc : (HodgeH.map (relFreeAb.π (offDiagonal X)) δ).baseChange (k := E) =
        HodgeH.map (r.whiskerLeft (relFreeAb.π (offDiagonal X))) δ.baseChange :=
      HodgeH.baseChange_map ..
    have forget_pull : H.map _ (freeAb.map (scaledGraph t u c)) d
        (HodgeH.map (r.whiskerLeft (relFreeAb.π (offDiagonal X))) δ.baseChange) =
        H.map _ (sqZeroExt.whiskerLeft (relFreeAb.π (offPoints (X := W) s)) ≫ q) d
          δ.baseChange :=
      (map_comp ..).symm
    exact (congrArg _ forget_bc).trans (forget_pull.trans (map_comp ..))
  intro w hw
  -- A chart `A` of `X` and an open `O ∋ (c w, c w)`: by `h_near` every point of `O` comes from `A`,
  -- the differences of its coordinates cut out the diagonal, and `δ` is their symbol.
  obtain ⟨A, O, hO, hc_mem_O, h_near⟩ := hδ _ (c.app _ w) (toIsField E)
  -- A chart `a` of `W` at `w = ζ a.point` that `lift u c` maps into `O` and that avoids `s \ {w}`.
  have h_open : IsOpenSubfunctor ((O.whisker r).preimage (lift u c :) ⊓ offPoints
    (s \ {w} : Set _)) :=
    (hO.whisker_restrictAlg.preimage (lift u c :)).inf isOpenSubfunctor_offPoints
  have hw_O : (u.app (of E E) w, c.app (of E E) w) ∈ O.obj (r.obj (of E E)) := by
    rwa [← h_coin w hw]
  have hw_off : w ∈ (offPoints (X := W) (s \ {w} : Set _)).obj (of E E) := by
    simp [mem_offPoints_iff, toIsField, ComesFromPoints]
  obtain ⟨a, ⟨⟨ζ : a.coordRing ⟶ of E E⟩, rfl⟩, ha_O, ha_off⟩ :=
    h_open.exists_mem_locus_and_point_mem (toIsField E) ⟨hw_O, hw_off⟩
  -- `φ`, `ψ` express `u`, `c` in the charts; the differences `f` cut out the coincidences.
  obtain ⟨⟨φ : A.coordRing ⟶ r.obj a.coordRing⟩, hφ⟩ := h_near.fst_mem_locus ha_O
  obtain ⟨⟨ψ : A.coordRing ⟶ r.obj a.coordRing⟩, hψ⟩ := h_near.snd_mem_locus ha_O
  obtain ⟨h_cut, -⟩ := h_near.isLocalSymbol ha_O hφ hψ
  let f : Fin d → a.coordRing := (φ ∘ A.coordinate : _ → a.coordRing) -
    (ψ ∘ A.coordinate : _ → a.coordRing)
  replace h_cut {C : CommAlg E} (α : a.coordRing ⟶ C) :
      span (.range f) ≤ ker α.hom ↔ c.app C (W.map α a.point) = u.app C (W.map α a.point) := by
    rw [c.naturality_apply, u.naturality_apply, eq_comm]
    exact h_cut _ (r.map α)
  -- The coincidences are reduced and `w` is the only one in `a`, so `f` generates `ker ζ`.
  have ker_le : ker ζ.hom ≤ span (.range f) :=
    ker_le_of_cuts_out_coincidences ⟨h_red, h_coin, h_field⟩ a ζ hw ha_off h_cut
  -- So `f` cuts out exactly the point `w` of the chart `a`.
  have f_cut : CutsOutLocus W (ComesFromPoints {W.map ζ a.point}) a.point f := by
    refine fun C α ↦ ⟨fun hα ↦ ?_, fun ⟨_, rfl, hα⟩ ↦ (h_cut α).mpr ?_⟩
    · simp [ComesFromPoints, eq_comp_structureMap_of_ker_le (ker_le.trans hα)]
    · rw [hα, c.naturality_apply, u.naturality_apply]
      exact congrArg _ (h_coin _ hw)
  have V_le : (offPoints {W.map ζ a.point}).preimage (pointMap a.point) ≤
      (offPoints s).preimage (pointMap a.point) := by
    -- A point that avoids `w` avoids `s`, as the chart `a` avoids `s \ {w}`.
    intro C p hp K κ hK ⟨z, hz, hκz⟩
    exact (offPoints _).map p.down ha_off K κ hK
      ⟨z, ⟨hz, fun hzw ↦ hp K κ hK ⟨z, hzw, hκz⟩⟩, hκz⟩
  -- On the chart `a`, the class is `n w` times the symbol of `f`.
  exact ⟨a, f, ⟨_, rfl⟩, f_cut, V_le,
    map_pointMap_map_scaledGraph_eq_smul_symbolClass hO h_near off_le ha_O hφ hψ rfl ker_le f_cut
      V_le (hJ _ hw) hc_mem_O⟩

/-- The fixed point formula. If `X` has an atlas of dimension `d`, some `δ` in `Hdg^d(X × X)` pulls
back, as `δ.baseChange` (`δ` read on `E`-algebras through `restrictAlg k E`), along
`scaledGraph t u c` to `∑ w ∈ s, n w • pointClass d w` whenever the coincidences of `u`, `c` are
reduced and form `s`, with Jacobian ratio `n w` at `w ∈ s`. -/
lemma exists_diagonal_map_scaledGraph_eq_sum_pointClass (hX : HasAtlas d X) :
    ∃ δ : HodgeH (freeAb.obj (X ⊗ X)) d,
      ∀ {E : Type} [Field E] [CharZero E] [Algebra k E] {W : CommAlg E ⥤ Type 1}
        [IsSeparatedFunctor W] [IsChartCovered d W] (u c : W ⟶ restrictAlg k E ⋙ X)
        (s : Finset (W.obj (of E E))) (t : E) (n : W.obj (of E E) → E),
        IsCoincidenceSet u c s → (∀ w ∈ s, HasJacobianRatio u c d t (n w) w) →
          H.map hodgeCoeff (freeAb.map (scaledGraph t u c)) d δ.baseChange =
            ∑ w ∈ s, n w • pointClass d w := by
  obtain ⟨δ, hδ⟩ := exists_diagonal_local_terms hX
  exact ⟨δ, fun u c s t n hs hJ ↦ (hδ u c s t n hs hJ).2⟩

/-- The classes of the `k`-points of `X`, where `X` has an atlas of charts with `d` étale
coordinates (`HasAtlas d X`). There is a degree-`d` Hodge class `δ` on `X × X` such that for every
`k`-point `z`: (a) some class with support `z` has multiplicity `1` at `z`; (b) the class of `z` is
the pull-back of `δ` along `x ↦ (z, x)`; (c) for every separated `W` whose field-valued points lie
in charts with `d` coordinates, and every `u : W ⟶ X` whose coincidences with the constant map at
`z` form the reduced finite set `s`, the pull-back of the class of `z` along `u` is the sum of the
classes of the points of `s`. -/
lemma exists_diagonal_pointClass [hX : HasAtlas d X] :
    ∃ δ : HodgeH (freeAb.obj (X ⊗ X)) d, ∀ z : X.obj (of k k),
      -- (a)
      (∃ ξ : HodgeH (relFreeAb (offPoints {z})) d, IsPointSum {z} 1 ξ) ∧
      -- (b)
      HodgeH.map (freeAb.map (lift (constMap z) (𝟙 X))) δ = pointClass d z ∧
      -- (c)
      ∀ {W : CommAlg k ⥤ Type 1} [IsSeparatedFunctor W] [IsChartCovered d W] (u : W ⟶ X)
        (s : Finset (W.obj (of k k))), IsCoincidenceSet (constMap z) u s →
          HodgeH.map (freeAb.map u) (pointClass d z) = ∑ w ∈ s, pointClass d w := by
  obtain ⟨δ, hδ⟩ := exists_diagonal_local_terms hX
  refine ⟨δ.baseChange, fun z ↦ ?_⟩
  -- The fixed point formula for the constant map `constMap z` with `t = 1`: all ratios are `1`.
  have formula {W : CommAlg k ⥤ Type 1} [IsSeparatedFunctor W] [IsChartCovered d W] (u : W ⟶ X)
      (s : Finset (W.obj (of k k))) (hs : IsCoincidenceSet (constMap z) u s) :
      (∃ ξ : HodgeH (relFreeAb (offPoints s)) d, IsPointSum (X := W) s 1 ξ) ∧
        H.map _ (freeAb.map (scaledGraph 1 (constMap z) u)) d (δ.baseChange (k := k)) =
          ∑ w ∈ s, pointClass d w := by
    -- The identity matrix has determinant `1` and relates `du - dc` to itself.
    have ratio_one (w : W.obj (of k k)) : HasJacobianRatio (E := k) (constMap z) u d 1 1 w :=
      fun A _ ↦ ⟨1, Matrix.det_one, fun v α γ _ _ _ ↦ by rw [one_smul, Matrix.one_mulVec]⟩
    obtain ⟨h_pts, h_sum⟩ := hδ (E := k) (constMap z) u s 1 1 hs fun w _ ↦ ratio_one w
    exact ⟨h_pts, h_sum.trans (Finset.sum_congr rfl fun w _ ↦ one_smul _ _)⟩
  -- For `u = 𝟙 X` the only coincidence is `z`.
  have coin_id : IsCoincidenceSet (constMap z) (𝟙 X) {z} := by
    refine ⟨?_, by simp [constMap]⟩
    rintro _ (rfl : _ = X.map structureMap z)
    exact (map_map_structureMap ..).symm
  obtain ⟨h_pts, h_cl⟩ := formula (𝟙 X) {z} coin_id
  rw [Finset.sum_singleton] at h_cl
  rw [Finset.coe_singleton] at h_pts
  refine ⟨h_pts, h_cl, ?_⟩
  intro W hW_sep hW_cov u s hs
  -- Pull the formula for `𝟙 X` back along `u`.
  have pr_comp : sqZeroExt.whiskerLeft (freeAb.map u) ≫
      freeAb.map (scaledGraph 1 (constMap z) (𝟙 X)) = freeAb.map (scaledGraph 1 (constMap z) u) :=
    freeAb.hom_ext (Y := _ ⋙ _)
  rw [← (formula u s hs).2, ← h_cl, ← pr_comp]
  exact (map_comp ..).symm

/-- If `X` has an atlas of dimension `d`, then for every `k`-point `z` of `X` some class of degree
`d` relative to the complement of `z` has multiplicity `1` at `z`. -/
lemma exists_isPointSum_singleton [HasAtlas d X] (z : X.obj (of k k)) :
    ∃ ξ : HodgeH (relFreeAb (offPoints {z})) d, IsPointSum {z} 1 ξ := by
  obtain ⟨δ, hδ⟩ := exists_diagonal_pointClass (d := d) (X := X)
  exact (hδ z).1

/-- If `X` has an atlas of dimension `d`, the class of every `k`-point `z` of `X` is the pull-back
of one class `δ` on `X × X` along `x ↦ (z, x)`. -/
private lemma exists_map_lift_constMap_eq_pointClass [HasAtlas d X] :
    ∃ δ : HodgeH (freeAb.obj (X ⊗ X)) d, ∀ z : X.obj (of k k),
      HodgeH.map (freeAb.map (lift (constMap z) (𝟙 X))) δ = pointClass d z := by
  obtain ⟨δ, hδ⟩ := exists_diagonal_pointClass (d := d) (X := X)
  exact ⟨δ, fun z ↦ let ⟨_, h_cl, _⟩ := hδ z; h_cl⟩

/-- Let `X` have an atlas of dimension `d`, `z` a `k`-point of `X`, and `u : W ⟶ X` a map from a
separated `W` covered by charts of dimension `d` whose fibre over `z` is reduced and is the finite
set `s` (`IsCoincidenceSet (constMap z) u s`). Then `u` pulls the class of `z` back to the sum of
the classes of the points of `s`. -/
lemma map_pointClass_eq_sum_of_isCoincidenceSet [HasAtlas d X] {z : X.obj (of k k)}
    {W : CommAlg k ⥤ Type 1} [IsSeparatedFunctor W] [IsChartCovered d W] (u : W ⟶ X)
    (s : Finset (W.obj (of k k))) (hs : IsCoincidenceSet (constMap z) u s) :
    HodgeH.map (freeAb.map u) (pointClass d z) = ∑ w ∈ s, pointClass d w := by
  obtain ⟨δ, hδ⟩ := exists_diagonal_pointClass (d := d) (X := X)
  exact (hδ z).2.2 u s hs

omit [CharZero k] in
/-- Let `z`, `z'` be two `k`-points of `X` at which every map from `X` to the affine line takes
the same value. Then every Hodge class `x` on `X`, of any degree `a`, has the same restriction to
`z` and to `z'`: the same pull-back along the constant maps from the one-point functor `𝟙_`. -/
lemma map_constMap_eq_of_forall_affine_eq {z z' : X.obj (of k k)}
    (h_val : ∀ g : X ⟶ affineSpace k 1, (g (of k k) z).down 0 = (g (of k k) z').down 0)
    {a : ℕ} (x : HodgeH (freeAb.obj X) a) :
    H.map hodgeCoeff (freeAb.map
        (sqZeroExt.whiskerLeft (constMap (W := 𝟙_ (CommAlg k ⥤ Type 1)) z))) a x =
      H.map hodgeCoeff (freeAb.map
        (sqZeroExt.whiskerLeft (constMap (W := 𝟙_ (CommAlg k ⥤ Type 1)) z'))) a x := by
  -- The point is represented by the pair `P = (k, 0)`. So it has no cohomology in positive degree,
  -- and a class of degree 0 is determined by its value at `P`.
  let P : HodgeTest k := ⟨of k k, Empty⟩
  obtain ⟨h_proj, eval_bij⟩ :=
    -- `P` represents the one-point functor: each of its points comes from exactly one map.
    projective_and_eval_bijective (Y := sqZeroExt ⋙ 𝟙_ _) hodgeCoeff (B := P) ⟨⟩ fun _ ↦
      ⟨fun ⟨_⟩ ⟨_⟩ _ ↦ congrArg _ (hom_ext (by ext) nofun), fun _ ↦ ⟨⟨structureMap, 0⟩, rfl⟩⟩
  cases a with
  | succ a =>
    -- `h_proj` makes the cohomology of the point vanish in positive degree.
    subsingleton
  | zero =>
    rw [← x.mk₀_homEquiv₀_apply]
    -- In degree `0` the pull-back of the class of a map is the class of the composite; `erw`
    -- unfolds the definition of `H.map`.
    have map_mk₀ (w : X.obj (of k k)) :
        H.map hodgeCoeff (freeAb.map
            (sqZeroExt.whiskerLeft (constMap (W := 𝟙_ (CommAlg k ⥤ Type 1)) w))) 0
            (mk₀ (homEquiv₀ x)) =
          mk₀ (freeAb.map (sqZeroExt.whiskerLeft (constMap (W := 𝟙_ (CommAlg k ⥤ Type 1)) w)) ≫
            homEquiv₀ x) := by
      erw [H.map, bilinearComp_apply_apply, mk₀_comp_mk₀]
    refine (map_mk₀ z).trans ((congrArg mk₀ ?_).trans (map_mk₀ z').symm)
    refine eval_bij.1 (ULift.down_injective (formBasis.ext_elem fun i ↦ ?_))
    -- On the pairs `(A, 0)` the class `x` is a natural map from `X A` to forms; its `i`-th
    -- coordinate is a map to the affine line, to which `h_val` applies.
    let incl : 𝟭 (CommAlg k) ⟶ HodgeTest.withIndex Empty ⋙ HodgeTest.sqZeroExt :=
      ⟨fun _ ↦ ofHom (inlAlgHom ..), by intros; ext; exact ext rfl (funext nofun)⟩
    let form : X ⟶ ((Functor.whiskeringRight (CommAlg k) AddCommGrpCat (Type 1)).obj
      (forget AddCommGrpCat)).obj (withIndex Empty ⋙ hodgeCoeff) :=
        freeAb.homEquiv X _ (Functor.whiskerRight incl
      (freeAb.obj X) ≫ (HodgeTest.withIndex Empty).whiskerLeft (homEquiv₀ x))
    exact h_val (form ≫ ⟨fun A ↦ ↾(⟨fun _ ↦ formBasis.repr ·.down i⟩), fun _ _ _ ↦ by
      ext; congrm ⟨fun _ ↦ $(repr_withIndex_map ..)⟩⟩)

/-- Two `k`-points of `X` at which all maps from `X` to the affine line take the same value have
the same class. -/
lemma pointClass_eq_of_functions_eq [HasAtlas d X] {z z' : X.obj (of k k)}
    (h_val : ∀ g : X ⟶ affineSpace k 1, (g (of k k) z).down 0 = (g (of k k) z').down 0) :
    pointClass d z = pointClass d z' := by
  -- `pointClass d z` is the pull-back of one class `δ` along `lift (constMap z) (𝟙 X)`; by the
  -- Künneth formula `δ` is a sum of products `x × y`, so it is enough to compare their pull-backs.
  obtain ⟨δ, hδ⟩ := exists_map_lift_constMap_eq_pointClass (d := d) (X := X)
  rw [← hδ z, ← hδ z']
  refine AddMonoidHom.eqOn_closureM (f := H.map _ _ d) (g := H.map _ _ d) ?_ (kunneth δ)
  rintro _ ⟨a, b, hab, x, y, rfl⟩
  -- The pull-back of `x × y` is the product of the restriction of `x` to the point with `y`.
  let γ := freeAb.map (λ_ (sqZeroExt ⋙ X)).inv ≫ freeAb.prod (sqZeroExt ⋙ 𝟙_ _) (sqZeroExt ⋙ X)
  have pull_prod (w : X.obj (of k k)) :
      H.map hodgeCoeff (sqZeroExt.whiskerLeft (freeAb.map (lift (constMap w) (𝟙 X)))) d
          (HodgeH.map (freeAb.prod X X) (cup exteriorAlg.mulPairing x y hab :)) =
        H.map _ γ d (cup exteriorAlg.mulPairing
          (H.map hodgeCoeff (freeAb.map (sqZeroExt.whiskerLeft (constMap (W := 𝟙_ _) w))) a x)
          (H.map _ (𝟙 _) b y) hab) :=
    (HodgeH.map_comp ..).symm.trans
      (cup_map exteriorAlg.mulPairing x y hab _ _ (freeAb.hom_ext (Y := _ ⋙ _)))
  refine (pull_prod z).trans (.trans ?_ (pull_prod z').symm)
  rw [map_constMap_eq_of_forall_affine_eq h_val]

end FixedPointFormula

end New.Variety

/-!
## The product of a point class with a point class of a curve

`New.Variety.IsPointSum.cup_pointClass`: in Hodge cohomology (`New.Variety.HodgeH`) the external
product (`New.Variety.cup`) of the classes `New.Variety.pointClass` of a point of `X` and a point of
a curve `Y` is the class of the product point. On a product chart this is
`New.Variety.symbolClass_succ`, the product rule for the symbols `[dT / T]`; excision carries it to
`X × Y`.
-/

section PointClassProduct

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Functor New.Variety.relFreeAb

set_option backward.isDefEq.respectTransparency false

/-- Let `x` be a class of degree `d` on `X` relative to `U`, `y` a class of degree `1` on `Y`
relative to `W`, and `s`, `t` points of `X` and `Y` with values in `R` that map `T` into `U` and
`S` into `W`. The pull-back of the external product of `x` and `y` along the point `(s, t)` of
`X × Y` is the external product of the pull-backs of `x` along `s` and `y` along `t`, pulled back
along the diagonal of `Spec R` (`lift (𝟙 _) (𝟙 _)`). -/
lemma New.Variety.pull_cup_along_pair {k : Type} [Field k] [CharZero k] {d : ℕ} {R : CommAlg k}
    {X Y : CommAlg k ⥤ Type 1} {U : Subfunctor X} {W : Subfunctor Y} {T S : Subfunctor (reprBy R)}
    (s : X.obj R) (t : Y.obj R) (hT : T ≤ U.preimage (pointMap s))
    (hS : S ≤ W.preimage (pointMap t)) (x : HodgeH (relFreeAb U) d) (y : HodgeH (relFreeAb W) 1) :
    HodgeH.map (relFreeAb.map (pointMap (Y := X ⊗ Y) (A := R) (s, t)) (sup_le_sup hT hS))
        (HodgeH.map (relFreeAb.prod U W) (cup exteriorAlg.mulPairing x y (add_comm 1 d) :)) =
      HodgeH.map (relFreeAb.map (lift (𝟙 (reprBy R)) (𝟙 (reprBy R))) le_rfl ≫ relFreeAb.prod T S)
        (cup exteriorAlg.mulPairing (x.map (relFreeAb.map (pointMap s) hT))
          (y.map (relFreeAb.map (pointMap t) hS)) (add_comm 1 d) :) := by
  rw [← HodgeH.map_comp]
  exact cup_map _ x y _ (whiskerLeft _ (relFreeAb.map _ hT)) (whiskerLeft _ (relFreeAb.map _ hS))
    (hom_ext (U := (T ⊔ S).whisker _))

/-- Over a field `k` of characteristic `0`, let `X` and `Y` have atlases of dimensions `d` and `1`.
Let `z` be a `k`-point of `X × Y`. Take the classes of `z.1` and `z.2` and multiply them with the
wedge product of coefficients. Pull the product back along `ℤ[X × Y] → ℤ[X] ⊗ ℤ[Y]`. The result is
the class of `z`, in degree `d + 1` of the Hodge cohomology of `X × Y`. -/
lemma New.Variety.IsPointSum.cup_pointClass {k : Type} [Field k] [CharZero k] {d : ℕ}
    {X Y : CommAlg k ⥤ Type 1} [HasAtlas d X] [HasAtlas 1 Y] (z : (X ⊗ Y).obj (CommAlgCat.of k k)) :
    HodgeH.map (freeAb.prod X Y)
        (cup (exteriorAlg (k := k)).mulPairing (pointClass d z.1) (pointClass 1 z.2)
          (add_comm 1 d)) =
      pointClass (d + 1) z := by
  -- The product of the local classes `x`, `y` of `z.1`, `z.2` is a class relative to
  -- `U = (X ∖ z.1) × Y ∪ X × (Y ∖ z.2)`. By excision we compare it with a local class `ξ` of `z` on
  -- the product chart, where both come from the universal symbol `symbolClass`, by
  -- `symbolClass_succ`. By `exists_isPointSum_singleton` local classes exist, and `pointClass` is
  -- the image of any of them.
  obtain ⟨x, x_pt⟩ : ∃ x : HodgeH (relFreeAb (offPoints {z.1})) d, IsPointSum {z.1} 1 x :=
    exists_isPointSum_singleton z.1
  obtain ⟨y, y_pt⟩ : ∃ y : HodgeH (relFreeAb (offPoints {z.2})) 1, IsPointSum {z.2} 1 y :=
    exists_isPointSum_singleton z.2
  have cl_fst : pointClass d z.1 = .map (π _) x := x_pt.map_eq_pointClass.symm
  have cl_snd : pointClass 1 z.2 = .map (π _) y := y_pt.map_eq_pointClass.symm
  -- Charts `a ∋ z.1`, `b ∋ z.2` and functions `g`, `g'` on them that cut out these points, with
  -- `x = [dg / g]` on `a` and `y = [dg' / g']` on `b`.
  obtain ⟨a, g, ha, hx⟩ := x_pt z.1 rfl
  obtain ⟨b, g', hb, hy⟩ := y_pt z.2 rfl
  let G : Fin (d + 1) → (a.prod b).coordRing := Fin.snoc (g · ⊗ₜ 1) (1 ⊗ₜ g' 0)
  -- The equations `g` and `g'` together cut out `z` in the product chart.
  have cut : CutsOutLocus (X ⊗ Y) (ComesFromPoints {z}) (a.prod b).point G := fun _ α ↦ by
    refine .symm (exists_eq_left.trans (Prod.ext_iff.trans ?_))
    simpa -dsimp [G, ComesFromPoints, Ideal.span_le, Set.subset_def, and_comm] using!
      ((hx.1 _ (_ ≫ α)).and (hy.1 _ (_ ≫ α))).symm
  obtain ⟨ξ, ξ_local, ξ_pt⟩ :=
    (a.prod b).exists_isLocalSymbol cut ((range_pointMap_prod ..).ge _ ⟨ha, hb⟩)
  let U : Subfunctor (X ⊗ Y) :=
    (offPoints {z.1}).preimage (fst X Y) ⊔ (offPoints {z.2}).preimage (snd X Y)
  -- A point that avoids `z.1` or `z.2` in its coordinate avoids `z`.
  have hU : U ≤ (offPoints (X := X ⊗ Y) {z}).preimage (𝟙 _) := by
    rintro _ _ (h | h) _ _ hK ⟨_, ⟨⟩, e⟩ <;> exact h _ _ hK ⟨_, rfl, by injections⟩
  let η : HodgeH (relFreeAb U) (d + 1) :=
    HodgeH.map (relFreeAb.prod ..) (cup exteriorAlg.mulPairing x y (add_comm 1 d) :)
  have η_eq : η = ξ.map (relFreeAb.map (𝟙 _) hU) := by
    -- A point off the product chart is off `a` or off `b`, so it has a neighbourhood in `U`.
    have near (K) (hK : IsField K.1) (q) (hq : q ∉ (a.prod b).locus.obj K) :
        ∃ O, IsOpenSubfunctor O ∧ q ∈ O.obj K ∧ O ≤ U := by
      obtain hq | hq := not_and_or.1 fun h ↦ hq ((range_pointMap_prod a b).ge K h)
      · obtain ⟨O, hO_open, hqO, hO_le⟩ := exists_isOpenSubfunctor_le_offPoints ha hK hq
        exact ⟨_, hO_open.preimage _, hqO, fun _ _ h ↦ .inl (hO_le _ h)⟩
      · obtain ⟨O, hO_open, hqO, hO_le⟩ := exists_isOpenSubfunctor_le_offPoints hb hK hq
        exact ⟨_, hO_open.preimage _, hqO, fun _ _ h ↦ .inr (hO_le _ h)⟩
    -- By excision it suffices to compare pull-backs to the product chart. That of `η` is the
    -- product of the symbols of `g ⊗ 1` and `1 ⊗ g'` (`pull_cup_along_pair`, `hx`, `hy`).
    refine (hodge_excision (a.prod b).isOpenSubfunctor near (by rfl) _).1
      ((pull_cup_along_pair ..).trans
        ((congrArg _ (congrArg₂ (fun u v ↦ cup _ u v _) (hx.map _).2.2 (hy.map _).2.2)).trans ?_))
    change _ =
      (ξ.map (relFreeAb.map (𝟙 _) hU)).map (relFreeAb.map (pointMap (a.prod b).point) le_rfl)
    -- Read `pull_cup_along_pair` backwards: this is the pull-back, along `(g ⊗ 1, 1 ⊗ g')`, of the
    -- product of the universal symbols on `𝔸^d × 𝔸^1`.
    erw [one_smul, one_smul, ← pull_cup_along_pair]
    -- `symbolClass_succ` turns the product into `[dG / G]`, the pull-back of `ξ` by `ξ_local`.
    simpa -dsimp [G, (symbolClass_succ ..).2, ← HodgeH.map_comp, pointMap_comp] using!
      congr($(ξ_local.2.2).map (relFreeAb.map (𝟙 (reprBy _)) fun K _ h ↦ hU K h)).symm
  rw [cl_fst, cl_snd]
  -- The left side is the image of `η`, hence of `ξ`, in the cohomology of `X ⊗ Y`.
  refine (cup_map _ _ _ _ (whiskerLeft _ (π _)) (whiskerLeft _ (π _)) rfl).symm.trans
    ((HodgeH.map_comp (π U) (relFreeAb.prod ..) _).trans ((congrArg _ η_eq).trans ?_))
  simp [← HodgeH.map_comp, π_map, ξ_pt.map_eq_smul_pointClass]

end PointClassProduct
