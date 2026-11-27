import Lib.Cohomology.PointClass.LinearIndependence

/-!
# Woods Hole (half of Atiyah–Bott): maps killed under λ_h on Hodge classes are h-null

The main theorem, `New.Variety.ellAdicCohom.woods_hole`: if a combination `∑ b_i u_i` of maps
`W → Y` kills all Hodge classes of `Y` under the Hodge–Tate map `λ_h` (`New.Variety.hodgeTateMap`),
then for every `c : W → Y` the local terms of weight `h` at the coincidences of `c` and the `u_i`
add up to zero (`New.Variety.IsNullFamily`). The proof pulls back the diagonal class of
`New.Variety.exists_diagonal_local_terms`, writes it as a sum of cross products
(`New.Variety.kunneth`) and takes the coefficient of `t ^ h` in the scaling parameter `t`: a linear
form does this (`Polynomial.exists_dual_eval_mul_eq_coeff_mul`), the pull-back of a cross product is
`New.Variety.map_scaledGraph_baseChange_cross`, and
`New.Variety.sum_mul_hodgeTateMap_scaledGraph_eq_zero` is the vanishing of the weighted sum.
`New.Variety.HodgeH` is Hodge cohomology, `New.Variety.algPoints` the functor of points, and
`New.Variety.HasAtlas` a finite cover by charts with `d` étale coordinates.

## Overview of this theory

Throughout, `ℓ` is a fixed prime. Cohomology of a functor `X` to sets, with coefficients in a
functor `F` to abelian groups, is `Extⁿ(ℤ[X], F)`. Here `ℤ[X]` is the free abelian group functor on
`X`, and the Ext is taken in functors on test objects: rings, or pairs of a ring and a module.

On absolutely integrally closed rings `A` (every monic polynomial of positive degree has a root),
locally constant functions on `Spec A` give `𝔽_ℓ`-cohomology. Their Witt vectors give
`ℤ_ℓ`-cohomology. `New.Variety.ellAdicCohom` is `X ↦ ℚ_ℓ ⊗ Hⁿ(X ×_R Ω, ℤ_ℓ)`, for `X` over a ring
`R` and an `R`-algebra `Ω`. Test objects may also be pairs `(B, M)` of a `k`-algebra `B` and a
`B`-module `M`. On these, `New.Variety.HodgeH` of a functor `N` in degree `q` is `Ext^q` from
`(B, M) ↦ N(B ⊕ M)` to `(B, M) ↦ ⋀_B M`.

* `New.Variety.IsProperOver.proper_base_change`: let `A` be an absolutely integrally closed local
  domain that is a valuation ring, with `ℓ` a unit in `A`. Let `Y` be proper over `Spec A`. Then
  restriction from `Y` to its closed fibre is bijective on `𝔽_ℓ`-cohomology in every degree.
* `New.Variety.isTestCohomEquiv_baseChangeTransition`: let `A` be a valuation ring of an algebraic
  closure `ℚ̄` of `ℚ`, with a prime `p` in its maximal ideal and `ℓ` a unit. Let `A` be an algebra
  over a ring `R`, and let `Y` over `R` be built from charts étale over tori
  (`New.Variety.IsCharted`). Then pull-back `Hⁿ(Y_A, 𝔽_ℓ) → Hⁿ(Y_ℚ̄, 𝔽_ℓ)` is bijective for all `n`.
* `New.Variety.ellAdicCohom.woods_hole`: let `R ⊆ E → k ⊆ ℚ̄_p`, with `E` a field of characteristic
  0 and `k` algebraically closed. Let `Y` be proper and `W` projective over `R`. Let `Y` over `E`
  and `W` over `k` have atlases of dimension `d`. Let `uᵢ : W ⟶ Y` be maps, and let `bᵢ ∈ k` be
  almost all zero. Let `λ_h` be the Hodge–Tate map `New.Variety.hodgeTateMap h`. Assume that
  `h > d`, or that `∑ bᵢ λ_h(uᵢ^* x) = 0`, read over `k`, for all `x` of degree at most `d` in
  `HodgeH` of `Y` over `E`. Then `New.Variety.IsNullFamily` holds: for `c : W ⟶ Y`, if each
  coincidence `c y = uᵢ y`, `y ∈ W(k)`, has a tangent polynomial `P` with `P(1) ≠ 0`, the terms
  `bᵢ · (coefficient of degree h of P) / P(1)` add up to zero.

These replace proper base change (SGA 4, XII) and smooth base change (SGA 4), here with coefficients
`𝔽_ℓ` over such rings. They also replace half of the holomorphic Lefschetz (Woods Hole) formula of
Atiyah and Bott, for `h`-forms and correspondences. No comparison with étale or coherent cohomology
is stated.

Structure of the development. `Etale`: descent, Mayer–Vietoris, limits, `ℓ`-adic coefficients.
`ProperBaseChange`: cover `X` by points with values in valuation rings, and reduce to the valuation
rings of a single field. `LerayHirsch`, `TorsionTheories`, `ProjectiveLine`: `1` and the first Chern
class of `O(1)` form a basis of the cohomology of `ℙ¹`. With duality from `Lib.PadicComparison`,
`SmoothBaseChange` follows. `Hodge`: point classes, the Künneth formula, local terms of the
diagonal. `PointClass`: the Hodge–Tate map of `Lib.PadicComparison` keeps distinct point classes
independent, by reduction to `ℙᵈ` and `ℙ¹`.

## This file

Notions from other files:
* `New.Variety.HodgeH.baseChange`: Base change: for an E-algebra k, the additive map from the Hodge
  cohomology over E of N to that over k of N restricted to k-algebras.

## Relation to the literature

Known result: Half of the holomorphic Lefschetz (Woods Hole) formula for h-forms and
correspondences. No trace is computed here. The statement is that if a combination of pull-backs
kills the Hodge classes of degree at most the dimension d under the Hodge–Tate map λ_h, then the z^h
coefficients of the local terms det(1−zA)/det(1−A) at simple coincidences add up to zero. Source:
M. F. Atiyah, R. Bott, A Lefschetz fixed point formula for elliptic complexes II, Ann. of Math. 88
(1968) 451-491; G. Kondyrev, A. Prikhodko, Holomorphic Atiyah-Bott formula for correspondences,
Arnold Math. J. (2022); SGA5 III 6.12.
-/

open CategoryTheory AlgebraicGeometry Polynomial Finset CartesianMonoidalCategory Functor
  MonoidalCategory

set_option backward.isDefEq.respectTransparency false

/-- Let `k` be an infinite field and `h` a natural number. Some linear form `L` on the functions
`k → k` reads off the coefficient of `X ^ h` on polynomial functions: for every polynomial `Q` and
`a` in `k`, `L` sends `t ↦ Q(t) * a` to the coefficient of `X ^ h` in `Q`, times `a`. -/
lemma Polynomial.exists_dual_eval_mul_eq_coeff_mul (k : Type) [Field k] [Infinite k] (h : ℕ) :
    ∃ L : Module.Dual k (k → k),
      ∀ (Q : k[X]) (a : k), L (fun t : k ↦ Q.eval t * a) = Q.coeff h * a := by
  -- Over an infinite field a polynomial is determined by its values, so the coefficient functional
  -- extends from polynomial functions to all functions.
  have h_inj : Function.Injective (LinearMap.pi (leval (R := k)) : k[X] →ₗ[k] k → k) :=
    fun Q Q' h_eq ↦ Polynomial.funext (congrFun h_eq)
  obtain ⟨L, hL⟩ := (LinearMap.pi (leval (R := k))).dualMap_surjective_of_injective h_inj
    (lcoeff k h)
  refine ⟨L, fun Q a ↦ ?_⟩
  simpa [LinearMap.pi] using LinearMap.congr_fun hL (Q * C a)

/-- Let `f g : W ⟶ X` be maps from a functor on `k`-algebras to a functor on `E`-algebras restricted
to `k`-algebras, and `t` in `k`. Pulling the cross product `x × y` of two Hodge classes of `X` back
along `scaledGraph t f g` (`w ↦ (f (s_t w), g w)`, where `s_t : (a, m) ↦ (a, t m)` scales the module
part of `A ⊕ M`), after base change to `k`, gives the cup product of the scaled pull-back
`s_t f^* x` and of `g^* y`, restricted to the diagonal of `W`. -/
lemma New.Variety.map_scaledGraph_baseChange_cross {E k : Type} [Field E] [CharZero E] [Field k]
    [CharZero k] [Algebra E k] {X : CommAlg E ⥤ Type 1} {W : CommAlg k ⥤ Type 1}
    (f g : W ⟶ restrictAlg E k ⋙ X) (t : k) {d q q' : ℕ} (e : q' + q = d)
    (x : HodgeH (freeAb X) q) (y : HodgeH (freeAb X) q') :
    H.map hodgeCoeff (freeAb.map (scaledGraph t f g)) d
        (HodgeH.baseChange (HodgeH.map (freeAb.prod X X) (cup exteriorAlg.mulPairing x y e :))) =
      HodgeH.map (freeAb.map (lift (𝟙 W) (𝟙 W)) ≫ freeAb.prod W W)
        (cup exteriorAlg.mulPairing (HodgeH.scale t (HodgeH.map (freeAbMap f) x.baseChange))
          (HodgeH.map (freeAbMap g) y.baseChange) e :) := by
  -- base change commutes with the cross product; then the pull-back of a cup product is the cup
  -- product of the pull-backs (`cup_map`)
  have h_bc :
      (HodgeH.map (freeAb.prod X X) (cup exteriorAlg.mulPairing x y e :)).baseChange (k := k) =
      .map (whiskerLeft _ (freeAb.prod X X))
        (cup (exteriorAlg (k := k)).mulPairing x.baseChange y.baseChange e :) :=
    (HodgeH.baseChange_map (freeAb.prod X X) (cup exteriorAlg.mulPairing x y e :)).trans
      (congrArg _ ((HodgeTest.baseComparison (k := k) (E := E)).pull_cup
        (abTensor_hom_ext fun _ _ _ ↦ by rfl) x y _))
  refine (congrArg (H.map _ _ d) h_bc).trans ?_
  -- `using!`: the pull-back along `scaledGraph` matches the composite `γ` of `cup_map` only up to
  -- unfolding
  simpa only [H.map_comp] using!
    cup_map (γ := _ ≫ _) exteriorAlg.mulPairing x.baseChange y.baseChange e
    (HodgeTest.scaleModule t _ ≫ whiskerLeft _ (freeAbMap f))
      (whiskerLeft _ (freeAbMap g)) freeAb.hom_ext

-- Keeps definitional checks from unfolding the Ext groups.
seal CategoryTheory.Abelian.Ext in
/-- The vanishing half of the Woods Hole argument. Let `u i : W ⟶ Y` be maps over `R` and `b i ∈ k`
almost all zero. Assume that `Y` over `E` (`algPointsOf E R Y`, the functor of `E`-algebra points of
`Y`) has an atlas of dimension `d`, and that `h > d` or the sum of the `b i • λ_h ((u i)^* x)` is
zero for the Hodge classes `x` of `Y` of degree at most `d`, where `λ_h` is the Hodge–Tate map
`hodgeTateMap`. Let `c : W ⟶ Y`, and let `φ` be a linear form on `PairH` of `W`, the target of
`λ_d`: total cohomology on pairs `(S, M)` of `Z[W](B_{S,M})` with coefficients `S[1/p]`. Let `L` be
a linear form on `k → k` that reads off the coefficient of `t ^ h` on polynomial functions. Then for
every class `z` of `Y × Y`, the sum over `i` of `b i` times `L` of `t ↦ φ (λ_d (Φ t i z))` is zero.
Here `Φ t i z` is `z` pulled back along `(u i ∘ s_t, c)` (`New.Variety.scaledGraph`), with
`s_t : (a, m) ↦ (a, t m)` on the square-zero extension `B ⊕ M` of a `k`-algebra `B`. -/
lemma New.Variety.sum_mul_hodgeTateMap_scaledGraph_eq_zero {p : ℕ} {A : Type*} {E k : Type}
    {d h : ℕ} {I : Type} [CommRing A] [Field E] [CharZero E] [Algebra A E] [Field k]
    [IsAlgClosed k] [EmbeddedInQpBar p k] [Algebra E k] {R : Subalgebra A E}
    {W Y : Over (Spec (CommRingCat.of R))} {u : I → (W ⟶ Y)} {b : I →₀ k}
    (hY_atlas : HasAtlas d (algPointsOf E (CommRingCat.of R) Y))
    (h_null : h ≤ d → ∀ q : ℕ, q ≤ d →
      ∀ x : HodgeH (freeAb.obj ((algPoints E (CommRingCat.of R)).obj Y)) q,
        (b.linearCombination k fun i : I ↦
          hodgeTateMap h (x.map (freeAb.map
            ((algPoints E (CommRingCat.of R)).map (u i)))).baseChange) = 0)
    (c : W ⟶ Y) (φ : Module.Dual k (PairH (freeAb (algPointsOf k (CommRingCat.of R) W))))
    (L : Module.Dual k (k → k))
    (hL : ∀ (Q : k[X]) (a : k), L (fun t : k ↦ Q.eval t * a) = Q.coeff h * a)
    (z : HodgeH (freeAb.obj
      (algPointsOf E (CommRingCat.of R) Y ⊗ algPointsOf E (CommRingCat.of R) Y)) d) :
    ∑ i : b.support, b i * L (fun t : k ↦ φ (hodgeTateMap d
      (H.map hodgeCoeff (freeAb.map (scaledGraph t ((algPoints k (CommRingCat.of R)).map (u i))
        ((algPoints k (CommRingCat.of R)).map c))) d (HodgeH.baseChange z)))) = 0 := by
  let XY : CommAlg E ⥤ Type 1 := algPointsOf E (CommRingCat.of R) Y
  let XW : CommAlg k ⥤ Type 1 := algPointsOf k (CommRingCat.of R) W
  let D (f : W ⟶ Y) : XW ⟶ restrictAlg E k ⋙ XY := (algPoints k (CommRingCat.of R)).map f
  -- `Φ t i` is base change to `k` followed by pull-back along `(u i ∘ s_t, c)`.
  let Φ (t : k) (i : b.support) : HodgeH (freeAb.obj (XY ⊗ XY)) d →+ HodgeH (freeAb XW) d :=
    (H.map hodgeCoeff (freeAb.map (scaledGraph t (D (u i)) (D c))) d).comp HodgeH.baseChange
  -- restate the goal with `Φ`, and `φ`, `z` in terms of `XW`, `XY`
  revert φ z
  intro (φ : Module.Dual k (PairH (freeAb XW))) (z : HodgeH (freeAb.obj (XY ⊗ XY)) d)
  show ∑ i : b.support, b i * L (fun t : k ↦ φ (hodgeTateMap d (Φ t i z))) = 0
  -- the diagonal of `W`, followed by the map to the tensor square
  let diag := freeAb.map (lift (𝟙 _) (𝟙 _)) ≫ freeAb.prod XW XW
  -- `z` is a finite sum of cross products (`kunneth`); on each, `L` keeps the part of weight `h`.
  induction kunneth z using AddSubmonoid.closure_induction_left with
  | zero => simp [← Pi.zero_def]
  | add_left g hg z _ ih =>
    obtain ⟨q, q', e, x, y, rfl⟩ := hg
    -- on a cross product `x × y` the pull-back is `s_t (u i)^* x × c^* y` restricted to the
    -- diagonal (`map_scaledGraph_baseChange_cross`), and `hodgeTateMap_cup` expands its `λ_d`
    have h_lam (t : k) (i : b.support) :
        hodgeTateMap d
            (Φ t i (HodgeH.map (freeAb.prod XY XY) (cup exteriorAlg.mulPairing x y e :))) =
          PairH.map diag (∑ j ∈ range (d + 1),
            (d.choose j • (-1 : k) ^ ((q + j) * (d - j)) • HodgeTatePair.cross
              (hodgeTateMap (d - j) (.map (freeAbMap (D c)) y.baseChange)))
              (hodgeTateMap j (.scale t (.map (freeAbMap (D (u i))) x.baseChange)))) := by
      -- `refine` sees through `Φ`, which `rw` does not
      refine (congrArg (hodgeTateMap d)
        (map_scaledGraph_baseChange_cross (D (u i)) (D c) t e x y)).trans ?_
      rw [hodgeTateMap_map, hodgeTateMap_cup]
    -- the sum of `h_null`, read through the pull-backs along `D (u i)`
    have h_wt (hd : h ≤ d) :
        ∑ i : b.support, b i • hodgeTateMap h (.map (freeAbMap (D (u i))) x.baseChange) = 0 := by
      -- `using!`: `h_null` pulls back along `algPoints E` then restricts, `D` along `algPoints k`;
      -- the two agree only by unfolding
      simpa using! (sum_attach b.support _).trans (h_null hd q (by omega) x)
    -- By `hodgeTateMap_scale` the term of weight `j` carries `t ^ j`, so `L` keeps the term of
    -- weight `h` of the sum over `i` (none if `h > d`): the image under `M` of the sum in `h_wt`,
    -- with `M = φ ∘ diag ∘ (cross with λ_{d - h} (c^* y))` scaled as in `hodgeTateMap_cup`
    let M : PairH (freeAb XW) →ₗ[k] k := φ ∘ₗ PairH.map diag ∘ₗ
      (d.choose h • (-1 : k) ^ ((q + h) * (d - h)) • HodgeTatePair.cross
        (hodgeTateMap (d - h) (HodgeH.map (freeAbMap (D c)) y.baseChange)))
    -- `using!`: the two sides agree only up to unfolding in implicit arguments
    simpa [M, h_lam, ih, hL, hodgeTateMap_scale, ← Pi.add_def, ← sum_fn, mul_add, sum_add_distrib,
      -univ_eq_attach, -LinearMap.smul_apply, -LinearMap.coe_smul, ← eval_X_pow (R := k),
      -eval_pow] using! fun hd ↦ congrArg M (h_wt hd)

/-- Half of the Atiyah–Bott formula. Let `Y` be proper and `W` projective over `R`, a subalgebra of
`E`; let `R → E → k → ℚ̄_p` with `E`, `k` fields of characteristic 0 and `k` algebraically closed
(`EmbeddedInQpBar p k`); let `Y` over `E` and `W` over `k` have atlases of dimension `d`
(`New.Variety.HasAtlas`: finitely many charts with `d` étale coordinates). Let `u i : W ⟶ Y` be maps
and `b i ∈ k` almost all zero. Assume that `h > d`, or that `∑ b i • λ_h ((u i)^* x) = 0` for every
Hodge class `x` of `Y` over `E` of degree `q ≤ d`, read over `k`, with `λ_h` the Hodge–Tate map
`New.Variety.hodgeTateMap h`. Then `∑ b i [u i]` is `h`-null: for every `c : W ⟶ Y`, the local terms
of weight `h` at the coincidences of `c` and the `u i` add up to zero (`New.Variety.IsNullFamily`).
-/
lemma New.Variety.ellAdicCohom.woods_hole {p : ℕ} {A : Type*} {E k : Type} {d h : ℕ} {I : Type}
    [CommRing A] [Field E] [CharZero E] [Algebra A E] [Field k] [IsAlgClosed k]
    [EmbeddedInQpBar p k] [Algebra E k] {R : Subalgebra A E}
    {W Y : Over (Spec (CommRingCat.of R))} [IsProper Y.hom] {u : I → (W ⟶ Y)} {b : I →₀ k}
    (hY_atlas : HasAtlas d (algPointsOf E (CommRingCat.of R) Y))
    (hW_atlas : HasAtlas d (algPointsOf k (CommRingCat.of R) W))
    (h_proj : HasProjEmbedding W.hom)
    (h_null : h ≤ d → ∀ q : ℕ, q ≤ d →
      ∀ x : HodgeH (freeAb.obj ((algPoints E (CommRingCat.of R)).obj Y)) q,
        (b.linearCombination k fun i : I ↦
          hodgeTateMap h (x.map (freeAb.map
            ((algPoints E (CommRingCat.of R)).map (u i)))).baseChange) = 0) :
    IsNullFamily u b d h := by
  -- Pull the diagonal class `δ` back along `(u i ∘ s_t, c)`, apply a linear form
  -- `φ ∘ hodgeTateMap d` that is `1` on point classes, take the coefficient of `t ^ h` and sum with
  -- weights `b i`. By `exists_diagonal_local_terms` this is the sum of the local terms; `kunneth`
  -- and `h_null` make it zero.
  let XY : CommAlg E ⥤ Type 1 := algPointsOf E (CommRingCat.of R) Y
  let XW : CommAlg k ⥤ Type 1 := algPointsOf k (CommRingCat.of R) W
  let D (f : W ⟶ Y) : XW ⟶ restrictAlg E k ⋙ XY := (algPoints k (CommRingCat.of R)).map f
  -- `IsNullFamily`: given `c`, the set `S` of pairs `(i, y)` with `c y = u i y` at a `k`-point
  -- `y`, and tangent polynomials `P` with `P(1) ≠ 0` at them (`hP`), the local terms add up to zero
  intro (c : W ⟶ Y) S (P : (Σ _ : b.support, PointsIn W (CommAlgCat.of k k)) → k[X])
    (hP : ∀ y ∈ S, IsTangentPoly d (D c) (D (u y.fst)) y.snd (P y) ∧ (P y).eval 1 ≠ 0)
  -- `δ` is the class of the diagonal; `hδ` computes its pull-backs (`exists_diagonal_local_terms`)
  obtain ⟨δ, hδ⟩ := exists_diagonal_local_terms hY_atlas
  obtain ⟨φ, hφ⟩ :
      ∃ φ : Module.Dual k (PairH (freeAb XW)), ∀ z ∈ Set.range (pointClass d),
        φ (hodgeTateMap d z) = 1 :=
    Module.exists_dual_forall_apply_eq_one (linearIndepOn_hodgeTateMap_pointClass h_proj)
  -- a linear form on functions `k → k` that gives the coefficient of `t ^ h` on polynomial ones
  obtain ⟨L, hL⟩ : ∃ L : Module.Dual k (k → k),
      ∀ (Q : k[X]) (a : k), L (fun t : k ↦ Q.eval t * a) = Q.coeff h * a :=
    Polynomial.exists_dual_eval_mul_eq_coeff_mul k h
  -- `Φ t i` is base change to `k` followed by pull-back along `(u i ∘ s_t, c)`.
  let Φ (t : k) (i : b.support) : HodgeH (freeAb.obj (XY ⊗ XY)) d →+ HodgeH (freeAb XW) d :=
    (H.map hodgeCoeff (freeAb.map (scaledGraph t (D (u i)) (D c))) d).comp HodgeH.baseChange
  -- A coincidence `y` has Jacobian ratio `P y t / P y 1` and is reduced, so the coincidences of `c`
  -- and `u i` form a finite set `s i` of `k`-points.
  have h_ratio (y : Σ _ : b.support, PointsIn W (CommAlgCat.of k k)) (hy : y ∈ S) (t : k) :
      HasJacobianRatio (D (u y.fst)) (D c) d t ((P y).eval t / (P y).eval 1) y.snd :=
    IsTangentPoly.hasJacobianRatio_eval_div (c := D c) (hP y hy).left hW_atlas.isChartCovered
      (hP y hy).right t
  have h_const (y : Σ _ : b.support, PointsIn W (CommAlgCat.of k k)) (hy : y ∈ S)
      (x : XW.obj (CommAlgCat.of k (DualNumber k))) (hx : XW.map SqZeroExt.fst x = y.snd) :
      ConstIfCoincident (D (u y.fst)) (D c) x :=
    IsTangentPoly.constIfCoincident (c := D c) (hP y hy).left hW_atlas.isChartCovered
      (hP y hy).right hx
  have h_coin (i : b.support) :
      ∃ s : Finset (XW.obj (CommAlgCat.of k k)), IsCoincidenceSet (D (u i)) (D c) s := by
    obtain ⟨r, chart, h_cover⟩ := hW_atlas.exists_finite_charts
    -- a `k[ε]`-valued coincidence reduces to a `k`-valued one, a point of `S`
    have h_mem_red (x : XW.obj (CommAlgCat.of k (DualNumber k)))
        (e : (D c).app _ x = (D (u i)).app _ x) :
        (⟨i, XW.map SqZeroExt.fst x⟩ : Σ _ : b.support, PointsIn W (CommAlgCat.of k k)) ∈ S := by
      congrm _ ≫ $e.1
    exact exists_isCoincidenceSet _ _ (hX := isSeparatedFunctor_algPointsOf)
      (fun x e ↦ h_const ⟨i, XW.map SqZeroExt.fst x⟩ (h_mem_red x e) x rfl e) chart
      fun K hK x _ ↦ h_cover K hK x
  choose s hs using h_coin
  have h_mem (i : b.support) (w : XW.obj (CommAlgCat.of k k)) (hw : w ∈ s i) :
      (⟨i, w⟩ : Σ _ : b.support, PointsIn W (CommAlgCat.of k k)) ∈ S := by
    obtain ⟨-, hs_coin, -⟩ := hs i
    exact congrArg ULift.down (hs_coin w hw)
  have hS : S = univ.sigma s := by
    refine Set.ext fun w ↦ ⟨fun hw ↦ ?_, fun hw ↦ h_mem _ _ (by simpa using hw)⟩
    -- a coincidence at a `k`-point comes from a point of `s`
    obtain ⟨-, -, hs_all⟩ := hs w.fst
    simpa using hs_all _ (Field.toIsField k) _ (ULift.down_inj.1 hw)
  have h_fix (i : b.support) (t : k) :
      Φ t i δ = ∑ w ∈ s i, ((P ⟨i, w⟩).eval t / (P ⟨i, w⟩).eval 1) • pointClass d w :=
    (hδ (D (u i)) (D c) (s i) t (fun w ↦ (P ⟨i, w⟩).eval t / (P ⟨i, w⟩).eval 1) (hs i)
      fun w hw ↦ h_ratio ⟨i, w⟩ (h_mem i w hw) t).right
  -- The weighted sum of the pull-backs of the diagonal class `δ` vanishes.
  have h_zero : ∑ i : b.support, b i * L (fun t : k ↦ φ (hodgeTateMap d (Φ t i δ))) = 0 :=
    sum_mul_hodgeTateMap_scaledGraph_eq_zero hY_atlas h_null c φ L hL δ
  rw [hS]
  refine ⟨finite_toSet _, .trans ?_ h_zero⟩
  -- By `h_fix`, `hφ` and `hL` the `i`-th term for `δ` is the sum of the local terms over `s i`.
  rw [finsum_mem_coe_finset, sum_sigma]
  simp [h_fix, hL, hφ, ← sum_fn, mul_sum, division_def, mul_assoc]
