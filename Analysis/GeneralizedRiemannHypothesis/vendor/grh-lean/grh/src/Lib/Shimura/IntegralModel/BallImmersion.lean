import Lib.Shimura.IntegralModel.UniversalFamily
import Lib.Shimura.TraceFormula.DefiniteTrace
import Lib.Shimura.Uniformisation.ModelExists

/-!
# Balls immerse; holomorphy, arcs and complex points of the covers

This file gives a local and global description of the covers
`New.Variety.UniversalFamily.GraphClosure`. These are reduced closures `C.scheme` of the complex
points `C.point a`. Here `a = (x, ℓ, P)` (`New.Variety.ModuliPoint`) is an adelic frame, a
reflection (1 on a line, −1 on a complement) and marked vectors.

* `New.Variety.AnalyticFamily.isHolomorphicImmersionAt_of_holomorphicAt`: let the objects `x b'`
  have models of the tori of an analytic family. Let `b` be in its domain. Suppose the uniformised
  points are holomorphic at `(b, z)` for every `z`. Then `x` is a holomorphic immersion at `b`.
* `New.Variety.ModuliPoint.exists_finite_analyticFamily_isLevelIso`: at each nonzero level, finitely
  many analytic families reach every point up to isomorphism.
* `New.Variety.UniversalFamily.isHolomorphicImmersionAt_datumPoint`,
  `New.Variety.UniversalFamily.GraphClosure.holomorphicAt_point`: the points of an analytic family
  depend holomorphically, and immersively, on the parameter.
* `New.Variety.UniversalFamily.GraphClosure.exists_arc`,
  `New.Variety.UniversalFamily.GraphClosure.exists_arc_centre_eq`: every point of `C.scheme`, and
  every complex point, is the centre of an arc of objects.
* `New.Variety.UniversalFamily.GraphClosure.point_surjective`: suppose some map `c` sends each
  `C.point a` to `U.datumPoint 1 a`. Then every complex point of `C.scheme` is some `C.point a`.

`New.HolomorphicAt φ w` says that regular functions pull back along `φ` to functions analytic at
`w`.

Notions from other files:
* `New.Variety.AnalyticFamily`: tori with a fixed frame over a domain `f.domain` in ℂⁿ⁻¹, with
  period maps `Q_b` analytic in `b`; the derivative of `Q` along `v` is ℂ-linear for the complex
  structure given by `Q_b` only if `v = 0` (`eq_zero_of_linear`).
* `New.Variety.ModuliPoint.act`: `a.act g α = (x g, ℓ, α i • P i)` for `a = (x, ℓ, P)`.
* `New.Variety.UniversalFamily.datumPoint`: for `a = (x, ℓ, P)`, a chosen complex point over `R` of
  the fibre power of the family: an object modelled on `(x, ℓ)`, with its non-zero `𝔪`-torsion
  points and the points `P`.

## Relation to the literature

Known; see `Lib.Shimura.IntegralModel.TowerExistence` and `Lib.Shimura.ThetaModuli.UniversalFamily`
for sources.
-/

open Filter in
/-- Let `g` be a function on a complex normed space whose derivative has the derivative `D₂` at
`w₀`. Suppose that, for all large `k`, the derivative of `g` at `w₀ + k⁻¹ • a` vanishes in the
direction `u + k⁻¹ • c`. Then the derivative of `g` at `w₀` sends `c` to `-D₂ a u`. -/
lemma fderiv_apply_eq_neg_of_eventually_eq_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {g : F → ℂ} {D₂ : F →L[ℂ] F →L[ℂ] ℂ} {w₀ a u c : F}
    (hD₂ : HasFDerivAt (fderiv ℂ g) D₂ w₀)
    (h_zero : ∀ᶠ k : ℕ in atTop, fderiv ℂ g (w₀ + (k : ℂ)⁻¹ • a) (u + (k : ℂ)⁻¹ • c) = 0) :
    fderiv ℂ g w₀ c = -D₂ a u := by
  -- `δ t` is the derivative of `g` at `w₀ + t • a` in the direction `u + t • c`. It vanishes at
  -- `t = k⁻¹` for large `k`, so its derivative at `0` is zero.
  let δ (t : ℂ) : ℂ := fderiv ℂ g (w₀ + t • a) (u + t • c)
  have hδ : HasDerivAt δ (D₂ a u + fderiv ℂ g w₀ c) 0 :=
    ((hD₂.hasLineDerivAt a).clm_apply ((hasFDerivAt_id u).hasLineDerivAt c)).congr_deriv (by simp)
  -- Otherwise `δ` has no zero in a punctured neighbourhood of `0`.
  by_contra h_ne
  have h_ne_seq : ∀ᶠ k : ℕ in atTop, δ (↑k)⁻¹ ≠ 0 :=
    tendsto_natCast_atTop_cobounded
      (tendsto_inv₀_cobounded' (hδ.eventually_ne (by rwa [Ne, add_eq_zero_iff_eq_neg'])))
  exact h_zero.frequently h_ne_seq

namespace New.Variety

open CategoryTheory Over OverMorphism AlgebraicGeometry NumberField IsLocalRing ThetaObject Obj
  TorusModel Filter Cardinal IsGroupBaseChange LocallyOfFiniteType Set Submodule
  ModuliPoint

variable {E : Type} [Field E] [CMBase E] {D : PEL E}
  {R : Subalgebra (𝓞 E) E} {ν : ℕ} [NeZero ν] {U : UniversalFamily D R} {J : Type} [Finite J]
  {γ : J → nonZeroDivisors (𝓞 E) × GUPlus E D.Index}

/-- Two invertible finite adelic matrices that induce the same map on torsion classes are equal. -/
lemma eq_of_forall_torsionClass_mulVec_eq {A B : GL D.Index (𝔸f E)}
    (h_tors : ∀ w : D.Index → 𝔸f E, torsionClass (A.val.mulVec w) = torsionClass (B.val.mulVec w)) :
    A = B := by
  refine Units.ext (funext₂ fun k l ↦ sub_eq_zero.mp (eq_zero_of_forall_mul_integral fun a ↦ ?_))
  -- Compare the classes of the torsion points of `a` times the `l`-th basis vector.
  simpa [mul_comm, mul_sub] using torsionClass_eq_iff.mp (h_tors (Pi.single l a)) k

omit [NeZero ν] in
/-- Let `a`, `a'` be points and `g` an element of `GUPlus E D.Index`. Suppose `z` carries the
reflection of `a` to that of `a'` and the marked points of `a` to those of `a'`, and
`g⁻¹ = a'.frame⁻¹ * z * a.frame`. Then `z` is an isomorphism from `a.act g` to `a'` at every level
`K`: it matches reflections and marked points, and `a'.frame⁻¹ * z * (a.act g).frame ∈ K`. -/
lemma ModuliPoint.isLevelIso_act_of_inv_eq {a a' : ModuliPoint E D.Index ν} {g : GUPlus E D.Index}
    {z : GL D.Index E} (K : Subgroup (GL D.Index (𝔸f E)))
    (h_x : g.val⁻¹ = a'.frame⁻¹ * toFinGL z * a.frame)
      (h_refl : ratConj z a.reflection = a'.reflection)
    (h_P : ∀ j : Fin ν, a'.markedPoint j = realVecAction z (a.markedPoint j)) :
      (a.act g).IsLevelIso K z a' := by
  refine ⟨?_, by simpa [act] using h_refl, fun j ↦ by simp [act, h_P]⟩
  -- The level part `a'.frame⁻¹ * z * (a.frame * g)` is `g⁻¹ * g = 1`.
  show a'.frame⁻¹ * toFinGL z * (a.frame * g.val) ∈ K
  simp [← mul_assoc, ← h_x]

/-- Balls immerse. Let `f` be an analytic family of theta tori over `f.domain`, and `X` a theta
family (an abelian scheme with `𝓞 E`-action and theta coordinates) over `Z`. Let each `x b'` be a
complex point of `Z` with a model `m b'`, a uniformisation of the fibre of `X` at `x b'` by the
torus `f.torus b'`. Let `ψ (b', z)` be the image of `z` under this uniformisation, a complex point
of `X`. If `b ∈ f.domain` and `ψ` is holomorphic at every `(b, z)`, then `x` is a holomorphic
immersion at `b` as a family of complex points of `Z`: it is holomorphic there, and constant to
first order only in the direction `0`. -/
lemma AnalyticFamily.isHolomorphicImmersionAt_of_holomorphicAt {f : AnalyticFamily D} {Z : Scheme}
    {τ : Z ⟶ Spec (CommRingCat.of (𝓞 E))}
    {X : ThetaFamily D Z τ} {x : BallBase D.Index → ThetaObject X (Spec (CommRingCat.of ℂ))}
    (m : ∀ b : BallBase D.Index, (x b).TorusModel (f.torus b).toPeriodMap) {b : BallBase D.Index}
    (hb : b ∈ f.domain) :
    let ψ (q : BallBase D.Index × BallFibre E D.Index) :=
      atGeneric (m q.1).uniformisation.expMap q.2 ≫ (x q.1).toFamily.left
    (∀ z : BallFibre E D.Index, HolomorphicAt ψ (b, z)) → IsHolomorphicImmersionAt x b := by
  intro ψ h_hol
  refine ⟨?_, fun v hv ↦ ?_⟩
  · -- The point `x b'` of the base is the image of `ψ (b', 0)`.
    simpa [ψ] using ((h_hol 0).comp (g := fun b' ↦ (b', 0)) (by fun_prop)).comp_hom X.total.hom
  -- Let the base point be still in the direction `v`. Follow `y` along the family as
  -- `T y b' = Q_b' Q_b⁻¹ y`, with derivative `T' y` along `v`. By `f.eq_zero_of_linear` it is
  -- enough that `T'` commutes with `I`.
  let T (y : BallFibre E D.Index) (b' : BallBase D.Index) : BallFibre E D.Index :=
    (f.torus b').realEquiv ((f.torus b).realEquiv.symm y)
  let T' (y : BallFibre E D.Index) : BallFibre E D.Index := fderiv ℂ (T y) b v
  have h_an (w : RealVectors E D.Index) : AnalyticAt ℂ (fun b' ↦ (f.torus b').realEquiv w) b :=
    f.analyticAt b hb w
  -- The torsion sections `b' ↦ ψ (b', k⁻¹ • T l b')`, `l` in the lattice, are still: their `k`-th
  -- multiple is the zero section over the base point, and multiplication by `k` is an immersion.
  have h_torsion (l : BallFibre E D.Index) (hl : l ∈ (m b).uniformisation.lattice) (k : ℕ)
    (hk : k ≠ 0) :
      IsFirstOrderConst ψ (b, (k : ℂ)⁻¹ • T l b) (v, (k : ℂ)⁻¹ • T' l) := by
    have h_curve : HasFDerivAt (fun b' : BallBase D.Index ↦ (b', (k : ℂ)⁻¹ • T l b'))
        ((ContinuousLinearMap.id ℂ (BallBase D.Index)).prod ((k : ℂ)⁻¹ • fderiv ℂ (T l) b)) b :=
      (hasFDerivAt_id b).prodMk
        ((h_an ((f.torus b).realEquiv.symm l)).differentiableAt.hasFDerivAt.const_smul (k : ℂ)⁻¹)
    -- `T l b'` lies in the lattice of the member `b'`: the period maps carry the lattices onto
    -- each other.
    have h_lattice (b' : BallBase D.Index) : T l b' ∈ (m b').uniformisation.lattice := by
      simp_all [T, TorusModel.lattice_eq, mem_classLattice, (f.torus _).realEquiv.eq_symm_apply]
    -- So the `k`-th multiple of the section is the zero section over `x b'`.
    have h_mul_eq (b' : BallBase D.Index) :
        ψ (b', (k : ℂ)⁻¹ • T l b') ≫ (k • 𝟙 X.total).left = x b' ≫ (X.levelPoints 0).left := by
      have h_exp_zero : (m b').uniformisation.expMap (T l b') = 0 :=
        ((m b').uniformisation.eq_zero_iff (T l b')).mp (h_lattice b')
      simp_all [← (x _).isGroupBaseChange.nsmul_id_comp, ← comp_left_assoc, ← map_nsmul,
        ← Nat.cast_smul_eq_nsmul ℂ, ψ, ← (x _).isGroupBaseChange.pullSection_comp, comp_nsmul]
    have h_still :
        IsFirstOrderConst (fun b' ↦ ψ (b', (k : ℂ)⁻¹ • T l b') ≫ (k • 𝟙 X.total).left) b v := by
      simpa only [h_mul_eq, Category.assoc] using hv.comp_hom (X.levelPoints 0).left
    exact (h_hol _).isFirstOrderConst_of_nsmul X.relative_dim hk
      ((isJet_comp_iff h_curve ((h_hol _).comp_hom _)).mp h_still)
  -- On the fibre over `b`, `ψ` is a uniformisation, hence an immersion; so it is enough to test
  -- `T' (I • y) - I • T' y` on functions `r` regular near `ψ (b, 0)`.
  obtain ⟨-, h_fibre_still⟩ :=
    (m b).uniformisation.isHolomorphicImmersionAt_of_isPullback (x b).isGroupBaseChange.isPullback 0
  refine f.eq_zero_of_linear b hb v fun y ↦ sub_eq_zero.mp (h_fibre_still _ ?_)
  refine (isJet_comp_iff (hasFDerivAt_prodMk_right b 0) (h_hol 0)).mpr
    (isFirstOrderConst_iff.mpr fun U r hU ↦ ?_)
  -- `r ∘ ψ` is analytic at `(b, 0)`; `D₂` is its second derivative there.
  obtain ⟨h_near, h_analytic⟩ : (∀ᶠ w in nhds (b, 0), LandsIn (ψ w) U) ∧
      AnalyticAt ℂ (fun w ↦ PointFn.ofSection r (CommRingCat.of ℂ) (ψ w)) (b, 0) :=
    h_hol 0 (PointFn.isRegularOn_ofSection r) hU
  obtain ⟨D₂, hD₂⟩ := h_analytic.fderiv.differentiableAt
  set i : BallFibre E D.Index →L[ℂ] BallBase D.Index × BallFibre E D.Index := .inr ℂ _ _
  -- The derivative of `r ∘ ψ` along `T' y` is given by the second derivative `D₂`, linearly in `y`.
  have h_fderiv_T'_eq (y : BallFibre E D.Index) :
      fderiv ℂ (fun q ↦ PointFn.ofSection r _ (ψ q)) (b, 0) (i (T' y)) = -D₂ (i y) (v, 0) := by
    -- Both sides are real-linear in `y`, and the lattice spans.
    have h_span : y ∈ span ℝ ((m b).uniformisation.lattice : Set (BallFibre E D.Index)) := by
      simp [IsZLattice.span_top]
    induction h_span using span_induction with
    | mem l hl =>
      -- By `h_torsion`, the derivative of `r ∘ ψ` at `(b, k⁻¹ • l)` in the direction
      -- `(v, k⁻¹ • T' l)` vanishes for all large `k`.
      refine fderiv_apply_eq_neg_of_eventually_eq_zero hD₂ ?_
      have h_curve_lim : Tendsto (fun k : ℕ ↦ (b, (k : ℂ)⁻¹ • T l b)) atTop (nhds (b, 0)) :=
        tendsto_const_nhds.prodMk_nhds (tendsto_inv_atTop_nhds_zero_nat.zero_smul_const _)
      filter_upwards [eventually_ne_atTop 0, h_curve_lim.eventually h_near] with k hk h_in
      simpa [i, T] using isFirstOrderConst_iff.mp (h_torsion l hl k hk) U r h_in
    | zero => simp [T, T']
    | add y y' _ _ hy hy' =>
      -- `T'` is additive and real-linear, because the periods are.
      have h_T'_add : T' (y + y') = T' y + T' y' := by
        simp (disch := fun_prop) [T', T, fderiv_fun_add]
      simp only [h_T'_add, map_add, add_apply, neg_add, hy, hy']
    | smul a y _ hy =>
      have h_T'_smul : T' (a • y) = a • T' y := by
        simp (disch := fun_prop) [T', T, fderiv_fun_const_smul]
      simp [h_T'_smul, hy]
  -- The right side of `h_fderiv_T'_eq` is `ℂ`-linear in `y`.
  dsimp only [T, T'] at h_fderiv_T'_eq
  simp [h_fderiv_T'_eq]

/-- For `𝔪 ≠ 0` there are finitely many analytic families `f k`, `k : κ`, with this property: every
point `a : ModuliPoint E D.Index ν` is isomorphic at level `levelGU D.Index 𝔪`, by some
`z : GL D.Index E`, to a point `(f k).ballPoint 0 p` (the member of `f k` at `p.1`, with marked
points `p.2`) with `p.1` in the domain of `f k`. -/
lemma ModuliPoint.exists_finite_analyticFamily_isLevelIso (D : PEL E) (ν : ℕ) {𝔪 : 𝓞 E}
    (h𝔪 : 𝔪 ≠ 0) :
    ∃ (κ : Type) (f : κ → AnalyticFamily D),
      Finite κ ∧
      ∀ a : ModuliPoint E D.Index ν, ∃ k : κ, ∃ p ∈ (f k).domain.1 ×ˢ .univ, ∃ z : GL D.Index E,
        a.IsLevelIso (levelGU D.Index 𝔪) z ((f k).ballPoint 0 p) := by
  -- Index by the double cosets of the frames `a.frame`, and take the ball at a chosen point of
  -- each.
  let φ (a : ModuliPoint E D.Index ν) :
      DoubleCoset.Quotient
        ((toFinGL : GL D.Index E →* GL D.Index (𝔸f E)).range : Set (GL D.Index (𝔸f E)))
        (levelGU D.Index 𝔪 : Set (GL D.Index (𝔸f E))) :=
    DoubleCoset.mk toFinGL.range (levelGU D.Index 𝔪) a.frame
  -- For each coset `c`, a family through its chosen point meets every point with that frame.
  choose f hf using fun c : range φ ↦ exists_isBallFamily (rangeSplitting φ c)
  -- Signed frames meet finitely many double cosets.
  have h_finite : (range φ).Finite := by
    exact (finite_isSignedFrame_classes (isOpen_congruenceGL_span h𝔪)).subset <|
      range_subset_iff.mpr fun a ↦ ⟨a.frame, ⟨a.reflection, a.isSignedFrame⟩, rfl⟩
  refine ⟨range φ, f, h_finite, fun a ↦ ?_⟩
  -- The chosen point of the coset of `a` has the frame `toFinGL z * a.frame * k`; move `a` there.
  let c : range φ := ⟨φ a, a, rfl⟩
  obtain ⟨-, ⟨z, rfl⟩, k, hk, hz⟩ := (DoubleCoset.eq ..).mp (apply_rangeSplitting φ c).symm
  obtain ⟨hk_GU, -⟩ := Subgroup.mem_inf.mp hk
  let a' : ModuliPoint E D.Index ν :=
    { frame := toFinGL z * a.frame * k
      reflection := ratConj z a.reflection
      markedPoint := realVecAction z ∘ a.markedPoint
      isSignedFrame := a.isSignedFrame.mul z hk_GU
      isReflection := a.isReflection.conj _ }
  obtain ⟨p, hp, h_pt⟩ := (hf c).exists_ballPoint_eq a' hz.symm
  refine ⟨c, p, hp, z, ?_⟩
  -- `z` carries `a` to `a'`, with level part `k⁻¹`.
  rw [h_pt]
  simpa [a', isLevelIso_iff, mul_assoc]

/-- Let `f` be an analytic family and `P` marked vectors. The map sending a parameter `p` to the
point `U.datumPoint 𝔪 (f.ballPoint P p)` of the fibre power of the universal family `U` (the member
of `f` at `p`, with its non-zero `𝔪`-torsion points and the points `P` translated by `p.2`) is a
holomorphic immersion at every `p` whose base coordinate `p.1` lies in the domain of `f`. -/
lemma UniversalFamily.isHolomorphicImmersionAt_datumPoint {f : AnalyticFamily D}
    {P : Fin ν → RealVectors E D.Index} {𝔪 : nonZeroDivisors (𝓞 E)}
    (p : BallBase D.Index × (Fin ν → BallFibre E D.Index)) (hp : p.1 ∈ f.domain) :
    IsHolomorphicImmersionAt (fun q ↦ (U.datumPoint 𝔪 (f.ballPoint P q)).left) p := by
  obtain ⟨h_base_hol, h_base_imm⟩ : IsHolomorphicImmersionAt (fun b ↦ (U.obj (f, b)).left) p.1 :=
    f.isHolomorphicImmersionAt_of_holomorphicAt (U.model ⟨f, ·⟩) hp (U.holomorphic f _ hp)
  have h_an (w : RealVectors E D.Index) : ContDiffAt ℂ ⊤ (fun q ↦ (f.torus q.1).realEquiv w) p :=
    (f.analyticAt _ hp w).contDiffAt.fst''
  -- The uniformisation of the family at an analytic fibre coordinate `k` is holomorphic.
  have h_unif (k : BallBase D.Index × (Fin ν → BallFibre E D.Index) → BallFibre E D.Index)
      (hk : ContDiffAt ℂ ⊤ k p) :
      HolomorphicAt (fun q ↦ atGeneric (U.model (f, q.1)).uniformisation.expMap (k q) ≫
        (ThetaObject.toFamily (U.obj (f, q.1)).left).left) p :=
    (U.holomorphic f _ hp _).comp (v₀ := p) (g := fun q ↦ (q.1, k q))
      (ContDiffAt.analyticAt (by fun_prop))
  -- Describe the points by the models of the family `f`; holomorphy is tested on the projections
  -- to the factors of the fibre power.
  have h_hol : HolomorphicAt (fun q ↦ (U.datumPoint 𝔪 (f.ballPoint P q)).left) p := by
    simp_rw [← IsPointOf.eq_datumPoint (a := f.ballPoint P _) ⟨U.model (f, _), rfl⟩]
    refine HasGermAt.of_jointly_mono (fun l ↦ (Over.map U.base.hom).map (Limits.Pi.π _ l))
      (fun h_eq ↦ ext (fibrePower_ext_iff.mpr ⟨?_, fun l ↦ congrArg (·.left) (h_eq l)⟩)) ?_
      -- over the base point: `simp` leaves `Spec.map _ = ?b`, and `rfl` fixes the implicit `b`
      (by simp; rfl)
    · -- The projections separate points: there is at least one factor, and it sees the base.
      simpa using congrArg (·.left ≫ U.family.total.hom) (h_eq Classical.ofNonempty)
    · -- The torsion points and the marked points have analytic fibre coordinates.
      rintro (l | i)
      · -- `using!`: a torsion point is the exponential of its period only after unfolding.
        simpa using! h_unif
          (fun q ↦ (f.torus q.1).realEquiv (toRealVectors (ThetaTori.ratLift f.frame l.val.val)))
            (h_an _)
      · simpa [π] using h_unif (fun q ↦ q.2 i + (f.torus q.1).realEquiv (P i)) (by fun_prop)
  refine ⟨h_hol, fun (v, y) hv ↦ ?_⟩
  -- Project to the base to get `v = 0`, then to the `i`-th marked point to get `y i = 0`.
  have h_base_still : IsFirstOrderConst (fun b ↦ (U.obj (f, b)).left) p.1
      (ContinuousLinearMap.fst ℂ (BallBase D.Index) (Fin ν → BallFibre E D.Index) (v, y)) := by
    refine (isJet_comp_iff hasFDerivAt_fst h_base_hol).mp ?_
    simp_rw [← IsPointOf.eq_datumPoint (a := f.ballPoint P _) ⟨U.model (f, _), rfl⟩] at hv
    simpa using hv.comp_hom (U.family.fibrePower _).hom
  obtain rfl : v = 0 := h_base_imm v h_base_still
  suffices h_fibre_zero : ∀ i, y i = 0 by simpa [funext_iff] using h_fibre_zero
  intro i
  -- Along the fibre over `p.1`, the `i`-th marked point is still in the direction `y`.
  have h_fibre : IsFirstOrderConst
      (fun w ↦ (U.datumPoint 𝔪 (f.ballPoint P (p.1, w))).left ≫ U.family.proj (.inr i)) p.2 y := by
    simpa only [Category.assoc] using
      ((isJet_comp_iff (hasFDerivAt_prodMk_right p.1 p.2) h_hol).mpr hv).comp_hom
        (U.family.proj (.inr i))
  simp_rw [← IsPointOf.eq_datumPoint (a := f.ballPoint P _) ⟨U.model (f, _), rfl⟩] at h_fibre
  obtain ⟨h_fibre_hol, h_imm⟩ := (U.model
    (f, p.1)).uniformisation.isHolomorphicImmersionAt_of_isPullback
      (ThetaObject.isGroupBaseChange (X := U.family) _).isPullback
        (p.2 i + (f.torus p.1).realEquiv (P i))
  refine h_imm (y i) ((isJet_comp_iff
    ((hasFDerivAt_apply (𝕜 := ℂ) i p.2).add_const _) h_fibre_hol).mp ?_)
  simpa [π] using h_fibre

namespace UniversalFamily.GraphClosure

/-- Let `C` be the cover (the reduced closure of the points `C.point a`, whose component `j` is
`U.datumPoint (γ j).1 (a.act (γ j).2)`), `f` an analytic family and `P` marked vectors. The map
sending a parameter `p` to the complex point `C.point (f.ballPoint P p)` of `C` is holomorphic at
every `p` whose base coordinate `p.1` lies in the domain of `f`. -/
lemma holomorphicAt_point (C : U.GraphClosure γ ν) {f : AnalyticFamily D}
    (P : Fin ν → RealVectors E D.Index)
    (p : BallBase D.Index × (Fin ν → BallFibre E D.Index)) (hp : p.1 ∈ f.domain) :
    HolomorphicAt (fun q ↦ (C.point (f.ballPoint P q)).left) p := by
  -- Test on the components of the cover; each is given by a translated family, so
  -- `isHolomorphicImmersionAt_datumPoint` applies.
  refine .of_jointly_mono _ C.hom_ext (fun j ↦ ?_) fun q ↦ Over.w (C.point (f.ballPoint P q))
  -- The translate by `(γ j).2` of a point of `f` is the point of the translated family.
  have h_act (q : BallBase D.Index × (Fin ν → BallFibre E D.Index)) :
      (f.ballPoint P q).act (γ j).2 = (f.heckeTranslate (γ j).2).ballPoint P q := by
    simp [act, AnalyticFamily.heckeTranslate, funext_iff]
  have h_component (q : BallBase D.Index × (Fin ν → BallFibre E D.Index)) :
      (C.point (f.ballPoint P q)).left ≫ (ReducedClosure.proj C j).left =
        (U.datumPoint (γ j).1 ((f.heckeTranslate (γ j).2).ballPoint P q)).left := by
    rw [← comp_left, C.point_comp_proj, h_act]
  obtain ⟨h_hol, -⟩ := isHolomorphicImmersionAt_datumPoint (U := U) (𝔪 := (γ j).1)
    (f := f.heckeTranslate (γ j).2) (P := P) p hp
  simpa only [h_component] using h_hol

/-- Let `C` be the cover (the reduced closure of the points `C.point a`) and `z` a point of
`C.scheme`. There are a valuation subring `V` of `ℂ`, an arc `α : Spec V ⟶ C.scheme`, a point `b`
and a map `ρ` from the residue field of `z` to the residue field of `V` with two properties. (a) The
closed point of `α` is `z`, through `ρ`. (b) Whenever `C.point b ≫ u` is the point
`U.datumPoint 𝔪 a`, the composite of `α` and `u` is a point of the universal family for `a` at level
`𝔪`. -/
lemma exists_arc (C : U.GraphClosure γ ν) (z : C.scheme.left) :
    ∃ᵉ (V : ValuationSubring ℂ) (α : Spec (CommRingCat.of V) ⟶ C.scheme.left)
      (b : ModuliPoint E D.Index ν) (ρ : C.scheme.left.residueField z →+* ResidueField V),
      -- (a)
      specMap ρ ≫ C.scheme.left.fromSpecResidueField z = specMap (residue V) ≫ α ∧
      -- (b)
      ∀ {𝔪 : nonZeroDivisors (𝓞 E)}
        {u : C.scheme ⟶
          (Over.map U.base.hom).obj (ThetaFamily.fibrePower (NonzeroTorsion 𝔪 D.Index ⊕ Fin ν))}
        {a : ModuliPoint E D.Index ν},
        C.point b ≫ u = U.datumPoint 𝔪 a → U.family.IsPointOf 𝔪 a (α ≫ u.left) := by
  have := U.isDedekindDomain
  have := isLocallyNoetherian C.scheme.hom
  -- At the level `𝔫` that determines the points `C.point a`, finitely many families `f k` meet all
  -- of them; in each, one point `C.point ((f k).ballPoint 0 (b k))` specialises to all points of
  -- the family.
  obtain ⟨𝔫, h_level⟩ := C.exists_level_point_eq
  obtain ⟨κ, f, hκ, h_meet⟩ := exists_finite_analyticFamily_isLevelIso D ν
    (nonZeroDivisors.coe_ne_zero 𝔫)
  -- In each family some member `b k` is generic: its point specialises to those of all members.
  choose b hb_mem hb using fun k ↦ exists_generic_member C.scheme.hom
    ((f k).domain.isOpen.prod isOpen_univ)
    ((f k).isConnected.prod isConnected_univ) fun p hp ↦ C.holomorphicAt_point 0 p hp.1
  have h_dense : IsDenseFamily fun k ↦ (C.point ((f k).ballPoint 0 (b k))).left := by
    intro w
    refine C.isSeparatingFamily.right.induction_on w isClosed_closure fun a ↦ ?_
    obtain ⟨k, q, hq, z_iso, h_rel⟩ := h_meet a
    simpa only [h_level h_rel] using
      (hb k q hq).mem_closed isClosed_closure (subset_closure (mem_range_self k))
  -- So an arc `α` starts at one of these points and has its centre at `z`.
  obtain ⟨k, V, α, h_start, rfl⟩ := New.exists_valuative_arc_of_isDenseFamily _ h_dense z
  -- The closed point of `V` is the image of the point of its residue field.
  rw [← comap_closedPoint (residue V.valuationSubring)]
  refine ⟨_, α, (f k).ballPoint 0 (b k), _,
    (C.scheme.left.SpecToEquivOfField _).left_inv (specMap _ ≫ α), ?_⟩
  intro 𝔪 u a h_u
  -- The generic point of `α ≫ u` is the point of `a`.
  refine .of_generic (?_ : U.family.IsPointOf 𝔪 a
    (specMap V.valuationSubring.subtype ≫ α ≫ u.left))
  rw [reassoc_of% h_start, ← comp_left, h_u]
  exact isPointOf_datumPoint

/-- Let `C` be the cover (the reduced closure of the points `C.point a`) and `t` a complex point of
`C.scheme` over `R`. There are a valuation subring `V` of `ℂ`, an arc `α : Spec V ⟶ C.scheme`, a
point `b` and a ring map `φ` from the residue field of `V` to `ℂ` with two properties. (a) The
closed point of `α`, seen through `φ`, is `t`. (b) Whenever `C.point b ≫ u` is the point
`U.datumPoint 𝔪 a`, the composite of `α` and `u` is a point of the universal family for `a` at level
`𝔪`. -/
lemma exists_arc_centre_eq (C : U.GraphClosure γ ν)
    (t : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))) ⟶ C.scheme) :
    ∃ᵉ (V : ValuationSubring ℂ) (α : Spec (CommRingCat.of V) ⟶ C.scheme.left)
      (b : ModuliPoint E D.Index ν) (φ : ResidueField V →+* ℂ),
      -- (a)
      specMap (φ.comp (residue V)) ≫ α = t.left ∧
      -- (b)
      ∀ {𝔪 : nonZeroDivisors (𝓞 E)} {u : C.scheme ⟶
          (Over.map U.base.hom).obj (ThetaFamily.fibrePower (NonzeroTorsion 𝔪 D.Index ⊕ Fin ν))}
        {a : ModuliPoint E D.Index ν},
        C.point b ≫ u = U.datumPoint 𝔪 a → U.family.IsPointOf 𝔪 a (α ≫ u.left) := by
  -- Take an arc `α` over a valuation ring `V` centred at the image `s` of `t`. The residue field of
  -- `s` is countable, so `t` is the centre of `α` under an embedding `φ` of the residue field of
  -- `V`, whose cardinality is at most that of `ℂ`.
  obtain ⟨s, φ₀, hφ₀, h_countable⟩ := exists_countable_residue_point C.scheme.hom t.left
  obtain ⟨V, α, b, ρ, h_centre_ρ, h_arc⟩ := C.exists_arc s
  obtain ⟨φ, rfl⟩ := exists_ringHom_complex_extend ρ.injective φ₀.injective
    (mk_quotient_le.trans (mk_set_le _) : #(ResidueField V) ≤ #ℂ)
  -- Through `φ`, the closed point of `α` is that of the residue field of `s`, which is `t`.
  refine ⟨V, α, b, φ, ?_, h_arc⟩
  calc specMap (φ.comp (residue V)) ≫ α = specMap φ ≫ specMap (residue V) ≫ α := by
        simp [specMap]
    _ = specMap φ ≫ specMap ρ ≫ C.scheme.left.fromSpecResidueField s := by rw [h_centre_ρ]
    _ = t.left := by simpa [specMap] using hφ₀

/-- Let `C` be the graph closure for the pairs γ_j = (𝔪_j, g_j) and ν. Here `C.scheme` is the
reduced closure, in a product of fibre powers of the universal family `U`, of the tuples over j of
`U.datumPoint 𝔪_j (a.act g_j)`, and `C.point a` is its complex point for a point a = (x, ℓ, P) at
infinite level: an adelic matrix x, a reflection ℓ for which x is a signed frame, and marked
vectors P i in (E ⊗ ℝ)ⁿ.
Suppose a morphism `c` from `C.scheme` to the fibre power of the abelian scheme of `U` indexed by
the nonzero 1-torsion and `Fin ν` sends each `C.point a` to `U.datumPoint 1 a`, the chosen complex
point given by an object modelled on (x, ℓ) with the images of the P i. Then every complex point
over `R` of `C.scheme` is `C.point a` for some a. -/
lemma point_surjective (C : U.GraphClosure γ ν)
    {c : C.scheme ⟶
      (Over.map U.base.hom).obj (ThetaFamily.fibrePower (NonzeroTorsion 1 D.Index ⊕ Fin ν))}
    (hc : ∀ a : ModuliPoint E D.Index ν, C.point a ≫ c = U.datumPoint 1 a) :
    C.point.Surjective := by
  -- Follow an arc from a point `C.point b` to `t`; at its centre the object has a model `(g, ℓ)`,
  -- and the isogenies between components identify `t` with `C.point (g, ℓ, P ∘ b.markedPoint)`.
  intro t
  obtain ⟨V, α, b, φ, h_centre, h_arc⟩ := C.exists_arc_centre_eq t
  -- Along the arc `α ≫ c` is the point of an object `y` with a model `e`.
  obtain @⟨y, V_y, h_V_y, Y_y, e, he⟩ := h_arc (hc b)
  -- Pull objects and full structures back to the centre; there `y` is modelled on some `(g, ℓ)`.
  choose x h_pb using fun y' : ThetaObject U.family (Spec (CommRingCat.of V)) ↦
    exists_isPullbackAlong (X := U.family) (specMap (φ.comp (residue V))) y'
  have h_full (y' : ThetaObject U.family (Spec (CommRingCat.of V))) (e' : y'.FullLevelStructure) :
      ∃ f' : (x y').FullLevelStructure,
        f'.torsionPoint = (h_pb y').isGroupBaseChange.pullSection ∘ₗ e'.torsionPoint :=
    FullLevelStructure.exists_pullback (h_pb y') e'
  choose f hf using h_full
  -- The structure map of `x y` on `𝓞 E` is that of `R` followed by the embedding `Φ v₀` in `ℂ`.
  have h_struct (r : 𝓞 E) : (x y).baseHom r = Φ v₀ r.val := by
    calc (x y).baseHom r = algebraMap R ℂ (algebraMap (𝓞 E) R r) := by
          have h_base : y ≫ U.base.hom = α ≫ C.scheme.hom := by simp [← c.w, reassoc_of% he]
          simp [baseHom, ← h_pb y, reassoc_of% h_centre, reassoc_of% h_base]
      -- The embedding of `R` in `ℂ` is `Φ v₀` by definition.
      _ = Φ v₀ r.val := rfl
  obtain ⟨g, ℓ, d, Y, m, hm, h_refl⟩ := exists_torusModel (f y e.fullStructure) h_struct
  have h_onto : m.π.Surjective := m.uniformisation.surjective.comp Y.realEquiv.surjective
  have h_lift (w : RealVectors E D.Index) :
      ∃ P' : RealVectors E D.Index, m.π P' = (h_pb y).isGroupBaseChange.pullSection (e.π w) :=
    h_onto _
  choose P hP using h_lift
  -- The candidate is `(g, ℓ, P ∘ b.markedPoint)`; compare it with `t` on each component `i`.
  refine ⟨{ frame := g, reflection := ℓ, markedPoint := P ∘ b.markedPoint,
            isSignedFrame := ⟨_, Y.isSignedFrameFor⟩, isReflection := h_refl },
    C.hom_ext fun i ↦ ?_⟩
  -- `(γ i).2` is a frame for a positive scalar `μ`, an integer since `(γ i).2⁻¹` is integral.
  obtain ⟨⟨c₀, h_pos, h_frame⟩, h_inv_int⟩ :
      (γ i).2.val ∈ GU E D.Index ∧ ∀ k l : D.Index, (γ i).2.val⁻¹ k l ∈ Ô E :=
    (γ i).2.prop
  obtain ⟨μ, rfl⟩ := h_frame.exists_intCast_eq (γ i).2.prop
  lift μ to ℕ using mod_cast h_pos.le
  -- Along the arc an isogeny `χ` inducing `(γ i).2⁻¹` on torsion maps `y` to the component `y'`.
  -- Its pull-back `ψ` comes from a rational matrix `z` between the models.
  obtain @⟨y', V_y', h_V_y', Y_y', e', he'⟩ := h_arc (C.point_comp_proj b i)
  have h_refl_b : ratConj (1 : GL D.Index E) b.reflection = (b.act (γ i).2).reflection := by
    simp [ratConj, act]
  have h_level : (b.act (γ i).2).frame⁻¹ * toFinGL 1 * b.frame = (γ i).2.val⁻¹ := by simp [act]
  have h_scalar : IsScalarFrame (γ i).2.val⁻¹⁻¹ μ := by simpa using And.intro h_pos h_frame
  obtain ⟨hρ, χ, hχ_isog, hχ_lin, h_cls, h_tor, hχ⟩ :=
    exists_isogeny (μ := μ) 1 h_refl_b e e' h_level h_inv_int h_scalar
  obtain ⟨ψ, hψ_pt, hψ_lin, hψ_sec⟩ :=
    (h_pb y).isGroupBaseChange.exists_hom_baseChange (h_pb y').isGroupBaseChange (𝟙 _) χ
  have h_struct' (r : 𝓞 E) : (x y').baseHom r = Φ v₀ r.val := by
    simp [(h_pb _).baseHom_eq_comp, hρ, ← m.baseHom_eq]
  obtain ⟨g', ℓ', d', Y', m', hm', h_refl'⟩ := exists_torusModel (f y' e'.fullStructure) h_struct'
  have hψ_cls : (x y').lineBundle.picClass.pull ψ.left = μ • (x y).lineBundle.picClass := by
    -- `using!`: the point of `ψ` over the centre is its pull-back only after unfolding
    -- `pointEquiv`.
    simpa [(h_pb _).lineBundle_eq_pull] using!
      congr(y'.lineBundle.picClass.pull $(hψ_pt (𝟙 _)).1).trans congr(($h_cls).pull _)
  obtain ⟨z, hz_π, -, hz_ℓ⟩ := exists_matrix_of_hom m m' ψ (mod_cast h_pos.ne') hψ_cls
  -- Both descriptions of `ψ` on torsion agree, and torsion determines an adelic matrix.
  have h_matrix : (γ i).2.val⁻¹ = g'⁻¹ * toFinGL z * g := by
    refine eq_of_forall_torsionClass_mulVec_eq fun w ↦ m'.fullStructure.injective ?_
    refine .trans ?_ (torsionPoint_comp _ _ hz_π w)
    simp [hm, hm', hf, h_tor, hψ_sec]
  -- The component `i` of `t` is the point with frame `g'`, reflection `ℓ'` and the images under `z`
  -- of the marked vectors `P ∘ b.markedPoint`. By `z` it is isomorphic to the translate of our
  -- candidate by `(γ i).2`.
  have h_pt :
      U.family.IsPointOf (γ i).1
        ⟨g', ℓ', fun j ↦ realVecAction z (P (b.markedPoint j)), ⟨_, Y'.isSignedFrameFor⟩, h_refl'⟩
        (t ≫ ReducedClosure.proj C i).left := by
    refine ⟨m', ?_⟩
    rw [comp_left, ← reassoc_of% h_centre, he']
    -- `↓`: `hz_π` must rewrite before the other lemmas
    simp [fibrePower_ext_iff, ← (h_pb _).comp_toFamily, ↓← hz_π, pullSection_comp_assoc, act,
      hm', hf, hP, hψ_sec, hχ, h_pb]
  refine (C.point_comp_proj _ i).trans (ext ((isPointOf_datumPoint.eq_iff h_pt).mpr ⟨z, ?_⟩))
  exact isLevelIso_act_of_inv_eq _ h_matrix hz_ℓ fun j ↦ rfl

end UniversalFamily.GraphClosure

end New.Variety
