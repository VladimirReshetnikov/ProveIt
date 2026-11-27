import Lib.General.Geometry.GeometricPoints
import Lib.Shimura.ThetaGroup
import Lib.Shimura.ThetaNormality.NormalGeneration
import Lib.Shimura.Uniformisation.HolomorphicFamilies

/-!
# Uniformisations over an arc: theta coordinates, Weil pairing and extension of maps

Let `A` be an abelian scheme over an arc `O` (`New.ValuativeArc`, a valuation ring with fraction
field `ℂ`). Let `u : V / Λ ≅ A(O)` be a uniformisation (`New.Uniformisation`) with `Λ = u.lattice`,
and let `L` be a linear system whose coordinates are theta functions (`New.HasThetaCoords`).
Sections of `L` are read as functions on `V`. Lifts of translations then act by twisted
translations, and their commutators are given by the Weil pairing. With these tools, an additive map
`s' : V → A'(O)` that kills `Λ` and has theta coordinates is shown to come from a morphism `A ⟶ A'`
over `O`, not only over `ℂ`.

## Main definitions and results

* `New.Variety.isSeparatingFamily_atGeneric_of_surjective`: the complex points `New.atGeneric` of
  the sections are dense in `A`.
* `New.Variety.thetaEval`, `New.Variety.exists_theta_evaluation`: `H⁰(L)` embeds in the
  functions on `V`, and lifts of translations (`New.Variety.IsTranslationLift`) act by multiples
  of the twisted translations `New.RealComplexForm.thetaShift`.
* `New.Variety.lift_commutator_iff_weil_pairing`: the commutator of two lifts is given by the
  Riemann phase `New.RealComplexForm.riemannPhase`.
* `New.Variety.exists_sections_of_translation_stable`: one scalar puts a finite family of theta
  functions in a stable `O`-module. No orbit of the dual lattice consists only of common zeros.
* `New.Variety.exists_section_of_hasThetaCoords`: a section of `π : A' ⟶ A` through the points
  `s' z`.
* `New.Variety.exists_hom_of_hasThetaCoords`: a homomorphism `A ⟶ A'`, obtained from its graph in
  `A × A'`.

Notions from other files:
* `New.IsAbelianScheme`: a commutative group scheme A over S is abelian if it is smooth and proper
  over S and multiplication by every m ≠ 0 is surjective.
* `New.LineBundle.H0`: The R-module of global sections of L, for a scheme X over R; a section `r`
  has a component `r.val i` (a `New.PointFn`) in each chart `i`.
* `New.IsPosRiemann`: The Riemann form E of B is positive: E(u, iu) > 0 for every u ≠ 0.
* `New.Variety.IsTranslationLift`: The R-linear endomorphism Φ of H⁰(L) is pull-back along the
  translation t_z by the section z followed by some isomorphism t_z^*L ≅ L.

## Relation to the literature

Known result: Homomorphisms and line bundles of abelian schemes extend from the generic fibre. Here
only maps of complex tori that multiply a theta polarisation by an integer are treated, where the
kernel of the polarisation is killed by a unit of the ring, over any valuation ring of the complex
numbers (not noetherian, any rank). The map and the identity of line bundle classes extend together,
and points extend by properness. Source: S. Bosch, W. Lütkebohmert, M. Raynaud, Néron Models (1990),
1.2/8 and 4.4/1; G. Faltings, C.-L. Chai, Degeneration of Abelian Varieties (1990), I.2.7; L.
Moret-Bailly, Pinceaux de variétés abéliennes, Astérisque 129 (1985), II.3.5.

See also `Lib.Shimura.IntegralModel.UniversalFamily` and `Lib.Shimura.Uniformisation.AppellHumbert`.
-/

namespace New.Variety

section SectionComponents

open CategoryTheory AlgebraicGeometry

variable {X : Scheme.{0}} {ι : Type} {L : LineBundle X ι} {R : Type} [CommRing R]
  [X.Over (Spec ⟨R⟩)]

private lemma _root_.New.LineBundle.H0.isSection_val (r : L.H0 R) : L.IsSection r.val :=
  r.prop.left

private lemma _root_.New.LineBundle.H0.isRegularOn_val (r : L.H0 R) (i : ι) :
    (r.val i).IsRegularOn (L.opens i) :=
  (LineBundle.H0.isSection_val r).left i

/-- At a point that lands in the charts `i` and `j`, the components of a global section `r`
differ by the transition function: `r i = g_ij · r j`. -/
private lemma _root_.New.LineBundle.H0.val_eq_transition_mul (r : L.H0 R) (i j : ι)
    (A : CommRingCat) (t : Spec A ⟶ X) (hi : LandsIn t (L.opens i)) (hj : LandsIn t (L.opens j)) :
    r.val i A t = L.transition i j A t * r.val j A t :=
  (LineBundle.H0.isSection_val r).right i j A t hi hj

/-- A component `r.val i` of a global section vanishes at the points outside the chart `i`. -/
private lemma _root_.New.LineBundle.H0.val_eq_zero_of_not_landsIn (r : L.H0 R) (i : ι)
    (A : CommRingCat) (t : Spec A ⟶ X) (h_out : ¬LandsIn t (L.opens i)) : r.val i A t = 0 :=
  r.prop.right i A t h_out

/-- A frame of `L` is a unit at every point that lands in the chart `i`. -/
private lemma _root_.New.LineBundle.IsFrame.isUnit_apply {s : ι → PointFn X} (hs : L.IsFrame s)
    (i : ι) (A : CommRingCat) (t : Spec A ⟶ X) (ht : LandsIn t (L.opens i)) : IsUnit (s i A t) :=
  hs.right i A t ht

end SectionComponents

/-! ## Sections along a uniformisation as theta functions -/

section ComplexComparison

open CategoryTheory AlgebraicGeometry Over ValuativeArc Function IsSchemeTheoreticallyDominant

variable {V ι κ : Type} [FinComplexSpace V]
  {O : Type} [CommRing O] [ValuativeArc O] {A : Over (Spec ⟨O⟩)}

/-- Let A be a smooth proper scheme over a valuation ring O with fraction field ℂ, and let
s : Z → (sections of A over O) be surjective. Then A is reduced and the complex points
`atGeneric s z` (the sections restricted to the generic point `Spec ℂ` of `Spec O`) are dense in
A. -/
lemma isSeparatingFamily_atGeneric_of_surjective [Smooth A.hom] [IsProper A.hom] {Z : Type}
    {s : Z → (MonoidalCategoryStruct.tensorUnit (Over (Spec (CommRingCat.of O))) ⟶ A)}
    (hs_surj : Function.Surjective s) :
    IsSeparatingFamily (atGeneric s) := by
  -- `A` is reduced because its generic fibre is reduced and scheme-theoretically dominant
  refine ⟨isReduced (Limits.pullback.fst A.hom genericPt), ?_⟩
  -- the generic point is dense in `Spec O`; `Spec ℂ` has a single point
  have h_dense :
      IsDenseFamily fun _ : Spec (.of ℂ) ↦ (genericPt : Spec (.of ℂ) ⟶ Spec (.of O)) := by
    -- `convert`: the two sides differ only in the point of the one-point space `Spec ℂ`
    convert (ValuativeArc.genericPt (O := O)).denseRange
    exact congrArg _ (by subsingleton)
  refine h_dense.of_fibres A.hom fun _ y hy ↦ ?_
  -- by the valuative criterion every complex point over `genericPt` comes from a section
  obtain ⟨z, hz⟩ := bijective_restrict_genericPt.surjective.comp hs_surj (homMk y hy)
  exact ⟨z, congrArg (fun g ↦ g.left) hz⟩

/-- If the linear system `L` is an embedding and has theta functions as coordinates along `s`, the
family of complex points of `s` is holomorphic. -/
lemma _root_.New.HasThetaCoords.holomorphicAt [Finite κ] {Λ : Submodule ℤ V}
    {s : V → (MonoidalCategoryStruct.tensorUnit (Over (Spec (CommRingCat.of O))) ⟶ A)}
    {L : LineBundle A.left κ} {B : ThetaTori.LatticeForm Λ} {χ : V → ℂ} {θ : V → κ → ℂ}
    (h : HasThetaCoords (ι := κ) (P := V) Λ (atGeneric s) L B χ θ) (hL : L.IsProjEmbedding A.hom)
    (z : V) :
    HolomorphicAt (atGeneric s) z := by
  -- the homogeneous coordinates `θ` of the points are entire functions
  refine .of_isHomogeneousCoords hL (fun i ↦ ?_) (.of_forall h.hasFieldCoords) fun _ ↦ Over.w _
  exact analyticAt_of_eventually_differentiableAt (.of_forall (h.mem_thetaSpace i).1)

section ThetaEval

variable {L : LineBundle A.left κ} {χ : V → ℂ} {θ : V → κ → ℂ} {Λ : Submodule ℤ V}
  {s : V → (MonoidalCategoryStruct.tensorUnit (Over (Spec (CommRingCat.of O))) ⟶ A)}
  {B : ThetaTori.LatticeForm Λ}

/-- For theta coordinates `θ` of `L` along `s`, a chart in which `θ z` does not vanish. -/
private noncomputable def thetaChart (h : HasThetaCoords Λ (atGeneric s) L B χ θ) (z : V) : κ :=
  (h.hasFieldCoords z).exists_ne_zero.choose

/-- The theta function `θ z` does not vanish in the chart `thetaChart h z`. -/
private lemma apply_thetaChart_ne_zero (h : HasThetaCoords Λ (atGeneric s) L B χ θ) (z : V) :
    θ z (thetaChart h z) ≠ 0 :=
  (h.hasFieldCoords z).exists_ne_zero.choose_spec

/-- Sections of `L` read as functions on `V`, for theta coordinates `θ` of `L` along `s`: a
section `r` goes to `z ↦ θ z i * r_i (s z)` for a chart `i` with `θ z i ≠ 0`. The value does not
depend on the chart (`New.Variety.thetaEval_eq_iff`). -/
noncomputable def thetaEval (h : HasThetaCoords Λ (atGeneric s) L B χ θ) : L.H0 O →ₗ[O] V → ℂ :=
  .pi fun z ↦ θ z (thetaChart h z) •
    { toFun r := r.val (thetaChart h z) (CommRingCat.of ℂ) (atGeneric s z)
      map_add' := by simp
      map_smul' := by simp [H0_smul, atGeneric, ValuativeArc.genericPt_eq, Algebra.smul_def] }

/-- `thetaEval h r` is the function `g` exactly when `r_i = g / θ_i` at each point `s z`, in each
chart `i` with `θ z i ≠ 0`. -/
lemma thetaEval_eq_iff (h : HasThetaCoords Λ (atGeneric s) L B χ θ) (r : L.H0 O) (g : V → ℂ) :
    thetaEval h r = g ↔ ∀ (i : κ) (z : V),
      θ z i ≠ 0 → r.val i (CommRingCat.of ℂ) (atGeneric s z) = g z / θ z i := by
  -- the chart does not matter: `θ z i * r i = θ z j * r j` if `θ z i` and `θ z j` are not zero
  constructor
  · rintro rfl i z hi
    simp [thetaEval, LineBundle.H0.val_eq_transition_mul r i (thetaChart h z),
      h.hasFieldCoords .., field, apply_thetaChart_ne_zero h, hi]
  · -- at each `z` the value of `thetaEval h r` is read in the chart `thetaChart h z`
    intro h_val
    funext z
    simp [thetaEval, h_val _ z (apply_thetaChart_ne_zero h z), mul_div_cancel₀,
      apply_thetaChart_ne_zero h]

/-- `thetaEval h` sends the coordinate sections to the theta functions. -/
lemma thetaEval_coordSection (h : HasThetaCoords Λ (atGeneric s) L B χ θ) (i : κ) :
    thetaEval h (coordSection h.isLinearSystem i) = fun z : V ↦ θ z i := by
  simp +contextual [thetaEval_eq_iff, coordSection, h.hasFieldCoords .., field]

end ThetaEval

variable [IsAbelianScheme A]
  {L : LineBundle A.left κ} (u : Uniformisation A V) {B : ThetaTori.LatticeForm u.lattice}
  {χ : V → ℂ} {θ : V → κ → ℂ} (h : HasThetaCoords u.lattice (atGeneric u.expMap) L B χ θ)

/-- Along a uniformisation, `thetaEval h` is injective: the points `atGeneric u.expMap z` are
dense, so sections that agree there are equal. -/
lemma thetaEval_injective (h : HasThetaCoords u.lattice (atGeneric u.expMap) L B χ θ) :
    Function.Injective (thetaEval h) := by
  intro r r' hr
  -- in each chart `i` with `θ z i ≠ 0`, a section `s` has the value `thetaEval h s z / θ z i`
  have h_val (s : L.H0 O) : ∀ (i : κ) (z : V), θ z i ≠ 0 →
      s.val i (CommRingCat.of ℂ) (atGeneric u.expMap z) = thetaEval h s z / θ z i :=
    (thetaEval_eq_iff h s (thetaEval h s)).mp rfl
  refine H0_ext fun hi hi' ↦ (isSeparatingFamily_atGeneric_of_surjective u.surjective).pointFn_ext
    hi hi' ?_
  simp +contextual [h.hasFieldCoords .., h_val, hr]

/-- Along a uniformisation, a lift `Φ` of the translation by `u.expMap a` acts through
`thetaEval h` as a multiple of the shift `B.thetaShift a`. -/
lemma exists_thetaEval_eq_smul_thetaShift
    (h : HasThetaCoords u.lattice (atGeneric u.expMap) L B χ θ)
    (a : V) (Φ : Module.End O ↥(L.H0 O)) (hΦ : IsTranslationLift L (u.expMap a) Φ) :
    ∃ c : ℂ, ∀ r : ↥(L.H0 O), thetaEval h (Φ r) = c • B.thetaShift a (thetaEval h r) := by
  -- the frame `w` compares the coordinates `θ` of `L` with the shifted ones of its translate:
  -- by `riemannForm_eq_of_isFrame` it is a constant `c` times their quotient and an exponential
  -- factor, the one in `thetaShift`
  obtain ⟨w, hw, h_pull⟩ := hΦ
  obtain ⟨-, -, c, hc⟩ := h.riemannForm_eq_of_isFrame (h.pull_translate (u.atGeneric_add a)) hw
    u.holomorphicAt u.atGeneric_add_of_mem
  refine ⟨c, fun r ↦ (thetaEval_eq_iff h _ _).mpr fun i z hi ↦ ?_⟩
  simp [h_pull _ _ (thetaChart h (z + a)), hc, apply_thetaChart_ne_zero h, hi, ← u.atGeneric_add,
    thetaShift_apply, h.hasFieldCoords .., thetaEval, field]

/-- Let L have theta coordinates θ_i along s for a lattice Λ. Then r ↦ θ_i·r_i
(`New.Variety.thetaEval`) is an O-linear map from H⁰(L) to functions on V that sends the
coordinates to the θ_i. If Λ and s are the lattice and exponential map of a uniformisation, this
map is injective and sends lifts of translations to scalar multiples of
`New.RealComplexForm.thetaShift`. -/
lemma exists_theta_evaluation {Λ : Submodule ℤ V}
    {s : V → (MonoidalCategoryStruct.tensorUnit (Over (Spec (CommRingCat.of O))) ⟶ A)}
    {B : ThetaTori.LatticeForm Λ} (h : HasThetaCoords Λ (atGeneric s) L B χ θ) :
    ∃ T : L.H0 O →ₗ[O] V → ℂ,
      -- (a) `T r` is the function `g` with `r i = g / θ i` along the family
      (∀ (r : L.H0 O) (g : V → ℂ),
        T r = g ↔
          ∀ (i : κ) (z : V), θ z i ≠ 0 → r.val i (CommRingCat.of ℂ) (atGeneric s z) = g z / θ z i) ∧
      -- (b) the coordinates go to the theta functions
      (∀ i : κ, T (coordSection h.isLinearSystem i) = fun z : V ↦ θ z i) ∧
      -- (c) along a uniformisation `T` is injective and turns lifts of translations into multiples
      -- of shifts
      ∀ u : Uniformisation A V, Λ = u.lattice → s = u.expMap →
        Function.Injective T ∧
        ∀ (a : V) (Φ : Module.End O ↥(L.H0 O)),
          IsTranslationLift L (s a) Φ →
          ∃ c : ℂ, ∀ r : ↥(L.H0 O), T (Φ r) = c • B.thetaShift a (T r) := by
  refine ⟨thetaEval h, thetaEval_eq_iff h, thetaEval_coordSection h, ?_⟩
  rintro u rfl rfl
  exact ⟨thetaEval_injective u h, exists_thetaEval_eq_smul_thetaShift u h⟩

include h

/-- Weil pairing: let L have theta coordinates for B, and let Φ, Ψ lift to L^m the translations
by the images of a, b. Then ΦΨ = c·ΨΦ on all coordinates if and only if
c = exp(2πi m E(a,b)), E the Riemann form of B. -/
lemma lift_commutator_iff_weil_pairing {m : ℕ} {a b : V} {c : O}
    {Φ Ψ : Module.End O ↥((L.pow m).H0 O)}
    (hΦ : IsTranslationLift (L.pow m) (u.expMap a) Φ)
    (hΨ : IsTranslationLift (L.pow m) (u.expMap b) Ψ) :
    (∀ (l : (L.pow m).IsLinearSystem) (i : Fin m → κ),
        Φ (Ψ (coordSection l i)) = c • Ψ (Φ (coordSection l i))) ↔
      algebraMap O ℂ c = (m • B).riemannPhase a b := by
  -- Under the embedding `T` of sections into functions, `Φ` and `Ψ` act as multiples of the shifts
  -- by `a` and `b`, which commute up to the factor given by the Riemann form.
  let T : (L.pow m).H0 O →ₗ[O] V → ℂ := thetaEval (h.pow m)
  have hT_inj : Function.Injective T := thetaEval_injective u (h.pow m)
  obtain ⟨α, hα⟩ : ∃ α : ℂ, ∀ s : (L.pow m).H0 O, T (Φ s) = α • (m • B).thetaShift a (T s) :=
    exists_thetaEval_eq_smul_thetaShift u (h.pow m) a Φ hΦ
  obtain ⟨β, hβ⟩ : ∃ β : ℂ, ∀ s : (L.pow m).H0 O, T (Ψ s) = β • (m • B).thetaShift b (T s) :=
    exists_thetaEval_eq_smul_thetaShift u (h.pow m) b Ψ hΨ
  have h_comm_T (s : (L.pow m).H0 O) : T (Φ (Ψ s)) = (m • B).riemannPhase a b • T (Ψ (Φ s)) := by
    simp [T, hα, hβ, (h.pow m).isAppellHumbert.thetaShift_comm a, funext_iff, field]
  constructor
  · intro h_comm
    -- compare the two factors on a coordinate `i` whose theta function does not vanish at `0`
    obtain ⟨i, hi⟩ := ((h.pow m).hasFieldCoords 0).exists_ne_zero
    set x : (L.pow m).H0 O := coordSection (h.pow m).isLinearSystem i
    have hx : T x ≠ 0 := (thetaEval_coordSection (h.pow m) i).trans_ne (ne_iff.mpr ⟨0, hi⟩)
    have h_ne : T (Ψ (Φ x)) ≠ 0 := by
      simpa [map_eq_zero_iff, hT_inj, hΨ.injective, hΦ.injective] using ne_zero_of_map hx
    have h_eq : algebraMap O ℂ c • T (Ψ (Φ x)) = T (Φ (Ψ x)) := by simp [x, h_comm]
    exact smul_left_injective ℂ h_ne (h_eq.trans (h_comm_T _))
  · -- if `c` is the Riemann phase, both sides agree after the injective `T`
    intro hc
    simp [← hT_inj.eq_iff, h_comm_T, ← hc]

/-- Let `L` have theta coordinates `θ` of type `(B, χ)` along `u`, `B` be positive, `n` a unit of
`O`, and `N` an `O`-module of sections of `L` containing the coordinate sections. Suppose that each
`a` in the dual lattice `B.dualLattice` has `n • a ∈ u.lattice` (`h_torsion`), and that the
translation by `a` has a lift that preserves `N` (`h_lift`). For finitely many theta functions `f_j`
(elements of `B.thetaSpace χ`, the space that also holds each coordinate `θ_k`) of type `(B, χ)`
with `f_i ≠ 0` there are `γ ≠ 0` and sections `r_j ∈ N` such that: (a) the `k`-th component of `r_j`
at the point `u.expMap z` is `γ f_j(z)/θ_k(z)` whenever `θ_k(z) ≠ 0`; (b) for every field-valued
point `t`, some component of some `r_j` is nonzero at some translate of `t` by `B.dualLattice`. -/
lemma exists_sections_of_translation_stable [Finite κ] [IsPosRiemann B] {n : ℕ}
    (hn : IsUnit (n : O)) {N : Submodule O (L.H0 O)}
    (h_torsion : ∀ a ∈ B.dualLattice, n • a ∈ u.lattice)
    (h_lift : ∀ a ∈ B.dualLattice,
      ∃ Φ : Module.End O ↥(L.H0 O), IsTranslationLift L (u.expMap a) Φ ∧ N ≤ N.comap Φ)
    (hN : ∀ k : κ, coordSection h.isLinearSystem k ∈ N) {f : ι → V → ℂ} [Finite ι]
    (hf : ∀ j : ι, f j ∈ B.thetaSpace χ) (i : ι) (hf_ne : f i ≠ 0) :
    ∃ γ ≠ (0 : CommRingCat.of ℂ), ∃ r : ι → N,
      -- (a)
      (∀ (j : ι) (k : κ) (z : V), θ z k ≠ 0 →
        (r j : L.H0 O).val k (CommRingCat.of ℂ) (atGeneric u.expMap z) = γ * f j z / θ z k) ∧
      -- (b)
      ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ A.left),
        ∃ a ∈ B.dualLattice, ∃ (j : ι) (k : κ),
          (r j : L.H0 O).val k ⟨K⟩ (t ≫ (translation (u.expMap a)).left) ≠ 0 := by
  -- Read sections as theta functions through `T`. By
  -- `IsAppellHumbert.exists_proportional_orbit_lattice` there is `γ` such that a module of sections
  -- stable under the lifts `Φ a` holds the coordinates iff it holds all `γ • f j`.
  -- Apply this to `N`, and to the sections that vanish on an orbit.
  let T : L.H0 O →ₗ[O] V → ℂ := thetaEval h
  have hT_iff (r : L.H0 O) (g : V → ℂ) : T r = g ↔ ∀ (k : κ) (z : V), θ z k ≠ 0 →
      r.val k (CommRingCat.of ℂ) (atGeneric u.expMap z) = g z / θ z k := thetaEval_eq_iff h r g
  have hT_coord (k : κ) : T (coordSection h.isLinearSystem k) = fun z : V ↦ θ z k :=
    thetaEval_coordSection h k
  have hT_inj : Function.Injective T := thetaEval_injective u h
  choose! Φ hΦ hΦN using h_lift
  -- each lift `Φ a` acts through `T` as a multiple `c a` of the shift
  have h_shift (a : V) (ha : a ∈ B.dualLattice) :
      ∃ c : ℂ, ∀ r : L.H0 O, T (Φ a r) = c • B.thetaShift a (T r) :=
    exists_thetaEval_eq_smul_thetaShift u h a (Φ a) (hΦ a ha)
  choose! c hc using h_shift
  -- A chart `p` that contains the section `u.expMap 0`.
  obtain ⟨p, hp_in⟩ := L.exists_landsIn (u.expMap 0).left
  have hθ : θ 0 p ≠ 0 := ((h.hasFieldCoords ..).1.1 (hp_in.comp _)).ne_zero
  have hc_unit (a : V) (ha : a ∈ B.dualLattice) : ∃ d : Oˣ, algebraMap O ℂ d = c a * c (-a) := by
    -- `Φ a * Φ (-a)` lifts the identity, so it multiplies by a frame `w`, whose value at the
    -- section `u.expMap 0` is a unit of `O`.
    obtain ⟨w, hw, h_mul⟩ := (hΦ a ha).mul (hΦ _ (neg_mem ha))
    refine ⟨(hw.isUnit_apply (p, p) _ (u.expMap 0).left (by simpa using hp_in)).unit, ?_⟩
    -- evaluate `Φ a (Φ (-a) x)`, for the coordinate `x` of the chart `p`, by `h_mul` and by `hc`
    let x : L.H0 O := coordSection h.isLinearSystem p
    have h_read : (Φ a (Φ (-a) x)).val p (CommRingCat.of ℂ) (atGeneric u.expMap 0) =
        T (Φ a (Φ (-a) x)) 0 / θ 0 p := (hT_iff _ _).mp rfl p 0 hθ
    have h_in : LandsIn (atGeneric u.expMap 0) (L.opens p) := hp_in.comp _
    have h_frame := h_mul x p p (CommRingCat.of ℂ) (atGeneric u.expMap 0) h_in
      (by simpa [← map_add] using h_in)
    -- `↓` (use before the subterms are simplified): without it the goal does not close
    simpa [x, ↓hT_coord, ↓hc, *, h.isAppellHumbert.thetaShift_thetaShift, coordSection, field,
      hw.1.1 _ _, L.transition_self, hp_in.comp, ValuativeArc.genericPt_eq, atGeneric,
      -map_zero] using h_frame.symm.trans h_read
  have h_coord_theta (k : κ) : (fun z : V ↦ θ z k) ∈ B.thetaSpace χ := h.mem_thetaSpace k
  have hp_ne : (⟨_, h_coord_theta p⟩ : B.thetaSpace χ) ≠ 0 := fun h0 ↦
    hθ (congrFun (congrArg Subtype.val h0) 0)
  obtain ⟨γ, hγ, h_scale⟩ := h.isAppellHumbert.exists_proportional_orbit_lattice
    (fun j ↦ ⟨f j, hf j⟩) (fun k ↦ ⟨_, h_coord_theta k⟩) i p c hn h_torsion (by simpa) hp_ne hc_unit
  have h_iff (M : Submodule O (L.H0 O)) (hM : ∀ a ∈ B.dualLattice, ∀ r ∈ M, Φ a r ∈ M) :
      (∀ k : κ, coordSection h.isLinearSystem k ∈ M) ↔
        ∀ j : ι, ∃ r ∈ M, ∀ (i : κ) (z : V), θ z i ≠ 0 →
          r.val i (CommRingCat.of ℂ) (atGeneric u.expMap z) = γ * f j z / θ z i := by
    have h_stable (a : V) (ha : a ∈ B.dualLattice) :
        ∀ x ∈ M.map T, c a • B.thetaShift a x ∈ M.map T :=
      fun _ ⟨r, hr, hx⟩ ↦ ⟨_, hM a ha r hr, by rw [hc a ha, hx]⟩
    simpa [← hT_coord, hT_inj.eq_iff, hT_iff, -Subtype.exists] using h_scale _ h_stable
  choose r hrN hr using (h_iff N hΦN).mp hN
  refine ⟨γ, hγ, fun j ↦ ⟨r j, hrN j⟩, hr, fun K _ t ↦ ?_⟩
  by_contra! h_zero
  -- `Z`, the sections that vanish on the orbit of `t`, is stable under the `Φ a`.
  let Z : Submodule O (L.H0 O) :=
    { carrier := {s | ∀ a ∈ B.dualLattice, ∀ i : κ,
        s.val i (CommRingCat.of K) (t ≫ (translation (u.expMap a)).left) = 0}
      add_mem' := by simp +contextual
      zero_mem' := by simp
      smul_mem' := by simp +contextual [H0_smul] }
  have hZ (b : V) (hb : b ∈ B.dualLattice) (s : L.H0 O) (hs : s ∈ Z) : Φ b s ∈ Z := by
    intro a ha i
    by_cases h_in : LandsIn (t ≫ (translation (u.expMap a)).left) (L.opens i)
    · obtain ⟨w, -, h_mul⟩ := hΦ b hb
      rw [h_mul s i _ _ _ h_in (L.exists_landsIn _).choose_spec]
      refine mul_eq_zero_of_right _ ?_
      simpa [← comp_left, add_assoc, comp_add] using hs (a + b) (add_mem ha hb) _
    · exact LineBundle.H0.val_eq_zero_of_not_landsIn (Φ b s) i _ _ h_in
  -- If `Z` held all `r j`, it would hold the coordinates; but they do not all vanish at `t`.
  obtain ⟨k, hk⟩ := L.exists_landsIn t
  have h_coord : coordSection h.isLinearSystem k ∈ Z :=
    (h_iff Z hZ).mpr (fun j ↦ ⟨r j, fun a ha ↦ h_zero a ha j, hr j⟩) k
  simpa [coordSection, L.transition_self, hk] using h_coord 0 (by simp) k

end ComplexComparison

/-!
## Extension of linear maps to sections and homomorphisms over an arc

`New.HasThetaCoords` says that the coordinates of a linear system at the complex points
`New.atGeneric` are theta functions of type `(B, χ)`. Standing hypotheses: `N` has such coordinates
along `u.expMap`, and the Riemann form of `B` is positive (an instance `IsPosRiemann B`). Further,
`n` is a unit of `O`, and every `a` in the dual lattice of `B` has `n • a ∈ u.lattice`, and the
translation by `u.expMap a` lifts to `N`. Also `s'` kills `u.lattice`, `A'` is proper over `O`, and
`M` is a projective embedding of `A'`.
-/

section ArcExtension

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory Over Category LineBundle PointFn

variable {V ι κ O : Type} [FinComplexSpace V] [CommRing O] [ValuativeArc O]
  {A A' : Over (Spec ⟨O⟩)} [AddObj A']
  {s' : V →+ (MonoidalCategoryStruct.tensorUnit (Over (Spec (CommRingCat.of O))) ⟶ A')} [Finite κ]
  [IsAbelianScheme A] [Finite ι]
  (u : Uniformisation A V) {N : LineBundle A.left ι} {B : ThetaTori.LatticeForm u.lattice}
  {χ : V → ℂ} {θ : V → ι → ℂ}
  (h : HasThetaCoords u.lattice (atGeneric u.expMap) N B χ θ) [IsPosRiemann B]
  (hs' : ∀ l ∈ u.lattice, s' l = 0) {n : ℕ} (hn : IsUnit (n : O))
  (h_tors_lift : ∀ a ∈ B.dualLattice,
    n • a ∈ u.lattice ∧ ∃ Φ : Module.End O ↥(N.H0 O), IsTranslationLift N (u.expMap a) Φ)
  [IsProper A'.hom] {M : LineBundle A'.left κ} (hM : M.IsProjEmbedding A'.hom)

include h hs' hn h_tors_lift hM

omit h hs' hn hM [IsPosRiemann B] [Finite ι] in
/-- The lift of a translation by a point of the dual lattice preserves the module of all
sections. -/
private lemma exists_isTranslationLift_top_of_dualLattice :
    ∀ a ∈ B.dualLattice, ∃ Φ : Module.End O ↥(N.H0 O),
      IsTranslationLift N (u.expMap a) Φ ∧
        (⊤ : Submodule O (N.H0 O)) ≤ (⊤ : Submodule O (N.H0 O)).comap Φ :=
  fun a ha ↦ (h_tors_lift a ha).right.imp fun _ hΦ ↦ ⟨hΦ, le_top⟩

omit h hn h_tors_lift hM [IsProper A'.hom] in
/-- If `n • z₀` lies in the lattice `u.lattice`, which `s'` kills, then the translation of `A'` by
`s' z₀` followed by `ν`, multiplication by `n`, is `ν`. -/
private lemma translation_comp_eq_of_nsmul_mem {ν : A'.left ⟶ A'.left}
    (hν_def : (n • 𝟙 A').left = ν) {z₀ : V} (h_mem : n • z₀ ∈ u.lattice) :
    (translation (s' z₀)).left ≫ ν = ν := by
  simp [← hν_def, ← comp_nsmul _, ← map_nsmul, hs' _ h_mem, ← comp_left, comp_nsmul]

omit h hs' hn h_tors_lift hM [IsProper A'.hom] in
/-- The translation of `A'` by `s' z₀` moves the complex point `atGeneric s' x` to
`atGeneric s' (x + z₀)`. -/
private lemma atGeneric_comp_translation (x z₀ : V) :
    atGeneric s' x ≫ (translation (s' z₀)).left = atGeneric s' (x + z₀) := by
  simp [atGeneric, ← comp_left, comp_add]

omit h hs' hn h_tors_lift hM [IsProper A'.hom] in
/-- If the homomorphism `π : A' ⟶ A` sends `s' z` to `u.expMap z`, it carries the translation of
`A'` by `s' z₀` to the translation of `A` by `u.expMap z₀`. -/
private lemma comp_translation_eq_translation_comp (π : A' ⟶ A) [IsAdditive π]
    (h_lift : ∀ z : V, s' z ≫ π = u.expMap z) (z₀ : V) :
    π.left ≫ (translation (u.expMap z₀)).left = (translation (s' z₀)).left ≫ π.left := by
  simp [h_lift, ← comp_left, comp_add, add_comp]

/-- Assume the standing hypotheses from the section head (`h`, `IsPosRiemann B`, unit `n` with
`h_tors_lift`, `s'` killing `u.lattice`, `A'` proper, `hM`). Let `π : A' ⟶ A` be a homomorphism that
sends `s' z` to `u.expMap z`. Let the theta coordinates `f` of `M` along `s'` have the same type
`(B, χ)` as those of `N`. Let `ν^* π^* N ⊗ M ^ m` and `ν^* M ⊗ (π^* N) ^ m` have the same class,
where `ν` is multiplication by `n` on `A'` and `m = n ^ 2`. Then `π` has a section `e` that sends
`u.expMap z` to `s' z` and satisfies `[e^* M] = [N]`. -/
lemma exists_section_of_hasThetaCoords (π : A' ⟶ A) [IsAdditive π] {f : V → κ → ℂ}
    {ν : A'.left ⟶ A'.left} {m : ℕ} (hm : n ^ 2 = m) (h_lift : ∀ z : V, s' z ≫ π = u.expMap z)
    (hf : HasThetaCoords u.lattice (atGeneric s') M B χ f) (hν_def : (n • 𝟙 A').left = ν)
    (h_cls :
      (((N.pull π.left).pull ν).mul (M.pow m)).picClass =
        ((M.pull ν).mul ((N.pull π.left).pow m)).picClass) :
    ∃ e : A ⟶ A',
      -- (a) `e` extends the given points
      (∀ z : V, u.expMap z ≫ e = s' z) ∧
      -- (b) `e` pulls `M` back to `N`
      (M.pull e.left).picClass = N.picClass ∧
      -- (c) `e` is a section of `π`
      e ≫ π = 𝟙 A := by
  -- The coordinates `f` of `M`, scaled by `γ`, are sections `r j` of `N`. If they have no common
  -- zero, they define a linear system on `A` that agrees with `M` on the points of the
  -- uniformisation, hence a map `e`. Common zeros are excluded on the closure `Γ` of the `s' z`.
  have hν (z : V) : atGeneric s' ((n : V →L[ℂ] V) z) = atGeneric s' z ≫ ν := by
    simp [atGeneric, ← hν_def, comp_nsmul, ← comp_left]
  have hπ (z : V) : atGeneric u.expMap z = atGeneric s' z ≫ π.left := by simp [atGeneric, ← h_lift]
  -- `n` is a unit of the domain `O`, so `m = n ^ 2` is not `0`
  have hm0 : m ≠ 0 := hm.symm.trans_ne (pow_ne_zero 2 fun h0 ↦ by simp [h0] at hn)
  -- `w` is a frame of the quotient of the two bundles in `h_cls`: an isomorphism between them.
  obtain ⟨w, hw⟩ := picClass_eq_iff.mp h_cls
  obtain ⟨Γ, p, P, _, hP, hΓ⟩ : ∃ (Γ : Scheme) (p : Γ ⟶ A'.left) (P : V → (Spec (.of ℂ) ⟶ Γ)),
      IsClosedImmersion p ∧ (∀ z, P z ≫ p = atGeneric s' z) ∧ IsSeparatingFamily P :=
    exists_reduced_closure _
  have hA : IsSeparatingFamily (atGeneric u.expMap) :=
    isSeparatingFamily_atGeneric_of_surjective u.surjective
  -- `Γ → A` is proper and its image holds the dense points `atGeneric u.expMap z`
  have h_surj : AlgebraicGeometry.Surjective (p ≫ π.left) := hA.2.surjective _ P (by grind)
  -- a coordinate `i₀` of `M` whose theta function does not vanish at `0`
  obtain ⟨i₀, hi₀⟩ := (hf.hasFieldCoords 0).exists_ne_zero
  have hf_ne : (fun z : V ↦ f z i₀) ≠ 0 := ne_of_apply_ne (fun g ↦ g 0) hi₀
  -- Sections `r j` of `N` with value `γ * f z j / θ z i` at `u.expMap z` in chart `i` (`hr`), not
  -- all zero on the orbit of any field-valued point under the dual lattice (`h_orbit`).
  obtain ⟨γ, hγ, r, hr, h_orbit⟩ :=
    exists_sections_of_translation_stable (N := ⊤) u h hn (fun a ha ↦ (h_tors_lift a ha).left)
      (exists_isTranslationLift_top_of_dualLattice u h_tors_lift) (by simp) hf.mem_thetaSpace
      i₀ hf_ne
  -- Both sides of `h_cls` have theta coordinates along `s'`, so `w` at `s' z` is a constant `c`
  -- times their quotient `f (n • z) θ(z) ^ m / (θ (n • z) f(z) ^ m)` (`hw_val`).
  have hθ := h.pull 1 hπ fun _ ↦ id
  have hn_mem (l) (hl : l ∈ u.lattice) : (n : V →L[ℂ] V) l ∈ u.lattice := by
    simpa using nsmul_mem hl n
  obtain ⟨-, -, c, hw_val⟩ :=
    ((hθ.pull _ hν hn_mem).mul (hf.pow _)).riemannForm_eq_of_isFrame
      ((hf.pull _ hν hn_mem).mul (hθ.pow _)) hw (hf.holomorphicAt hM)
      fun l hl ↦ atGeneric_add_of_map_eq_zero s' (hs' l hl)
  have h_nonzero (i : ι) (K : Type) [Field K] (ζ : Spec (.of K) ⟶ Γ)
      (hi : LandsIn (ζ ≫ p ≫ π.left) (N.opens i)) :
      ∃ j : κ, (r j : N.H0 O).val i (.of K) (ζ ≫ p ≫ π.left) ≠ 0 := by
    -- If all `r j` vanish at `ζ`, they vanish on its orbit, which `h_orbit` forbids.
    by_contra h_zero
    obtain ⟨z₀, hz₀, j, a, h_ne⟩ := h_orbit K (ζ ≫ p ≫ π.left)
    refine h_ne ?_
    wlog ha : LandsIn ((ζ ≫ p ≫ π.left) ≫ (translation (u.expMap z₀)).left) (N.opens a)
    · exact LineBundle.H0.val_eq_zero_of_not_landsIn (r j : N.H0 O) a _ _ ha
    -- `T` is the translation by `s' z₀`; `T ≫ ν = ν` because `n • z₀` lies in the lattice.
    obtain ⟨h_tors, -⟩ := h_tors_lift z₀ hz₀
    let T : A'.left ⟶ A'.left := (translation (s' z₀)).left
    have hTν : T ≫ ν = ν := translation_comp_eq_of_nsmul_mem u hs' hν_def h_tors
    have hT (x : V) : atGeneric s' x ≫ T = atGeneric s' (x + z₀) := atGeneric_comp_translation x z₀
    have hTπ : π.left ≫ (translation (u.expMap z₀)).left = T ≫ π.left :=
      comp_translation_eq_translation_comp u π h_lift z₀
    let Q := M.mul (N.pull π.left)
    obtain ⟨⟨b, b₁, b', i'⟩, hb⟩ := (M.mul ((M.pull T).mul (Q.pull ν))).exists_landsIn (ζ ≫ p)
    have hr_reg (j : κ) := LineBundle.H0.isRegularOn_val (r j : N.H0 O)
    have hw_unit (x) := hw.isUnit_apply x (.of K)
    obtain ⟨h_lin, h_ah, h_mem, h_lifts⟩ := hf
    have hM_reg (i j : κ) : (M.transition i j).IsRegularOn (M.opens i) :=
      h_lin.isRegularOn_transition i j
    -- At `s' z` the function `φ b i j` is `(f j / f b) ^ m` times a factor that depends only on
    -- `n • z` modulo the lattice; this factor is invariant under `T`. This gives `key` at the
    -- points `P z`, hence on `Γ`.
    let φ (b : κ) (i : ι) (j : κ) : PointFn A'.left :=
      w ((i', fun _ ↦ b), b', fun _ ↦ i) * ((r j : N.H0 O).val i ^ m).pull π.left
    simp [IsHomogeneousCoords, hTπ, Q, IsFrame, IsSection, IsRegularOn, pow,
      landsIn_iInf] at hw hr_reg hM_reg hw_unit h_lifts h_zero ha hb
    have key : (φ b i b * (M.transition b₁ j ^ m).pull T).pull p _ ζ =
        (φ b₁ a j).pull (p ≫ T) _ ζ := by
      -- Both sides are regular on the open `U` of `Γ` and agree at the `P z` in it; `ζ` is in `U`.
      refine hΓ.pointFn_ext
        (U := p ⁻¹ᵁ (Q.opens (b, i) ⊓ T ⁻¹ᵁ Q.opens (b₁, a) ⊓ ν ⁻¹ᵁ Q.opens (b', i'))) ?_ ?_ ?_ _ ζ
        (by simp [Q, hi, ha, hb])
      · simp +contextual [Q, φ, hw, hr_reg, hM_reg, IsRegularOn]
      · simp +contextual [Q, φ, hw, hr_reg, hTν, reassoc_of% hTν, IsRegularOn]
      · simp +contextual [Q, φ, hw_val, hr, ← assoc, hP, hT, ← hν, h.hasFieldCoords .., h_lifts,
          ← hπ, (h.mem_thetaSpace _).2, (h_mem _).2, h_tors, h_ah.ne_zero,
          mul_pow, div_pow, field]
    -- At `ζ` the left side vanishes, and the right side is a unit times a power of `r j`.
    simpa [φ, hw_unit, h_zero, ha, hb, hi, hm0, hTπ, hTν, reassoc_of% hTν] using key
  -- The `r j` give a map `W` to projective space that pulls the hyperplane class back to `N`.
  obtain ⟨W, hW_cls, hW⟩ :=
    exists_picClass_eq_pull_hyperplane (p ≫ π.left)
      (fun j ↦ LineBundle.H0.isSection_val (r j : N.H0 O)) h_nonzero
  have h_lifts (z : V) :
      ((ProjSpace.hyperplaneBundle κ).pull W).IsHomogeneousCoords (atGeneric u.expMap z) (f z) := by
    obtain ⟨i, hi⟩ := (h.hasFieldCoords z).exists_ne_zero
    simpa [IsHomogeneousCoords, hr, hγ, hi, field] using hW i _ _
      ((h.hasFieldCoords ..).1.2 hi.isUnit)
  -- `u.expMap z` and `s' z` have the same coordinates `f z`, and `M` is an embedding.
  obtain ⟨e, he, heM⟩ :=
    hA.exists_map_of_coords (ProjSpace.isLinearSystem_hyperplaneBundle.pull W) hM h_lifts
      hf.hasFieldCoords
  exact ⟨e, fun z ↦ bijective_restrict_genericPt.injective (he z), by rw [heM, hW_cls],
    hA.hom_ext (by grind)⟩

/-- Let `u` uniformise the abelian scheme `A` over `O`, and let `N` be a projective embedding of `A`
with theta coordinates of type `(B, χ)` along `u`, where `B` is positive. Let `n` be a unit of `O`
such that each `a` in `B.dualLattice` has `n • a ∈ u.lattice` and translation by `u.expMap a` lifts
to sections of `N`. Let `s'` be a homomorphism from `V` to the sections of a commutative group `A'`
proper over `O` that kills `u.lattice`, and let `M` be a projective embedding of `A'` with theta
coordinates of type `(μ • B, χ ^ μ)` along `s'`. If the classes of `N` and `M` obey the
parallelogram law (`ParallelogramLaw`; through `pull_nsmul_eq_sq_smul`, pulling back along
multiplication by `d` then multiplies the class by `d ^ 2`), then there is a homomorphism
`ψ : A ⟶ A'` that (a) sends `u.expMap z` to `s' z` for all `z`, and (b) satisfies
`ψ^* [M] = μ • [N]`. -/
lemma exists_hom_of_hasThetaCoords (hN : N.IsProjEmbedding A.hom)
    (hN_par : N.picClass.ParallelogramLaw) (hM_par : M.picClass.ParallelogramLaw) {μ : ℕ}
    {θ' : V → κ → ℂ} (h' : HasThetaCoords u.lattice (atGeneric s') M (μ • B) (χ ^ μ) θ') :
    ∃ ψ : A ⟶ A',
      IsAdditive ψ ∧
      -- (a)
      (∀ z : V, u.expMap z ≫ ψ = s' z) ∧
      -- (b)
      M.picClass.pull ψ.left = μ • N.picClass := by
  -- Apply `exists_section_of_hasThetaCoords` to the projection `A × A' → A`, the points
  -- `S z = (u.expMap z, s' z)`, the bundle `N ^ (μ + k)` on `A` and the embedding `M ⊠ N ^ k`, both
  -- of type `(μ + k) • B`. The section it gives is the graph of `ψ`.
  -- `μ + 1` and `μ + 2` differ by `1`, so they are not both in the maximal ideal of `O`.
  obtain ⟨k, hk, hμk⟩ : ∃ k ≠ 0, IsUnit (↑(μ + k) : O) := by
    by_contra! h_none
    simpa [← one_add_one_eq_two] using
      (IsLocalRing.maximalIdeal O).sub_mem (h_none 2 nofun) (h_none 1 nofun)
  have : NeZero (μ + k) := ⟨by lia⟩
  let S := AddMonoidHom.mk' (fun z ↦ lift (u.expMap z) (s' z)) fun a b ↦ by
    ext1 <;> simp [add_comp]
  let Q := (M.pull (snd A A').1).mul ((N.pow k).pull (fst A A').1)
  have hQ : Q.IsProjEmbedding ((fst A A').1 ≫ A.hom) :=
    (hM.of_isPullback (.flip (.of_hasPullback ..))).mul (hN.pow hk)
  have hQ_theta : HasThetaCoords u.lattice (atGeneric S) Q ((μ + k) • B) (χ ^ (μ + k))
      fun z i ↦ θ' z i.1 * ∏ a, θ z (i.2 a) := by
    rw [add_smul, pow_add]
    exact (h'.pull 1 (by simp [atGeneric, S, ← comp_left, -snd_left, -lift_left]) fun _ ↦ id).mul
      ((h.pow k).pull 1 (by simp [atGeneric, S, ← comp_left, -fst_left, -lift_left]) fun _ ↦ id)
  have hS (l) (hl : l ∈ u.lattice) : S l = 0 := by
    ext1 <;> simp [S, hs' l hl, (u.eq_zero_iff l).1 hl]
  -- The dual lattice of `(μ + k) • B` is carried into the lattice by `(μ + k) * n`, and its
  -- translations lift to `N ^ (μ + k)`: apply `h_tors_lift` to `(μ + k) • a`.
  have h_dual : ∀ a ∈ RealComplexForm.dualLattice ((μ + k) • B),
      ((μ + k) * n) • a ∈ u.lattice ∧ ∃ Φ, IsTranslationLift (N.pow (μ + k)) (u.expMap a) Φ := by
    clear * - h_tors_lift hN_par
    simp_all [exists_isTranslationLift_iff, ThetaTori.mem_dualLattice_nsmul, mul_nsmul,
      hN_par.nsmul_pairing_eq_pairing_nsmul, ← comp_nsmul, ← map_nsmul]
  -- By `pull_nsmul_eq_sq_smul`, pulling back along multiplication by `d` multiplies the classes of
  -- `N` and `M` by `d ^ 2`.
  let N' := (N.pow (μ + k)).pull (fst A A').1
  let ν (d : ℕ) := (d • 𝟙 (MonoidalCategoryStruct.tensorObj A A')).left
  have h_cls (d : ℕ) :
      ((N'.pull (ν d)).mul (Q.pow (d ^ 2))).picClass =
        ((Q.pull (ν d)).mul (N'.pow (d ^ 2))).picClass := by
    have hN_sq := congrArg (·.pull (fst A A').1) (pull_nsmul_eq_sq_smul hN_par d)
    have hM_sq := congrArg (·.pull (snd A A').1) (pull_nsmul_eq_sq_smul hM_par d)
    linear_combination (norm := (simp [Q, N', ν, ← Pic.pull_picClass, ← Pic.pull_comp, ← comp_left,
      nsmul_comp, comp_nsmul, sub_eq_zero, -fst_left, -snd_left]; module)) μ • hN_sq - hM_sq
  obtain ⟨e, he, he_cls, he_fst⟩ :=
    exists_section_of_hasThetaCoords u (h.pow _) hS (mod_cast hμk.mul hn) h_dual hQ (fst ..) rfl
      (by simp [S]) hQ_theta rfl (h_cls _)
  have hψ (z) : u.expMap z ≫ e ≫ snd A A' = s' z := by simp [reassoc_of% he, S]
  refine ⟨e ≫ snd .., isAdditive_of_universal ?_, hψ, by simpa [Q, add_smul, he_fst,
    ← Pic.pull_picClass, ← Pic.pull_comp, ← comp_left, -snd_left, -fst_left] using he_cls⟩
  -- Additivity can be checked on the dense family of sections of `A × A`.
  have : Smooth (MonoidalCategoryStruct.tensorObj A A).hom := by
    rw [tensorObj_hom]
    infer_instance
  refine (isSeparatingFamily_atGeneric_of_surjective
      (homEquivToProd.symm.surjective.comp (u.surjective.prodMap u.surjective))).hom_ext ?_
  simp [reassoc_of% comp_add, ← comp_add _, ← map_add, reassoc_of% he, S, comp_add]

end ArcExtension

end New.Variety
