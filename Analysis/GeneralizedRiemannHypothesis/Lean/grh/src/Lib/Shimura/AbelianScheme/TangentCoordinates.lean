import Lib.General.Geometry.PointsOfProperSchemes

/-!
# Étale coordinates at zero, infinitesimal points and unramified torsion

Let A be a commutative group scheme over S with an action of a ring O. The file studies the tangent
space of A at 0 through coordinate functions evaluated at points that vanish modulo a square-zero
ideal.

## Main definitions and results

* `New.IsSqZeroExt`, `New.IsInfinitesimal`, `New.tangentCoords`: square-zero extensions ψ, points
  that vanish modulo ker ψ, and their coordinates z(y) − z(0).
* `New.IsEtaleChart`, `New.exists_isEtaleChart`: étale coordinates; they exist on a smooth scheme.
* `New.IsLieChart`, `New.exists_isLieChart`: coordinates at 0 that are additive on infinitesimal
  points and in which O acts by matrices.
* `New.HasSignature`, `New.HasSignature.of_points`: the rank-one signature condition for ρ, b, b' on
  these matrices passes from a jointly injective family of ring maps to every map φ into a local
  ring for which φ(ρ b − ρ b') is a unit.
* `New.Variety.eq_zero_of_nsmul_eq_zero_of_comp_eq_zero`: torsion of invertible order in an abelian
  scheme over a local ring is unramified. The ideal I cutting out the locus where the section
  vanishes satisfies I ≤ I² by
  `New.IsInfinitesimal.eq_zero_of_isUnit_and_nsmul_eq_zero_of_cast_eq_zero`, so I = 0 by Nakayama's
  lemma.

Notions from other files:
* `New.IsAbelianScheme`: a commutative group scheme A over S is abelian if it is smooth and proper
  over S and multiplication by every m ≠ 0 is surjective.

## Relation to the literature

Known; see `Lib.Shimura.AbelianScheme.IsogenyFlatness` and `Lib.Shimura.ThetaModuli.UniversalFamily`
for sources.
-/

noncomputable section

/-!
## Étale coordinates at 0, the Lie action and infinitesimal points

The tangent space at 0 of a commutative group scheme A over S, through coordinates. The coordinate
functions are sections over an open V. They are evaluated at ring-valued points through
`New.PointFn.ofSection`. `New.LandsIn t V` says that the point t lands in the open V, `AddObj A`
makes A a commutative group scheme over S (group structures on all Hom(T, A), functorial in T), and
`New.ModuleObj O A` is an action of the ring O on A (O-module structures on all groups Hom(T, A),
functorial in T).
-/

section TangentCoords

open CategoryTheory AlgebraicGeometry TrivSqZeroExt CommRingCat Spec Over Matrix IsLocalRing

namespace New

section Definitions

variable {S X : Scheme} {A : Over S} {ι O R M : Type} {B C C' D : CommRingCat} {V : A.left.Opens}
  (f : X ⟶ S) [AddObj A] {t : Spec C ⟶ S} {s : Spec B ⟶ S} (ψ : C ⟶ C') (z : ι → Γ(A.1, V))
  (y : Over.mk t ⟶ A) [CommRing O] [ModuleObj O A] [Fintype ι] [DecidableEq ι] [CommRing R]
  [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

/-! ### Square-zero extensions, charts and the conditions on the Lie action -/

/-- A point of X with values in a local ring B lands in some affine open of X. -/
lemma exists_isAffineOpen_landsIn [IsLocalRing B] (t : Spec B ⟶ X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ LandsIn t V := by
  simpa [landsIn_iff_mem] using
    exists_isAffineOpen_mem_and_subset (x := t (closedPoint B)) (U := ⊤) trivial

/-- The ring homomorphism ψ is surjective and its kernel has square zero. -/
class IsSqZeroExt (ψ : C ⟶ C') where
  /-- ψ is surjective. -/
  coe_surjective : Function.Surjective ψ
  /-- The product of two elements of ker ψ is zero. -/
  mul_eq_zero : ∀ {a b : C}, ψ a = 0 → ψ b = 0 → a * b = 0

/-- For ψ : C → C', the C-point y of the group scheme A becomes 0 in A(C'). -/
def IsInfinitesimal : Prop := (homMk (Spec.map ψ) : mk (Spec.map ψ ≫ t) ⟶ mk t) ≫ y = 0

/-- For a C-point y of A over t : Spec C → S and functions z_i on the open V, the entry
z_i(y) − z_i(0) in C; a function takes the value 0 at a point that does not land in V. -/
def tangentCoords (i : ι) : C :=
  PointFn.ofSection (z i) C y.1 - PointFn.ofSection (z i) C (0 : mk t ⟶ A).1

/-- The z_i are regular on V and étale coordinates for f: along square-zero extensions C → C',
points in V lift uniquely over S with any prescribed lifts of the values z_i. -/
def IsEtaleChart (V : X.Opens) (z : ι → Γ(X, V)) : Prop :=
  ∀ ⦃C D : CommRingCat⦄ ⦃ψ : C ⟶ D⦄ [IsSqZeroExt ψ] ⦃t : Spec C ⟶ S⦄ (x : Spec D ⟶ X) (l : ι → C),
    LandsIn x V → x ≫ f = Spec.map ψ ≫ t →
    ψ ∘ l = (fun s ↦ PointFn.ofSection s D x) ∘ z →
    ∃! y : mk t ⟶ mk f, Spec.map ψ ≫ y.1 = x ∧ (fun s ↦ PointFn.ofSection s C y.1) ∘ z = l

variable (R M) in
/-- The morphism Spec R → Spec(R ⊕ M) induced by the projection of the trivial square-zero
extension R ⊕ M onto R. -/
abbrev Variety.sqZeroReduction :
    Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (TrivSqZeroExt R M)) :=
  specMap (fstHom R R M).toRingHom

/-- The projection R ⊕ M → R of the trivial square-zero extension is a square-zero extension. -/
instance isSqZeroExt_fstHom : IsSqZeroExt (ofHom (fstHom R R M).toRingHom) where
  coe_surjective := fst_surjective
  mul_eq_zero := by aesop

variable (A) in
/-- The functions z are coordinates at 0 over s : Spec B → S in which O acts by the matrices m:
(a) the z_i are étale coordinates on V; for every ring map φ : B → C, with t : Spec C → S the
induced point, (b) the zero C-point of A lies in V, and, for C-points y, x that vanish modulo a
square-zero ideal and dz = `New.tangentCoords z`, (c) dz(ay) = φ(m(a)) dz(y) for a in O and
(d) dz(y + x) = dz(y) + dz(x). -/
def IsLieChart (s : Spec B ⟶ S) (V : A.left.Opens) (z : ι → Γ(A.left, V)) (m : O → Matrix ι ι B) :
    Prop :=
  IsEtaleChart A.hom V z ∧
  ∀ ⦃C : CommRingCat⦄ ⦃φ : B ⟶ C⦄ ⦃t : Spec C ⟶ S⦄, Spec.map φ ≫ s = t →
    LandsIn (0 : mk t ⟶ A).left V ∧
    ∀ ⦃D : CommRingCat⦄ ⦃ψ : C ⟶ D⦄ [IsSqZeroExt ψ] ⦃y : mk t ⟶ A⦄, IsInfinitesimal ψ y →
      (∀ a : O, tangentCoords z (a • y) = (m a).map φ *ᵥ tangentCoords z y) ∧
      ∀ x : mk t ⟶ A, IsInfinitesimal ψ x →
        tangentCoords z (y + x) = tangentCoords z y + tangentCoords z x

/-- The signature condition for a ring map ρ : O → R, elements b, b' of O and square matrices m(a)
over R: some vector X with a unit coordinate has m(a)X = ρ(a)X for all a in O, and
m(b) − ρ(b')·1 = Xξᵀ for some vector ξ. -/
def HasSignature (ρ : O →+* R) (b b' : O) (m : O → Matrix ι ι R) : Prop :=
  ∃ (X ξ : ι → R) (k : ι),
    IsUnit (X k) ∧ (∀ a : O, m a *ᵥ X = ρ a • X) ∧ m b - ρ b' • 1 = vecMulVec X ξ

end Definitions

variable {S X : Scheme} {A : Over S} {ι O : Type} {B C C' D : CommRingCat} {V : A.left.Opens}
  {f : X ⟶ S} [AddObj A] {t : Spec C ⟶ S} {s : Spec B ⟶ S} {ψ : C ⟶ C'} {z : ι → Γ(A.1, V)}
  {y : Over.mk t ⟶ A} [CommRing O] [ModuleObj O A]

/-! ### Existence of charts; the signature condition -/

/-- The two conditions of `New.IsSqZeroExt` as one conjunction. -/
lemma IsSqZeroExt.surjective_and_mul_eq_zero (hψ : IsSqZeroExt ψ) :
    (⇑ψ).Surjective ∧ ∀ a b : C, ψ a = 0 → ψ b = 0 → a * b = 0 :=
  ⟨hψ.coe_surjective, fun _ _ ↦ hψ.mul_eq_zero⟩

/-- The kernel of a square-zero extension ψ is a nilpotent ideal: its square is zero. -/
lemma IsSqZeroExt.isNilpotent_ker (hψ : IsSqZeroExt ψ) : IsNilpotent (RingHom.ker ψ.hom) := by
  refine ⟨2, ?_⟩
  simp_all [hψ.surjective_and_mul_eq_zero, ← le_bot_iff, Ideal.mul_le, sq]

/-- For a square-zero extension ψ : C → C', the map Spec C' → Spec C is surjective. -/
lemma IsSqZeroExt.surjective_specMap (hψ : IsSqZeroExt ψ) : Surjective (Spec.map ψ) := by
  -- A surjection with nil kernel induces a homeomorphism of spectra.
  have h_pow_mem (x : C') : ∃ n > 0, x ^ n ∈ ψ.hom.range := ⟨1, by simp [hψ.coe_surjective x]⟩
  have h_ker_le (a : C) (ha : a ∈ RingHom.ker ψ.hom) : a ∈ nilradical C :=
    ⟨2, by simp_all [hψ.surjective_and_mul_eq_zero, sq]⟩
  have h_homeo : IsHomeomorph (PrimeSpectrum.comap ψ.hom) :=
    PrimeSpectrum.isHomeomorph_comap ψ.hom h_pow_mem h_ker_le
  exact ⟨h_homeo.surjective⟩

/-- For a square-zero extension ψ : C → C', a point y : Spec C → X lands in the open V if its
restriction along Spec C' → Spec C does. -/
lemma IsSqZeroExt.landsIn_of_comp (hψ : IsSqZeroExt ψ) {y : Spec C ⟶ X} {V : X.Opens}
    (h_in : LandsIn (Spec.map ψ ≫ y) V) : LandsIn y V :=
  -- Every point of Spec C is the image of a point of Spec C', where the composite lands in V.
  hψ.surjective_specMap.surj.forall.mpr h_in

open MvPolynomial Algebra FormallySmooth FormallyUnramified RingHom in
/-- If f : X → S is smooth of relative dimension d, every point x of X has an open neighbourhood
V on which some d functions are étale coordinates for f. -/
lemma exists_isEtaleChart (x : X) {d : ℕ} (hf : SmoothOfRelativeDimension d f) :
    ∃ V : X.Opens, ∃ z : Fin d → Γ(X, V), x ∈ V ∧ IsEtaleChart f V z := by
  -- On affine opens `V` over `U` the map is étale over a polynomial ring; the images of the
  -- variables are the coordinates, and étale means unique lifting along `ψ`.
  obtain ⟨U, hU, V, hV, hx, hVU, h_smooth⟩ := hf.exists_isStandardSmoothOfRelativeDimension x
  obtain ⟨g, hg, h_etale⟩ := h_smooth.exists_etale_mvPolynomial
  refine ⟨V, g ∘ .X, hx, fun C C' ψ hψ t y l hy hyt hl ↦ ?_⟩
  -- A point `ρ` of `V` lies over `σ` and has coordinates `l` iff `ρ ∘ g` is evaluation at `(σ, l)`.
  have h_point_iff {C : CommRingCat} (ρ : Γ(X, V) ⟶ C) (σ : Γ(S, U) ⟶ C) (l : Fin d → C) :
      (map ρ ≫ hV.fromSpec) ≫ f = map σ ≫ hU.fromSpec ∧
          (PointFn.ofSection · C (map ρ ≫ hV.fromSpec)) ∘ g ∘ .X = l ↔
        ρ.hom.comp g = eval₂Hom σ.hom l := by
    -- `map_comp` is left out: it would undo the folding of `Spec.map` by `← map_comp_assoc`.
    simp [-map_comp, map_inj, hg, ← hU.SpecMap_appLE_fromSpec _ hV hVU, ← map_comp_assoc,
      cancel_mono, CommRingCat.hom_ext_iff, comp_assoc, MvPolynomial.ringHom_ext'_iff,
      _root_.funext_iff]
  -- Write `t` and `y` as ring maps `σ : Γ(S, U) ⟶ C` and `ξ : Γ(X, V) ⟶ C'`.
  obtain ⟨σ, rfl⟩ : ∃ σ : Γ(S, U) ⟶ C, map σ ≫ hU.fromSpec = t := by
    rw [← landsIn_opensRange, hU.opensRange_fromSpec]
    exact hψ.landsIn_of_comp (by simpa [← hyt] using landsIn_preimage.mp (hy.mono hVU))
  obtain ⟨ξ, rfl⟩ := landsIn_opensRange.mp (by rwa [hV.opensRange_fromSpec])
  have hξ : ξ.hom.comp g = eval₂Hom (σ ≫ ψ).hom (ψ ∘ l) :=
    (h_point_iff ξ (σ ≫ ψ) (ψ ∘ l)).1 ⟨by simp [hyt], hl.symm⟩
  algebraize [g, eval₂Hom σ.hom l, eval₂Hom (σ ≫ ψ).hom (ψ ∘ l)]
  have h_nil : IsNilpotent (ker ψ.hom) := hψ.isNilpotent_ker
  -- Existence: `g` is formally smooth, so `ξ` lifts to an algebra map `ρ` into `C`.
  obtain ⟨ρ, rfl⟩ :
      ∃ ρ : Γ(X, V) →ₐ[MvPolynomial (Fin d) Γ(S, U)] C, ofHom ρ.toRingHom ≫ ψ = ξ := by
    let ξ_alg : Γ(X, V) →ₐ[MvPolynomial (Fin d) Γ(S, U)] C' := ⟨ξ.hom, RingHom.congr_fun hξ⟩
    let ψ_alg : C →ₐ[MvPolynomial (Fin d) Γ(S, U)] C' := ⟨ψ.hom, map_eval₂Hom _ _ _⟩
    refine ⟨liftOfSurjective ξ_alg ψ_alg hψ.coe_surjective h_nil, ?_⟩
    ext a
    exact AlgHom.congr_fun (comp_liftOfSurjective ξ_alg ψ_alg hψ.coe_surjective h_nil) a
  obtain ⟨hρ_over, hρ_coord⟩ :=
    (h_point_iff (ofHom ρ.toRingHom) σ l).2 (RingHom.ext ρ.commutes)
  refine ⟨homMk _ hρ_over, ⟨by simp, hρ_coord⟩,
    fun ⟨y', _, hy'_over⟩ ⟨hy'_red, hy'_coord⟩ ↦ ?_⟩
  -- Uniqueness: another lift is an algebra map `ρ'` congruent to `ρ`, and `g` is unramified.
  obtain ⟨ρ', rfl⟩ := landsIn_opensRange.mp
    (hψ.landsIn_of_comp (landsIn_opensRange.mpr ⟨ofHom ρ.toRingHom ≫ ψ, hy'_red.symm⟩) :
      LandsIn y' hV.fromSpec.opensRange)
  have h_alg : ρ'.hom.comp g = eval₂Hom σ.hom l := (h_point_iff ρ' σ l).1 ⟨hy'_over, hy'_coord⟩
  have h_red : ρ' ≫ ψ = ofHom ρ.toRingHom ≫ ψ := by
    simpa [-map_comp, ← map_comp_assoc, cancel_mono, map_inj] using hy'_red
  obtain rfl : ⟨ρ'.hom, RingHom.congr_fun h_alg⟩ = ρ :=
    FormallyUnramified.ext' ψ.hom h_nil _ _ (ConcreteCategory.congr_hom h_red)
  rfl

@[simp]
lemma tangentCoords_zero : tangentCoords z (0 : mk t ⟶ A) = 0 := sub_self _

/-- Let `ρ : O → B` be a ring map, `b, b'` elements of `O`, and `m(a)` square matrices over `B`
indexed by `ι`. `New.HasSignature` means that some vector `X` with a unit coordinate has
`m(a)X = ρ(a)X` for all `a`, and `m(b) − ρ(b')·1 = Xξᵀ` for some vector `ξ`. If ring maps
`σ n : B → D` with jointly trivial kernel are such that this holds after applying each `σ n`, then
it holds after applying every `φ : B → C` with `C` local and `φ(ρ(b) − ρ(b'))` a unit. -/
lemma HasSignature.of_points [Fintype ι] [DecidableEq ι]
    {ρ : O →+* B} {b b' : O} {N : Sort*} {m : O → Matrix ι ι B}
    {σ : N → (B ⟶ D)} (h_inj : ∀ r : B, (∀ n : N, σ n r = 0) → r = 0)
    (h_points : ∀ n : N, HasSignature ((σ n).hom.comp ρ) b b' fun a : O ↦ (m a).map (σ n))
    (φ : B ⟶ C) [IsLocalRing C] (h_unit : IsUnit (φ (ρ b - ρ b'))) :
    HasSignature (φ.hom.comp ρ) b b' fun a : O ↦ (m a).map φ := by
  -- Put `q = m b - ρ b'`. Three identities hold after every `σ n`, where `q = X ξᵀ` and `X` is an
  -- eigenvector, so they hold in `B`, as the `σ n` are jointly injective: the trace of `q` is
  -- `ρ b - ρ b'`, its columns are eigenvectors and its 2 × 2 minors vanish. In the local ring `C`
  -- some diagonal entry of `q` is then a unit.
  have h_points_exists : ∀ n : N, ∃ (X ξ : ι → D) (k : ι), IsUnit (X k) ∧
      (∀ a : O, (m a).map (σ n) *ᵥ X = σ n (ρ a) • X) ∧
      (m b).map (σ n) - σ n (ρ b') • 1 = vecMulVec X ξ := h_points
  choose X ξ k hX_unit hX_eigen hX_rank using h_points_exists
  obtain ⟨q, hq⟩ : ∃ q : Matrix ι ι B, q + ρ b' • 1 = m b := add_right_surjective _ _
  have h_eigen (n : N) (a : O) (i : ι) : ∑ j : ι, σ n (m a i j) * X n j = σ n (ρ a) * X n i :=
    congrFun (hX_eigen n a) i
  have h_rank (n : N) (i j : ι) : σ n (q i j) = X n i * ξ n j := by
    simpa [← hq, Matrix.map_add, map_smul', vecMulVec] using congr_fun₂ (hX_rank n) i j
  have h_eigen_b (n : N) (i : ι) :
      ∑ j : ι, σ n (q i j) * X n j + σ n (ρ b') * X n i = σ n (ρ b) * X n i := by
    simpa [← hq, one_apply, add_mul, Finset.sum_add_distrib, apply_ite (σ n)] using h_eigen n b i
  have h_trace : ρ b - ρ b' - ∑ i, q i i = 0 := by
    -- `q X = (ξ ⬝ X) X` is the trace times `X`; compare with `q X = (ρ b - ρ b') X` at a unit
    -- entry of `X`.
    refine h_inj _ fun n ↦ (hX_unit n).mul_left_eq_zero.1 ?_
    have h_comm : ∑ j : ι, σ n (q (k n) j) * X n j = ∑ j : ι, σ n (q j j) * X n (k n) := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [h_rank n (k n) j, h_rank n j j]
      ring
    simp [sub_mul, Finset.sum_mul, ← h_eigen_b n (k n), h_comm]
  -- The columns of `q` are eigenvectors of every `m a`, and the 2 × 2 minors of `q` vanish.
  have h_col (a : O) (i l : ι) : ∑ j : ι, m a i j * q j l - ρ a * q i l = 0 :=
    h_inj _ fun n ↦ by simp [← mul_assoc, ← Finset.sum_mul, h_rank, h_eigen]
  have h_minor (i j l : ι) : q l l * q i j - q i l * q l j = 0 :=
    h_inj _ fun n ↦ by simp only [map_sub, map_mul, h_rank]; ring
  rw [sub_eq_zero.1 h_trace, map_sum] at h_unit
  obtain ⟨l, -, c, hc⟩ := exists_of_isUnit_sum h_unit
  -- The eigenvector is the `l`-th column of `q`, and `ξ` is the `l`-th row divided by `q l l`.
  refine ⟨fun i ↦ φ (q i l), fun j ↦ ↑c⁻¹ * φ (q l j), l, ⟨c, hc⟩, fun a ↦ funext fun i ↦ ?_, ?_⟩
  · simpa [mulVec, dotProduct, sub_eq_zero] using congrArg φ (h_col a i l)
  · have h_entry (i j : ι) : φ (q i j) = φ (q i l) * (↑c⁻¹ * φ (q l j)) := by
      have h_minor_φ : c * φ (q i j) = φ (q i l) * φ (q l j) := by
        rw [hc, ← map_mul, ← map_mul, ← sub_eq_zero, ← map_sub, h_minor i j l, map_zero]
      rw [← one_mul (φ (q i j)), ← c.inv_mul, mul_assoc, h_minor_φ]
      ring
    simpa [← hq, Matrix.map_add, map_smul', ← ext_iff, vecMulVec] using h_entry

lemma IsInfinitesimal.smul (hy : IsInfinitesimal ψ y) (c : O) : IsInfinitesimal ψ (c • y) := by
  simp_all [IsInfinitesimal]

/-- A C-point y of A over t : Spec C → S that is infinitesimal for ψ : C → C' restricts to the zero
point along Spec C' → Spec C. -/
lemma IsInfinitesimal.map_comp_left (hy : IsInfinitesimal ψ y) :
    Spec.map ψ ≫ y.left = (0 : mk (Spec.map ψ ≫ t) ⟶ A).left :=
  congrArg (fun b : mk (Spec.map ψ ≫ t) ⟶ A ↦ b.left) hy

/-- Let y be a C-point of A over t : Spec C → S that is infinitesimal for ψ : C → C', and let a be
the morphism over S induced by a ring map χ : C → D. If φ : D → B and κ : C' → B satisfy
χ ≫ φ = ψ ≫ κ, the pull-back a ≫ y is infinitesimal for φ. -/
lemma IsInfinitesimal.precomp (hy : IsInfinitesimal ψ y) {χ : C ⟶ D} {t' : Spec D ⟶ S}
    (a : mk t' ⟶ mk t) (ha_left : a.left = Spec.map χ) {φ : D ⟶ B} (κ : C' ⟶ B)
    (h_comm : χ ≫ φ = ψ ≫ κ) : IsInfinitesimal φ (a ≫ y) := by
  -- Compose `hy` with `map κ`; by `h_comm` and `ha_left`, `map κ ≫ map ψ = map φ ≫ a.left`.
  have h_red : map κ ≫ map ψ ≫ y.left = map κ ≫ (0 : mk (map ψ ≫ t) ⟶ A).left :=
    congrArg (map κ ≫ ·) hy.map_comp_left
  ext
  simpa [ha_left, h_comm, Hom.zero_def, ← show a.left ≫ t = t' from a.w, ← map_comp_assoc,
    -map_comp] using h_red

namespace IsEtaleChart

/-! ### Points that vanish modulo a square-zero ideal -/

/-- Let z be étale coordinates on an open V of A containing the zero C-point (over
t : Spec C → S), and ψ a square-zero extension out of C. For every vector l with entries in ker ψ
there is exactly one C-point y that vanishes modulo ker ψ and has z(y) − z(0) = l. -/
lemma existsUnique_tangentCoords_eq (hz : IsEtaleChart A.hom V z)
    (h_zero_in : LandsIn (0 : mk t ⟶ A).left V) (hψ : IsSqZeroExt ψ) (l : ι → C)
    (hl : ∀ k : ι, ψ (l k) = 0) :
    ∃! y : mk t ⟶ A, IsInfinitesimal ψ y ∧ tangentCoords z y = l := by
  -- Lift the zero point along `ψ` with prescribed coordinates `l + z(0)`.
  have h_coords : ψ ∘ (l + fun k ↦ PointFn.ofSection (z k) C (0 : mk t ⟶ A).left) =
      (fun s ↦ PointFn.ofSection s C' (map ψ ≫ (0 : mk t ⟶ A).left)) ∘ z := by
    simp [PointFn.isRegularOn_ofSection _ ψ, h_zero_in, hl, funext_iff]
  have h_lift :
      ∃! y : mk t ⟶ mk A.hom,
        map ψ ≫ y.left = map ψ ≫ (0 : mk t ⟶ A).left ∧
        (PointFn.ofSection · C y.left) ∘ z =
          l + fun k ↦ PointFn.ofSection (z k) C (0 : mk t ⟶ A).left :=
    hz _ _ (h_zero_in.comp _) (by simp) h_coords
  refine (existsUnique_congr fun _ ↦ ?_).2 h_lift
  exact OverMorphism.ext_iff.and sub_eq_iff_eq_add

/-- Let the open V contain the zero C-point, and let y be a C-point that is infinitesimal for a
square-zero extension ψ. For the morphism a over S induced by a ring map χ : C → D, the
coordinates z(a ≫ y) − z(0) are those of y mapped by χ. -/
lemma tangentCoords_comp (h_zero_in : LandsIn (0 : mk t ⟶ A).left V) (hy : IsInfinitesimal ψ y)
    {χ : C ⟶ D} {t' : Spec D ⟶ S} (a : mk t' ⟶ mk t)
    (ha_left : a.left = Spec.map χ) [hψ : IsSqZeroExt ψ] :
    tangentCoords z (a ≫ y) = χ ∘ tangentCoords z y := by
  -- `y` lies in `V` because its reduction `0` does; on `V` the `z k` commute with `χ`.
  have hy_in : LandsIn y.left V :=
    hψ.landsIn_of_comp (by rw [hy.map_comp_left]; exact h_zero_in.comp _)
  simp [← comp_zero a, -comp_zero, tangentCoords, PointFn.isRegularOn_ofSection _ χ, hy_in, ha_left,
    h_zero_in, funext_iff]

/-- The coordinates z(y) − z(0) of a C-point y that is infinitesimal for the square-zero extension
ψ lie in ker ψ; here z are étale coordinates on V, which contains the zero C-point. -/
lemma map_tangentCoords_eq_zero (_hz : IsEtaleChart A.hom V z)
    (h_zero_in : LandsIn (0 : mk t ⟶ A).left V) (hy : IsInfinitesimal ψ y) [hψ : IsSqZeroExt ψ]
    (k : ι) :
    ψ (tangentCoords z y k) = 0 := by
  -- `ψ ∘ tangentCoords z y` is `tangentCoords z` of the reduction of `y`, which is `0`.
  have hy_zero : (homMk (map ψ) : mk (map ψ ≫ t) ⟶ mk t) ≫ y = 0 := hy
  have h_nat :=
    tangentCoords_comp (z := z) h_zero_in hy (homMk (map ψ) : mk (map ψ ≫ t) ⟶ mk t) rfl
  rw [hy_zero, tangentCoords_zero] at h_nat
  exact (congrFun h_nat k).symm

/-- A C-point y that is infinitesimal for the square-zero extension ψ and has coordinates
z(y) − z(0) = 0 is zero; here z are étale coordinates on V, which contains the zero C-point. -/
lemma eq_zero_of_tangentCoords_eq_zero (hz : IsEtaleChart A.hom V z)
    (h_zero_in : LandsIn (0 : mk t ⟶ A).left V) (hy : IsInfinitesimal ψ y) [hψ : IsSqZeroExt ψ]
    (h_dv : tangentCoords z y = 0) : y = 0 :=
  (hz.existsUnique_tangentCoords_eq h_zero_in hψ 0 (by simp)).unique ⟨hy, h_dv⟩
    ⟨rfl, tangentCoords_zero⟩

end IsEtaleChart

/-! ### Coordinates at 0 -/

variable [Fintype ι]

/-- The functions z of a chart at 0 (`New.IsLieChart`) are étale coordinates on V. -/
lemma IsLieChart.isEtaleChart {s : Spec B ⟶ S} {V : A.left.Opens} {z : ι → Γ(A.left, V)}
    {m : O → Matrix ι ι B} (h_lie : IsLieChart A s V z m) : IsEtaleChart A.hom V z := h_lie.1

/-- For a chart at 0 over s : Spec B → S and the point t = Spec φ ≫ s of a ring map φ : B → C,
the zero C-point of A lies in V. -/
lemma IsLieChart.zero_landsIn {s : Spec B ⟶ S} {V : A.left.Opens} {z : ι → Γ(A.left, V)}
    {m : O → Matrix ι ι B} (h_lie : IsLieChart A s V z m) {φ : B ⟶ C} (ht : Spec.map φ ≫ s = t) :
    LandsIn (0 : mk t ⟶ A).left V := (h_lie.2 ht).1

/-- For a chart at 0 over s with matrices m, the point t = Spec φ ≫ s, and a C-point y that is
infinitesimal for a square-zero extension ψ: dz(a y) = φ(m(a)) dz(y) for a in O, where
dz = `New.tangentCoords z`. -/
lemma IsLieChart.tangentCoords_smul {s : Spec B ⟶ S} {V : A.left.Opens} {z : ι → Γ(A.left, V)}
    {m : O → Matrix ι ι B} (h_lie : IsLieChart A s V z m) {φ : B ⟶ C} (ht : Spec.map φ ≫ s = t)
    {ψ : C ⟶ C'} [IsSqZeroExt ψ] {y : mk t ⟶ A} (hy : IsInfinitesimal ψ y) (a : O) :
    tangentCoords z (a • y) = (m a).map φ *ᵥ tangentCoords z y := ((h_lie.2 ht).2 hy).1 a

/-- For a chart at 0 over s, the point t = Spec φ ≫ s, and C-points y, x that are infinitesimal
for a square-zero extension ψ: dz(y + x) = dz(y) + dz(x), where dz = `New.tangentCoords z`. -/
lemma IsLieChart.tangentCoords_add {s : Spec B ⟶ S} {V : A.left.Opens} {z : ι → Γ(A.left, V)}
    {m : O → Matrix ι ι B} (h_lie : IsLieChart A s V z m) {φ : B ⟶ C} (ht : Spec.map φ ≫ s = t)
    {ψ : C ⟶ C'} [IsSqZeroExt ψ] {y x : mk t ⟶ A} (hy : IsInfinitesimal ψ y)
    (hx : IsInfinitesimal ψ x) :
    tangentCoords z (y + x) = tangentCoords z y + tangentCoords z x := ((h_lie.2 ht).2 hy).2 x hx

/-- The four conditions of a chart at 0, each with its own quantifiers, give `New.IsLieChart`. -/
lemma IsLieChart.of_isEtaleChart {s : Spec B ⟶ S} {V : A.left.Opens} {z : ι → Γ(A.left, V)}
    {m : O → Matrix ι ι B} (h_chart : IsEtaleChart A.hom V z)
    (h_zero : ∀ ⦃C : CommRingCat⦄ ⦃φ : B ⟶ C⦄ ⦃t : Spec C ⟶ S⦄, Spec.map φ ≫ s = t →
      LandsIn (0 : mk t ⟶ A).left V)
    (h_smul : ∀ ⦃C : CommRingCat⦄ ⦃φ : B ⟶ C⦄ ⦃t : Spec C ⟶ S⦄, Spec.map φ ≫ s = t →
      ∀ ⦃D : CommRingCat⦄ ⦃ψ : C ⟶ D⦄ [IsSqZeroExt ψ] ⦃y : mk t ⟶ A⦄, IsInfinitesimal ψ y →
      ∀ a : O, tangentCoords z (a • y) = (m a).map φ *ᵥ tangentCoords z y)
    (h_add : ∀ ⦃C : CommRingCat⦄ ⦃φ : B ⟶ C⦄ ⦃t : Spec C ⟶ S⦄, Spec.map φ ≫ s = t →
      ∀ ⦃D : CommRingCat⦄ ⦃ψ : C ⟶ D⦄ [IsSqZeroExt ψ] ⦃y x : mk t ⟶ A⦄, IsInfinitesimal ψ y →
      IsInfinitesimal ψ x → tangentCoords z (y + x) = tangentCoords z y + tangentCoords z x) :
    IsLieChart A s V z m :=
  ⟨h_chart, fun _ _ _ ht ↦ ⟨h_zero ht, fun _ _ _ _ hy ↦
    ⟨h_smul ht hy, fun _ hx ↦ h_add ht hy hx⟩⟩⟩

/-- Coordinates at 0 exist. Let `A` be a commutative group scheme over `S` with an action of `O`,
smooth of relative dimension `g`, and let `s : Spec B → S` with `B` local. Then there are an open
`V` of `A`, functions `z : Fin g → Γ(A, V)` and `g × g` matrices `m(a)` over `B` (for `a` in `O`)
such that, for every ring map `φ : B → C` with induced point `t = Spec φ ≫ s`, `New.IsLieChart`
holds with the matrices `φ(m(a))`: the `z_i` are étale coordinates on `V`, the zero `C`-point lies
in `V`, and on `C`-points vanishing modulo a square-zero ideal the differentials `dz` are additive
and `a` acts on them by `φ(m(a))`. -/
lemma exists_isLieChart {g : ℕ} (hd : SmoothOfRelativeDimension g A.hom) [IsLocalRing B]
    (s : Spec B ⟶ S) :
    ∃ (V : A.left.Opens) (z : Fin g → Γ(A.left, V)), ∃ m : O → Matrix (Fin g) (Fin g) B,
      ∀ {C : CommRingCat} {t : Spec C ⟶ S} {φ : B ⟶ C}, Spec.map φ ≫ s = t →
      IsLieChart A t V z fun a : O ↦ (m a).map φ := by
  -- Work with the universal pair of infinitesimal points `Y .inl`, `Y .inr` over the square-zero
  -- extension `B ⊕ B^{2g}`, whose coordinates are the `2g` basis vectors. Every pair of such points
  -- is a pull-back of it, so the coordinates of `c • (y + y')` are linear forms over `B` in those
  -- of `y` and `y'`.
  obtain ⟨V, z, h_mem, hz⟩ := exists_isEtaleChart ((0 : mk s ⟶ A).left (closedPoint B)) hd
  have h_in {C : CommRingCat} {φ : B ⟶ C} : LandsIn (0 : mk (map φ ≫ s) ⟶ A).left V :=
    (landsIn_iff_mem.mpr h_mem).comp _
  -- `Y c` is the infinitesimal point whose `k`-th coordinate is the basis vector number `c k`.
  have h_univ_point (c : Fin g → Fin g ⊕ Fin g) :
      ∃ Y : mk (map (ofHom (inlHom B (Fin g ⊕ Fin g → B))) ≫ s) ⟶ A,
        IsInfinitesimal (ofHom (fstHom B B (Fin g ⊕ Fin g → B)).toRingHom) Y ∧
          tangentCoords z Y = inr ∘ (Pi.single · 1) ∘ c :=
    (hz.existsUnique_tangentCoords_eq h_in isSqZeroExt_fstHom _ (by simp)).exists
  choose Y hY hY_coords using h_univ_point
  -- The coefficients of the linear forms: the `B^{2g}`-parts of the universal coordinates.
  let b (c : O) : Fin g → Fin g ⊕ Fin g → B := snd ∘ tangentCoords z (c • (Y .inl + Y .inr))
  have h_coords_smul_add (c : O) {C C' : CommRingCat} {φ : B ⟶ C} {ψ : C ⟶ C'} [hψ : IsSqZeroExt ψ]
      {y y' : mk (map φ ≫ s) ⟶ A} (hy : IsInfinitesimal ψ y) (hy' : IsInfinitesimal ψ y') :
      tangentCoords z (c • (y + y')) =
        fun k ↦ φ ∘ b c k ⬝ᵥ (tangentCoords z y ⊕ᵥ tangentCoords z y') := by
    let L : Fin g ⊕ Fin g → C := tangentCoords z y ⊕ᵥ tangentCoords z y'
    have h_univ : IsInfinitesimal (ofHom (fstHom B B _).toRingHom) (c • (Y .inl + Y .inr)) :=
      IsInfinitesimal.smul (by rw [IsInfinitesimal, comp_add, hY, hY, add_zero]) c
    have h_ker (v : Fin g ⊕ Fin g → C) : ψ (v ⬝ᵥ L) = 0 := by
      simp [L, dotProduct, hz.map_tangentCoords_eq_zero h_in hy,
        hz.map_tangentCoords_eq_zero h_in hy']
    algebraize [φ.hom]
    -- The entries of `L` lie in the square-zero kernel of `ψ`, so sending the basis vectors to them
    -- is a `B`-algebra map `B ⊕ B^{2g} → C`; `q` is the induced map of schemes over `S`.
    have h_mul_eq_zero (v v' : Fin g ⊕ Fin g → B) :
        Fintype.linearCombination B L v * Fintype.linearCombination B L v' = 0 :=
      -- `Fintype.linearCombination B L v` is `(φ ∘ v) ⬝ᵥ L`, which lies in `ker ψ` by `h_ker`.
      hψ.mul_eq_zero (h_ker (φ ∘ v)) (h_ker (φ ∘ v'))
    let q : mk (map φ ≫ s) ⟶ mk (map (ofHom (inlHom B (Fin g ⊕ Fin g → B))) ≫ s) :=
      (Over.map s).map
        (specOver.map (liftEquivOfComm ⟨Fintype.linearCombination B L, h_mul_eq_zero⟩))
    -- Coordinates determine the point, so `q` pulls the universal pair back to `y`, `y'`.
    have h_pull (c : Fin g → Fin g ⊕ Fin g) {x : mk (map φ ≫ s) ⟶ A} (hx : IsInfinitesimal ψ x)
        (hL : tangentCoords z x = L ∘ c) : q ≫ Y c = x := by
      refine (hz.existsUnique_tangentCoords_eq h_in hψ (tangentCoords z x)
          (hz.map_tangentCoords_eq_zero h_in hx)).unique ⟨(hY c).precomp q rfl (φ ≫ ψ) ?_, ?_⟩
        ⟨hx, rfl⟩
      · exact hom_ext (RingHom.ext fun _ ↦ (map_add _ _ _).trans (add_eq_left.2 (h_ker _)))
      · simp [IsEtaleChart.tangentCoords_comp (z := z) h_in (hY c) q rfl, hY_coords, hL, funext_iff]
    -- The universal coordinates have no `B`-part; pull them back along `q`.
    have h_fst : ∀ k : Fin g, (tangentCoords z (c • Y .inl + c • Y .inr) k).fst = 0 := by
      simpa using hz.map_tangentCoords_eq_zero h_in h_univ
    -- `using!`: the two sides agree only after unfolding `Fintype.linearCombination`.
    simpa [b, h_pull .inl hy rfl, h_pull .inr hy' rfl, lift, h_fst, funext_iff, comp_add] using!
      IsEtaleChart.tangentCoords_comp (z := z) h_in h_univ q rfl
  refine ⟨V, z, toCols₁ ∘ b, fun {C t φ} ht ↦ IsLieChart.of_isEtaleChart hz ?_ ?_ ?_⟩
  · intro C₁ φ₁ t₁ ht₁
    obtain rfl : map (φ ≫ φ₁) ≫ s = t₁ := by rw [map_comp_assoc, ht, ht₁]
    exact h_in
  · intro C₁ φ₁ t₁ ht₁ D ψ _ y hy a
    obtain rfl : map (φ ≫ φ₁) ≫ s = t₁ := by rw [map_comp_assoc, ht, ht₁]
    -- Take `y' = 0`: only the first `g` columns of `b a` remain.
    -- `using!`: the sum matches `mulVec` of the first `g` columns only up to unfolding.
    simpa [dotProduct] using! h_coords_smul_add a hy (comp_zero _)
  · intro C₁ φ₁ t₁ ht₁ D ψ _ y x hy hx
    obtain rfl : map (φ ≫ φ₁) ≫ s = t₁ := by rw [map_comp_assoc, ht, ht₁]
    -- The linear form for `c = 1` at `(y, x)` is the sum of those at `(y, 0)`, `(0, x)`.
    have h_split : tangentCoords z ((1 : O) • (y + x)) =
        tangentCoords z ((1 : O) • (y + 0)) + tangentCoords z ((1 : O) • (0 + x)) := by
      simp only [h_coords_smul_add 1 hy hx, h_coords_smul_add 1 hy (comp_zero _),
        h_coords_smul_add 1 (comp_zero _) hx]
      simp [funext_iff, dotProduct]
    simpa using h_split

/-- Let A → S be smooth of constant relative dimension, let t : Spec C → S factor through
s : Spec B → S with B local, let the C-point y of A vanish modulo the square-zero ideal ker ψ,
and let m ∈ ℕ. If m is invertible in C, my = 0 forces y = 0; if m = 0 in C, my = 0. -/
lemma IsInfinitesimal.eq_zero_of_isUnit_and_nsmul_eq_zero_of_cast_eq_zero (hy : IsInfinitesimal ψ y)
    [h : IsSqZeroExt ψ]
    {g : ℕ} (hd : SmoothOfRelativeDimension g A.hom) [IsLocalRing B] (a : mk t ⟶ mk s) (m : ℕ) :
    (IsUnit (m : C) → m • y = 0 → y = 0) ∧ ((m : C) = 0 → m • y = 0) := by
  obtain ⟨V, z, mat, h_jac⟩ := exists_isLieChart (O := ℤ) hd s
  have h_lie := h_jac ((map_preimage _ =≫ s).trans a.w)
  have h_base : Spec.map (𝟙 C) ≫ t = t := by simp
  have h_in := h_lie.zero_landsIn h_base
  -- The coordinates are additive on infinitesimal points, so those of `m • y` are `m` times
  -- those of `y`.
  have h_nsmul (k : ℕ) : IsInfinitesimal ψ (k • y) := by simpa using hy.smul (k : ℤ)
  have h_add (k : ℕ) :
      tangentCoords z (k • y + y) = tangentCoords z (k • y) + tangentCoords z y :=
    h_lie.tangentCoords_add h_base (h_nsmul k) hy
  have h_dv : tangentCoords z (m • y) = (m : C) • tangentCoords z y := by
    induction m with
    | zero => simp
    | succ k ih => rw [succ_nsmul, h_add k, ih, Nat.cast_succ, add_smul, one_smul]
  -- An infinitesimal point with vanishing coordinates is zero.
  refine ⟨fun hm hmy ↦ ?_, fun hm ↦ ?_⟩
  · have h_smul_zero : (m : C) • tangentCoords z y = 0 := by
      rw [← h_dv, hmy, tangentCoords_zero]
    exact h_lie.isEtaleChart.eq_zero_of_tangentCoords_eq_zero h_in hy
      (hm.smul_eq_zero.1 h_smul_zero)
  · have h_coords_zero : tangentCoords z (m • y) = 0 := by rw [h_dv, hm, zero_smul]
    exact h_lie.isEtaleChart.eq_zero_of_tangentCoords_eq_zero h_in (h_nsmul m) h_coords_zero

/-- Let A → S be smooth of constant relative dimension, let t : Spec C → S factor through
s : Spec B → S with B local, and let the C-point y of A vanish modulo the square-zero ideal ker ψ.
If m is invertible in C, then my = 0 forces y = 0. -/
lemma IsInfinitesimal.eq_zero_of_nsmul_eq_zero (hy : IsInfinitesimal ψ y) [IsSqZeroExt ψ] {g : ℕ}
    (hd : SmoothOfRelativeDimension g A.hom) [IsLocalRing B] (a : mk t ⟶ mk s) {m : ℕ}
    (hm : IsUnit (m : C)) (hmy : m • y = 0) : y = 0 :=
  (hy.eq_zero_of_isUnit_and_nsmul_eq_zero_of_cast_eq_zero hd a m).left hm hmy

/-- Let A → S be smooth of constant relative dimension, let t : Spec C → S factor through
s : Spec B → S with B local, and let the C-point y of A vanish modulo the square-zero ideal ker ψ.
If m = 0 in C, then my = 0. -/
lemma IsInfinitesimal.nsmul_eq_zero (hy : IsInfinitesimal ψ y) [IsSqZeroExt ψ] {g : ℕ}
    (hd : SmoothOfRelativeDimension g A.hom) [IsLocalRing B] (a : mk t ⟶ mk s) {m : ℕ}
    (hm : (m : C) = 0) : m • y = 0 :=
  (hy.eq_zero_of_isUnit_and_nsmul_eq_zero_of_cast_eq_zero hd a m).right hm

end New

end TangentCoords

/-! ## Unramified torsion sections -/

section TorsionUnramified

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory IsLocalRing Ideal Ideal.Quotient
  Spec AddMonObj

/-- Let B be an abelian scheme of relative dimension g over a local ring R and m a natural number
invertible in R. A section x with mx = 0 that vanishes at some point of Spec R with values in a
nonzero ring K is zero. -/
lemma New.Variety.eq_zero_of_nsmul_eq_zero_of_comp_eq_zero {R K : Type} {g : ℕ} [CommRing R]
    [IsLocalRing R]
    {B : Over (Spec ⟨R⟩)} [IsAbelianScheme B] (hd : SmoothOfRelativeDimension g B.hom) {m : ℕ}
    (h_unit : IsUnit (m : R)) {x : MonoidalCategoryStruct.tensorUnit (Over (Spec ⟨R⟩)) ⟶ B}
    (h_torsion : m • x = 0) [CommRing K] [Nontrivial K] {s : Spec ⟨K⟩ ⟶ Spec ⟨R⟩}
    (h_vanish : toUnit (Over.mk s) ≫ x = 0) : x = 0 := by
  -- Let `I` be the ideal of `R` that cuts out the locus `x = 0`. Over `R / I²` the section
  -- vanishes modulo the square-zero ideal `I / I²` and is killed by the unit `m`, hence is zero. So
  -- `I ≤ I²`, and `I = 0` by Nakayama's lemma.
  -- `hI`: a ring map `γ` kills `I` exactly when `x` pulled back along `γ` factors through the
  -- zero section `ζ[B]`; `I` is finitely generated since `ζ[B]` is of finite presentation.
  obtain ⟨I, hI_fg, hI⟩ := exists_ideal_le_ker_iff_factors ζ[B].left x.left
  have h_fg : I.FG := hI_fg (locallyOfFinitePresentation_left
    (h := inferInstanceAs (LocallyOfFinitePresentation (𝟙 (Spec ⟨R⟩)))))
  -- `R ⧸ I² → R ⧸ I` is onto, and its kernel `I / I²` has square zero.
  have h_sq : IsSqZeroExt (CommRingCat.ofHom (factor (mul_le_right : I * I ≤ I))) := by
    refine ⟨factor_surjective mul_le_right, fun {a b} ↦ ?_⟩
    obtain ⟨a, rfl⟩ := mk_surjective a
    obtain ⟨b, rfl⟩ := mk_surjective b
    simpa [eq_zero_iff_mem, ← map_mul] using mul_mem_mul
  have h_inf : IsInfinitesimal (CommRingCat.ofHom (factor (mul_le_right : I * I ≤ I)))
      (toUnit (specOver R (R ⧸ I * I)) ≫ x) := by
    -- `using!`: the composite of the two quotient maps is `mk I` only up to unfolding.
    simpa [IsInfinitesimal, eq_zero_iff_factors_zero_section, -map_comp, ← map_comp_assoc] using!
      hI (mk I)
  have h_zero : toUnit (specOver R (R ⧸ I * I)) ≫ x = 0 :=
    (h_inf.eq_zero_of_isUnit_and_nsmul_eq_zero_of_cast_eq_zero (h := h_sq) hd (toUnit _) m).1
      (h_unit.map (algebraMap R (R ⧸ I * I))) (by rw [← comp_nsmul, h_torsion, comp_zero])
  have h_le_sq : I ≤ I • I :=
    ((hI (mk (I * I))).2 (eq_zero_iff_factors_zero_section.1 h_zero)).trans_eq mk_ker
  -- `I` is proper, because `x` vanishes on the spectrum of the nonzero ring `K`.
  have h_le_ker : I ≤ RingHom.ker (preimage s).hom := by
    simpa [hI, eq_zero_iff_factors_zero_section] using h_vanish
  -- Nakayama's lemma: a finitely generated ideal inside the Jacobson radical with `I ≤ I • I`.
  have h_bot : I = ⊥ := I.eq_bot_of_le_smul_of_le_jacobson_bot I h_fg h_le_sq
    (h_le_ker.trans ((le_maximalIdeal (RingHom.ker_ne_top _)).trans (maximalIdeal_le_jacobson _)))
  simpa [eq_zero_iff_factors_zero_section, h_bot] using hI (.id R)

end TorsionUnramified

end
