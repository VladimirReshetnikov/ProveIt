import Lib.General.Algebra.MultivariatePolynomials
import Lib.Shimura.ThetaGroup
import Lib.Shimura.ThetaNormality.NormalGeneration

/-!
# Absolute Frobenius, Serre's theorem on sections of powers, and projective embeddings

A line bundle (`New.LineBundle`) is an open cover `U i` with a cocycle `g i j`, and `L.picClass` is
its class in the additively written Picard group. `New.LineBundle.IsLinearSystem` says that the
transition functions behave like the affine coordinates `s j / s i` of a map to a projective space.
The file shows that the absolute `l ^ f`-Frobenius multiplies the class of a linear system by
`l ^ f`.

## Main definitions and results

* `New.Variety.absFrobenius f X`: the absolute `l ^ f`-Frobenius of a scheme `X` over a field of
  characteristic `l`. It acts on `B`-valued points through `x ↦ x ^ l ^ f` on `B`
  (`New.Variety.comp_absFrobenius`), commutes with all morphisms and fixes the underlying space.
* `New.Variety.eventually_span_coordSection`: let `N` be a projective embedding of an integral
  scheme over a field and `p` a base change to a noetherian ring. For large `m` the monomials of
  degree `m` in the coordinates span the sections of `(p^* N) ^ m`.
* The instance `New.isProper_pi`: the product in `Over S` of a finite family of proper schemes over
  `S` is proper over `S`.
* `New.Variety.HasProjEmbedding.of_isClosedImmersion_pi`: if finitely many `S`-schemes have
  projective embeddings over `S`, so does every closed subscheme of their fibre product.

Notions from other files:
* `New.LineBundle.pull`, `New.LineBundle.pow`: the pull-back of a line bundle along a morphism, and
  its `m`-th tensor power, whose charts are indexed by `m`-tuples of indices.
* `New.LineBundle.IsProjEmbedding`: a linear system on a proper scheme whose affine coordinates
  `g i j` separate the ring-valued points of each chart `U i` over the base.
* `New.Variety.coordSection`: the `j`-th coordinate `s j` of a linear system as a global section.
* `New.ThetaTori.formSpan R x m`: the values at a family `x` of the forms of degree `m` over `R`.

## Relation to the literature

Known result: a case of the surjectivity half of Serre's theorem on sections of powers of a
projective embedding.
-/

universe u v

namespace New.Variety

/-! ## The absolute Frobenius and classes of linear systems -/

section AbsoluteFrobenius

open CategoryTheory AlgebraicGeometry CommRingCat LineBundle Spec

/-- If `Spec B` maps to the spectrum of a field `k` of characteristic `l`, then `l = 0` in `B`. -/
lemma natCast_eq_zero_of_over_charP {k : Type} [Field k] {l : ℕ} {B : CommRingCat} [CharP k l]
    (s : Spec B ⟶ Spec ⟨k⟩) : (l : B) = 0 := by
  rw [← map_natCast (preimage s).hom, CharP.cast_eq_zero, map_zero]

variable {k : Type} {l : ℕ} [Field k] [CharP k l] [Fact l.Prime] (f : ℕ) (X Y : Over (Spec ⟨k⟩))

/-- For a scheme `X` over a field `k` of prime characteristic `l`, there is an endomorphism of the
underlying scheme that acts on `B`-valued points through `x ↦ x ^ l ^ f` on `B`, for every ring
`B`. -/
lemma exists_absFrobenius :
    ∃ F : X.left ⟶ X.left, ∀ (B : CommRingCat) (t : Spec B ⟶ X.left),
      t ≫ F =
        specMap (frobPow (natCast_eq_zero_of_over_charP (l := l) (B := B) (t ≫ X.hom)) f) ≫ t := by
  -- Glue the maps `Spec (x ↦ x ^ l ^ f) ≫ t` over all ring-valued points `t` of `X`.
  let twist (B : CommRingCat) (t : Spec B ⟶ X.left) : Spec B ⟶ X.left :=
    specMap (frobPow (natCast_eq_zero_of_over_charP (l := l) (B := B) (t ≫ X.hom)) f) ≫ t
  -- Ring maps commute with `x ↦ x ^ l ^ f`.
  have frob_comm {A B : CommRingCat} (φ : A ⟶ B) (hA : (l : A) = 0) (hB : (l : B) = 0) :
      φ ≫ ofHom (frobPow hB f) = ofHom (frobPow hA f) ≫ φ := by
    ext x
    simp
  have twist_comp (A B : CommRingCat) (φ : A ⟶ B) (t : Spec A ⟶ X.left) :
      twist B (Spec.map φ ≫ t) = Spec.map φ ≫ twist A t := by
    simp only [twist, ← map_comp_assoc]
    rw [frob_comm]
  -- Glue on the cover of `X` by the single open set `⊤`.
  obtain ⟨F, hF⟩ := exists_hom_of_cover isOpenCover_top (fun (_ : Unit) B t _ ↦ twist B t)
    fun _ _ A B φ t _ _ ↦ twist_comp A B φ t
  exact ⟨F, fun B t ↦ hF () B t landsIn_top⟩

/-- For a scheme `X` over a field `k` of prime characteristic `l`, the absolute `l ^ f`-Frobenius of
the underlying scheme. It acts on `B`-valued points through `x ↦ x ^ l ^ f` on `B`
(`comp_absFrobenius`: `t ≫ absFrobenius f X = specMap (frobPow _ f) ≫ t`, where `frobPow` is that
map on `B` and `specMap` its map on spectra), and this determines it. -/
noncomputable def absFrobenius : X.left ⟶ X.left :=
  (exists_absFrobenius (l := l) f X).choose

lemma comp_absFrobenius {B : CommRingCat} (t : Spec B ⟶ X.left) :
    t ≫ absFrobenius f X =
      specMap (frobPow (natCast_eq_zero_of_over_charP (B := B) (t ≫ X.hom)) f) ≫ t :=
  (exists_absFrobenius f X).choose_spec B t

lemma absFrobenius_comm (g : X.left ⟶ Y.left) : absFrobenius f X ≫ g = g ≫ absFrobenius f Y :=
  -- Test on ring-valued points, where both sides are given by `comp_absFrobenius`.
  hom_ext_of_points (by simp [← Category.assoc, comp_absFrobenius])

lemma absFrobenius_apply (x : X.left) : absFrobenius f X x = x := by
  -- Test on the spectrum of the residue field at `x`, which has a single point.
  let t := X.left.fromSpecResidueField x
  have ht (s : Spec (X.left.residueField x)) : t s = x := X.left.fromSpecResidueField_apply x s
  calc absFrobenius f X x = (t ≫ absFrobenius f X) default := by rw [Scheme.Hom.comp_apply, ht]
    _ = x := by rw [comp_absFrobenius, Scheme.Hom.comp_apply, ht]

/-- Let `L` be a linear system (the data of a map to projective space) on a scheme `X` over a field
of characteristic `l`. The pull-back of `L` along the absolute `l ^ f`-Frobenius has class `l ^ f`
times that of `L` in the additively written Picard group. -/
lemma picClass_pull_absFrobenius {ι : Type} {L : LineBundle X.left ι} (hL : L.IsLinearSystem) :
    l ^ f • L.picClass = (L.pull (absFrobenius f X)).picClass := by
  -- `L.pow (l ^ f)` is indexed by tuples of indices. On the constant tuples its cover is that of
  -- `L` and its cocycle the `l ^ f`-th power of that of `L`.
  rw [← picClass_pow]
  -- The Frobenius does not move the charts.
  have h_opens (a : ι) : (L.pull (absFrobenius f X)).opens a = L.opens a := by
    ext x
    simp [absFrobenius_apply]
  refine picClass_eq_of_le (fun a _ ↦ a) (fun a ↦ ?_) fun a b A t ht ↦ ?_
  · exact le_iInf fun _ ↦ (h_opens a).le
  · -- `L.transition a b` is regular on `L.opens a`, so it commutes with `x ↦ x ^ l ^ f`.
    rw [h_opens] at ht
    have h_frob : L.transition a b A (t ≫ absFrobenius f X) = L.transition a b A t ^ l ^ f := by
      rw [comp_absFrobenius]
      exact hL.isRegularOn_transition a b _ t ht
    simpa [pow] using h_frob

end AbsoluteFrobenius

/-! ## Saturation and Serre's theorem on sections of powers -/

section SerreSaturation

open MvPolynomial AlgebraicGeometry Scheme CategoryTheory MorphismProperty Filter Set Submodule
  ThetaTori LineBundle Spec Limits.pullback

/-- Multiplying the value at `x` of a form of degree `m` by a member of the family `x` gives the
value of a form of degree `m + 1`. -/
lemma mul_mem_formSpan_succ {k F : Type*} {ι : Type} [CommRing k] [CommRing F] [Algebra k F]
    {x : ι → F} (j : ι) {m : ℕ} {f : F} (hf : f ∈ formSpan k x m) :
    f * x j ∈ formSpan k x (m + 1) :=
  mul_mem_mul hf (subset_span ⟨j, rfl⟩)

/-- Cancellation: let `k` be a noetherian ring, `F` a commutative `k`-algebra and `x` a finite
family in `F` with `x r = 1`. For all large `D`: if every `f * x j` is the value at `x` of a form of
degree `D + 1`, then `f` is the value at `x` of a form of degree `D`. -/
lemma eventually_mem_formSpan_of_mul {k F : Type*} {ι : Type} [CommRing k] [IsNoetherianRing k]
    [Finite ι] [CommRing F] [Algebra k F] (x : ι → F) {r : ι} (hr : x r = 1) :
    ∀ᶠ D : ℕ in atTop, ∀ f : F,
      (∀ j : ι, f * x j ∈ formSpan k x (D + 1)) → f ∈ formSpan k x D := by
  -- Idea: the ideals `I c` of the polynomial ring defined below increase with `c`, hence stabilise
  -- at some `c`. For `D ≥ c`, `f = f * x r` is the value of a homogeneous `p ∈ I (D + 1) = I c`.
  let T : ℕ → Submodule k F := formSpan k x
  -- The `n`-th coefficient of `φ p = p(X · x)` is the value at `x` of the degree `n` part of `p`.
  let φ : MvPolynomial ι k →ₐ[k] Polynomial F := aeval fun i ↦ Polynomial.X * .C (x i)
  have φ_mul_X (p : MvPolynomial ι k) (j : ι) : φ (p * X j) = φ p * Polynomial.X * .C (x j) := by
    simp [φ, mul_assoc]
  -- `p ∈ I c`: for each `n`, this value `g` has all `g * x i` in `T n`, and `g` itself lies in
  -- `T (n - 1)` if `c < n`.
  let I (c : ℕ) : Ideal (MvPolynomial ι k) :=
    { carrier := {p | ∀ n : ℕ,
        (∀ i : ι, (φ p).coeff n * x i ∈ T n) ∧ (c < n → (φ p).coeff n ∈ T (n - 1))}
      add_mem' := by simp_all [add_mul, add_mem]
      zero_mem' := by simp
      smul_mem' q p hp := by
        induction q using MvPolynomial.induction_on with
        | C a => simp_all [smul_mem, p.C_mul']
        | add q q' hq hq' => simp_all [add_mul, add_mem]
        | mul_X q j hq =>
          -- Multiplying by a variable shifts the coefficients: the new one in degree `n + 1` is
          -- the old one in degree `n` times `x j`.
          intro n
          rw [smul_eq_mul, mul_right_comm, φ_mul_X, Polynomial.coeff_mul_C]
          rcases n with _ | n
          · simp
          · rw [Polynomial.coeff_mul_X]
            exact ⟨fun i ↦ mul_mem_formSpan_succ i ((hq n).1 j), fun _ ↦ (hq n).1 j⟩ }
  have I_mono : Monotone I := fun c c' hcc' p hp n ↦
    ⟨(hp n).1, fun hn ↦ (hp n).2 (hcc'.trans_lt hn)⟩
  obtain ⟨c, hc : ∀ m, c ≤ m → I c = I m⟩ := WellFoundedGT.monotone_chain_condition ⟨I, I_mono⟩
  filter_upwards [eventually_ge_atTop c] with D hD f hf
  obtain ⟨p, hp_homog, hp_val⟩ : ∃ p : MvPolynomial ι k, p.IsHomogeneous (D + 1) ∧ p.aeval x = f :=
    (map_homogeneousSubmodule_eq_formSpan k x (D + 1)).ge (by simpa [hr] using hf r)
  have hp : φ p = .X ^ (D + 1) * algebraMap F (Polynomial F) f := by
    rw [← hp_val, ← p.aeval_algebraMap_apply (Polynomial F)]
    exact eval₂_mul_of_isHomogeneous hp_homog ..
  have hp_mem : p ∈ I (D + 1) := fun n ↦ by
    obtain rfl | hn := eq_or_ne n (D + 1) <;> simp [*, T]
  rw [← hc (D + 1) (by lia)] at hp_mem
  simpa [hp] using (hp_mem (D + 1)).2 (by lia)

/-- Saturation: let `k` be a noetherian ring, `F` a commutative `k`-algebra and `x` a finite family
in `F` with `x r = 1`. For all large `D`: if for each `i` some `f * x i ^ N` is the value at
`x` of a form of degree `D + N`, then `f` is the value at `x` of a form of degree `D`. -/
lemma eventually_mem_formSpan_of_mul_pow {k F : Type*} {ι : Type} [CommRing k]
    [IsNoetherianRing k] [Finite ι] [CommRing F] [Algebra k F] (x : ι → F) {r : ι} (hr : x r = 1) :
    ∀ᶠ D : ℕ in atTop, ∀ f : F,
      (∀ i : ι, ∃ N : ℕ, f * x i ^ N ∈ formSpan k x (D + N)) → f ∈ formSpan k x D := by
  classical
  -- Induction on the exponents `N i` reduces to the case where all of them are `1`.
  obtain ⟨c, cancel⟩ : ∃ c : ℕ, ∀ D ≥ c, ∀ f : F,
      (∀ j : ι, f * x j ∈ formSpan k x (D + 1)) → f ∈ formSpan k x D :=
    eventually_atTop.1 (eventually_mem_formSpan_of_mul x hr)
  refine eventually_atTop.2 ⟨c, fun D hD f hf ↦ ?_⟩
  -- Choose exponents `N i` with `f * x i ^ N i` a form.
  choose N hN using hf
  induction N using WellFoundedLT.induction generalizing D f with | ind N ih
  refine cancel D hD f fun j ↦ ?_
  rcases h_exp : N j with _ | n
  · simpa [h_exp] using mul_mem_formSpan_succ j (hN j)
  · -- Apply the induction hypothesis to `f * x j`, with `N j` lowered by one.
    refine ih (Function.update N j n) (update_lt_self_iff.2 (by lia)) (D + 1) (by lia) (f * x j)
      fun i ↦ ?_
    obtain rfl | hij := eq_or_ne i j
    · rw [Function.update_self, mul_assoc, ← pow_succ', add_right_comm, add_assoc, ← h_exp]
      exact hN i
    · rw [Function.update_of_ne hij, mul_right_comm, add_right_comm]
      exact mul_mem_formSpan_succ j (hN i)

/-- The transition functions of the `m`-th power of `L` are products of `m` transition functions
of `L`. -/
lemma pow_transition_apply {X : Scheme} {ι : Type} (L : LineBundle X ι) {m : ℕ} (c d : Fin m → ι)
    {B : CommRingCat} (ξ : Spec B ⟶ X) :
    (L.pow m).transition c d B ξ = ∏ a : Fin m, L.transition (c a) (d a) B ξ := by
  simp [LineBundle.pow]

/-- Let `L` be a projective embedding (finitely many coordinates) of a scheme `X` over a ring `k`,
let `t` be a section of `L ^ m`, given as a value `t c` at `B`-valued points in each chart `c` (an
`m`-tuple of indices), regular and compatible with the transition functions (`IsSection`), and let
`ξ` be a `B`-valued point over `k` in the charts `i` and `j`, with affine coordinates
`x l = L.transition i l (ξ)`. Then for some `N`, the value of `t` at `ξ` in the chart `i` times
`x j ^ N` is the value at `x` of a form of degree `m + N`. -/
lemma exists_mul_pow_mem_formSpan_of_isSection {k ι : Type} [CommRing k] [Finite ι]
    {X : Over (Spec (CommRingCat.of k))} {L : LineBundle X.left ι} (hL : L.IsProjEmbedding X.hom)
    {m : ℕ} {t : (Fin m → ι) → PointFn X.left} (ht : (L.pow m).IsSection t)
    {B : CommRingCat} [Algebra k B] {ξ : Spec B ⟶ X.left}
    (h_alg : algebraMap k B = (Spec.preimage (ξ ≫ X.hom)).hom) {i j : ι}
    (hi : LandsIn ξ (L.opens i)) (hj : LandsIn ξ (L.opens j)) :
    ∃ N : ℕ, t (fun _ ↦ i) B ξ * L.transition i j B ξ ^ N ∈
      formSpan k (fun l : ι ↦ L.transition i l B ξ) (m + N) := by
  obtain ⟨t_reg, t_glue⟩ := ht
  let x : ι → B := fun l ↦ L.transition i l B ξ
  let y : ι → B := fun l ↦ L.transition j l B ξ
  -- The chart `j` is affine and its sections are the polynomials `ψ P` in the coordinates
  -- `transition j l`, whose values at `ξ` are the `y l`.
  obtain ⟨-, ψ, ψ_surj, -, ψ_ev⟩ := hL.exists_affine_chart j
  obtain ⟨P, hP⟩ : ∃ P : MvPolynomial ι k, ∀ (C : CommRingCat) (u : Spec C ⟶ X.left),
      LandsIn u (L.opens j) → PointFn.ofSection (ψ P) C u = t (fun _ ↦ j) C u :=
    ψ_surj.exists.1 ((t_reg fun _ ↦ j).mono le_iInf_const).exists_ofSection
  -- The value of `t` in the chart `i` is `x j ^ m` times its value in the chart `j`.
  have ht_i : t (fun _ ↦ i) B ξ = x j ^ m * aeval y P := by
    rw [t_glue _ (fun _ ↦ j) B ξ ((landsIn_iInf ξ).2 fun _ ↦ hi) ((landsIn_iInf ξ).2 fun _ ↦ hj),
      ← hP B ξ hj, ψ_ev hj P, aeval_def, h_alg, pow_transition_apply, Fin.prod_const, coe_eval₂Hom]
  -- The `l`-th coordinate is a section: compare its values in the charts `i` and `j`.
  have h_cocycle : x = fun l ↦ x j * y l :=
    funext fun l ↦ (hL.isLinearSystem.isSection l).right i j B ξ hi hj
  -- Homogenise `P` to a form `Q` of degree `D = m + deg P`; then `Q(x) = x j ^ D * P(y)`.
  obtain ⟨Q, hQ, hQP⟩ :=
    exists_homogenization (N := m + P.totalDegree) (isHomogeneous_X k j) P le_add_self
  have hQ_val : aeval x Q = t (fun _ ↦ i) B ξ * x j ^ P.totalDegree :=
    calc aeval x Q = aeval (fun l ↦ x j * y l) Q := by rw [← h_cocycle]
      _ = x j ^ (m + P.totalDegree) * aeval y Q := eval₂_mul_of_isHomogeneous hQ _ (x j) y
      _ = t (fun _ ↦ i) B ξ * x j ^ P.totalDegree := by
        rw [hQP (aeval y) (by simp [y, transition_self _ _ _ _ hj]), ht_i, pow_add, mul_right_comm]
  exact ⟨P.totalDegree, (map_homogeneousSubmodule_eq_formSpan k x _).le ⟨Q, hQ, hQ_val⟩⟩

/-- Let `ξ` be a quasi-compact scheme-theoretically dominant ring-valued point of `X` in the chart
`i` of a line bundle `L`. A global section of `L` whose value at `ξ` in this chart is zero is
zero. -/
lemma eq_zero_of_apply_eq_zero_of_dominant {k ι : Type} [CommRing k]
    {X : Over (Spec (CommRingCat.of k))} {L : LineBundle X.left ι} {B : CommRingCat}
    (ξ : Spec B ⟶ X.left) [IsSchemeTheoreticallyDominant ξ] [QuasiCompact ξ] {i : ι}
    (hi : LandsIn ξ (L.opens i)) (s : L.H0 k) (hs : (s : ι → PointFn X.left) i B ξ = 0) :
    s = 0 := by
  obtain ⟨s, ⟨s_reg, s_glue⟩, _⟩ := s
  refine H0_ext fun {c} h_reg h_zero ↦
    h_reg.ext_of_dominant_of_isOpenCover ξ h_zero isOpenCover_top fun _ C u hu _ ↦ ?_
  -- Over `ξ` the section vanishes in the chart `i`, hence in every chart.
  obtain ⟨χ, rfl⟩ := map_surjective u
  change s c C (Spec.map χ ≫ ξ) = 0
  rw [s_glue c i C _ hu (hi.comp _), s_reg _ χ ξ hi, show s i B ξ = 0 from hs, map_zero, mul_zero]

/-- A case of Serre's theorem, surjectivity half. Let `N` be a projective embedding (finitely many
coordinates) of an integral scheme `A` over a field `F`, and `p : A' ⟶ A` the base change along
`b : Spec k ⟶ Spec F`, with `k` noetherian. For all large `m`, the global sections of `(p^* N) ^ m`
are spanned over `k` by its coordinates `coordSection h`, where `h` is any proof that it is a linear
system. These coordinates are indexed by `m`-tuples of indices, each giving a monomial of degree `m`
in the coordinates of `p^* N`. -/
lemma eventually_span_coordSection {k F ι : Type} [CommRing k] [IsNoetherianRing k] [Finite ι]
    [Field F] {A : Over (Spec (CommRingCat.of F))} [IsIntegral A.left] {N : LineBundle A.left ι}
    (A' : Over (Spec (CommRingCat.of k))) (hN : N.IsProjEmbedding A.hom) {p : A'.left ⟶ A.left}
    {b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of F)} (h_pb : IsPullback p A'.hom A.hom b) :
    ∀ᶠ m : ℕ in atTop, ∀ h : ((N.pull p).pow m).IsLinearSystem,
      span k (range (coordSection h)) = ⊤ := by
  -- Let `ξ : Spec B ⟶ A'` be the base change of the generic point `ζ` of `A`, in the chart `i`.
  -- Evaluation at `ξ` embeds `H⁰` in `B`, and the values of the coordinates span the forms of
  -- degree `m` in the `x j = transition i j (ξ)`. A section times a power of any `x j` is a form,
  -- so by `eventually_mem_formSpan_of_mul_pow` the section itself is one.
  let η : A.left := genericPoint A.left
  let ζ : Spec (A.left.residueField η) ⟶ A.left := A.left.fromSpecResidueField η
  have : IsDominant ζ :=
    ⟨by simp [DenseRange, ζ, η, dense_iff_closure_eq, range_fromSpecResidueField]⟩
  have : IsSchemeTheoreticallyDominant ζ := .of_isDominant ζ
  have : IsAffineHom p := of_isPullback h_pb.flip inferInstance
  have : Flat p := of_isPullback h_pb.flip inferInstance
  obtain ⟨B, φ, ξ, hξ : IsPullback ξ (Spec.map φ) p ζ⟩ := exists_isPullback_SpecMap p ζ
  -- `ξ` is scheme-theoretically dominant by flat base change.
  have : IsSchemeTheoreticallyDominant ξ := by
    rw [← hξ.isoPullback_hom_fst]
    infer_instance
  have : QuasiCompact ξ := of_isPullback hξ.flip inferInstance
  obtain ⟨i, hζi⟩ := N.exists_landsIn ζ
  have hi : LandsIn ξ ((N.pull p).opens i) := by
    change LandsIn (ξ ≫ p) (N.opens i)
    simpa only [hξ.w] using hζi.comp _
  let : Algebra k B := (Spec.preimage (ξ ≫ A'.hom)).hom.toAlgebra
  -- `x` gives the affine coordinates of `ξ` in the chart `i`.
  let x (j : ι) : B := (N.pull p).transition i j B ξ
  have hx (j : ι) : x j = φ (N.transition i j _ ζ) := (congrArg (N.transition i j B) hξ.w).trans
    (hN.isLinearSystem.isRegularOn_transition i j φ ζ hζi)
  have hN' : (N.pull p).IsProjEmbedding A'.hom := hN.of_isPullback h_pb
  filter_upwards [eventually_mem_formSpan_of_mul_pow (k := k) x (transition_self _ _ _ _ hi)] with
    m h_sat h
  -- `ev` is evaluation at `ξ` in the chart `i`.
  let ev : ((N.pull p).pow m).H0 k →ₗ[k] B :=
    { toFun s := (s : (Fin m → ι) → PointFn A'.left) (fun _ ↦ i) B ξ
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  -- Since `ξ` is scheme-theoretically dominant, a section vanishing at `ξ` is zero.
  have ev_inj : Function.Injective ev := (injective_iff_map_eq_zero _).2
    (eq_zero_of_apply_eq_zero_of_dominant ξ ((landsIn_iInf ξ).2 fun _ ↦ hi))
  -- The coordinate indexed by an `m`-tuple evaluates to the corresponding monomial in `x`.
  have h_forms : formSpan k x m ≤ span k (ev '' range (coordSection h)) := by
    refine (span_pow ..).le.trans (span_mono fun y hy ↦ ?_)
    obtain ⟨g, hg, rfl⟩ := mem_pow_iff_prod.1 hy
    choose c hc using hg
    have h_monomial : ev (coordSection h c) = ∏ a : Fin m, x (c a) := pow_transition_apply _ _ c ξ
    exact ⟨coordSection h c, mem_range_self c, by simp [h_monomial, hc]⟩
  refine eq_top_iff'.2 fun ⟨t, ht, _⟩ ↦ ?_
  suffices h_form : t (fun _ ↦ i) B ξ ∈ formSpan k x m from
    (apply_mem_span_image_iff_mem_span ev_inj).1 (h_forms h_form)
  -- By saturation it is enough that for each `j` some `t(ξ) * x j ^ N` is a form.
  refine h_sat _ fun j ↦ ?_
  by_cases h_zero : N.transition i j _ ζ = 0
  · -- At such `j` we have `x j = 0`.
    exact ⟨1, by simp [hx, h_zero]⟩
  -- Otherwise `x j` is a unit, so `ξ` lies in the chart `j` as well.
  have hx_unit : IsUnit (x j) := by simpa only [hx] using (Ne.isUnit h_zero).map φ.hom
  have hj : LandsIn ξ ((N.pull p).opens j) :=
    ((hN'.isLinearSystem.isHomogeneousCoords_transition hi).landsIn_iff_isUnit j).mpr hx_unit
  exact exists_mul_pow_mem_formSpan_of_isSection hN' ht rfl hi hj

end SerreSaturation

end New.Variety

/-! ## Finite products of proper schemes -/

section ProperProduct

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

/-- A finite product of proper schemes over `S` is proper over `S`. -/
instance New.isProper_pi {S : Scheme} {J : Type*} [Finite J] {A : J → Over S}
    [h : ∀ l : J, IsProper (A l).hom] : IsProper (∏ᶜ A).hom := by
  -- Form the product in the category of proper schemes over `S`; the forgetful functor to
  -- `Over S` preserves it.
  let P : MorphismProperty Scheme := @IsProper
  have : P.HasOfPostcompProperty @IsProper :=
    HasOfPostcompProperty.of_le P @IsSeparated @IsProper.toIsSeparated
  let A' (l : J) : P.Over ⊤ S := ⟨A l, h l⟩
  let e := PreservesProduct.iso (Over.forget P ⊤ S) A'
  exact (P.over_iso_iff e).mp (∏ᶜ A').prop

end ProperProduct

/-!
## Projective embeddings of composites and products

The property `New.Variety.HasProjEmbedding` (proper, with a finite linear system that separates
points over the base) passes to composites.
-/

namespace New.Variety

open CategoryTheory AlgebraicGeometry LineBundle Limits

/-- If `A` has a projective embedding over `X`, and `X` has one over `S`, then `A` has one over `S`,
given by the Segre product of the two linear systems. -/
instance {X S : Scheme} {s : X ⟶ S} {A : Over X} [hA : HasProjEmbedding A.hom]
    [hs : HasProjEmbedding (X := X) (S := S) s] :
    HasProjEmbedding ((Over.map s).obj A).hom := by
  obtain ⟨⟨hA⟩, ⟨hs⟩⟩ := And.intro hA hs
  exact ⟨hA.mul hs⟩

/-- If an `S`-scheme `W` has a closed immersion over `S` into the fibre product of finitely many
`S`-schemes `A l`, each with a projective embedding over `S` (proper, with a finite linear system
that separates points), then `W` has a projective embedding over `S`. -/
lemma HasProjEmbedding.of_isClosedImmersion_pi {S : Scheme} {ι : Type} {W : Over S} [Finite ι]
    {A : ι → Over S}
    (i : W ⟶ ∏ᶜ A) [IsClosedImmersion i.left] [h : ∀ l : ι, HasProjEmbedding (A l).hom] :
    HasProjEmbedding W.hom := by
  choose κ N _ hN using fun l ↦ (hasProjEmbedding_iff (A l).hom).1 (h l)
  have := Fintype.ofFinite ι
  -- The Segre product embeds the fibre product; restrict it to the closed subscheme `W`.
  have h_prod : (LineBundle.pi fun l ↦ (N l).pull (Pi.π A l).left).IsProjEmbedding (∏ᶜ A).hom :=
    isProjEmbedding_pi (Pi.π A) hN (Pi.hom_ext _ _)
  rw [← i.w]
  exact ⟨h_prod.comp i.left⟩

end New.Variety
