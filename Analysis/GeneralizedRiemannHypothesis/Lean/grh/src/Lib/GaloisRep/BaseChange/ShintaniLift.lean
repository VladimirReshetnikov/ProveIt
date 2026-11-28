import Lib.GaloisRep.BaseChange.PrimeDegreeTransfer
import Lib.LocalGL.Shintani.LiftingGreenCharacters

/-!
# Base change at an inert place carries a label to its Shintani lift

Base change along a step `E'/E` (`New.IsStep E' μ`, which among other things makes `[E' : E]` prime)
at a place `w` of `E` that is split over `E⁺` and inert in `E'`: the local matching comes from
Shintani lifting for `GL n` over the residue fields.

* `New.inflateConj`: the conjugate of a function on `GL n` of the residue field, pulled back along
  reduction to `GL n 𝒪_w` and extended by zero to `GL n` of the completion.
* `New.exists_representation_heckeFun_inflateConj`: on forms of principal level at `w`, its Hecke
  operator is the action of a group algebra element of the finite group.
* `New.isLocalMatching_shintani`: inflated `Ξ` and, for some `φ`, inflated `g ↦ S ⟨g, φ⟩` are
  matching local data, where `S` is a class function on the semidirect product that descends to `Ξ`.
* `New.exists_baseChange_hasLabel`: a form with label `Ξ` at `w` has a weak base change with the
  lift `Ξ'` as label at the place `u` above `w`.

`New.localCongruence n w 0` is the kernel of reduction of `GL n 𝒪_w`; `New.HasLabel f hw χ` says
that this kernel fixes `f` and that `∑ conj (χ x) x` does not kill `f`.

Notions from other files:
* `New.Lift`: F lifts to F' over Z if, for every m, one Z-combination of characters of GL_m(k') ⋊
  Gal(k'/k) descends to both F (over k) and F' (over k').
* `New.IsLocalMatching`: Retracts G, G' of the adelic groups above a finite set of places,
  compatible levels, and bi-invariant functions that form matching pairs at a level where σ-cocycles
  split.

## Relation to the literature

Known; see `Lib.GaloisRep.BaseChange.PrimeDegreeTransfer` for sources.
-/

namespace New

open NumberField Representation Function ComplexConjugate FiniteField Module
  SemidirectProduct algebraMap

attribute [local instance low] Fintype.ofFinite

variable {E E' n : Type} [Field E] [CMType E] [Field E'] [Fintype n] [DecidableEq n]
  {w : FinPlace E}

open scoped Classical in
/-- The inflation of `χ`, conjugated: the function on `GL n (LocField w)` that sends `g` in
`GL n 𝒪_w` (`intGL n Valued.v.integer`) to `conj (χ (reduceGL g))`, the complex conjugate of `χ`
at the reduction of `g` modulo `w`, and is `0` outside `GL n 𝒪_w`. -/
noncomputable def inflateConj (χ : GL n (ResField w) → ℂ) (g : GL n (LocField w)) : ℂ :=
  if h : g ∈ intGL n Valued.v.integer then conj (χ (reduceGL ⟨g, h⟩)) else 0

/-- Let `K` be the forms of weight `κ` in `stdSpace E n` that are fixed by the kernel of reduction
at the split place `w`. On `K ⊓ W`, for each subrepresentation `W`, the finite group
`GL n (ResField w)` acts by some `ρ` such that the following holds for every `χ` and `v`, with `x`
the action of `∑ conj (χ g) g` on `v`. (a) The Hecke operator of `inflateConj χ` (which is
`conj (χ (g mod w))` on `GL n 𝒪_w` and `0` elsewhere) sends `v` to `x`. (b) `v` has label `χ`
(`New.HasLabel`: `v` is fixed by the reduction kernel and `∑ conj (χ g)` times the translates of `v`
by lifts of `g` is nonzero) exactly when `x ≠ 0`. -/
lemma exists_representation_heckeFun_inflateConj (hw : w.IsSplit) {κ : Weight E} :
    let π := ((stdSpace E n).formTranslation κ).comp (ofSplitPlace hw)
    let K := levelSpace π (localCongruence n w 0)
    ∀ W : Subrepresentation π, ∃ ρ : Representation ℂ (GL n (ResField w)) ↥(K ⊓ W.toSubmodule),
      ∀ (χ : GL n (ResField w) → ℂ) (v : ↥(K ⊓ W.toSubmodule)),
      let x := ρ.asAlgebraHom (groupAlgElem fun g : GL n (ResField w) ↦ conj (χ g)) v
      -- (a)
      heckeFun π (localCongruence n w 0) (inflateConj χ) v = x ∧
      -- (b)
      (HasLabel v.val.val hw χ ↔ x ≠ 0) := by
  classical
  -- `GL n 𝒪_w` acts on `K ⊓ W` and the kernel of reduction acts trivially, so the action descends
  -- to `ρ`. Both claims unfold to sums over lifts of the elements of `GL n (ResField w)`.
  intro π K W
  let π₀ : Representation ℂ (intGL n Valued.v.integer) _ :=
    π.comp (intGL n Valued.v.integer).subtype
  have hK : K = invariants (π₀.comp reduceGL.ker.subtype) := by
    aesop (add simp mem_localCongruence_zero)
  have h_stable (k : intGL n Valued.v.integer) : K ⊓ W.1 ≤ (K ⊓ W.1).comap (π₀ k) :=
    fun v ⟨hv_K, hv_W⟩ ↦ ⟨hK.ge (le_comap_invariants _ _ k (hK.le hv_K)), W.2 _ hv_W⟩
  let π₁ : intGL n Valued.v.integer →* (↥(K ⊓ W.1) →ₗ[ℂ] ↥(K ⊓ W.1))ˣ :=
    (subrepresentation π₀ _ h_stable).asGroupHom
  -- the kernel of reduction acts trivially on `K`
  have h_ker : reduceGL.ker ≤ π₁.ker := fun k hk ↦ by
    ext v : 3
    exact hK.le v.2.1 ⟨k, hk⟩
  let ρ : Representation ℂ (GL n (ResField w)) ↥(K ⊓ W.1) :=
    (Units.coeHom _).comp (reduceGL.liftOfSurjective reduceGL_surjective ⟨π₁, h_ker⟩)
  let lift : GL n (ResField w) → GL n (LocField w) := Subtype.val ∘ surjInv reduceGL_surjective
  refine ⟨ρ, fun χ v ↦ ?_⟩
  obtain ⟨hv_K, -⟩ := Submodule.mem_inf.mp v.prop
  have h_sum : (ρ.asAlgebraHom (groupAlgElem fun g ↦ conj (χ g)) v).1 =
      ∑ x, conj (χ x) • π (lift x) v := by
    simp [asAlgebraHom_eq_sum, Subtype.ext_iff]
    -- `ρ x v` is `π (lift x) v` by the definition of `ρ`
    rfl
  -- the kernel of reduction fixes `v`, so the first half of `HasLabel` holds
  have h_fixed : ∀ k : intGL n Valued.v.integer, reduceGL k = 1 →
      rightRegular ℂ (Gf E n) (WeylIndex n κ.1 → ℂ) (ofSplitPlace hw k.val) v.val.val = v.val.val :=
    fun k hk ↦ congrArg Subtype.val (hK.le hv_K ⟨k, hk⟩)
  refine ⟨?_, (and_iff_right h_fixed).trans ?_⟩
  · -- The cosets of the lifts modulo `localCongruence n w 0` are distinct and cover `GL n 𝒪_w`,
    -- off which `inflateConj χ` is zero.
    have h_right : ∀ (g : GL n (LocField w)) (k : localCongruence n w 0),
        inflateConj χ (g * k) = inflateConj χ g := by
      simp +contextual [inflateConj, mem_localCongruence_zero, mul_mem_cancel_right,
        ← MulMemClass.mk_mul_mk]
    have h_inj : Set.InjOn (fun x ↦ (lift x : GL n (LocField w) ⧸ localCongruence n w 0))
        (SetLike.coe (⊤ : Finset (GL n (ResField w)))) := by
      simp +contextual [lift, surjInv_eq, Set.InjOn, inv_mul_eq_one, QuotientGroup.eq,
        ← InvMemClass.coe_inv, -Subgroup.coe_inv, mem_localCongruence_zero, ← MulMemClass.mk_mul_mk,
        mul_mem_cancel_left]
    have h_cover : ∀ g : GL n (LocField w), inflateConj χ g ≠ 0 →
        ∃ x ∈ (⊤ : Finset (GL n (ResField w))),
          (lift x : GL n (LocField w) ⧸ localCongruence n w 0) = g := by
      simp +contextual [lift, surjInv_eq, inv_mul_eq_one, QuotientGroup.eq,
        ← InvMemClass.coe_inv, -Subgroup.coe_inv, mem_localCongruence_zero, ← MulMemClass.mk_mul_mk,
        mul_mem_cancel_left, inflateConj]
    obtain ⟨-, h_eq⟩ := heckeFun_eq_sum (r := lift) (s := ⊤) h_right hv_K h_inj h_cover
    simp [h_eq, lift, surjInv_eq, h_sum, inflateConj]
  · simp [Subtype.ext_iff, h_sum, finsum_eq_sum_of_fintype]
    -- `π (lift x)` is right translation by `ofSplitPlace hw (lift x)` (definition of
    -- `formTranslation`)
    rfl

/-- Reduction commutes with the map of completions induced by `ι`, if `ψ` is the map of residue
fields that `ι` induces on global integers. -/
lemma reduceGL_map_locMap [CMType E'] {u : FinPlace E'} {ι : E →+* E'} (he : u.comap ι = w)
    (ψ : ResField w →+* ResField u)
    (hψ : ∀ x : 𝓞 E, ψ (algebraMap (𝓞 E) (ResField w) x) = ↑(RingOfIntegers.mapRingHom ι x : 𝓞 E'))
    (g : GL n (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w))
    (hg : (Matrix.GeneralLinearGroup.map (locMap ι he)) g ∈ intGL n Valued.v.integer) :
    reduceGL ⟨Matrix.GeneralLinearGroup.map (n := n) (locMap ι he) g, hg⟩ =
      (reduceGL ⟨g, (map_locMap_mem_intGL_iff he).mp hg⟩).map ψ := by
  -- Take a global integer `x` congruent to the entry `g i j` at `w`. Both sides are the class of
  -- the image of `x` at `u`, since `locMap` pulls the valuation at `u` back to one equivalent to
  -- the valuation at `w`.
  ext i j
  obtain ⟨x, hx⟩ := algebraMap_ResField_surjective w
    (reduceGL ⟨g, (map_locMap_mem_intGL_iff he).1 hg⟩ i j)
  have h_ψx : ψ (reduceGL ⟨g, (map_locMap_mem_intGL_iff he).1 hg⟩ i j) =
      ↑(RingOfIntegers.mapRingHom ι x : 𝓞 E') := (congrArg ψ hx).symm.trans (hψ x)
  refine (h_ψx.trans ?_).symm
  erw [residue_eq_iff_valuation_sub_lt_one] at hx ⊢
  simpa using! ((isEquiv_comap_locMap ι he).lt_one_iff_lt_one (x := (x : E) - _)).2 hx

variable [Algebra E E'] [CMTypeOver E E'] {u : FinPlace E'}
  {μ : (𝔸f E)ˣ →* ℂˣ} [hμ : IsStep E' μ]
  (hw : star w ≠ w) (hu : star u ≠ u)
  (h_unique : ∀ u' : FinPlace E', FinPlace.below E u' = w ↔ u' = u)
  (hμ_trivial : ∀ x : (LocField w)ˣ, μ (locIdele w x) = 1) [Algebra (ResField w) (ResField u)]
  (h_residue : ∀ x : 𝓞 E, ((x : ResField w) : ResField u) = (x : 𝓞 E'))
  (h_degree : finrank (ResField w) (ResField u) = finrank E E') {Ξ : Hall (ResField w)}

include h_unique hμ_trivial h_residue h_degree

omit h_unique hμ_trivial h_residue h_degree in
/-- The Galois action on `GL n` of the residue field applies the automorphism to the entries. -/
private lemma galActionGL_apply {k k' : Type} [Field k] [Field k'] [Algebra k k'] [Finite k]
    [Finite k'] (φ : Gal(k'/k)) (x : GL n k') :
    galActionGL k k' n φ x = Matrix.GeneralLinearGroup.map (φ : k' →+* k') x :=
  rfl

omit h_unique hμ_trivial h_residue h_degree in
/-- Let `σ` in `Gal(E'/E)` fix the finite place `u` of `E'` and induce `φ` on the residue field of
`u`, where `φ` is an automorphism over the residue field of the place `w` of `E`. Let `a` be an
element of the finite adelic unitary group over `E'` whose component at `u` lies in `GL n 𝒪_u`.
Then the twisted norm `N = a · σ(a) ⋯ σ^{m-1}(a)` also has its component at `u` in `GL n 𝒪_u`, and
in `GL n (ResField u) ⋊ Gal(ResField u/ResField w)` the `m`-th power of (reduction of `a`, `φ`) is
(reduction of `N`, `φ ^ m`). -/
lemma exists_mk_reduceGL_pow_eq_mk_reduceGL_twistedNorm {σ : Gal(E'/E)} (hσ_u : u.comap σ = u)
    {φ : Gal(ResField u/ResField w)}
    (hσ : ∀ x : 𝓞 E', φ (algebraMap (𝓞 E') (ResField u) x) = algebraMap (𝓞 E') (ResField u) (σ • x))
    (a : Gf E' n) (ha : a.atPlace u ∈ intGL n Valued.v.integer) (m : ℕ) :
    ∃ h_norm : (twistedNorm (galoisGf σ) m a).atPlace u ∈ intGL n Valued.v.integer,
      (⟨reduceGL ⟨a.atPlace u, ha⟩, φ⟩ : GalSemidirect (ResField w) (ResField u) n) ^ m =
        ⟨reduceGL ⟨(twistedNorm (galoisGf σ) m a).atPlace u, h_norm⟩, φ ^ m⟩ := by
  -- The norm of length `m + 1` is `a · σ(N)`, with `N` the norm of length `m`. Reduction at `u`
  -- turns `σ` into `φ`, and `⟨x, φ⟩ * ⟨y, φ ^ m⟩ = ⟨x * φ y, φ ^ (m + 1)⟩`.
  induction m with
  | zero =>
    have h_one : (twistedNorm (galoisGf σ) 0 a).atPlace u = 1 := by simp [twistedNorm]
    have h_int : (twistedNorm (galoisGf σ) 0 a).atPlace u ∈ intGL n Valued.v.integer := by
      rw [h_one]
      exact one_mem _
    have h_reduce : reduceGL ⟨(twistedNorm (galoisGf σ) 0 a).atPlace u, h_int⟩ = 1 :=
      (congrArg reduceGL (Subtype.ext h_one)).trans (map_one reduceGL)
    refine ⟨h_int, ?_⟩
    rw [pow_zero, pow_zero, h_reduce]
    rfl
  | succ m ih =>
    obtain ⟨hN_int, h_pow⟩ := ih
    set N : GL n (LocField u) := (twistedNorm (galoisGf σ) m a).atPlace u
    let σN : GL n (LocField u) := Matrix.GeneralLinearGroup.map (locMap σ hσ_u) N
    have hσN_int : σN ∈ intGL n Valued.v.integer := (map_locMap_mem_intGL_iff hσ_u).2 hN_int
    have hσN_reduce : reduceGL ⟨σN, hσN_int⟩ = (reduceGL ⟨N, hN_int⟩).map φ :=
      reduceGL_map_locMap hσ_u φ hσ N hσN_int
    have h_succ : (twistedNorm (galoisGf σ) (m + 1) a).atPlace u = a.atPlace u * σN := by
      rw [twistedNorm_succ', map_mul, atPlace_galoisGf (h := hσ_u)]
    have h_int : (twistedNorm (galoisGf σ) (m + 1) a).atPlace u ∈ intGL n Valued.v.integer := by
      rw [h_succ]
      exact mul_mem ha hσN_int
    have h_reduce : reduceGL ⟨(twistedNorm (galoisGf σ) (m + 1) a).atPlace u, h_int⟩ =
        reduceGL ⟨a.atPlace u, ha⟩ * (reduceGL ⟨N, hN_int⟩).map φ := by
      rw [← hσN_reduce, ← map_mul]
      exact congrArg reduceGL (Subtype.ext h_succ)
    refine ⟨h_int, ?_⟩
    rw [pow_succ', h_pow, h_reduce, pow_succ', SemidirectProduct.mul_def, galActionGL_apply]

omit hμ_trivial h_residue h_degree in
include hμ in
/-- Let `u` be the only place of `E'` above `w`, and let `φ`, the Frobenius of the residue
extension at `u`, be nontrivial. Then some `σ ≠ 1` in `Gal(E'/E)` fixes `u`, lies outside the
inertia group of `u`, and induces `φ` on the residue field of `u`. -/
private lemma exists_ne_one_and_frobeniusAlgEquivOfAlgebraic_apply_eq
    {φ : Gal(ResField u/ResField w)}
    (hφ : φ = frobeniusAlgEquivOfAlgebraic (ResField w) (ResField u)) (hφ_ne : φ ≠ 1) :
    ∃ σ : Gal(E'/E), σ ≠ 1 ∧ u.comap σ = u ∧ σ ∉ Ideal.inertia Gal(E'/E) u.asIdeal ∧
      ∀ x : 𝓞 E', φ (algebraMap (𝓞 E') (ResField u) x) =
        algebraMap (𝓞 E') (ResField u) (σ • x) := by
  obtain rfl : FinPlace.below E u = w := (h_unique u).2 rfl
  obtain ⟨σ, h_frob⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 E) Gal(E'/E) u.1
  have hσ (x : 𝓞 E') : φ (algebraMap _ _ x) = algebraMap _ _ (σ • x) := by
    rw [hφ, eq_comm]
    simpa [card_ResField, ← Nat.card_eq_fintype_card, ← algebraMap_ResField_eq_zero,
      sub_eq_zero] using! h_frob x
  -- `φ ≠ 1`, so `σ` moves some residue class
  have h_moves : ∃ x : 𝓞 E', algebraMap _ (ResField u) (σ • x) ≠ algebraMap _ _ x := by
    simpa [hσ, AlgEquiv.ext_iff, (algebraMap_ResField_surjective u).forall] using hφ_ne
  have hσ_ne : σ ≠ 1 := by
    rintro rfl
    simp at h_moves
  have h_inertia : σ ∉ Ideal.inertia Gal(E'/E) u.asIdeal := by
    simpa [sub_eq_zero, ← algebraMap_ResField_eq_zero]
  exact ⟨σ, hσ_ne, (h_unique _).1 (below_comap σ u), h_inertia, hσ⟩

/-- Let `E'/E` be a step with `μ` (`New.IsStep`) and let `w` be split with `μ` trivial on its
ideles. Let `u` be the only place above `w`, split, with residue field of degree `[E' : E]` over
that of `w`, and let `Ξ` be a function on similarity classes of matrices over `ResField w`
(`New.Hall`). If `S` on `GalSemidirect (ResField w) (ResField u) n` is a class function that
descends to `Ξ` (so `S ⟨a, φ⟩ = Ξ.evalGL b` when `φ ≠ 1` and `⟨a, φ⟩ ^ orderOf φ` is `inl` of `b`
mapped to `ResField u`), then for some `φ` in the residue Galois group the inflations of the complex
conjugates of `Ξ` and of `S ⟨·, φ⟩` are matching local data (`New.IsLocalMatching`) above `{w}`.
Here `GL n` at `w` and at `u` is embedded by `New.ofSplitPlace`, at level `≡ 1` mod the maximal
ideal. -/
lemma isLocalMatching_shintani {S : GalSemidirect (ResField w) (ResField u) n → ℂ}
    (hS : IsClassFunction S) (h_lf : DescendsTo S Ξ) :
    ∃ φ : Gal(ResField u/ResField w),
      IsLocalMatching μ {w} (ofSplitPlace hw) (ofSplitPlace hu) (localCongruence n w 0)
        (localCongruence n u 0) {()} (fun _ ↦ inflateConj Ξ.evalGL)
        fun _ ↦ inflateConj fun g : GL n (ResField u) ↦ S ⟨g, φ⟩ := by
  classical
  -- Take for `φ` the Frobenius of the residue extension and for `σ` a Frobenius at `u` lifting
  -- it. Reduction carries twisted conjugation and twisted norms to conjugation and powers in the
  -- coset of `φ`, where `S` is a class function that lifts `Ξ`.
  obtain rfl : FinPlace.below E u = w := (h_unique u).2 rfl
  let φ := frobeniusAlgEquivOfAlgebraic (ResField (u.below E)) (ResField u)
  have h_order : orderOf φ = finrank E E' :=
    (orderOf_frobeniusAlgEquivOfAlgebraic _ _).trans h_degree
  have hφ_ne : φ ≠ 1 := by simpa [← h_order] using hμ.out.ne_one
  obtain ⟨σ, hσ_ne, hσ_u, h_inertia, hσ⟩ :=
    exists_ne_one_and_frobeniusAlgEquivOfAlgebraic_apply_eq h_unique (φ := φ) rfl hφ_ne
  obtain ⟨h_retr, h_retr', h_level⟩ := isLocalRetraction_ofSplitPlace n h_unique hu hw
  -- The place is unramified, so the level `m` of `exists_isBaseChangeLevel` is the maximal level
  -- `K` at `u`. Hence cocycles split at `K` (`h_coh`), and the indicator functions of `K` form a
  -- matching pair (`h_pair`).
  let K : Subgroup (Gf E' n) := (intGL n Valued.v.integer).comap (Gf.atPlace u)
  have h_unram : IsStepUnramifiedAt E' μ (u.below E) := fun u' hu' ↦ by
    obtain rfl : u' = u := (h_unique u').1 hu'
    exact ⟨⟨σ, h_inertia⟩, fun x hx ↦ by simp [hμ_trivial]⟩
  obtain ⟨m, hm⟩ := exists_isBaseChangeLevel (n := n) hσ_ne isOpen_stdLevel
  have hK : K = localLevel n (placesAbove E' {u.below E}) m := by
    refine h_level.symm.trans (Subgroup.ext fun g ↦ forall₂_congr fun u' hu' ↦ ?_)
    rw [hm.eq_localIntGL _ h_unram (by simp) u' hu']
  obtain ⟨-, -, h_coh, -, h_pair⟩ := hm.isMatchingLevel {u.below E}
  rw [← hK] at h_coh h_pair
  refine ⟨φ, σ, hσ_ne, Gf.atPlace _, Gf.atPlace u,
    ⟨fun _ ↦ ?_, h_retr, h_retr', Set.finite_singleton _, ?_⟩, ?_,
    isOpen_localCongruence.preimage_of_continuous, K, ⟨fun _ hk ↦ hk.1, h_level.ge⟩, h_coh,
    fun _ _ ↦ ⟨fun (k : Gf E' n) hk (δ : Gf E' n) ↦ ?_, fun P hP hPσ ↦ ?_⟩⟩
  · -- Inflated functions are bi-invariant under the principal level, with compact support.
    constructor <;>
      exact ⟨(finite_quotient_image_of_isCompact isOpen_localCongruence
        (isCompact_localIntGL _)).subset
        fun q _ ↦ ⟨_, by aesop (add simp inflateConj), q.out_eq⟩,
        by simp +contextual [mem_localCongruence_zero, inflateConj,
          mul_mem_cancel_right, ← MulMemClass.mk_mul_mk, mul_mem_cancel_left]⟩
  · -- The principal level at `u` is stable under `σ`,
    simp +contextual [hσ_u, reduceGL_map_locMap hσ_u φ hσ, EmbeddingLike.map_eq_one_iff, eq_ite_iff,
      Matrix.GeneralLinearGroup.ext_iff, Matrix.one_apply, atPlace_galoisGf,
      mem_localCongruence_zero, map_locMap_mem_intGL_iff]
  · -- and its preimage over `E` is the principal level below.
    simp +contextual [SetLike.ext_iff, reduceGL_map_locMap _ _ h_residue, eq_ite_iff,
      Matrix.GeneralLinearGroup.ext_iff, Matrix.one_apply, atPlace_baseChangeGf,
      mem_localCongruence_zero, map_locMap_mem_intGL_iff]
  · -- Twisted conjugation by `x` is conjugation by `inl x⁻¹` on the coset of `φ`.
    have h_conj (δ x : GL n (ResField u)) : S ⟨x⁻¹ * δ * x.map φ, φ⟩ = S ⟨δ, φ⟩ := hS ⟨δ, φ⟩ (inl _)
    have h_inv (a : GL n (LocField u)) ha : reduceGL ⟨a⁻¹, inv_mem ha⟩ = (reduceGL ⟨a, ha⟩)⁻¹ :=
      reduceGL.map_inv ⟨a, ha⟩
    have hk_int : k.atPlace u ∈ intGL n Valued.v.integer := hk
    change (inflateConj (fun g ↦ S ⟨g, φ⟩) ∘ Gf.atPlace u) (k⁻¹ * δ * galoisGf σ k) = _
    simp +contextual [hk_int, hσ_u, reduceGL_map_locMap hσ_u φ hσ, h_conj, h_inv,
      -SemidirectProduct.mk_eq_inl_mul_inr, inflateConj, atPlace_galoisGf, mul_mem_cancel_left,
      map_locMap_mem_intGL_iff, mul_mem_cancel_right, ← MulMemClass.mk_mul_mk]
  · -- Both functions vanish off `K`, so the root `z` for the indicator functions of `K` serves.
    refine (h_pair P ?_ hPσ).elim fun z ⟨hz, h_root⟩ ↦
      ⟨z, hz, fun γ (a : Gf E' n) hγ h_rt ↦ ⟨fun g hg h_eq ↦ ?_, fun δ hδ h_ne ↦ ?_⟩⟩
    · -- `P` comes from the supports of the indicators of `K`, which contain those of the inflations
      revert hP
      gcongr <;> simp +contextual [K, inflateConj, atPlace_baseChangeGf, map_locMap_mem_intGL_iff]
    · -- The indicator functions of `K` agree at `g` and `a`.
      obtain ⟨h_value_eq, -⟩ := h_root γ a hγ h_rt
      have h_int : g.atPlace (u.below E) ∈ intGL n Valued.v.integer ↔
          a.atPlace u ∈ intGL n Valued.v.integer := by
        simpa [K, atPlace_baseChangeGf, map_locMap_mem_intGL_iff] using congrArg (· ≠ 0)
          (h_value_eq g hg h_eq)
      by_cases ha : a.atPlace u ∈ intGL n Valued.v.integer
      · -- The norm of `a` is `g`, so `⟨a, φ⟩ ^ orderOf φ` is `g` after reduction; `S` lifts `Ξ`.
        have h_pow : (⟨reduceGL ⟨_, ha⟩, φ⟩ : GalSemidirect _ _ n) ^ orderOf φ =
            inl ((reduceGL ⟨_, h_int.mpr ha⟩).map (algebraMap _ _)) := by
          obtain ⟨hm, h_reduce⟩ := exists_mk_reduceGL_pow_eq_mk_reduceGL_twistedNorm hσ_u hσ a ha
            (orderOf φ)
          refine h_reduce.trans ?_
          rw [← h_order, ← hg] at h_eq
          simp [h_eq, reduceGL_map_locMap _ _ h_residue,
            atPlace_baseChangeGf]
        have h_prime : (finrank (ResField (u.below E)) (ResField u)).Prime := by
          simpa [h_degree] using hμ.out
        have h_value : S ⟨reduceGL ⟨_, ha⟩, φ⟩ = Ξ.evalGL (reduceGL ⟨_, h_int.mpr ha⟩) :=
          h_lf φ ((hasFixedField_iff_ne_one h_prime).mpr hφ_ne) _ _ rfl h_pow
        simp [h_int, ha, h_value, -SemidirectProduct.mk_eq_inl_mul_inr, inflateConj]
      · simp [h_int, ha, inflateConj]
    · obtain ⟨-, h_coset⟩ := h_root γ a hγ h_rt
      have hδ_int : Gf.atPlace u δ ∈ intGL n Valued.v.integer := by
        by_contra h_not
        simp [h_not, inflateConj] at h_ne
      exact h_coset δ hδ (by simpa [K] using hδ_int)

/-- Let `E'` contain a primitive 5040th root of unity, `w` be split with `μ` trivial on its ideles,
and `u` the only place above `w`, split, of residue degree `[E' : E]`. If the form `f` has the
character `Ξ` as label at `w` and `Ξ'` is a lift of `Ξ` (`New.Lift ℕ`), then some eigenform `f'`
(nonzero, with polynomials `P` at the places of `E'`) over `E'` of weight `κ.baseChange` is a weak
base change of `f` off `w` and `w̄`, with label `Ξ'` at `u`. -/
lemma exists_baseChange_hasLabel [HasPrimitiveRoot5040 E'] {κ : Weight E}
    {f : Gf E n → WeylIndex n κ.1 → ℂ} (hf : f ∈ (stdSpace E n).forms κ)
    (hΞ : IsChar (Ξ.evalGL (n := n))) {Ξ' : Hall (ResField u)} (h_shintani : Lift ℕ Ξ Ξ')
    (h_label : HasLabel f hw Ξ.evalGL) :
    ∃ f' ∈ (stdSpace E' n).forms κ.baseChange, ∃ P : FinPlace E' → Polynomial ℂ,
      IsEigenform f' P ∧ IsWeakBaseChange μ {w} f f' ∧ HasLabel f' hu Ξ'.evalGL := by
  -- Transfer `f` along the matching functions of `isLocalMatching_shintani`. The label of `f` gives
  -- the non-zero trace that `exists_isWeakBaseChange_of_matching` asks for; the transfer lies in
  -- the image of the operator of `S ⟨·, φ⟩`, which gives its label.
  obtain ⟨S, hS, h_lift, h_lift'⟩ := h_shintani.hasCommonLift n
  have hS_char : IsChar S := isChar_of_mem_virtualChars hS
  obtain ⟨φ, h_match⟩ := isLocalMatching_shintani hw hu h_unique hμ_trivial h_residue h_degree
    hS_char.isClassFunction h_lift
  let π := ((stdSpace E n).formTranslation κ).comp (ofSplitPlace hw)
  let K := levelSpace π (localCongruence n w 0)
  let T := heckeFun π (localCongruence n w 0) (inflateConj Ξ.evalGL)
  -- The trace is `classInner Ξ.evalGL ρ.character` up to a factor; if it vanished, the group
  -- algebra element of `conj Ξ` would kill `f`.
  have h_trace (V : Subrepresentation π) (hV : ⟨f, hf⟩ ∈ V) (_ : Module.Finite ℂ ↥(K ⊓ V.1))
      (h_maps : ∀ x ∈ K ⊓ V.1, T x ∈ K ⊓ V.1) : (T.restrict h_maps).trace ℂ ↥(K ⊓ V.1) ≠ 0 := by
    intro h_zero
    obtain ⟨ρ, hρ⟩ := exists_representation_heckeFun_inflateConj hw V
    have hf_fixed : ⟨f, hf⟩ ∈ K := mem_levelSpace.2 fun k ↦ by
      obtain ⟨hk_int, hk_red⟩ := mem_localCongruence_zero.mp k.prop
      obtain ⟨h_fix, -⟩ := h_label
      simpa [π, Subtype.ext_iff] using h_fix ⟨k, hk_int⟩ hk_red
    have h_op : T.restrict h_maps = ρ.asAlgebraHom (groupAlgElem fun g ↦ conj (Ξ.evalGL g)) :=
      LinearMap.ext fun x ↦ Subtype.ext (hρ _ x).1
    have h_orth : classInner Ξ.evalGL ρ.character = 0 := by
      simpa [h_op, classInner, character, asAlgebraHom_eq_sum, finMean,
        ↓ finsum_eq_sum_of_fintype] using h_zero
    have h_kill : ρ.asAlgebraHom (groupAlgElem (starRingEnd ℂ ∘ Ξ.evalGL)) = 0 :=
      hΞ.asAlgebraHom_groupAlgElem_eq_zero_iff.2 h_orth
    obtain ⟨-, h_label_iff⟩ := hρ _ ⟨_, hf_fixed, hV⟩
    exact h_label_iff.mp h_label (LinearMap.congr_fun h_kill _)
  obtain ⟨f', P, h_eig, h_same, -, y, hy, h_image⟩ :=
    exists_isWeakBaseChange_of_matching ⟨f, hf⟩ h_match ![] 0 () rfl (by simp) nofun (by
      rw [heckeGenEigenspace, iInf_of_empty, inf_top_eq]
      exact h_trace)
  obtain ⟨ρ, hρ⟩ := exists_representation_heckeFun_inflateConj (n := n) hu (κ := κ.baseChange) ⊤
  let x := ρ.asAlgebraHom (groupAlgElem fun g ↦ conj (S ⟨g, φ⟩)) ⟨y, hy, trivial⟩
  obtain rfl : f' = x := h_image.symm.trans (hρ _ ⟨y, hy, trivial⟩).1
  obtain ⟨-, h_label_iff⟩ := hρ Ξ'.evalGL x
  refine ⟨_, x.val.prop, P, h_eig, h_same, h_label_iff.mpr fun h_zero ↦ h_eig.1 ?_⟩
  -- The group algebra element `a` of `conj (S ⟨·, φ⟩)` acts as zero in every representation whose
  -- character is orthogonal to `S ∘ inl`. So `a = c * b * a`, with `b` the element of
  -- `conj (S ∘ inl) = conj Ξ'.evalGL` (third part of
  -- `isIrreducibleChar_and_mem_virtualChars_and_exists_mul`). If `b` killed `x = a y`, then
  -- `x = 0`.
  obtain ⟨-, -, h_absorb⟩ :=
    isIrreducibleChar_and_mem_virtualChars_and_exists_mul ℤ (hS_char.comp inl).star.isClassFunction
  obtain ⟨c, hc⟩ := h_absorb _ fun _ hV ↦
    hS_char.star.asAlgebraHom_groupAlgElem_eq_zero inl (inr φ)
      ((hS_char.comp inl).asAlgebraHom_groupAlgElem_eq_zero_iff.1 hV)
  rw [← DescendsTo.iff_comp_inl_eq_evalGL.1 h_lift'] at h_zero
  simpa [x, ← mk_eq_inl_mul_inr, h_zero] using
    congrArg (fun a ↦ ρ.asAlgebraHom a ⟨y, hy, trivial⟩) hc

end New
