import Lib.General.Analysis.HolomorphicIntegrals
import Lib.Shimura.Uniformisation.HolomorphicFamilies

/-!
# Smoothness near an arc from an immersive generic family and a bound on the tangent space

A criterion for smoothness of a scheme `X` over a normal domain `R` near an arc `Spec V ⟶ X`, where
`V` is a valuation subring of `ℂ`.

* `New.Variety.exists_landsIn_smoothOfRelativeDimension`: the criterion.

Idea: by the tangent bound, `d` functions map `X` to affine `d`-space over `R`, unramified at the
closed point of the arc. The holomorphic family makes this map dominant, so it is étale there.

Notions from other files:
* `New.LandsIn`: The morphism t: Y → X lands in the open U, that is, t⁻¹U is all of Y.
* `New.IsHolomorphicImmersionAt`: A family of complex points is holomorphic at a parameter and
  constant to first order only in the direction 0.
* `New.specMap`: The morphism of spectra given by a ring homomorphism.
* `New.Variety.sqZeroReduction`: The morphism from Spec R to Spec (R ⊕ M) given by the projection
  of the trivial square-zero extension.
* `New.PointFn.ofSection`: The function on ring-valued points given by a section s over U: its value
  at t is t*s if t lands in U, and 0 otherwise.
-/

open CategoryTheory AlgebraicGeometry Spec Set IsLocalRing CommRingCat TrivSqZeroExt Algebra Module
  TensorProduct MvPolynomial KaehlerDifferential IsLocalization.Away Localization LinearMap RingHom
  Cardinal New.PointFn HasRingHomProperty IsStandardSmoothOfRelativeDimension

/-- Let `S` be a quotient of a standard étale algebra over a normal domain `A`, with a map to a
domain `V` in which `A` embeds. Then `S` is étale over `A` after inverting some `g` whose image in
`V` is a unit. -/
lemma New.Variety.exists_etale_away_of_faithful {A S V : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing S] [CommRing V] [IsDomain V] [Algebra A S] [Algebra A V]
    [Algebra S V] [IsScalarTower A S V] [FaithfulSMul A V] (C : StandardEtalePair A)
    (π : C.Ring →ₐ[A] S) (hπ : Function.Surjective π) :
    ∃ g : S, IsUnit (algebraMap S V g) ∧ Algebra.Etale A (Away g) := by
  -- The image `y` in `V` of the generator `P.x` is a simple root of the monic `P.f`. By normality
  -- `P.f = minpoly A y * q`, and inverting `q(P.x)` kills the kernel of `π`.
  obtain ⟨⟨P⟩⟩ : IsStandardEtale A C.Ring := instIsStandardEtaleRing C
  let y : V := algHom A S V (π P.x)
  have hy : P.HasMap y := (P.hasMap.map π).map (algHom A S V)
  have root_iff (a : Polynomial A) : a.aeval y = 0 ↔ minpoly A y ∣ a :=
    minpoly.isIntegrallyClosed_dvd_iff ⟨P.f, P.monic_f, hy.1⟩ a
  obtain ⟨q, hq⟩ : minpoly A y ∣ P.f := (root_iff P.f).mp hy.1
  obtain ⟨-, q_unit⟩ : IsUnit ((minpoly A y).derivative.aeval y) ∧ IsUnit (q.aeval y) := by
    simpa [hq] using hy.isUnit_derivative_f
  have ker_killed (c : C.Ring) (hc : π c = 0) : q.aeval P.x * c = 0 := by
    -- up to a unit, `c` is a polynomial `a(P.x)`; here `a(y) = 0`, so `P.f` divides `q * a`
    obtain ⟨a, n, ha⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x c
    obtain ⟨b, rfl⟩ : minpoly A y ∣ a := by simp [← root_iff, y, a.aeval_algHom_apply, ← ha, hc]
    rw [← (P.hasMap.2.pow n).mul_left_eq_zero]
    calc
      _ = (P.f * b).aeval P.x := by rw [mul_assoc, ha, hq, ← map_mul, mul_left_comm, mul_assoc]
      _ = 0 := by simp [P.hasMap.1]
  have bij : Function.Bijective (awayMapₐ π (q.aeval P.x)) :=
    ⟨awayMap_injective_iff.mpr fun c hc ↦ ⟨1, by simpa using ker_killed c hc⟩,
      mapₐ_surjective_of_surjective _ hπ⟩
  -- the image of `π (q.aeval P.x)` in `V` is `q(y)`, a unit
  refine ⟨π (q.aeval P.x), ?_, .of_equiv (.ofBijective _ bij)⟩
  change IsUnit (algHom A S V (π (q.aeval P.x)))
  simpa [y, Polynomial.aeval_algHom_apply] using q_unit

/-- The differentials of elements of `B` span the relative cotangent space at a `k`-point. -/
lemma New.Variety.span_tmul_differential {R B : Type*} (k : Type*) [CommRing R] [CommRing B]
    [Field k] [Algebra R B] [Algebra B k] :
    Submodule.span k (Set.range (TensorProduct.mk B k Ω[B⁄R] 1 ∘ D R B)) = ⊤ := by
  simp [Set.range_comp, ← Submodule.baseChange_span, span_range_derivation]

/-- If the relative cotangent space at a `k`-point has dimension at most `d`, the differentials
of `d` elements span it. -/
lemma New.Variety.exists_span_differentials {R k : Type*} {B : Type} [CommRing R] [CommRing B]
    [Field k] [Algebra R B] [Algebra B k] [Algebra.FiniteType R B] {d : ℕ}
    (h_le : Module.finrank k (k ⊗[B] Ω[B⁄R]) ≤ d) :
    ∃ z : Fin d → B, Submodule.span k
      (Set.range fun i : Fin d ↦ TensorProduct.mk B k Ω[B⁄R] 1 (D R B (z i))) = ⊤ := by
  -- Choose a basis among the differentials; it has at most `d` elements, so pad it to `Fin d`.
  let diff : B → k ⊗[B] Ω[B⁄R] := fun y ↦ 1 ⊗ₜ[B] D R B y
  obtain ⟨ι, x, -, span_x, indep⟩ : ∃ (ι : Type) (x : ι → B), Function.Injective x ∧
      Submodule.span k (Set.range (diff ∘ x)) = Submodule.span k (Set.range diff) ∧
      LinearIndependent k (diff ∘ x) :=
    exists_linearIndependent' k diff
  have card_le : #ι ≤ #(Fin d) := by grw [indep.cardinalMk_le_finrank, h_le, Cardinal.mk_fin]
  obtain ⟨e⟩ : Nonempty (ι ↪ Fin d) := (Cardinal.le_def _ _).1 card_le
  obtain ⟨z, rfl⟩ : ∃ z : Fin d → B, z ∘ e = x := e.injective.surjective_comp_right x
  refine ⟨z, top_unique ((span_x.trans (span_tmul_differential k)).ge.trans ?_)⟩
  exact Submodule.span_mono (range_subset_iff.mpr fun i ↦ ⟨e i, rfl⟩)

/-- Let `B` be of finite type over `A`. If the differentials of elements coming from `A` span the
cotangent space of `B` over `R` at a `k`-point, then `B` is unramified over `A` at that point. -/
lemma New.Variety.isUnramifiedAt_of_span_differentials {R A B k : Type*} {ι : Sort*} [CommRing R]
    [CommRing A] [CommRing B] [Field k] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [Algebra B k] [Algebra.FiniteType A B] (x : ι → A)
    (hx : Submodule.span k
      (Set.range fun i : ι ↦ TensorProduct.mk B k Ω[B⁄R] 1 (D R B (algebraMap A B (x i)))) = ⊤) :
    IsUnramifiedAt A (PrimeSpectrum.comap (algebraMap B k) ⊥).asIdeal := by
  set p : PrimeSpectrum B := PrimeSpectrum.comap (algebraMap B k) ⊥
  -- `k` is an algebra over the residue field of `p`, as `p` is the kernel of `B → k`
  let toK : p.asIdeal.ResidueField →ₐ[B] k :=
    Ideal.ResidueField.liftₐ p.asIdeal (ofId B k) le_rfl fun _ ↦ .mk0 _
  algebraize [toK.toRingHom]
  refine unramifiedLocus_eq_compl_support.superset fun hp : p ∈ Module.support B Ω[B⁄A] ↦ ?_
  -- then `k ⊗ Ω[B⁄A]` is non-zero, but it is the image of `k ⊗ Ω[B⁄R]` under the zero map
  rw [mem_support_iff_nontrivial_residueField_tensorProduct] at hp
  have : Nontrivial (k ⊗[B] Ω[B⁄A]) :=
    (AlgebraTensorModule.cancelBaseChange B p.asIdeal.ResidueField k k Ω[B⁄A]).symm.nontrivial
  let pr : k ⊗[B] Ω[B⁄R] →ₗ[k] k ⊗[B] Ω[B⁄A] := (KaehlerDifferential.map R A B B).baseChange k
  have pr_zero : pr = 0 := ext_on_range hx (by simp [pr])
  exact ne_zero_of_surjective (baseChange_surjective k (map_surjective R A B)) pr_zero

/-- A polynomial ring in finitely many variables over a normal domain is normal. -/
lemma New.Variety.isIntegrallyClosed_mvPolynomial_fin {R : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] (n : ℕ) : IsIntegrallyClosed (MvPolynomial (Fin n) R) := by
  induction n with
  | zero => exact .of_equiv (isEmptyRingEquiv R (Fin 0)).symm
  | succ n ih => exact .of_equiv (finSuccEquiv R n).symm.toRingEquiv

/-- An algebra that is standard smooth of relative dimension `0` over the polynomial ring in `d`
variables over `R` is standard smooth of relative dimension `d` over `R`. -/
lemma New.Variety.isStandardSmoothOfRelativeDimension_of_mvPolynomial {R S : Type*} {d : ℕ}
    [CommRing R] [Nontrivial R] [CommRing S] [Algebra R S] [Algebra (MvPolynomial (Fin d) R) S]
    [IsScalarTower R (MvPolynomial (Fin d) R) S]
    [Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin d) R) S] :
    Algebra.IsStandardSmoothOfRelativeDimension d R S := by
  have : Algebra.IsStandardSmooth R (MvPolynomial (Fin d) R) :=
    .of_basis_kaehlerDifferential (mvPolynomialBasis R (Fin d)) (by simp [subset_def])
  have : Algebra.IsStandardSmoothOfRelativeDimension d R (MvPolynomial (Fin d) R) := by
    simp [IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth,
      rank_eq_card_basis (mvPolynomialBasis R (Fin d))]
  simpa using IsStandardSmoothOfRelativeDimension.trans d 0 R (MvPolynomial (Fin d) R) S

/-- Let `A = R[X₁, …, X_d]` with `R` a normal domain, and let `S` be a quotient of a standard étale
`A`-algebra, with a map to a domain `V` in which `A` embeds. Then `S` is standard smooth of relative
dimension `d` over `R` after inverting some `g` whose image in `V` is a unit. -/
lemma New.Variety.exists_isStandardSmoothOfRelativeDimension_away {R S V : Type*} {d : ℕ}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] [CommRing V] [IsDomain V]
    [Algebra R S] [Algebra (MvPolynomial (Fin d) R) S] [IsScalarTower R (MvPolynomial (Fin d) R) S]
    [Algebra (MvPolynomial (Fin d) R) V] [Algebra S V] [IsScalarTower (MvPolynomial (Fin d) R) S V]
    (h_inj : Function.Injective (algebraMap (MvPolynomial (Fin d) R) V))
    (C : StandardEtalePair (MvPolynomial (Fin d) R)) (π : C.Ring →ₐ[MvPolynomial (Fin d) R] S)
    (hπ : Function.Surjective π) :
    ∃ g : S, IsUnit (algebraMap S V g) ∧
      Algebra.IsStandardSmoothOfRelativeDimension d R (Away g) := by
  have : FaithfulSMul (MvPolynomial (Fin d) R) V :=
    (faithfulSMul_iff_algebraMap_injective _ V).2 h_inj
  have : IsIntegrallyClosed (MvPolynomial (Fin d) R) := isIntegrallyClosed_mvPolynomial_fin d
  obtain ⟨g, g_unit, g_etale⟩ := exists_etale_away_of_faithful (V := V) C π hπ
  rw [Etale.iff_isStandardSmoothOfRelativeDimension_zero] at g_etale
  exact ⟨g, g_unit, isStandardSmoothOfRelativeDimension_of_mvPolynomial⟩

/-- Two points of `X` that factor through a monomorphism `j : Spec B ⟶ X` are equal if and only if
the ring maps on `B` agree. -/
lemma New.Variety.specMap_comp_mono_eq_iff {X : Scheme} {B : CommRingCat} {S : Type} [CommRing S]
    (j : Spec B ⟶ X) [Mono j] (φ ψ : B →+* S) :
    specMap φ ≫ j = specMap ψ ≫ j ↔ ∀ x : B, φ x = ψ x := by
  simp [cancel_mono, map_inj, ConcreteCategory.hom_ext_iff]

/-- Let `Spec B ⟶ X` be a monomorphism over `Spec R`, and `t` the `k`-point of `X` given by
`B → k`. Suppose that `finrank k M ≤ d` whenever a deformation of `t` over `k ⊕ M*`, constant in
`Spec R`, pulls back to the constant point along `l : M` only for `l = 0`. Then the relative
cotangent space of `B` at `t` has dimension at most `d`. -/
lemma New.Variety.finrank_cotangent_le {d : ℕ} {X : Scheme} {R B : CommRingCat} {k : Type}
    [Field k] [Algebra R B] [Algebra B k] (s : X ⟶ Spec R) (j : Spec B ⟶ X) [Mono j]
    (hj : j ≫ s = specMap (algebraMap R B))
    (h_tangent : ∀ (M : ModuleCat k) (τ : Spec (of (TrivSqZeroExt k (Dual k M))) ⟶ X),
      sqZeroReduction k (Dual k M) ≫ τ = specMap (algebraMap B k) ≫ j →
      τ ≫ s =
        specMap (algebraMap k (TrivSqZeroExt k (Dual k M))) ≫ specMap (algebraMap B k) ≫ j ≫ s →
      (∀ l : M,
        specMap (TrivSqZeroExt.map (Dual.eval k M l)).toRingHom ≫ τ =
          specMap (algebraMap k (TrivSqZeroExt k k)) ≫ specMap (algebraMap B k) ≫ j →
        l = 0) →
      Module.finrank k M ≤ d) :
    Module.finrank k (k ⊗[B] Ω[B⁄R]) ≤ d := by
  -- Apply `h_tangent` to the dual of the cotangent space and the first-order point `x ↦ x(t) + dx`.
  let diff : B → k ⊗[B] Ω[B⁄R] := fun y ↦ 1 ⊗ₜ[B] D R B y
  have diff_mul (x y : B) :
      diff (x * y) = algebraMap B k x • diff y + algebraMap B k y • diff x := by
    simp [diff, tmul_add, smul_tmul']
  let τ : B →+* TrivSqZeroExt k (Dual k (Dual k (k ⊗[B] Ω[B⁄R]))) :=
    { toFun x := .inl (algebraMap B k x) + .inr (Dual.eval k _ (diff x))
      map_one' := by simp [diff]
      map_mul' x y := by ext <;> simp [diff_mul]
      map_zero' := by simp [diff]
      map_add' := by simp [diff, TrivSqZeroExt.ext_iff, tmul_add] }
  rw [← Subspace.dual_finrank_eq]
  refine h_tangent (.of k _) (specMap τ ≫ j) ?_ ?_ fun l hl ↦
    ext_on_range (span_tmul_differential (R := R) (B := B) k) ?_
  · -- the constant part of `τ` is `t`; `-Spec.map_comp` keeps the two composites combined
    simp [τ, ← map_comp_assoc, -Spec.map_comp, ← ofHom_comp, specMap_comp_mono_eq_iff]
  · -- `τ` is constant on `R`, as `D` is `R`-linear
    simp [τ, diff, hj, ← Spec.map_comp, algebraMap_eq_inl, map_inj, ConcreteCategory.hom_ext_iff]
  · -- if the pull-back along `l` is constant, `l` kills every `dx`, and these span
    change ∀ y : B, l (diff y) = 0
    simpa [τ, ← map_comp_assoc, -Spec.map_comp, ← ofHom_comp, specMap_comp_mono_eq_iff,
      TrivSqZeroExt.ext_iff, algebraMap_eq_inl] using hl

/-- A ring map `θ` from a formally unramified `A`-algebra to `K ⊕ K` (square zero) whose
infinitesimal part vanishes on `A` has zero infinitesimal part. -/
lemma New.Variety.inl_fst_eq_of_formallyUnramified {A B K : Type*} [CommRing A] [CommRing B]
    [CommRing K] [Algebra A B] [FormallyUnramified A B] (θ : B →+* TrivSqZeroExt K K)
    (hθ : ∀ a : A, (θ (algebraMap A B a)).snd = 0) (x : B) :
    TrivSqZeroExt.inl (θ x).fst = θ x := by
  algebraize [θ.comp (algebraMap A B)]
  let θ₀ : B →ₐ[A] TrivSqZeroExt K K := ⟨(inlHom K K).comp ((fstHom K K K).toRingHom.comp θ),
    fun a ↦ TrivSqZeroExt.ext rfl (hθ a).symm⟩
  have θ_eq : θ₀ = ⟨θ, fun _ ↦ rfl⟩ :=
    FormallyUnramified.ext' _ ⟨2, kerIdeal_sq K K⟩ _ _ (fun y ↦ by simp [θ₀])
  exact DFunLike.congr_fun θ_eq x

/-- Let `φ` be a holomorphic immersion at `b`, let `W` be an affine open and `f` a function on it
such that `Γ(X, W)[1/f]` is formally unramified over `A`, and let `φ b` land in the locus where `f`
is invertible. If the functions coming from `A` are constant to first order on the family along
`v`, then `v = 0`. -/
lemma New.Variety.eq_zero_of_fderiv_ofSection_eq_zero {A : Type*} [CommRing A] {d : ℕ} {X : Scheme}
    {W : X.Opens} [Algebra A Γ(X, W)] {f : Γ(X, W)} [FormallyUnramified A (Away f)]
    {φ : (Fin d → ℂ) → (Spec (of ℂ) ⟶ X)} {b v : Fin d → ℂ} (hW : IsAffineOpen W)
    (h_imm : IsHolomorphicImmersionAt φ b) (hb : LandsIn (φ b) W)
    (hb_f : LandsIn (φ b) (specMap (algebraMap Γ(X, W) (Away f)) ≫ hW.fromSpec).opensRange)
    (hA : ∀ a : A, fderiv ℂ
      (fun w : Fin d → ℂ ↦ PointFn.ofSection (algebraMap A Γ(X, W) a) (of ℂ) (φ w)) b v = 0) :
    v = 0 := by
  -- The jet `τ` along `v` (the `ℂ[ε]`-point with values `h(φ b) + ε d(h ∘ φ)(v)`) is given by
  -- `θ : Γ(X, W)[1/f] → ℂ[ε]`, which is constant on `A`.
  obtain ⟨φ_hol, φ_immersive⟩ := h_imm
  obtain ⟨τ, hτ : IsJet φ b (applyₗ v) τ⟩ := φ_hol.exists_isJet (applyₗ v)
  suffices τ_const : τ = specMap (algebraMap ℂ (TrivSqZeroExt ℂ ℂ)) ≫ φ b from
    φ_immersive v (by rwa [τ_const] at hτ)
  obtain ⟨θ, rfl⟩ : ∃ θ : of (Away f) ⟶ of (TrivSqZeroExt ℂ ℂ),
      Spec.map θ ≫ specMap (algebraMap Γ(X, W) (Away f)) ≫ hW.fromSpec = τ :=
    landsIn_opensRange.1 (hτ.landsIn hb_f)
  have θ_snd (a : A) : (θ (algebraMap A (Away f) a)).snd = 0 := by
    have jet : θ (algebraMap Γ(X, W) (Away f) (algebraMap A Γ(X, W) a)) =
        .inl (PointFn.ofSection (algebraMap A Γ(X, W) a) (of ℂ) (φ b)) + .inr (fderiv ℂ
          (fun w ↦ PointFn.ofSection (algebraMap A Γ(X, W) a) (of ℂ) (φ w)) b v) := by
      refine .trans ?_ (hτ.ofSection_eq hb (algebraMap A Γ(X, W) a))
      rw [← map_comp_assoc, ofSection_map_fromSpec]
      simp
    simp [IsScalarTower.algebraMap_apply A Γ(X, W) (Away f), jet, hA]
  have θ_eq : θ = ofHom ((inlHom ℂ ℂ).comp ((fstHom ℂ ℂ ℂ).toRingHom.comp θ.hom)) :=
    hom_ext (RingHom.ext fun x ↦ (inl_fst_eq_of_formallyUnramified θ.hom θ_snd x).symm)
  rw [← hτ.fst_comp]
  conv_lhs => rw [θ_eq]
  simp [specMap, Spec.map_comp]

/-- Let `Q` be a polynomial over a ring embedded in `ℂ` by `u`, and `Z` a map that is strictly
differentiable with surjective derivative at `b`. If `Q(Z w) = 0` for `w` near `b`, then
`Q = 0`. -/
lemma New.Variety.eq_zero_of_eventually_eval_eq_zero {R : Type*} [CommRing R] {d : ℕ}
    {Z : (Fin d → ℂ) → Fin d → ℂ} {Z' : (Fin d → ℂ) →L[ℂ] Fin d → ℂ} {b : Fin d → ℂ} {u : R →+* ℂ}
    (hu : Function.Injective u) (hZ : HasStrictFDerivAt Z Z' b) (hZ' : Z'.range = ⊤)
    {Q : MvPolynomial (Fin d) R}
    (hQ : ∀ᶠ w : Fin d → ℂ in nhds b, MvPolynomial.eval (Z w) (Q.map u) = 0) : Q = 0 := by
  have poly_zero : ∀ y : Fin d → ℂ, MvPolynomial.eval y (Q.map u) = 0 :=
    eq_zero_of_submersion (.eval_mvPolynomial _) hZ hZ' hQ
  exact MvPolynomial.map_injective _ hu (MvPolynomial.funext (by simpa using poly_zero))

/-- In an affine chart `W`, let `A = R[X₁, …, X_d]` act, let `u : R → ℂ` be injective, and let
the function coming from each `P` in `A` have the value `P(Z w)` at `φ w` for `w` near `b`, with
coefficients moved by `u`, where `Z` is analytic. Let `Γ(X, W)[1/f]` be formally unramified over
`A`, let `φ b` land in the locus of `W` where `f` is invertible, and let `φ` be a holomorphic
immersion at `b`. If the function of `Q` vanishes on the family near `b`, then `Q = 0`. -/
lemma New.Variety.eq_zero_of_eventually_ofSection_eq_zero {R : Type*} [CommRing R] {d : ℕ}
    {X : Scheme} {W : X.Opens} [Algebra (MvPolynomial (Fin d) R) Γ(X, W)] {f : Γ(X, W)}
    [FormallyUnramified (MvPolynomial (Fin d) R) (Away f)]
    {φ : (Fin d → ℂ) → (Spec (of ℂ) ⟶ X)} {b : Fin d → ℂ} {u : R →+* ℂ}
    {Z : (Fin d → ℂ) → Fin d → ℂ} (hW : IsAffineOpen W) (h_imm : IsHolomorphicImmersionAt φ b)
    (hb : LandsIn (φ b) W)
    (hb_f : LandsIn (φ b) (specMap (algebraMap Γ(X, W) (Away f)) ≫ hW.fromSpec).opensRange)
    (hu : Function.Injective u) (hZ : AnalyticAt ℂ Z b)
    (h_eval : ∀ P : MvPolynomial (Fin d) R,
      (fun w : Fin d → ℂ ↦
          PointFn.ofSection (algebraMap (MvPolynomial (Fin d) R) Γ(X, W) P) (of ℂ) (φ w))
        =ᶠ[nhds b] (fun y : Fin d → ℂ ↦ MvPolynomial.eval y (P.map u)) ∘ Z)
    {Q : MvPolynomial (Fin d) R}
    (hQ : ∀ᶠ w : Fin d → ℂ in nhds b,
      PointFn.ofSection (algebraMap (MvPolynomial (Fin d) R) Γ(X, W) Q) (of ℂ) (φ w) = 0) :
    Q = 0 := by
  -- The derivative of `Z` is injective, hence onto, so `Z` is a submersion at `b`.
  have Z_imm (v : Fin d → ℂ) (hv : fderiv ℂ Z b v = 0) : v = 0 := by
    refine eq_zero_of_fderiv_ofSection_eq_zero hW h_imm hb hb_f
      fun P : MvPolynomial (Fin d) R ↦ ?_
    rw [(h_eval P).fderiv_eq, fderiv_comp b
      (AnalyticOnNhd.eval_mvPolynomial _ _ ⟨⟩).differentiableAt hZ.differentiableAt]
    simp [hv]
  refine eq_zero_of_eventually_eval_eq_zero hu hZ.hasStrictFDerivAt
    (ker_eq_bot_iff_range_eq_top.1 (bot_unique Z_imm)) ?_
  filter_upwards [h_eval Q, hQ] with w hev hw using hev.symm.trans hw

/-- If a section over `U` vanishes at a complex point `x` in `U`, it vanishes at every complex
point in `U` to which `x` specialises. -/
lemma New.Variety.ofSection_eq_zero_of_specializes {X : Scheme} {U : X.Opens} {q : Γ(X, U)}
    {x y : Spec (of ℂ) ⟶ X} (hx : LandsIn x U) (hy : LandsIn y U)
    (hxy : x (closedPoint ℂ) ⤳ y (closedPoint ℂ))
    (hq : PointFn.ofSection q (of ℂ) x = 0) : PointFn.ofSection q (of ℂ) y = 0 := by
  have generise : LandsIn y (X.basicOpen q) → LandsIn x (X.basicOpen q) := by
    simpa [landsIn_iff_mem] using hxy.mem_open (X.basicOpen q).2
  simpa [landsIn_basicOpen, hx, hy, hq] using generise

/-- Let `Spec ρ` be the structure map of an affine chart `W` of `X` over `Spec R`, and let the
points `φ w` lie in `W` near `b`, all over `u : R → ℂ`. Then a polynomial in functions `z i` on
`W` restricts on the family to the polynomial, with coefficients moved by `u`, in the values of
the `z i`. -/
lemma New.Variety.ofSection_eval₂Hom_eventuallyEq {d : ℕ} {X : Scheme} {R : CommRingCat}
    {W : X.Opens} {s : X ⟶ Spec R} {ρ : R ⟶ Γ(X, W)} {u : R ⟶ of ℂ}
    {φ : (Fin d → ℂ) → (Spec (of ℂ) ⟶ X)} {b : Fin d → ℂ} (hW : IsAffineOpen W)
    (hρ : Spec.map ρ = hW.fromSpec ≫ s) (hs : ∀ w : Fin d → ℂ, φ w ≫ s = Spec.map u)
    (h_near : ∀ᶠ w : Fin d → ℂ in nhds b, LandsIn (φ w) W) (z : Fin d → Γ(X, W))
    (Q : MvPolynomial (Fin d) R) :
    (fun w : Fin d → ℂ ↦ PointFn.ofSection (eval₂Hom ρ.hom z Q) (of ℂ) (φ w)) =ᶠ[nhds b]
      (fun y : Fin d → ℂ ↦ MvPolynomial.eval y (Q.map u.hom)) ∘
        fun (w : Fin d → ℂ) (i : Fin d) ↦ PointFn.ofSection (z i) (of ℂ) (φ w) := by
  filter_upwards [h_near] with w hw
  -- `evalSection` is the ring map `Γ(X, W) → ℂ` of the point `φ w`, which lies over `u`
  have u_eq : ρ ≫ evalSection _ hw = u :=
    map_injective (by simp [hρ, hs, reassoc_of% map_evalSection_fromSpec])
  simp [ofSection_eq hw, ← u_eq, hom_eval₂]

/-- In an affine chart `W` of `X` over `Spec R`, let `A = R[X₁, …, X_d]` act by `X i ↦ z i` and
let `Γ(X, W)[1/f]` be formally unramified over `A`. Let all `φ w` lie over an injective
`u : R → ℂ`, let `φ` be a holomorphic immersion at `b`, let `φ b` land in the locus where `f`
is invertible, and let `φ b` specialise to `φ w` for `w` near `b`. If `Q(z)` vanishes at `φ b`,
then `Q = 0`: it vanishes at the specialisations, so on the image of a submersion. -/
lemma New.Variety.eq_zero_of_ofSection_eq_zero {d : ℕ} {X : Scheme} {R : CommRingCat}
    {W : X.Opens} [Algebra (MvPolynomial (Fin d) R) Γ(X, W)] {f : Γ(X, W)}
    [FormallyUnramified (MvPolynomial (Fin d) R) (Away f)] {s : X ⟶ Spec R} {ρ : R ⟶ Γ(X, W)}
    {u : R ⟶ of ℂ} {φ : (Fin d → ℂ) → (Spec (of ℂ) ⟶ X)} {b : Fin d → ℂ}
    {z : Fin d → Γ(X, W)} (hW : IsAffineOpen W)
    (hz : ∀ Q : MvPolynomial (Fin d) R,
      algebraMap (MvPolynomial (Fin d) R) Γ(X, W) Q = eval₂Hom ρ.hom z Q)
    (hρ : Spec.map ρ = hW.fromSpec ≫ s) (hs : ∀ w : Fin d → ℂ, φ w ≫ s = Spec.map u)
    (hu : Function.Injective u) (h_imm : IsHolomorphicImmersionAt φ b) (hb : LandsIn (φ b) W)
    (hb_f : LandsIn (φ b) (specMap (algebraMap Γ(X, W) (Away f)) ≫ hW.fromSpec).opensRange)
    (h_spec : ∀ᶠ w : Fin d → ℂ in nhds b, φ b (closedPoint ℂ) ⤳ φ w (closedPoint ℂ))
    {Q : MvPolynomial (Fin d) R}
    (hQ : PointFn.ofSection (algebraMap (MvPolynomial (Fin d) R) Γ(X, W) Q) (of ℂ) (φ b) = 0) :
    Q = 0 := by
  have φ_hol : HolomorphicAt φ b := h_imm.1
  have h_near : ∀ᶠ w : Fin d → ℂ in nhds b, LandsIn (φ w) W :=
    (φ_hol (isRegularOn_ofSection 0) hb).1
  have Z_an : AnalyticAt ℂ (fun (w : Fin d → ℂ) i ↦ PointFn.ofSection (z i) (of ℂ) (φ w)) b :=
    .pi fun i ↦ (φ_hol (isRegularOn_ofSection (z i)) hb).2
  refine eq_zero_of_eventually_ofSection_eq_zero hW h_imm hb hb_f hu Z_an
    (fun P ↦ by simpa only [hz] using ofSection_eval₂Hom_eventuallyEq hW hρ hs h_near z P) ?_
  filter_upwards [h_near, h_spec] with w hw hspec
  exact ofSection_eq_zero_of_specializes hb hw hspec hQ

/-- Let `j : Spec B ⟶ X` be an open immersion over `Spec R` and `g : B` such that `B[1/g]` is
standard smooth of relative dimension `d` over `R`. If `β : B → V` maps `g` to a unit, then the
point given by `β` lands in an open set of `X` that is smooth of relative dimension `d` over
`Spec R`. -/
lemma New.Variety.exists_smooth_open_of_standardSmooth_away {d : ℕ} {X : Scheme}
    {R B V : CommRingCat} [Algebra R B] (s : X ⟶ Spec R) (j : Spec B ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ s = specMap (algebraMap R B)) (g : B)
    (h_smooth : Algebra.IsStandardSmoothOfRelativeDimension d R (Away g)) (β : B ⟶ V)
    (hβ : IsUnit (β.hom g)) :
    ∃ U : X.Opens, LandsIn (Spec.map β ≫ j) U ∧ SmoothOfRelativeDimension d (U.ι ≫ s) := by
  let c : Spec (of (Away g)) ⟶ X := specMap (algebraMap B (Away g)) ≫ j
  have c_smooth : SmoothOfRelativeDimension d (c ≫ s) := by
    simp only [c, Category.assoc, hj, ← Spec.map_comp]
    exact Spec_iff.2 (locally_of isStandardSmoothOfRelativeDimension_respectsIso _
      ((isStandardSmoothOfRelativeDimension_algebraMap d).2 h_smooth))
  refine ⟨c.opensRange, landsIn_opensRange.2 ⟨ofHom (awayLift β.hom g hβ), ?_⟩, ?_⟩
  · -- `-Spec.map_comp` keeps the composites combined, so that they are compared as ring maps
    simp [c, ← map_comp_assoc, -Spec.map_comp, cancel_mono, map_inj, ConcreteCategory.hom_ext_iff]
  · rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc]
    exact comp_of_isOpenImmersion _ _ _ c_smooth

/-- Let `s : X ⟶ Spec R` be locally of finite type, `R` a normal domain, `φ` a family of complex
points of `X` and `arc` a point with values in a valuation subring `V` of `ℂ`. Assume:
(a) `arc` extends `φ w₀`;
(b) all `φ w` lie over one embedding `emb : R → ℂ`;
(c) `φ w₀` specialises to `φ w` for `w` near `w₀`;
(d) `φ` has `d` parameters and is a holomorphic immersion at `w₀`, that is, it is holomorphic
there and constant to first order only in the direction `0`;
(e) `ϑ : V → k` is a local map to a field, so it gives a `k`-point `t` at the closed point of
`arc`;
(f) if `τ` is a deformation of `t` over the square-zero extension `k ⊕ M*`, constant in `Spec R`,
whose pull-back to `k[ε]` along `l : M` is constant only for `l = 0`, then `finrank k M ≤ d`.
Then `s` is smooth of relative dimension `d` on an open set through which `arc` factors. -/
lemma New.Variety.exists_landsIn_smoothOfRelativeDimension {d : ℕ} {X : Scheme} {R : CommRingCat}
    {w₀ : Fin d → ℂ}
    {emb : R ⟶ of ℂ} {k : Type} {φ : (Fin d → ℂ) → (Spec (of ℂ) ⟶ X)} {V : ValuationSubring ℂ}
    {arc : Spec (of V) ⟶ X} [Field k] {ϑ : V →+* k} [IsLocalHom ϑ] (s : X ⟶ Spec R)
    [LocallyOfFiniteType s] [IsDomain R] [IsIntegrallyClosed R]
    (h_imm : IsHolomorphicImmersionAt φ w₀)
    (h_arc_extends : specMap V.subtype ≫ arc = φ w₀)
    (h_over : ∀ w : Fin d → ℂ, φ w ≫ s = Spec.map emb) (h_emb_inj : Function.Injective emb)
    (h_spec : ∀ᶠ w : Fin d → ℂ in nhds w₀, φ w₀ (closedPoint ℂ) ⤳ φ w (closedPoint ℂ))
    (h_tangent : ∀ (M : ModuleCat k) (τ : Spec (of (TrivSqZeroExt k (Dual k M))) ⟶ X),
      let t := specMap ϑ ≫ arc
      sqZeroReduction k (Dual k M) ≫ τ = t →
      τ ≫ s = specMap (algebraMap k (TrivSqZeroExt k (Dual k M))) ≫ t ≫ s →
      (∀ l : M,
        specMap (TrivSqZeroExt.map (Dual.eval k M l)).toRingHom ≫ τ =
          specMap (algebraMap k (TrivSqZeroExt k k)) ≫ t →
        l = 0) →
      Module.finrank k M ≤ d) :
    ∃ U : X.Opens, LandsIn arc U ∧ SmoothOfRelativeDimension d (U.ι ≫ s) := by
  -- In an affine chart `Spec B`, `d` functions `z` give a map to affine `d`-space over `R` that is
  -- unramified at the closed point of the arc. On the family `φ` it is a submersion at `w₀`, hence
  -- it is dominant, hence étale near the arc because `R` is normal.
  obtain ⟨W, hW, arc_W⟩ := exists_isAffineOpen_landsIn arc
  let B : CommRingCat := Γ(X, W)
  -- On the chart, `s` and the arc are given by ring maps `ρ : R ⟶ B` and `α : B ⟶ V`.
  obtain ⟨ρ, hρ⟩ : ∃ ρ : R ⟶ B, Spec.map ρ = hW.fromSpec ≫ s := map_surjective _
  obtain ⟨α, rfl⟩ : ∃ α : B ⟶ of V, Spec.map α ≫ hW.fromSpec = arc :=
    landsIn_opensRange.1 (by rwa [hW.opensRange_fromSpec])
  have finite_type : ρ.hom.FiniteType := by
    rw [← Spec_iff (P := @LocallyOfFiniteType), hρ]
    infer_instance
  algebraize [ρ.hom, ϑ.comp α.hom]
  -- The cotangent space at the closed point has dimension at most `d`.
  have t_eq : specMap (algebraMap B k) ≫ hW.fromSpec = specMap ϑ ≫ Spec.map α ≫ hW.fromSpec := by
    rw [← Spec.map_comp_assoc]
    rfl
  have cotangent_le : Module.finrank k (k ⊗[B] Ω[B⁄R]) ≤ d := finrank_cotangent_le s hW.fromSpec
    hρ.symm (by simpa only [reassoc_of% t_eq, t_eq, Category.assoc] using h_tangent)
  -- So `B` is unramified there over `A = R[X₁, …, X_d]`, `X i ↦ z i`, and some `B[1/f]` through
  -- which the arc factors is a quotient of a standard étale `A`-algebra.
  obtain ⟨z, z_span⟩ : ∃ z : Fin d → B, Submodule.span k
      (Set.range fun i : Fin d ↦ TensorProduct.mk B k Ω[B⁄R] 1 (D R B (z i))) = ⊤ :=
    exists_span_differentials cotangent_le
  let A : Type := MvPolynomial (Fin d) R
  let q : MvPolynomial (Fin d) R →ₐ[R] B := aeval z
  algebraize [q.toRingHom]
  have : FiniteType A B := .of_restrictScalars_finiteType R A B
  have unram : IsUnramifiedAt A (PrimeSpectrum.comap (algebraMap B k) ⊥).asIdeal :=
    isUnramifiedAt_of_span_differentials (R := R) MvPolynomial.X
      (by simpa [A, q, algebraMap_toAlgebra] using z_span)
  obtain ⟨f, f_ne_zero, C, π, π_surj⟩ : ∃ f : B, algebraMap B k f ≠ 0 ∧
      ∃ (C : StandardEtalePair A) (π : C.Ring →ₐ[A] Away f), Function.Surjective π :=
    unram.exists_hasStandardEtaleSurjectionOn
  obtain ⟨β, rfl⟩ : ∃ β : of (Away f) ⟶ of V, ofHom (algebraMap B (Away f)) ≫ β = α := by
    -- `f` is nonzero at the closed point and `ϑ` is local, so `α f` is a unit of `V`
    have αf_unit : IsUnit (α.hom f) := .of_map ϑ (α.hom f) (.mk0 _ f_ne_zero)
    exact ⟨ofHom (IsLocalization.Away.lift f αf_unit), hom_ext (lift_comp f αf_unit)⟩
  algebraize [β.hom, β.hom.comp (algebraMap A (Away f))]
  have : FormallyUnramified A (Away f) := .of_surjective π π_surj
  have w₀_W : LandsIn (φ w₀) W := by
    simpa only [h_arc_extends] using arc_W.comp (specMap V.subtype)
  have w₀_f : LandsIn (φ w₀) (specMap (algebraMap B (Away f)) ≫ hW.fromSpec).opensRange :=
    landsIn_opensRange.2 ⟨β ≫ ofHom V.subtype, by simpa using h_arc_extends⟩
  -- `A` embeds in `V`: a `Q` that vanishes at `φ w₀` vanishes at its specialisations `φ w`, so
  -- on the image of the submersion given by the values of the `z i`, so `Q = 0`.
  have A_inj : Function.Injective (algebraMap A V) := by
    refine (injective_iff_map_eq_zero _).2 fun (Q : A) hQ ↦ ?_
    have Q_arc : β.hom (algebraMap B (Away f) (q Q)) = 0 := hQ
    have Q_w₀ : PointFn.ofSection (q Q) (of ℂ) (φ w₀) = 0 := by
      rw [← h_arc_extends, ← map_comp_assoc, ofSection_map_fromSpec]
      simp [Q_arc]
    exact eq_zero_of_ofSection_eq_zero hW (fun _ ↦ rfl) hρ h_over h_emb_inj h_imm w₀_W w₀_f
      h_spec Q_w₀
  -- By normality some `B[1/f][1/g]` is étale over `A`, so smooth of dimension `d` over `R`.
  obtain ⟨g, g_unit, g_smooth⟩ : ∃ g : Away f, IsUnit (algebraMap (Away f) V g) ∧
      Algebra.IsStandardSmoothOfRelativeDimension d R (Away g) :=
    exists_isStandardSmoothOfRelativeDimension_away A_inj C π π_surj
  have chart_over : (specMap (algebraMap B (Away f)) ≫ hW.fromSpec) ≫ s =
      specMap (algebraMap R (Away f)) := by
    rw [Category.assoc, ← hρ, ← Spec.map_comp]
    rfl
  simpa using exists_smooth_open_of_standardSmooth_away s _ chart_over g g_smooth β g_unit
