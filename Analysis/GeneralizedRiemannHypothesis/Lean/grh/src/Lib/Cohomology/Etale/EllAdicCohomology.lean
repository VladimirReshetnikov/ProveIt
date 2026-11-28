import Lib.Cohomology.Etale.FilteredLimits
import Lib.PadicComparison.Completion

/-!
# ℓ-adic cohomology with its Galois action; finiteness and bijectivity from coefficients mod ℓ

`ℓ`-adic cohomology is defined as `Ext` on test rings, with coefficients in the Witt vectors of the
locally constant `𝔽_ℓ`-valued functions on the spectrum.

* `New.Variety.ellAdicCoeff`: the coefficient `ℤ_ℓ`; `New.Variety.ellAdicPull`: pull-back on
  cohomology, over `ℚ_ℓ`.
* `New.Variety.ellAdicCohom`, `New.Variety.ellAdicCohom.galoisAction`: cohomology of the base change
  to `Ω`, and the action of `Γ`.
* `New.Variety.exists_ellAdicCoeff_modShortExact_pow`,
  `New.Variety.exists_ellAdicCoeff_modShortExact`: reduction modulo `ℓ ^ k` and `ℓ`; completeness.
* `New.Variety.finite_H_ellAdicCoeff`, `New.Variety.IsCohomEquiv.bijective_ellAdicPull`: finiteness
  and bijectivity lift from `𝔽_ℓ`.

Notions from other files:
* `New.Variety.ModShortExact`: `ModShortExact a q` says that `0 → Φ → Φ → G → 0`, formed by
  multiplication by `a` and by `q`, is short exact.
* `New.Variety.TestRing`: The category of test rings (`New.Variety.IsTest`), as a full subcategory
  of commutative rings; `New.Variety.testIncl` is its inclusion functor.

## Relation to the literature

Known; see `Lib.Cohomology.Etale.FilteredLimits`, `Lib.PadicComparison.Completion` and
`Lib.PadicComparison.Primitive.ComparisonTheorem` for sources.
-/

noncomputable section

namespace New.Variety

open CategoryTheory AlgebraicGeometry CommRingCat LocallyConstant WittVector Function AddCommGrpCat
  TensorProduct Pi

variable {ℓ : ℕ} [ThePrime ℓ] {n : ℕ} (R : CommRingCat)
  (Ω : Type) [CommRing Ω] [Algebra R Ω]
  (Γ : Type*) [Group Γ] [MulSemiringAction Γ Ω] [SMulCommClass Γ R Ω]

/-! ### Definitions -/

/-- The coefficient `ℤ_ℓ`: a test ring `A` goes to the Witt vectors of the ring of locally constant
functions `Spec A → 𝔽_ℓ`. -/
abbrev ellAdicCoeff : AbFunctor TestRing :=
  moduleCoeff (asModules ((testIncl ⋙ locConstAlg) ⋙ wittFunctor ℤ_[ℓ]))

/-- Pull-back along `α : M ⟶ N` on `ℚ_ℓ ⊗ Ext^n(-, ℤ_ℓ)`, as an additive function of `α`. -/
def ellAdicPull (n : ℕ) {M N : AbFunctor TestRing} :
    (M ⟶ N) →+ ℚ_[ℓ] ⊗[ℤ_[ℓ]] H N ellAdicCoeff n →ₗ[ℚ_[ℓ]] ℚ_[ℓ] ⊗[ℤ_[ℓ]] H M ellAdicCoeff n :=
  AddMonoidHom.mk' (fun α : M ⟶ N ↦ (H.mapₗ ℤ_[ℓ] ellAdicCoeff α n).baseChange ℚ_[ℓ])
    (by aesop (add simp [H.mapₗ, H.map, Abelian.Ext.mk₀_add, tmul_add]))

/-- Pulling back along `β` and then along `α` is pulling back along `α ≫ β`. -/
lemma ellAdicPull.comp {M N K : AbFunctor TestRing} (α : M ⟶ N) (β : N ⟶ K)
    (x : ℚ_[ℓ] ⊗[ℤ_[ℓ]] H K ellAdicCoeff n) :
    ellAdicPull (ℓ := ℓ) n α (ellAdicPull n β x) = ellAdicPull n (α ≫ β) x := by
  induction x with
  | tmul r y => simp [ellAdicPull, H.mapₗ, H.map_comp]
  | add x y hx hy => simp [hx, hy]

/-- The functor of points (a functor from commutative rings to types, `PointFunctor`) of the base
change `X ×_R Ω` of a scheme `X` over `R`. -/
def geomPoints : Over (Spec R) ⥤ PointFunctor where
  obj X := baseChangeOf (pointsToBase X.hom) (ofHom (algebraMap R Ω))
  -- a point is a pair (point of `X`, ring map out of `Ω`); compose the first with `f`
  map {X Y} f :=
    { app B :=
        ↾fun x ↦
          ⟨(ULift.up (x.1.1.1 ≫ f.1), x.1.2), by
            -- `f` is a map over `Spec R`, so the new point lies over the same map out of `R`
            have h_over : (x.1.1.1 ≫ f.1) ≫ Y.hom = x.1.1.1 ≫ X.hom := by simp
            exact (congrArg (fun h ↦ ULift.up (Spec.preimage h)) h_over).trans x.2⟩ }

/-- Geometric `ℓ`-adic cohomology in degree `n`: `X ↦ ℚ_ℓ ⊗ H^n(X ×_R Ω, ℤ_ℓ)`. -/
def ellAdicCohom (n : ℕ) : (Over (Spec R))ᵒᵖ ⥤ ModuleCat ℚ_[ℓ] :=
  (geomPoints R Ω).op ⋙
    { obj X := ModuleCat.of ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] H (freeAb.obj (testIncl ⋙ X.unop)) ellAdicCoeff n)
      map u := ModuleCat.ofHom (ellAdicPull n (freeAb.map (mapOnTests u.unop)))
      map_id := by aesop_cat (add simp [ellAdicPull, H.mapₗ])
      map_comp := by aesop_cat (add simp [ellAdicPull.comp]) }

/-- The action on `H^n(X ×_R Ω)` of a group `Γ` acting on `Ω` by `R`-algebra automorphisms. -/
def ellAdicCohom.galoisAction (X : Over (Spec R)) (n : ℕ) :
    Representation ℚ_[ℓ] Γ (ellAdicCohom R Ω n ⟨X⟩) :=
  -- an `R`-automorphism `g` of `Ω` acts on the points over `Ω`, hence on their cohomology
  MonoidHom.comp
    { toFun (g : Ω ≃ₐ[R] Ω) :=
        ellAdicPull n
          (freeAb.map (mapOnTests (baseChangeTransition _ (CommRingCat.ofHom g) (by aesop))))
      map_one' := congr($((ellAdicCohom R Ω n).map_id (Opposite.op X)).hom)
      map_mul' g g' := by
        ext
        erw [ellAdicPull.comp, ← freeAb.map_comp]
        rfl }
    (MulSemiringAction.toAlgAut Γ R Ω)

/-- Pull-back along a map `f : X ⟶ Y` of `R`-schemes commutes with the action of `Γ`. -/
lemma ellAdicCohom.map_galoisAction {X Y : Over (Spec R)} (f : X ⟶ Y) (g : Γ)
    (x : ((ellAdicCohom R Ω n).obj (Opposite.op Y))) :
    (ellAdicCohom R Ω n).map f.op (galoisAction R Ω Γ Y n g x) =
      galoisAction R Ω Γ X n g ((ellAdicCohom R Ω n).map f.op x) := by
  -- both sides are pull-backs along a composite, and the two composites are the same map (the two
  -- composites have the same type only after unfolding `geomPoints`)
  repeat erw [ellAdicPull.comp, ← freeAb.map_comp]
  rfl

/-! ### Comparison with finite coefficients -/

/-- There is an exact sequence `0 → ℤ_ℓ → ℤ_ℓ → W_k(𝔽_ℓ) → 0` of coefficients whose first map is
`ℓ ^ k`, where the third term is the locally constant functions with values in `W_k(𝔽_ℓ)`, the
Witt vectors of length `k`. -/
lemma exists_ellAdicCoeff_modShortExact_pow (k : ℕ) :
    ∃ q : ellAdicCoeff ⟶ locConstCoeff ⟨TruncatedWittVector ℓ k (ZMod ℓ)⟩,
      ModShortExact ↑(ℓ ^ k) q := by
  -- A truncated Witt vector of locally constant functions is a locally constant function with
  -- values in truncated Witt vectors (`unflip`); `q` is truncation followed by this.
  let C (A : TestRing) := LocallyConstant (PrimeSpectrum (testIncl.obj A)) (ZMod ℓ)
  let tr (A : TestRing) : WittVector ℓ (C A) →+
      LocallyConstant (PrimeSpectrum (testIncl.obj A)) (TruncatedWittVector ℓ k (ZMod ℓ)) :=
    .mk' (fun x ↦ unflip (truncate k x)) fun x y ↦ LocallyConstant.ext fun a ↦
      ((truncate k).comp (map (evalRingHom a : C A →+* ZMod ℓ))).map_add x y
  refine ⟨_,
    modShortExact_of_isReductionMod (q := .mk fun A ↦ AddCommGrpCat.ofHom (tr A)) fun A ↦ ?_⟩
  -- `W(C A)` has no `ℓ`-torsion (`h_torsion_free`), and the first `k` coordinates of a Witt vector
  -- vanish exactly when it is a multiple of `ℓ ^ k` (`h_coeff_iff`)
  obtain ⟨-, h_torsion_free, -, h_coeff_iff⟩ :=
    isReductionMod_constantCoeff_and_isCompleteTorsionFree (p := ℓ) (ZMod ℓ)
      (locConstAlg.obj (testIncl.obj A))
  -- to show: no `ℓ ^ k`-torsion, `tr A` is onto, and its kernel is the multiples of `ℓ ^ k`
  refine ⟨h_torsion_free.regular.pow k, fun y ↦ ?_, fun x ↦ Iff.trans ?_ (h_coeff_iff k x)⟩
  · obtain ⟨x, hx⟩ := truncate_surjective ℓ k (C A) y.flip
    exact ⟨x, congrArg unflip hx⟩
  · -- `tr A x = 0` says that the first `k` coordinates of `x` vanish
    have h_tr_zero : tr A x = 0 ↔ truncate k x = 0 := by
      simpa only [map_zero] using
        (⟨congrArg LocallyConstant.flip, congrArg unflip⟩ :
          tr A x = tr A 0 ↔ truncate k x = truncate k 0)
    exact h_tr_zero.trans (mem_ker_truncate k x)

/-- Two facts on the coefficient `ℤ_ℓ`: (a) there is a map `q` to `𝔽_ℓ` with
`0 → ℤ_ℓ → ℤ_ℓ → 𝔽_ℓ → 0` exact, the first map being `ℓ`; (b) every `Ext^n(N, ℤ_ℓ)` is derived
`ℓ`-complete (`IsDerivedComplete`; `ℓ`-adic completeness implies it, and it allows solving by
successive approximation) (this does not involve `q`). -/
lemma exists_ellAdicCoeff_modShortExact :
    ∃ q : ellAdicCoeff ⟶ locConstCoeff ⟨ZMod ℓ⟩,
      ModShortExact ↑ℓ q ∧
      ∀ (N : AbFunctor TestRing) (n : ℕ), IsDerivedComplete (ℓ : ℤ_[ℓ]) (H N ellAdicCoeff n) := by
  -- `q` is the zeroth Witt coordinate; both claims are checked at each test ring.
  let C (A : TestRing) : CommAlg (ZMod ℓ) := (locConstAlg (p := ℓ)).obj (testIncl.obj A)
  refine ⟨_, modShortExact_of_isReductionMod
    (q := .mk fun _ ↦ AddCommGrpCat.ofHom constantCoeff.toAddMonoidHom) fun A ↦ ?_, ?_⟩
  · -- at a test ring `A`, the zeroth coordinate is reduction modulo `ℓ` on an `ℓ`-torsion-free ring
    obtain ⟨h_red, h_complete, -, -⟩ := isReductionMod_constantCoeff_and_isCompleteTorsionFree
      (ZMod ℓ) (C A)
    exact ⟨h_complete.regular, h_red⟩
  · -- the coefficients are `ℓ`-adically complete and `ℓ`-torsion-free at every test ring, hence
    -- derived `ℓ`-complete, and so their cohomology is derived `ℓ`-complete
    refine IsDerivedComplete.cohomology fun A ↦ ?_
    obtain ⟨-, h_complete, -, -⟩ := isReductionMod_constantCoeff_and_isCompleteTorsionFree (ZMod ℓ)
      (C A)
    exact IsCompleteTorsionFree.isDerivedComplete (B := (wittFunctor _).obj _) h_complete

/-- If `Ext^n(N, 𝔽_ℓ)` is finite, then `Ext^n(N, ℤ_ℓ)` is a finitely generated `ℤ_ℓ`-module. -/
lemma finite_H_ellAdicCoeff {N : AbFunctor TestRing}
    (h_finite : Finite (H N (locConstCoeff ⟨ZMod ℓ⟩) n)) :
    Module.Finite ℤ_[ℓ] (H N ellAdicCoeff n) := by
  -- Write `H = Ext^n(N, ℤ_ℓ)` and `q` for its reduction modulo `ℓ`. Choose lifts (`invFun q`) of
  -- the classes in the image of `q`: they give a map `f` to `H` from the free module on the finite
  -- set `Ext^n(N, 𝔽_ℓ)` with `H = im f + ℓ H`, and completeness of both sides makes `f` onto.
  obtain ⟨c, h_exact, h_complete⟩ := exists_ellAdicCoeff_modShortExact (ℓ := ℓ)
  let q : H N ellAdicCoeff n →+ H N (locConstCoeff ⟨ZMod ℓ⟩) n := H.push N c n
  let b := basisFun ℤ_[ℓ] (H N (locConstCoeff ⟨ZMod ℓ⟩) n)
  let f : (H N (locConstCoeff ⟨ZMod ℓ⟩) n → ℤ_[ℓ]) →ₗ[ℤ_[ℓ]] H N ellAdicCoeff n :=
    b.constr ℕ (invFun q)
  have hZ : IsDerivedComplete (ℓ : ℤ_[ℓ]) ℤ_[ℓ] := .of_isAdicComplete <| by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  -- successive approximation: it is enough to write each `y` as an element of `im f` plus `ℓ • z`
  refine .of_surjective f ((h_complete N n).exists_apply_eq_of_approx hZ.pi f id fun y ↦ ?_)
  -- `y` and the chosen lift of `q y` have the same reduction, so they differ by a multiple of `ℓ`
  have h_push_zero : H.push N c n (y - invFun q (q y)) = 0 := by simp [q, invFun_eq]
  obtain ⟨z, hz⟩ := h_exact.exists_smul_eq_of_push_eq_zero (y - invFun q (q y)) h_push_zero
  have h_approx : y = f (b (q y)) + (ℓ : ℤ_[ℓ]) • z := by simp [f, hz]
  exact ⟨b (q y), z, h_approx⟩

/-- An equivalence for `𝔽_ℓ`-coefficients induces bijections on `ℓ`-adic cohomology. -/
lemma IsCohomEquiv.bijective_ellAdicPull {M N : AbFunctor TestRing} {α : M ⟶ N}
    (h_equiv : IsCohomEquiv (locConstCoeff ⟨ZMod ℓ⟩) α) :
    Bijective (ellAdicPull (ℓ := ℓ) n α) := by
  obtain ⟨q, h_exact, h_complete⟩ := exists_ellAdicCoeff_modShortExact (ℓ := ℓ)
  -- Bijective modulo `ℓ` and derived `ℓ`-complete on both sides, so bijective over `ℤ_ℓ`: `of_mod`
  -- applied to the identity map of coefficients.
  have hZ : IsCohomEquiv ellAdicCoeff α :=
    (h_equiv.bij.of_mod (β := 𝟙 (𝟭 _ ⋙ _)) h_exact h_exact rfl (fun m _ ↦ h_complete N m)
      (h_complete M)).eqv
  -- `ellAdicPull` is the base change of this map to `ℚ_ℓ`
  exact map_bijective (f := 1) bijective_id (hZ n)

end New.Variety

end
