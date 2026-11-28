import Lib.Cohomology.Etale.BijectiveComparisons
import Lib.PadicComparison.Descent.TestCategory

/-!
# Flat base change in functor cohomology, and the base change adjunction for algebras

Cohomology here is H^n(N, Φ) = Ext^n(N, Φ) in the category of functors from C to abelian groups,
where Φ is a functor to S-modules. For a module M over an S-algebra T, the base change map
`New.Variety.baseChangeMap` goes from M ⊗_S H^n(N, Φ) to H^n(N, M ⊗_S Φ).
`New.Variety.HasFlatBaseChange N` says that this map is bijective for all S, T, Φ, n and all M flat
over S. The file proves bijectivity for N = ℤ[h_A], with h_A the functor represented by A, by the
Yoneda lemma, shows that for flat M the maps admit dévissage in N, and transfers bijectivity along
bijective comparisons. It also shows that base change of algebras is left adjoint to restriction of
scalars, and that ring maps send powers of p to powers of p.

## Main definitions and results

* `New.Variety.HasBaseChange.baseChangeMap_bijective_freeAb_reprBy`: the base change map is
  bijective for N = ℤ[h_A], by the Yoneda lemma.
* `New.Variety.HasBaseChange.devissage`: for M flat it admits dévissage, being compatible with the
  long exact sequences of short exact sequences.
* `New.Variety.Comparison.IsBijective.baseChangeMap_bijective_iff`: along a bijective comparison
  from an N with flat base change, base change by a flat M on the target holds exactly when the
  comparison stays bijective after tensoring the coefficients with M.
* `New.Variety.algBaseChangeAdj`: for a k-algebra S, the functor A ↦ S ⊗_k A
  (`New.Variety.algBaseChange`) is left adjoint to restriction of scalars
  (`New.Variety.restrictAlg`).
* `New.Variety.pointMap_algBaseChange_unit_bijective`: the base change S ⊗_k B represents Hom(B, -)
  on S-algebras.

Notions from other files:
* `New.Variety.moduleCoeff`: A functor F from C to k-modules, regarded as a functor to abelian
  groups, so that it can serve as the coefficients of cohomology.
* `New.Variety.freeAb`: The functor sending a set-valued functor Y to Z[Y], whose value at A is the
  free abelian group on Y(A).
* `New.Variety.tensorWith`: For a module M over the S-algebra T, the functor X ↦ M ⊗_S X from
  S-modules to T-modules.

## Relation to the literature

The arguments are the usual ones: the Yoneda lemma, exactness of tensoring with a flat module, and
the tensor-hom adjunction.
-/

namespace New.Variety

/-! ## Flat base change in functor cohomology: representable case and dévissage -/

section TensorCohomology

open CategoryTheory TensorProduct Function Module Flat Abelian.Ext H Comparison LongExactSeq Functor

variable {C C' : Type 1} [Category C] [Category C']
  {S T M : Type} [CommRing S] [CommRing T] [Algebra S T] [AddCommGroup M] [Module S M]
  [Module T M] [IsScalarTower S T M]
  {Φ : C ⥤ ModuleCat S} {Φ' : C' ⥤ ModuleCat S} {φ : C' ⥤ C} {N K : AbFunctor C} {N' : AbFunctor C'}
  {n : ℕ} (β : φ ⋙ Φ ⟶ Φ') (α : N' ⟶ φ ⋙ N)

/-- The base change map sends m ⊗ x to the image of the class x under the map of coefficients
y ↦ m ⊗ y. -/
@[simp]
lemma baseChangeMap_tmul (m : M) (x : H N (moduleCoeff Φ) n) :
    baseChangeMap T M N Φ n (m ⊗ₜ x) = push N (tensorWith.mk T m Φ) n x :=
  (rfl)

/-- For β: Φ∘φ → Φ' of functors to S-modules and α: N' → N∘φ, the comparison map H^n(N, Φ) → H^n(N',
Φ') (the map `pull α` of the comparison `ofModuleHom φ β` built from β), as an S-linear map. -/
noncomputable def Comparison.pullₗ (n : ℕ) :
    H N (moduleCoeff Φ) n →ₗ[S] H N' (moduleCoeff Φ') n where
  __ := (ofModuleHom φ β).pull α n
  map_smul' s := by
    -- A scalar acts by pushing along an endomorphism of the coefficients, which commutes with `β`.
    apply pull_push ⟨φ, _⟩
    ext
    apply_rules [ULift.ext, LinearMap.map_smul]

/-- The linear comparison map `pullₗ` has the same values as the additive one. -/
lemma Comparison.pullₗ_apply (x : H N (moduleCoeff Φ) n) :
    pullₗ β α n x = (ofModuleHom φ β).pull α n x :=
  rfl

/-- For β: Φ∘φ → Φ' and m ∈ M, the maps of coefficients y ↦ m ⊗ y (`tensorWith.mk T m`) commute with
β and M ⊗_S β, regarded as maps of coefficients in abelian groups (`coeffHom` of `ofModuleHom`):
both composites send y to m ⊗ β y. -/
lemma tensorWith.whiskerLeft_mk_comp_coeffHom (m : M) :
    whiskerLeft φ (tensorWith.mk T m Φ) ≫
        (ofModuleHom (Φ := Φ ⋙ tensorWith T M) φ (whiskerRight β (tensorWith T M))).coeffHom =
      (ofModuleHom φ β).coeffHom ≫ tensorWith.mk T m Φ' :=
  rfl

/-- Let β: Φ∘φ → Φ' be a map of functors to S-modules and α: N' → N∘φ. The base change maps
M ⊗_S H^n(N, Φ) → H^n(N, M ⊗_S Φ), and likewise for N' and Φ', commute with the comparison maps
`pullₗ` induced by (β, α) and by (M ⊗_S β, α). Here `tensorWith T M` is the functor M ⊗_S –, and
`moduleCoeff Φ` is Φ regarded as a functor to abelian groups. -/
lemma baseChangeMap_pull (x : M ⊗[S] H N (moduleCoeff Φ) n) :
    baseChangeMap T M N' Φ' n ((pullₗ β α n).lTensor M x) =
      pullₗ (Φ := Φ ⋙ tensorWith T M) (Φ' := Φ' ⋙ tensorWith T M)
        (whiskerRight β (tensorWith T M)) α n (baseChangeMap T M N Φ n x) := by
  induction x with
  | add => simp [*]
  | tmul m x =>
    exact (pull_push (ofModuleHom φ β) _ (tensorWith.mk T m Φ) (tensorWith.mk T m Φ')
      (tensorWith.whiskerLeft_mk_comp_coeffHom β m) α x).symm

/-- The Yoneda isomorphism `homReprEquiv`: Hom(ℤ[h_A], K) ≅ K(A), h_A the functor represented by A,
is natural in K: for a map γ: K → N of functors to abelian groups and x ∈ K(A), pushing along γ the
class of degree 0 that corresponds to x gives the class that corresponds to γ_A(x). Here `mk₀`
sends a morphism to its class in Ext^0. -/
lemma push_homReprEquiv_symm (γ : K ⟶ N) (A : C) (x : (K.obj A)) :
    push (freeAb (reprBy A)) γ 0 (mk₀ ((homReprEquiv A K).symm x)) =
      mk₀ ((homReprEquiv A N).symm (γ A x)) := by
  have h_natural (f : freeAb.obj (reprBy A) ⟶ K) :
      homReprEquiv A N (f ≫ γ) = γ.app A (homReprEquiv A K f) := rfl
  have h_comp : (homReprEquiv A K).symm x ≫ γ = (homReprEquiv A N).symm (γ A x) := by
    simp [AddEquiv.eq_symm_apply, h_natural]
  exact (mk₀_comp_mk₀ _ _).trans (congrArg mk₀ h_comp)

/-- The Yoneda isomorphism Φ(A) ≅ H^0(ℤ[h_A], Φ), as an S-linear map. -/
noncomputable def HasBaseChange.yonedaEquiv₀ (Φ : C ⥤ ModuleCat S) (A : C) :
    Φ.obj A ≃ₗ[S] H (freeAb.obj (reprBy A)) (moduleCoeff Φ) 0 :=
  AddEquiv.toLinearEquiv
    (show Φ.obj A ≃+ H (freeAb.obj (reprBy A)) (moduleCoeff Φ) 0 from
      (addEquiv₀.trans ((homReprEquiv A (moduleCoeff Φ)).trans .ulift)).symm) fun s x ↦ by
    -- A scalar acts on classes by pushing along an endomorphism of the coefficients.
    rw [smul_eq_push]
    exact (push_homReprEquiv_symm (CoeffAction.act s : End (moduleCoeff Φ)).asHom A (.up x)).symm

/-- `yonedaEquiv₀` sends x to the class of the map ℤ[h_A] → Φ that corresponds to x. -/
lemma HasBaseChange.yonedaEquiv₀_apply (Φ : C ⥤ ModuleCat S) (A : C) (x : Φ.obj A) :
    yonedaEquiv₀ Φ A x = mk₀ ((homReprEquiv A (moduleCoeff Φ)).symm (ULift.up x)) :=
  rfl

/-- For every object A, the map M ⊗_S H^n(ℤ[h_A], Φ) → H^n(ℤ[h_A], M ⊗_S Φ) is bijective in
every degree n (`AllBijective`), h_A the functor represented by A; no flatness of M is assumed. -/
lemma HasBaseChange.baseChangeMap_bijective_freeAb_reprBy (A : C) :
    AllBijective fun n : ℕ ↦ baseChangeMap T M (freeAb (reprBy A)) Φ n := by
  -- Both sides vanish in positive degree, as `ℤ[h_A]` is projective; in degree zero both are
  -- `M ⊗ Φ A` by the Yoneda lemma.
  rintro (_ | n)
  · let e : Φ.obj A ≃ₗ[S] H (freeAb.obj (reprBy A)) (moduleCoeff Φ) 0 := yonedaEquiv₀ Φ A
    let e' : M ⊗[S] Φ.obj A ≃+ (freeAb.obj (reprBy A) ⟶ moduleCoeff (Φ ⋙ tensorWith T M)) :=
      ((homReprEquiv A (moduleCoeff (Φ ⋙ tensorWith T M))).trans .ulift).symm
    have h_square (x : M ⊗[S] Φ.obj A) : baseChangeMap T M _ Φ 0 (e.lTensor M x) = mk₀ (e' x) := by
      induction x with
      | add => simp [*, mk₀_add]
      | tmul m x =>
        rw [LinearEquiv.lTensor_tmul, baseChangeMap_tmul, yonedaEquiv₀_apply]
        exact push_homReprEquiv_symm (tensorWith.mk T m Φ) A (ULift.up x)
    exact (bijective_iff_of_comm_sq h_square (e.lTensor M).bijective (mk₀_bijective _ _)).1
      e'.bijective
  · exact ⟨injective_of_subsingleton _, fun y ↦ ⟨0, Subsingleton.elim _ y⟩⟩

/-- The functor ℤ[h_A] has flat base change, h_A being the functor represented by A: the map
M ⊗_S H^n(ℤ[h_A], Φ) → H^n(ℤ[h_A], M ⊗_S Φ) is bijective for all n, all Φ and all flat M. -/
lemma hasFlatBaseChange_freeAb_reprBy (A : C) : HasFlatBaseChange (freeAb (reprBy A)) := by
  simp [HasFlatBaseChange, HasBaseChange.baseChangeMap_bijective_freeAb_reprBy]

/-- Composition with a class e in Ext^a(N', N), as an S-linear map from H^n(N, Φ) to
H^(a+n)(N', Φ). -/
noncomputable def HasBaseChange.precompₗ (Φ : C ⥤ ModuleCat S) {N N' : AbFunctor C} {a n n' : ℕ}
    (e : H N' N a) (h : a + n = n') : H N (moduleCoeff Φ) n →ₗ[S] H N' (moduleCoeff Φ) n' where
  toFun := e.precomp _ h
  map_add' := map_add _
  map_smul' := by simp [smul_eq_push, push]

/-- The base change map M ⊗_S H^n(N, Φ) → H^n(N, M ⊗_S Φ) turns M ⊗ (composition with a class e,
`precompₗ`) into composition with e. -/
lemma HasBaseChange.baseChangeMap_lTensor_precompₗ {N N' : AbFunctor C} {a n n' : ℕ}
    (e : H N' N a) (h : a + n = n') (x : M ⊗[S] H N (moduleCoeff Φ) n) :
    baseChangeMap T M N' Φ n' ((precompₗ Φ e h).lTensor M x) =
      e.comp (baseChangeMap T M N Φ n x) h := by
  induction x with
  | add => simp [*]
  | tmul m x => simp [precompₗ, H.push]

/-- For M flat, the long exact sequence of Ext(–, Φ) of a short exact sequence X, tensored
with M. -/
noncomputable def HasBaseChange.tensoredSeq (M : Type) [AddCommGroup M] [Module S M] [Flat S M]
    (Φ : C ⥤ ModuleCat S) {X : ShortComplex (AbFunctor C)} (hX : X.ShortExact) : LongExactSeq where
  A n := .of (M ⊗[S] H X.X₃ (moduleCoeff Φ) n)
  B n := .of (M ⊗[S] H X.X₂ (moduleCoeff Φ) n)
  C n := .of (M ⊗[S] H X.X₁ (moduleCoeff Φ) n)
  f n := ((precompₗ Φ (mk₀ X.g) n.zero_add).lTensor M).toAddMonoidHom
  g n := ((precompₗ Φ (mk₀ X.f) n.zero_add).lTensor M).toAddMonoidHom
  δ n := ((precompₗ Φ hX.extClass n.one_add).lTensor M).toAddMonoidHom
  injective_f :=
    lTensor_preserves_injective_linearMap (precompₗ Φ (mk₀ X.g) _)
      (contravariant hX (moduleCoeff Φ)).injective_f
  exact_f_g n := lTensor_exact M ((contravariant hX (moduleCoeff Φ)).exact_f_g n)
  exact_g_delta n := lTensor_exact M ((contravariant hX (moduleCoeff Φ)).exact_g_delta n)
  exact_delta_f n := lTensor_exact M ((contravariant hX (moduleCoeff Φ)).exact_delta_f n)

/-- For M flat over S, with M a module over the S-algebra T, the maps M ⊗_S H^n(N, Φ) → H^n(N,
M ⊗ Φ) admit dévissage in N (`New.Variety.Devissage`): the four and five lemmas apply to them along
short exact sequences, and they are bijective for N = 0. -/
lemma HasBaseChange.devissage [Flat S M] :
    Devissage fun (N : C ⥤ Ab) (n : ℕ) ↦ baseChangeMap T M N Φ n := by
  -- For `M` flat, `M ⊗ –` of the long exact sequence of `Ext (–, Φ)` is again long exact, and
  -- `baseChangeMap` maps it to the long exact sequence of `Ext (–, M ⊗ Φ)`.
  let base {N : AbFunctor C} (n : ℕ) :
      M ⊗[S] H N (moduleCoeff Φ) n →+ H N (moduleCoeff (Φ ⋙ tensorWith T M)) n :=
    (baseChangeMap T M N Φ n).toAddMonoidHom
  have h_hom (X : ShortComplex (AbFunctor C)) (hX : X.ShortExact) :
      Hom (tensoredSeq M Φ hX) (contravariant hX (moduleCoeff (Φ ⋙ tensorWith T M)))
        base base base :=
    { comm_f := fun _ x ↦ baseChangeMap_lTensor_precompₗ _ _ x
      comm_g := fun _ x ↦ baseChangeMap_lTensor_precompₗ _ _ x
      comm_delta := fun _ x ↦ baseChangeMap_lTensor_precompₗ _ _ x }
  refine ⟨⟨fun hX ↦ (h_hom _ hX).four_lemma⟩, fun N hN ↦ ?_, fun X hX ↦ (h_hom X hX).five_lemma⟩
  -- For the zero functor both sides are trivial.
  have (F : AbFunctor C) (n : ℕ) : Subsingleton (H N F n) := subsingleton_of_id_eq_zero hN F n
  simp [nontriviality, AllBijective, Bijective, Surjective]

/-- `IsAcyclicAt φ F B` says that restriction along φ (the comparison `Comparison.restrict φ F`,
taken with α = `freeAbMap` of the identity of h_B∘φ) from H^n(ℤ[h_B], F) to H^n(ℤ[Hom(B, φ –)], F∘φ)
is bijective for all n; so the latter is F(B) in degree 0 and zero in positive degree. -/
abbrev IsAcyclicAt (φ : C' ⥤ C) (F : AbFunctor C) (B : C) : Prop :=
  IsBijective (Comparison.restrict φ F) (freeAbMap (𝟙 (φ ⋙ reprBy B)))

variable {D : Type*} [Category D] {Ψ : C ⥤ D}

/-- For β: Ψ∘φ → Ψ', α: N' → N∘φ and a functor F to S-modules, the statement that the comparison map
(built from F∘β and α, as in `pullₗ`; `IsBijective` of `ofModuleHom`) H^n(N, F∘Ψ) → H^n(N', F∘Ψ') is
bijective for all n. -/
abbrev CoeffCompBijective {Ψ' : C' ⥤ D} (β : φ ⋙ Ψ ⟶ Ψ') (α : N' ⟶ φ ⋙ N) (F : D ⥤ ModuleCat S) :
    Prop :=
  (ofModuleHom (S := S) φ (Φ := Ψ ⋙ F) (whiskerRight β F)).IsBijective α

/-- Suppose β and α induce bijections H^n(N, Φ) → H^n(N', Φ'), M is flat over S and N has flat
base change (its base change maps are bijective for every flat tensor factor). Then
M ⊗ H^n(N', Φ') → H^n(N', M ⊗ Φ') is bijective for all n if and only if the comparison map
H^n(N, M ⊗ Φ) → H^n(N', M ⊗ Φ') is, which is what `CoeffCompBijective` says. -/
lemma Comparison.IsBijective.baseChangeMap_bijective_iff {β : φ ⋙ Φ ⟶ Φ'} {α : N' ⟶ φ ⋙ N}
    (hβ : (ofModuleHom φ β).IsBijective α) [Flat S M] (hN : HasFlatBaseChange N) :
    (AllBijective fun n : ℕ ↦ baseChangeMap T M N' Φ' n) ↔ CoeffCompBijective β α
      (tensorWith T M) := by
  -- In the commutative square `baseChangeMap_pull`, the comparison tensored with `M` and the map
  -- `baseChangeMap` for `N` are bijective; so one of the other two is bijective iff the other is.
  refine forall_congr' fun n ↦ ?_
  have h_ten : Bijective ((pullₗ β α n).lTensor M) := map_bijective bijective_id (hβ n)
  have h_square : baseChangeMap T M N' Φ' n ∘ (pullₗ β α n).lTensor M =
      pullₗ (Φ := Φ ⋙ tensorWith T M) (Φ' := Φ' ⋙ tensorWith T M)
        (whiskerRight β (tensorWith T M)) α n ∘ baseChangeMap T M N Φ n :=
    funext (baseChangeMap_pull β α)
  rw [← h_ten.of_comp_iff, h_square]
  exact (hN S T M Φ n).of_comp_iff _

end TensorCohomology

/-! ## Base change of algebras as left adjoint to restriction of scalars -/

section BaseChangeAdjunction

open CategoryTheory ConcreteCategory

variable {C k S : Type _} [Category C] [CommRing k] [CommRing S] [Algebra k S]

/-- Base change from commutative k-algebras to commutative S-algebras is left adjoint to
restriction of scalars. -/
def algBaseChangeAdj : algBaseChange S ⊣ restrictAlg k S :=
  Adjunction.mkOfHomEquiv
    { -- `S`-algebra maps `S ⊗ A → B` correspond to `k`-algebra maps `A → B` (`AlgHom.liftEquiv`,
      -- with the `k`-algebra structure on `B` given by restriction of scalars; type class search
      -- does not find it, so it is left to unification and the scalar tower is given explicitly)
      homEquiv A B :=
        homEquiv.trans (Equiv.symm (homEquiv.trans
          (@AlgHom.liftEquiv k S A B _ _ _ _ _ _ _ (_) (IsScalarTower.of_compHom k S B))))
      -- both sides agree on pure tensors
      homEquiv_naturality_left_symm _ _ := ext (tmul_ext fun _ _ ↦ by rfl) }

/-- For functors X to k-algebras and Y to S-algebras, the bijection between natural S-algebra maps
S ⊗_k X → Y and natural k-algebra maps X → Y. Its inverse sends β to the map s ⊗ a ↦ s • β a. -/
abbrev baseChangeTranspose :
    (X : C ⥤ CommAlg k) → (Y : C ⥤ CommAlg S) →
      (((Functor.whiskeringRight C (CommAlg k) (CommAlg S)).obj (algBaseChange S)).obj X ⟶ Y) ≃
        (X ⟶ ((Functor.whiskeringRight C (CommAlg S) (CommAlg k)).obj (restrictAlg k S)).obj Y) :=
  ((algBaseChangeAdj (k := k) (S := S)).whiskerRight C).homEquiv

/-- For a k-algebra B and an S-algebra A, composing with the unit B → S ⊗ B is a bijection from the
S-algebra maps S ⊗ B → A to the k-algebra maps B → A. Here `pointMap` is the Yoneda map given by
the unit, from Hom(S ⊗ B, –) to Hom(B, –) restricted to S-algebras. -/
lemma pointMap_algBaseChange_unit_bijective (B : CommAlg k) :
    AllBijective fun A : CommAlg S ↦
      pointMap (Y := restrictAlg k S ⋙ reprBy B) ⟨algBaseChangeAdj.unit B⟩ A :=
  fun A ↦
    -- up to universe lifts, this map is the bijection of hom-sets of the adjunction
    ULift.map_bijective.2 (algBaseChangeAdj.homEquiv B A).bijective

end BaseChangeAdjunction

end New.Variety

/-!
## Ring maps and powers of p

A ring map `f : A → B` sends powers of p to powers of p; this is the condition under which it
induces a map of localisations `A[1/p] → B[1/p]`.
-/

/-- Every ring map f : A → B maps the powers of a natural number p in A into the powers of p
in B. -/
lemma New.Variety.powers_le_comap_powers (p : ℕ) {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) :
    Submonoid.powers (p : A) ≤ (Submonoid.powers (p : B)).comap f := by
  simp [Submonoid.powers_le]
