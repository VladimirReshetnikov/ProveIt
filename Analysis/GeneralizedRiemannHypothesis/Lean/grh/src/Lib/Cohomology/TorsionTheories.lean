import Lib.Adelic.Unitary.Defs
import Lib.Cohomology.Etale.RelativeChains
import Lib.Cohomology.LerayHirsch
import Lib.General.Algebra.CohomologyBaseChange
import Lib.PadicComparison.HodgeTate.ExtCocycles

/-!
# Tensoring degree-two classes; cohomology theories with ℓ-torsion coefficients

The file works in categories of functors to abelian groups. First, a class in `Ext² (N, K)` between
functors with flat values is restricted along any functor and tensored with any abelian-group-valued
functor, compatibly (`New.Variety.exists_isTensorClass`). Then the cohomology of a space over `X` is
computed on the category of elements of `X`. Last, the file treats cohomology theories with
`ℓ`-torsion coefficients on categories over the test rings, families of ideals, and the theory of
locally constant functions.

## Main definitions and results

* `New.Variety.IsTensorClass`, `New.Variety.exists_isTensorClass`: a family of classes that extends
  `S ⊗ ξ` from functors `S` with flat values to all functors, and its existence.
* `New.Variety.hasUniversalPoints_elements`,
  `New.Variety.isBijective_relFreeAb_tautologicalSection`, `New.Variety.sliceEquiv`: cohomology of a
  space over `X` is computed on the category of elements of `X` (`New.Variety.elementsProj`).
* `New.Variety.InvertsPrime`, `New.Variety.TestOver`: a local absolutely integrally closed ring `A`
  in which `ℓ` is invertible, and the category of test rings over `A`.
* `New.Variety.TorsionCoeff`, `New.Variety.Theory`: coefficients with Zariski descent, and theories,
  where classes also extend from closed loci. `New.Variety.Theory.locallyConstant` is the theory of
  locally constant functions.
* `New.Variety.IdealFamily`, `New.Variety.Theory.onZeros`: a compatible family of ideals, and the
  coefficient that sees only the locus where it is zero.
* `New.Variety.IdealFamily.isCohomEquiv_constToZeros`,
  `New.Variety.TorsionCoeff.pullbackAlong_oneLocConst_surjective`: the map from `ℤ/ℓ` relative to
  the locus where the ideal is the unit ideal to the locally constant functions on the zero locus is
  an equivalence for coefficients with Zariski descent, provided the locally constant functions
  along `g` underlie a theory `Θ`; hence every class on the constant functor `ℤ` with coefficients
  in a `TorsionCoeff g` (killed by `ℓ`, with Zariski descent) comes from one on the locally constant
  functions to `ℤ/ℓ`.

Notions from other files:
* `New.Variety.HasFlatValues F`: every value of `F` is a flat `ℤ`-module.
* `New.Variety.restrictAlong φ`, `New.Variety.freeAb`: the functor `N ↦ N ∘ φ`, and the functor
  sending a set-valued functor `Y` to `ℤ[Y]`, the free abelian group on `Y(A)` at each `A`.
* `New.Variety.relFreeAb U`, `New.Variety.abCoker α`: the functor `ℤ[V]/ℤ[U]` for `U ⊆ V`, whose Ext
  groups are the relative cohomology of `(V, U)`; the cokernel of `α`, formed objectwise.
* `New.Variety.IsTest`: a test ring A is reduced and absolutely integrally closed, and any a, b ∈ A
  admit an idempotent e with a ∣ eb and b ∣ (1 − e)a.
* `New.Variety.Comparison`: a functor φ : C' → C with a map F∘φ → F'; it `IsBijective` along α :
  N' → N∘φ if Ext^n(N, F) → Ext^n(N', F') is bijective for all n. `HasUniversalPoints u`, a
  sufficient condition: the fibres of u over points are representable, with the same coefficients.
* `New.Variety.IsCohomDense`, `New.Variety.HasZariskiDescent`: `U ⊆ Y` is dense for `F` if, for
  every point `h_A → Y`, the inclusion of the preimage of `U` induces bijections on Ext with
  coefficients `F`; `F` has Zariski descent if every `U` that contains `Y` near each maximal ideal
  (`New.Variety.IsZariskiLocallyTop`) is dense for `F`.

## Relation to the literature

Known result: Cup product with a degree-two class and closed supports, for mod-ℓ cohomology as Ext.
Only the formal set-up is given, for Ext on test rings. It consists of ℓ-torsion coefficient
theories with closed supports cut out by families of ideals, and a degree-two class between flat
functors tensored with every functor. No Chern class, Künneth formula, Gysin map or Poincaré duality
is stated here. Source: for the setting, Milne, Étale Cohomology, Ch. VI.

See also `Lib.Cohomology.Etale.FilteredLimits` and `Lib.PadicComparison.Duality.GoodPairs`.
-/

noncomputable section

namespace New.Variety

/-!
## Tensoring a degree 2 class between flat functors with every functor

A class `ξ` in `Ext² (N, K)` between functors with flat values is written as a product of two
extension classes of short exact sequences that stay exact after tensoring, and a map.

Conventions: `New.Variety.AbFunctor` is the category of covariant functors to abelian groups,
`New.Variety.H` is `Ext` in it, `New.Variety.TotalH` the sum over all degrees with the Yoneda
product `New.Variety.TotalH.comp`, and `New.Variety.abTensor` the pointwise tensor product.
-/

section TensoringClasses

open CategoryTheory Abelian TotalH AddCommGrpCat

variable {C : Type 1} [Category.{0} C] {N K : AbFunctor C}
set_option backward.isDefEq.respectTransparency false

/-- The constant functor on C with value the one-point set. -/
abbrev onePointFunctor (C : Type*) [Category C] : C ⥤ Type 1 := Functor.const C PUnit.{2}

/-- For `ρ : ℤ[pt] ⟶ K`, that is, a family of elements `ρ [pt]` of the values of `K` compatible
with the maps of `K`, the map `S ⟶ S ⊗ K`, `x ↦ x ⊗ ρ [pt]`, natural in `S`. -/
def tensorPoint (ρ : freeAb.obj (onePointFunctor C) ⟶ K) :
    𝟭 (AbFunctor C) ⟶ abTensor.flip.obj K where
  app S :=
    { app c :=
        ofHom ((TensorProduct.mk ℤ (S.obj c) (K.obj c)).flip
          (ρ.app c (FreeAbelianGroup.of ⟨⟩))).toAddMonoidHom
      naturality c c' f := by
        -- The elements `ρ.app c (.of ⟨⟩)` are compatible with the maps of `K`; so on `x` both
        -- sides are `S.map f x ⊗ K.map f (ρ [pt])`, by the definition of `abTensor`.
        rw [show ρ.app c' (.of ⟨⟩) = K.map f (ρ.app c (.of ⟨⟩)) from ρ.naturality_apply f (.of ⟨⟩)]
        rfl }

/-- A family of classes in `Ext² (S ⊗ φ^* N, S ⊗ φ^* K)`, one for every functor `φ : D ⥤ C` and
every functor `S` from `D` to abelian groups; `φ^* N` is `φ ⋙ N`. -/
abbrev TensorClassFamily (N K : AbFunctor C) : Type 2 :=
  ∀ (D : Type 1) [Category.{0} D] (φ : D ⥤ C) (S : AbFunctor D),
    H ((abTensor.flip.obj (φ ⋙ N)).obj S) ((abTensor.flip.obj (φ ⋙ K)).obj S) 2

/-- The family `h` extends `(φ, S) ↦ S ⊗ φ^* ξ` from flat `S` to all `S`, compatibly with classes
between the functors `S` and with restriction. The equations are in total cohomology. -/
structure IsTensorClass [HasFlatValues N] [HasFlatValues K] (ξ : H N K 2)
    (h : TensorClassFamily N K) : Prop where
  /-- For a class `y` from `S` to `S'`, `y ⊗ φ^* N` followed by `h D φ S'` is `h D φ S` followed
  by `y ⊗ φ^* K`. -/
  comm (D : Type 1) [Category.{0} D] (φ : D ⥤ C) (S S' : AbFunctor D) (y : TotalH S S') :
    comp (map (abTensor.flip.obj (φ ⋙ N)) y) (h D φ S').toTotalH =
      comp (h D φ S).toTotalH (map (abTensor.flip.obj (φ ⋙ K)) y)
  /-- For flat `S` the class is `ξ`, restricted along `φ` and tensored with `S`. -/
  eq_of_flat (D : Type 1) [Category.{0} D] (φ : D ⥤ C) (S : AbFunctor D) [HasFlatValues S] :
    (h D φ S).toTotalH = map (abTensor.obj S) (map (restrictAlong φ) ξ.toTotalH)
  /-- The classes are compatible with restriction along a further functor `ψ : E ⥤ D`. -/
  restrict (D : Type 1) [Category.{0} D] (φ : D ⥤ C) (S : AbFunctor D)
    (E : Type 1) [Category.{0} E] (ψ : E ⥤ D) :
    map (restrictAlong ψ) (h D φ S).toTotalH = (h E (ψ ⋙ φ) (ψ ⋙ S)).toTotalH

/-- Let `N` and `K` be functors with flat values and `ξ` a class in `Ext² (N, K)`. Then `ξ` can
be tensored with every functor, flat or not, compatibly: there is a family of classes in
`Ext² (S ⊗ φ^* N, S ⊗ φ^* K)`, for every functor `φ : D ⥤ C` and every `S` on `D`, that commutes
with classes between the `S`, is the restricted and tensored `ξ` for `S` with flat values, and is
compatible with restriction (`New.Variety.IsTensorClass`). -/
lemma exists_isTensorClass [HasFlatValues N] [HasFlatValues K] (ξ : H N K 2) :
    ∃ h : TensorClassFamily N K, IsTensorClass ξ h := by
  -- Cover N twice by sums of representables: ξ is the product of two extension classes and a map u.
  -- The two sequences stay exact after restricting and tensoring, which defines the new classes.
  -- `g M` is the cover of `M`; its extension class maps Extⁿ(ker, F) onto Extⁿ⁺¹(M, F) (`h_onto`).
  have h_cover : ∀ M : AbFunctor C, ∃ (ι : Type 1) (c : ι → C)
      (g : freeAb.obj (sigma fun i : ι ↦ reprBy (c i)) ⟶ M) (h_ses : (kerComplex g).ShortExact),
      ∀ (F : AbFunctor C) (n : ℕ),
        Function.Surjective ((LongExactSeq.contravariant h_ses F).δ n) :=
    fun M ↦ exists_acyclic_cover M
  choose ι c g h_exact h_onto using h_cover
  -- the values of the kernel of a cover are subgroups of free groups, so flat
  have h_flat_ker (M : AbFunctor C) : HasFlatValues (kerComplex (g M)).X₁ :=
    ⟨fun A ↦
      have := HasFlatValues.flat A (F := freeAb.obj (sigma fun i ↦ reprBy (c M i)))
      inferInstanceAs (Module.Flat ℤ ((g M).app A).hom.toIntLinearMap.ker)⟩
  let N₁ : AbFunctor C := (kerComplex (g N)).X₁
  -- ξ comes from degree 1 on the kernel N₁ and that from degree 0, so from a map u (`h_onto`)
  obtain ⟨u, rfl⟩ : ∃ u : (kerComplex (g N₁)).X₁ ⟶ K,
      (h_exact N).extClass.comp ((h_exact N₁).extClass.comp (.mk₀ u) rfl) rfl = ξ :=
    (h_onto N K 1).comp ((h_onto N₁ K 0).comp (Ext.mk₀_bijective _ K).surjective) ξ
  -- the cover of a flat M, restricted along φ, stays exact after tensoring with any functor
  have h_ses_tensor {D : Type 1} [Category.{0} D] (φ : D ⥤ C) (M : AbFunctor C) [HasFlatValues M]
      (S : AbFunctor D) :
      (ShortComplex.mk
        ((abTensor.flip.map (φ.whiskerLeft (kerComplex (g M)).f)).app S)
        ((abTensor.flip.map (φ.whiskerLeft (g M))).app S)
        (((kerComplex (g M)).map (restrictAlong φ)).map (abTensor.obj S)).zero).ShortExact :=
    abTensor_shortExact (G := φ ⋙ M) (G' := φ ⋙ (kerComplex (g M)).X₁)
      ((h_exact M).map_of_exact (restrictAlong φ)) S
  refine ⟨fun D _ φ S ↦ (h_ses_tensor φ N S).extClass.comp
      ((h_ses_tensor φ N₁ S).extClass.comp
        (.mk₀ ((abTensor.flip.map (φ.whiskerLeft u)).app S)) rfl) rfl,
    { comm := ?_, eq_of_flat := ?_, restrict := ?_ }⟩
  · intro D instD φ S S' y
    induction y using DirectSum.induction_on with
    | of a y =>
      -- y passes each extension class with the sign (-1) ^ a (`extClass_sign_comm`), and the two
      -- signs cancel; it passes the map induced by u by `naturality`
      -- (`map_of` and the `flip` simp lemmas are excluded)
      simp [N₁, ← comp_of, comp_assoc, naturality, smul_smul,
        comp_assoc_of_eq (extClass_sign_comm (h_ses_tensor φ _) _), ← mul_pow,
        -map_of, -Functor.flip_obj_obj, -Functor.flip_map_app]
    | zero => simp only [map_zero, AddMonoidHom.zero_apply]
    | add y y' hy hy' => simp only [map_add, AddMonoidHom.add_apply, hy, hy']
  · intro D instD φ S instS
    -- exact functors respect Yoneda products, extension classes and `mk₀`; then both sides are the
    -- same class, written with `abTensor.flip` or `abTensor`
    simp only [map_of, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
      Ext.mapExactFunctor_mk₀]
    rfl
  · intro D instD φ S E instE ψ
    -- likewise
    simp only [map_of, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
      Ext.mapExactFunctor_mk₀]
    rfl

end TensoringClasses

/-! ## Slices, torsion coefficients, families of ideals and theories -/

section Theories

open CategoryTheory Function QuotientAddGroup AddCommGrpCat ObjectProperty Abelian.Ext
  CategoryOfElements Ideal CommAlgCat CartesianMonoidalCategory TotalH Comparison H Subtype

export CartesianMonoidalCategory (toUnit)

set_option backward.isDefEq.respectTransparency false

variable {C C' : Type 1} [Category C] [Category C']
  {F G M N : AbFunctor C} {α : M ⟶ N} {X E : C ⥤ Type 1} (φ : C' ⥤ C) {F' N' : AbFunctor C'}
  {c : Comparison F F'}

/-! ### A sieve cut out by a map to an acyclic object -/

/-- Let `φ : C' ⥤ C` be full and faithful, `q : φ A ⟶ b`, and `R` a sieve on `A` such that a map `f`
out of `A` lies in `R` exactly when `φ f` factors through `q`, and then it factors uniquely. Let `b`
be acyclic for `F` along `φ` (`New.Variety.IsAcyclicAt`: with coefficients `φ ⋙ F`, `Hom (b, φ –)`
has cohomology `F b` in degree `0` only). If `F.map q` is onto, then in every degree `n` restriction
`H^n (h_A, φ ⋙ F) → H^n (R, φ ⋙ F)` is onto; here `h_A = reprBy A` is the functor `Hom (A, –)`,
lifted to a higher universe. -/
lemma surjective_restrict_of_quotient_sieve {A : C'} {R : Subfunctor (reprBy A)} [φ.Full]
    [φ.Faithful] {b : C} (q : φ A ⟶ b)
    (h_factor : ∀ {d : C'} (f : A ⟶ d), ⟨f⟩ ∈ R d → ∃! g : b ⟶ φ.obj d, q ≫ g = φ.map f)
    (h_mem : ∀ {d : C'} (f : A ⟶ d) (g : b ⟶ φ.obj d), q ≫ g = φ.map f → ⟨f⟩ ∈ R d)
    (h_acyclic : IsAcyclicAt φ F b) (h_onto : Surjective (F.map q)) (n : ℕ) :
    Surjective (H.map (φ ⋙ F) (freeAb.map R.ι) n) := by
  -- acyclicity of `b`: the cohomology of `φ ⋙ reprBy b` is `F b` in degree `0` (`h_sec`) and
  -- vanishes in positive degrees (`h_vanish`)
  obtain ⟨h_sec, h_vanish⟩ :
      Bijective ((Comparison.restrict φ F).homOfValue (𝟙 (φ ⋙ reprBy b))) ∧
        ∀ n : ℕ, Subsingleton (H (freeAb (φ ⋙ reprBy b)) (φ ⋙ F) (n + 1)) :=
    isBijective_reprBy_iff.mp h_acyclic
  -- composing with `q` identifies the maps out of `b` with the sieve `R`
  let v : φ ⋙ reprBy b ⟶ R.toFunctor :=
    { app d := ↾fun g ↦ ⟨_, h_mem _ g.down (φ.map_preimage _).symm⟩
      naturality d d' f := by
        ext
        simp [reprBy, reprFunctor, ← Category.assoc] }
  have hv_equiv : IsCohomEquiv (φ ⋙ F) (freeAb.map v) := by
    -- `v` sends `g : b ⟶ φ.obj d` to `f` exactly when `q ≫ g = φ.map f`
    exact .of_bijective fun d ↦ (bijective_iff_existsUnique _).mpr fun f ↦
      (Equiv.ulift.existsUnique_congr fun g ↦ by aesop).mpr (h_factor _ f.property)
  -- it suffices to be onto after pulling back along `v`
  refine (Surjective.of_comp_iff' (hv_equiv n) _).mp ?_
  cases n with
  | zero =>
    -- in degree `0` the target is `F b`, and the map is `F.map q`
    intro y
    -- `y` is `mk₀` of the map `homOfValue (F.map q x)` for some `x`, by `h_onto` and `h_sec`
    obtain ⟨x, rfl⟩ := (mk₀_bijective (freeAb.obj (φ ⋙ reprBy b)) (φ ⋙ F)).surjective.comp
      (h_sec.surjective.comp h_onto) y
    refine ⟨.mk₀ ((homReprEquiv A (φ ⋙ F)).symm x), ?_⟩
    -- both sides are `mk₀` of maps out of `ℤ[Hom (b, φ –)]`, which agree on generators
    -- on a generator `g`, both maps give `F.map (q ≫ g) x`
    have h_gen (d : C') (g : (φ ⋙ reprBy b).obj d) :
        F.map (φ.map (φ.preimage (q ≫ g.down))) x = F.map g.down (F.map q x) := by
      simp
    -- (on a generator both sides unfold to a value plus `0`; `add_left_inj` drops the `0`)
    have h_maps : freeAb.map v ≫ freeAb.map R.ι ≫ (homReprEquiv A (φ ⋙ F)).symm x =
        (Comparison.restrict φ F).homOfValue (𝟙 (φ ⋙ reprBy b)) (F.map q x) :=
      freeAb.hom_ext fun d g ↦ (add_left_inj 0).2 (h_gen d g)
    simpa [H.map] using congrArg mk₀ h_maps
  | succ n =>
    -- the target is zero
    have := h_vanish n
    exact surjective_to_subsingleton _

/-- Let `φ : C' ⥤ C` be full and faithful, `q : φ A ⟶ b`, and `R` a sieve on `A` that
contains every `f` such that `φ f` factors through `q`. Let `b` be acyclic for `F` along `φ`
(`New.Variety.IsAcyclicAt`). Then a section `x` of `F` at `φ A` that dies along every map in `R`
dies along `q`. -/
lemma map_eq_zero_of_dies_along_quotient_sieve {A : C'} {R : Subfunctor (reprBy A)} [φ.Full]
    [φ.Faithful] {b : C} (q : φ A ⟶ b)
    (h_mem : ∀ {d : C'} (f : A ⟶ d) (g : b ⟶ φ.obj d), q ≫ g = φ.map f → ⟨f⟩ ∈ R d)
    (h_acyclic : IsAcyclicAt φ F b) (x : (φ ⋙ F).obj A)
    (h_dies : ∀ (d : C') (f : A ⟶ d), ⟨f⟩ ∈ R d → (φ ⋙ F).map f x = 0) :
    F.map q x = 0 := by
  -- acyclicity of `b` in degree `0`: a section of `F` at `b` is determined by its images under
  -- all `g : b ⟶ φ.obj d`
  have h_sec : Bijective ((Comparison.restrict φ F).homOfValue (𝟙 (φ ⋙ reprBy b))) :=
    (isBijective_reprBy_iff.mp h_acyclic).1
  -- so it suffices to check `F.map q x` under each `g`, and `q ≫ g` lies in `R`
  refine h_sec.injective (freeAb.hom_ext fun d g ↦ ?_)
  rw [homOfValue_app]
  have h_zero : (φ ⋙ F).map (φ.preimage (q ≫ g.down)) x = 0 :=
    h_dies d _ (h_mem _ g.down (φ.map_preimage _).symm)
  simpa using h_zero

/-- Let `φ : C' ⥤ C` be full and faithful, `q : φ A ⟶ b`, and `R` the sieve of the maps `f` out of
`A` such that `φ f` factors, uniquely, through `q`. Let `b` be acyclic for `F` along `φ`
(`New.Variety.IsAcyclicAt`: with coefficients `φ ⋙ F`, `Hom (b, φ –)` has cohomology `F b` in
degree `0` only). (a) If `F.map q` is onto, restriction `H^n (h_A, φ ⋙ F) → H^n (R, φ ⋙ F)` is
onto for all `n`. (b) A section of `F` at `φ A` that dies along every map in `R` dies along `q`.
Part (a) is `New.Variety.surjective_restrict_of_quotient_sieve`, part (b) is
`New.Variety.map_eq_zero_of_dies_along_quotient_sieve`. -/
lemma surjective_and_map_eq_zero_of_quotient_sieve {A : C'} {R : Subfunctor (reprBy A)} [φ.Full]
    [φ.Faithful] {b : C} (q : φ A ⟶ b)
    (h_factor : ∀ {d : C'} (f : A ⟶ d), ⟨f⟩ ∈ R d → ∃! g : b ⟶ φ.obj d, q ≫ g = φ.map f)
    (h_mem : ∀ {d : C'} (f : A ⟶ d) (g : b ⟶ φ.obj d), q ≫ g = φ.map f → ⟨f⟩ ∈ R d)
    (h_acyclic : IsAcyclicAt φ F b) :
    (Surjective (F.map q) → ∀ n : ℕ, Surjective (H.map (φ ⋙ F) (freeAb.map R.ι) n)) ∧
    ∀ x : (φ ⋙ F).obj A, (∀ (d : C') (f : A ⟶ d), ⟨f⟩ ∈ R d → (φ ⋙ F).map f x = 0) →
      F.map q x = 0 :=
  ⟨fun h_onto n ↦ surjective_restrict_of_quotient_sieve φ q h_factor h_mem h_acyclic h_onto n,
    fun x h_dies ↦ map_eq_zero_of_dies_along_quotient_sieve φ q h_mem h_acyclic x h_dies⟩

/-! ### Slices: the category of elements of a set-valued functor -/

/-- For φ: C' → C and a section q of X∘φ, the functor a ↦ (φ(a), q(a)) from C' to the category
of elements of X. -/
def sectionLift (q : (φ ⋙ X).sections) : C' ⥤ X.Elements where
  obj c := X.elementsMk (φ.obj c) (q.1 c)
  map f := ⟨φ.map f, q.2 f⟩

/-- For a section q of a set-valued functor X, the morphism from the constant one-point functor
to X sending the point at c to q(c). -/
def sectionMap (q : X.sections) : onePointFunctor C ⟶ X := X.sectionsEquivHom PUnit.{2} q

/-- For a set-valued functor X on C, the projection (c, x) ↦ c to C from the category of elements of
X, whose objects are the pairs (c, x) with x ∈ X(c). -/
abbrev elementsProj (X : C ⥤ Type 1) : X.Elements ⥤ C := Functor.Elements.π X

/-- Universal points pass to categories of elements. Let `u : E' ⟶ c.functor ⋙ E` have universal
points (`New.Variety.Comparison.HasUniversalPoints`) for the comparison `c` from `F` to `F'`, and
let `X` be a set-valued functor on `C`. Then `u`, pulled back to the category of elements of
`c.functor ⋙ X`, has universal points for the comparison that `c` induces from the elements of `X`
(coefficient `F` restricted there) to those of `c.functor ⋙ X`. -/
lemma Comparison.HasUniversalPoints.on_elements {E' : C' ⥤ Type 1} {u : E' ⟶ c.functor ⋙ E}
    (hu : c.HasUniversalPoints u) :
    HasUniversalPoints (F := elementsProj X ⋙ F)
      (.of (Functor.Elements.precomp c.functor X)
        ((elementsProj (c.functor ⋙ X)).whiskerLeft c.coeffHom))
      (Y := elementsProj X ⋙ E) ((elementsProj (c.functor ⋙ X)).whiskerLeft u) := by
  intro a y
  -- the universal point `(x, s)` over `y`, with the element of `X` transported along `s`
  obtain ⟨b, x, s, hx_over, h_univ, h_coeff_bij⟩ := hu a.obj y
  refine ⟨(c.functor ⋙ X).elementsMk b (X.map s a.val), x, ⟨s, rfl⟩, hx_over, fun d w f hw ↦ ?_,
    h_coeff_bij⟩
  obtain ⟨g, ⟨hg_x, hg_comp⟩, h_uniq⟩ := h_univ d.obj w f.1 hw
  -- `g` respects the elements of `X` because `f = s ≫ c.functor.map g` does
  have hg_el : X.map (c.functor.map g) (X.map s a.val) = d.val := by
    rw [← Functor.map_comp_apply, hg_comp]
    exact f.2
  refine ⟨⟨g, hg_el⟩, ⟨hg_x, ?_⟩, ?_⟩
  · ext
    exact hg_comp
  · rintro g' ⟨hg'_x, hg'_comp⟩
    ext
    exact h_uniq g'.1 ⟨hg'_x, congrArg (·.1) hg'_comp⟩

private lemma bijective_map_id (G : AbFunctor C) (b : C) :
    Bijective fun v : G.obj b ↦ G.map (𝟙 b) v := by
  rw [G.map_id]
  exact bijective_id

/-- For an element a = (c, x) of E, the forgetful map from morphisms out of a to morphisms out of c
has universal points (`New.Variety.Comparison.HasUniversalPoints`) for the restriction of G to the
category of elements of E. -/
lemma hasUniversalPoints_reprBy_elements (a : E.Elements) :
    HasUniversalPoints (Comparison.restrict (elementsProj E) G) (Y := reprBy a.obj) (Y' := reprBy a)
      { app _ := ↾fun f ↦ ⟨f.down.1⟩ } := by
  intro b y
  -- the universal point over `y : a.fst ⟶ b` is `y` itself, read as a map from `a` to the
  -- point `E.map y a.snd` over `b`; the coefficient map is the identity of `G b`
  refine ⟨E.elementsMk b (E.map y.down a.val), ⟨⟨y.down, rfl⟩⟩, 𝟙 b, by aesop, ?_,
    bijective_map_id G b⟩
  rintro d ⟨z, hz⟩ f ⟨⟩
  -- the map `f : b ⟶ d.fst` respects the elements of `E`, as `y ≫ f` does; it gives the unique
  -- lift, as maps between elements are determined by their underlying maps
  have hf_el : E.map f (E.map y.down a.val) = d.val :=
    (E.map_comp_apply y.down f a.val).symm.trans hz
  refine ⟨⟨f, hf_el⟩, ?_⟩
  aesop

/-- The tautological section (c, x) ↦ x of the pull-back of X to its own category of elements. -/
def tautologicalSection : onePointFunctor X.Elements ⟶ elementsProj X ⋙ X :=
  sectionMap ⟨fun a ↦ a.2, fun f ↦ f.2⟩

/-- The tautological section `New.Variety.tautologicalSection` has universal points
(`New.Variety.Comparison.HasUniversalPoints`) for the restriction of any coefficient G to the
category of elements of X. -/
lemma hasUniversalPoints_elements :
    HasUniversalPoints (Comparison.restrict (elementsProj X) G) tautologicalSection := by
  intro a y
  -- the universal point over `y` is `(a, y)` itself, with the identity of `a`; the coefficient
  -- map is `G.map (𝟙 a)`, the identity of `G a`
  refine ⟨X.elementsMk a y, PUnit.unit, 𝟙 a, ?_, fun d z f hf ↦ ?_, bijective_map_id G a⟩
  · -- the tautological section at `(a, y)` is `y`
    aesop
  · refine ⟨⟨f, hf.symm⟩, ?_⟩
    -- it is unique, as maps between elements are determined by their underlying maps
    aesop

/-- The relative cohomology of a pair `U ⊆ X` is computed on the category of elements of `X`, as
that of the point relative to the preimage of `U`: restricting to the elements of `X` and pulling
back along the tautological section (`New.Variety.tautologicalSection`) gives bijections
`Ext^n (ℤ[X]/ℤ[U], G) → Ext^n (ℤ[pt]/ℤ[U'], G')` for all `n`, where `U'` is the preimage of `U`
and `G'` is `G` restricted to the elements of `X`. -/
lemma isBijective_relFreeAb_tautologicalSection (U : Subfunctor X) :
    IsBijective (Comparison.restrict (elementsProj X) G) (N := relFreeAb U)
      (relFreeAb.map (U := U.whisker (Comparison.restrict (elementsProj X) G).functor)
        tautologicalSection
        le_rfl) := by
  -- the tautological section maps the sequence `ℤ[U'] → ℤ[pt] → ℤ[pt]/ℤ[U']` of the preimage
  -- `U'` of `U` to the restriction of `ℤ[U] → ℤ[X] → ℤ[X]/ℤ[U]`. Five lemma for the long exact
  -- sequences: the comparison is bijective on `U` and on `X` (`hasUniversalPoints_elements`), hence
  -- on the quotient.
  let c₀ := Comparison.restrict (elementsProj X) G
  exact ((pull_hom_contravariant (relFreeAb.shortExact U).2 (relFreeAb.shortExact _).2 c₀
        { τ₁ := freeAbMap ((U.whisker c₀.functor).fromPreimage tautologicalSection)
          τ₂ := freeAbMap tautologicalSection
          τ₃ := relFreeAb.map (U := U.whisker c₀.functor) tautologicalSection le_rfl
          comm₁₂ := freeAb.hom_ext
          comm₂₃ := rfl }).five_lemma
      (hasUniversalPoints_elements.isBijective_subfunctor U)).mp
        hasUniversalPoints_elements.isBijective

/-! ### Total cohomology over a slice -/

/-- A comparison is bijective on total cohomology (restrict along `c.functor`, push along
`c.coeffHom`, then pull back along `α`) if and only if it is bijective in each degree. -/
lemma bijective_totalH_iff_isBijective {α : N' ⟶ c.functor ⋙ N} :
    (Bijective fun x : TotalH N F ↦
        pullbackAlong α (TotalH.mapThenComp (restrictAlong c.functor) (TotalH.homClass c.coeffHom)
          x)) ↔
      c.IsBijective α := by
  -- the map on total cohomology is the direct sum of the maps `c.pull α n`
  have h_total_eq_sum :
      (TotalH.comp (.homClass α)).comp
          (TotalH.mapThenComp (N := N) (restrictAlong _) (.homClass c.coeffHom)) =
        DirectSum.map (c.pull α) := by
    ext n x : 2
    calc
      TotalH.comp (.homClass α)
        (TotalH.comp (TotalH.map (restrictAlong c.functor) (.of _ n x)) (.homClass c.coeffHom))
      _ = TotalH.comp (.homClass α)
          (.of _ n (H.push _ c.coeffHom n (x.mapExactFunctor (restrictAlong c.functor)))) := by
        rw [TotalH.map_of, of_comp_homClass]
        rfl
      _ = .of _ n (c.pull α n x) := pullbackAlong_of ..
      _ = DirectSum.map (c.pull α) (.of _ n x) := by rw [DirectSum.map_of]
  -- a direct sum of maps is bijective if and only if each summand is
  show Bijective ((TotalH.comp (.homClass α)).comp
    (TotalH.mapThenComp (N := N) (restrictAlong c.functor) (.homClass c.coeffHom))) ↔ _
  rw [h_total_eq_sum]
  exact .trans (.and (DirectSum.map_injective _) (DirectSum.map_surjective _)) forall_and.symm

alias ⟨_, Comparison.IsBijective.bijective_totalH⟩ := bijective_totalH_iff_isBijective

/-- The additive isomorphism from total Ext(N ⊗ ℤ[X], F) to total Ext between the pull-backs of N
and F to the category of elements of X: restrict there, then precompose with
n ↦ n ⊗ [tautological point]. -/
def sliceEquiv :
    TotalH (abTensor N (freeAb X)) F ≃+ TotalH (elementsProj X ⋙ N) (elementsProj X ⋙ F) :=
  -- restrict to the points of `X`, then pull back along
  -- `tensorPoint (freeAbMap tautologicalSection)`, the map `n ↦ n ⊗ [tautological point]`
  AddEquiv.ofBijective ((TotalH.comp _).comp (TotalH.map (restrictAlong (elementsProj X)))) <| by
    -- by dévissage it suffices to treat `N = ℤ[Y]`, `Y` a sum of representable functors
    -- `h_bij`: the comparison is bijective in every degree at `N`
    have h_bij :=
      (devissage (.restrict _ F) (abTensor.flip (freeAb X))
          ((restrictAlong _).whiskerLeft
            (tensorPoint (freeAbMap
              tautologicalSection)))).allBijective_of_allBijective_sigma_reprBy (fun ι c ↦ ?_) N
    · -- bijective in each degree, so bijective on total cohomology
      -- (`using!`: after `simp` the two sides differ only by unfolding `elementsProj`)
      simpa [mapThenComp] using! IsBijective.bijective_totalH h_bij
    · -- the case `N = ℤ[Y]`: `ℤ[Y] ⊗ ℤ[X] = ℤ[Y × X]`, and over the points of `X` the functor `Y`
      -- is the pull-back of the tautological point along the projection `Y × X → X`
      refine (IsCohomEquiv.of_isIso (freeAb.prod (sigma fun i ↦ reprBy (c i)) X)).bij.trans
        (hasUniversalPoints_elements.isBijective_of_isPullback
          (v := lift (𝟙 (elementsProj X ⋙ sigma fun i ↦ reprBy (c i)))
            (toUnit (elementsProj X ⋙ sigma fun i ↦ reprBy (c i)) ≫ tautologicalSection))
          (toUnit (elementsProj X ⋙ sigma fun i ↦ reprBy (c i)))
          (snd (sigma fun i ↦ reprBy (c i)) X) ?_)
        (freeAb.hom_ext fun _ _ ↦ rfl)
      refine isPullback_iff.mpr ⟨fun B z ↦ rfl, fun B w x h_snd ↦ ?_⟩
      -- the unique point over `x` is its first coordinate
      refine ⟨x.fst, ⟨rfl, Prod.ext rfl h_snd.symm⟩, ?_⟩
      rintro z' ⟨_, h_lift⟩
      exact congrArg Prod.fst h_lift

/-- The ring `A` is local and absolutely integrally closed, and the prime `ℓ` is invertible in it.
Instance search finds `ℓ` from `A`. -/
class InvertsPrime (A : Type) [CommRing A] (ℓ : outParam ℕ) extends ThePrime ℓ,
  IsAbsIntegrallyClosedLocal A where
  /-- The prime `ℓ` is invertible in `A`. -/
  isUnit_prime : IsUnit (ℓ : A)

/-! ### Tests over a ring, coefficients, families of ideals, theories -/

/-- The category of tests over A: the full subcategory of commutative A-algebras whose
underlying rings are test rings. -/
abbrev TestOver (A : Type) [CommRing A] : Type 1 := FullSubcategory (C := CommAlg A) (IsTest ·)

/-- The functor from tests over A to test rings that forgets the A-algebra structure. -/
def TestOver.toTest (A : Type) [CommRing A] : TestOver A ⥤ TestRing :=
  ObjectProperty.lift _ (ι _ ⋙ forget₂ (CommAlg A) CommRingCat) (·.property)

section

variable {A : Type} [CommRing A] {ℓ : ℕ} (g : C ⥤ TestOver A)

/-- For a functor g from C to tests over A, the functor sending c to the commutative ring underlying
g(c), where `testIncl` is the inclusion of test rings (`TestRing`) into commutative rings. -/
abbrev ringOf : C ⥤ CommRingCat := g ⋙ TestOver.toTest A ⋙ testIncl

/-- For g from C to tests over A, the functor sending c to the abelian group of locally constant
functions Spec g(c) → ℤ/ℓ. -/
abbrev locConstAlong [InvertsPrime A ℓ] : C ⥤ AddCommGrpCat :=
  g ⋙ TestOver.toTest A ⋙ locConstCoeff ⟨ZMod ℓ⟩

/-- A coefficient along g: a functor F (the field `functor`) to abelian groups, killed by ℓ, that
satisfies Zariski descent (`New.Variety.HasZariskiDescent`) for the rings g(c). -/
structure TorsionCoeff [InvertsPrime A ℓ] where
  /-- The coefficient, a functor from `C` to abelian groups. -/
  functor : AbFunctor C
  /-- Every value of `F` is killed by `ℓ`. -/
  prime_smul_eq_zero (c : C) (x : functor.obj c) : ℓ • x = 0
  /-- `F` satisfies Zariski descent for the rings `(ringOf g).obj c`. -/
  zariski_descent : HasZariskiDescent (ringOf g) functor

end

variable {A : Type} [CommRing A] {ℓ : ℕ} [InvertsPrime A ℓ] (g : C ⥤ TestOver A)
  (ι : C ⥤ CommRingCat.{0})

/-- For a functor ι from C to commutative rings, ideals I_c (the field `ideal c`) of ι(c) such that
I_b is generated by the image of I_a for every morphism a → b. -/
structure IdealFamily where
  /-- The ideal `ideal c` (I_c) of the ring `ι.obj c`. -/
  ideal (c : C) : Ideal (ι.obj c)
  /-- For every morphism `f : a ⟶ b`, the image of `ideal a` generates `ideal b`. -/
  map_eq {a b : C} (f : a ⟶ b) : (ideal a).map (ι.map f).hom = ideal b

/-- For an ideal I of ι(c), the subfunctor of Hom(c, −) of the morphisms f: c → d such that ι(f)
sends I to zero. -/
def killingMaps {c : C} (I : Ideal (ι.obj c)) : Subfunctor (reprFunctor.obj ⟨c⟩) where
  obj _ := {f | I.map (ι.map f.1).hom = ⊥}
  map := by simp_all [reprFunctor, ← Ideal.map_map]

/-- A theory: an `ℓ`-torsion coefficient `F` (the field `functor`) with Zariski descent
(`New.Variety.TorsionCoeff`) that behaves well on closed loci. For an ideal `I` of the ring at `c`,
let `Z ⊆ Hom (c, -)` be the maps that kill `I` (`New.Variety.killingMaps`). Then
`H^n (Hom (c, -), F) → H^n (Z, F)` is onto, and a section of `F` over `c` that dies along `Z`
vanishes near every maximal ideal containing `I`. -/
structure Theory extends TorsionCoeff g where
  /-- In every degree `n`, restriction of cohomology from all maps out of `c` to the maps that kill
  the ideal `I` is onto. -/
  restrict_surjective (c : C) (I : Ideal ((ringOf g).obj c)) (n : ℕ) :
      Surjective (H.map functor (freeAb.map (killingMaps (ringOf g) I).ι) n)
  /-- A section `x` of `F` over `c` that dies along every map killing `I` (hypothesis `h_dies`)
  vanishes near each maximal ideal `m ⊇ I`: for some `a ∉ m`, it dies along every map `c ⟶ d`
  that makes `a` invertible. -/
  dies_near (c : C) (I : Ideal ((ringOf g).obj c)) (x : functor.obj c)
      (h_dies : ∀ (d : C) (f : c ⟶ d), ⟨f⟩ ∈ (killingMaps (ringOf g) I).obj d → functor.map f x = 0)
      (m : Ideal ((ringOf g).obj c)) (hm : m.IsMaximal) (hIm : I ≤ m) :
      ∃ a : (ringOf g).obj c, a ∉ m ∧
        ∀ (d : C) (f : c ⟶ d), IsUnit ((ringOf g).map f a) → functor.map f x = 0

variable {g : C ⥤ TestOver A} {ι : C ⥤ CommRingCat.{0}} (I : IdealFamily ι)

/-- The pull-back of a compatible family of ideals I along a functor φ: C' → C, with ideal
I_{φ(c')} at the object c'. -/
def IdealFamily.whisker (φ : C' ⥤ C) : IdealFamily (φ ⋙ ι) where
  ideal c := I.ideal (φ.obj c)
  map_eq f := I.map_eq (φ.map f)

/-- For a compatible family of ideals I, the subfunctor of the one-point functor that is
non-empty exactly at the objects c with I_c = 0. -/
def IdealFamily.botLocus : Subfunctor (onePointFunctor C) where
  obj c := {_x : (onePointFunctor C).obj c | I.ideal c = ⊥}
  map f := by simp_all [← I.map_eq f]

/-- For a compatible family of ideals I, the subfunctor of the one-point functor that is
non-empty exactly at the objects c where I_c is the unit ideal. -/
def IdealFamily.topLocus : Subfunctor (onePointFunctor C) where
  obj c := {_x : (onePointFunctor C).obj c | I.ideal c = ⊤}
  map f := by grind [I.map_eq f, Ideal.map_top]

/-- Let `I` be a compatible family of ideals of the rings `ι c`, for `ι` a functor on the category
`C`. Off the closed locus of `I c` the family becomes the unit ideal: if `m` does not contain
`I c`, some `a ∉ m` has `I d = ⊤` along every map `c ⟶ d` that inverts `a`. -/
lemma IdealFamily.exists_notMem_eq_top {c : C} {m : Ideal (ι.obj c)} (h_not_le : ¬I.ideal c ≤ m) :
    ∃ a ∉ m, ∀ (d : C) (f : c ⟶ d), IsUnit (ι.map (X := c) (Y := d) f a) → I.ideal d = ⊤ := by
  -- any `a ∈ I.ideal c` outside `m` will do: a map that inverts `a` puts a unit into `I.ideal d`
  obtain ⟨a, haI, ham⟩ := IsConcreteLE.not_le_iff_exists.1 h_not_le
  exact ⟨a, ham, fun d f hf ↦
    eq_top_of_isUnit_mem _ ((I.map_eq f).le (mem_map_of_mem _ haI)) hf⟩

/-- The quotient of G whose value at c is G(c) modulo the sections killed by every map c → d with
I_d = 0. -/
def IdealFamily.zerosCoeff (G : AbFunctor C) {ι : C ⥤ CommRingCat.{0}} (I : IdealFamily ι) :
    AbFunctor C where
  obj c := .of (G c ⧸ AddSubgroup.ofSub
      {x : G.obj c | ∀ (d : C) (f : c ⟶ d), I.ideal d = ⊥ → G.map (X := c) (Y := d) f x = 0}
      ⟨0, by simp⟩ (by simp_all))
  map f := AddCommGrpCat.ofHom
    (QuotientAddGroup.map _ _ (G.map f).hom fun x hx d g hd ↦ by simpa using hx d (f ≫ g) hd)

/-- The quotient morphism from G to `New.Variety.IdealFamily.zerosCoeff`, sending each section to
its class. -/
def IdealFamily.toZerosCoeff (G : AbFunctor C) {ι : C ⥤ CommRingCat.{0}}
    (I : IdealFamily ι) : G ⟶ I.zerosCoeff G where
  app _ := AddCommGrpCat.ofHom (mk' _)

/-- Let `G` be a functor from the category `C` to abelian groups and `I` a family of ideals on `C`.
At an object `d` where the ideal `I.ideal d` is zero, the quotient map from `G d` to
`I.zerosCoeff G d` is bijective: a section that dies along every map to an object where `I` is zero
dies along the identity of `d`. -/
lemma IdealFamily.bijective_toZerosCoeff (G : AbFunctor C) {ι : C ⥤ CommRingCat.{0}}
    (I : IdealFamily ι) (d : C) (h_bot : I.ideal d = ⊥) :
    Bijective (I.toZerosCoeff G d) := by
  -- a section that dies wherever `I` does dies along the identity of `d`, since `I.ideal d = ⊥`
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, mk_surjective⟩
  have h_dies : ∀ (e : C) (f : d ⟶ e), I.ideal e = ⊥ → G.map f x = 0 := (eq_zero_iff x).1 hx
  simpa using h_dies d (𝟙 d) h_bot

/-- Let `V` be a subfunctor of the one-point functor that is dense for `F`
(`New.Variety.IsCohomDense`); it picks the objects `c` with `⟨⟩ ∈ V c`. A map `α : M ⟶ N` of
functors to abelian groups that is bijective at each of these objects is an equivalence for `F`:
`Ext^n (N, F) → Ext^n (M, F)` is bijective for all `n`. -/
lemma IsCohomDense.isCohomEquiv_of_bijective_on {F M N : AbFunctor C} {α : M ⟶ N}
    {V : Subfunctor (onePointFunctor C)} (h_dense : IsCohomDense F V)
    (h_bij : ∀ c : C, ⟨⟩ ∈ V c → Bijective (α c)) :
    IsCohomEquiv F α := by
  -- kernel and cokernel of `α` vanish at the objects of `V`, so they are killed by a dense sieve
  have h_ker (c : C) (s : M.obj c) (hs : α c s = 0) : s ∈ locallyZero F M c := by
    refine h_dense.of_preimage_le (pointMap ⟨⟩) fun b f hb ↦ ?_
    -- `α b` is injective and sends `M.map f s` to `N.map f (α c s) = 0`
    refine (h_bij b hb).injective (?_ : α b (M.map f.down s) = α b 0)
    simp [α.naturality_apply, hs]
  have h_coker (c : C) (t : N.obj c) : abCoker.π α c t ∈ locallyZero F (abCoker α) c := by
    refine h_dense.of_preimage_le (pointMap ⟨⟩) fun b f hb ↦ ?_
    -- `α b` is onto, so the cokernel of `α` is zero at `b`
    exact (eq_zero_iff _).2 ((h_bij b hb).surjective _)
  exact LocalIso.isCohomEquiv ⟨h_ker, h_coker⟩

/-! ### The theory of locally constant functions -/

/-- For an ideal `I` of the ring of a test `B` over `A`, there is a test `D` over `A` with a map
`π : B ⟶ D` such that (a) the ring map of `π` is onto and its kernel is the radical of `I`,
(b) every map out of `B` that kills `I` factors uniquely through `π`, and (c) `π` kills `I`. -/
lemma TestOver.exists_quotient (B : TestOver A) (I : Ideal ((ringOf (𝟭 (TestOver A))).obj B)) :
    ∃ (D : TestOver A) (π : B ⟶ D),
      RingHom.ker ((ringOf (𝟭 (TestOver A))).map (π : B ⟶ D)).hom = radical I ∧
      Surjective π.hom.hom' ∧
      (∀ (E : TestOver A) (f : B ⟶ E),
        ⟨f⟩ ∈ killingMaps (ringOf (𝟭 (TestOver A))) I E → ∃! k : D ⟶ E, π ≫ k = f) ∧
      I.map π.hom.hom' = ⊥ := by
  -- `D` is the quotient of `B` by the radical of `I`, a test since the radical is a radical ideal
  let D : TestOver A :=
    ⟨CommAlgCat.of A (B.obj ⧸ radical I), B.property.quotient I.radical_isRadical⟩
  let π : B ⟶ D := ⟨ofHom (Quotient.mkₐ ..)⟩
  refine ⟨D, π, mk_ker, mk_surjective, fun E f hf ↦ ?_, map_mk_eq_bot_of_le le_radical⟩
  -- a map to a reduced ring that kills `I` kills its radical, so it factors through `π`
  have h_kill : I.map ((ringOf (𝟭 (TestOver A))).map f).hom = ⊥ := hf
  have h_reduced : (⊥ : Ideal ((ringOf (𝟭 (TestOver A))).obj E)).IsRadical :=
    Ideal.isRadical_bot_iff.2 E.property.isReduced
  have h_rad : radical I ≤ comap ((ringOf (𝟭 (TestOver A))).map f).hom ⊥ :=
    (radical_mono (le_comap_of_map_le h_kill.le)).trans (h_reduced.comap _)
  let k₀ : D ⟶ E := ⟨ofHom (Quotient.liftₐ _ _ h_rad)⟩
  refine ⟨k₀, rfl, fun k hk ↦ ?_⟩
  -- maps out of the quotient `D` are determined by their composites with `π`
  have h_eq : π ≫ k = π ≫ k₀ := hk
  have h_alg : (π ≫ k).hom.hom = (π ≫ k₀).hom.hom := congrArg (fun u : B ⟶ E ↦ u.hom.hom) h_eq
  exact hom_ext _ (CommAlgCat.hom_ext (Ideal.Quotient.algHom_ext _ h_alg))

/-- Let `g` be a functor from a category `C` to tests over `A`, `s` a locally constant function
from Spec of the ring `g(c)` to `ℤ/ℓ`, and `P` a prime of that ring. Then there is `a ∉ P` such that
along every map `c ⟶ d` that makes `a` invertible, `s` becomes the constant function with value
`s P`. -/
lemma exists_locConst_eq_const {c : C} (s : locConstAlong g c)
    (P : PrimeSpectrum ((ringOf g).obj c)) :
    ∃ a : (ringOf g).obj c, a ∉ P.asIdeal ∧ ∀ (d : C) (f : c ⟶ d),
      IsUnit ((ringOf g).map (Y := d) f a) →
      (locConstAlong g).map f s = ⟨LocallyConstant.const _ (s.down.toFun P)⟩ := by
  -- the open set where `s` takes the value `s P` contains a basic open set `D(a) ∋ P`
  obtain ⟨_, ⟨a, rfl⟩, haP, h_const⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.1
    (s.down.isLocallyConstant {s.down.toFun P}) P rfl
  refine ⟨a, haP, fun d f hf ↦ ULift.down_injective (LocallyConstant.ext fun Q ↦ ?_)⟩
  -- once `a` is a unit, every prime `Q` at `d` pulls back into `D(a)`, where `s` is constant
  exact h_const (Q.asIdeal.notMem_of_isUnit hf)

/-- The theory (`New.Variety.Theory`) on the category of tests over A whose coefficient sends B to
the locally constant functions Spec B → ℤ/ℓ. -/
def Theory.locallyConstant : Theory (𝟭 (TestOver A)) where
  functor := locConstAlong (𝟭 (TestOver A))
  -- the values lie in `ZMod ℓ`
  prime_smul_eq_zero _ _ := congr(⟨⟨$(by aesop (add simp ZMod.natCast_self)), _⟩⟩)
  zariski_descent := by
    -- Any two elements of a test ring are comparable after a partition
    -- (`IsTest.isComparableRing`), so Zariski descent follows from additivity along
    -- idempotents (`HasPartitions`).
    refine HasPartitions.hasZariskiDescent ⟨fun B e he _ ↦ ?_, fun _ _ ↦ by
      apply hasPartitions_locConstCoeff.bijective_prod⟩ (𝟙 _) (by simp) fun B ↦ B.2.isComparableRing
    -- The cut along `e` is the quotient by the ideal `(e)`, which is radical.
    obtain ⟨D, π, h_ker, h_surj, h_univ, h_kill⟩ := B.exists_quotient (span {e})
    refine ⟨D, π, ?_, ?_, h_surj, h_ker.le.trans (B.2.isRadical_span_idempotent he)⟩
    · simpa [killingMaps, map_span] using! h_kill
    · simpa [killingMaps, map_span] using h_univ
  restrict_surjective B I := by
    -- The maps that kill `I` are those through the quotient `π` by the radical of `I`, and locally
    -- constant functions lift along `π`.
    obtain ⟨D, π, -, h_surj, h_univ, h_kill⟩ := B.exists_quotient I
    refine surjective_restrict_of_quotient_sieve (F := locConstAlong (𝟭 _)) (𝟭 _) π @h_univ ?_
      (IsCohomEquiv.of_isIso _).bij ?_
    · rintro E _ k (rfl : π ≫ k = _)
      exact (killingMaps ..).map k h_kill
    · exact ULift.map_surjective.2 (comapAddMonoidHom_surjective_of_isComparableRing _
        (B.2.isComparableRing_of_associated (h_surj.forall.2 fun x ↦ ⟨x, .rfl⟩)))
  dies_near B I s hs (m : Ideal B.1) hm hIm := by
    -- `s` dies on the residue field at `m`, so its value at `m` is `0`; it is constant near `m`.
    let π : B ⟶ ⟨CommAlgCat.of A (B.1 ⧸ m), B.2.quotient hm.isPrime.isRadical⟩ :=
      ⟨ofHom (Quotient.mkₐ ..)⟩
    have h_zero : (locConstAlong (𝟭 (TestOver A))).map π s = 0 :=
      hs _ π (map_mk_eq_bot_of_le hIm)
    obtain ⟨a, ha, h_const⟩ := exists_locConst_eq_const s (.comap (Ideal.Quotient.mk m) ⊥)
    refine ⟨a, fun h ↦ ha (mk_ker.ge h), fun d f hf ↦ (h_const d f hf).trans ?_⟩
    exact congr(⟨.const _ (($h_zero).1.1 _)⟩)

variable (Θ : Theory g) (I : IdealFamily (ringOf g)) (M : TorsionCoeff g)

/-- The morphism from ℤ[pt], the constant functor ℤ, to the locally constant ℤ/ℓ-valued
functions on Spec g(c), sending the generator to the constant function 1. -/
def oneLocConst : freeAb (onePointFunctor C) ⟶ locConstAlong g :=
  freeAb.desc (fun _ _ ↦ ⟨LocallyConstant.const _ 1⟩) (by tauto)

/-- For a coefficient M along g and a set-valued functor X on C, the restriction of M to the
category of elements of X along the projection (c, x) ↦ c. -/
protected def TorsionCoeff.onElements : TorsionCoeff (elementsProj X ⋙ g) where
  functor := elementsProj X ⋙ M.functor
  prime_smul_eq_zero a := M.prime_smul_eq_zero a.1
  zariski_descent Y U hU a y := by
    -- Maps out of the point `a` are maps out of `a.1` (`hasUniversalPoints_reprBy_elements`), so it
    -- suffices to show that the sieve `V` of the `f` out of `a.1` that carry `y` into `U` is dense
    -- for `M.functor`.
    let V : Subfunctor (reprBy a.1) :=
      { obj d := {f | ⟨⟨f.1, rfl⟩⟩ ∈ (U.preimage (pointMap y)).obj ⟨X.map f.1 a.2⟩}
        map g f hf := (U.preimage (pointMap y)).map (Functor.Elements.homMk (x :=
          ⟨X.map f.1 a.2⟩) (y := ⟨X.map (f.1 ≫ g) a.2⟩) g (X.map_comp_apply ..).symm) hf }
    -- `V` is locally everything, because `U` is so at the image of `y` under `f`.
    have hV : IsZariskiLocallyTop (ringOf g) V :=
      fun d f m hm ↦ by
        obtain ⟨r, hr, h_mem⟩ := hU ⟨X.map f.1 a.2⟩ (Y.map ⟨f.1, rfl⟩ y) m hm
        exact ⟨r, hr, fun e k hk ↦ by
          simpa only [← Y.map_comp_apply] using!
            h_mem ⟨X.map (f.1 ≫ k) a.2⟩ ⟨k, (X.map_comp_apply ..).symm⟩ hk⟩
    refine ((hasUniversalPoints_reprBy_elements a).isCohomEquiv_incl_iff V ?_).1
      (M.zariski_descent hV).isCohomEquiv
    -- `V` pulls back to the preimage of `U`.
    ext @⟨d, x⟩ ⟨f : a.1 ⟶ d, rfl : X.map f a.2 = x⟩
    rfl

/-- The restriction of a theory Θ on C to the category of elements of a set-valued functor X on
C, along the projection to C. -/
def Theory.onElements : Theory (elementsProj X ⋙ g) :=
  ⟨TorsionCoeff.onElements Θ.toTorsionCoeff,
    fun a I n ↦
      (((hasUniversalPoints_reprBy_elements a).isBijective_subfunctor
          (killingMaps (ringOf g) I) n).2.comp
        (Θ.restrict_surjective ((Variety.elementsProj X).obj a) I n)).forall.mpr
          (⟨Equiv.ofBijective _ ((hasUniversalPoints_reprBy_elements a).isBijective n) ·,
            map_pull_eq_pull_map (by exact freeAb.hom_ext fun _ _ ↦ rfl) ..⟩),
    fun a I x h m hm hI ↦ by
      obtain ⟨b, hb, h_dies⟩ := Θ.dies_near _ I x
        (fun d f ↦ h (X.elementsMk d (X.map f a.2)) ⟨f, rfl⟩) m hm hI
      exact ⟨b, hb, fun d f ↦ h_dies d.1 f.1⟩⟩

/-- Zero sections of the kernel of `I.toZerosCoeff Θ.functor`, together with the objects where `I`
is the unit ideal (the preimage of `I.topLocus` under the map `toUnit _` to the one-point functor),
are locally everything (`New.Variety.IsZariskiLocallyTop`). So if a section `x` of `Θ.functor` over
`c` dies along every map `c ⟶ d` with `I_d = 0`, then each maximal ideal `m` of the ring of `c`
misses some `a` such that every map `c ⟶ d` inverting `a` kills `x` or makes `I_d` the unit
ideal. -/
lemma Theory.isZariskiLocallyTop_ker_toZerosCoeff :
    IsZariskiLocallyTop (ringOf g)
      (zeroSection (kerComplex (I.toZerosCoeff Θ.functor)).X₁ ⊔ I.topLocus.preimage
        (toUnit _)) := by
  rintro c ⟨s, hs⟩ m hm
  -- `s` is a section of `Θ.functor` over `c` whose class in `I.zerosCoeff Θ.functor` is zero
  have h_dies : ∀ (d : C) (f : c ⟶ d), I.ideal d = ⊥ → Θ.functor.map f s = 0 := (eq_zero_iff s).1 hs
  by_cases hI : I.ideal c ≤ m
  · -- the maps that kill `I.ideal c` land where `I` is zero, so `s` vanishes near `m`
    obtain ⟨a, ha, h_near⟩ :=
      Θ.dies_near c (I.ideal c) s (fun d f hf ↦ h_dies d f ((I.map_eq f).symm.trans hf)) m hm hI
    exact ⟨a, ha, fun d f hf ↦ .inl (Subtype.ext (h_near d f hf))⟩
  · -- `I` becomes the unit ideal near `m`
    obtain ⟨a, ha, h_top⟩ := I.exists_notMem_eq_top hI
    exact ⟨a, ha, fun d f hf ↦ .inr (h_top d f hf)⟩

/-- Let `Θ` be a theory and `I` a family of ideals on the category `C`. The locus `I.botLocus` of
the objects where `I` is zero is dense for the coefficient `I.zerosCoeff Θ.functor`
(`New.Variety.IsCohomDense`): for every object `c`, restriction from all maps out of `c` to the maps
into that locus is bijective on `Ext^n` for all `n`. -/
lemma Theory.isCohomDense_botLocus : IsCohomDense (I.zerosCoeff Θ.functor) I.botLocus := by
  -- injectivity in degree `0` (higher degrees of the source vanish), and surjectivity
  refine fun c y n ↦ ⟨?_, ?_⟩
  · cases n with
    | zero =>
      -- a class of degree `0` is `mk₀ u` for a map `u : ℤ[h_c] ⟶ I.zerosCoeff Θ.functor`; by
      -- Yoneda, `u` is a section of `I.zerosCoeff Θ.functor` over `c`, the class of a section `x`
      -- of `Θ.functor`
      refine (injective_iff_map_eq_zero _).2 fun a hx ↦ ?_
      obtain ⟨u, rfl⟩ : ∃ u : freeAb (reprBy c) ⟶ I.zerosCoeff Θ.functor, mk₀ u = a :=
        (mk₀_bijective _ _).surjective a
      obtain ⟨z, rfl⟩ : ∃ z : (I.zerosCoeff Θ.functor).obj c,
          (homReprEquiv c (I.zerosCoeff Θ.functor)).symm z = u :=
        (homReprEquiv c (I.zerosCoeff Θ.functor)).symm.surjective u
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
      simp only [H.map, bilinearComp_apply_apply, mk₀_comp_mk₀, mk₀_eq_zero_iff,
        EmbeddingLike.map_eq_zero_iff] at hx ⊢
      -- `x` dies in `I.zerosCoeff Θ.functor` where `I` is zero, and there `I.zerosCoeff Θ.functor`
      -- is `Θ.functor`
      refine (eq_zero_iff x).2 fun d f hd ↦ (I.bijective_toZerosCoeff _ d hd).injective ?_
      -- evaluate `hx` at the generator given by `f`, a map into the locus where `I` is zero
      have h_at : (I.toZerosCoeff Θ.functor).app d (Θ.functor.map f x) =
        (I.toZerosCoeff Θ.functor).app d 0 :=
        (add_zero _).symm.trans (congrArg (fun w ↦ w.app d (.of ⟨⟨f⟩, hd⟩)) hx)
      exact h_at
    | succ n => exact injective_of_subsingleton _
  · -- on the sieve of the maps that kill `I.ideal c`, classes in `I.zerosCoeff Θ.functor` come from
    -- `Θ.functor`, and those extend to `c` by `Θ.restrict_surjective`
    let R : Subfunctor (reprBy c) := I.botLocus.preimage (pointMap y)
    have h_sieve : killingMaps (ringOf g) (I.ideal c) = R :=
      Subfunctor.ext (funext fun _ ↦ Set.ext fun _ ↦ (I.map_eq _).congr_left)
    have h_sur : Surjective (H.map Θ.functor (freeAb.map R.ι) n) := by
      rw [← h_sieve]
      exact Θ.restrict_surjective c (I.ideal c) n
    have h_push : Bijective (H.push (freeAb R.toFunctor) (I.toZerosCoeff Θ.functor) n) :=
      push_bijective_of_points _ (fun d f ↦ I.bijective_toZerosCoeff _ d (Subtype.prop f)) n
    exact (h_push.surjective.comp h_sur).forall.2 fun x ↦ ⟨_, map_push _ _ x⟩

/-- The coefficient obtained from the theory Θ by dividing by the sections at c that are killed
by every map c → d with I_d = 0 (`New.Variety.IdealFamily.zerosCoeff`). -/
def Theory.onZeros : TorsionCoeff g where
  functor := I.zerosCoeff Θ.functor
  prime_smul_eq_zero c := Quot.ind fun x ↦ congrArg _ (Θ.prime_smul_eq_zero c x)
  zariski_descent Y U hU := by
    -- The locus `I.botLocus` is dense, so it suffices to work over a point `z` of it.
    refine ((Θ.isCohomDense_botLocus I).preimage (toUnit _)).trans fun d z n ↦ ?_
    -- There `I.toZerosCoeff Θ.functor` is bijective, so descent follows from descent for
    -- `Θ.functor`.
    have h_bij (e : C) (f : (reprBy d).obj e) : Bijective ((I.toZerosCoeff Θ.functor).app e) :=
      I.bijective_toZerosCoeff _ _ ((pointMap z).app e f).2
    exact (bijective_iff_of_comm_sq (map_push _ _) (push_bijective_of_points _ h_bij n)
        (push_bijective_of_points _ (fun e f ↦ h_bij e (Subtype.val f)) n)).1
      (Θ.zariski_descent hU ..)

/-- For a coefficient `M` along `g` (its values are killed by `ℓ`) and a functor `N` from `C` to
abelian groups, `ℓ` kills the total cohomology `TotalH N M.functor`, the sum over `n` of
`Ext^n (N, M.functor)`. -/
lemma TorsionCoeff.nsmul_totalH_eq_zero (y : TotalH N M.functor) : ℓ • y = 0 := by
  -- `End M.functor` acts on total cohomology, and `ℓ` times the identity of `M.functor` is zero
  let act : CoeffAction (End M.functor) M.functor := ⟨RingHom.id (End M.functor)⟩
  have h_zero : ℓ • (1 : End M.functor) = 0 := End.ext (by bound [M.prime_smul_eq_zero])
  rw [← smul_one_smul (End M.functor) ℓ y, h_zero, zero_smul]

variable [NeZero ℓ] [HasFlatValues N]

/-- For `ℓ ≠ 0` and a functor `N` from `C` to abelian groups with flat values, the sequence
`0 → N → N → N / ℓN → 0` is short exact; its maps are multiplication by `ℓ` and the quotient map
`abCoker.π`. -/
lemma shortExact_nsmul_abCoker :
    ∃ w : (ℓ • 𝟙 N) ≫ abCoker.π (ℓ • 𝟙 N) = 0,
      ShortComplex.ShortExact ⟨ℓ • 𝟙 N, abCoker.π (ℓ • 𝟙 N), w⟩ := by
  refine shortExact_of_app (fun c ↦ ?_) (fun _ ↦ eq_zero_iff) fun _ ↦ mk_surjective
  -- a flat `ℤ`-module is torsion-free, so multiplication by `ℓ ≠ 0` is injective
  have h_flat : Module.Flat ℤ (N.obj c) := HasFlatValues.flat c
  exact (HasUniqueDiv.of_isTorsionFree ℤ _).nsmul_right_injective NeZero.out

/-- For a coefficient `M` along `g` and a functor `N` with flat values, pull-back along the quotient
map `N → N / ℓN` is onto, from the total cohomology of `N / ℓN` to that of `N`, both with
coefficients `M.functor`. -/
lemma TorsionCoeff.pullbackAlong_abCoker_pi_surjective :
    Surjective (pullbackAlong (G := M.functor) (abCoker.π (ℓ • 𝟙 N))) := by
  -- by the long exact sequence of `shortExact_nsmul_abCoker` it suffices that pull-back along
  -- `ℓ • 𝟙 N` is zero
  obtain ⟨w, h_exact⟩ := shortExact_nsmul_abCoker (ℓ := ℓ) (N := N)
  obtain ⟨h_mid, -, -⟩ := exact_triangle h_exact M.functor
  refine fun y ↦ (h_mid y).mp ?_
  -- pull-back along `ℓ • 𝟙 N` is `ℓ` times a class, and `ℓ` kills total cohomology
  simp_rw [pullbackAlong, TotalH.homClass, ← addEquiv₀_symm_apply, map_nsmul]
  exact M.nsmul_totalH_eq_zero _

/-- The map from (ℤ[pt]/ℤ[O])/ℓ, O the locus where I is the unit ideal, to locally constant
ℤ/ℓ-valued functions modulo those dying where I = 0, sending the point to 1. -/
def IdealFamily.constToZeros :
    abCoker (ℓ • 𝟙 (relFreeAb I.topLocus)) ⟶ I.zerosCoeff (locConstAlong g) :=
  abCoker.desc
    (abCoker.desc (oneLocConst ≫ I.toZerosCoeff (locConstAlong g)) (by
      -- where `I` is everything, a map that kills `I` goes to the zero ring, which has no prime
      refine freeAb.hom_ext fun _ u ↦ (eq_zero_iff _).2 fun _ f h_bot ↦ ?_
      have h_triv : (⊥ : Ideal _) = ⊤ := h_bot.symm.trans (I.topLocus.map f u.2)
      exact congr(⟨⟨$(funext fun P ↦ P.2.1.elim (eq_top_mono bot_le h_triv)), _⟩⟩)))
    -- locally constant functions with values in `ZMod ℓ` are killed by `ℓ`
    (relFreeAb.hom_ext fun _ _ ↦ congr(⟦$(by
      rw [map_nsmul, Theory.locallyConstant.prime_smul_eq_zero])⟧))

omit [NeZero ℓ] in
/-- The map `New.Variety.IdealFamily.constToZeros` sends the class of `n` times the generator to the
class of the constant function `n`. -/
lemma IdealFamily.constToZeros_zsmul_mk (c : C) (n : ℤ) :
    I.constToZeros c ⟦n • relFreeAb.mk I.topLocus ⟨⟩⟧ = ⟦⟨.const _ n⟩⟧ := by
  refine congrArg (⟦·⟧) ?_
  -- `oneLocConst` sends the generator to the constant function `1`
  show ((oneLocConst (g := g)).app c).hom' (n • FreeAbelianGroup.of PUnit.unit) = _
  have h_one : ((oneLocConst (g := g)).app c).hom' (.of PUnit.unit) =
      ⟨LocallyConstant.const _ (1 : ZMod ℓ)⟩ := freeAb.desc_of ..
  rw [map_zsmul, h_one, ← zsmul_one]
  rfl

omit [NeZero ℓ] in
/-- Let `g` be a functor from a category `C` to tests over `A`, with a theory `Θ` whose coefficient
is the locally constant `ℤ/ℓ`-valued functions, and `I` a family of ideals of the rings `g(c)`.
Then for every functor `φ : C' ⥤ C` and every coefficient `F'` on `C'` with Zariski descent for the
rings of `φ ⋙ g`, the map `New.Variety.IdealFamily.constToZeros`, restricted along `φ`, is an
equivalence for `F'` (`New.Variety.IsCohomEquiv`). -/
lemma IdealFamily.isCohomEquiv_constToZeros (hΘ : Θ.functor = locConstAlong g)
    (hF : HasZariskiDescent (ringOf (φ ⋙ g)) F') :
    IsCohomEquiv F' (φ.whiskerLeft I.constToZeros) := by
  -- The map is locally injective and locally surjective, for sieves dense for `F'`
  -- (`LocalIso.isCohomEquiv`). It sends `n` times the generator to the constant function `n`.
  refine LocalIso.isCohomEquiv ⟨fun c ↦ Quot.ind fun s hn ↦ ?_, fun c t ↦ ?_⟩
  · -- Kernel: the section is the class of a multiple `n` of the generator.
    have h_mult : s ∈ AddSubgroup.zmultiples (relFreeAb.mk (I.topLocus.whisker φ) ⟨⟩) :=
      relFreeAb.mem_of_mk_mem (.zmultiples (relFreeAb.mk (I.topLocus.whisker φ) ⟨⟩)) (by simp) s
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 h_mult
    -- The constant `n` dies where `I` does, so locally it is zero or `I` is everything.
    have h_loc : IsZariskiLocallyTop (ringOf g)
        (zeroSection (kerComplex (I.toZerosCoeff (locConstAlong g))).X₁ ⊔
          I.topLocus.preimage (toUnit _)) := by
      rw [← hΘ]
      exact Θ.isZariskiLocallyTop_ker_toZerosCoeff I
    have h_ker_n : (I.toZerosCoeff (locConstAlong g)).app (φ.obj c)
        ⟨LocallyConstant.const _ (n : ZMod ℓ)⟩ = 0 :=
      (I.constToZeros_zsmul_mk _ n).symm.trans hn
    refine (hF (h_loc.whisker φ)).of_preimage_le (pointMap ⟨⟨.const _ n⟩, h_ker_n⟩)
      fun B f hf ↦ ?_
    by_cases hB : ⟨⟩ ∈ (I.topLocus.whisker φ).obj B
    · -- where `I` is everything the relative group is zero
      have h_rel_zero (x : (relFreeAb (I.topLocus.whisker φ)).obj B) : x = 0 :=
        AddSubgroup.mem_bot.1 (relFreeAb.mem_of_mk_mem ⊥ (fun _ ↦ relFreeAb.mk_eq_zero hB) x)
      exact congrArg (Quot.mk _) (h_rel_zero _)
    · -- otherwise the ring has a maximal ideal; the value `n` of the constant there is `0`
      obtain ⟨m, hm, -⟩ := exists_le_maximal (I.ideal (φ.obj B)) hB
      have h_cast : (n : ZMod ℓ) = 0 :=
        congrArg (fun t ↦ t.val.down.toFun ⟨m, hm.isPrime⟩) (hf.resolve_right hB)
      obtain ⟨r, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).1 h_cast
      refine (eq_zero_iff _).2 ⟨r • relFreeAb.mk (I.topLocus.whisker φ) ⟨⟩, ?_⟩
      -- both sides are `ℓ * r` times the generator at `B`, which `φ.map f` fixes
      have h_map : (relFreeAb I.topLocus).map (φ.map f.down)
          (relFreeAb.mk (I.topLocus.whisker φ) ⟨⟩) = relFreeAb.mk (I.topLocus.whisker φ) ⟨⟩ := rfl
      simp [mul_smul, h_map]
  · -- Cokernel: a locally constant function is constant near each maximal ideal, and constants
    -- are in the image.
    have h_loc : IsZariskiLocallyTop (ringOf g) (zeroSection (abCoker I.constToZeros)) := by
      rintro c ⟨⟨s : locConstAlong g c⟩⟩ m hm
      obtain ⟨a, ha, h_const⟩ := exists_locConst_eq_const s ⟨m, hm.isPrime⟩
      obtain ⟨n, hn⟩ := ZMod.intCast_surjective (s.down.toFun ⟨m, hm.isPrime⟩)
      refine ⟨a, ha, fun B f hf ↦ (eq_zero_iff _).2 ⟨_, (I.constToZeros_zsmul_mk B n).trans ?_⟩⟩
      rw [hn]
      exact congrArg _ (h_const B f hf).symm
    exact (hF (h_loc.whisker φ)).preimage _

/-- For a coefficient `M` along `g` (`M.functor` is `ℓ`-torsion with Zariski descent, `ℓ ≠ 0`), let
L(c) be the group of locally constant functions Spec g(c) → ℤ/ℓ, and let `oneLocConst : ℤ → L` send
the generator to the constant function 1. Then pull-back along `oneLocConst`, from total Ext(L,
M.functor) to total Ext(ℤ, M.functor), is surjective. -/
lemma TorsionCoeff.pullbackAlong_oneLocConst_surjective :
    Surjective (pullbackAlong (G := M.functor) (oneLocConst (g := g))) := by
  -- Take the zero family of ideals `I`, and write `R` for `relFreeAb I.topLocus` and `L` for
  -- `locConstAlong _`. Then `oneLocConst` followed by the quotient `L → I.zerosCoeff L` is the
  -- composite `ℤ → R → R / ℓ → I.zerosCoeff L`, and pull-back along each of these three maps is
  -- onto.
  let I : IdealFamily (ringOf (𝟭 (TestOver A))) := IdealFamily.mk ⊥ (by simp)
  -- Where the zero ideal is everything there is no maximal ideal: the empty subfunctor is dense.
  have h_dense : IsCohomDense M.functor (⊥ : Subfunctor (I.whisker g).topLocus.toFunctor) := by
    refine M.zariski_descent fun c y m hm ↦ ?_
    -- `y` says that the zero ideal of the ring at `c` is the unit ideal
    exact (hm.ne_top (eq_top_mono bot_le y.property)).elim
  -- so the cohomology of the locus where `I` is the unit ideal is that of the empty functor, zero
  have h_acyclic (n : ℕ) (x : H (freeAb.obj (I.whisker g).topLocus.toFunctor) M.functor n) :
    x = 0 :=
    (h_dense.isCohomEquiv n).injective
      ((H.subsingleton_of_id_eq_zero (freeAb.hom_ext nofun) M.functor n).allEq _ _)
  obtain ⟨w, h_short⟩ := relFreeAb.shortExact (I.whisker g).topLocus
  -- the ascription elaborates the term first and only then matches it with the stated type
  have h_rel : IsCohomEquiv M.functor (relFreeAb.π (I.whisker g).topLocus) :=
    (isCohomEquiv_quotient_of_acyclic h_short h_acyclic :)
  have h_j : IsCohomEquiv M.functor (g.whiskerLeft I.constToZeros) :=
    I.isCohomEquiv_constToZeros g .locallyConstant rfl M.zariski_descent
  refine ((h_rel.bijective_pullbackAlong.surjective.comp M.pullbackAlong_abCoker_pi_surjective).comp
      h_j.bijective_pullbackAlong.surjective).forall.2
    fun y ↦ ⟨pullbackAlong (g.whiskerLeft (I.toZerosCoeff _)) y, ?_⟩
  -- each side is one pull-back, and the two composite maps are the same by definition of
  -- `IdealFamily.constToZeros`
  exact (pullbackAlong_pullbackAlong ..).trans
    (.symm ((pullbackAlong_pullbackAlong ..).trans (pullbackAlong_pullbackAlong ..)))

end Theories

end New.Variety

end
