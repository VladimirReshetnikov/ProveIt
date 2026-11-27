import Lib.General.Algebra.AbsIntegrallyClosed

/-!
# Cohomology of functors as Ext: test rings, points, functoriality, coefficients

Fix a category `C` of test objects and a coefficient functor `F : C ⥤ Ab`. A space is a functor
`Y : C ⥤ Type 1`, and its cohomology is `New.Variety.H N F n = Extⁿ(N, F)` with `N = ℤ[Y]`, computed
in the category `New.Variety.AbFunctor C` of functors `C ⥤ Ab`. Here `H.map` is pull-back in `N` and
`H.push` is push-forward in `F`. In the main case `C` is the category of test rings, a scheme is
replaced by its functor of points, and `F` sends `A` to the locally constant functions `Spec A → Λ`
for an abelian group `Λ`. The file proves stability properties of test rings, formal functoriality
of `H` and the additive Yoneda lemma, and it fixes vocabulary for fixed point formulas and
congruence relations with Frobenius.

## Main definitions and results

* `New.Variety.H N F n = Extⁿ(N, F)` and `New.Variety.freeAb` (the functor `Y ↦ ℤ[Y]`), with
  pull-back `New.Variety.H.map` in `N` and push-forward `New.Variety.H.push` in `F`.
* `New.Variety.IsCohomEquiv F α`: `α` is bijective on all `Extⁿ(-, F)`.
  `New.Variety.IsCohomDense F U`: the subfunctor `U` gives such an equivalence over every point
  `New.Variety.pointMap y`.
* `New.Variety.IsTest`, `New.Variety.TestRing`: test rings and their category. A test ring is
  reduced and absolutely integrally closed, and divisibility in it is total after a partition by an
  idempotent.
* `New.Variety.locConstCoeff`, `New.Variety.TestCohomology.map`: the coefficients A ↦ {locally
  constant Spec A → Λ} on test rings, and pull-back on cohomology.
* `New.Variety.IsTest.pi`, `New.Variety.IsTest.localization`, `New.Variety.IsTest.quotient`:
  products, localisations and quotients by radical ideals of test rings are test rings.
* `New.Variety.H.dimension_shift_induction`: induction on classes by dimension shifting. Identities
  between maps of `Ext` groups are checked in degree zero and on connecting maps.

Notions from other files:
* `New.Variety.IsAbsIntegrallyClosed`: A is absolutely integrally closed: every monic polynomial
  over A of positive degree has a root in A.

## Relation to the literature

Known; see `Lib.Cohomology.Etale.FilteredLimits` and `Lib.Cohomology.WoodsHole` for sources.
-/

noncomputable section

/-!
## Cohomology as Ext, comparisons and Zariski descent

* `New.Variety.Comparison`: a comparison of two theories, with the induced map
  `New.Variety.Comparison.pull`.
* `New.Variety.HasPartitions` and `New.Variety.HasZariskiDescent`: for tests with rings `ι A`,
  cutting along idempotents, and Zariski descent (a subfunctor that holds near every maximal ideal,
  `New.Variety.IsZariskiLocallyTop`, is dense).
-/

section Defs

open CategoryTheory Functor AddCommGrpCat AddMonoidHom Function Abelian Ext FreeAbelianGroup

namespace New.Variety

variable (C : Type 1)
  {C' : Type 1} [Category.{0, 1} C] [Category.{0, 1} C']
  {D T : Type*} [Category* D] [Category* T]

/-- A functor is applied to an object. -/
scoped instance : CoeFun (D ⥤ T) fun _ ↦ D → T := ⟨obj⟩

/-- A map of functors is applied to an object. -/
scoped instance {F G : D ⥤ T} : CoeFun (F ⟶ G) fun _ ↦ ∀ A : D, F A ⟶ G A := ⟨(·.app)⟩

/-- A subfunctor is applied to an object. -/
scoped instance {F : D ⥤ Type _} : CoeFun (Subfunctor F) fun _ ↦ ∀ A : D, Set (F A) := ⟨(·.obj)⟩

/-- The category of covariant functors from C to abelian groups. -/
abbrev AbFunctor : Type 2 := C ⥤ AddCommGrpCat.{1}

-- `HasAbFunctorExt` is a reducible `def` and not an `abbrev`: the kernel then compares these
-- instances by `C` alone instead of unfolding them.
/-- The assertion that Ext groups in the category of functors from C to abelian groups exist,
with values in a larger universe. -/
@[reducible]
def HasAbFunctorExt : Prop := HasExt.{2} (AbFunctor C)

variable {C} {Y E : D ⥤ Type 1} (p : E ⟶ Y) {J : Type 1} (X : J → C ⥤ Type 1)

/-! ### Fibre powers and disjoint unions -/

/-- For p: E → Y, the (m+1)-fold fibre power of E over Y: tuples of m+1 points of E(A) with the
same image in Y(A). -/
def cech (m : ℕ) : D ⥤ Type 1 where
  obj A := {e : Fin (m + 1) → E A // ∀ i j : Fin (m + 1), p.app A (e i) = p.app A (e j)}
  map f := ↾fun e ↦ ⟨fun i ↦ E.map f (e.1 i), fun i j ↦ by simp [e.2 i j]⟩

/-- The projection from the (m+1)-fold fibre power of p: E → Y to E taking the j-th coordinate. -/
def cech.proj (m : ℕ) (j : Fin (m + 1)) : cech p m ⟶ E where
  app _ := ↾fun e ↦ e.1 j

/-- For a family X_i of set-valued functors on C, the functor sending A to the disjoint union of
the X_i(A). -/
def sigma : C ⥤ Type 1 :=
  CategoryTheory.Functor.mk (fun A ↦ Σ i : J, X i A) fun f ↦ ↾fun x ↦ ⟨x.1, (X x.1).map f x.2⟩

/-- The inclusion of X_i into the disjoint union of the family of functors X. -/
def sigma.ι (i : J) : X i ⟶ sigma X where
  app _ := ↾fun x ↦ ⟨i, x⟩

variable {Y E W : C ⥤ Type 1} (ι : C ⥤ CommRingCat.{0}) (R : Type*) [Ring R]
  (N F G : AbFunctor C) (n : ℕ) (U : Subfunctor Y) (φ : C' ⥤ C) (u : W ⟶ Y) (p : E ⟶ Y)

instance : HasAbFunctorExt C := .standard _

/-! ### Cohomology, equivalences and comparisons -/

/-- The group Ext^n(N,F) in the category of functors from C to abelian groups; for N = Z[Y] it
is the cohomology H^n(Y,F). -/
abbrev H : Type 2 := Abelian.Ext N F n

/-- The functor sending a set-valued functor Y to Z[Y], whose value at A is the free abelian group
on Y(A). -/
def freeAb : (D ⥤ Type 1) ⥤ D ⥤ Ab.{1} := (whiskeringRight D (Type 1) Ab) free

/-- A functor from C to small abelian groups, regarded as taking values in abelian groups of the
next universe. -/
def liftCoeff (F : C ⥤ Ab.{0}) : AbFunctor C := F ⋙ AddCommGrpCat.uliftFunctor

/-- The contravariant functor sending an object A of C to the set-valued functor h_A = Hom(A,−),
lifted to the next universe. -/
def reprFunctor : Cᵒᵖ ⥤ C ⥤ Type 1 := uliftCoyoneda.{1} (C := C)

/-- The functor h_A = Hom(A,−) represented by the object A. -/
abbrev reprBy (A : C) : C ⥤ Type 1 := reprFunctor ⟨A⟩

/-- For a morphism f: A → B of C, the map of representable functors h_B → h_A given by
precomposition with f. -/
abbrev reprMap {A B : C} (f : A ⟶ B) :
    reprFunctor.obj (Opposite.op B) ⟶ reprFunctor.obj (Opposite.op A) := reprFunctor.map f.op

/-- For φ: C' → C, the functor N ↦ N∘φ from functors on C to functors on C', with values in D. -/
abbrev restrictAlong : (C ⥤ D) ⥤ C' ⥤ D := (whiskeringLeft C' C D) φ

/-- For α: N' → N, the homomorphism Ext^n(N,F) → Ext^n(N',F) given by precomposition with α. -/
def H.map {N N' : AbFunctor C} (F : AbFunctor C) (α : N' ⟶ N) (n : ℕ) : H N F n →+ H N' F n :=
  (mk₀ α).precomp F n.zero_add

/-- For β: F → F', the homomorphism Ext^n(N,F) → Ext^n(N,F') given by postcomposition with β. -/
def H.push {F F' : AbFunctor C} (β : F ⟶ F') (n : ℕ) : H N F n →+ H N F' n := (mk₀ β).postcomp N rfl

/-- The additive map sending a morphism β: F → G to the induced homomorphism
Ext^n(N,F) → Ext^n(N,G). -/
def H.pushHom : (F ⟶ G) →+ H N F n →+ H N G n :=
  AddMonoidHom.mk' (fun β : F ⟶ G ↦ push N β n) (by simp [push, mk₀_add])

/-- An action of the ring R on the functor F, that is, a ring homomorphism from R to the
endomorphism ring of F. -/
class CoeffAction where
  /-- The ring homomorphism from `R` to the endomorphisms of `F`. -/
  act : R →+* End F

instance [CoeffAction R F] (n : ℕ) : Module R (H N F n) :=
  (ModuleCat.mkOfSMul
    (.comp (.mk' ((extFunctorObj N n).mapEnd F) fun _ _ ↦ End.ext (extFunctorObj N n).map_add)
      CoeffAction.act)).isModule

/-- α: N' → N is an equivalence for F: the pull-back Ext^n(N,F) → Ext^n(N',F) is bijective for
every n. -/
def IsCohomEquiv {N N' : AbFunctor C} (α : N' ⟶ N) : Prop := ∀ n : ℕ, Bijective (H.map F α n)

/-- A comparison from F on C to F' on C': a functor φ: C' → C (the field `functor`) with a natural
transformation (the field `coeffHom`) β: F∘φ → F'. -/
structure Comparison (F' : AbFunctor C') where of ::
  /-- The functor `C' ⥤ C` between the categories of tests. -/
  functor : C' ⥤ C
  /-- The map from the restriction of `F` along `functor` to `F'`. -/
  coeffHom : functor ⋙ F ⟶ F'

/-- The comparison from F to itself given by the identity functor of C and the identity of F. -/
abbrev Comparison.id : Comparison F F := of (𝟭 C) (𝟙 F)

/-- For a comparison (φ,β) and α: N' → N∘φ, the homomorphism Ext^n(N,F) → Ext^n(N',F') obtained
by restricting along φ, pushing by β and pulling by α. -/
def Comparison.pull {F : AbFunctor C} {F' : AbFunctor C'} (c : Comparison F F') {N : AbFunctor C}
    {N' : AbFunctor C'} (α : N' ⟶ c.functor ⋙ N) (n : ℕ) : H N F n →+ H N' F' n :=
  (H.map F' α n).comp
    ((H.push (c.functor ⋙ N) c.coeffHom n).comp ((restrictAlong c.functor).mapExtAddHom N F n))

/-! ### Fibre products, points and dense subfunctors -/

/-- The functor sending a natural transformation p between functors D → T to the functor A ↦ p_A
from D to the category of arrows of T. -/
def toArrowFunctor {T : Type*} [Category* T] :
    CategoryTheory.Arrow (D ⥤ T) ⥤ D ⥤ CategoryTheory.Arrow T :=
  (evaluation D T ⋙ mapArrowFunctor (D ⥤ T) T).flip

/-- The functor sending a map p: E → Y of set-valued functors on C to the (m+1)-fold fibre power
of E over Y. -/
def cechFunctor (m : ℕ) : Arrow (C ⥤ Type 1) ⥤ C ⥤ Type 1 :=
  toArrowFunctor ⋙ (whiskeringRight C (Arrow (Type 1)) (Type 1)) (cech Arrow.leftToRight m)

/-- For u: W → Y and p: E → Y, the fibre product of W and E over Y. -/
def fibreProd : C ⥤ Type 1 :=
  CategoryTheory.Functor.mk (fun A ↦ {x : W A × E A // u A x.1 = p A x.2}) fun f ↦
    ↾fun x ↦ ⟨(W.map f x.1.1, E.map f x.1.2), by aesop⟩

/-- The first projection from the fibre product of W and E over Y to W. -/
def fibreProd.fst : fibreProd u p ⟶ W where
  app _ := ↾fun x ↦ x.1.1

/-- The second projection from the fibre product of W and E over Y to E. -/
def fibreProd.snd : fibreProd u p ⟶ E where
  app _ := ↾fun x ↦ x.1.2

/-- The map h_A → Y corresponding to a point y of Y(A) by the Yoneda lemma. -/
def pointMap {A : C} (y : Y A) : reprBy A ⟶ Y := uliftCoyonedaEquiv.symm y

/-- For maps f_i: X_i → Y of set-valued functors, the map from the disjoint union of the X_i to
Y that is f_i on X_i. -/
def sigma.desc {ι : Type 1} {X : ι → C ⥤ Type 1} (f : ∀ i : ι, X i ⟶ Y) : sigma X ⟶ Y where
  app A := ↾fun x ↦ (f x.1).app A x.2
  naturality := by aesop (add simp sigma)

/-- For a subfunctor U of Y and φ: C' → C, the subfunctor U∘φ of Y∘φ. -/
def _root_.CategoryTheory.Subfunctor.whisker : Subfunctor (φ ⋙ Y) where
  obj A := U (φ A)
  map f := U.map (φ.map f)

/-- The subfunctor U of Y is dense for F: for every point h_A → Y, the inclusion of the preimage
of U in h_A is an equivalence for F. -/
def IsCohomDense : Prop :=
  ∀ (A : C) (y : Y A), IsCohomEquiv F (freeAb.map (U.preimage (pointMap y)).ι)

/-! ### Tests with rings: idempotents and Zariski descent -/

/-- The map `π : A ⟶ B` cuts `A` along the element `e` of the ring `ι A`: (a) `ι π` kills `e`;
(b) every `f : A ⟶ B'` such that `ι f` kills `e` factors uniquely through `π`; (c) `ι π` is
surjective; (d) its kernel lies in the ideal `(e)`. By (a), (c), (d), `ι B = ι A ⧸ (e)`. -/
def IsQuotientByElem {A B : C} (e : ι.obj A) π :=
  ι.map (X := A) (Y := B) π e = 0 ∧
  (∀ (B' : C) (f : A ⟶ B'), ι.map f e = 0 → ∃! g : B ⟶ B', π ≫ g = f) ∧
  Surjective (ι.map π) ∧
  RingHom.ker (ι.map π).hom ≤ Ideal.span {e}

/-- The tests `C`, with rings `ι A`, can be cut along idempotents, compatibly with the coefficients
`F`: each idempotent e ≠ 1 of ι(A) has a `New.Variety.IsQuotientByElem` A → B, and
ι(A) ≅ ι(B₁) × ι(B₂) via maps A → B₁, B₂ implies F(A) ≅ F(B₁) × F(B₂). -/
structure HasPartitions where
  /-- Every idempotent `e ≠ 1` of the ring of `A` is killed by a universal map `π : A ⟶ B`, and the
  ring of `B` is the quotient by `e`. -/
  exists_quotient (A : C) (e : ι.obj A) :
      IsIdempotentElem e → e ≠ 1 → ∃ B π, IsQuotientByElem ι (B := B) e π
  /-- If two maps from `A` make the ring of `A` the product of the rings of `B₁` and `B₂`, they make
  the group `F.obj A` the product of `F.obj B₁` and `F.obj B₂`. -/
  bijective_prod {A B₁ B₂ : C} (π₁ : A ⟶ B₁) (π₂ : A ⟶ B₂) :
      Bijective (fun x : ι.obj A ↦ (ι.map (Y := B₁) π₁ x, ι.map (Y := B₂) π₂ x)) →
      Bijective fun x : F.obj A ↦ (F.map π₁ x, F.map π₂ x)

/-- The subfunctor `U` of `Y` is locally everything for the rings `ι A`: for every `y ∈ Y(A)` and
maximal ideal `m` of the ring `ι A` there is `a ∉ m` such that `y` maps into `U` along every
`A ⟶ B` that makes `a` invertible. -/
abbrev IsZariskiLocallyTop : Prop :=
  ∀ (A : C) (y : Y.obj A) (m : Ideal (ι.obj A)), Ideal.IsMaximal m →
    ∃ a ∉ m, ∀ (B : C) (f : A ⟶ B), IsUnit (ι.map f a) → Y.map f y ∈ U B

/-- Zariski descent for `F`: a subfunctor `U` of `Y` that is locally everything
(`New.Variety.IsZariskiLocallyTop`) is dense for `F` (`New.Variety.IsCohomDense`). -/
def HasZariskiDescent : Prop :=
  ∀ ⦃Y : C ⥤ Type 1⦄ ⦃U : Subfunctor Y⦄, IsZariskiLocallyTop ι U → IsCohomDense F U

/-- If the subfunctor `U` of `Y` is locally everything for the rings `ι A`
(`New.Variety.IsZariskiLocallyTop`), then its restriction `U.whisker φ` along `φ : C' ⥤ C` is
locally everything for the rings `ι (φ A')`. -/
lemma IsZariskiLocallyTop.whisker {ι : C ⥤ CommRingCat} {U : Subfunctor Y}
    (h : IsZariskiLocallyTop ι U) : IsZariskiLocallyTop (φ ⋙ ι) (U.whisker φ) := by
  intro A y m hm_max
  obtain ⟨a, ha_not_mem, h_mem_of_unit⟩ : ∃ a ∉ m, ∀ (B : C) (f : φ.obj A ⟶ B),
      IsUnit (ι.map f a) → Y.map f y ∈ U B := h (φ.obj A) y m hm_max
  exact ⟨a, ha_not_mem, fun B f ↦ h_mem_of_unit (φ.obj B) (φ.map f)⟩

/-! ### Pointwise surjections, integer relations and products of coefficients -/

/-- The property of p: E → Y that E(A) → Y(A) is surjective for every object A. -/
def IsPointwiseSurjective : Prop := ∀ A : C, Surjective (p A)

variable {R φ} {ι : Type} (F : ι → AbFunctor C) {I V V' : Type*} [Fintype I]

/-- For u: Y' → Y∘φ, the induced map of free abelian group functors Z[Y'] → Z[Y]∘φ. -/
abbrev freeAbMap {Y : C ⥤ Type 1} {Y' : C' ⥤ Type 1} (u : Y' ⟶ φ ⋙ Y) : freeAb Y' ⟶ φ ⋙ freeAb Y :=
  freeAb.map u

/-- For a ring `R` and a map f: A → R, any a, b in R have an idempotent e of A with a ∣ f(e)b and
b ∣ (1 − f(e))a: on one part of the partition given by f(e), a divides b, and on the other part b
divides a. -/
def IsComparableRing {A : Type*} [Mul A] (f : A → R) : Prop :=
  ∀ a b : R, ∃ e : A, IsIdempotentElem e ∧ a ∣ f e * b ∧ b ∣ (1 - f e) * a

/-- The integers `m i` add up to zero on every fibre of `v`, that is, `∑ m i • [v i] = 0` in the
free abelian group on `V`. -/
def Cancels (m : I → ℤ) (v : I → V) : Prop := ∑ i : I, m i • FreeAbelianGroup.of (v i) = 0

/-- If the integers `m i` cancel on the fibres of `v` and `v'` factors through `v` (equal values
of `v` give equal values of `v'`), then they cancel on the fibres of `v'`. -/
lemma Cancels.mono {m : I → ℤ} {v : I → V} {v' : I → V'} (h : Cancels m v)
    (hv : FactorsThrough v' v) : Cancels m v' := by
  -- Apply to `∑ m i • of (v i) = 0` the additive map that sends `of (v i)` to `of (v' i)`;
  -- it exists because `v'` factors through `v`.
  let g : V → FreeAbelianGroup V' := extend v (of ∘ v') 0
  have hg (i : I) : g (v i) = of (v' i) := (hv.comp_left of).extend_apply 0 i
  unfold Cancels at h ⊢
  calc ∑ i : I, m i • of (v' i)
      = lift g (∑ i : I, m i • of (v i)) := by
        simp [_root_.map_sum, _root_.map_zsmul, lift_apply_of, hg]
    _ = 0 := by rw [h, map_zero]

/-- For a family `F : ι → AbFunctor C` of abelian-group-valued functors on C (here `ι` is an index
type), the functor sending A to the product of the groups F_i(A). -/
def piAbFunctor : AbFunctor C :=
  CategoryTheory.Functor.mk _ fun f ↦ ofHom (AddMonoidHom.piMap fun i ↦ ((F i).map f).hom)

/-- The projection from the product of the family `F : ι → AbFunctor C` of functors to its i-th
factor F_i. -/
def piAbFunctor.π (i : ι) : piAbFunctor F ⟶ F i where
  app _ := ofHom (Pi.evalAddMonoidHom _ i)

/-- For a family of maps f_i : A_i → B_i, the assertion that every f_i is bijective. -/
abbrev AllBijective {ι : Sort*} {A B : ι → Type*} (f : ∀ i : ι, A i → B i) : Prop :=
  ∀ i : ι, Bijective (f i)

/-- A natural transformation with values in a concrete category whose forgetful functor reflects
isomorphisms is an isomorphism if it is bijective at every object. -/
abbrev isoOfAppBijective {C : Type*} [Category C] {P : D → D → Type _} {T : D → Type _}
    [∀ X Y, FunLike (P X Y) (T X) (T Y)] {F G : C ⥤ D} [ConcreteCategory D P]
    [(forget D).ReflectsIsomorphisms] (γ : F ⟶ G) (h : AllBijective fun A : C ↦ γ A) :
    F ≅ G :=
  haveI h_iso : IsIso γ := by
    simpa [γ.isIso_iff_isIso_app, ConcreteCategory.isIso_iff_bijective] using h
  asIso γ

end New.Variety

end Defs

/-!
## Test rings, functors of points and locally constant coefficients

* `New.Variety.PointFunctor`, `New.Variety.pointsToBase`: spaces, and the map from the functor of
  points of a scheme over Spec R to h_R.
-/

section TestCohomology

open CategoryTheory AlgebraicGeometry PrimeSpectrum Spec ObjectProperty Subfunctor

namespace New.Variety

variable (A : Type*) [CommRing A] (Λ : Ab.{0})

/-! ### Test rings -/

/-- A is an absolutely integrally closed local domain: a local domain in which every monic
polynomial of positive degree has a root. -/
class IsAbsIntegrallyClosedLocal extends IsDomain A, IsLocalRing A, IsAbsIntegrallyClosed A

/-- A is a test ring: reduced, absolutely integrally closed, and any a, b admit an idempotent e
with a ∣ eb and b ∣ (1 − e)a. -/
structure IsTest extends IsAbsIntegrallyClosed A where
  /-- Any two elements of `A` are comparable for divisibility after a partition by an idempotent
  (`New.Variety.IsComparableRing` for the identity map of `A`). -/
  isComparableRing : IsComparableRing (· : A → A)
  /-- The ring `A` has no nonzero nilpotent elements. -/
  isReduced : IsReduced A

/-- The category of test rings (`New.Variety.IsTest`), as a full subcategory of commutative
rings. -/
abbrev TestRing : Type 1 := FullSubcategory (C := CommRingCat.{0}) (IsTest ·)

/-- The inclusion functor from the category of test rings into the category of commutative
rings. -/
abbrev testIncl : TestRing ⥤ CommRingCat := ObjectProperty.ι _

/-! ### Spaces and their cohomology -/

/-- The category of covariant functors from (small) commutative rings to sets of the next
universe. -/
abbrev PointFunctor : Type 2 := CommRingCat.{0} ⥤ Type 1

variable {X Y : PointFunctor} (u : X ⟶ Y) {R : CommRingCat} (s : X ⟶ reprBy R) (I : Set R)
  {B : CommRingCat} (φ : R ⟶ B)

/-- For an abelian group Λ, the functor on commutative rings sending A to the group of locally
constant functions Spec A → Λ. -/
def locConstSpec : CommRingCat.{0} ⥤ Ab where
  obj A := AddCommGrpCat.of (LocallyConstant (PrimeSpectrum A) Λ)
  map f :=
    AddCommGrpCat.ofHom (LocallyConstant.comapAddMonoidHom ⟨comap f.hom, continuous_comap f.hom⟩)

/-- For an abelian group Λ, the coefficient functor on test rings sending A to the group of
locally constant functions Spec A → Λ. -/
def locConstCoeff : AbFunctor TestRing := liftCoeff (testIncl ⋙ locConstSpec Λ)

/-- For a map u: X → Y of set-valued functors on rings, its restriction to a map of functors on
test rings. -/
abbrev mapOnTests : testIncl ⋙ X ⟶ testIncl ⋙ Y := testIncl.whiskerLeft u

/-- For u: X → Y and each degree n, the pull-back homomorphism Hⁿ(Y, Λ) → Hⁿ(X, Λ) on
cohomology computed on test rings. -/
abbrev TestCohomology.map :
    (n : ℕ) →
    H (freeAb.obj (testIncl ⋙ Y)) (locConstCoeff Λ) n →+
      H (freeAb.obj (testIncl ⋙ X)) (locConstCoeff Λ) n :=
  H.map (locConstCoeff Λ) (freeAb.map (mapOnTests u))

/-- The map u: X → Y of functors on rings induces isomorphisms Hⁱ(Y, Λ) → Hⁱ(X, Λ) in each degree i,
for cohomology computed on test rings with locally constant coefficients. -/
abbrev IsTestCohomEquiv : Prop := IsCohomEquiv (locConstCoeff Λ) (freeAb.map (mapOnTests u))

/-- The image of u: X → Y, restricted to test rings, is cohomologically dense in Y for the
coefficient functor of locally constant functions Spec A → Λ. -/
abbrev HasCohomDenseImage : Prop := IsCohomDense (locConstCoeff Λ) (range (mapOnTests u))

/-! ### Spaces over a ring -/

/-- For a morphism s: X → Spec R, the map from the functor of points of X to h_R sending a
point x ∈ X(A) to the ring map R → A whose spectrum is s∘x. -/
def pointsToBase {X : Scheme} {R : CommRingCat} (s : X ⟶ Spec R) :
    Scheme.Spec.rightOp ⋙ uliftYoneda.obj X ⟶ reprBy R where
  -- a point `x : Spec B ⟶ X` goes to the ring map `R ⟶ B` whose spectrum is `x ≫ s`
  app B := ↾fun x ↦ ULift.up (Spec.preimage (x.1 ≫ s))
  naturality := by
    -- the goal is the naturality of `Spec.preimage` under precomposition, after unfolding `h_R`
    delta reprBy reprFunctor
    aesop

/-- For s: X → h_R and a point x ∈ X(B), the ring homomorphism R → B that is the image of x
under s. -/
def baseRingMap (x : X B) : R ⟶ B := (s B x).down

/-- The map of `h_R` along `f : B ⟶ B'` sends a ring map `R ⟶ B` to its composite with `f`. -/
private lemma reprBy_map_down {B' : CommRingCat} (f : B ⟶ B') (y : (reprBy R).obj B) :
    ((reprBy R).map f y).down = y.down ≫ f :=
  rfl

@[simp]
lemma baseRingMap_map {B' : CommRingCat} (f : B ⟶ B') (x : X.obj B) :
    baseRingMap s (X.map (X := B) (Y := B') f x) = baseRingMap s x ≫ f := by
  simp [baseRingMap, NatTrans.naturality_apply, reprBy_map_down]

/-- For s: X → h_R and a subset I of R, the subfunctor of points x ∈ X(B) whose structure map
R → B sends I to 0. -/
def zeroPoints : Subfunctor X :=
  Subfunctor.mk (fun _ ↦ {x | ∀ a ∈ I, baseRingMap s x a = 0}) (by aesop)

/-- For s: X → h_R and a subset I of R, the subfunctor of points x ∈ X(B) whose structure map
R → B sends every element of I to a unit. -/
def unitPoints : Subfunctor X :=
  Subfunctor.mk (fun _ ↦ {x | ∀ a ∈ I, IsUnit (baseRingMap s x a)}) (by simp_all [IsUnit.map])

/-- For s: X → h_R and a ring map φ: R → B, the base change X_B = X ×_{h_R} h_B. -/
abbrev baseChangeOf : CommRingCat ⥤ Type 1 := fibreProd s (reprMap φ)

end New.Variety

end TestCohomology
namespace New.Variety

/-!
## Stability of test rings; local rings as valuation rings

Stability properties of test rings, the rings on which points and cohomology are evaluated.

* `New.Variety.isTest_of_preValuationRing`: an absolutely integrally closed domain in which of any
  two elements one divides the other is a test ring.
* `New.Variety.IsTest.pi`, `New.Variety.IsTest.localization`, `New.Variety.IsTest.quotient`:
  products, localisations and quotients by radical ideals of test rings are test rings.
* `New.Variety.IsTest.exists_valuationSubring_atPrime`: the local rings of a test ring are valuation
  rings of algebraically closed fields.
-/

section TestRings

open IsLocalRing ValuationRing IsLocalization IsAbsIntegrallyClosed LocallyConstant Ideal.Quotient

universe u

variable {A : Type u}
  {B : Type*} [CommRing A] [CommRing B]
  {M : Submonoid A} {f : A →+* B} (K : Type*) [Field K] [IsAlgClosed K]

/-- An algebraically closed field is an absolutely integrally closed local domain. -/
instance : IsAbsIntegrallyClosedLocal K := {}

/-- A valuation subring of an algebraically closed field is an absolutely integrally closed local
domain. -/
instance (V : ValuationSubring K) : IsAbsIntegrallyClosedLocal V := {of_isIntegrallyClosedIn K with}

/-- The group of locally constant functions `Spec A → Λ` is generated by the functions equal to
a constant `a` on the basic open set `D(e)` of an idempotent `e` and to `0` elsewhere: a subgroup
that contains these functions contains every locally constant function. -/
lemma locallyConstant_mem_of_indicator {Λ : Type*} [AddCommGroup Λ]
    {S : AddSubgroup (LocallyConstant (PrimeSpectrum A) Λ)}
    (h : ∀ (a : Λ) (e : A) (he : IsIdempotentElem e),
      indicator (const (PrimeSpectrum A) a) (PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩) ∈ S)
    (y : LocallyConstant (PrimeSpectrum A) Λ) : y ∈ S := by
  classical
  -- Each fibre of `y` is clopen, hence of the form `D(e a)` with `e a` idempotent, and `y` is
  -- the finite sum over its values `a` of the functions equal to `a` on `D(e a)` and `0` elsewhere.
  choose e he_idem h_fiber_eq using show ∀ a : Λ,
      ∃ e : A, IsIdempotentElem e ∧ {x | y.toFun x = a} = PrimeSpectrum.basicOpen e from
    fun a ↦ PrimeSpectrum.isClopen_iff.mp (y.isLocallyConstant.isClopen_fiber a)
  have h_clopen (a : Λ) : IsClopen (PrimeSpectrum.basicOpen (e a) : Set (PrimeSpectrum A)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e a, he_idem a, rfl⟩
  have h_sum : y = ∑ a ∈ y.range_finite.toFinset,
      indicator (const (PrimeSpectrum A) a) (h_clopen a) := by
    ext x
    -- at `x` only the term of `a = y x` is non-zero
    change evalAddMonoidHom x y = evalAddMonoidHom x _
    rw [map_sum]
    simp [Set.indicator, ← h_fiber_eq]
  rw [h_sum]
  exact sum_mem fun a _ ↦ h a (e a) (he_idem a)

/-- If divisibility in `A` is total, every element of the extension of an ideal `J` along
`f : A →+* B` is a multiple of `f i` for a single `i ∈ J`. -/
lemma exists_map_dvd_of_mem_map [PreValuationRing A] {J : Ideal A} {x : B}
    (hx : x ∈ Ideal.map f J) : ∃ i ∈ J, f i ∣ x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, hi, dvd_rfl⟩
  | zero => exact ⟨0, J.zero_mem, dvd_zero _⟩
  | add x y _ _ ih_x ih_y =>
    -- of the two elements of `J`, one divides the other, and its image divides both terms
    obtain ⟨i, hi, h_dvd_x⟩ := ih_x
    obtain ⟨j, hj, h_dvd_y⟩ := ih_y
    obtain h_ij | h_ji := dvd_total i j
    · exact ⟨i, hi, dvd_add h_dvd_x ((map_dvd f h_ij).trans h_dvd_y)⟩
    · exact ⟨j, hj, dvd_add ((map_dvd f h_ji).trans h_dvd_x) h_dvd_y⟩
  | smul a x _ ih =>
    obtain ⟨i, hi, h_dvd_x⟩ := ih
    exact ⟨i, hi, h_dvd_x.mul_left a⟩

/-- An absolutely integrally closed domain `A` in which of any two elements one divides the other
(`PreValuationRing A`) is a test ring: the idempotent `e` can be taken to be `1` or `0`. -/
lemma isTest_of_preValuationRing [IsDomain A] [PreValuationRing A] [IsAbsIntegrallyClosed A] :
    IsTest A where
  toIsAbsIntegrallyClosed := inferInstance
  isComparableRing := by
    -- take `e = 1` if `a ∣ b` and `e = 0` if `b ∣ a`
    intro a b
    obtain h_dvd | h_dvd := dvd_total a b
    · exact ⟨1, .one, by simpa using h_dvd, by simp⟩
    · exact ⟨0, .zero, by simp, by simpa using h_dvd⟩
  isReduced := inferInstance

/-! ### Products, localisations and quotients of test rings -/

/-- A product of test rings is a test ring. -/
lemma IsTest.pi {ι : Type*} {R : ι → Type*} [∀ i : ι, CommRing (R i)]
    (h_test : ∀ i : ι, IsTest (R i)) : IsTest (∀ i : ι, R i) := by
  have h_red (i : ι) : IsReduced (R i) := (h_test i).isReduced
  refine
    { exists_root := fun P hP h_deg ↦ ?_
      isComparableRing := fun a b ↦ ?_
      isReduced := inferInstance }
  · -- choose a root of `P` in every factor
    have h_root (i : ι) : ∃ x : R i, P.eval₂ (Pi.evalRingHom R i) x = 0 :=
      (h_test i).exists_eval₂_eq_zero (Pi.evalRingHom R i) hP h_deg
    choose x hx using h_root
    -- the `i`-th component of `P(x)` is `P` evaluated at `x i` through the projection to `R i`
    have h_eval (i : ι) : P.eval x i = P.eval₂ (Pi.evalRingHom R i) (x i) := by
      simp [P.eval₂_eq_sum_range, Polynomial.eval]
    exact ⟨x, funext fun i ↦ (h_eval i).trans (hx i)⟩
  · -- choose a comparing idempotent in every factor
    have h_idem (i : ι) :
        ∃ e : R i, IsIdempotentElem e ∧ a i ∣ e * b i ∧ b i ∣ (1 - e) * a i :=
      (h_test i).isComparableRing (a i) (b i)
    choose e he_idem h_dvd_ab h_dvd_ba using h_idem
    exact ⟨e, funext he_idem, pi_dvd_iff.mpr h_dvd_ab, pi_dvd_iff.mpr h_dvd_ba⟩

/-- Let `A` be a test ring and `f : A →+* B` a ring map such that every element of `B` is
associated to (a unit times) the image of an element of `A`. Then any `y`, `z` in `B` have an
idempotent `e` of `A` with `y ∣ f e * z` and `z ∣ (1 - f e) * y` (`IsComparableRing f`). -/
lemma IsTest.isComparableRing_of_associated (h : IsTest A)
    (hf : ∀ y : B, ∃ x : A, Associated (f x) y) : IsComparableRing f := by
  -- Up to units, two elements of `B` are images of elements of `A`, and these are comparable.
  intro y z
  obtain ⟨a, u, rfl⟩ : ∃ a : A, Associated (f a) y := hf y
  obtain ⟨b, v, rfl⟩ : ∃ b : A, Associated (f b) z := hf z
  obtain ⟨e, he_idem, h_dvd_ab, h_dvd_ba⟩ :
      ∃ e : A, IsIdempotentElem e ∧ a ∣ e * b ∧ b ∣ (1 - e) * a := h.isComparableRing a b
  have h_dvd_yz : f a * u ∣ f e * (f b * v) := by
    simpa [← mul_assoc] using f.map_dvd h_dvd_ab
  have h_dvd_zy : f b * v ∣ (1 - f e) * (f a * u) := by
    simpa [← mul_assoc] using f.map_dvd h_dvd_ba
  exact ⟨e, he_idem, h_dvd_yz, h_dvd_zy⟩

/-- If any two elements of `B` are comparable by an idempotent `e` of `A` through `f`, then they are
comparable by the idempotent `f e` of `B` itself. -/
lemma IsComparableRing.id (h : IsComparableRing f) : IsComparableRing (id : B → B) := fun a b ↦
  have ⟨e, he_idem, h_dvd_ab, h_dvd_ba⟩ := h a b
  ⟨f e, he_idem.map f, h_dvd_ab, h_dvd_ba⟩

/-- Every element of the localisation of `A` at `M` is associated to the image of an element
of `A`. -/
lemma exists_associated_localization (y : Localization M) :
    ∃ x : A, Associated (algebraMap A (Localization M) x) y := by
  -- `y = x / s`, so `y` times the unit `s` is `x`
  obtain ⟨⟨x, s⟩, h_eq⟩ := IsLocalization.surj M y
  exact ⟨x, .symm ⟨(map_units (Localization M) s).unit, h_eq⟩⟩

/-- The localisation of a test ring `A` at a submonoid `M` is a test ring. -/
lemma IsTest.localization (h : IsTest A) : IsTest (Localization M) :=
  have : IsReduced A := h.isReduced
  ⟨h.of_isLocalization M,
    (h.isComparableRing_of_associated exists_associated_localization).id, inferInstance⟩

/-- The quotient of a test ring by a radical ideal is a test ring. -/
lemma IsTest.quotient (h : IsTest A) {J : Ideal A} (hJ : J.IsRadical) : IsTest (A ⧸ J) := by
  have h_assoc (y : A ⧸ J) : ∃ x : A, Associated (Ideal.Quotient.mk J x) y :=
    (mk_surjective y).imp fun _ hx ↦ .of_eq hx
  exact ⟨h.of_surjective mk_surjective, (h.isComparableRing_of_associated h_assoc).id,
    J.isRadical_iff_quotient_reduced.mp hJ⟩

/-- Let `A` be a test ring, `p` a prime ideal of `A` and `L` the localisation of `A` at `p`. Then
`L` is an absolutely integrally closed local domain (`IsAbsIntegrallyClosedLocal`), of any two
elements of `L` one divides the other (`PreValuationRing`), and there are an algebraically closed
field `K`, a valuation subring `O` of `K` and an `A`-algebra structure on `O` for which `O` is a
localisation of `A` at `p`. -/
lemma IsTest.exists_valuationSubring_atPrime (h : IsTest A) (p : Ideal A) [p.IsPrime] :
    let L := Localization.AtPrime p
    IsAbsIntegrallyClosedLocal L ∧ PreValuationRing L ∧
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (O : ValuationSubring K) (_ : Algebra A O),
      IsLocalization.AtPrime O p := by
  -- The localisation `L` is a local test ring. There one of `e`, `1 - e` is a unit for every `e`,
  -- so of any two elements one divides the other; being reduced, `L` is then a domain, hence a
  -- valuation ring of its fraction field.
  intro L
  have h_test_L : IsTest L := h.localization
  have h_test_frac : IsTest (FractionRing L) := h_test_L.localization
  obtain ⟨h_aic, h_comp, h_red⟩ := h_test_L
  have h_total (x y : L) : x ∣ y ∨ y ∣ x := by
    obtain ⟨e, he_idem, h_dvd_xy, h_dvd_yx⟩ := h_comp x y
    obtain h_unit | h_unit : IsUnit e ∨ IsUnit (1 - e) := isUnit_or_isUnit_one_sub_self e
    · exact Or.inl (h_unit.dvd_mul_left.mp h_dvd_xy)
    · exact Or.inr (h_unit.dvd_mul_left.mp h_dvd_yx)
  -- `x * y` divides `x ^ 2` or `y ^ 2`, and `L` is reduced, so `L` has no zero divisors
  have h_sq (x y : L) : x * y ∣ x * x ∨ x * y ∣ y * y :=
    (h_total y x).imp (mul_dvd_mul_left x) fun hxy ↦ mul_dvd_mul_right hxy y
  have h_zero {x y : L} (hxy : x * y = 0) : x = 0 ∨ y = 0 := by
    simpa [hxy, ← sq] using h_sq x y
  have : NoZeroDivisors L := ⟨h_zero⟩
  have : IsDomain L := NoZeroDivisors.to_isDomain L
  have h_aic_local : IsAbsIntegrallyClosedLocal L := { h_aic with }
  have : ValuationRing L := iff_dvd_total.mpr ⟨h_total⟩
  -- `L` is the ring of integers `O` of its valuation on `FractionRing L`, which is algebraically
  -- closed as a localisation of the test ring `L`
  let O : ValuationSubring (FractionRing L) := (valuation L (FractionRing L)).valuationSubring
  let e_int : L ≃+* O := equivInteger L (FractionRing L)
  let h_alg : Algebra A O := (e_int.toRingHom.comp (algebraMap A L)).toAlgebra
  have h_loc : IsLocalization.AtPrime O p :=
    (isLocalization_iff_of_ringEquiv p.primeCompl e_int).1 inferInstance
  exact ⟨h_aic_local, inferInstance, FractionRing L, inferInstance, h_test_frac.isAlgClosed, O,
    h_alg, h_loc⟩

/-- The residue field of an absolutely integrally closed local domain is algebraically closed. -/
instance [IsAbsIntegrallyClosedLocal A] : IsAlgClosed (ResidueField A) :=
  isAlgClosed (.of_surjective residue_surjective)

end TestRings

/-!
## Functoriality of cohomology and induction by dimension shifting

For a comparison `c = (φ, β)` (`New.Variety.Comparison`), `c.pull α` restricts along the functor
`φ`, pushes by `β` and pulls by `α`.

* `New.Variety.Comparison.map_pull_eq_pull_map`, `New.Variety.Comparison.pull_push`,
  `New.Variety.Comparison.pull_trans`: comparisons commute with pull-back and push-forward, and they
  compose.
-/

section Functoriality

open CategoryTheory Limits Abelian.Ext Functor Function H ShortComplex ShortExact

variable {D : Type _}
  {C C' C'' : Type 1} [Category D] [Category C] [Category C'] [Category C'']
  {F G N M K : AbFunctor C} {F' G' N' M' : AbFunctor C'} {F'' N'' : AbFunctor C''} {n : ℕ}
  (c : Comparison F F') (c' : Comparison F' F'') (a' : M' ⟶ N') (a : N' ⟶ c.functor ⋙ N)
  (α' : K ⟶ M) (α : M ⟶ N) (β : F ⟶ G) (β' : G ⟶ K) (Ξ : (D ⥤ Ab) ⥤ AbFunctor C')
  {R : Type _} [Ring R]

/-! ### Induction on classes and exact functors -/

/-- The functor is exact: it is additive and preserves finite limits and finite colimits. -/
class abbrev IsExactFunctor :=
  Additive Ξ, PreservesFiniteLimits Ξ, PreservesFiniteColimits Ξ

/-- A ring `R` acting on `F` acts on `Ext^n(N,F)` by push-forward along the endomorphism of `F`
by which `r` acts. -/
lemma H.smul_eq_push [CoeffAction R F] (r : R) (x : H N F n) : r • x = push N
  (CoeffAction.act r : End F).asHom n x := rfl

variable (R)
  {Φ Ψ : (C ⥤ Ab) ⥤ AbFunctor C'} [IsExactFunctor (D := C) (C' := C') Φ] [IsExactFunctor Ψ]
  {Θ : (C' ⥤ Ab) ⥤ AbFunctor C''} [IsExactFunctor (D := C') (C' := C'') Θ] (η : Φ ⟶ Ψ) (x : H N F n)

/-- Functors from `C` to abelian groups form a Grothendieck abelian category. -/
instance : IsGrothendieckAbelian.{1} (AbFunctor C) :=
  { ab5OfSize := { ofShape := fun _ ↦ inferInstance }
    hasSeparator := .of_equivalence (opOpEquivalence C).congrLeft }

/-- Induction on Ext classes out of `N`: a property `P` holds for every class `x` in `Ext^n(N,F)` if
it holds for the classes `mk₀ f` of morphisms `f : N ⟶ F` (`h₀`) and, for each short exact
sequence `S` of functors `0 → S.X₁ → S.X₂ → S.X₃ → 0` and each `y` in `Ext^n(N,S.X₃)`, passes from
`y` to its image in `Ext^{n+1}(N,S.X₁)` under the connecting class (`h`). -/
@[induction_eliminator]
lemma H.dimension_shift_induction {P : ∀ {F : AbFunctor C} {n : ℕ}, H N F n → Prop}
    (h₀ : ∀ (F : AbFunctor C) (f : N ⟶ F), P (F := F) (n := 0) (mk₀ f))
    (h : ∀ (S : ShortComplex (AbFunctor C)) (hS : ShortExact S) (n : ℕ) (y : H N S.X₃ n),
      P y → P (y.comp hS.extClass rfl)) :
    P x := by
  -- Dimension shifting: induction on the degree `n`, for all coefficients `F` at once.
  induction n generalizing F with
  | zero =>
    obtain ⟨f, rfl⟩ := (mk₀_bijective N F).surjective x
    exact h₀ F f
  | succ n ih =>
    -- Embed `F` in an injective object `I`; `x` dies in `Ext^{n+1}(N,I)`, so it is the image of a
    -- class on the cokernel `I/F` under the connecting map.
    let S : ShortComplex (AbFunctor C) :=
      ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : ShortExact S := ⟨exact_cokernel (Injective.ι F)⟩
    obtain ⟨y, rfl⟩ : ∃ y : H N S.X₃ n, y.comp hS.extClass rfl = x :=
      x.covariant_sequence_exact₁ N hS (eq_zero_of_injective _) rfl
    exact h S hS n y (ih y)

set_option backward.isDefEq.respectTransparency false

lemma mapExactFunctor_mapExactFunctor :
    (x.mapExactFunctor Φ).mapExactFunctor Θ = x.mapExactFunctor (Φ ⋙ Θ) := by
  induction x with
  | h₀ F f => simp [mapExactFunctor_mk₀]
  | h S hS n x ih => simp [ih, mapExactFunctor_comp, mapExactFunctor_extClass]

/-- For a natural transformation η: Φ → Ψ of exact functors and x in Ext^n(N,F), pushing Φ(x)
forward along η_F equals pulling Ψ(x) back along η_N, in Ext^n(ΦN,ΨF). -/
lemma mapExactFunctor_naturality :
    push (Φ.obj N) (η F) n (x.mapExactFunctor Φ) =
      H.map (Ψ.obj F) (η N) n (x.mapExactFunctor Ψ) := by
  induction x with
  | h₀ => simp [H.push, mapExactFunctor_mk₀, H.map]
  | h S hS n x ih =>
    -- The connecting classes of `Φ S` and `Ψ S` are compatible with `η` (`h_nat`). After
    -- unfolding, reassociate the composites and use `h_nat`, then `ih`.
    have h_nat : (hS.map_of_exact Φ).extClass.comp (mk₀ (η.app S.X₁)) (add_zero 1) =
        (mk₀ (η.app S.X₃)).comp (hS.map_of_exact Ψ).extClass (zero_add 1) :=
      extClass_naturality (hS.map_of_exact Φ) (hS.map_of_exact Ψ) (mapNatTrans S η)
    simp_all [← comp_assoc_of_second_deg_zero, comp_assoc (h₂₃ := rfl), H.push, H.map,
      mapExactFunctor_comp, mapExactFunctor_extClass]

namespace H

@[simp]
lemma map_id : map F (𝟙 N) n x = x := by simp [map]

lemma map_comp : map F (α' ≫ α) n x = map F α' n (map F α n x) := by simp [map]

lemma push_comp : push N (β ≫ β') n x = push N β' n (push N β n x) := by simp [H.push]

/-- The additive map sending a morphism α: M → N to the pull-back Ext^n(N,F) → Ext^n(M,F). -/
def mapHom (F M N : AbFunctor C) (n : ℕ) : (M ⟶ N) →+ H N F n →+ H M F n :=
  AddMonoidHom.mk' (fun α : M ⟶ N ↦ map F α n) (by simp [map, mk₀_add])

lemma map_push : map G α n (push N β n x) = push M β n (map F α n x) := by simp [map, H.push]

/-- For a ring R acting on F and α: M → N, the pull-back Ext^n(N,F) → Ext^n(M,F) as an R-linear
map. -/
def mapₗ (F : AbFunctor C) [CoeffAction R F] (α : M ⟶ N) (n : ℕ) : H N F n →ₗ[R] H M F n :=
  { map F α n with map_smul' r := map_push α (CoeffAction.act r : End F).asHom }

lemma mapExactFunctor_restrictAlong_id : x.mapExactFunctor (restrictAlong (𝟭 C)) = x := by
  induction x with
  | h₀ F f => simp [mapExactFunctor_mk₀, show (𝟭 C).whiskerLeft f = f from rfl]
  | h S hS n x ih => simp [ih, mapExactFunctor_comp, mapExactFunctor_extClass]

end H

/-- An isomorphism `α : M ⟶ N` induces bijections `Ext^n(N,F) → Ext^n(M,F)` in every degree. -/
lemma IsCohomEquiv.of_isIso [IsIso α] : IsCohomEquiv F α := by
  intro n
  -- pull-back along `inv α` is inverse to pull-back along `α`
  refine bijective_iff_has_inverse.mpr ⟨map F (inv α) n, fun x ↦ ?_, fun x ↦ ?_⟩ <;>
    simp [← H.map_comp]

/-- If `γ : F ⟶ G` and `γ' : F' ⟶ G'` intertwine the coefficient maps of two comparisons with the
same functor `c.functor`, then the comparison maps commute with push-forward along `γ` and `γ'`. The
target of `α` is `c.functor ⋙ N`, written through the comparison `⟨c.functor, β⟩`. -/
lemma Comparison.pull_push (β : c.functor ⋙ G ⟶ G') (γ : F ⟶ G) (γ' : F' ⟶ G')
    (h : whiskerLeft c.functor γ ≫ β = c.coeffHom ≫ γ')
    (α : N' ⟶ { functor := c.functor, coeffHom := β : Comparison G G' }.functor ⋙ N) (x : H N F n) :
    pull ⟨c.functor, β⟩ α n (push N γ n x) = push N' γ' n (c.pull α n x) := by
  -- after unfolding, both sides push along `whiskerLeft c.functor γ ≫ β = c.coeffHom ≫ γ'`
  simp [h, pull, H.map, H.push, mapExtAddHom, mapExactFunctor_comp, mapExactFunctor_mk₀]

@[simp]
lemma Comparison.id_pull : (id F).pull α = H.map F α := by
  ext n x
  simp [mapExactFunctor_restrictAlong_id, x.comp_mk₀_id, pull, H.map, H.push, mapExtAddHom]

/-- The composite of comparisons (φ,β) from F to F' and (φ',β') from F' to F'': the functor φ∘φ'
with the map Fφφ' → F'φ' → F''. -/
abbrev Comparison.trans : Comparison F F'' where
  functor := c'.functor ⋙ c.functor
  coeffHom := c'.functor.whiskerLeft c.coeffHom ≫ c'.coeffHom

variable {c c' a a' α' α}

/-- If `α' : K ⟶ M` induces bijections on cohomology with coefficients `F`, then `α' ≫ α` does if
and only if `α : M ⟶ N` does. -/
lemma IsCohomEquiv.comp_iff (h' : IsCohomEquiv F α') :
    IsCohomEquiv F (α' ≫ α) ↔ IsCohomEquiv F α := by
  refine forall_congr' fun n ↦ ?_
  rw [show ⇑(H.map F (α' ≫ α) n) = H.map F α' n ∘ H.map F α n from funext (H.map_comp α' α)]
  exact (h' n).of_comp_iff' _

namespace Comparison

/-- The comparison map of `(𝟭 C, β)` along the identity of `N` is the push-forward along `β`. -/
lemma pull_id_eq_push : pull ⟨𝟭 C, β⟩ (𝟙 N) n = push N β n := by
  ext
  simp [mapExactFunctor_restrictAlong_id, pull, H.map, H.push, mapExtAddHom]

/-- For `η : φ ⟶ ψ` and `β : ψ ⋙ F ⟶ F'`, moving `η` from the coefficient map (`η F` before
`β`) to the source map (`η N` after `α`) does not change the comparison map. The target of `α` is
`φ ⋙ N`, written through the comparison `⟨φ, whiskerRight η F ≫ β⟩`. -/
lemma pull_whiskerRight {φ ψ : C' ⥤ C} (η : φ ⟶ ψ) (β : ψ ⋙ F ⟶ F')
    (α : N' ⟶ { functor := φ, coeffHom := whiskerRight η F ≫ β : Comparison F F' }.functor ⋙ N) :
    pull ⟨φ, whiskerRight η F ≫ β⟩ α n = pull ⟨ψ, β⟩ (α ≫ whiskerRight η N) n := by
  ext x
  -- `η` induces a map of restriction functors; push its naturality by `β` and pull it by `α`.
  have h_nat : push (φ ⋙ N) (whiskerRight η F) n (x.mapExactFunctor (restrictAlong φ)) =
      H.map (ψ ⋙ F) (whiskerRight η N) n (x.mapExactFunctor (restrictAlong ψ)) :=
    mapExactFunctor_naturality ((whiskeringLeft C' C Ab).map η) x
  change H.map F' α n (push (φ ⋙ N) (whiskerRight η F ≫ β) n
      (x.mapExactFunctor (restrictAlong φ))) =
    H.map F' (α ≫ whiskerRight η N) n (push (ψ ⋙ N) β n (x.mapExactFunctor (restrictAlong ψ)))
  rw [H.push_comp, h_nat, H.map_comp, ← H.map_push]

/-! ### Squares and composites of comparisons -/

/-- The comparison `c` is natural in the source of cohomology: if `a' : M' ⟶ N'` lies over
`α : M ⟶ N`, in the sense that the square formed with `a` and `b` commutes, then pulling a class
back by `c` along `a` and then along `a'` is pulling it back along `α` and then by `c` along `b`. -/
lemma map_pull_eq_pull_map {a' : M' ⟶ N'} {a : N' ⟶ c.functor ⋙ N} {α : M ⟶ N}
    {b : M' ⟶ c.functor ⋙ M} (h_comm : a' ≫ a = b ≫ whiskerLeft c.functor α) (n : ℕ) (x : H N F n) :
    H.map F' a' n (c.pull a n x) = c.pull b n (H.map F α n x) := by
  -- both sides precompose the restricted and pushed class with one side of the square
  simp [H.map, pull, H.push, mapExtAddHom, mapExactFunctor_comp, mapExactFunctor_mk₀, h_comm]

/-- Comparison maps compose. Applying the comparison map of c along a and then that of c' along α'
gives the comparison map of the composite `New.Variety.Comparison.trans` c c', taken along
`α' ≫ whiskerLeft c'.functor a`, the map `a` restricted along the functor of c'. -/
lemma pull_trans {α' : N'' ⟶ c'.functor ⋙ N'} (x : H N F n) :
    c'.pull α' n (c.pull a n x) = (c.trans c').pull (α' ≫ whiskerLeft c'.functor a) n x := by
  -- restricting along `c.functor` and then along `c'.functor` is restricting along
  -- `c'.functor ⋙ c.functor`
  have h_restrict : (x.mapExactFunctor (restrictAlong c.functor)).mapExactFunctor
    (restrictAlong c'.functor) =
      x.mapExactFunctor (restrictAlong (c'.functor ⋙ c.functor)) :=
    mapExactFunctor_mapExactFunctor x
  simp [h_restrict, pull, H.map, H.push, mapExtAddHom, mapExactFunctor_comp, mapExactFunctor_mk₀]

end Comparison

end Functoriality

end New.Variety

/-!
## Module coefficients and points of an `R`-scheme in `k`-algebras

* `New.Variety.algPoints`: a scheme `X` over `R` gives the functor `A ↦ X(A)` on commutative
  `k`-algebras.
-/

section AlgebraPoints

open CategoryTheory AlgebraicGeometry CommRingCat Functor

namespace New.Variety

variable {k : Type} [CommRing k] {C : Type 1} [Category C] (F : C ⥤ ModuleCat k)

/-- A functor F from C to k-modules, regarded as a functor to abelian groups, so that it can
serve as the coefficients of cohomology. -/
def moduleCoeff : AbFunctor C := liftCoeff (F ⋙ forget₂ (ModuleCat k) Ab)

/-- The ring `k` acts on `moduleCoeff F` through the action of `k` on the values of `F`. -/
instance : CoeffAction k (moduleCoeff F) where
  act :=
    .comp ⟨((whiskeringRight ..) (forget₂ .. ⋙ AddCommGrpCat.uliftFunctor)).mapEnd F, rfl, by tauto⟩
      (algebraMap ..)

/-! ### Commutative algebras and functors of points -/

/-- The category of (small) commutative algebras over a commutative ring k. -/
abbrev CommAlg (k : Type) [CommRing k] : Type 1 := CommAlgCat.{0, 0} k

/-- A ring map of k-algebras that respects the structure maps, as a morphism of k-algebras. -/
abbrev CommAlg.homOfRingHom {A T : CommAlg k} (f : A →+* T)
    (e : ∀ (r : k), f.toFun ((algebraMap k A) r) = (algebraMap k T) r) : A ⟶ T :=
  (ConcreteCategory.ofHom ⟨f, e⟩ : A ⟶ T)

variable (k) (k' : Type) [CommRing k'] [Algebra k k'] (R : CommRingCat.{0}) [Algebra R k]

/-- Restriction of scalars along k → k': the functor regarding a commutative k'-algebra as a
k-algebra. -/
def restrictAlg : CommAlg k' ⥤ CommAlg k :=
  CategoryTheory.Functor.mk
    (id (@CommAlgCat.of k _ · _ {Algebra.restrictScalars .. with smul := (algebraMap k k' · • ·)}))
    (@id _ fun f ↦ CommAlg.homOfRingHom f.hom'.toRingHom fun _ ↦ f.hom'.commutes' _)

/-- For an R-algebra k, the contravariant functor from commutative k-algebras to schemes over
Spec R sending A to Spec A, with structure map given by R → k → A. -/
def specAlg : CommAlg k ⥤ (Over (Spec R))ᵒᵖ :=
  { restrictAlg R k ⋙ (algSpec R).rightOp with
    obj A := ⟨Over.mk (Spec.map (ofHom ((algebraMap k A).comp (algebraMap R k))))⟩ }

/-- For an R-algebra k, the functor sending a scheme X over Spec R to its functor of points
A ↦ X(A) on commutative k-algebras A. -/
def algPoints : Over (Spec R) ⥤ CommAlg k ⥤ Type 1 := uliftYoneda.{1} ⋙ restrictAlong (specAlg k R)

/-- For an R-algebra k and a scheme X over Spec R, the functor sending a commutative k-algebra A
to the set X(A) of morphisms Spec A → X over Spec R. -/
abbrev algPointsOf : Over (Spec R) → CommAlg k ⥤ Type 1 := (algPoints k R).obj

end New.Variety

end AlgebraPoints
/-!
## Tangent polynomials at coincidences and congruence relations

Maps `W ⟶ Z` of schemes over `R` are described through points with values in rings:
`New.Variety.PointsIn X A` is `X(A)`. A tangent vector at `y ∈ W(k)` is a point of `W(k[ε])` over
`y`.

* `New.Variety.IsTangentPoly`: a polynomial `P` with `P t = P 0 * det (1 - t (dc)⁻¹ du)` at a
  coincidence `c y = u y`.
* `New.Variety.IsNullFamily`: the local terms of a fixed point formula for a linear combination of
  maps add up to zero in weight `h`.
* `New.Variety.CongruenceRelation`: a congruence relation between maps and Frobenius powers modulo
  `𝔭`.
-/

section LocalTerms

open CategoryTheory AlgebraicGeometry CommAlgCat TrivSqZeroExt Module

namespace New.Variety

variable {k M : Type} [CommRing k] [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M]
  [IsCentralScalar k M] {R : CommRingCat} [Algebra R k]
  {Z W : Over (Spec R)} {A B : CommAlg k} (c : W ⟶ Z)

/-- The first projection `k ⊕ M → k` of the trivial square-zero extension is surjective, and its
kernel ideal squares to zero. -/
lemma fst_surjective_and_kerIdeal_sq_eq_bot :
    (fst (R := k) (M := M)).Surjective ∧ kerIdeal k M ^ 2 = ⊥ :=
  ⟨fst_surjective, by simp⟩

/-- The k-algebra homomorphism k ⊕ M → k from the trivial square-zero extension, sending (a, m)
to a. -/
def SqZeroExt.fst : of k (TrivSqZeroExt k M) ⟶ of k k := ofHom (fstHom k k M)

/-- The points X(A) of a scheme X over Spec R with values in the k-algebra A, that is, the
morphisms Spec A → X over Spec R. -/
abbrev PointsIn (X : Over (Spec R)) (A : CommAlg k) : Type 1 := algPointsOf k R X A

/-- For a k-algebra homomorphism φ: A → B and a point y in W(A), the point in W(B) obtained by
composing y with Spec φ. -/
noncomputable abbrev PointsIn.map (φ : A ⟶ B) : PointsIn W A → PointsIn W B :=
  (algPointsOf k R W).map φ

/-- `P` is a tangent polynomial of the maps `c, u : W ⟶ Z` at the point `y ∈ W(k)`, the algebraic
form of `P t = P 0 * det (1 - t (dc)⁻¹ du)`; here `W` and `Z` are functors of points on
commutative `k`-algebras.
Precisely: there are a finitely generated `k`-module `T`, a point `v ∈ W(k ⊕ T^*)` (square-zero
extension by the dual), which turns each `x ∈ T` into a point `f x ∈ W(k[ε])` by evaluation
`T^* → k` at `x`, and `A ∈ End T`, with (a) `T` of rank `d`;
(b) `v` lifts `y`, so the `f x` are tangent vectors at `y`;
(c) `x ↦ c (f x)` is injective; (d) `u (f x) = c (f (A x))`; (e) `P(t) = P(0) det (1 - t A)`
for all `t ∈ k`. -/
def IsTangentPoly {W Z : CommAlg k ⥤ Type 1} (d : ℕ) (c u : W ⟶ Z) (y : W.obj (of k k))
    (P : Polynomial k) : Prop :=
  ∃ᵉ (T : FGModuleCat k) (v : W.obj (of k (TrivSqZeroExt k (Dual k T)))) (A : Module.End k T),
    -- a vector `x : T` gives a point `f x` of `W` with values in `k ⊕ k`
    let f (x : T) := W.map (ofHom (TrivSqZeroExt.map (Dual.eval k T x))) v
    -- (a) `T` has dimension `d`
    finrank k T = d ∧
    -- (b) `v` lies over `y`
    W.map SqZeroExt.fst v = y ∧
    -- (c) `c` is injective on the points `f x`
    (c (of k (TrivSqZeroExt k k)) ∘ f).Injective ∧
    -- (d) `du = dc ∘ A`
    (∀ φ : T, u (of k (TrivSqZeroExt k k)) (f φ) = c (of k (TrivSqZeroExt k k)) (f (A φ))) ∧
    -- (e) `P(t) = P(0) det (1 - t A)`
    ∀ t : k, Polynomial.eval t P = P.eval 0 * (1 - t • A).det

/-- The formal sum `∑ a_i [u_i]` of maps `u_i : W ⟶ Z` is null in weight `h`, for tangent
polynomials of rank `d`: for every `c : W ⟶ Z`, let `S` be the set of coincidences `(i, y)` with
`a_i ≠ 0`, `y ∈ W(k)` and `c(y) = u_i(y)`. If each `(i, y)` in `S` is given a tangent polynomial
`P (i, y)` of rank `d` of `c, u_i` at `y` (`New.Variety.IsTangentPoly`) with `P(1) ≠ 0`, then `S`
is finite and the sum over `S` of `a_i · (coefficient of degree h of P) / P(1)` is zero. -/
def IsNullFamily {k I : Type} [Field k] [Algebra R k] (u : I → (W ⟶ Z)) (a : I →₀ k) (d h : ℕ) :
    Prop :=
  ∀ c : W ⟶ Z,
    -- the pairs of an index `i` with `a i ≠ 0` and a `k`-point where `c` and `u i` agree
    let S : Set (Σ _ : a.support, PointsIn W (CommAlgCat.of k k)) :=
      {y | y.snd.down ≫ c = y.snd.down ≫ u y.fst}
    ∀ P : (Σ _ : a.support, PointsIn W (CommAlgCat.of k k)) → Polynomial k,
      (∀ y ∈ S,
        IsTangentPoly d ((algPoints k R).map c) ((algPoints k R).map (u y.fst)) y.snd (P y) ∧
        (P y).eval 1 ≠ 0) →
      S.Finite ∧ ∑ᶠ y ∈ S, a y.fst * (P y).coeff h / (P y).eval 1 = 0

/-- A congruence relation between the maps `u_i : W ⟶ Z` and powers of Frobenius modulo `𝔭`: for
every field `k` of characteristic `p` and every point `x : Spec k ⟶ W` whose ring map `R → k`
sends every element of `𝔭` to zero, `∑ m_i [u_i(x) ∘ F^{a_i}] = 0` as a formal sum of points of `Z`
(`New.Variety.Cancels`), where `F^{a_i}` is the `a_i`-th iterate of the Frobenius `y ↦ y^p` of
`k`. -/
def CongruenceRelation {I : Type*} [Fintype I] (m : I → ℤ) (𝔭 : Set R) (p : ℕ) [Fact (Nat.Prime p)]
    (a : I → ℕ) (u : I → (W ⟶ Z)) : Prop :=
  ∀ (k : Type _) [Field k] [CharP k p] (x : Spec (CommRingCat.of k) ⟶ W.left),
    (∀ r ∈ 𝔭, (Spec.preimage (x ≫ W.hom)).hom r = 0) →
    Cancels m fun i ↦ Spec.map (CommRingCat.ofHom (iterateFrobenius k p (a i))) ≫ x ≫ (u i).left

/-- `c : W ⟶ Z` is a Galois covering with the finite group `Δ`, which acts on `W` through `a`:
every `a δ` is an automorphism of `W` over `Z`, `c` is surjective, and on points with values in
fields of characteristic `0`, `Δ` acts simply transitively on each fibre of `c`. -/
structure IsGaloisCovering {Δ : FiniteGrp.{0}} (a : Δ →* CategoryTheory.End W) where
  /-- Every `δ ∈ Δ` acts over `Z`: `a δ` followed by `c` is `c`. -/
  comp_eq (δ : Δ) : (a δ).asHom ≫ c = c
  /-- The morphism of schemes underlying `c` is surjective. -/
  surjective : Surjective c.left
  /-- Two points with values in a field of characteristic 0 and with the same image under `c` differ
  by a unique element of `Δ` (`c.1` and `(a δ).1` are the underlying morphisms of schemes). -/
  torsor (k : Type*) [Field k] [CharZero k] (x y : Spec (CommRingCat.of k) ⟶ W.left) :
      x ≫ c.1 = y ≫ c.1 → ∃! g : Δ, x ≫ (a g).asHom.1 = y

end New.Variety

end LocalTerms

/-!
## Additive Yoneda and objectwise exactness for functors to abelian groups

* `New.Variety.freeAb.desc`, `New.Variety.freeAb.hom_ext`: maps out of ℤ[Y] are natural families
  of elements indexed by the points of `Y`.
* `New.Variety.homReprEquiv`: the additive Yoneda lemma; it follows that ℤ[h_A] is projective.
* `New.Variety.exact_of_app`, `New.Variety.shortExact_of_app`: exactness is checked objectwise.
-/

section Representable

open CategoryTheory NatTrans Function FreeAbelianGroup AddCommGrpCat ShortComplex QuotientAddGroup

namespace New.Variety

variable {C : Type _} [Category C]
  {F M N : C ⥤ Ab} {Y : C ⥤ Type 1} (A : C) (α : M ⟶ N) (U : Subfunctor Y)

/-- For maps `s A : Y(A) → F(A)` natural in `A` (this is `h`), the morphism ℤ[Y] → F sending each
generator [y] to `s A y`. -/
def freeAb.desc (s : (A : C) → Y.obj A → F.obj A)
    (h : ∀ (A B : C) (f : A ⟶ B) (y : Y.obj A), s B (Y.map f y) = F.map f (s A y)) :
    freeAb.obj Y ⟶ F where
  app A := ofHom (FreeAbelianGroup.lift (s A))
  naturality := by aesop (add simp [freeAb, free])

@[simp]
lemma freeAb.desc_of (s : (A : C) → Y.obj A → F.obj A)
    (h : ∀ (A B : C) (f : A ⟶ B) (y : Y.obj A),
      s B ((ConcreteCategory.hom (Y.map f)) y) = (ConcreteCategory.hom (F.map f)) (s A y))
    (A : C) (y : Y.obj A) :
    desc (F := F) (Y := Y) s h A (FreeAbelianGroup.of y) = s A y := by
  -- at `A` the map is the lift of `s A` to the free abelian group
  show FreeAbelianGroup.lift (s A) (FreeAbelianGroup.of y) = s A y
  exact FreeAbelianGroup.lift_apply_of (s A) y

/-- Two maps ℤ[Y] → F agree if they agree on every generator [y]. -/
lemma freeAb.hom_ext {z z' : freeAb Y ⟶ F}
    (h : ∀ (A : C) (y : Y.obj A), z A (.of y) = z' A (.of y) := by tauto) : z = z' := by
  ext A : 2
  -- at `A` both maps are additive maps out of a free abelian group, so generators decide
  exact AddCommGrpCat.hom_ext (FreeAbelianGroup.lift_ext _ _ (h A))

@[simp]
lemma freeAb.map_of {E : C ⥤ Type 1} (u : E ⟶ Y) (A : C) (y : E.obj A) :
    freeAb.map u A (FreeAbelianGroup.of y) = FreeAbelianGroup.of (u A y) :=
  rfl

/-- The universal property of `freeAb`: for a functor `X` to sets and a functor `Y` to abelian
groups, the bijection between maps ℤ[X] → Y and maps X → Y. -/
abbrev freeAb.homEquiv :
    (X : C ⥤ Type _) → (Y : C ⥤ AddCommGrpCat) →
      (((Functor.whiskeringRight C (Type _) AddCommGrpCat).obj free).obj X ⟶ Y) ≃
        (X ⟶ ((Functor.whiskeringRight C AddCommGrpCat (Type _)).obj (forget AddCommGrpCat)).obj
          Y) := (adj.whiskerRight C).homEquiv

/-- The additive Yoneda lemma: maps ℤ[h_A] → F correspond to elements of F(A), compatibly with
addition; here h_A = Hom(A, −) is the functor represented by `A` (`New.Variety.reprBy`). -/
def homReprEquiv (F : C ⥤ Ab) : (freeAb (reprBy A) ⟶ F) ≃+ F A :=
  -- The universal property of `freeAb`, then the Yoneda lemma.
  ⟨(freeAb.homEquiv (reprBy A) F).trans uliftCoyonedaEquiv, by tauto⟩

/-- The additive Yoneda bijection is natural in the target: composing with `e : E ⟶ F` corresponds
to applying `e` at `A`. -/
private lemma homReprEquiv_comp {E : C ⥤ Ab} (f : freeAb (reprBy A) ⟶ E) (e : E ⟶ F) :
    homReprEquiv A F (f ≫ e) = e.app A (homReprEquiv A E f) :=
  rfl

/-- The free abelian group ℤ[h_A] on a represented functor is projective. -/
instance : Projective (freeAb (reprBy A)) where
  factors {E X} f e h_epi := by
    -- By `homReprEquiv` a lift of `f` along `e` is a preimage of `homReprEquiv A X f` under the
    -- value of `e` at `A`, which is surjective since `e` is an epimorphism.
    obtain ⟨x, hx⟩ :=
      (AddCommGrpCat.epi_iff_surjective (e.app A)).mp inferInstance (homReprEquiv A X f)
    refine ⟨(homReprEquiv A E).symm x, (homReprEquiv A X).injective ?_⟩
    rw [homReprEquiv_comp, AddEquiv.apply_symm_apply, hx]

/-- The value at `x ∈ N(A)` of a finite sum of maps `N ⟶ F` is the sum of their values. -/
lemma sum_app_apply {ι : Type*} {A : C} {x : N.obj A} [Fintype ι] {g : ι → (N ⟶ F)} :
    (∑ i : ι, g i) A x = ∑ i : ι, g i A x := by
  simp [← homAddEquiv_apply]

/-! ### Cokernels and relative chains -/

/-- The cokernel of a map α: M → N of functors to abelian groups, formed objectwise: A ↦
N(A)/α(M(A)). -/
def abCoker : C ⥤ Ab where
  obj A := AddCommGrpCat.of (N.obj A ⧸ (α A).hom.range)
  map f := ofHom (QuotientAddGroup.map _ _ (N.map f).hom (by simp [LE.le, ← naturality_apply]))

/-- The quotient map N → coker α, sending an element of N(A) to its class modulo α(M(A)). -/
def abCoker.π : N ⟶ abCoker α where
  app A := ofHom (QuotientAddGroup.mk' (α A).hom.range)

/-- The quotient map `abCoker.π α` is an epimorphism. -/
instance : Epi (abCoker.π α) where
  left_cancellation f g h := by
    ext A ⟨x⟩
    -- the class of `x` is the value of `abCoker.π α` at `x`
    exact ConcreteCategory.congr_hom (NatTrans.congr_app h A) x

/-- For a subfunctor `U` of a set-valued functor `Y`, the functor to abelian groups ℤ[Y]/ℤ[U], the
cokernel of the map ℤ[U] → ℤ[Y]. -/
def relFreeAb : C ⥤ Ab := abCoker (freeAb.map U.ι)

/-- For a subfunctor `U` of `Y`, the quotient morphism ℤ[Y] → ℤ[Y]/ℤ[U]. -/
def relFreeAb.π : freeAb Y ⟶ relFreeAb U := abCoker.π (freeAb.map U.ι)

/-- For `x ∈ Y(A)`, the class of the generator [x] in ℤ[Y(A)]/ℤ[U(A)]. -/
abbrev relFreeAb.mk {A : C} (x : Y.obj A) : (relFreeAb U).obj A := π U A (FreeAbelianGroup.of x)

variable {U α} {g : N ⟶ F}

/-- If the maps `α : M ⟶ N` and `g : N ⟶ F` of functors to abelian groups give an exact sequence
`M(A) → N(A) → F(A)` at every object `A`, then `α ≫ g = 0` (the witness `w`) and the short complex
`M ⟶ N ⟶ F` is exact. -/
lemma exact_of_app (h : ∀ A : C, Function.Exact (α A) (g A)) :
    ∃ w : α ≫ g = 0, ShortComplex.Exact ⟨α, g, w⟩ := by
  have h_zero : α ≫ g = 0 := by
    ext A x
    simpa using (h A).apply_apply_eq_zero x
  refine ⟨h_zero, ?_⟩
  -- The evaluation functors jointly reflect isomorphisms, so exactness is checked objectwise.
  -- (The reflection stays inside the call: its target `Ab` has a universe that cannot be named.)
  apply (JointlyReflectIsomorphisms.exact_iff (F := (evaluation C _).obj)
    ⟨NatIso.isIso_of_isIso_app⟩ _).mpr
  exact fun A ↦ (ab_exact_iff_function_exact _).mpr (h A)

/-- If at every object `A` the map `α A` is injective, the sequence `M(A) → N(A) → F(A)` is exact
in the middle and `g A` is surjective, then `α ≫ g = 0` (the witness `w`) and the short complex
`M ⟶ N ⟶ F` of functors to abelian groups is short exact. -/
lemma shortExact_of_app (h_inj : ∀ A : C, Function.Injective (α A))
    (h_exact : ∀ A : C, Function.Exact (α A) (g A)) (h_surj : ∀ A : C, Surjective (g A)) :
    ∃ w : α ≫ g = 0, ShortExact ⟨α, g, w⟩ := by
  obtain ⟨w, hw⟩ := exact_of_app h_exact
  have h_mono : Mono α := by grind [mono_iff_mono_app, AddCommGrpCat.mono_iff_injective]
  have h_epi : Epi g := by grind [epi_iff_epi_app, AddCommGrpCat.epi_iff_surjective]
  exact ⟨w, .mk' hw h_mono h_epi⟩

/-- For `f : N ⟶ F` with `α ≫ f = 0`, the induced morphism `coker α ⟶ F` through which `f`
factors. -/
def abCoker.desc (f : N ⟶ F) (h : α ≫ f = 0) : abCoker α ⟶ F where
  app A :=
    ofHom (QuotientAddGroup.lift (α A).hom.range (f A).hom (by simp [LE.le, ← comp_app_apply, h]))
  naturality := by aesop (add simp abCoker)

/-- For a subfunctor `U` of `Y`, two maps ℤ[Y]/ℤ[U] → F agree if they agree on the class of every
generator [x]. -/
lemma relFreeAb.hom_ext {f g : relFreeAb U ⟶ F}
    (h : ∀ (A : C) (x : Y.obj A), f A (mk U x) = g A (mk U x) := by tauto) :
    f = g := by
  -- the quotient map ℤ[Y] → ℤ[Y]/ℤ[U] is an epimorphism, so it suffices to compare both maps after
  -- it, on generators
  exact (cancel_epi (abCoker.π (freeAb.map U.ι))).mp (freeAb.hom_ext h)

end New.Variety

end Representable

end
