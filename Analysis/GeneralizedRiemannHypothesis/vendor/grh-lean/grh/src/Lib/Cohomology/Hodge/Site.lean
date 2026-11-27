import Lib.Cohomology.Hodge.CupProduct
import Lib.General.Geometry.EtaleCharts

/-!
# Hodge cohomology on algebras with free modules; universal points of charts

This file makes the pairs (A, M) of a k-algebra A and a free module M = A^ι
(`New.Variety.HodgeTest`) into a category and defines Hodge cohomology on it. A morphism is a
k-algebra map a together with an a-semilinear map of the modules. A functor of points N on
k-algebras is evaluated on the square-zero extension A ⊕ M, which sees tangent vectors.

* `New.Variety.HodgeTest.sqZeroExt`, `New.Variety.exteriorAlg`: the functors (A, M) ↦ A ⊕ M
  and (A, M) ↦ ⋀_A M.
* `New.Variety.HodgeH`: Hodge cohomology, Ext^q from N(A ⊕ M) to ⋀_A M in functors on pairs, with
  pull-back `New.Variety.HodgeH.map`, scaling `New.Variety.HodgeH.scale` and base change
  `New.Variety.HodgeH.baseChange`.
* `New.Variety.HodgeTest.existsUnique_lift_away`: maps out of (A[1/g], A[1/g]^ι) are the maps
  out of (A, A^ι) that invert g.
* `New.Variety.EtaleChart.univPoint`, `New.Variety.EtaleChart.exists_univPoint`: for a chart with
  ring R and d étale coordinates, the point through which the pair (R, R^d) represents
  (A, M) ↦ Hom(R, A ⊕ M).

Notions from other files:
* `New.Variety.HodgeTest`: a pair (A, M) as above, given by A and a finite ordered index set ι.
* `New.Variety.moduleCoeff`: a functor F from C to k-modules, regarded as a functor to abelian
  groups, so that it can serve as the coefficients of cohomology.
* `New.Variety.Comparison`: a functor φ : C' ⥤ C with a map φ ⋙ F ⟶ F' of coefficients; its `pull`
  along α : N' ⟶ φ ⋙ N maps Ext^n(N, F) to Ext^n(N', F').
* `New.Variety.EtaleChart`: a chart of X: a k-algebra R with finitely many étale coordinates and a
  point y in X(R) that embeds Spec R as an open subfunctor.
* `New.Variety.pointMap`: the map h_A → Y corresponding to a point y of Y(A) by the Yoneda lemma;
  here h_A = `New.Variety.reprBy A` is the functor of maps out of A.

## Relation to the literature

Known; see `Lib.Cohomology.Hodge.FixedPointFormula` for sources.
-/

noncomputable section

open CategoryTheory Functor Function Module ExteriorAlgebra TrivSqZeroExt CommAlgCat Pi

namespace New.Variety

set_option backward.isDefEq.respectTransparency false

variable {T T' M M' : Type} [CommRing T] [CommRing T'] [AddCommGroup M] [AddCommGroup M']
  [Module T M] [Module T' M'] {a : T →+* T'} (m : M →ₛₗ[a] M')

/-! ### Semilinear maps on exterior algebras -/

/-- For a ring map a: T → T' and an a-semilinear map m: M → M', the ring homomorphism ⋀_T M →
⋀_{T'} M' extending a and m. -/
def exteriorMap : ExteriorAlgebra T M →+* ExteriorAlgebra T' M' :=
  -- View the target as a `T`-algebra through `a`; then `ι ∘ m` is `T`-linear with squares zero.
  letI := Algebra.compHom (ExteriorAlgebra T' M') a
  (ExteriorAlgebra.lift T ⟨⟨(ι T' ∘ₛₗ m).toAddHom, (ι T' ∘ₛₗ m).map_smul'⟩, by simp⟩).toRingHom

@[simp]
lemma exteriorMap_iota (x : M) : exteriorMap m (ι T x) = ι T' (m x) := by
  simp [exteriorMap]

@[simp]
lemma exteriorMap_smul (r : T) (x : ExteriorAlgebra T M) :
    exteriorMap m (r • x) = a r • exteriorMap m x := by
  -- `exteriorMap m` is `T`-linear for the action of `T` on the target through `a`, and that
  -- action of `r` is the action of `a r`.
  let : Algebra T (ExteriorAlgebra T' M') := Algebra.compHom (ExteriorAlgebra T' M') a
  exact map_smul (ExteriorAlgebra.lift T _) r x

lemma exteriorMap_iotaMulti {d : ℕ} (v : Fin d → M) :
    exteriorMap m (ιMulti T d v) = ιMulti T' d (m ∘ v) := by
  simp [comp_def, ιMulti_apply, map_list_prod]

variable {k : Type} [CommRing k] (ι : Type) [Fintype ι] [LinearOrder ι]

/-- Pairs form a category: a morphism (A, A^ι) → (B, B^κ) is a pair f = ⟨f.1, f.2⟩ of a
k-algebra map f.1 : A → B and an f.1-semilinear map f.2 : A^ι → B^κ. -/
instance : Category (HodgeTest k) where
  Hom X Y :=
    Σ a : X.baseAlg ⟶ Y.baseAlg,
      (X.Index → X.baseAlg) →ₛₗ[(a.hom : X.baseAlg →+* Y.baseAlg)] Y.Index → Y.baseAlg
  id _ := ⟨𝟙 _, .id⟩
  comp f g := ⟨f.1 ≫ g.1, g.2.toAddHom.comp f.2.toAddHom, by simp⟩

private lemma HodgeTest.id_fst (P : HodgeTest k) : (𝟙 P : P ⟶ P).1 = 𝟙 P.baseAlg := rfl

private lemma HodgeTest.id_snd_apply (P : HodgeTest k) (x : P.Index → P.baseAlg) :
    (𝟙 P : P ⟶ P).2 x = x := rfl

private lemma HodgeTest.comp_fst {P Q R : HodgeTest k} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).1 = f.1 ≫ g.1 := rfl

/-- The semilinear map of a composite of morphisms of pairs is the composite of the semilinear
maps. -/
private lemma HodgeTest.comp_snd_apply {P Q R : HodgeTest k} (f : P ⟶ Q) (g : Q ⟶ R)
    (x : P.Index → P.baseAlg) : (f ≫ g).2 x = g.2 (f.2 x) := rfl

/-! ### Functors on pairs: square-zero extension and exterior algebra -/

/-- For a finite set ι, the functor A ↦ (A, A^ι) from k-algebras to pairs; an algebra map acts
coordinatewise on A^ι. -/
abbrev HodgeTest.withIndex : CommAlg k ⥤ HodgeTest k where
  obj A := ⟨A, ι⟩
  map a := ⟨a, { toFun x := a ∘ x, map_add' := by simp, map_smul' := by aesop }⟩

variable {ι} {A B : CommAlg k} (f : A ⟶ B) (a) (v : ι → M')

/-- For a ring map a: T → T' and vectors v_i in M', the a-semilinear map T^ι → M', (t_i) ↦ Σ
a(t_i) v_i. -/
def semilinearOfBasis : (ι → T) →ₛₗ[a] M' :=
  ∑ i : ι, LinearMap.toSpanSingleton T' M' (v i) ∘ₛₗ a.toSemilinearMap ∘ₛₗ LinearMap.proj i

@[simp]
lemma semilinearOfBasis_single (i : ι) : semilinearOfBasis a v (single i 1) = v i := by
  simp [semilinearOfBasis, single_apply]

/-- The functor sending a pair (A, M) to the square-zero extension A ⊕ M, as a k-algebra. -/
def HodgeTest.sqZeroExt : HodgeTest k ⥤ CommAlg k where
  obj X := CommAlgCat.of k (TrivSqZeroExt X.baseAlg (X.Index → X.baseAlg))
  map f :=
    ofHom
      { toFun x := (f.1 x.fst, f.2 x.snd)
        map_one' := by simp [TrivSqZeroExt.ext_iff]
        map_mul' := by simp [TrivSqZeroExt.ext_iff]
        map_zero' := by simp [TrivSqZeroExt.ext_iff]
        map_add' := by simp [TrivSqZeroExt.ext_iff]
        commutes' := by simp [TrivSqZeroExt.ext_iff, Algebra.algebraMap_eq_smul_one] }

/-- The functor sending a pair (A, M) to the exterior algebra ⋀_A M, as a k-algebra. -/
def exteriorAlg : HodgeTest k ⥤ AlgCat k where
  obj X := AlgCat.of k (ExteriorAlgebra X.baseAlg (X.Index → X.baseAlg))
  map f :=
    AlgCat.ofHom <|
      AlgHom.mk' (exteriorMap f.2) fun r x ↦ by simpa using exteriorMap_smul f.2 (r • 1) x
  map_id X := by
    ext x
    induction x using induction with
    | algebraMap r => simp [Algebra.algebraMap_eq_smul_one, HodgeTest.id_fst]
    | ι v => simp [HodgeTest.id_snd_apply]
    | mul x y hx hy => rw [map_mul, map_mul, hx, hy]
    | add x y hx hy => rw [_root_.map_add, _root_.map_add, hx, hy]
  map_comp f g := by
    ext x
    induction x using induction with
    | algebraMap r => simp [Algebra.algebraMap_eq_smul_one, HodgeTest.comp_fst]
    | ι v => simp [HodgeTest.comp_snd_apply]
    | mul x y hx hy => rw [map_mul, map_mul, hx, hy]
    | add x y hx hy => rw [_root_.map_add, _root_.map_add, hx, hy]

/-- The functor (A, M) ↦ ⋀_A M with values in abelian groups: the coefficient of Hodge
cohomology. -/
abbrev hodgeCoeff : AbFunctor (HodgeTest k) :=
  moduleCoeff (exteriorAlg ⋙ forget₂ (AlgCat k) (ModuleCat k))

open HodgeTest Comparison H IsLocalization
variable {N N' : AbFunctor (CommAlg k)} {q : ℕ} (t : k) {C : Type _} [Category C]
  {P Q : HodgeTest k}

/-- For a functor Φ to k-algebras with underlying functor F to abelian groups, the pairing F ⊗ F
→ F given by multiplication. -/
def _root_.CategoryTheory.Functor.mulPairing (Φ : C ⥤ AlgCat k) :
    let F := moduleCoeff (Φ ⋙ forget₂ (AlgCat k) (ModuleCat k))
    abTensor F F ⟶ F :=
  { app c := AddCommGrpCat.ofHom (LinearMap.mul' ℤ (ULift (Φ c))).toAddMonoidHom
    naturality _ _ f :=
      addCommGrp_tensor_hom_ext fun _ _ ↦ congrArg ULift.up (map_mul (Φ.map f).1 ..).symm }

/-- For a test (A, A^ι), the basis of the exterior algebra ⋀_A A^ι over A formed by the wedge
products of standard basis vectors. -/
abbrev HodgeTest.formBasis {c : HodgeTest k} :
    Basis (Finset c.Index) c.baseAlg (ExteriorAlgebra c.baseAlg (c.Index → c.baseAlg)) :=
  (basisFun c.baseAlg c.Index).ExteriorAlgebra

/-- Let f : P → Q be a morphism of pairs whose semilinear map f.2 sends the i-th standard basis
vector to the (j i)-th one, for an order embedding j. Then the induced map of exterior algebras
sends the basis form of a set s of indices (the wedge of its basis vectors in increasing order) to
the basis form of j(s). -/
lemma exteriorMap_formBasis (f : P ⟶ Q) (j : P.Index ↪o Q.Index)
    (h_basis : ∀ i : P.Index, f.2 (single i 1) = single (j i) 1) (s : Finset P.Index) :
    exteriorMap f.2 (P.formBasis s) = Q.formBasis (s.map j.toEmbedding) := by
  -- Both sides are wedges of basis vectors in increasing order; `j` keeps that order, so it turns
  -- the increasing enumeration of `s` into that of `s.map j`.
  have h_card : (s.map j.toEmbedding).card = s.card := Finset.card_map _
  have h_enum : (s.orderEmbOfFin rfl).trans j = (s.map j.toEmbedding).orderEmbOfFin h_card :=
    Finset.orderEmbOfFin_unique' h_card (by simp)
  simp [basis_apply_ofCard, h_basis, comp_def, ιMulti_family, Set.powersetCard.ofFinEmbEquiv,
    ιMulti_apply, map_list_prod, ← h_enum]

private lemma HodgeTest.withIndex_map_snd_single (i : ι) :
    ((withIndex ι).map f).2 (single i 1) = single i 1 := by
  show f ∘ single i 1 = single i 1
  grind

/-- Let f : A → B be a map of k-algebras and x a form in ⋀_A A^ι. Under the map ⋀_A A^ι → ⋀_B B^ι
induced by f, the coordinate at a set s of indices in the basis of wedge products of standard basis
vectors (`formBasis`) is f applied to the coordinate of x at s. -/
lemma HodgeTest.repr_withIndex_map (x :
    ExteriorAlgebra ((withIndex ι).obj A).baseAlg
      (((withIndex ι).obj A).Index → ((withIndex ι).obj A).baseAlg))
    (s : Finset ((withIndex ι).obj B).Index) :
    formBasis.repr (exteriorMap ((withIndex ι).map f).2 x) s = f (formBasis.repr x s) := by
  -- Expand `x` in the basis; the map is `f`-semilinear and fixes the basis forms
  -- (`exteriorMap_formBasis`).
  have h_form (t : Finset ι) : exteriorMap ((withIndex ι).map f).2 (formBasis t) = formBasis t := by
    simpa using
      exteriorMap_formBasis ((withIndex ι).map f) (.refl _) (withIndex_map_snd_single f) t
  conv_lhs => rw [← formBasis.sum_repr x, _root_.map_sum]
  simp [h_form, Finsupp.single_apply]

/-- For a pair C = (A, M), the k-algebra projection A ⊕ M → A, (a, m) ↦ a, from the square-zero
extension. -/
abbrev HodgeTest.baseProj (C : HodgeTest k) : sqZeroExt C ⟶ C.baseAlg :=
  ofHom (fstHom k C.baseAlg (C.Index → C.baseAlg))

/-- Two morphisms of pairs P → Q are equal if their algebra maps f.1 and g.1 are equal and their
semilinear maps f.2 and g.2 agree on the standard basis vectors of P. -/
lemma HodgeTest.hom_ext {f g : P ⟶ Q} (h_ring : f.1 = g.1)
    (h_basis : ∀ i : P.Index, f.2 (single i 1) = g.2 (single i 1)) :
    f = g := by
  -- Once the algebra maps are identified, the two semilinear maps agree on a basis.
  obtain ⟨a, m⟩ := f
  obtain ⟨a', m'⟩ := g
  obtain rfl : a = a' := h_ring
  obtain rfl : m = m' := (basisFun P.baseAlg P.Index).ext fun i ↦ by simpa using h_basis i
  rfl

private lemma HodgeTest.snd_sqZeroExt_map_apply (f : P ⟶ Q) (x : sqZeroExt.obj P) :
    (sqZeroExt.map f x).snd = f.2 x.snd := rfl

private lemma HodgeTest.baseProj_apply (C : HodgeTest k) (x : sqZeroExt.obj C) :
    C.baseProj x = x.fst := rfl

private lemma HodgeTest.sqZeroExt_map_comp_baseProj (f : P ⟶ Q) :
    sqZeroExt.map f ≫ Q.baseProj = P.baseProj ≫ f.1 := rfl

/-! ### Hodge cohomology, scaling, localisation and base change -/

/-- Hodge cohomology: for a functor N from k-algebras to abelian groups, Ext^q from (A, M) ↦ N(A
⊕ M) to (A, M) ↦ ⋀_A M, in functors on pairs. -/
abbrev HodgeH (N : CommAlg k ⥤ AddCommGrpCat) (q : ℕ) : Type 2 :=
  H (HodgeTest.sqZeroExt (k := k) ⋙ N) hodgeCoeff q

/-- For α: N' → N, the k-linear pull-back from the degree-q Hodge cohomology of N to that of N'. -/
abbrev HodgeH.map (α : N' ⟶ N) : HodgeH N q →ₗ[k] HodgeH N' q :=
  mapₗ k hodgeCoeff (whiskerLeft HodgeTest.sqZeroExt α) q

/-- For t in k and a functor F on pairs, the natural endomorphism of F induced on each pair (A, M)
by the identity of A and multiplication by t on M. -/
def HodgeTest.scaleModule (F : HodgeTest k ⥤ C) : F ⟶ F :=
  whiskerRight
    ({ app _ := ⟨𝟙 _, t • LinearMap.id⟩
       naturality X Y f := by
         refine hom_ext rfl fun i ↦ ?_
         -- `f.2` is semilinear over `f.1`, a map of `k`-algebras, which fixes `t • 1`.
         have h_smul : f.2 ((t • (1 : X.baseAlg)) • single i 1) = f.1 (t • 1) • f.2 (single i 1) :=
           f.2.map_smulₛₗ (t • 1) (single i 1)
         simpa [comp_snd_apply] using h_smul.symm } :
      𝟭 (HodgeTest k) ⟶ 𝟭 (HodgeTest k))
    F

/-- For t ∈ k, the endomorphism of the degree-q Hodge cohomology of N induced by (a, m) ↦ (a, tm) on
A ⊕ M. -/
abbrev HodgeH.scale : HodgeH N q →+ HodgeH N q :=
  H.map hodgeCoeff (HodgeTest.scaleModule t (HodgeTest.sqZeroExt ⋙ N)) q

/-- Objects of `HodgeTest k` are pairs (A, A^ι): a commutative k-algebra A with the free module on a
finite index set ι, and `withIndex ι` sends A to (A, A^ι). Let f : A → B be a map of k-algebras that
is a localisation at the powers of g. Then any morphism of pairs φ : (A, A^ι) → Z whose algebra map
φ.1 sends g to a unit factors uniquely through the morphism (A, A^ι) → (B, B^ι) induced by f. -/
lemma HodgeTest.existsUnique_lift_away (g : A) (h_loc : (Submonoid.powers g).IsLocalizationMap f)
    (Z : HodgeTest k) (φ : (withIndex ι).obj A ⟶ Z) (hg : IsUnit (φ.1 g)) :
    ∃! y : (withIndex ι).obj B ⟶ Z, (withIndex ι).map f ≫ y = φ := by
  -- A morphism out of `(B, B^ι)` is an algebra map with the images of the basis vectors. The
  -- algebra map is fixed by the universal property of the localisation, and `f` preserves the
  -- basis (`withIndex_map_snd_single`).
  let : Algebra A B := f.hom.toAlgebra
  have : Away g B := ⟨h_loc⟩
  -- The lift: the algebra map `B → Z` given by the localisation, and on the basis
  -- `single i 1 ↦ φ.2 (single i 1)`.
  let lift : (withIndex ι).obj B ⟶ Z :=
    ⟨ofHom (Away.liftAlgHom g hg), semilinearOfBasis _ fun i ↦ φ.2 (single i 1)⟩
  have h_lift : (withIndex ι).map f ≫ lift = φ :=
    hom_ext (Hom.ext (AlgHom.ext fun x ↦ Away.lift_eq g hg x)) fun i ↦ by
      rw [comp_snd_apply, withIndex_map_snd_single f i]
      exact semilinearOfBasis_single _ _ i
  have h_injective : Injective fun y : (withIndex ι).obj B ⟶ Z ↦ (withIndex ι).map f ≫ y := by
    intro y y' h_eq
    refine hom_ext ?_ fun i ↦ ?_
    · -- The algebra maps agree after the localisation map `f`, hence everywhere.
      have h_fst : f ≫ y.1 = f ≫ y'.1 := congrArg Sigma.fst h_eq
      exact Hom.ext (algHom_ext (.powers g) (congrArg Hom.hom h_fst))
    · -- On the basis vectors, which `f` sends to basis vectors.
      have h_snd : ((withIndex ι).map f ≫ y).2 (single i 1) =
          ((withIndex ι).map f ≫ y').2 (single i 1) :=
        congrArg (fun h : (withIndex ι).obj A ⟶ Z ↦ h.2 (single i 1)) h_eq
      rwa [comp_snd_apply, comp_snd_apply, withIndex_map_snd_single f i] at h_snd
  exact h_injective.existsUnique_of_mem_range ⟨lift, h_lift⟩

variable {E : Type} [CommRing E] [Algebra E k] {N N' : AbFunctor (CommAlg E)}

/-- For an E-algebra k, the comparison from Hodge coefficients over E to those over k, given by
restriction of scalars on pairs and the identity of ⋀_A M. -/
def HodgeTest.baseComparison : Comparison (hodgeCoeff (k := E)) (hodgeCoeff (k := k)) where
  functor :=
          { obj X := ⟨(restrictAlg E k).obj X.baseAlg, X.Index⟩
            map f := ⟨(restrictAlg E k).map f.1, f.2⟩ }
  coeffHom := by apply 𝟙

/-- Base change: for an E-algebra k, the additive map from the Hodge cohomology over E of N to
that over k of N restricted to k-algebras. -/
def HodgeH.baseChange : HodgeH N q →+ HodgeH (restrictAlg E k ⋙ N) q :=
  baseComparison.pull (whiskerRight (𝟙 (HodgeTest.sqZeroExt ⋙ restrictAlg E k)) N) q

@[simp]
lemma HodgeH.baseChange_map (α : N' ⟶ N) (x : HodgeH N q) :
    baseChange (k := k) (map α x) = map (whiskerLeft (restrictAlg E k) α) x.baseChange :=
  -- Both paths restrict `α` along `sqZeroExt` and the restriction of scalars; the square of
  -- whiskerings that `map_pull_eq_pull_map` needs commutes, its other sides being identities.
  (map_pull_eq_pull_map (by aesop) q x).symm

variable {k : Type} [Field k] {d : ℕ} {X : CommAlg k ⥤ Type 1} (a : EtaleChart (k := k) d X)

/-! ### The universal point of a chart -/

/-- Étale maps lift uniquely along square-zero extensions, so exactly one k-algebra map u :
a.coordRing → a.coordRing ⊕ a.coordRing^d lifts the identity and sends each coordinate x_i to (x_i,
e_i). -/
private lemma EtaleChart.existsUnique_univPoint :
    ∃! u : a.coordRing ⟶ HodgeTest.sqZeroExt.obj ⟨a.coordRing, Fin d⟩,
      u ≫ baseProj ⟨a.coordRing, Fin d⟩ = 𝟙 a.coordRing ∧
        ∀ i : Fin d, u (a.coordinate i) = (a.coordinate i, single i 1) :=
  etale_polyEval_iff.1 a.etale (baseProj ⟨a.coordRing, Fin d⟩) fst_surjective_and_kerIdeal_sq_eq_bot
    (𝟙 _)
    (fun i ↦ (a.coordinate i, single i 1)) fun _ ↦ rfl

/-- The universal point of an étale chart a with ring R = a.coordRing and d coordinates x_i: the
k-algebra map u : R → R ⊕ R^d that lifts the identity of R and sends each x_i to (x_i, e_i), where
e_i is the i-th basis vector of R^d. These two conditions determine u. -/
def EtaleChart.univPoint : a.coordRing ⟶ HodgeTest.sqZeroExt.obj ⟨a.coordRing, Fin d⟩ :=
  (EtaleChart.existsUnique_univPoint a).exists.choose

private lemma EtaleChart.univPoint_comp_baseProj :
    a.univPoint ≫ baseProj ⟨a.coordRing, Fin d⟩ = 𝟙 a.coordRing :=
  (EtaleChart.existsUnique_univPoint a).exists.choose_spec.left

private lemma EtaleChart.univPoint_coordinate (i : Fin d) :
    a.univPoint (a.coordinate i) = (a.coordinate i, single i 1) :=
  (EtaleChart.existsUnique_univPoint a).exists.choose_spec.right i

lemma EtaleChart.leftInverse_fst_univPoint : LeftInverse fst a.univPoint :=
  -- The projection `baseProj` takes the first part, and after u it is the identity.
  fun r ↦ ConcreteCategory.congr_hom a.univPoint_comp_baseProj r

/-- Through the universal point u of a chart with ring R and d coordinates, the pair (R, R^d)
represents c = (A, M) ↦ (k-algebra maps R → A ⊕ M): at each pair c, `pointMap`, which sends a
morphism of pairs f : (R, R^d) → c to u followed by `sqZeroExt.map f`, is a bijection. -/
lemma EtaleChart.bijective_pointMap_univPoint (c : HodgeTest k) :
    Bijective (pointMap (Y := HodgeTest.sqZeroExt ⋙ reprBy a.coordRing) ⟨a.univPoint⟩ c) := by
  -- A map s : R → A ⊕ M is determined by its first part and by the M-parts of the s (x_i), since
  -- étale maps lift uniquely along A ⊕ M → A. These data are a morphism of pairs (R, R^d) → c.
  let inv (s : a.coordRing ⟶ sqZeroExt.obj c) : (⟨a.coordRing, Fin d⟩ : HodgeTest k) ⟶ c :=
    ⟨s ≫ c.baseProj, semilinearOfBasis _ fun i ↦ (s (a.coordinate i)).snd⟩
  -- The algebra map of f is recovered: naturality of the projection, then u followed by the
  -- projection is the identity.
  have h_base (f : ⟨a.coordRing, Fin d⟩ ⟶ c) :
    (a.univPoint ≫ sqZeroExt.map f) ≫ c.baseProj = f.1 := by
    simp [sqZeroExt_map_comp_baseProj, reassoc_of% a.univPoint_comp_baseProj]
  have h_left (f : ⟨a.coordRing, Fin d⟩ ⟶ c) : inv (a.univPoint ≫ sqZeroExt.map f) = f := by
    refine hom_ext (h_base f) fun i ↦ ?_
    -- The basis vector e_i is the M-part of the image of x_i.
    simp [inv, EtaleChart.univPoint_coordinate a i, snd_sqZeroExt_map_apply]
  have h_right (s : a.coordRing ⟶ sqZeroExt.obj c) : a.univPoint ≫ sqZeroExt.map (inv s) = s := by
    -- Both sides lift s followed by the projection, and u sends x_i to (x_i, e_i).
    refine a.lift_unique (π := c.baseProj) fst_surjective_and_kerIdeal_sq_eq_bot (h_base (inv s))
      fun i ↦ ?_
    calc (a.univPoint ≫ sqZeroExt.map (inv s)) (a.coordinate i)
        = sqZeroExt.map (inv s) (a.coordinate i, single i 1) :=
          congrArg (sqZeroExt.map (inv s)) (a.univPoint_coordinate i)
      _ = s (a.coordinate i) := TrivSqZeroExt.ext rfl (semilinearOfBasis_single _ _ i)
  -- `pointMap` sends f to u followed by `sqZeroExt.map f`.
  exact bijective_iff_has_inverse.2 ⟨fun s ↦ ⟨inv s.down⟩,
    fun f ↦ ULift.down_injective (h_left f.down), fun s ↦ ULift.down_injective (h_right s.down)⟩

/-- A chart with ring R and d coordinates has a section u of `fst : R ⊕ R^d → R` through which
(R, R^d) represents (A, M) ↦ (k-algebra maps R → A ⊕ M), namely `EtaleChart.univPoint`. -/
lemma EtaleChart.exists_univPoint :
    ∃ u : a.coordRing ⟶ HodgeTest.sqZeroExt ⟨a.coordRing, Fin d⟩,
      LeftInverse fst u ∧
        AllBijective fun c : HodgeTest k ↦
          pointMap (Y := HodgeTest.sqZeroExt ⋙ reprBy a.coordRing) ⟨u⟩ c :=
  ⟨a.univPoint, a.leftInverse_fst_univPoint, a.bijective_pointMap_univPoint⟩

/-- Over a field k of characteristic zero, the values of a functor F to k-vector spaces are flat
as abelian groups: k is flat over ℤ, and every k-vector space is flat over k. -/
instance [CharZero k] (F : C ⥤ ModuleCat k) : HasFlatValues (moduleCoeff (k := k) (C := C) F) :=
  ⟨fun c : C ↦ Module.Flat.trans ℤ k (ULift (F.obj c))⟩

end New.Variety

end
