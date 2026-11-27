import Lib.Cohomology.Hodge.Site
import Lib.PadicComparison.Descent.AlmostDescent

/-!
# Vanishing of Hodge cohomology with supports below the depth, and Zariski descent

* `New.Variety.depth_vanishing`: the abstract induction on a regular sequence.
* `New.Variety.DepthVanishing.subsingleton_of_isWeaklyRegular`: for a pair `c = (A, M)`, the
  cohomology of `h_c` relative to the locus `New.Variety.someUnitLocus f` where some `f i` is a unit
  vanishes below the depth of the ideal `(f)`.
* `New.Variety.hodge_vanishing_along_diagonal`: on a chart with étale coordinates `x_1, …, x_{2d}`
  and the ideal of the `x_i - x_{d+i}` (the diagonal), it vanishes in degrees below `d`.
* `New.Variety.isCohomEquiv_someUnitLocus_of_span_eq_top`,
  `New.Variety.hasZariskiDescent_hodgeCoeff`: for the unit ideal it vanishes in all degrees, which
  gives Zariski descent for Hodge cohomology.

`New.Variety.H N F n` is `Ext^n(N, F)` in functors to abelian groups, `New.Variety.relFreeAb U` is
`ℤ[V] / ℤ[U]` for `U ⊆ V`, and `New.Variety.hodgeCoeff` is the coefficient functor `(A, M) ↦ ⋀_A M`.

Notions from other files:
* `New.Variety.HodgeTest`: a test for Hodge cohomology over k, namely a commutative k-algebra A and
  a finite index set ι, standing for the pair (A, M) with M = A^ι.
* `New.Variety.reprBy`: the functor h_A = Hom(A,−) represented by the object A.

## Relation to the literature

Known; see `Lib.Cohomology.Hodge.FixedPointFormula` for sources.
-/

open CategoryTheory Function TensorProduct Ideal RingTheory.Sequence MvPolynomial Functor RingHom
  IsLocalization.Away ConcreteCategory TrivSqZeroExt IsLocalizedModule LinearMap Localization Fin

/-- Let `N` be an `R`-module, `B` an `R`-algebra and `a ∈ R`. The map `N ⊗ B → N ⊗ B[1/a]`, induced
by the localization of `B` at the image of `a`, becomes bijective after tensoring with `R[1/a]`. -/
lemma bijective_lTensor_lTensor_toAlgHom_away {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
    (N : Type*) [AddCommGroup N] [Module R N] (a : R) :
    Bijective
      (((IsScalarTower.toAlgHom R B (Away (algebraMap R B a))).toLinearMap.lTensor N).lTensor
        (Away a)) := by
  -- `F : N ⊗ B → R[1/a] ⊗ (N ⊗ B[1/a])` is a localization at `a`, and the map in question is
  -- its extension to `R[1/a] ⊗ (N ⊗ B)`.
  let g : B →ₗ[R] Away (algebraMap R B a) := (IsScalarTower.toAlgHom R B _).toLinearMap
  let F : N ⊗[R] B →ₗ[R] Away a ⊗[R] (N ⊗[R] Away (algebraMap R B a)) :=
    (TensorProduct.assoc R (Away a) N _).toLinearMap ∘ₗ
      TensorProduct.map (TensorProduct.mk R (Away a) N 1) g
  have h_F_eq :
      (F.liftBaseChange (Away a)).restrictScalars R = (g.lTensor N).lTensor (Away a) := by
    ext
    simp [F, smul_tmul']
  rw [← h_F_eq, LinearMap.coe_restrictScalars]
  exact isBaseChange (.powers a) _ F

namespace New.Variety

variable {A k ι : Type} [CommRing A] [CommRing k] {c : HodgeTest k} {n d : ℕ} [Fintype ι]

/-- For a pair `c = (A, M)` and a family `(f_i)` in `A`, the subfunctor of h_c of the morphisms
`y : c ⟶ X` whose ring map `A → X.baseAlg` sends some `f_i` to a unit. -/
def someUnitLocus (f : ι → c.baseAlg) : Subfunctor (reprBy c) where
  obj _ := {y | ∃ i : ι, IsUnit (y.1.1 (f i))}
  map a _ := Exists.imp fun _ ↦ IsUnit.map a.1.1

/-- Depth vanishing. Let `H n` assign to each `A`-module an `A`-module such that every element of
every `H n M` is killed by a power of each element of `I`, and such that an `M`-regular `r` is
regular on `H n M` once `H m (M / r M)` vanishes for all `m < n`. If `I` contains a weakly
`M`-regular sequence `l` longer than `n`, then `H n M = 0`. -/
lemma depth_vanishing (H : ℕ → ModuleCat A → ModuleCat A) {I : Ideal A} {l : List A}
    (h_torsion : ∀ (n : ℕ) (M : ModuleCat A) (x : H n M), I ≤ (torsionOf A (H n M) x).radical)
    (h_regular : ∀ (n : ℕ) (M : ModuleCat A) (r : A), IsSMulRegular M r →
      (∀ m < n, Subsingleton (H m (ModuleCat.of A (QuotSMulTop r M)))) → IsSMulRegular (H n M) r)
    (h_le : ofList l ≤ I) (hn : n < l.length) (M : ModuleCat A) (h_weak : IsWeaklyRegular M l) :
    Subsingleton (H n M) := by
  induction l generalizing M n with
  | nil => simp at hn
  | cons r l ih =>
    -- By induction `H m (M / r)` vanishes for `m < n`, so `r` is regular on `H n M`;
    -- but `r ∈ I`, so a power of `r` kills each class.
    obtain ⟨hr_mem, hl_le⟩ : r ∈ I ∧ ofList l ≤ I := by simpa [span_singleton_le_iff_mem] using h_le
    obtain ⟨hr_reg, hl_reg⟩ := (isWeaklyRegular_cons_iff M r l).1 h_weak
    have h_quot : ∀ m < n, Subsingleton (H m (ModuleCat.of A (QuotSMulTop r M))) :=
      fun m hm ↦ ih hl_le (by grind) _ hl_reg
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨j, hj⟩ : ∃ j : ℕ, r ^ j ∈ torsionOf A (H n M) x := h_torsion n M x hr_mem
    exact ((h_regular n M r hr_reg h_quot).pow j).right_eq_zero_of_smul hj

/-- The flat algebras over a commutative ring `R`, as a property of commutative `R`-algebras. -/
private abbrev flatAlgebras (R : Type) [CommRing R] : ObjectProperty (CommAlg R) :=
  fun B ↦ Module.Flat R B

/-- For a flat `R`-algebra `B` and `b ∈ B`, the maps from `B` to flat `R`-algebras that send `b`
to a unit. -/
private def flatUnitLocus {R : Type} [CommRing R] (B : (flatAlgebras R).FullSubcategory)
    (b : B.1) : Subfunctor (reprBy B) where
  obj _ := {x | IsUnit (x.1.1 b)}
  map a _ := .map a.1.hom

/-- The localization `B[1/b]` of a flat `R`-algebra `B`, again a flat `R`-algebra. -/
private abbrev flatAway {R : Type} [CommRing R] (B : (flatAlgebras R).FullSubcategory) (b : B.1) :
    (flatAlgebras R).FullSubcategory :=
  ⟨.of _ (Away b), B.2.trans ..⟩

/-- The localization map `B → B[1/b]`, as a member of `flatUnitLocus B b`. -/
private abbrev flatToAway {R : Type} [CommRing R] (B : (flatAlgebras R).FullSubcategory) (b : B.1) :
    (flatUnitLocus B b).toFunctor.obj (flatAway B b) :=
  ⟨⟨⟨B.1.toAway b⟩⟩, algebraMap_isUnit b⟩

/-- `B[1/b]` represents the maps from a flat `R`-algebra `B` that send `b` to a unit: for every
flat `D`, composing with `B → B[1/b]` maps `Hom(B[1/b], D)` bijectively onto them. -/
private lemma bijective_pointMap_flatToAway {R : Type} [CommRing R]
    (B : (flatAlgebras R).FullSubcategory) (b : B.1) (D : (flatAlgebras R).FullSubcategory) :
    Bijective ((pointMap (flatToAway B b)).app D) := by
  refine pointMap_bijective_of_existsUnique _ _ (fun D' y hy ↦ ?_) D
  -- the lift of `y` to `B[1/b]`, unique by the universal property of the localization
  refine ⟨⟨ofHom (liftAlgHom _ hy)⟩, by ext; exact lift_eq b hy _, ?_⟩
  rintro χ rfl
  ext
  simp [Algebra.algHom]

/-- For a pair `c`, consider the comma category of pairs `(S, s)` of a type `S` and a map
`s : S → (c ⟶ d)` to the points of h_c at some `d`. This is the subfunctor of `(S, s) ↦ S` of the
`t ∈ S` whose ring map `s t` sends `g` to a unit. -/
private def commaUnitLocus (g : c.baseAlg) :
    Subfunctor (Comma.fst (𝟭 Type) (coyoneda.obj ⟨c⟩) ⋙ uliftFunctor) where
  obj X := {t | IsUnit ((X.hom t.1).1 g)}
  map a _ h := congr(IsUnit (($a.w _).1 g)).mpr (h.map a.right.1.1)

/-- Let `Q` be a closed class (it holds for zero functors and has two-out-of-three along short
exact sequences whose first term lies in `Q`) of functors on the comma category of pairs `(S, s)`,
and let `Q` contain `ℤ[commaUnitLocus g]` for every `g`. Then `Q` contains `relFreeAb` of the
union of the loci `commaUnitLocus (f i)`. -/
private lemma IsClosedClass.relFreeAb_iSup_commaUnitLocus {f : ι → c.baseAlg}
    (Q : (Comma (𝟭 Type) (coyoneda.obj ⟨c⟩) ⥤ Ab.{1}) → Prop) (hQ : IsClosedClass Q)
    (h_freeAb : ∀ g : c.baseAlg, Q (freeAb.obj (commaUnitLocus g).toFunctor)) :
    Q (relFreeAb (iSup (commaUnitLocus ∘ f))) := by
  have h_inf (g g' : c.baseAlg) :
      commaUnitLocus (g * g') = commaUnitLocus g ⊓ commaUnitLocus g' := by
    aesop (add simp commaUnitLocus)
  have h_range_inf : ∀ W ∈ Set.range (commaUnitLocus (c := c)),
      ∀ W' ∈ Set.range (commaUnitLocus (c := c)), W ⊓ W' ∈ Set.range (commaUnitLocus (c := c)) := by
    rintro _ ⟨g, rfl⟩ _ ⟨g', rfl⟩
    exact ⟨g * g', h_inf g g'⟩
  have h_union : Q (freeAb.obj (iSup (commaUnitLocus ∘ f)).toFunctor) :=
    hQ.freeAb_iSup (.range commaUnitLocus) (Set.forall_mem_range.2 h_freeAb) h_range_inf (by simp)
  have h_one (X : Comma (𝟭 Type) (coyoneda.obj ⟨c⟩)) : ∀ t, t ∈ (commaUnitLocus 1).obj X := by
    simp [commaUnitLocus]
  have h_ambient : Q (freeAb.obj (Comma.fst (𝟭 Type) (coyoneda.obj ⟨c⟩) ⋙ uliftFunctor)) :=
    hQ.freeAb_of_bijective (commaUnitLocus 1).ι
      (fun X ↦ (Equiv.subtypeUnivEquiv (h_one X)).bijective)
      (h_freeAb 1)
  obtain ⟨_, h_exact⟩ := relFreeAb.shortExact (iSup (commaUnitLocus ∘ f))
  obtain ⟨-, h_two_of_three⟩ := hQ
  exact (h_two_of_three _ h_exact h_union).mp h_ambient

/-- Depth vanishing for Hodge coefficients. Let `c = (A, M)` be a pair, `f` a finite family in `A`
and `l` a weakly `A`-regular sequence in the ideal generated by the `f i`. Then the cohomology of
h_c with coefficients `⋀ M`, relative to the locus where some `f i` is a unit, vanishes in every
degree `n` less than the length of `l`. -/
lemma DepthVanishing.subsingleton_of_isWeaklyRegular {f : ι → c.baseAlg} (l : List c.baseAlg)
    (hl_le : ofList l ≤ span (Set.range f)) (hn : n < l.length)
    (h_reg : IsWeaklyRegular c.baseAlg l) :
    Subsingleton (H (relFreeAb (someUnitLocus f)) hodgeCoeff n) := by
  -- Compare with the flat `A`-algebras `B`, `A = c.baseAlg`, along `B ↦ (B, B ^ c.Index)`: the
  -- group is a product of copies of local cohomology of `A` along `(f)`, which vanishes below the
  -- depth.
  -- To treat both sites at once, use sets `S` with a family `S → (c ⟶ d)` of points of `h_c`:
  -- `L φ x s` sends `B` to the family `(x ⟶ B) → (c ⟶ φ B)` given by `s`.
  let L {C : Type 1} [Category.{0} C] (φ : C ⥤ HodgeTest k) (x : C) (s : c ⟶ φ.obj x) :
      C ⥤ Comma (𝟭 Type) (coyoneda.obj ⟨c⟩) :=
    { obj B := ⟨x ⟶ B, φ.obj B, ↾fun t ↦ s ≫ φ.map t⟩
      map a := .mk (↾fun t ↦ t ≫ a) (φ.map a) }
  let ψ : HodgeTest k ⥤ Comma (𝟭 Type) (coyoneda.obj ⟨c⟩) := L (𝟭 (HodgeTest k)) c (𝟙 c)
  let P : ObjectProperty (CommAlg c.baseAlg) := flatAlgebras c.baseAlg
  -- `V` is the locus where some `f i` is a unit.
  let V : Subfunctor (Comma.fst (𝟭 Type) (coyoneda.obj ⟨c⟩) ⋙ uliftFunctor) :=
    iSup (commaUnitLocus ∘ f)
  -- The comparison `γ` along `B ↦ (B, B ^ c.Index)` reads `⋀ (B ^ c.Index)` in its standard basis,
  -- as a product of copies of `A ⊗ B`.
  let γ :
      Comparison hodgeCoeff
        (piAbFunctor fun _ ↦ moduleCoeff (asModules P.ι ⋙ tensorWith c.baseAlg _)) :=
    ⟨P.ι ⋙ restrictAlg k _ ⋙ HodgeTest.withIndex c.Index,
      fun B ↦ (AddEquiv.ulift.trans
        ((Pi.basisFun B.1 c.Index).ExteriorAlgebra.equivFun.toAddEquiv.trans
          (.piCongrRight fun _ ↦ (TensorProduct.lid c.baseAlg _).symm.toAddEquiv.trans
            (.symm .ulift)))).toAddCommGrpIso.hom,
      fun B D a ↦ by
        ext
        congrm (⟨1 ⊗ₜ $(HodgeTest.repr_withIndex_map a.1 _ ·)⟩)⟩
  let ψ' : P.FullSubcategory ⥤ Comma (𝟭 Type) (coyoneda.obj ⟨c⟩) :=
    L γ.functor ⟨.of _ c.baseAlg, .self⟩ ⟨ofHom ⟨.id _, by tauto⟩, .id⟩
  let η : ψ' ⟶ γ.functor ⋙ ψ := .mk fun B ↦ .mk (ψ'.obj B).hom (𝟙 _)
  -- `coeffAway N a`: the coefficients `B ↦ A[1/a] ⊗ N ⊗ B` on flat algebras.
  let coeffAway (N : ModuleCat c.baseAlg) (a : c.baseAlg) : AbFunctor P.FullSubcategory :=
    moduleCoeff ((asModules P.ι ⋙ tensorWith c.baseAlg N) ⋙ tensorWith c.baseAlg (Away a))
  -- `HN n N`: cohomology of `(h_A, V)` on flat algebras with coefficients `B ↦ N ⊗ B`.
  let HN (n : ℕ) (N : ModuleCat c.baseAlg) : ModuleCat c.baseAlg := ModuleCat.of c.baseAlg
    (H (ψ' ⋙ relFreeAb V) (moduleCoeff (asModules P.ι ⋙ tensorWith c.baseAlg N)) n)
  have hasFlatBaseChange_V : HasFlatBaseChange (ψ' ⋙ relFreeAb V) :=
    -- it holds on each `ℤ[commaUnitLocus g]`, which is representable, and passes to `relFreeAb V`
    -- (`(… :)`: the term is elaborated from its arguments, then compared with the predicate)
    IsClosedClass.relFreeAb_iSup_commaUnitLocus (f := f) _
      (HasFlatBaseChange.isClosedClass.comap (restrictAlong ψ')) fun g ↦
      (HasFlatBaseChange.isClosedClass.freeAb_of_bijective _
        (bijective_pointMap_flatToAway ⟨.of .., .self⟩ g) (hasFlatBaseChange_freeAb_reprBy _) :)
  -- For the coefficients `B ↦ A[1/a] ⊗ N ⊗ B` the locus of `a` is dense: they do not change
  -- from `B` to `B[1/a]`, which represents the locus over `B`.
  have isCohomDense_unitLocus (N : ModuleCat c.baseAlg) (a : c.baseAlg) :
      IsCohomDense (coeffAway N a) ((commaUnitLocus a).whisker ψ') := by
    rintro B ⟨⟨y⟩⟩
    -- the only point of `h_A` at `B` is the structure map `A → B`
    obtain rfl : y = structureMap := by ext
    exact (Comparison.isBijective_of_repr _ (bijective_pointMap_flatToAway B _)
      (ULift.map_bijective.2 (bijective_lTensor_lTensor_toAlgHom_away (B := B.obj) N a))).eqv
  -- So `HN n N` localized at `f i` is zero, by flat base change: a power of `f i` kills each class.
  have le_radical_torsionOf (n : ℕ) (N : ModuleCat c.baseAlg) (x : HN n N) :
      span (.range f) ≤ (torsionOf c.baseAlg (HN n N) x).radical := by
    refine span_le.2 (Set.range_subset_iff.2 fun i ↦ ?_)
    -- a power of `f i` kills `x` once `1 ⊗ x` vanishes in `A[1/f i] ⊗ HN n N`
    have h_ker : x ∈ ker (TensorProduct.mk c.baseAlg (Away (f i)) (HN n N) 1) := by
      have V_dense : IsCohomDense (coeffAway N (f i)) (V.whisker ψ') :=
        (isCohomDense_unitLocus N (f i)).mono fun _ ↦ le_iSup (commaUnitLocus ∘ f) i _
      -- the flat base change map out of `A[1/f i] ⊗ HN n N` is injective, and its target group
      -- vanishes
      exact (hasFlatBaseChange_V _ c.baseAlg ..).injective
        (((relFreeAb.isCohomEquiv_iff_subsingleton_rel _).1 V_dense.isCohomEquiv n).elim ..)
    exact exists_exists_eq_and.1 ((mem_ker_iff (.powers (f i))).1 h_ker)
  -- The long exact sequence of `0 → N → N → N / r → 0`, which stays exact over flat `B`.
  have isSMulRegular_HN (n : ℕ) (N : ModuleCat c.baseAlg) (r : c.baseAlg) (hr : IsSMulRegular N r)
      (ih : ∀ m < n, Subsingleton (HN m (.of _ (QuotSMulTop r N)))) : IsSMulRegular (HN n N) r :=
    -- `(… :)`: the term is elaborated from its arguments, then compared with `r • ·`
    fun y z ↦ (eq_of_tensorPush_eq (exact_lsmul_mkQ_smul_top N r) Quot.exists_rep
      (fun B ↦ B.property.rTensor_preserves_injective_linearMap _ hr) ih :)
  have HN_subsingleton : Subsingleton (HN n (.of _ c.baseAlg)) :=
    depth_vanishing HN le_radical_torsionOf isSMulRegular_HN hl_le hn _ h_reg
  -- The comparison is bijective on each `commaUnitLocus g`: both sites represent it by inverting
  -- `g`, and there the coefficient map of `γ` is an isomorphism.
  have comparison_bijective :
      γ.IsBijective (N := ψ ⋙ relFreeAb V) (N' := ψ' ⋙ relFreeAb V) (whiskerRight η _) :=
    IsClosedClass.relFreeAb_iSup_commaUnitLocus (f := f) _ (γ.isClosedClass η) fun g ↦
      -- replace the locus of `g` by the object that represents it, on pairs and on flat algebras
      ((γ.isBijective_congr (pointMap_comp _ (whiskerRight η (commaUnitLocus g).toFunctor))
          (.of_bijective
            (pointMap_bijective_of_existsUnique ((commaUnitLocus g).whisker ψ) _
              (HodgeTest.existsUnique_lift_away _ g isLocalization.1)))
          (.of_bijective (bijective_pointMap_flatToAway ⟨.of .., .self⟩ g))).2
        -- for representable functors only the coefficients at the representing objects count
        (γ.isBijective_of_repr (u := pointMap ⟨𝟙 _⟩) ⟨𝟙 _⟩
          (pointMap_id_bijective_of_fullyFaithful (𝟭 _) _)
          (.comp (AddEquiv.bijective _) (bijective_of_isIso (hodgeCoeff.map (_ ≫ _))))) :)
  have V_eq : V.whisker ψ = someUnitLocus f := by
    ext
    simp [V, Subfunctor.whisker]
    rfl
  rw [← V_eq]
  -- the group embeds into a product of copies of `HN n A`, which vanishes
  refine ⟨fun x y ↦ ?_⟩
  apply (H.pi_bijective ..).injective.comp (comparison_bijective n).injective
  exact funext fun i ↦ HN_subsingleton.elim ..

/-- Let `c = (A, M)` be a pair and `f` a finite family that generates the unit ideal of `A`. Then
the inclusion into h_c of the locus where some `f i` is a unit induces bijections on the
cohomology with coefficients `⋀ M`, in every degree. -/
lemma isCohomEquiv_someUnitLocus_of_span_eq_top {f : ι → c.baseAlg}
    (h_span : span (Set.range f) = ⊤) :
    IsCohomEquiv hodgeCoeff (freeAb.map (someUnitLocus f).ι) := by
  -- The unit ideal holds the weakly regular sequence `1, …, 1` of any length.
  refine (relFreeAb.isCohomEquiv_iff_subsingleton_rel _).2 fun n ↦ ?_
  exact DepthVanishing.subsingleton_of_isWeaklyRegular (List.replicate (n + 1) 1) (by aesop)
    (by simp) ⟨by simp⟩

/-- The first `d` variables of a polynomial ring in `d + e` variables form a weakly regular
sequence. -/
lemma isWeaklyRegular_X_castAdd (e : ℕ) :
    IsWeaklyRegular (MvPolynomial (Fin (d + e)) k)
      (List.ofFn (X (R := k) ∘ castAdd (n := d) e)) := by
  refine ⟨fun i hi_len ↦ (isSMulRegular_quotient_iff_mem_of_smul_mem ..).mpr fun q hq ↦ ?_⟩
  have hi : i < d + e := by grind
  have h_vars : {r : MvPolynomial (Fin (d + e)) k |
      r ∈ (List.ofFn (X (R := k) ∘ castAdd (n := d) e)).take i} =
      X '' castAdd e '' {j : Fin d | j < i} := by
    grind -ring -linarith [List.mem_take_iff_getElem]
  -- Membership in the ideal of the variables below `i` is read off the monomials, and
  -- multiplying by the `i`-th variable does not change the exponents below `i`.
  rw [smul_eq_mul, mul_top, ofList, h_vars, mem_ideal_span_X_image] at hq ⊢
  intro m hm
  have h_mem : Finsupp.single ⟨i, hi⟩ 1 + m ∈
      ((List.ofFn (X (R := k) ∘ castAdd (n := d) e))[i] • q).support := by
    simp_all
  exact (hq _ h_mem).imp (by grind -linarith [Finsupp.add_apply])

/-- Let `c = (A, M)` be a pair over `k` and `x_1, …, x_{2d}` étale coordinates on `A`, that is,
the `k`-algebra map `polyEval x : k[X_1, …, X_{2d}] → A` sending `X_i` to `x_i` is étale. Then
the cohomology of h_c with coefficients `⋀ M` and supports in the common zeros of the
`x_i − x_{d+i}` vanishes in degrees below `d`. -/
lemma hodge_vanishing_along_diagonal {x : Fin (d + d) → c.baseAlg} (hx_etale : (polyEval x).Etale)
    (hn : n < d) :
    Subsingleton (H (relFreeAb (someUnitLocus (x ∘ castAdd d - x ∘ natAdd d))) hodgeCoeff n) := by
  -- By `DepthVanishing.subsingleton_of_isWeaklyRegular` it suffices that the `x i - x (d + i)` form
  -- a weakly regular sequence in `c.baseAlg`.
  -- It is the image of the first `d` variables under a flat map: a linear change of variables
  -- `σ` followed by the étale map `polyEval x`.
  let σ : MvPolynomial (Fin (d + d)) k →ₐ[k] MvPolynomial (Fin (d + d)) k :=
    bind₁ (append (X ∘ castAdd d - X ∘ natAdd d) (-X ∘ natAdd d))
  -- on the variables `σ` is the involution `(u, v) ↦ (u - v, -v)` of the two halves
  have hσ_X (i : Fin (d + d)) : σ (σ (X i)) = X i := by
    -- without `-natAdd_eq_addNat` the lemma `append_right` would not apply
    induction i using Fin.addCases <;> simp [σ, -natAdd_eq_addNat]
  have hσ : Involutive σ := AlgHom.congr_fun (algHom_ext hσ_X : σ.comp σ = AlgHom.id k _)
  let algebra_σ : Algebra (MvPolynomial (Fin (d + d)) k) c.baseAlg :=
    ((polyEval x).comp σ.toRingHom).toAlgebra
  have h_flat : Module.Flat (MvPolynomial (Fin (d + d)) k) c.baseAlg :=
    Flat.comp (.of_bijective hσ.bijective) (Etale.iff_flat_and_formallyUnramified.1 hx_etale).1
  refine DepthVanishing.subsingleton_of_isWeaklyRegular _ ?_ (by simpa)
    (isWeaklyRegular_X_castAdd (k := k) d).of_flat
  simp [ofList, Set.range, algebraMap_toAlgebra, σ]

/-- Zariski descent for Hodge cohomology (`New.Variety.HasZariskiDescent`), with the pair `(A, M)`
seen through its square-zero extension `A ⊕ M`: a subfunctor that is locally everything for these
rings is dense for the coefficients `(A, M) ↦ ⋀_A M`. -/
lemma hasZariskiDescent_hodgeCoeff :
    HasZariskiDescent (HodgeTest.sqZeroExt (k := k) ⋙ forget₂ (CommAlg k) CommRingCat)
      hodgeCoeff := by
  intro Y U hU X y
  -- No maximal ideal holds all the elements whose inversion puts `y` into `U`, so finitely many
  -- of them generate the unit ideal of the square-zero extension.
  let G : Set (HodgeTest.sqZeroExt.obj X) :=
    {f | ∀ X' (g : X ⟶ X'), IsUnit (HodgeTest.sqZeroExt.map g f) → Y.map g y ∈ U.obj X'}
  have h_span : span G = ⊤ := by
    by_contra h_ne
    obtain ⟨m, hm, h_le⟩ := ne_top_iff_exists_maximal.1 h_ne
    obtain ⟨f, hf_notMem, hf_mem⟩ := hU X y m hm
    exact hf_notMem (h_le (subset_span hf_mem))
  obtain ⟨s, hs_sub, hs_span⟩ := (span_eq_top_iff_finite _).1 h_span
  -- Their first components `X.baseProj i` define a dense subfunctor `someUnitLocus` inside the
  -- preimage of `U`.
  have h_dense : IsCohomDense hodgeCoeff (someUnitLocus fun i : s ↦ X.baseProj i) := by
    refine fun _ g ↦ isCohomEquiv_someUnitLocus_of_span_eq_top ?_
    rw [← map_top (X.baseProj ≫ g.1.1).1, ← hs_span, Ideal.map_span, Set.image_eq_range]
    rfl
  exact (h_dense.mono fun X' g ⟨i, h_unit⟩ ↦
    hs_sub i.prop _ _ (isUnit_iff_isUnit_fst.2 h_unit)).isCohomEquiv

end New.Variety
