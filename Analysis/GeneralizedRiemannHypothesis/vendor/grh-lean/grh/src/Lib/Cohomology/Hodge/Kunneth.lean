import Lib.Cohomology.Hodge.DepthVanishing
import Lib.Cohomology.LerayHirsch

/-!
# Künneth formula: Hodge classes on X × X are sums of external products

The Künneth formula for Hodge cohomology `New.Variety.HodgeH`, in the weak form that the fixed-point
formula needs: cross products span.

* `New.Variety.kunneth`: over a field of characteristic 0, if `X` has an atlas, every class on
  `X × X` is a sum of cross products of classes on `X`.

Hodge cohomology is an Ext group in functors on pairs `(A, M)`, where `M` is a finite free
`A`-module (`New.Variety.HodgeTest`). It is taken from `(A, M) ↦ ℤ[X(A ⊕ M)]` to the exterior
algebra `(A, M) ↦ ⋀ M` (`New.Variety.hodgeCoeff`).

The proof first treats a product of two represented functors through the Leray–Hirsch map. It then
passes to the general case by dévissage in each factor.

Notions from other files:
* `CategoryTheory.Functor.mulPairing`: For a functor Φ to k-algebras with underlying functor F to
  abelian groups, the pairing F ⊗ F → F given by multiplication.
* `New.Variety.exteriorAlg`: The functor sending a pair (A, M) to the exterior algebra ⋀_A M, as a
  k-algebra.
* `New.Variety.lerayHirsch`: For an exact functor Φ and classes θ_i in Ext^{d_i}(ΦG, F), the map
  w ↦ Σ θ_i∘Φ(w_i) from finitely supported families in total Ext(S, G) to total Ext(ΦS, F).
* `New.Variety.freeAb`: The functor sending a set-valued functor Y to Z[Y], whose value at A is the
  free abelian group on Y(A).
* `New.Variety.abTensor`: The pointwise tensor product over ℤ of two functors from C to abelian
  groups, as a bifunctor.
* `New.Variety.H`, `New.Variety.TotalH`: The group Ext^n(N, F) in functors to abelian groups, and
  the direct sum of these groups over n.

## Relation to the literature

Known; see `Lib.Cohomology.Hodge.FixedPointFormula` for sources.
-/

namespace New.Variety

open CategoryTheory MonoidalCategory TensorProduct Abelian Function Finsupp AddSubmonoid Module
  Basis Algebra.TensorProduct CommAlgCat CartesianMonoidalCategory TotalH Ext Comparison
  IsCohomEquiv Eqv Finset

/-- Coordinates for the classes on the functor represented by a test `a`: they all have degree `0`
and are the forms on `a` (`New.Variety.TotalH.sectionEquiv`), here written in the basis
`a.formBasis` of the forms, reindexed by `g` and with its vectors multiplied by the signs `η`. -/
private noncomputable def formCoord {k : Type} [Field k] (a : HodgeTest k) {I : Type}
    (g : Finset a.Index ≃ I) (η : I → ℤˣ) :
    (I →₀ a.baseAlg) ≃+ TotalH (freeAb (reprBy a)) hodgeCoeff :=
  a.formBasis.reindex g
    |>.groupSMul η
    |>.repr.symm.toAddEquiv.trans (.trans (.symm .ulift) (sectionEquiv hodgeCoeff a))

/-- For a basis `b` over `k` of the forms on a test `c`, the `k`-linear isomorphism from families,
indexed by `b`, of families of elements of the ring `A'` of `c'` indexed by subsets of the index set
of `c'`, to families of elements of `A' ⊗ A` indexed by pairs of subsets: each vector of `b` is
expanded in the basis `c.formBasis` of the forms on `c`, over the ring `A` of `c`, indexed by
subsets of the index set of `c`. -/
private noncomputable def formTensor {k : Type} [Field k] (c c' : HodgeTest k) {J : Type}
    [DecidableEq J] (b : Basis J k (_root_.ExteriorAlgebra c.baseAlg (c.Index → c.baseAlg))) :
    (J →₀ Finset c'.Index →₀ c'.baseAlg) ≃ₗ[k]
      Finset c'.Index × Finset c.Index →₀ c'.baseAlg ⊗[k] c.baseAlg :=
  (equivFinsuppOfBasisRight (M := Finset c'.Index →₀ c'.baseAlg) b).symm ≪≫ₗ
    (c.formBasis.repr.restrictScalars k).lTensor _ ≪≫ₗ finsuppTensorFinsupp ..

/-- The cross product of two forms is their product. Let `l : c' ⟶ p` and `q : c ⟶ p` be maps of
tests, `x` a form on `c'` and `y` a form on `c`, read as classes of degree `0` on the represented
functors (`sectionEquiv`). The product of these classes, pulled back to `ℤ[h_p]` along the point
`(l, q)` of `h_c' × h_c`, is the class of the product of the images of `x` and `y` on `p`. -/
private lemma pullbackAlong_cross_sectionEquiv {k : Type} [Field k] {c c' p : HodgeTest k}
    (l : c' ⟶ p) (q : c ⟶ p) (x : _root_.ExteriorAlgebra c'.baseAlg (c'.Index → c'.baseAlg))
    (y : _root_.ExteriorAlgebra c.baseAlg (c.Index → c.baseAlg)) :
    pullbackAlong
        (freeAb.map (pointMap (Y := reprBy c' ⊗ reprBy c) (⟨l⟩, ⟨q⟩)) ≫ freeAb.prod _ _)
        (TotalH.comp
          (TotalH.map (abTensor.flip (freeAb (reprBy c))) (sectionEquiv hodgeCoeff c' ⟨x⟩))
          (homClass ((abTensor hodgeCoeff).map ((homReprEquiv c hodgeCoeff).symm ⟨y⟩) ≫
            exteriorAlg.mulPairing))) =
      sectionEquiv hodgeCoeff p ⟨exteriorMap l.snd x * exteriorMap q.snd y⟩ := by
  let f : freeAb (reprBy c') ⟶ hodgeCoeff := (homReprEquiv c' hodgeCoeff).symm ⟨x⟩
  let g : freeAb (reprBy c) ⟶ hodgeCoeff := (homReprEquiv c hodgeCoeff).symm ⟨y⟩
  -- All classes have degree zero, so the left side is the class of one morphism.
  change pullbackAlong _ (TotalH.comp (TotalH.map (abTensor.flip _) (homClass f)) _) =
    homClass ((homReprEquiv p hodgeCoeff).symm _)
  rw [map_homClass, ← homClass_comp, ← homClass_comp]
  refine congrArg homClass ((AddEquiv.eq_symm_apply _).mpr ?_)
  -- By Yoneda it corresponds to the product of the values of `f` at `l` and of `g` at `q`.
  have hf : f p (.of ⟨l⟩) = ⟨exteriorMap l.snd x⟩ := FreeAbelianGroup.lift_apply_of ..
  have hg : g p (.of ⟨q⟩) = ⟨exteriorMap q.snd y⟩ := FreeAbelianGroup.lift_apply_of ..
  change exteriorAlg.mulPairing p (f p (.of ⟨l⟩) ⊗ₜ g p (.of ⟨q⟩)) = _
  rw [hf, hg]
  rfl

/-- Some basis `b` over `k` of the forms on a test `c = (A, I)` (the exterior algebra `⋀_A A^I`) has
the Leray–Hirsch property: for every test `c'`, the Leray–Hirsch map for `Φ = – ⊗ ℤ[h_c]` and the
classes `θ j` (the product with the form `b j`, read as a class of degree `0` on `h_c`) is bijective
at `ℤ[h_c']`. So the products with the `b j` give all classes on the product of the functors `h_c'`
and `h_c` represented by `c'` and `c`, each in one way. -/
lemma exists_basis_forms_lerayHirsch {k : Type} [Field k] (c : HodgeTest k) :
    ∃ J : Type, ∃ b : Basis J k (ExteriorAlgebra c.baseAlg (c.Index → c.baseAlg)),
      ∀ c' : HodgeTest k,
      Bijective
        (lerayHirsch (Φ := abTensor.flip (freeAb (reprBy c)))
          (fun j : J ↦
            mk₀
              ((abTensor _).map ((homReprEquiv c hodgeCoeff).symm ⟨b j⟩) ≫ exteriorAlg.mulPairing))
          (freeAb (reprBy c'))) := by
  classical
  -- The product of the functors represented by `c'` and `c` is represented by
  -- `p = (A' ⊗ A, M' ⊕ M)` (index sets added), and the classes on a represented functor are the
  -- forms (`sectionEquiv`). So the claim is that the forms on `p` are the tensor product of the
  -- forms on `c'` and on `c`.
  let b : Basis (ofVectorSpaceIndex k c.baseAlg × Finset c.Index) k
      (_root_.ExteriorAlgebra c.baseAlg (c.Index → c.baseAlg)) :=
    (ofVectorSpace k c.baseAlg).smulTower c.formBasis
  refine ⟨ofVectorSpaceIndex k c.baseAlg × Finset c.Index, b, fun c' ↦ ?_⟩
  let p : HodgeTest k := ⟨c'.baseAlg ⊗ c.baseAlg, c'.Index ⊕ₗ c.Index⟩
  let l : c' ⟶ p := ⟨ofHom includeLeft, semilinearOfBasis _ fun i ↦ Pi.single (.inl i) 1⟩
  let q : c ⟶ p := ⟨ofHom includeRight, semilinearOfBasis _ fun i ↦ Pi.single (.inr i) 1⟩
  have hl (i : c'.Index) : l.snd (Pi.single i 1) = Pi.single (Sum.inl i) 1 :=
    semilinearOfBasis_single ..
  have hq (i : c.Index) : q.snd (Pi.single i 1) = Pi.single (Sum.inr i) 1 :=
    semilinearOfBasis_single ..
  -- `p` is the coproduct of `c'` and `c`: a map from `p` is a ring map from the tensor product and
  -- the images of the basis vectors.
  let z : (reprBy c' ⊗ reprBy c) p := (⟨l⟩, ⟨q⟩)
  have h_coprod (B : HodgeTest k) : Bijective (pointMap z B) := by
    refine (bijective_iff_existsUnique _).2 fun ⟨⟨f⟩, ⟨g⟩⟩ ↦ ?_
    -- `χ` is the ring map out of `A' ⊗ A` with the two given restrictions.
    obtain ⟨χ, ⟨hχ_left, hχ_right⟩, hχ_unique⟩ := existsUnique_tensor_desc f.fst g.fst
    let v : p.Index → B.Index → B.baseAlg :=
      Sum.elim (fun i ↦ f.snd (Pi.single i 1)) fun i ↦ g.snd (Pi.single i 1)
    let φ : p ⟶ B := ⟨χ, semilinearOfBasis _ v⟩
    have hφ (j : p.Index) : φ.snd (Pi.single j 1) = v j := semilinearOfBasis_single ..
    have hφ_left : l ≫ φ = f :=
      HodgeTest.hom_ext hχ_left fun i ↦ (congrArg φ.snd (hl i)).trans (hφ _)
    have hφ_right : q ≫ φ = g :=
      HodgeTest.hom_ext hχ_right fun i ↦ (congrArg φ.snd (hq i)).trans (hφ _)
    refine ⟨⟨φ⟩, Prod.ext (congrArg ULift.up hφ_left) (congrArg ULift.up hφ_right), ?_⟩
    rintro ⟨ψ⟩ ⟨⟩
    refine congrArg ULift.up (HodgeTest.hom_ext (hχ_unique _ ⟨rfl, rfl⟩) ?_)
    rintro (i | i)
    · exact ((hφ (.inl i)).trans (congrArg ψ.snd (hl i))).symm
    · exact ((hφ (.inr i)).trans (congrArg ψ.snd (hq i))).symm
  -- So pulling back along `ℤ[h_p] → ℤ[h_c' × h_c] → ℤ[h_c'] ⊗ ℤ[h_c]` is bijective on classes.
  let π :
      freeAb.obj (reprBy p) ⟶ (abTensor.obj (freeAb.obj (reprBy c'))).obj (freeAb.obj (reprBy c)) :=
    freeAb.map (isoOfAppBijective (pointMap z) h_coprod).hom ≫ freeAb.prod ..
  -- Up to a sign `ε`, the basis of the forms on `p` consists of the products of basis forms.
  have h_wedge (S : Finset c'.Index) (T : Finset c.Index) :
      ∃ η : ℤˣ,
        exteriorMap l.snd (c'.formBasis S) * exteriorMap q.snd (c.formBasis T) =
          η • p.formBasis (S.disjSum T) := by
    have h_left : exteriorMap l.snd (c'.formBasis S) = p.formBasis (S.map .inl) :=
      exteriorMap_formBasis l (.sumLexInl ..) hl S
    have h_right : exteriorMap q.snd (c.formBasis T) = p.formBasis (T.map .inr) :=
      exteriorMap_formBasis q (.sumLexInr ..) hq T
    have h_disjoint : Disjoint (S.map .inl) (T.map .inr) := disjoint_map_inl_map_inr S T
    have h_union : (S.map .inl).disjUnion (T.map .inr) h_disjoint = S.disjSum T := by aesop
    rw [h_left, h_right, ← h_union]
    exact ⟨_, ExteriorAlgebra.basis_mul_of_disjoint (I := p.Index) _ ⟨_, rfl⟩ ⟨_, rfl⟩ h_disjoint⟩
  choose ε hε using h_wedge
  -- In the coordinates `formCoord` for classes on represented functors, the map becomes the
  -- isomorphism `formTensor c c' b`.
  refine ((of_isIso π).bijective_pullbackAlong.of_comp_iff' _).mp
    ((bijective_iff_of_comm_sq ?_ (mapRange.addEquiv (formCoord c' 1 1)).bijective
        (formCoord p sumEquiv.toEquiv (uncurry ε)).bijective).mp (formTensor c c' b).bijective)
  -- Both sides are additive: check the square on `r • (form S)` placed at the index `(i, T)`.
  refine curryAddEquiv.surjective.forall.mpr fun w ↦ w.induction_linear (by simp [map_zero])
    (fun u v hu hv ↦ by simp_all only [map_add, Function.comp_apply]) fun ⟨⟨i, T⟩, S⟩ r ↦ ?_
  have h_source :
      mapRange.addEquiv (formCoord c' 1 1) (curryAddEquiv (single ((i, T), S) r)) =
        single (i, T) (sectionEquiv hodgeCoeff c' ⟨r • c'.formBasis S⟩) := by
    simp [formCoord, groupSMul, -map_smul]
    rfl
  have h_index : p.formBasis.reindex sumEquiv.toEquiv (S, T) = p.formBasis (S.disjSum T) :=
    Basis.reindex_apply _ _ _
  have h_target :
      formCoord p sumEquiv.toEquiv (uncurry ε)
          (formTensor c c' b (curryAddEquiv (single ((i, T), S) r))) =
        sectionEquiv hodgeCoeff p ⟨r ⊗ₜ[k] i.val • ε S T • p.formBasis (S.disjSum T)⟩ := by
    simp [formCoord, formTensor, b, groupSMul, h_index]
    rfl
  -- The product of the two forms, both carried to `p`, is the form on the right.
  have h_scalar : l.fst r * q.fst i.val = r ⊗ₜ[k] i.val := (tmul_mul_tmul ..).trans (by simp)
  rw [Function.comp_apply, h_source, h_target, lerayHirsch_single, ← h_scalar, ← hε,
    ← smul_mul_smul_comm]
  refine (pullbackAlong_cross_sectionEquiv l q _ (b (i, T))).trans ?_
  rw [smulTower_apply, exteriorMap_smul, exteriorMap_smul, ofVectorSpace_apply_self]
  rfl

/-- Moving an endomorphism `ρ` of the coefficients across a cross product. Let `μ : F ⊗ F → F` be a
pairing for which `ρ` on the second factor has the same effect as `ρ` on the first. Then the product
of a class `x` on `N` with `g = f ≫ ρ` is the product of `x` pushed along `ρ` with `f`. The left
side is written through the functor `N ⊗ –` and the right side through `– ⊗ M`. -/
private lemma cross_comp_eq_comp_cross {C : Type 1} [Category C] {M N F : AbFunctor C}
    [HasFlatValues M] [HasFlatValues N] [HasFlatValues F] (μ : abTensor F F ⟶ F) (ρ : F ⟶ F)
    (h_balanced : (abTensor F).map ρ ≫ μ = (abTensor.flip F).map ρ ≫ μ) {f g : M ⟶ F}
    (h_factor : g = f ≫ ρ) {a : ℕ} (x : H N F a) :
    TotalH.comp (TotalH.map (abTensor N) (homClass g))
        (H.push ((abTensor.flip.obj F).obj N) μ a (x.mapExactFunctor (abTensor.flip F))).toTotalH =
      TotalH.comp (TotalH.map (abTensor.flip M) (TotalH.comp x.toTotalH (homClass ρ)))
        (homClass ((abTensor F).map f ≫ μ)) := by
  subst h_factor
  -- The two morphisms `F ⊗ M → F` agree by `h_balanced` and the bifunctoriality of `⊗`.
  have h_morphism :
      (abTensor.flip.map (f ≫ ρ)).app F ≫ μ =
        (abTensor.flip M).map ρ ≫ (abTensor F).map f ≫ μ :=
    calc (abTensor.flip.map (f ≫ ρ)).app F ≫ μ
        = (abTensor F).map f ≫ (abTensor F).map ρ ≫ μ := by simp
      _ = (abTensor F).map f ≫ (abTensor.flip F).map ρ ≫ μ := by rw [h_balanced]
      _ = (abTensor.flip M).map ρ ≫ (abTensor F).map f ≫ μ := by simp
  -- The image of `x` is natural in the second factor.
  have h_natural :
      TotalH.comp (TotalH.map (abTensor.flip M) x.toTotalH)
          (homClass ((abTensor.flip.map (f ≫ ρ)).app F)) =
        TotalH.comp (homClass ((abTensor N).map (f ≫ ρ)))
          (TotalH.map (abTensor.flip F) x.toTotalH) :=
    naturality (abTensor.flip.map (f ≫ ρ)) x.toTotalH
  rw [map_comp_assoc, map_homClass, map_homClass, ← homClass_comp, ← h_morphism, homClass_comp,
    TotalH.comp_assoc_of_sq h_natural, map_of]
  exact congrArg _ (of_comp_homClass _).symm

/-- The first factor of the Künneth formula, for a represented second factor. Let `N` be a functor
that lies in every closed class (`New.Variety.IsClosedClass`) containing the represented functors
(`h_devissage`), and let `θ` be the products with a basis of the classes of each degree on `N`.
Then the Leray–Hirsch map of `θ` for `Φ = N ⊗ –` is bijective at every represented functor. -/
private lemma bijective_lerayHirsch_reprBy {k : Type} [Field k] [CharZero k]
    {N : AbFunctor (HodgeTest k)} [HasFlatValues N]
    (h_devissage : ∀ {P : AbFunctor (HodgeTest k) → Prop}, IsClosedClass P →
      (∀ c : HodgeTest k, P (freeAb (reprBy c))) → P N)
    (c : HodgeTest k) :
    Bijective (lerayHirsch (Φ := abTensor N)
      (fun i : Σ a : ℕ, ofVectorSpaceIndex k (H N hodgeCoeff a) ↦
        H.push _ exteriorAlg.mulPairing i.fst
          ((i.snd : H N hodgeCoeff i.fst).mapExactFunctor (abTensor.flip _)))
      (freeAb (reprBy c))) := by
  classical
  -- By dévissage in the first factor, the products with a basis `b` of the forms on `c` give a
  -- bijection. Both maps are the cross product on `H(N) ⊗ forms(c)`: the coordinates for the
  -- basis of `H(N)` are exchanged for those for `b`.
  obtain ⟨J, b, hb⟩ := exists_basis_forms_lerayHirsch c
  let I := Σ a, ofVectorSpaceIndex k (H N hodgeCoeff a)
  let forms : (I × J →₀ k) ≃+ (I →₀ TotalH (freeAb (reprBy c)) hodgeCoeff) :=
    curryAddEquiv (α := I).trans (mapRange.addEquiv
      (b.repr.symm.toAddEquiv.trans (.trans (.symm .ulift) (sectionEquiv hodgeCoeff c))))
  let classes : (I × J →₀ k) ≃ₗ[k] (J →₀ Π₀ a, H N hodgeCoeff a) :=
    Finsupp.domLCongr (.prodComm _ J) ≪≫ₗ curryLinearEquiv k ≪≫ₗ
      mapRange.linearEquiv (DFinsupp.basis fun a ↦ ofVectorSpace k (H N hodgeCoeff a)).repr.symm
  refine (bijective_iff_of_comm_sq ?_ forms.bijective
      (h_devissage isClosedClass_isLerayHirschBasis hb)).1 classes.bijective
  -- Both sides are additive: compare them on `r • x ⊗ b j`.
  refine fun w ↦ w.induction_linear (by simp [map_zero])
    (fun u v hu hv ↦ by simp only [map_add, hu, hv]) fun ⟨⟨a, x⟩, j⟩ r ↦ ?_
  have h_forms : forms (single (⟨a, x⟩, j) r) =
      single ⟨a, x⟩ (sectionEquiv hodgeCoeff c ⟨r • b j⟩) := by
    simp [I, forms]
    rfl
  have h_classes : classes (single (⟨a, x⟩, j) r) = single j (r • x.val.toTotalH) := by
    simp [I, classes, DFinsupp.basis]
    rfl
  -- The scalar `r` acts on the coefficients by `ρ`; move it out of the class of `r • b j` ...
  let ρ : hodgeCoeff (k := k) ⟶ hodgeCoeff := (CoeffAction.act r).asHom
  have h_scalar :
      (homReprEquiv c hodgeCoeff).symm (ρ.app c ⟨b j⟩) =
        (homReprEquiv c hodgeCoeff).symm ⟨b j⟩ ≫ ρ := by
    apply (mk₀_bijective ..).injective
    rw [← mk₀_comp_mk₀]
    exact (push_homReprEquiv_symm ρ c ⟨b j⟩).symm
  -- ... and across the product of forms, which is bilinear.
  have h_balanced :
      (abTensor hodgeCoeff).map ρ ≫ exteriorAlg.mulPairing =
        (abTensor.flip hodgeCoeff).map ρ ≫ exteriorAlg.mulPairing := by
    have h_bilinear (A : HodgeTest k) (u v : exteriorAlg.obj A) : u * r • v = r • u * v := by
      rw [mul_smul_comm, smul_mul_assoc]
    exact abTensor_hom_ext fun A u v ↦ congrArg ULift.up (h_bilinear A u.down v.down)
  rw [h_forms, h_classes, lerayHirsch_single, lerayHirsch_single, TotalH.smul_eq_comp]
  exact cross_comp_eq_comp_cross exteriorAlg.mulPairing ρ h_balanced h_scalar x.val

/-- Künneth: over a field `k` of characteristic `0`, if `X` has an atlas of dimension `d`
(`HasAtlas`: it yields a subfunctor that is locally all of `X` and is built from charts represented
on `HodgeTest k`), every class `z` in `HodgeH` of degree `n` on `X × X` is a finite sum of cross
products `x × y` of Hodge classes on `X` of degrees `a` and `b` with `b + a = n`. The cross product
is the cup product `cup` for the multiplication of exterior algebras, pulled back along
`ℤ[X × X] → ℤ[X] ⊗ ℤ[X]` (`New.Variety.freeAb.prod`). -/
lemma kunneth {k : Type} [Field k] [CharZero k] {X : CommAlg k ⥤ Type 1} {d n : ℕ}
    [hX : HasAtlas d X] (z : HodgeH (freeAb.obj (X ⊗ X)) n) :
    z ∈ AddSubmonoid.closure
      {w : HodgeH (freeAb.obj (X ⊗ X)) n |
        ∃ (a b : ℕ) (e : b + a = n), ∃ (x : HodgeH (freeAb.obj X) a) (y : HodgeH (freeAb.obj X) b),
          w = HodgeH.map (freeAb.prod X X) (cup (exteriorAlg (k := k)).mulPairing x y e :)} := by
  classical
  -- Replace `X` by a dense subfunctor `U` built from charts. Leray–Hirsch, applied in one factor
  -- and then in the other, writes every class on `U × U` as a sum of products of classes on `U`.
  obtain ⟨V, hV_cover, hV_built⟩ : ∃ V : Subfunctor X, IsCharting V := hX.exists_isCharting
  -- `V` is locally all of `X`; `U` is `V` read on pairs, `(A, M) ↦ V(A ⊕ M)`, and it is dense by
  -- Zariski descent.
  let U : Subfunctor (HodgeTest.sqZeroExt ⋙ X) := V.whisker (HodgeTest.sqZeroExt (k := k))
  let N : AbFunctor (HodgeTest k) := freeAb U.toFunctor
  have hU : IsCohomDense hodgeCoeff U := hasZariskiDescent_hodgeCoeff (hV_cover.whisker _)
  -- Dévissage: a class closed in the sense of `IsClosedClass` that contains the represented
  -- functors contains `N = ℤ[U]`, as the charts from which `V` is built are represented on
  -- `HodgeTest k` (`exists_univPoint`).
  have h_devissage {P : AbFunctor (HodgeTest k) → Prop} (hP : IsClosedClass P)
      (h : ∀ c : HodgeTest k, P (freeAb (reprBy c))) : P N := by
    refine hV_built _ (hP.comap (restrictAlong _)) fun b _ ↦ ?_
    obtain ⟨u, -, h_rep⟩ := b.exists_univPoint
    exact hP.freeAb_of_bijective _ h_rep (h _)
  -- `θ ⟨a, x⟩` is the product with `x`, for `x` in a basis of the classes of degree `a` on `U`.
  let θ (i : Σ a, ofVectorSpaceIndex k (H N hodgeCoeff a)) :
      H (abTensor N hodgeCoeff) hodgeCoeff i.fst :=
    H.push _ exteriorAlg.mulPairing _
      ((i.snd : H N hodgeCoeff i.fst).mapExactFunctor (abTensor.flip _))
  -- Dévissage in the second factor: the products with the classes `θ i` give all classes on
  -- `U × U`, here read on the part `U₂` of `X × X` with both coordinates in `U`.
  let U₂ : Subfunctor ((HodgeTest.sqZeroExt ⋙ X) ⊗ (HodgeTest.sqZeroExt ⋙ X)) :=
    U.preimage (fst _ _) ⊓ U.preimage (snd _ _)
  let α : freeAb U₂.toFunctor ⟶ abTensor N N :=
    freeAb.map (NatIso.ofComponents fun _ ↦ (Equiv.Set.prod ..).toIso).hom ≫
      freeAb.prod U.toFunctor _
  have h_basis : Bijective (lerayHirsch (Φ := abTensor N) θ N) :=
    h_devissage isClosedClass_isLerayHirschBasis (bijective_lerayHirsch_reprBy h_devissage)
  have h_onto : Surjective (pullbackAlong α ∘ lerayHirsch (Φ := abTensor N) θ N) :=
    ((of_isIso α).bijective_pullbackAlong.comp h_basis).surjective
  -- `U₂` is dense in `X × X`, so restriction of classes is injective.
  have h_restrict : IsCohomEquiv hodgeCoeff (freeAb.map U₂.ι) :=
    ((hU.preimage (fst ..)).inf (hU.preimage (snd ..))).isCohomEquiv
  refine (mem_map_iff_mem (h_restrict n).injective).1 ?_
  -- The restriction of `z` is the degree `n` part of a sum of terms `x × y` on `U × U`.
  obtain ⟨w, hw⟩ := h_onto (.of _ n (H.map _ (freeAb.map U₂.ι) n z))
  rw [← DirectSum.of_eq_same n (H.map _ (freeAb.map U₂.ι) n z), ← hw]
  clear hw
  refine w.induction_linear (by simp) (by simp_all [add_mem]) fun ⟨a, x, hx⟩ y ↦ ?_
  induction y using DirectSum.induction_on with
  | zero => simp
  | add y y' hy hy' => simp_all [add_mem]
  | of b y =>
    -- The homogeneous classes `x` and `y` on `U` are restrictions of classes on `X`.
    obtain ⟨x, rfl⟩ := (hU.isCohomEquiv a).surjective x
    obtain ⟨y, rfl⟩ := (hU.isCohomEquiv b).surjective y
    -- The cross product `x × y` on `X × X` restricts to the product of the restrictions.
    have h_square :
        α ≫ (abTensor.map (freeAb.map U.ι)).app N ≫ (abTensor _).map (freeAb.map U.ι) =
        freeAb.map U₂.ι ≫ HodgeTest.sqZeroExt.whiskerLeft (freeAb.prod X X) :=
      freeAb.hom_ext
    let x' : H N hodgeCoeff a := H.map _ (freeAb.map U.ι) a x
    let y' : H N hodgeCoeff b := H.map _ (freeAb.map U.ι) b y
    have h_cross :
        H.map hodgeCoeff (freeAb.map U₂.ι) (b + a)
            (HodgeH.map (freeAb.prod X X) (cup exteriorAlg.mulPairing x y rfl :)) =
          H.map hodgeCoeff α (b + a)
            ((y'.mapExactFunctor (abTensor N)).comp (θ ⟨a, x', hx⟩) rfl) := by
      refine (H.map_comp ..).symm.trans ((cup_map (h := h_square) ..).trans ?_)
      exact congrArg _ (comp_assoc_of_third_deg_zero ..)
    obtain rfl | hn := eq_or_ne n (b + a)
    · refine ⟨_, subset_closure ⟨a, b, rfl, x, y, rfl⟩, h_cross.trans ?_⟩
      simp [lerayHirsch_single, comp_of, H.map, x', y']
      rfl
    · -- A product of degree `b + a ≠ n` has no part in degree `n`.
      simp [θ, lerayHirsch_single, comp_of, DirectSum.of_eq_of_ne, hn]

end New.Variety
