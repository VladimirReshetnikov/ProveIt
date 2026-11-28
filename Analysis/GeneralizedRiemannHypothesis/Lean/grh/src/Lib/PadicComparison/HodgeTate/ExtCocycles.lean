import Lib.Cohomology.Hodge.Site

/-!
# Ext¹ classes of cocycles of functors, and contraction on exterior algebras

For functors `N`, `F` from `C` to abelian groups (`New.Variety.AbFunctor C`),
`New.Variety.TotalH N F = ⨁ₙ Extⁿ(N, F)` is the total Ext group. Its Yoneda product is
`New.Variety.TotalH.comp x y`, with `x` first. A morphism `f` gives the class
`New.Variety.TotalH.homClass f` of degree 0, and `New.Variety.TotalH.map Φ` applies an exact functor
`Φ` degree by degree. The file proves a sign rule for connecting classes and attaches to a 1-cocycle
a class in `Ext¹`. For a semilinear map `φ = (φ₀, φ₁) : M → T' × M'`, it also defines
`New.Variety.contraction φ : ⋀ M → ⋀ M'`, which contracts with `φ₀` and applies `φ₁` to the
remaining factors, and proves a product rule for it.

## Main definitions and results

* `New.Variety.TotalH.extClass_sign_comm`: the connecting classes of a short exact sequence of
  functors `Ψ → Ξ → Φ` commute with a class of degree `a` up to the sign `(-1) ^ a`.
* `New.Variety.Cocycle`, `New.Variety.Cocycle.cohomClass`: a 1-cocycle from `F` to `G` twists
  `G × F` into an extension of `F` by `G`, hence a class in `Ext¹(F, G)`.
* `New.Variety.contraction_mul`: `New.Variety.contraction φ` is a graded derivation along
  `New.Variety.exteriorMapSnd φ`, the ring map of `φ₁`.

Notions from other files:
* `New.Variety.abTensor`: The pointwise tensor product over ℤ of two such functors, as a bifunctor.
* `New.Variety.restrictAlong`: For φ: C' → C, the functor N ↦ N∘φ from functors on C to functors on
  C', with values in D.

## Relation to the literature

Known; see `Lib.PadicComparison.HodgeTate.PeriodMap` for sources.
-/

/-!
## Ext¹ classes of 1-cocycles and signs of connecting classes

* `New.Variety.abTensor_shortExact`: tensoring with a short exact sequence of functors whose
  quotient is flat gives a short exact sequence.
* `New.Variety.Gm`: the unit group of a commutative ring, as a functor to abelian groups.
-/

namespace New.Variety

open CategoryTheory Limits Abelian.Ext AddCommGrpCat ShortComplex LinearMap TotalH pushout

variable {C : Type 1} [Category C] {F G F' G' : AbFunctor C}

set_option backward.isDefEq.respectTransparency false

/-! ### The sign rule for connecting classes -/

/-- Let `S` be a short exact sequence of functors, `α : A ⟶ B` a monomorphism, and `a : S.X₁ ⟶ A`,
`b : S.X₂ ⟶ B` with `a ≫ α = S.f ≫ b`. Then there is a map `c : S.X₃ ⟶ cokernel α` that
commutes with the quotient maps, and the class of `S` followed by `a` is `c` followed by the class
of the sequence `A → B → cokernel α`. -/
lemma exists_cokernel_map_extClass {S : ShortComplex (AbFunctor C)} (hS : S.ShortExact)
    {A B : AbFunctor C} (α : A ⟶ B) [Mono α] (a : S.X₁ ⟶ A) (b : S.X₂ ⟶ B)
    (h_square : a ≫ α = S.f ≫ b) :
    ∃ c : S.X₃ ⟶ cokernel α,
      S.g ≫ c = b ≫ cokernel.π α ∧
      hS.extClass.comp (mk₀ a) (add_zero 1) =
        (mk₀ c).comp (ShortExact.mk (exact_cokernel α)).extClass (zero_add 1) := by
  have hS_epi : Epi S.g := hS.epi_g
  -- `S.f ≫ b = a ≫ α` dies in the cokernel of `α`
  obtain ⟨c, hc⟩ := hS.exact.desc' (b ≫ cokernel.π α) (by simp [← reassoc_of% h_square])
  exact ⟨c, hc, hS.extClass_naturality ⟨exact_cokernel α⟩ ⟨a, b, c, h_square, hc.symm⟩⟩

/-- Let `0 → Ψ K → Ξ K → Φ K → 0` (maps `i`, `p`) be short exact for every `K`, with `Φ`, `Ψ`
exact and `Ξ` additive, and let `T` be a short exact sequence of functors. In the 3 × 3 diagram
with these rows for the three terms of `T`, the two composites of connecting classes from
`Φ T.X₃` to `Ψ T.X₁` in `Ext²` differ by a sign. -/
lemma extClass_anticomm {Ψ Ξ Φ : AbFunctor C ⥤ AbFunctor C} [IsExactFunctor Φ] [IsExactFunctor Ψ]
    [Ξ.Additive] {i : Ψ ⟶ Ξ} {p : Ξ ⟶ Φ} {hw_zero : ∀ K : AbFunctor C, i.app K ≫ p.app K = 0}
    (h_row : ∀ K : AbFunctor C, ShortExact ⟨i.app K, p.app K, hw_zero K⟩)
    {T : ShortComplex (AbFunctor C)} (hT : T.ShortExact) :
    (hT.map_of_exact Φ).extClass.comp (h_row T.X₁).extClass (rfl : 1 + 1 = 2) =
      -(h_row T.X₃).extClass.comp (hT.map_of_exact Ψ).extClass rfl := by
  have h_mono (K : AbFunctor C) : Mono (i.app K) := (h_row K).mono_f
  have h_epi (K : AbFunctor C) : Epi (p.app K) := (h_row K).epi_g
  have hT_mono : Mono T.f := hT.mono_f
  -- Both classes that end in `Ψ.obj T.X₁` are pulled back from the class of the diagonal
  -- monomorphism `α`, along maps `u` and `v` to its cokernel.
  let α : Ψ.obj T.X₁ ⟶ Ξ.obj T.X₂ := Ψ.map T.f ≫ i.app T.X₂
  obtain ⟨u, hu : p.app T.X₁ ≫ u = Ξ.map T.f ≫ cokernel.π α, hu_class⟩ :=
    exists_cokernel_map_extClass (h_row T.X₁) α (𝟙 _) (Ξ.map T.f) (by simp [α])
  obtain ⟨v, hv : Ψ.map T.g ≫ v = i.app T.X₂ ≫ cokernel.π α, hv_class⟩ :=
    exists_cokernel_map_extClass (hT.map_of_exact Ψ) α (𝟙 _) (i.app T.X₂) (Category.id_comp α)
  -- Push the row at `T.X₃` out along `v`; this compares its class with that of `inl`.
  obtain ⟨c, hc : p.app T.X₃ ≫ c = inr v (i.app T.X₃) ≫ cokernel.π (inl v (i.app T.X₃)),
      hc_class⟩ :=
    exists_cokernel_map_extClass (h_row T.X₃) (inl v (i.app T.X₃)) v (inr v (i.app T.X₃)) condition
  -- The column of `Φ` maps to the same pushed-out sequence, by `u`, `b` and `-c`. The sign comes
  -- from the difference that defines `b`.
  have h_desc : i.app T.X₂ ≫ (cokernel.π α ≫ pushout.inl v (i.app T.X₃) -
      Ξ.map T.g ≫ pushout.inr v (i.app T.X₃)) = 0 := by
    simp [← reassoc_of% hv, condition]
  obtain ⟨b, hb⟩ : ∃ b : Φ.obj T.X₂ ⟶ pushout v (i.app T.X₃), p.app T.X₂ ≫ b =
      cokernel.π α ≫ pushout.inl v (i.app T.X₃) - Ξ.map T.g ≫ pushout.inr v (i.app T.X₃) :=
    (h_row T.X₂).exact.desc' _ h_desc
  have h_left : u ≫ pushout.inl v (i.app T.X₃) = Φ.map T.f ≫ b := by
    simp [← cancel_epi (p.app _), ← p.naturality_assoc, hb, reassoc_of% hu, ← Ξ.map_comp_assoc]
  have h_right : b ≫ cokernel.π (pushout.inl v (i.app T.X₃)) = Φ.map T.g ≫ (-c) := by
    simp [← cancel_epi (p.app _), ← p.naturality_assoc, hc, reassoc_of% hb]
  have h_column : (hT.map_of_exact Φ).extClass.comp (mk₀ u) (add_zero 1) =
      (mk₀ (-c)).comp (ShortExact.mk (exact_cokernel (pushout.inl v (i.app T.X₃)))).extClass
        (zero_add 1) :=
    (hT.map_of_exact Φ).extClass_naturality ⟨exact_cokernel _⟩ ⟨u, b, -c, h_left, h_right⟩
  -- With `ε`, `ε'` the classes of `α` and `inl`, both sides are `-c` followed by `ε'` and `ε`.
  -- Write the two classes through `α` as `u`, `v` followed by `ε`, then move `-c` across.
  rw [comp_mk₀_id] at hu_class hv_class
  rw [hu_class, hv_class]
  simp [← comp_assoc_of_second_deg_zero, h_column, hc_class]

/-- Let `Φ`, `Ψ` be exact functors and `Ξ` an additive functor to `AbFunctor C`, with natural maps
`i : Ψ ⟶ Ξ` and `p : Ξ ⟶ Φ` such that `0 → ΨK → ΞK → ΦK → 0` is short exact for every `K`. For `x`
in `Ext^a(F,G)`, `Φ(x)` followed by the extension class at `G` equals `(−1)^a` times the extension
class at `F` followed by `Ψ(x)`, in total Ext. -/
lemma TotalH.extClass_sign_comm {Ψ Ξ Φ : (C ⥤ Ab) ⥤ AbFunctor C} [IsExactFunctor Φ]
    [IsExactFunctor Ψ] [Ξ.Additive] {i : Ψ ⟶ Ξ} {p : Ξ ⟶ Φ}
    {hw_zero : ∀ K : C ⥤ Ab, i.app K ≫ p.app K = 0}
    (h_row : ∀ K : C ⥤ Ab, ShortExact ⟨i.app K, p.app K, hw_zero K⟩) {a : ℕ} (x : H F G a) :
    comp (map Φ (DirectSum.of (H F G) a x)) (h_row G).extClass.toTotalH =
      (-1) ^ a • comp (h_row F).extClass.toTotalH (map Ψ x.toTotalH) := by
  -- Induction on the degree: `x` is a map `f`, or a class followed by the class of a short
  -- exact sequence `T`. In degree zero the claim is the naturality of the rows in `f`.
  induction x with
  | h₀ G f =>
    have h_nat : (h_row F).extClass.comp (mk₀ (Ψ.map f)) (add_zero 1) =
        (mk₀ (Φ.map f)).comp (h_row G).extClass (zero_add 1) :=
      (h_row F).extClass_naturality (h_row G)
        ⟨Ψ.map f, Ξ.map f, Φ.map f, i.naturality f, p.naturality f⟩
    simp [comp_of, h_nat, mapExactFunctor_mk₀]
  | h T hT n x ih =>
    -- compose `ih` with the class of `Ψ T`; passing the class of `T` costs one more sign
    calc comp (map Φ (DirectSum.of (H F T.X₁) (n + 1) (x.comp hT.extClass rfl)))
          (h_row T.X₁).extClass.toTotalH
        = comp (map Φ (DirectSum.of (H F T.X₃) n x))
            (comp (h_row T.X₃).extClass.toTotalH (-map Ψ hT.extClass.toTotalH)) := by
          -- `extClass_anticomm` for `T`, in the total Ext groups
          have h_anti :
              comp (map Φ (DirectSum.of (H T.X₃ T.X₁) 1 hT.extClass))
                  (h_row T.X₁).extClass.toTotalH =
                -comp (h_row T.X₃).extClass.toTotalH (map Ψ hT.extClass.toTotalH) := by
            simp [comp_of, mapExactFunctor_extClass, extClass_anticomm h_row hT]
          simp only [← comp_of, map_comp, comp_assoc, h_anti, map_neg]
      _ = comp ((-1) ^ n • comp (h_row F).extClass.toTotalH (map Ψ x.toTotalH))
            (-map Ψ hT.extClass.toTotalH) := comp_assoc_of_eq ih _
      _ = (-1) ^ (n + 1) • comp (h_row F).extClass.toTotalH
            (map Ψ (x.comp hT.extClass rfl).toTotalH) := by
          simp [← comp_of, map_comp, pow_add, comp_assoc]

/-- If `f ≫ g = 0`, the maps `f` and `g` tensored pointwise with `K` also compose to zero. -/
lemma abTensor_flip_map_app_comp_eq_zero {E : AbFunctor C} {f : G' ⟶ E} {g : E ⟶ G}
    (hfg : f ≫ g = 0) (K : AbFunctor C) :
    (abTensor.flip.map f).app K ≫ (abTensor.flip.map g).app K = 0 :=
  -- `(abTensor.flip.map f).app K` is `(abTensor.obj K).map f` by definition.
  (ShortComplex.map ⟨f, g, hfg⟩ (abTensor.obj K)).zero

/-- A short exact sequence 0 → G' → E → G → 0 of functors to abelian groups, G with flat values,
stays short exact after pointwise tensor product with any K. -/
lemma abTensor_shortExact [HasFlatValues G] {E : AbFunctor C} {f : G' ⟶ E} {g : E ⟶ G}
    {hfg : f ≫ g = 0} (hS : ShortExact (ShortComplex.mk f g hfg)) (K : AbFunctor C) :
    ShortExact (ShortComplex.mk ((abTensor.flip.map f).app K) ((abTensor.flip.map g).app K)
      (abTensor_flip_map_app_comp_eq_zero hfg K)) := by
  -- At each object `c` the sequence is a short exact sequence of abelian groups. Tensoring is right
  -- exact, and it keeps the first map injective because the quotient `G.obj c` is flat.
  have h_at (c : C) :
      ((ShortComplex.mk f g hfg).map ((evaluation C AddCommGrpCat).obj c)).ShortExact :=
    hS.map_of_exact _
  have h_surj (c : C) : Function.Surjective (g.app c).hom.toIntLinearMap :=
    (h_at c).ab_surjective_g
  have h_exact (c : C) :
      Function.Exact (f.app c).hom.toIntLinearMap (g.app c).hom.toIntLinearMap :=
    LongExactSeq.exact_of_shortComplex_exact (h_at c).exact
  refine (shortExact_of_app (fun c ↦ ?_) (fun c ↦ ?_) fun c ↦ ?_).2
  · have hG_flat : Module.Flat ℤ (G.obj c) := HasFlatValues.flat c
    exact lTensor_injective_of_exact_of_flat _ (h_surj c) _ (h_at c).ab_injective_f (h_exact c) _
  · exact lTensor_exact (K.obj c) (h_exact c) (h_surj c)
  · exact lTensor_surjective (K.obj c) (h_surj c)

/-- The multiplicative group: the functor sending a commutative ring R to its unit group R^×,
written additively. `liftCoeff` wraps each value in `ULift`, so for `u : Gm A` the underlying unit
is `u.down`. -/
def Gm : AbFunctor CommRingCat :=
  liftCoeff (forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙ CommGrpCat.toAddCommGrp)

lemma Gm.ext {A : CommRingCat} {u v : Gm A} : u = v ↔ u.down.val = v.down.val :=
  ULift.ext_iff.trans Units.ext_iff

/-! ### Cocycles and their extension classes -/

/-- A 1-cocycle from F to G: homomorphisms D(f): F(c) → G(d) for f: c → d, with
D(gf) = G(g)D(f) + D(g)F(f). -/
structure Cocycle (F G : AbFunctor C) where
  /-- The homomorphism `F(c) → G(d)` attached to a morphism `c ⟶ d`. -/
  component {c d : C} : (c ⟶ d) → (F.obj c ⟶ G.obj d)
  /-- The cocycle rule `D(gf) = G(g) D(f) + D(g) F(f)`. -/
  cocycle_comp {c d e : C} (f : c ⟶ d) (g : d ⟶ e) :
      component (f ≫ g) = component f ≫ G.map g + F.map f ≫ component g

namespace Cocycle

variable (D : Cocycle F G)

/-- For a cocycle D, the sequence G → E → F with E(c) = G(c) × F(c), where f acts by (y,x) ↦
(G(f)y + D(f)x, F(f)x). -/
@[local simp]
def extension : ShortComplex (AbFunctor C) where
  X₁ := G
  X₂ :=
    { obj c := AddCommGrpCat.of (G.obj c × F.obj c)
      map f :=
        ofHom (((G.map f).hom.coprod (D.component f).hom).prod
          ((F.map f).hom.comp (AddMonoidHom.snd ..)))
      map_id c := by
        -- the cocycle rule at `𝟙 c ≫ 𝟙 c` reads `D(𝟙) = D(𝟙) + D(𝟙)`
        have h_zero : D.component (𝟙 c) = 0 := by simpa using D.cocycle_comp (𝟙 c) (𝟙 c)
        aesop
      map_comp := by aesop (add simp [cocycle_comp, add_assoc]) }
  X₃ := F
  f := { app _ := ofHom (AddMonoidHom.inl ..) }
  g := { app _ := ofHom (AddMonoidHom.snd ..) }

lemma shortExact_extension : D.extension.ShortExact := by
  -- at each object `c` the sequence is `G c → G c × F c → F c`, by `inl` and `snd`
  refine (shortExact_of_app (fun c ↦ ?_) (fun c ↦ ?_) fun c ↦ ?_).2 <;> aesop_cat

/-- For a cocycle D from F to G, the class in Ext^1(F,G) of its extension G → E → F, viewed in
the total Ext group. -/
noncomputable abbrev cohomClass : TotalH F G := toTotalH D.shortExact_extension.extClass

/-- The class of a cocycle `D` compared with that of a short exact sequence `S`. Let
`α : F ⟶ S.X₃` and `β : G ⟶ S.X₁`, and let `σ c : F(c) → S.X₂(c)` lift `α` at each object `c`.
If the failure of `σ` to be natural along `f : c ⟶ d` is `D(f)` carried into `S.X₂(d)` by `β`
and `S.f`, then the class of `D` followed by `β` is `α` followed by the class of `S`. -/
lemma cohomClass_comp_eq_extClass {S : ShortComplex (AbFunctor C)} (hS : ShortExact S)
    (α : F ⟶ S.X₃) (β : G ⟶ S.X₁) (σ : ∀ c : C, F.obj c ⟶ S.X₂.obj c)
    (h_lift : ∀ c : C, σ c ≫ S.g c = α c)
    (h_cocycle : ∀ (c d : C) (f : c ⟶ d),
      σ c ≫ S.X₂.map f = D.component f ≫ β d ≫ S.f d + F.map f ≫ σ d) :
    D.cohomClass.comp (TotalH.homClass β) = pullbackAlong α hS.extClass.toTotalH := by
  -- Map `D.extension.X₂ = G × F` to `S.X₂` by `β ≫ S.f` on `G` and `σ` on `F`. This is natural
  -- by `h_cocycle` and gives a map of short exact sequences `D.extension ⟶ S`.
  let τ : D.extension.X₂ ⟶ S.X₂ :=
    { app c := ofHom (((β ≫ S.f).app c).hom.coprod (σ c).hom)
      naturality c d f := by simp [AddCommGrpCat.ext_iff, add_assoc, elementwise_of% h_cocycle] }
  have h_left : β ≫ S.f = D.extension.f ≫ τ := by aesop
  have h_right : τ ≫ S.g = D.extension.g ≫ α := by
    ext
    simp [τ, ← h_lift, ← S.f.comp_app_apply]
  have h_nat : D.shortExact_extension.extClass.comp (mk₀ β) (add_zero 1) =
      (mk₀ α).comp hS.extClass (zero_add 1) :=
    D.shortExact_extension.extClass_naturality hS ⟨β, τ, α, h_left, h_right⟩
  simp [comp_of, h_nat]

/-- If `α : F ⟶ F'` and `β : G ⟶ G'` intertwine the cocycles `D` and `D'`, the class of `D`
followed by `β` is `α` followed by the class of `D'`. -/
lemma cohomClass_naturality (D' : Cocycle F' G') (α : F ⟶ F') (β : G ⟶ G')
    (h_comm : ∀ (c d : C) (f : c ⟶ d), α.app c ≫ D'.component f = D.component f ≫ β.app d) :
    D.cohomClass.comp (TotalH.homClass β) = pullbackAlong α D'.cohomClass := by
  -- `α` lifts to `D'.extension.X₂ = G' × F'` by `x ↦ (0, α x)`
  let σ (c : C) : F.obj c ⟶ D'.extension.X₂.obj c := α.app c ≫ ofHom (AddMonoidHom.inr ..)
  refine D.cohomClass_comp_eq_extClass D'.shortExact_extension α β σ (fun c ↦ rfl) fun c d f ↦ ?_
  -- on `G'` this is `h_comm`, on `F'` the naturality of `α`
  have h_cd (x : F.obj c) : D'.component f (α.app c x) = β.app d (D.component f x) :=
    AddCommGrpCat.ext_iff.mp (h_comm c d f) x
  simp [σ, AddCommGrpCat.ext_iff, h_cd]

/-- Restricting the class of `D` along a functor `φ : C ⥤ C` gives the class of the cocycle
`f ↦ D(φ f)`. -/
lemma map_cohomClass_restrict {φ : C ⥤ C} :
    D.cohomClass.map (restrictAlong φ) =
      cohomClass ⟨fun f ↦ by exact D.component (φ.map f), by simp [cocycle_comp]⟩ :=
  map_extClass D.shortExact_extension

end Cocycle

end New.Variety

/-!
## Contraction of exterior algebras along a semilinear map

* `New.Variety.contraction_one`, `New.Variety.contraction_ι_mul`: the recursion that determines
  `New.Variety.contraction φ`.
-/

section Contraction

open ExteriorAlgebra CliffordAlgebra

namespace New.Variety

variable {T T' M M' : Type} [CommRing T] [CommRing T'] [AddCommGroup M] [AddCommGroup M']
  [Module T M] [Module T' M'] {a : T →+* T'} (φ : M →ₛₗ[a] T' × M')

/-- The map `exteriorMap m` acts on the scalar (degree zero) part through the ring map `a`. -/
lemma algebraMapInv_exteriorMap (m : M →ₛₗ[a] M') (x : ExteriorAlgebra T M) :
    algebraMapInv (exteriorMap m x) = a (algebraMapInv x) := by
  induction x using left_induction with
  | algebraMap r => simp [algebraMapInv, Algebra.algebraMap_eq_smul_one]
  | add x x' ih ih' => simp [ih, ih']
  | ι_mul x m ih => simp [algebraMapInv]

/-- Contraction with `φ₀` for a semilinear map `φ = (φ₀, φ₁) : M → T' × M'`. It is the map
`⋀ M → ⋀ (T' × M')` induced by `φ`, followed by contraction with the first projection and then the
map to `⋀ M'`. -/
noncomputable def contraction : ExteriorAlgebra T M →ₛₗ[a] ExteriorAlgebra T' M' where
  toFun :=
    ExteriorAlgebra.map (LinearMap.snd T' T' M') ∘
      CliffordAlgebra.contractLeft (LinearMap.fst T' T' M') ∘ exteriorMap φ
  map_add' := by simp
  map_smul' := by simp

@[simp]
lemma contraction_one : contraction φ 1 = 0 := by simp [contraction]

/-- For semilinear φ: M→T'×M', the map of exterior algebras ΛM→ΛM' induced by the second
component M→M' of φ. -/
noncomputable abbrev exteriorMapSnd : ExteriorAlgebra T M →+* ExteriorAlgebra T' M' :=
  exteriorMap (LinearMap.snd T' T' M' ∘ₛₗ φ)

/-- The recursion: contracting `m ∧ x` gives `φ₀ m` times the image of `x`, minus `φ₁ m ∧` the
contraction of `x`. -/
@[simp]
lemma contraction_ι_mul (m : M) (x : ExteriorAlgebra T M) :
    contraction φ (ExteriorAlgebra.ι T m * x) =
      (φ m).1 • exteriorMapSnd φ x - ExteriorAlgebra.ι T' (φ m).2 * contraction φ x := by
  have h_snd :
      ExteriorAlgebra.map (LinearMap.snd T' T' M') (exteriorMap φ x) = exteriorMapSnd φ x := by
    induction x using left_induction with
    | algebraMap r => simp [Algebra.algebraMap_eq_smul_one]
    | add x x' ih ih' => simp [ih, ih']
    | ι_mul x m ih => simp [ih]
  simp [contraction, contractLeft_ι_mul, h_snd]

/-- The graded Leibniz rule for `contraction φ` along the ring map `exteriorMapSnd φ`. The sign
when the contraction passes `x` comes from the grade involution `exteriorMap s`, induced by the
map `s = -1` on `M'`. -/
lemma contraction_mul {s : M' →ₗ[T'] M'} (hs : ∀ m : M', s m = -m) (x y : ExteriorAlgebra T M) :
    contraction φ (x * y) =
      exteriorMap s (exteriorMapSnd φ x) * contraction φ y +
        contraction φ x * exteriorMapSnd φ y := by
  induction x using left_induction with
  | algebraMap => simp [Algebra.algebraMap_eq_smul_one]
  | add x x' ih ih' =>
    simp only [add_mul, map_add, ih, ih']
    abel
  | ι_mul x m ih =>
    -- Expand both sides by `contraction_ι_mul`; the sign comes from `s m = -m`.
    simp [ih, hs, mul_assoc, mul_add, sub_mul]
    abel

end New.Variety

end Contraction
