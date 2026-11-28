import Lib.Cohomology.Etale.BijectiveComparisons

/-!
# Pointwise tensor product of functors, total Ext with Yoneda composition, external products

Products in the cohomology `New.Variety.H N F n = Ext^n(N, F)` of functors from `C` to abelian
groups (`New.Variety.AbFunctor C`).

* `New.Variety.abTensor`, `New.Variety.HasFlatValues`: the pointwise tensor product, exact for flat
  values.
* `New.Variety.TotalH`: the direct sum of all `Ext^n(N, F)`, with the Yoneda product
  `New.Variety.TotalH.comp` and the action `New.Variety.TotalH.map` of exact functors
  (`IsExactFunctor`: sending exact sequences to exact sequences). Pull-back and push-forward become
  products with classes of degree zero, so degrees need no tracking.
* `New.Variety.TotalH.exact_triangle`: the long exact sequence, as an exact triangle.
* `New.Variety.cup`: the external product, natural in the spaces (`New.Variety.cup_map`) and in the
  site (`New.Variety.Comparison.pull_cup`).

`comp x y` is written in diagram order: `x` in `TotalH M N`, `y` in `TotalH N F`.

Notions from other files:
* `New.Variety.H.map`, `New.Variety.H.push`: the maps Ext^n(N,F) → Ext^n(N',F) and
  Ext^n(N,F) → Ext^n(N,F') given by α: N' → N and β: F → F'.
* `New.Variety.Comparison`: a comparison from F on C to F' on C' is a functor φ: C' → C with a
  natural transformation β: F∘φ → F' (the field `coeffHom`).
* `New.Variety.Comparison.pull`: for a comparison (φ,β) and α: N' → N∘φ, the homomorphism
  Ext^n(N,F) → Ext^n(N',F') obtained by restricting along φ, pushing by β and pulling by α.
* `New.Variety.restrictAlong`: for a functor φ: C' → C and a category D, the functor N ↦ N∘φ from
  functors C → D to functors C' → D.

## Relation to the literature

Known; see `Lib.Cohomology.Hodge.FixedPointFormula` for sources.
-/

noncomputable section

namespace New.Variety

open CategoryTheory Abelian Ext TensorProduct Functor DirectSum Function H LongExactSeq

variable {C C' : Type 1} [Category C] [Category C'] {M N N' F F' G G' : AbFunctor C} {a b e n : ℕ}
  {A : Type _} [Category A] (Φ Ψ : AbFunctor C ⥤ AbFunctor C') [IsExactFunctor Φ] [IsExactFunctor Ψ]
  {f : N ⟶ F} {R : Type*} [Ring R] [CoeffAction R F] {S : ShortComplex (AbFunctor C)}

/-! ### The pointwise tensor product and flat functors -/

@[ext high]
lemma addCommGrp_tensor_hom_ext {A B X : Ab} {f g : .of (A ⊗[ℤ] B) ⟶ X}
    (h : ∀ (a : A) (b : B), f (a ⊗ₜ b) = g (a ⊗ₜ b)) :
    f = g :=
  AddCommGrpCat.hom_ext (AddMonoidHom.toIntLinearMap_injective (ext' h))

/-- For homomorphisms f: A → A' and g: B → B' of abelian groups, the homomorphism f ⊗ g: A ⊗ B →
A' ⊗ B' of tensor products over ℤ. -/
abbrev abTensorMap {A B A' B' : Ab} (f : A ⟶ A') (g : B ⟶ B') :
    AddCommGrpCat.of (A ⊗[ℤ] B) ⟶ AddCommGrpCat.of (A' ⊗[ℤ] B') :=
  AddCommGrpCat.ofHom (TensorProduct.map f.hom.toIntLinearMap g.hom.toIntLinearMap).toAddMonoidHom

/-- The pointwise tensor product over ℤ of two functors from C to abelian groups, as a
bifunctor. -/
def abTensor : AbFunctor C ⥤ AbFunctor C ⥤ AbFunctor C :=
  curryObj
    { obj p :=
        { obj c := AddCommGrpCat.of (p.1.obj c ⊗[ℤ] p.2.obj c)
          map f := abTensorMap (p.1.map f) (p.2.map f) }
      map f := { app c := abTensorMap (f.1.app c) (f.2.app c) }
      map_id _ := by
        ext
        rfl
      map_comp _ _ := by
        ext
        rfl }

/-- Two maps out of a pointwise tensor product `F ⊗ G` are equal if at each object `c` they agree
on the pure tensors `a ⊗ b`. -/
lemma abTensor_hom_ext {f g : abTensor F G ⟶ G'}
    (h_tmul : ∀ (c : C) (a : F.obj c) (b : G.obj c), f c (a ⊗ₜ b) = g c (a ⊗ₜ b)) : f = g :=
  NatTrans.ext (funext fun c ↦ addCommGrp_tensor_hom_ext (h_tmul c))

/-- Every value F(c) of the functor F from C to abelian groups is a flat ℤ-module. -/
class HasFlatValues (F : AbFunctor C) where
  /-- Each value of `F` is a flat `ℤ`-module. -/
  flat (c : C) : Module.Flat ℤ (F.obj c)

instance (φ : C' ⥤ C) [HasFlatValues F] : HasFlatValues (C := C') (φ ⋙ F) :=
  ⟨fun c ↦ HasFlatValues.flat (φ.obj c)⟩

instance : (abTensor F).Additive := ⟨abTensor_hom_ext fun _ _ _ ↦ tmul_add ..⟩

instance : (abTensor.flip F).Additive := ⟨abTensor_hom_ext fun _ _ _ ↦ add_tmul ..⟩

instance [HasFlatValues F] : IsExactFunctor (abTensor F) := by
  -- Exactness is tested object by object, where it is the flatness of `F.obj c`.
  have h_exact (S : ShortComplex (AbFunctor C)) (hS : S.Exact) : (S.map (abTensor F)).Exact :=
    (exact_of_app fun c ↦ (HasFlatValues.flat c).lTensor_exact _
      (exact_of_shortComplex_exact (hS.map ((evaluation ..).obj c)))).2
  obtain ⟨_, _⟩ := ((abTensor F).exact_tfae.out 2 4 :).mp h_exact
  exact ⟨⟩

instance [HasFlatValues F] : IsExactFunctor (abTensor.flip F) := by
  -- The same argument, with the flat factor on the right.
  have h_exact (S : ShortComplex (AbFunctor C)) (hS : S.Exact) : (S.map (abTensor.flip F)).Exact :=
    (exact_of_app fun c ↦ (HasFlatValues.flat c).rTensor_exact _
      (exact_of_shortComplex_exact (hS.map ((evaluation ..).obj c)))).2
  obtain ⟨_, _⟩ := ((abTensor.flip F).exact_tfae.out 2 4 :).mp h_exact
  exact ⟨⟩

/-! ### Total cohomology and the Yoneda product -/

/-- The sum `x + y` of two classes in `Ext^a(N, F)`, as a named constant for
`New.Variety.addCommGroupH`. -/
@[reducible]
def H.add (x y : H N F a) : H N F a := x + y

/-- The abelian group structure of `Ext^a(N, F)`, equal to Mathlib's by definition. The addition is
written through `New.Variety.H.add` for elaboration only: without the named constant,
definitional equality checks on sums of classes time out in later files. -/
instance addCommGroupH : AddCommGroup (H N F a) := { Ext.instAddCommGroup with add := .add }

/-- The total Ext group, the direct sum of the Ext^n(N,F) over all n ≥ 0. -/
abbrev TotalH (N F : AbFunctor C) : Type 2 := DirectSum ℕ (H (C := C) N F)

/-- The biadditive map from total `Ext(M, N)` and total `Ext(N, F)` to total `Ext(M, F)` that
extends the Yoneda composition of homogeneous classes. The `choose` makes no real choice: it only
keeps the formula from unfolding. See `TotalH.comp_def` and `TotalH.comp_of`. -/
@[irreducible]
def TotalH.comp : TotalH M N →+ TotalH N F →+ TotalH M F :=
  (@exists_eq (TotalH M N →+ TotalH N F →+ TotalH M F)
    (toAddMonoid fun a ↦
      (toAddMonoid fun b ↦
        ((bilinearComp M N F a b (a + b) rfl).compr₂
          (DirectSum.of (H M F) (a + b))).flip).flip)).choose

/-- `comp` is the biadditive extension to the direct sums of the Yoneda compositions
`Ext^a(M, N) × Ext^b(N, F) → Ext^(a + b)(M, F)`. -/
lemma TotalH.comp_def :
    (comp : TotalH M N →+ TotalH N F →+ TotalH M F) =
      toAddMonoid fun a : ℕ ↦ (toAddMonoid fun b : ℕ ↦
        ((bilinearComp M N F a b (a + b) rfl).compr₂
          (DirectSum.of (H M F) (a + b))).flip).flip := by
  unfold comp
  exact exists_eq.choose_spec

/-- On homogeneous classes `comp` is the Yoneda composition. -/
@[local simp]
lemma TotalH.comp_of (x : H M N a) (y : H N F b) (h : a + b = n) :
    comp (DirectSum.of (H M N) a x) (DirectSum.of (H N F) b y) =
      DirectSum.of (H M F) n (x.comp y h) := by
  subst h
  simp [comp_def]

/-- A class x in Ext^n(N,F), as the element of the total group ⊕_m Ext^m(N,F) concentrated in
degree n. -/
abbrev _root_.CategoryTheory.Abelian.Ext.toTotalH (x : H N F n) : TotalH N F :=
  DirectSum.of (H N F) n x

namespace TotalH

/-- For an exact functor `Φ`, the additive map from total `Ext(N, F)` to total `Ext(Φ N, Φ F)`
obtained by applying `Φ` in each degree. See `TotalH.map_def` and `TotalH.map_of`. -/
@[irreducible]
def map : TotalH N F →+ TotalH (Φ.obj N) (Φ.obj F) :=
  (@exists_eq (TotalH N F →+ TotalH (Φ N) (Φ F)) (DirectSum.map (Φ.mapExtAddHom N F))).choose

/-- `map Φ` is the direct sum of the maps induced by `Φ` on `Ext` in each degree. -/
@[local simp]
lemma map_def :
    map Φ =
      (DirectSum.map (Φ.mapExtAddHom N F) : TotalH N F →+ TotalH (Φ.obj N) (Φ.obj F)) := by
  unfold map
  exact exists_eq.choose_spec

lemma map_map (Θ : (C' ⥤ Ab) ⥤ AbFunctor A) [IsExactFunctor (C' := A) Θ] (x : TotalH N F) :
    map Θ (map Φ x) = map (Φ ⋙ Θ) x := by aesop (add simp mapExactFunctor_mapExactFunctor)

/-- For an exact functor Φ and u in total Ext(ΦF,K), the additive map x ↦ Φx·u (Yoneda product)
from total Ext(N,F) to total Ext(ΦN,K). -/
def mapThenComp {K : AbFunctor C'} (u : TotalH (Φ F) K) : TotalH N F →+ TotalH (Φ.obj N) K :=
  (comp.flip u).comp (map (N := N) Φ)

variable {Φ Ψ} {x : TotalH M N} (r : R) (y : TotalH N F)

lemma comp_assoc (y : TotalH N F) (z : TotalH F G) : comp (comp x y) z = comp x (comp y z) := by
  -- Both sides are additive in each variable, so reduce to homogeneous classes.
  induction z using DirectSum.induction_on with
  | zero => simp
  | add z z' hz hz' => simp_all
  | of c z =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | add y y' hy hy' => simp_all
    | of b y =>
      induction x using DirectSum.induction_on with
      | zero => simp
      | add x x' hx hx' => simp_all
      | of a x => simp [add_assoc, comp_of, Ext.comp_assoc]

/-- A morphism f: N → F as a degree-zero element of total Ext(N,F). -/
abbrev homClass (f : N ⟶ F) : TotalH N F := DirectSum.of (H N F) 0 (mk₀ f)

/-- For f: N → F, the additive map from total Ext(F,G) to total Ext(N,G) given by precomposition
with f. -/
abbrev pullbackAlong (f : N ⟶ F) : TotalH F G →+ TotalH N G := comp (homClass f)

/-- On a homogeneous class `map Φ` is the image of the class under `Φ`. -/
@[simp]
lemma map_of (x : H N F a) :
    map Φ (DirectSum.of (H N F) a x) =
      DirectSum.of (H (Φ.obj N) (Φ.obj F)) a (x.mapExactFunctor Φ) := by
  simp [map_def]

lemma map_homClass : map Φ (homClass f) = homClass (Φ.map f) := by simp [mapExactFunctor_mk₀]

lemma map_comp : map Φ (comp x y) = comp (map Φ x) (map Φ y) := by
  -- Both sides are additive in `x` and `y`, so reduce to homogeneous classes.
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp_all
  | of a x =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | add y y' hy hy' => simp_all
    | of b y => simp [comp_of, mapExactFunctor_comp]

/-- An exact functor commutes with the pull-back along a morphism `f`. -/
lemma map_pullbackAlong {f : G ⟶ M} :
    map Φ (pullbackAlong f x) = pullbackAlong (Φ.map f) (map Φ x) := by
  -- `↓`: `map_comp` has to apply before the simp lemma `map_def` unfolds it.
  simp [↓map_comp, mapExactFunctor_mk₀]

/-- The class of a composite `f ≫ g` is the Yoneda product of the classes. -/
lemma homClass_comp (g : F ⟶ G) : homClass (f ≫ g) = comp (F := G) (homClass f) (homClass g) := by
  simp [comp_of]

/-- An exact functor sends the extension class of a short exact sequence `S` to the extension class
of the image sequence. -/
lemma map_extClass {S : ShortComplex (AbFunctor C)} (h : S.ShortExact) :
    map Φ h.extClass.toTotalH = (h.map_of_exact Φ).extClass.toTotalH := by
  aesop (add simp mapExactFunctor_extClass)

/-- Pulling a homogeneous class back along `f` is `New.Variety.H.map` in its degree. -/
lemma pullbackAlong_of (x : H F G n) :
    pullbackAlong f (DirectSum.of (H F G) n x) = DirectSum.of (H N G) n (H.map G f n x) := by
  simp [H.map]

/-- Composing a homogeneous class with the class of `f` is the push-forward along `f` in its
degree. -/
lemma of_comp_homClass (x : H M N n) :
    comp (DirectSum.of (H M N) n x) (homClass f) = DirectSum.of (H M F) n (push M f n x) := by
  simp [push]

@[simp]
lemma comp_id : comp x (homClass (𝟙 N)) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp_all
  | of a x => simp

/-- Pulling back along `f` is `New.Variety.H.map` in every degree. -/
lemma pullbackAlong_eq_map : pullbackAlong f = DirectSum.map (H.map G f) := by
  aesop (add simp comp_of)

lemma pullbackAlong_id : pullbackAlong (𝟙 M) x = x := by
  ext
  simp [pullbackAlong_eq_map]

lemma map_id : map (𝟭 (AbFunctor C)) x = x := by
  ext n
  -- The identity functor is restriction along the identity of `C`, which fixes every class.
  have h_id : (𝟭 (AbFunctor C)).mapExtAddHom M N n (x n) = x n :=
    mapExactFunctor_restrictAlong_id (x n)
  simpa using h_id

/-- For a natural transformation `η : Φ ⟶ Ψ` of exact functors, pushing `Φ x` along `η F` equals
pulling `Ψ x` back along `η N`. -/
lemma naturality (η : Φ ⟶ Ψ) (x : TotalH N F) :
    comp (map Φ x) (homClass (η F)) = pullbackAlong (η N) (map Ψ x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n x => simpa [H.push, H.map] using congrArg toTotalH (mapExactFunctor_naturality η x)
  | add x y hx hy => simp_all

/-- The action of a scalar `r` of `R` on the coefficients `F` (`CoeffAction R F` gives each `r` an
endomorphism `CoeffAction.act r` of `F`) is the product with the class of its action map. -/
lemma smul_eq_comp : r • y = comp y (homClass (End.asHom (CoeffAction.act r))) := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | add y y' hy hy' => simp_all
  | of a y => simp [← of_smul, smul_eq_push, push]

/-- The Yoneda product is linear in the second factor over the scalars acting on `F`. -/
lemma comp_smul : comp x (r • y) = r • comp x y := by simp [smul_eq_comp, comp_assoc]

variable {y}

/-! ### Reassociated forms -/

/-- Associativity, with the product `comp x y` given by an equation `h`. -/
lemma comp_assoc_of_eq {z : TotalH M F} (h : comp x y = z) (u : TotalH F G) :
    comp x (comp y u) = comp (F := G) z u := by
  rw [← h, comp_assoc]

/-- Pulling back along `g` and then along `f` is pulling back along `f ≫ g`. -/
lemma pullbackAlong_pullbackAlong (g : F ⟶ G) (u : TotalH G G') :
    pullbackAlong f (pullbackAlong g u) = pullbackAlong (f ≫ g) u := by
  simp [comp_assoc_of_eq]

variable (Φ) in
/-- An exact functor Φ respects Yoneda products: Φ(x·y)·u = Φx·(Φy·u) in total Ext. -/
lemma map_comp_assoc {K : AbFunctor C'} (u : TotalH (Φ.obj F) K) :
    comp (map Φ (comp x y)) u = comp (map Φ x) (comp (map Φ y) u) := by
  -- `↓`: `map_comp` has to apply before the simp lemma `map_def` unfolds it.
  simp [↓map_comp, comp_assoc_of_eq]

/-- `New.Variety.TotalH.mapThenComp` of a product `comp x y`, with `map Φ x` given by an
equation `h`. -/
lemma mapThenComp_comp {K : AbFunctor C'} {z : TotalH (Φ.obj M) (Φ.obj N)} {u : TotalH (Φ.obj F) K}
    (h : map Φ x = z) :
    mapThenComp Φ u (comp x y) = comp z (mapThenComp Φ u y) := by
  subst h
  exact map_comp_assoc Φ u

/-- If `comp x y = comp z w`, then the same holds after a product with any `u` on the right. -/
lemma comp_assoc_of_sq {z : TotalH M N'} {w : TotalH N' F} (h : comp x y = comp (N := N') z w)
    (u : TotalH F G) :
    comp x (comp y u) = comp z (comp w u) := by
  simp [comp_assoc_of_eq, h]

/-! ### The exact triangle and representable functors -/

/-- Exactness on total classes is tested degree by degree. Let `ξ` be a class in `Ext^e(M, N)` and
`ζ` a class in `Ext^b(G, M)` with `ζ · ξ = 0`, and suppose that every homogeneous class `y` in
`Ext(M, F)` with `ζ · y = 0` is zero or of the form `ξ · x`. Then composition with `ξ` followed by
composition with `ζ` is exact at total `Ext(M, F)`. -/
lemma exact_precomp {ξ : H M N e} {ζ : H G M b}
    (h_ker : ∀ {n : ℕ} {y : H M F n}, (∀ (m : ℕ) (hm : b + n = m), ζ.comp (c := m) y hm = 0) →
      y = 0 ∨ ∃ (a : ℕ) (ha : e + a = n) (x : Abelian.Ext N F a), ξ.comp (b := a) x ha = y)
    (h_comp : ζ.comp ξ rfl = 0) :
    Exact (comp (F := F) ξ.toTotalH) (comp ζ.toTotalH) := by
  classical
  -- The composite vanishes by `h_comp`. A class `y` killed by `ζ` is the sum of its homogeneous
  -- parts; each part is killed by `ζ`, so by `h_ker` it is zero or comes from `ξ`.
  have h_composite (x : TotalH N F) : comp ζ.toTotalH (comp ξ.toTotalH x) = 0 := by
    simp [← comp_assoc, comp_of ζ ξ rfl, h_comp]
  refine .of_comp_of_mem_range (funext h_composite) fun y hy ↦ ?_
  have h_part (z : TotalH M F) (n m : ℕ) (hm : b + n = m) :
      ζ.comp (z n) hm = comp ζ.toTotalH z m := by
    induction z using DirectSum.induction_on with
    | zero => simp
    | add z₁ z₂ h₁ h₂ => simp [h₁, h₂]
    | of i w =>
      subst hm
      rw [comp_of ζ w rfl]
      obtain rfl | h_ne := eq_or_ne i n
      · simp
      · simp [of_apply, h_ne]
  rw [← sum_support_of y]
  refine (comp ξ.toTotalH).range.sum_mem fun n _ ↦ ?_
  rcases h_ker (y := y n) (fun m hm ↦ by simp [h_part, hy]) with h_zero | ⟨a, ha, x, hx⟩
  · simp [h_zero]
  · exact ⟨DirectSum.of (H N F) a x, by rw [← hx, comp_of]⟩

/-- The long exact sequence of a short exact sequence `S` in the first variable, as an exact
triangle of total groups: pull-back along `S.g`, pull-back along `S.f` and composition with the
extension class are exact at each of the three vertices. -/
lemma exact_triangle (h : S.ShortExact) (F : AbFunctor C) :
    -- (a) at the classes on the middle term
    Exact (pullbackAlong (G := F) S.g) (pullbackAlong S.f) ∧
    -- (b) at the classes on the subobject
    Exact (pullbackAlong (G := F) S.f) (comp h.extClass.toTotalH) ∧
    -- (c) at the classes on the quotient
    Exact (comp (F := F) h.extClass.toTotalH) (pullbackAlong S.g) := by
  -- By `exact_precomp` it is enough to argue degree by degree, in the long exact Ext sequence `L`.
  let L := LongExactSeq.contravariant h F
  have h_f_g : (mk₀ S.f).comp (mk₀ S.g) rfl = 0 := by simp
  have h_extClass_f : h.extClass.comp (mk₀ S.f) rfl = 0 := by simp
  have h_g_extClass : (mk₀ S.g).comp h.extClass rfl = 0 := by simp
  refine ⟨exact_precomp (fun {n y} hy ↦ ?_) h_f_g,
    exact_precomp (fun {n y} hy ↦ ?_) h_extClass_f,
    exact_precomp (fun {n y} hy ↦ ?_) h_g_extClass⟩
  · exact .inr ⟨n, zero_add n, (L.exact_f_g n y).1 (hy n (zero_add n))⟩
  · exact .inr ⟨n, zero_add n, (L.exact_g_delta n y).1 (hy (n + 1) (add_comm 1 n))⟩
  · rcases n with _ | n
    · -- in degree 0 nothing comes from the extension class, but the first map is injective
      exact .inl ((injective_iff_map_eq_zero (L.f 0)).1 L.injective_f y (hy 0 rfl))
    · exact .inr ⟨n, add_comm 1 n, (L.exact_delta_f n y).1 (hy (n + 1) (zero_add (n + 1)))⟩

/-- The cohomology Ext(`freeAb (reprBy c)`, G) of the free abelian functor ℤ[Hom(c, −)] on a
representable functor is concentrated in degree zero. -/
lemma bijective_directSum_of_zero_reprBy (G : AbFunctor C) (c : C) :
    Bijective (DirectSum.of (H (freeAb (reprBy c)) G) 0) :=
  ⟨of_injective 0, fun x ↦ ⟨x 0, ext fun
    | 0 => rfl
    | _ + 1 => by subsingleton⟩⟩

/-- The Yoneda isomorphism from G(c) to the total Ext(ℤ[h_c], G), which is concentrated in
degree 0; here h_c = Hom(c, −). -/
def sectionEquiv (G : AbFunctor C) (c : C) : G c ≃+ TotalH (freeAb (reprBy c)) G :=
  -- Yoneda identifies the sections with the classes of degree zero, and these are all classes.
  (homReprEquiv c G).symm.trans
    ((addEquiv₀ (C := AbFunctor C)).symm.trans
      (AddEquiv.ofBijective _ (bijective_directSum_of_zero_reprBy G c)))

end TotalH

/-- A cohomological equivalence `f` (each pull-back `H.map G f n` is bijective) gives a bijection on
total cohomology with coefficients in `G`. -/
lemma IsCohomEquiv.bijective_pullbackAlong (h : IsCohomEquiv G f) :
    Bijective (TotalH.pullbackAlong (G := G) f) := by
  rw [TotalH.pullbackAlong_eq_map]
  exact (congrAddEquiv fun n ↦ .ofBijective _ (h n)).bijective

variable [HasFlatValues M] [HasFlatValues G] (x : TotalH M F) (y : TotalH N G) [HasFlatValues G']

/-! ### External products -/

/-- For x in total Ext(M,F), y in total Ext(N,G), with M, G of flat values, the Yoneda composite
of M ⊗ y and x ⊗ G in total Ext(M ⊗ N, F ⊗ G). -/
def TotalH.cup : TotalH ((abTensor.obj M).obj N) ((abTensor.obj F).obj G) :=
  (y.map (abTensor M)).comp (F := abTensor F G) (x.map (abTensor.flip G))

/-- Pushing the first factor along `β` pushes the external product along `β ⊗ G`. -/
lemma TotalH.cup_comp_homClass_left (β : F ⟶ F') :
    cup (comp x (homClass (F := F') β)) y = comp (cup x y) (homClass (abTensor.map β G)) := by
  simp [cup, map_comp, comp_assoc_of_eq, mapExactFunctor_mk₀]

/-- Pushing the second factor along `γ` pushes the external product along `F ⊗ γ`. -/
lemma TotalH.cup_comp_homClass_right (γ : G ⟶ G') :
    cup x (comp y (homClass (F := G') γ)) = comp (cup x y) (homClass ((abTensor F).map γ)) := by
  -- `γ` sits between the classes of `y` and `x`; naturality moves it past the class of `x`.
  have h_flip (P : AbFunctor C) : (abTensor.obj P).map γ = (abTensor.flip.map γ).app P := rfl
  rw [cup, cup, map_comp_assoc, comp_assoc, map_homClass, h_flip M, h_flip F]
  exact congrArg (comp (map (abTensor.obj M) y)) (naturality (abTensor.flip.map γ) x).symm

variable {K : AbFunctor C} (μ : abTensor F G ⟶ K) (x : H M F a) (y : H N G b)

/-- For x in Ext^a(M,F), y in Ext^b(N,G), M and G of flat values, the product in Ext^{a+b}(M ⊗
N, K): their external product pushed along μ: F ⊗ G → K. -/
def cup {n : ℕ} (h : b + a = n) : H ((abTensor.obj M).obj N) K n :=
  push ((abTensor.obj M).obj N) μ n
    ((y.mapExactFunctor (abTensor M)).comp (x.mapExactFunctor (abTensor.flip G)) h)

/-- On homogeneous classes, the external product of total classes followed by `μ` is
`New.Variety.cup`. -/
lemma TotalH.cup_of (h : b + a = n) :
    comp (cup (DirectSum.of (H M F) a x) (DirectSum.of (H N G) b y)) (homClass μ) =
      DirectSum.of (H ((abTensor.obj M).obj N) K) n (Variety.cup μ x y h) := by
  simp [cup, Variety.cup, h, push]

/-- The product `New.Variety.cup` is natural in both spaces. Here `H N F n` is `Ext^n(N, F)` for
functors from `C` to abelian groups, `⊗` is their pointwise tensor product `abTensor`, and `H.map`
is the pull-back of classes along a morphism. Let `x ∈ Ext^a(M, F)` and `y ∈ Ext^b(N, G)` with
`b + a = n`, let `μ : F ⊗ G ⟶ K`, and let `M`, `M'`, `G` have flat values. Let `α : M' ⟶ M` and
`β : N' ⟶ N`, and let `γ : L ⟶ M ⊗ N` be `γ' : L ⟶ M' ⊗ N'` followed by `α ⊗ β` (`h`). Then in
`Ext^n(L, K)` the pull-back along `γ` of the product of `x` and `y` is the pull-back along `γ'` of
the product of `α^* x` and `β^* y`. -/
lemma cup_map {M N N' F G : AbFunctor C} {a b n : ℕ} [HasFlatValues M] [HasFlatValues G]
    {K : AbFunctor C} (μ : (abTensor.obj F).obj G ⟶ K) (x : H M F a) (y : H N G b)
    {M' : AbFunctor C} [HasFlatValues M'] (hn : b + a = n) (α : M' ⟶ M) (β : N' ⟶ N)
    {L : AbFunctor C} {γ : L ⟶ (abTensor.obj M).obj N} {γ' : L ⟶ (abTensor.obj M').obj N'}
    (h : γ' ≫ (abTensor.map α).app N' ≫ (abTensor.obj M).map β = γ) :
    H.map K γ n (cup μ x y hn) =
      H.map K γ' n (cup μ (H.map F α a x) (H.map G β b y) hn) := by
  -- On the right `α` sits between the classes of `y` and `x`; naturality moves it past the class
  -- of `y` to the space, where `γ'`, `α` and `β` compose to `γ` by `h`.
  let z : H ((abTensor.obj M).obj G) K a :=
    push ((abTensor.obj M).obj G) μ a (x.mapExactFunctor (abTensor.flip.obj G))
  have h_nat :
      push ((abTensor.obj M').obj N) ((abTensor.map α).app G) b
          (y.mapExactFunctor (abTensor.obj M')) =
        H.map ((abTensor.obj M).obj G) ((abTensor.map α).app N) b
          (y.mapExactFunctor (abTensor.obj M)) :=
    mapExactFunctor_naturality (abTensor.map α) y
  calc H.map K γ n (cup μ x y hn)
      = H.map K (γ' ≫ (abTensor.obj M').map β) n
          ((H.map ((abTensor.obj M).obj G) ((abTensor.map α).app N) b
            (y.mapExactFunctor (abTensor.obj M))).comp z hn) := by
        simp [z, cup, H.push, H.map, Ext.comp_assoc, hn, h]
    _ = H.map K (γ' ≫ (abTensor.obj M').map β) n
          ((push ((abTensor.obj M').obj N) ((abTensor.map α).app G) b
            (y.mapExactFunctor (abTensor.obj M'))).comp z hn) := by
        rw [h_nat]
    _ = H.map K γ' n (cup μ (H.map F α a x) (H.map G β b y) hn) := by
        simp [z, cup, H.push, H.map, Ext.comp_assoc, hn, mapExactFunctor_comp, mapExactFunctor_mk₀]

variable {F' : AbFunctor C'} {c : Comparison F F'}

/-- Let y be the pull-back of a class x along a comparison c = (ψ, β) and A: N' → N∘ψ. Let φ be an
endofunctor of C', with s: F' → F'∘φ and α: N' → N'∘φ. If σ: ψ → ψ∘φ satisfies βφ∘Fσ = s∘β and
Aφ∘α = Nσ∘A, then restricting y along φ and pulling back along α gives the push-forward s_*y in
total Ext. -/
lemma TotalH.pull_twist {N : C ⥤ AddCommGrpCat} {N' : AbFunctor C'} {φ : C' ⥤ C'} {x : H N F n}
    {y : H N' F' n} {A : N' ⟶ c.functor ⋙ N} {s : F' ⟶ φ ⋙ F'} (h : y = c.pull A n x)
      (σ : c.functor ⟶ φ ⋙ c.functor)
    (α : N' ⟶ φ ⋙ N') (h_coeff : whiskerRight σ F ≫ φ.whiskerLeft c.coeffHom = c.coeffHom ≫ s)
    (h_space : α ≫ φ.whiskerLeft A = A ≫ whiskerRight σ N) :
    pullbackAlong α (map (restrictAlong φ) y.toTotalH) = comp y.toTotalH (homClass s) := by
  -- Both sides are pull-backs of `x`, and `σ` moves from the coefficients to the space.
  have h_move : Comparison.pull ⟨c.functor, whiskerRight σ F ≫ φ.whiskerLeft c.coeffHom⟩ A n x =
      Comparison.pull ⟨φ ⋙ c.functor, φ.whiskerLeft c.coeffHom⟩ (A ≫ whiskerRight σ N) n x := by
    rw [Comparison.pull_whiskerRight]
  simpa [h, h_space, ← h_coeff, map_def, Comparison.pull, H.map, H.push, mapExtAddHom,
    mapExactFunctor_comp, mapExactFunctor_mk₀, mapExactFunctor_mapExactFunctor] using! congrArg
    toTotalH h_move.symm

/-- For `x` in Ext^b(N ∘ Θ, F), pulling back along `c` and `η` commutes in total Ext with composing
by `ξ` in Ext^a(N', N) on `A`, restricted along `Θ` before and along `Θ'` after the pull-back. -/
lemma Comparison.pull_comp_restrictAlong {F : AbFunctor C} {a b n : ℕ} {A : Type _} [Category A]
    {N N' : AbFunctor A} {Θ : C ⥤ A} {Θ' : C' ⥤ A} {F' : AbFunctor C'} {c : Comparison F F'}
    {η : Θ' ⟶ c.functor ⋙ Θ} (ξ : H N' N a) (x : H ((restrictAlong Θ).obj N) F b) (h : a + b = n) :
    TotalH.comp (ξ.mapExactFunctor (restrictAlong Θ')).toTotalH
        (c.pull (whiskerRight η N) b x).toTotalH =
      (c.pull (whiskerRight η N') n ((ξ.mapExactFunctor (restrictAlong Θ)).comp x h)).toTotalH := by
  -- Restriction is natural in the functor of sites: `η` commutes with the image of `ξ`.
  have h_total :
      ((push _ (whiskerRight η N) a (ξ.mapExactFunctor (restrictAlong Θ'))).comp
        (push _ c.coeffHom b (x.mapExactFunctor (restrictAlong c.functor))) h).toTotalH =
      ((H.map _ (whiskerRight η N') a (ξ.mapExactFunctor (restrictAlong (c.functor ⋙ Θ)))).comp
        (push _ c.coeffHom b (x.mapExactFunctor (restrictAlong c.functor))) h).toTotalH :=
    congrArg (fun (z : H (Θ' ⋙ N') ((c.functor ⋙ Θ) ⋙ N) a) ↦ (z.comp _ h).toTotalH)
      (mapExactFunctor_naturality ((whiskeringLeft C' A AddCommGrpCat).map η) ξ)
  -- `using!`: restriction along `c.functor ⋙ Θ` and along `Θ` then `c.functor` agree only by
  -- definition.
  simpa [h, pull, H.map, H.push, mapExtAddHom, mapExactFunctor_comp,
    mapExactFunctor_mapExactFunctor, Ext.comp_assoc] using! h_total

/-- Let `c` be a comparison from `F` on `C` to `F'` on `C'`, let `η : Θ' ⟶ c.functor ⋙ Θ` be a
natural transformation, and let `x ∈ H (Θ ⋙ N) F a` and `y ∈ H (Θ ⋙ N') F b` be Ext classes with
`b + a = n`. Suppose `c` carries the multiplication `μ : F ⊗ F ⟶ F` to `μ' : F' ⊗ F' ⟶ F'` (`hμ`),
and `F`, `F'`, `N` have flat values. Then pulling back the product `cup μ x y` along `c` and `η`
gives the `μ'`-product of the pull-backs of `x` and `y` along `c` and `η`. -/
lemma Comparison.pull_cup {F : AbFunctor C} {a b n : ℕ} {A : Type _} [Category A]
    {N N' : AbFunctor A} {Θ : C ⥤ A} {Θ' : C' ⥤ A} {F' : AbFunctor C'} {c : Comparison F F'}
    {η : Θ' ⟶ c.functor ⋙ Θ} [HasFlatValues F] [HasFlatValues F'] [HasFlatValues N]
    {μ : (abTensor.obj F).obj F ⟶ F} {μ' : (abTensor.obj F').obj F' ⟶ F'} (hμ :
      (abTensor.map c.coeffHom).app (c.functor ⋙ F) ≫ (abTensor.obj F').map c.coeffHom ≫ μ' =
        c.functor.whiskerLeft μ ≫ c.coeffHom)
    (x : H (Θ ⋙ N) F a) (y : H (Θ ⋙ N') F b) (h : b + a = n) :
    c.pull (whiskerRight η ((abTensor.obj N).obj N')) n (cup μ x y h :) =
      cup μ' (c.pull (whiskerRight η N) a x) (c.pull (whiskerRight η N') b y) h := by
  -- A pull-back is restriction along `c.functor` and push along `c.coeffHom`, then pull-back along
  -- `η`; the product commutes with each of the two steps.
  let x' : H (c.functor ⋙ Θ ⋙ N) F' a := push _ c.coeffHom a
    (x.mapExactFunctor (restrictAlong c.functor))
  let y' : H (c.functor ⋙ Θ ⋙ N') F' b :=
    push _ c.coeffHom b (y.mapExactFunctor (restrictAlong c.functor))
  -- First step: `mapExactFunctor_naturality` moves the push of `y` along `c.coeffHom` past the
  -- class of `x`; there the two pushes and the pairing `μ'` compose as `hμ` says.
  have h_push :
      push _ c.coeffHom n ((cup μ x y h).mapExactFunctor (restrictAlong c.functor)) = cup μ' x' y'
        h := by
    have h_nat := congrArg (push _ ((abTensor.map c.coeffHom).app F' ≫ μ') a)
      (mapExactFunctor_naturality (abTensor.flip.map c.coeffHom)
        (x.mapExactFunctor (restrictAlong c.functor)))
    -- Simplify `h_nat` in place: stated in simplified form it would need the degree equations
    -- written out.
    simp [hμ, H.push, mapExactFunctor_mapExactFunctor, H.map] at h_nat
    simp [x', y', cup, ← h_nat, H.push, mapExactFunctor_comp, mapExactFunctor_mapExactFunctor,
      mapExactFunctor_mk₀]
    rfl -- restricting along `c.functor` commutes with `⊗` by definition
  -- Second step: `η` on a tensor product is `η` on each factor, so `cup_map` applies.
  have h_eta : 𝟙 _ ≫ (abTensor.map (whiskerRight η N)).app (Θ' ⋙ N') ≫
      (abTensor.obj _).map (whiskerRight η N') = whiskerRight η ((abTensor.obj N).obj N') :=
    abTensor_hom_ext fun _ _ _ ↦ rfl
  have h_map : H.map F' (whiskerRight η ((abTensor.obj N).obj N')) n (cup μ' x' y' h) =
      cup μ' (H.map F' (whiskerRight η N) a x') (H.map F' (whiskerRight η N') b y') h :=
    (cup_map μ' x' y' h _ _ h_eta).trans (map_id _)
  exact (congrArg (H.map F' _ n) h_push).trans h_map

end New.Variety

end
