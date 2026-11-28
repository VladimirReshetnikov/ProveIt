import Lib.General.Algebra.LongExactSequences

/-!
# Criteria for comparison maps of Ext cohomology of functors of points to be bijective

For a set-valued functor of points `Y` on a category `C` with coefficients `F`, cohomology is
`Hⁿ(Y, F) = New.Variety.H (freeAb.obj Y) F n`, an `Ext` group in functors to abelian groups, where
`ℤ[Y]` is the free abelian functor on `Y`; `reprBy A` is the functor `B ↦ (A ⟶ B)` (lifted), and a
point `y` of `Y A` gives `pointMap y : reprBy A ⟶ Y`, `f ↦ Y.map f y`. A comparison `c = (φ, β)`
with `φ : C' ⥤ C` and `β : φ ⋙ F ⟶ F'`, together with a map `u : Y' ⟶ φ ⋙ Y`, gives maps
`c.pull (freeAbMap u) n : Hⁿ(Y, F) → Hⁿ(Y', F')`. The file gives criteria for these maps to be
bijective. The tools are dévissage and Čech descent along covers, and pointwise descriptions of
bijections and pull-back squares. The file also builds cocycle classes from witnesses of a relation
`R ⊆ V × L`, relative to a subfunctor `U ⊆ V`, by a Čech-type complex.

## Main definitions and results

* `New.Variety.witnessed.universalClass`, `New.Variety.witnessed.cocycleClass`: splicing the short
  exact sequences into which the complex of points with witnesses splits gives a universal class;
  its push-forward along a cocycle with values in `F` is a class in `Extⁿ(ℤ[V]/ℤ[U], F)`.
* `New.Variety.cech_descent_step`, `New.Variety.Devissage.allBijective_freeAb_range_of_cech`: Čech
  descent of bijectivity from `E` and its fibre powers `New.Variety.cech p m` to the image of
  `p : E ⟶ Y`.
* `New.Variety.IsCover`: `p` is a cover for `F`, that is, the inclusion of its image induces
  bijections on all `Extⁿ(ℤ[-], F)`; pointwise surjections are covers
  (`New.Variety.IsPointwiseSurjective.isCover`).
* `New.Variety.Comparison.IsBijective`: for a natural map `α : N' ⟶ c.functor ⋙ N`, the maps
  `c.pull α n : Extⁿ(N, F) → Extⁿ(N', F')` are bijective in all degrees; for `α = freeAbMap u` these
  are the maps `Hⁿ(Y, F) → Hⁿ(Y', F')`.
* `New.Variety.Comparison.isBijective_of_fibres`: it is enough to test on the fibres over the points
  of `Y`; the proof is Čech descent (`New.Variety.Comparison.bijectiveUpTo_of_cech_pred`), one
  condition of `New.Variety.BijectiveUpTo` at a time.
* `New.Variety.Comparison.HasUniversalPoints.isBijective`: representable fibres with equal
  coefficients (`New.Variety.Comparison.IsUnivPoint`) suffice;
  `New.Variety.Comparison.isBijective_of_adj` is the case of an adjunction.

Notions from other files:
* `New.Variety.H`: The group Ext^n(N,F) in the category of functors from C to abelian groups;
  `H.map F α n` is the pull-back along α: N' → N and `H.push N β n` the push-forward along β:
  F → F'.
* `New.Variety.Comparison`: A comparison from F on C to F' on C' is a functor φ: C' → C with a map
  β: F∘φ → F'. For α: N' → N∘φ, `Comparison.pull` is the map Ext^n(N,F) → Ext^n(N',F') that
  restricts along φ, pushes by β and pulls by α.
* `New.Variety.BijectiveUpTo`: For maps f_n: A_n → B_n, the first r of the conditions: f₀ injective,
  f₀ surjective, f₁ injective, f₁ surjective, and so on.
* `New.Variety.IsCohomEquiv`: α: N' → N is an equivalence for F: the pull-back
  Ext^n(N,F) → Ext^n(N',F) is bijective for every n.
* `New.Variety.freeAbMap`: For u: Y' → Y∘φ, the induced map of free abelian group functors
  Z[Y'] → Z[Y]∘φ.

## Relation to the literature

Known; see `Lib.Cohomology.Hodge.FixedPointFormula` and `Lib.Cohomology.Etale.FilteredLimits` for
sources.
-/

noncomputable section

namespace New.Variety

/-!
## Witnesses, a Čech-type resolution and the universal cocycle class

Cohomology classes from witnesses. A relation `R ⊆ V × L` between functors of points gives each
point `x` of `V` a set of witnesses `l`. A subfunctor `U ⊆ V` consists of points that have one. The
chains on tuples `(x, l₁, …, lₘ)` form a Čech-type complex, exact in positive degrees.
-/

section WitnessCocycles

open CategoryTheory MonoidalCategory Abelian.Ext FreeAbelianGroup QuotientAddGroup Fin ShortComplex
  abCoker H freeAb

variable {C : Type _} [Category C] {m n : ℕ} {V L : C ⥤ Type _} (R : Subfunctor (V ⊗ L))

-- Needed: without it, instance search fails on the quotient groups in
-- `shortExact_boundaryFromCoker` and several later steps fail.
set_option backward.isDefEq.respectTransparency false

/-! ### The complex of points with witnesses -/

/-- The functor of points with `m` witnesses: a point `x` of `V` together with `m` points `l i`
of `L` such that each pair `(x, l i)` lies in `R`. -/
def witnessed (m : ℕ) : C ⥤ Type _ where
  obj A := {t : V.obj A × (Fin m → L.obj A) // ∀ i : Fin m, (t.fst, t.snd i) ∈ R.obj A}
  map f := ↾fun t ↦
    ⟨(V.map f t.val.fst, fun i ↦ L.map f (t.val.snd i)), fun i ↦ R.map f (t.property i)⟩

namespace witnessed

/-- Reindexing the witnesses of a point along `g`: the `i`-th new witness is the `g i`-th old
one. -/
def reindexWitness (g : Fin m → Fin n) : witnessed R n ⟶ witnessed R m where
  app _ := ↾fun t ↦ ⟨(t.val.fst, t.val.snd ∘ g), fun i ↦ t.property (g i)⟩

/-- The boundary map from chains with `m + 1` witnesses to chains with `m` witnesses: the
alternating sum of the maps that drop one witness. -/
def boundary (m : ℕ) : freeAb.obj (witnessed R (m + 1)) ⟶ freeAb.obj (witnessed R m) :=
  ∑ j : Fin (m + 1), (-1) ^ j.val • freeAb.map (reindexWitness R j.succAbove)

/-- The boundary of a boundary is zero. -/
lemma boundary_comp_boundary (m : ℕ) : boundary R (m + 1) ≫ boundary R m = 0 := by
  cases m with
  | zero =>
    -- Dropping the two witnesses of a point in either order gives the same point.
    simpa [boundary, add_neg_eq_zero] using freeAb.hom_ext
  | succ m =>
    -- The points with `m + 1` witnesses, for all `m`, form a simplicial object, and `boundary`
    -- is the differential of its alternating face map complex.
    exact AlgebraicTopology.AlternatingFaceMapComplex.d_squared
      (.mk _ (fun g ↦ reindexWitness R g.unop) ⋙ freeAb) m

/-- The map induced by the boundary, from the chains with `m + 1` witnesses modulo boundaries to
the chains with `m` witnesses. -/
def boundaryFromCoker (m : ℕ) : abCoker (boundary R (m + 1)) ⟶ freeAb.obj (witnessed R m) :=
  desc (α := boundary R (m + 1)) (boundary R m) (boundary_comp_boundary R m)

lemma proj_comp_boundaryFromCoker (m : ℕ) :
    π (boundary R (m + 1)) ≫ boundaryFromCoker R m = boundary R m :=
  rfl

/-- The natural isomorphism from points with `0` witnesses to points of `V` that forgets the empty
tuple of witnesses. -/
def noWitness : witnessed R 0 ≅ V :=
  NatIso.ofComponents fun A ↦
    ((Equiv.subtypeUnivEquiv fun _ ↦ nofun).trans
      (Equiv.prodUnique (V.obj A) (Fin 0 → L.obj A))).toIso

variable {R}

/-- A point of `V` that has a witness is a boundary, as a chain without witnesses. -/
lemma proj_boundary_of_eq_zero {A : C} {t : (witnessed R 0).obj A}
    (h_wit : ∃ l : L.obj A, (t.val.fst, l) ∈ R.obj A) :
    (π (boundary R 0)).app A (of t) = 0 := by
  obtain ⟨l, hl⟩ := h_wit
  -- `t` is the boundary of the same point with the one witness `l`.
  refine (eq_zero_iff _).2 ⟨of ⟨(t.val.fst, fun _ ↦ l), fun _ ↦ hl⟩, ?_⟩
  simp [boundary, reindexWitness, Subsingleton.elim _ t.val.snd]

/-- With `Cₘ` the chains on points with `m` witnesses, the sequence
`0 → Cₘ₊₁/∂Cₘ₊₂ → Cₘ → Cₘ/∂Cₘ₊₁ → 0` is short exact. -/
lemma shortExact_boundaryFromCoker :
    ∃ w : boundaryFromCoker R m ≫ π (boundary R m) = 0,
      (ShortComplex.mk (boundaryFromCoker R m) (π (boundary R m)) w).ShortExact := by
  refine shortExact_of_app (fun A ↦ ?_) (fun A x ↦ ?_) fun _ ↦ mk_surjective
  · -- Injectivity. Let `c` put a chosen witness (if there is one) in front of the others. It is a
    -- contraction, `c ∂ t + ∂ c t = t`, so `c` induces a left inverse of `boundaryFromCoker`.
    let c m := lift fun t : (witnessed R m).obj A ↦ ∑ᶠ h : ∃ l, (t.1.1, l) ∈ R.obj A,
      @of ((witnessed R (m + 1)).obj A) ⟨(t.1.1, cons h.choose t.1.2), cases h.choose_spec t.2⟩
    have h_contr (t : (witnessed R (m + 1)).obj A) :
        (boundary R (m + 1)).app A (-c _ (of t)) = c m ((boundary R m).app A (of t)) - of t := by
      have h_wit : ∃ l, (t.1.1, l) ∈ R.obj A := ⟨_, t.2 0⟩
      simp [c, h_wit, boundary, sum_app_apply, -NatTrans.app_sum, reindexWitness]
      simp [pow_succ, sum_univ_succ]
      rfl
    have h_inv : AddMonoidHom.mk' (mk' _ ∘ c m ∘ (boundary R m).app A) (by simp) =
        mk' ((boundary R (m + 1)).app A).hom.range :=
      lift_ext _ _ fun t ↦ eq_iff_sub_mem.2 ⟨_, h_contr t⟩
    exact Function.HasLeftInverse.injective ⟨fun x ↦ ⟦c m x⟧, Quot.ind (DFunLike.congr_fun h_inv)⟩
  · -- Exactness in the middle: `boundaryFromCoker` has the same image as `boundary`.
    exact (eq_zero_iff x).trans (.symm exists_mk)

lemma boundaryFromCoker_comp_π : boundaryFromCoker R m ≫ π (boundary R m) = 0 :=
  shortExact_boundaryFromCoker.fst

lemma shortExact_boundaryFromCoker_π :
    ShortExact (ShortComplex.mk (boundaryFromCoker R m) (π (boundary R m))
      boundaryFromCoker_comp_π) :=
  shortExact_boundaryFromCoker.snd

variable {U : Subfunctor V} (hU : ∀ A : C, ∀ x ∈ U.obj A, ∃ l : L.obj A, (x, l) ∈ R.obj A)
  {F : AbFunctor C} {C' : Type 1} [Category C'] {F' : AbFunctor C'} {V' L' : C' ⥤ Type _}
  {R' : Subfunctor (V' ⊗ L')} {U' : Subfunctor V'}
  (hU' : ∀ A : C', ∀ x ∈ U'.obj A, ∃ l : L'.obj A, (x, l) ∈ R'.obj A)

/-! ### The class of a cocycle -/

/-- The map `x ↦ [x]` from `ℤ[V]/ℤ[U]` to the chains without witnesses modulo boundaries. It is
well defined because every point of `U` has a witness. -/
def fromRel : relFreeAb U ⟶ abCoker (boundary R 0) :=
  desc (freeAb.map (noWitness R).inv ≫ π (boundary R 0))
    (freeAb.hom_ext fun A x ↦ proj_boundary_of_eq_zero (hU A x.val x.property))

/-- The universal class in degree `n`, with coefficients in the chains with `n` witnesses modulo
boundaries. In degree `0` it is the map `fromRel hU`; each further degree composes with the
extension class of the short exact sequence `shortExact_boundaryFromCoker`. -/
def universalClass : ∀ n : ℕ, H (relFreeAb U) (abCoker (boundary R n)) n
  | 0 => mk₀ (fromRel hU)
  | n + 1 => (universalClass n).comp shortExact_boundaryFromCoker_π.extClass rfl

lemma universalClass_zero : universalClass hU 0 = mk₀ (fromRel hU) :=
  rfl

lemma universalClass_succ (n : ℕ) :
    universalClass hU (n + 1) =
      (universalClass hU n).comp shortExact_boundaryFromCoker_π.extClass rfl :=
  rfl

/-- The class of a cocycle. A cocycle of degree `n` is a map `y` to `F` from the chains with `n`
witnesses modulo boundaries. Its class in `Extⁿ(ℤ[V]/ℤ[U], F)` is the push-forward of
`universalClass hU n` along `y`. -/
def cocycleClass : (abCoker (boundary R n) ⟶ F) →+ H (relFreeAb U) F n :=
  AddMonoidHom.mk' (fun y ↦ H.push (relFreeAb U) y n (universalClass hU n))
    (by simp [H.push, mk₀_add])

lemma cocycleClass_apply (y : abCoker (boundary R n) ⟶ F) :
    cocycleClass hU y = push (relFreeAb U) y n (universalClass hU n) :=
  rfl

/-! ### Naturality -/

/-- Let `γ` and `y` be compatible maps between the last two terms of short exact sequences `S`
and `T`, let `β : T.X₁ ⟶ F`, and let `x` be a class in `Extⁿ(N, S.X₃)`. Then there is a map
`z : S.X₁ ⟶ F` with `z s = β t` whenever `t` and `s` have the same image in `T.X₂`, and the
product of `y_* x` with `β_* [T]` equals `z_*` of the product of `x` with `[S]`. Here `[S]` and
`[T]` are the extension classes. -/
lemma exists_map_extClass_comp {S T : ShortComplex (AbFunctor C)} (hS : S.ShortExact)
    (hT : T.ShortExact) (β : T.X₁ ⟶ F) {N : AbFunctor C} (x : H N S.X₃ n) (γ : S.X₂ ⟶ T.X₂)
    (y : S.X₃ ⟶ T.X₃) (h_comm : S.g ≫ y = γ ≫ T.g) :
    ∃ z : S.X₁ ⟶ F,
      (∀ (A : C) (s : S.X₁.obj A) (w : F.obj A),
        (∃ t : T.X₁.obj A, T.f.app A t = γ.app A (S.f.app A s) ∧ β.app A t = w) →
          w = z.app A s) ∧
      (H.push N y n x).comp (hT.extClass.comp (mk₀ β) rfl) rfl =
        H.push N z (n + 1) (x.comp hS.extClass rfl) := by
  -- `γ` restricts to a map `z₁ : S.X₁ ⟶ T.X₁`, which completes a morphism of short exact sequences.
  have h_mono : Mono T.f := hT.mono_f
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : S.X₁ ⟶ T.X₁, z₁ ≫ T.f = S.f ≫ γ :=
    hT.exact.lift' (S.f ≫ γ) (by simp [← h_comm])
  refine ⟨z₁ ≫ β, fun A s w ⟨t, ht, hw⟩ ↦ ?_, ?_⟩
  · obtain rfl : t = z₁.app A s := ConcreteCategory.injective_of_mono_of_preservesPullback _
      (ht.trans (ConcreteCategory.congr_hom (NatTrans.congr_app hz₁ A) s).symm)
    exact hw.symm
  · simp [← comp_assoc_of_third_deg_zero,
      ← hS.extClass_naturality hT ⟨z₁, γ, y, hz₁, h_comm.symm⟩, H.push]

/-- Classes of cocycles are carried along an exact functor `Φ`. Let the maps `q m` send chains
with `m` witnesses for `R'` to the image under `Φ` of the chains with `m` witnesses for `R`,
compatibly with reindexing and, in degree `0`, with `α`. Then a cocycle `y` for `R` induces a
cocycle `y'` for `R'`, and the class of `y`, moved along `Φ`, `β` and `α`, is the class of `y'`. -/
lemma map_cocycleClass (Φ : AbFunctor C ⥤ AbFunctor C') [IsExactFunctor Φ] (β : Φ.obj F ⟶ F')
    {α : relFreeAb U' ⟶ Φ.obj (relFreeAb U)}
    (q : ∀ m : ℕ, freeAb.obj (witnessed R' m) ⟶ Φ.obj (freeAb.obj (witnessed R m)))
    (h_deg_zero : ∀ (A : C') (x : V'.obj A),
      (α ≫ Φ.map (fromRel hU)).app A (relFreeAb.mk U' x) =
        (q 0 ≫ Φ.map (π (boundary R 0))).app A (of ((noWitness R').inv.app A x)))
    (h_reindex : ∀ (m n : ℕ) (g : Fin m → Fin n),
      freeAb.map (reindexWitness R' g) ≫ q m = q n ≫ Φ.map (freeAb.map (reindexWitness R g)))
    (y : abCoker (boundary R n) ⟶ F) :
    ∃ y' : abCoker (boundary R' n) ⟶ F',
      π (boundary R' n) ≫ y' = q n ≫ Φ.map (π (boundary R n) ≫ y) ≫ β ∧
      H.map F' α n (H.push (Φ.obj (relFreeAb U)) β n ((cocycleClass hU y).mapExactFunctor Φ)) =
        cocycleClass hU' y' := by
  -- The maps `q m` commute with the boundaries, so they descend to maps `k m` of the cokernels.
  -- They form maps of the short exact sequences `shortExact_boundaryFromCoker`. Naturality of
  -- `extClass` and induction on `n` show that `universalClass hU n` is carried to the
  -- push-forward of `universalClass hU' n` along `k n`.
  have h_bd (m : ℕ) :
      boundary R' m ≫ q m = q (m + 1) ≫ Φ.map (π _) ≫ Φ.map (boundaryFromCoker R m) :=
    calc
      _ = q (m + 1) ≫ Φ.map (boundary R m) := by
        simp [boundary, Preadditive.sum_comp, Preadditive.comp_sum, h_reindex]
      _ = q (m + 1) ≫ Φ.map (π _) ≫ Φ.map (boundaryFromCoker R m) := by
        rw [← Φ.map_comp, proj_comp_boundaryFromCoker]
  let k (m : ℕ) : abCoker (boundary R' m) ⟶ Φ.obj (abCoker (boundary R m)) :=
    abCoker.desc (q m ≫ Φ.map (π _))
      (by simp [reassoc_of% h_bd, ← Φ.map_comp, shortExact_boundaryFromCoker.1])
  have h_cl (n : ℕ) : H.map _ α n ((universalClass hU n).mapExactFunctor Φ) =
      push _ (k n) n (universalClass hU' n) := by
    induction n with
    | zero =>
      simpa [universalClass_zero, H.map, H.push, mapExactFunctor_mk₀] using
        congrArg mk₀ (relFreeAb.hom_ext h_deg_zero)
    | succ n ih =>
      have hS := (shortExact_boundaryFromCoker (R := R) (m := n)).2
      have hS' := (shortExact_boundaryFromCoker (R := R') (m := n)).2
      have h_nat : hS'.extClass.comp (mk₀ (k (n + 1))) rfl =
          (mk₀ (k n)).comp (hS.map_of_exact Φ).extClass rfl :=
        hS'.extClass_naturality (hS.map_of_exact Φ)
          ⟨k (n + 1), q n, k n, (cancel_epi (π _)).1 (h_bd n).symm, rfl⟩
      have h_ih : (mk₀ α).comp ((universalClass hU n).mapExactFunctor Φ) n.zero_add =
          (universalClass hU' n).comp (mk₀ (k n)) rfl := ih
      -- Unfold one splicing step on both sides; `h_nat` moves `k` past the extension class.
      simp [universalClass_succ, ← comp_assoc (h₁₂ := n.zero_add), h_ih, h_nat, H.map, H.push,
        mapExactFunctor_comp, mapExactFunctor_extClass]
  refine ⟨k n ≫ Φ.map y ≫ β, ?_, ?_⟩
  · have h_proj : π (boundary R' n) ≫ k n = q n ≫ Φ.map (π (boundary R n)) := rfl
    rw [reassoc_of% h_proj, Φ.map_comp_assoc]
  · simpa [H.map, H.push, cocycleClass_apply, mapExactFunctor_comp, mapExactFunctor_mk₀] using
      congrArg (H.push _ (Φ.map y ≫ β) n) (h_cl n)

/-- Pull-back of the class of a cocycle along a comparison `c`. Let `u` map points and `v` map
witnesses so that the relation `R'` goes to `R`, and let `α` be induced by `u`. If the cocycle
`y'` is `y` read through `u` and `v` and followed by the coefficient map of `c`, then the class of
`y` pulls back to the class of `y'`. -/
lemma pull_cocycleClass (c : Comparison F F') (u : V' ⟶ c.functor ⋙ V) (v : V' ⊗ L' ⟶ c.functor ⋙ L)
    (hR : ∀ A : C', ∀ x ∈ R'.obj A, (u.app A x.1, v.app A x) ∈ R.obj (c.functor.obj A))
    {y : abCoker (boundary R n) ⟶ F} {y' : abCoker (boundary R' n) ⟶ F'}
    (hy : ∀ (A : C') (t : (witnessed R' n).obj A),
      c.coeffHom.app A ((π (boundary R n) ≫ y).app (c.functor.obj A)
          (of ⟨(u.app A t.1.1, fun i : Fin n ↦ v.app A (t.1.1, t.1.2 i)),
            fun i : Fin n ↦ hR A _ (t.2 i)⟩)) =
        (π (boundary R' n) ≫ y').app A (of t))
    {α : relFreeAb U' ⟶ c.functor ⋙ relFreeAb U}
    (hα : ∀ (A : C') (x : V'.obj A),
      α.app A (relFreeAb.mk U' x) = relFreeAb.mk U (u.app A x)) :
    c.pull α n (cocycleClass hU y) = cocycleClass hU' y' := by
  -- `u` and `v` map a point with witnesses for `R'` to a point with witnesses for `R`.
  let q (m : ℕ) : witnessed R' m ⟶ c.functor ⋙ witnessed R m :=
    { app A := ↾fun t ↦
        ⟨(u.app A t.1.1, fun i ↦ v.app A (t.1.1, t.1.2 i)), fun i ↦ hR A _ (t.2 i)⟩
      naturality A B f := by
        ext
        congrm ⟨($(u.naturality f) _, fun i ↦ $(v.naturality f) (_, _)), _⟩ }
  -- On points without witnesses `q 0` is `u`, which induces `α`.
  have h_deg_zero (A : C') (x : V'.obj A) :
      (α ≫ (restrictAlong c.functor).map (fromRel hU)).app A (relFreeAb.mk U' x) =
        (freeAbMap (q 0) ≫ (restrictAlong c.functor).map (π _)).app A
          (of ((noWitness R').inv A x)) := by
    refine (congrArg _ (hα A x)).trans
      (congrArg (fun t ↦ (π (boundary R 0)).app _ (FreeAbelianGroup.of t)) ?_)
    exact Subtype.ext (Prod.ext rfl (funext nofun))
  obtain ⟨z, hz, h_coc⟩ :=
    map_cocycleClass hU hU' (restrictAlong c.functor) c.coeffHom (fun m ↦ freeAbMap (q m))
      h_deg_zero
      (fun _ _ _ ↦ hom_ext) y
  -- The induced cocycle `z` is `y'`: they agree on generators by `hy`.
  obtain rfl : z = y' := (cancel_epi (π _)).1 (hz.trans (hom_ext hy))
  exact h_coc

end witnessed

end WitnessCocycles

/-!
## Closed classes, dévissage, Čech descent and covers

* `New.Variety.IsClosedClass`: the class P of functors D → Ab contains 0 and, along a short exact
  sequence whose subobject is in P, contains the middle term exactly when it contains the quotient.
* `New.Variety.Devissage`: the five and four lemmas for a family of maps f_{N,n};
  `New.Variety.Comparison.devissage` shows that comparison maps of Ext groups have them.

`New.Variety.cech p m` is the (m+1)-fold fibre power of `E` over `Y`.
-/

section CechDescent

open CategoryTheory MonoidalCategory Subfunctor ShortComplex CartesianMonoidalCategory witnessed
  abCoker cech Function Limits

variable {C C' D : Type _} [Category C] [Category C'] [Category D] {Y E : D ⥤ Type 1}
  (F) (p : E ⟶ Y) {P : D ⥤ Ab → Prop} {A B : (D ⥤ Ab.{1}) → ℕ → Type*}
  (f : ∀ (N : D ⥤ Ab) (n : ℕ), A N n → B N n)

/-! ### Closed classes -/

/-- A closed class P of functors D → Ab: (a) P contains every zero functor N (written `𝟙 N = 0`);
(b) for a short exact sequence 0 → X₁ → X₂ → X₃ → 0 with X₁ in P, the middle term X₂ is in P exactly
when the quotient X₃ is. Nothing is asked about X₁ when X₂ and X₃ are in P. -/
def IsClosedClass (P : (D ⥤ Ab.{1}) → Prop) : Prop :=
  (∀ N : D ⥤ Ab, 𝟙 N = 0 → P N) ∧
  ∀ S : ShortComplex (CategoryTheory.Functor.{_, 1, _, 2} D Ab),
    ShortExact S → P S.X₁ → (P S.X₂ ↔ P S.X₃)

/-- A closed class P is invariant under isomorphism: for an isomorphism g : M → N, P holds for M
exactly when it holds for N. Proof: apply (b) to 0 → ker g → M → N → 0, whose kernel is zero. -/
lemma IsClosedClass.iff_of_isIso (hP : IsClosedClass P) {M N : D ⥤ Ab} (g : M ⟶ N) [IsIso g] :
    P M ↔ P N := by
  obtain ⟨h_zero, h_short⟩ := hP
  exact h_short _ ⟨exact_kernel g⟩ (h_zero _ ((isZero_kernel_of_mono g).eq_of_src (𝟙 _) 0))

/-- If N is a zero object (its identity is zero), then every group Extⁿ(N, F) has at most one
element. -/
lemma H.subsingleton_of_id_eq_zero {N : AbFunctor C} (h_id : 𝟙 N = 0) (F : AbFunctor C) (n : ℕ) :
    Subsingleton (H N F n) := by
  -- every class is its composite with the identity of `N`, which is zero
  refine ⟨fun x y ↦ ?_⟩
  rw [← x.mk₀_id_comp, ← y.mk₀_id_comp]
  simp [h_id]

/-- The stepwise four lemma for the family f: along every short exact sequence 0 → X₁ → X₂ → X₃ → 0,
the first r conditions of `New.Variety.BijectiveUpTo` at X₂ and the first r − 1 at X₁ give the first
r at X₃. -/
structure StepwiseFourLemma where
  /-- The first r conditions at X₂ and the first r − 1 at X₁ give the first r at X₃. -/
  bijectiveUpTo_quotient {X : ShortComplex (CategoryTheory.Functor.{_, 1, _, 2} D Ab)} {r : ℕ} :
      ShortExact X → BijectiveUpTo (f X.X₂) r → BijectiveUpTo (f X.X₁) (r - 1) →
        BijectiveUpTo (f X.X₃) r

/-! ### Dévissage -/

/-- The five and four lemmas for a family of maps f_{N,n} : A N n → B N n, indexed by functors N :
D → Ab and degrees n, as for a map of contravariant δ-functors. In `bijectiveUpTo_quotient`, `r - 1`
is subtraction of natural numbers; for r = 0 there is no condition. -/
structure Devissage extends StepwiseFourLemma f where
  /-- Five lemma: the functors on which `f` is bijective in all degrees form a closed class. -/
  isClosedClass : IsClosedClass (AllBijective <| f ·)

/-- For a comparison (φ,β) from F to F', exact functors Φ, Φ' and a natural map η: Φ'N → (ΦN)∘φ,
the induced maps Ext^n(ΦN,F) → Ext^n(Φ'N,F') have the five- and four-lemma properties
`New.Variety.Devissage`. -/
lemma Comparison.devissage {F : AbFunctor C} {F' : AbFunctor C'} (c : Comparison F F')
    (Φ : (D ⥤ Ab) ⥤ C ⥤ AddCommGrpCat) {Φ' : (D ⥤ Ab) ⥤ C' ⥤ AddCommGrpCat}
    (η : Φ' ⟶ Φ ⋙ restrictAlong c.functor) [IsExactFunctor Φ] [IsExactFunctor Φ'] :
    Devissage fun (N : D ⥤ Ab) (n : ℕ) ↦ c.pull (η N) n := by
  -- A short exact sequence gives a morphism of long exact sequences; the four and five lemmas
  -- `LongExactSeq.Hom.four_lemma` and `LongExactSeq.Hom.five_lemma` apply to it.
  have ladder (X : ShortComplex (D ⥤ Ab.{1})) (hX : X.ShortExact) :
      (LongExactSeq.contravariant (hX.map_of_exact Φ) F).Hom
        (LongExactSeq.contravariant (hX.map_of_exact Φ') F')
        (c.pull (X.mapNatTrans η).τ₃) (c.pull (X.mapNatTrans η).τ₂)
        (c.pull (X.mapNatTrans η).τ₁) :=
    c.pull_hom_contravariant (hX.map_of_exact Φ) (hX.map_of_exact Φ') (mapNatTrans X η)
  refine
    { bijectiveUpTo_quotient := fun hX ↦ (ladder _ hX).four_lemma
      isClosedClass := ⟨fun N hN n ↦ ?_, fun X hX ↦ (ladder X hX).five_lemma⟩ }
  -- For `N = 0` both cohomology groups are trivial.
  have h_sub : Subsingleton (H (Φ.obj N) F n) :=
    H.subsingleton_of_id_eq_zero (by simp [← Φ.map_id, hN]) F n
  have h_sub' : Subsingleton (H (Φ'.obj N) F' n) :=
    H.subsingleton_of_id_eq_zero (by simp [← Φ'.map_id, hN]) F' n
  exact ⟨injective_of_subsingleton _, surjective_to_subsingleton _⟩

variable {f}

/-- The projection from the one-fold fibre power `cech p 0` to E is an isomorphism. -/
instance : IsIso (proj p 0 0) :=
  (isoOfAppBijective _ fun _ ↦
    ((Equiv.subtypeUnivEquiv (by simp)).trans (.funUnique (Fin 1) _)).bijective).isIso_hom

/-- Čech descent, for a family of maps f_{N,n} : A N n → B N n indexed by functors N : D → Ab and
degrees n. Suppose that, in short exact sequences, r conditions of
`New.Variety.BijectiveUpTo` on the middle term and r − 1 on the kernel give r on the quotient. Then
r on Z[E] and r − 1 on all fibre powers of p give r on Z[im p]. -/
theorem cech_descent_step (h_four : StepwiseFourLemma f) {r : ℕ}
    (hE : BijectiveUpTo (f (freeAb E)) r)
    (h_cech : ∀ m : ℕ, BijectiveUpTo (f (freeAb (cech p m))) (r - 1)) :
    BijectiveUpTo (f (freeAb (range p).toFunctor)) r := by
  -- Let `R` relate a point of the image to the points of `E` over it. The points of the image with
  -- `m + 1` witnesses for `R` form the fibre power `cech p m`.
  let R : Subfunctor ((range p).toFunctor ⊗ E) :=
    Subfunctor.equalizer (ι ⊤ ≫ snd _ _ ≫ p) (ι ⊤ ≫ fst _ _ ≫ (range p).ι)
  -- `e` forgets the point of the image, which is recovered as `p` of the first witness.
  let e (m : ℕ) : witnessed R (m + 1) ≅ cech p m := NatIso.ofComponents fun A ↦ Equiv.toIso
    { toFun := fun ⟨⟨y, x⟩, h_wit⟩ ↦ ⟨x, fun i j ↦ (h_wit i).2.trans (h_wit j).2.symm⟩
      invFun := fun ⟨x, h_fibre⟩ ↦
        ⟨(⟨p.app A (x 0), x 0, rfl⟩, x), fun i ↦ ⟨⟨⟩, h_fibre i 0⟩⟩
      left_inv := fun ⟨⟨y, x⟩, h_wit⟩ ↦ Subtype.ext (Prod.ext (Subtype.ext (h_wit 0).2) rfl) }
  -- The four lemma for the short exact sequence `shortExact_boundaryFromCoker_π`, its last two
  -- terms changed by isomorphisms.
  have h_four_iso {m k : ℕ} {P K : D ⥤ Ab} (eP : freeAb (witnessed R m) ≅ P)
      (eK : abCoker (boundary R m) ≅ K) :
      BijectiveUpTo (f P) k →
      BijectiveUpTo (f (abCoker (boundary R (m + 1)))) (k - 1) →
      BijectiveUpTo (f K) k := by
    have h_comp_zero :
        (boundaryFromCoker R m ≫ eP.hom) ≫ eP.inv ≫ π (boundary R m) ≫ eK.hom = 0 := by
      simp [reassoc_of% boundaryFromCoker_comp_π]
    exact h_four.bijectiveUpTo_quotient (X :=
      ⟨boundaryFromCoker R m ≫ eP.hom, eP.inv ≫ π _ ≫ eK.hom, h_comp_zero⟩)
      (shortExact_of_iso (isoMk (.refl (abCoker _)) eP eK) shortExact_boundaryFromCoker_π)
  -- By induction on `k`, for all `m` at once: if `k` conditions hold on the fibre powers, they
  -- hold on the chains with at least two witnesses modulo boundaries.
  have h_cok (k : ℕ) (hk : ∀ m : ℕ, BijectiveUpTo (f (freeAb (cech p m))) k) (m : ℕ) :
      BijectiveUpTo (f (abCoker (boundary R (m + 2)))) k := by
    induction k generalizing m with
    | zero => simp [BijectiveUpTo]
    | succ k ih =>
      exact h_four_iso (freeAb.mapIso (e _)) (.refl _) (hk _)
        (ih (by grind [BijectiveUpTo]) _)
  -- Every point of the image has a witness, so every chain without witnesses is a boundary and
  -- the chains with one witness modulo boundaries are `freeAb` of the image.
  have h_zero : π (boundary R 0) = 0 := by
    refine freeAb.hom_ext fun A t ↦ proj_boundary_of_eq_zero ?_
    obtain ⟨x, h_px⟩ := t.val.1.property
    exact ⟨x, ⟨⟩, h_px⟩
  have h_iso : IsIso (boundaryFromCoker R 0) :=
    shortExact_boundaryFromCoker_π.isIso_f_iff.2 (.of_epi_eq_zero _ h_zero)
  exact h_four_iso (freeAb.mapIso (e 0 ≪≫ asIso (proj p 0 0)))
    (asIso (boundaryFromCoker R 0) ≪≫ freeAb.mapIso (noWitness R)) hE (h_cok _ h_cech 0)

/-- Čech descent: if the maps f obey the five and four lemmas (`New.Variety.Devissage`) and are
bijective in all degrees on ℤ[-] of every fibre power of p: E → Y, E included, then they are so
on ℤ[im p]. -/
lemma Devissage.allBijective_freeAb_range_of_cech (h_dev : Devissage f)
    (h_cech : ∀ m : ℕ, AllBijective (f (freeAb (cech p m)))) :
    AllBijective (f (freeAb (range p).toFunctor)) := by
  -- the first fibre power `cech p 0` is isomorphic to `E`
  have hE : AllBijective (f (freeAb E)) :=
    (h_dev.isClosedClass.iff_of_isIso (freeAb.map (proj p 0 0))).mp (h_cech 0)
  simp only [allBijective_iff_forall_bijectiveUpTo] at hE h_cech ⊢
  exact fun r ↦ cech_descent_step p h_dev.toStepwiseFourLemma (hE r) (h_cech · (r - 1))

/-- p: E → Y is a cover for F: the inclusion of the image of p in Y induces bijections on
Ext^n(Z[−],F) for all n. -/
def IsCover : Prop := IsCohomEquiv F (freeAb.map (Subfunctor.range p).ι)

lemma IsPointwiseSurjective.isCover {F : AbFunctor D} (hp : IsPointwiseSurjective p) :
    IsCover F p := by
  -- `range p` is all of `Y`, so its inclusion is an isomorphism
  have : IsIso (range p).ι := (range p).eq_top_iff_isIso.1 (by aesop : range p = ⊤)
  exact .of_isIso _

end CechDescent

/-!
## Pointwise bijections and pull-back squares of set-valued functors

* `New.Variety.IsCohomEquiv.of_bijective`: a map that is bijective at every object induces
  bijections on all `Extⁿ(ℤ[-], F)`.
* `New.Variety.isPullback_iff`: a square is a pull-back exactly when it commutes and is a pull-back
  of sets at every object; fibre products and fibre powers give such squares.
-/

section BijectiveEquivalence

open CategoryTheory Limits cech fibreProd Fin

variable {C : Type _} [Category C] {Y E W V : C ⥤ Type 1} {p : E ⟶ Y} {u : W ⟶ Y} {q : V ⟶ W}
  {v : V ⟶ E}

/-- A map `p : E ⟶ Y` that is bijective at every object is an isomorphism, so `ℤ[E] ⟶ ℤ[Y]` is an
equivalence for every coefficient functor `F`. -/
lemma IsCohomEquiv.of_bijective {F : AbFunctor C} (hp_bij : AllBijective fun B : C ↦ p B) :
    IsCohomEquiv F (freeAb.map p) :=
  of_isIso (freeAb.map (isoOfAppBijective p hp_bij).hom)

/-- A square of functors is a pull-back if and only if it commutes and is a pull-back on points at
every object. -/
@[local simp]
lemma isPullback_iff :
    IsPullback v q p u ↔
      (∀ (B : C) (z : V.obj B), p B (v B z) = u B (q B z)) ∧
      ∀ (B : C) (w : W.obj B) (x : E.obj B),
        p B x = u B w → ∃! z : V.obj B, q B z = w ∧ v B z = x := by
  -- Object by object, a pull-back of sets is a commuting square in which each compatible pair
  -- `(x, w)` has a point over it, and at most one.
  have h_app : IsPullback v q p u ↔ ∀ B : C,
      (∀ z : V.obj B, p B (v B z) = u B (q B z)) ∧
      (∀ z₁ z₂ : V.obj B, v B z₁ = v B z₂ → q B z₁ = q B z₂ → z₁ = z₂) ∧
      ∀ (x : E.obj B) (w : W.obj B), p B x = u B w → ∃ z : V.obj B, v B z = x ∧ q B z = w := by
    simp [IsPullback.iff_app, Types.isPullback_iff, ConcreteCategory.hom_ext_iff]
  grind [ExistsUnique]

/-- The fibre product of `u : W ⟶ Y` and `p : E ⟶ Y` with its two projections is a pull-back
square. -/
lemma isPullback_fibreProd : IsPullback (snd u p) (fst u p) p u := by
  simp_all [fibreProd, fst, snd, ExistsUnique]

/-- The fibre power with `m + 2` factors is the pull-back of `p` along the fibre power with `m + 1`
factors, by the first coordinate `proj p (m + 1) 0` (`proj p m i` is the `i`-th coordinate map of
`cech p m` to `E`) and the map that drops the first coordinate: a tuple is its first coordinate
together with the remaining ones. -/
lemma isPullback_cech {m : ℕ} :
    IsPullback (Y := cech p m) (proj p (m + 1) 0)
      { app _ := ↾fun e ↦ ⟨fun j : Fin (m + 1) ↦ e.val j.succ, by grind⟩ } p (proj p m 0 ≫ p) := by
  -- The point over a tuple `a` and a point `x` is the tuple `a` with `x` put in front.
  refine isPullback_iff.mpr
    ⟨fun _ e ↦ e.property _ _, fun B a x (hx : p.app B x = p.app B (a.val 0)) ↦ ?_⟩
  -- the tuple `x, a 0, …, a m` lies in the fibre power, since all its entries lie over `p x`
  let b : Fin (m + 1 + 1) → E.obj B := cons x a.val
  have h_b : ∀ i j : Fin (m + 1 + 1), p.app B (b i) = p.app B (b j) := by
    simp [b, forall_fin_succ, hx, a.property _ 0]
  refine ⟨⟨b, h_b⟩, ⟨rfl, rfl⟩, ?_⟩
  -- it is the only one: a tuple is its first coordinate followed by the others
  rintro z ⟨rfl, rfl⟩
  exact Subtype.ext (cons_self_tail z.val).symm

end BijectiveEquivalence

/-! ## Bijective comparisons: representable case, fibres, universal points -/

section BijectiveComparisons

open CategoryTheory Abelian Function Functor Subfunctor Ext H IsCohomEquiv ConcreteCategory cech
  Arrow BijectiveUpTo sigma IsPointwiseSurjective fibreProd Iso

variable {C C' C'' : Type 1} [Category C] [Category C'] [Category C'']
  {F G N : AbFunctor C} {F' G' N' : AbFunctor C'} {F'' N'' : AbFunctor C''} {Y E : C ⥤ Type 1}
  {Y' E' : C' ⥤ Type 1} {r : ℕ} {φ : C' ⥤ C} (c : Comparison F F') {A : C} {B : C'}
  (u : Y' ⟶ c.functor ⋙ reprBy A)

/-! ### Bijective comparisons and representable functors -/

/-- For a comparison (φ,β) from F to F' and α: N' → N∘φ, the property that Ext^n(N,F) →
Ext^n(N',F') is bijective for every n. -/
def Comparison.IsBijective {N : AbFunctor C} {N' : AbFunctor C'} (α : N' ⟶ c.functor ⋙ N) : Prop :=
  ∀ n : ℕ, Bijective (c.pull (N := N) (N' := N') α n)

/-- A map α: N → G of functors from C to abelian groups is an equivalence for F if and only if
the identity comparison from F to itself is bijective along α in every degree. -/
lemma isCohomEquiv_iff_isBijective {α : N ⟶ G} :
    IsCohomEquiv F α ↔ (Comparison.id F).IsBijective α := by
  simp [IsCohomEquiv, Comparison.IsBijective]

alias ⟨IsCohomEquiv.bij, Comparison.IsBijective.eqv⟩ := isCohomEquiv_iff_isBijective

lemma H.push_bijective_of_isIso {γ : F ⟶ G} (hγ : IsIso γ) (n : ℕ) : Bijective (push N γ n) :=
  bijective_of_isIso ((extFunctorObj N n).map γ)

lemma pointMap_comp (y : E.obj A) (p : E ⟶ Y) : pointMap y ≫ p = pointMap (p A y) := by
  ext
  apply p.naturality_apply

/-- If `Y` is represented by `B` through the point `z`, then `freeAb.obj Y` is projective and
maps from it to `F` are determined bijectively by the image of `z` in `F.obj B`. -/
lemma projective_and_eval_bijective (F : C ⥤ Ab) {B : C} (z : Y.obj B)
    (hz : AllBijective fun A : C ↦ pointMap z A) :
    Projective (freeAb Y) ∧ Bijective fun s : freeAb Y ⟶ F ↦ s B (FreeAbelianGroup.of z) := by
  -- `Y` is represented by `B`, so both claims come from `reprBy B`, the second by Yoneda
  let e : freeAb Y ≅ freeAb (reprBy B) := freeAb.mapIso (isoOfAppBijective _ hz).symm
  -- write `z` as `Y.map (𝟙 B) z`, the form in which the Yoneda equivalence returns it
  rw [← Y.map_id_apply B z]
  exact ⟨e.retract.projective, (e.homFromEquiv.trans (homReprEquiv B F).toEquiv).bijective⟩

/-- For a fully faithful functor `ψ : C ⥤ C'` and an object `c`, the functor
`d ↦ (ψ c ⟶ ψ d)` is represented by `c` through the identity of `ψ c`: the point map of the
identity is bijective at every object. -/
lemma pointMap_id_bijective_of_fullyFaithful (ψ : C ⥤ C') [ψ.Full] [ψ.Faithful] (c : C) :
    AllBijective fun d : C ↦
      pointMap (Y := ψ ⋙ reprBy (ψ.obj c)) (A := c) ⟨𝟙 (ψ.obj c)⟩ d := by
  intro d
  -- on `d` the map sends `f : c ⟶ d` to `𝟙 _ ≫ ψ.map f`
  have hψ : Bijective (ψ.map : (c ⟶ d) → _) := ⟨ψ.map_injective, ψ.map_surjective⟩
  exact ULift.map_bijective.mpr ((Iso.refl _).homFromEquiv.bijective.comp hψ)

namespace Comparison

/-- For `u : Y' ⟶ c.functor ⋙ reprBy A`, which sends a point `y` of `Y' B` to a map
`A ⟶ c.functor B`, the homomorphism `F A → (ℤ[Y'] ⟶ F')` that sends `x` (via the Yoneda bijection
`homReprEquiv A F : (ℤ[reprBy A] ⟶ F) ≃ F A`) to the section taking `y` to
`c.coeffHom B (F.map (u y) x)`. -/
noncomputable def homOfValue : F.obj A →+ (freeAb.obj Y' ⟶ F') :=
  AddMonoidHom.mk' (fun x ↦ freeAbMap u ≫ whiskerLeft c.functor ((homReprEquiv A F).symm x) ≫
    c.coeffHom)
    (by bound)

variable {c} {c' : Comparison F' F''} {α : N' ⟶ c.functor ⋙ N} {α' : N'' ⟶ c'.functor ⋙ N'}

/-- Let c, c' be comparisons from F to F' and F' to F'', with c' bijective in all degrees along α'.
Then c is bijective along α exactly if the composite comparison is bijective along γ, the composite
of α' with α whiskered by `c'.functor`. -/
lemma IsBijective.trans_iff (h_bij' : c'.IsBijective α') {γ : N'' ⟶ c'.functor ⋙ c.functor ⋙ N}
    (hγ : α' ≫ whiskerLeft c'.functor α = γ) :
    (c.trans c').IsBijective γ ↔ c.IsBijective α := by
  -- in each degree the composite comparison is that of `c` followed by a bijection
  simp [IsBijective, ← (h_bij' _).of_comp_iff', comp_def, pull_trans, hγ]

/-- Bijective comparisons compose: if `c` is bijective along `α` and `c'` along `α'`, the composite
comparison is bijective along the composite `γ` of `α'` with `α` whiskered by `c'.functor`. -/
lemma IsBijective.trans (h_bij : c.IsBijective α) (h_bij' : c'.IsBijective α')
    {γ : N'' ⟶ c'.functor ⋙ c.functor ⋙ N} (hγ : α' ≫ whiskerLeft c'.functor α = γ) :
    (c.trans c').IsBijective γ :=
  (h_bij'.trans_iff hγ).mpr h_bij

/-- Let `γ : F ⟶ G` and `γ' : F' ⟶ G'` be isomorphisms of coefficient functors. Let
`β : c.functor ⋙ G ⟶ G'` satisfy `β ∘ γ = γ' ∘ c.coeffHom`. Then `c` is bijective along `α` in all
degrees if and only if the comparison `(c.functor, β)` from `G` to `G'` is. -/
lemma isBijective_iff_of_coeff_iso {β : c.functor ⋙ G ⟶ G'} (γ : F ⟶ G) (γ' : F' ⟶ G') [IsIso γ]
    [IsIso γ'] (w : whiskerLeft c.functor γ ≫ β = c.coeffHom ≫ γ') :
    c.IsBijective α ↔ IsBijective ⟨c.functor, β⟩ α := by
  -- the two comparisons differ by the maps induced by `γ` and `γ'`, which are bijective
  simp [IsBijective, bijective_iff_of_comm_sq (c.pull_push β γ γ' w _), push_bijective_of_isIso]

lemma homOfValue_app (x : F.obj A) (B : C') (y : Y'.obj B) :
    c.homOfValue u x B (FreeAbelianGroup.of y) = c.coeffHom B (F.map (u B y).down x) := by
  -- by definition the left side is `c.coeffHom B` applied to `F.map (u B y).down x + 0`
  rw [← add_zero (F.map (u B y).down x)]
  rfl

attribute [instance] subsingleton_of_projective

variable {u}

/-- For `u : Y' ⟶ c.functor ⋙ reprBy A`, the comparison `Hⁿ(ℤ[reprBy A], F) → Hⁿ(ℤ[Y'], F')` is
bijective for all `n` if and only if `c.homOfValue u : F A → (ℤ[Y'] ⟶ F')` is bijective and
`Hⁿ(ℤ[Y'], F') = 0` for all `n ≥ 1`. -/
lemma isBijective_reprBy_iff :
    c.IsBijective (freeAbMap u) ↔
      Bijective (c.homOfValue u) ∧ ∀ n : ℕ, Subsingleton (H (freeAb Y') F' (n + 1)) := by
  -- treat degree zero and the positive degrees separately
  refine Nat.and_forall_add_one.symm.trans (.and ?_ (forall_congr' fun n ↦ ?_))
  · -- in degree zero the classes are morphisms, and the comparison is `c.homOfValue u` by Yoneda
    let e : H (freeAb.obj (reprBy A)) F 0 ≃ F.obj A := homEquiv₀.trans (homReprEquiv A F).toEquiv
    have h_square (x : F.obj A) : c.pull (freeAbMap u) 0 (e.symm x) = mk₀ (c.homOfValue u x) := by
      simp [e, pull, H.map, H.push, mapExtAddHom, mapExactFunctor_mk₀, homOfValue]
    exact (bijective_iff_of_comm_sq h_square e.symm.bijective (mk₀_bijective ..)).symm
  · -- in positive degree the source vanishes, as `freeAb.obj (reprBy A)` is projective
    exact ⟨fun h ↦ h.surjective.subsingleton,
      fun h ↦ ⟨injective_of_subsingleton _, fun y ↦ ⟨0, h.allEq _ y⟩⟩⟩

/-- Let `Y'` be represented by `B` through the point `z`, and let `u z : A ⟶ φ B` (the map under
`ULift`). If `c.coeffHom B ∘ F.map (u z) : F A → F' B` is bijective, the comparison along `u` is
bijective in all degrees. -/
lemma isBijective_of_repr (z : Y'.obj B) (hz : AllBijective fun D : C' ↦ pointMap z D)
    (h_coeff : Bijective fun x : F.obj A ↦ c.coeffHom B (F.map (u B z).down x)) :
    c.IsBijective (freeAbMap u) := by
  obtain ⟨h_proj, h_eval⟩ := projective_and_eval_bijective F' z hz
  -- sections on `Y'` are read at the point `z`, which turns `c.homOfValue u` into `h_coeff`
  have h_hom : Bijective (c.homOfValue u) := by
    rw [← h_eval.of_comp_iff']
    simpa [comp_def, homOfValue_app] using h_coeff
  -- the higher groups vanish, as `freeAb Y'` is projective
  exact isBijective_reprBy_iff.mpr ⟨h_hom, fun n ↦ inferInstance⟩

end Comparison

end BijectiveComparisons

section ComparisonDescent

open CategoryTheory Abelian Function Functor Subfunctor Ext H IsCohomEquiv ConcreteCategory cech
  Arrow BijectiveUpTo sigma IsPointwiseSurjective fibreProd Iso

variable {C C' : Type 1} [Category C] [Category C'] {F : AbFunctor C} {F' : AbFunctor C'}
  {Y E : C ⥤ Type 1} {Y' E' : C' ⥤ Type 1} {r : ℕ} {φ : C' ⥤ C} {c : Comparison F F'}
  {u : Y' ⟶ c.functor ⋙ Y} {v : E' ⟶ c.functor ⋙ E} {p : E ⟶ Y} {p' : E' ⟶ Y'}

namespace Comparison

/-- If the comparison is bijective along `u` and `p' : E' ⟶ Y'` is bijective at every object,
then it is bijective along `v = p' ≫ u`. -/
lemma IsBijective.precomp_of_bijective (h_bij : c.IsBijective (freeAbMap u))
    {v : E' ⟶ c.functor ⋙ Y}
    (p' : E' ⟶ Y') (w : p' ≫ u = v) (hp' : AllBijective fun B : C' ↦ p' B) :
    c.IsBijective (freeAbMap v) := by
  -- a bijection `p'` is an equivalence; compose its comparison with that along `u`
  subst w
  exact h_bij.trans (of_bijective hp').bij (freeAb.hom_ext fun _ _ ↦ rfl)

/-! ### Descent: covers and fibres -/

/-- The Čech step. Let `p : E ⟶ Y` and `p' : E' ⟶ Y'` be covers for `F` and `F'`, and let
`v : E' ⟶ c.functor ⋙ E` lift `u : Y' ⟶ c.functor ⋙ Y` to them (`w : p' ≫ u = v ≫ p`). Suppose that
(a) the comparison along `v` is bijective in all degrees and (b) on every fibre power `cech p m`
(`m + 1` factors) the comparison along the map `cech p' m ⟶ c.functor ⋙ cech p m` induced by
`(v, u)` satisfies the first `r - 1` conditions of `New.Variety.BijectiveUpTo`. Then the comparison
along `u` satisfies the first `r`. -/
lemma bijectiveUpTo_of_cech_pred (w : p' ≫ u = v ≫ c.functor.whiskerLeft p) (hp : IsCover F p)
    (hp' : IsCover F' p') (hv : c.IsBijective (freeAbMap v))
    (h_cech : ∀ m : ℕ, BijectiveUpTo (fun n : ℕ ↦ c.pull (freeAbMap (Y := cech p m)
      (Y' := cech p' m) ((cechFunctor m).map (homMk' v u w.symm))) n) (r - 1)) :
    BijectiveUpTo (fun n : ℕ ↦ c.pull (freeAbMap u) n) r := by
  -- The map of covers `(v, u)`, seen as a map of functors to arrows, lets every functor `N` on
  -- arrows be evaluated on `p` and on `p'`, with a map `τ N` between the results.
  let τ :
      (whiskeringLeft _ _ Ab).obj (toArrowFunctor (.mk p')) ⟶
        (whiskeringLeft _ _ Ab).obj (toArrowFunctor (.mk p)) ⋙ restrictAlong c.functor :=
    (whiskeringLeft _ _ Ab).map (toArrowFunctor.map (homMk' v u w.symm))
  -- The comparisons along `τ` obey the four lemma (`Comparison.devissage`), so Čech descent for the
  -- universal map `leftToRight` on the category of arrows gives the claim for the images of `p'`
  -- and `p`.
  have h_range :
      BijectiveUpTo (fun n : ℕ ↦ c.pull (τ (freeAb (range leftToRight).toFunctor)) n) r :=
    cech_descent_step leftToRight (c.devissage _ τ).toStepwiseFourLemma
      (allBijective_iff_forall_bijectiveUpTo.mp hv r) h_cech
  -- The images have the same cohomology as `Y'` and `Y`.
  exact (BijectiveUpTo.congr hp hp' (map_pull_eq_pull_map (freeAb.hom_ext fun _ _ ↦ rfl))).mpr
    h_range

/-- Let `u : Y' ⟶ c.functor ⋙ Y` and `t : E ⟶ Y`, and let `v : E' ⟶ c.functor ⋙ E`, with
`p' : E' ⟶ Y'`, be the pull-back of `u` along `t`. Suppose that for every point `x` of `E A` the
comparison is bijective in all degrees along the projection to `c.functor ⋙ reprBy A` of the fibre
product of `u` with the point `reprBy A ⟶ Y` given by `t x`. Then it is bijective along `v`. -/
lemma isBijective_of_fibres (t : E ⟶ Y) (h_pb : IsPullback v p' (c.functor.whiskerLeft t) u)
    (h_fibre : ∀ (A : C) (x : E.obj A),
      c.IsBijective (freeAbMap (snd u (whiskerLeft c.functor (pointMap (t A x)))))) :
    c.IsBijective (freeAbMap v) := by
  -- Induction on the number `r` of conditions, for all base changes at once, by Čech descent
  -- along the cover `q` of `E` by the representable functors of all its points and the cover `q'`
  -- of `E'` by the fibres of `v` over these points.
  refine allBijective_iff_forall_bijectiveUpTo.mpr fun r ↦ ?_
  induction r generalizing Y Y' E E' with
  | zero => simp [BijectiveUpTo]
  | succ r ih =>
    -- The fibre of `v` over `x` is the fibre of `u` over `t x`, by pasting of pull-backs.
    have h_fib (A : C) (x : E A) :
        c.IsBijective (freeAbMap (snd v (whiskerLeft _ (pointMap x)))) := by
      have h_fibre_tx : c.IsBijective (freeAbMap (snd u (whiskerLeft _ (pointMap x ≫ t)))) := by
        rw [pointMap_comp x t]
        exact h_fibre A x
      let i : c.functor ⋙ reprBy A ⟶ c.functor ⋙ E := whiskerLeft c.functor (pointMap x)
      have h_pasted : IsPullback (snd v i) (fst v i ≫ p') (i ≫ whiskerLeft c.functor t) u :=
        isPullback_fibreProd.paste_vert h_pb
      exact h_fibre_tx.precomp_of_bijective _
        (h_pasted.isoIsPullback_hom_fst _ _ isPullback_fibreProd)
        fun B ↦ (Iso.app _ B).toEquiv.bijective
    let repr (x : E.Elements) : C ⥤ Type 1 := reprBy x.obj
    let fib (x : E.Elements) : C' ⥤ Type 1 := fibreProd v (whiskerLeft _ (pointMap x.val))
    let q : sigma repr ⟶ E := desc fun x ↦ pointMap x.val
    let q' : sigma fib ⟶ E' := desc fun x ↦ fst v (whiskerLeft _ (pointMap x.val))
    have hq : IsPointwiseSurjective q := fun A y ↦ ⟨⟨⟨y⟩, ⟨𝟙 A⟩⟩, E.map_id_apply A y⟩
    -- a point `y` of `E'` is hit by the point `(y, 𝟙)` of the fibre of `v` over `v y`
    have hq' : IsPointwiseSurjective q' := fun B y ↦
      ⟨⟨⟨v B y⟩, (y, ⟨𝟙 _⟩), (E.map_id_apply ..).symm⟩, rfl⟩
    -- On the disjoint unions the comparison is the product of the bijections `h_fib`
    -- (`sigma_bijective`: cohomology turns disjoint unions into products).
    let v₁ : sigma fib ⟶ c.functor ⋙ sigma repr :=
      desc fun x ↦ snd v (whiskerLeft _ (pointMap x.val)) ≫ whiskerLeft _ (ι repr x)
    have hv₁ : c.IsBijective (freeAbMap v₁) := by
      intro n
      refine (bijective_iff_of_comm_sq (fun z ↦ funext fun x ↦ (map_pull_eq_pull_map ?_ n z).symm)
        (sigma_bijective ..) (sigma_bijective ..)).mpr (.piMap fun x ↦ h_fib x.obj x.val n)
      -- on the summand `x`, the map `v₁` is the second projection of the fibre over `x`
      exact freeAb.hom_ext fun _ _ ↦ rfl
    have h_sq : q' ≫ v = v₁ ≫ whiskerLeft _ q := by
      -- a point of a fibre product has the same image under both of its projections
      ext B ⟨x, ⟨_, h_lies⟩⟩
      exact h_lies
    -- The map of the fibre powers is a base change of `v`, so `ih` applies to it.
    have h_cech_pullback (m : ℕ) :
        IsPullback ((cechFunctor m).map (homMk' v₁ v h_sq.symm)) (proj q' m 0 ≫ q')
          (c.functor.whiskerLeft (proj q m 0 ≫ q)) v := by
      refine isPullback_iff.mpr
        ⟨fun B z ↦ (z.val 0).snd.property.symm, fun B y g hg ↦ ⟨?_, ?_, ?_⟩⟩
      · -- over a point `y` of `E'` and a tuple `g` lies the tuple that puts `y` beside each
        -- `g i`: each `g i` has the image of `g 0` in `E`, which is `v y`
        exact ⟨fun i ↦ ⟨(g.val i).fst, (y, (g.val i).snd), hg.symm.trans (g.property 0 i)⟩,
          fun _ _ ↦ rfl⟩
      · -- this tuple lies over `y` and over `g`
        exact ⟨rfl, rfl⟩
      · -- it is the only one: the points of `E'` in a tuple of the fibre power are all equal
        rintro z ⟨⟨⟩, ⟨⟩⟩
        refine Subtype.ext (funext fun i ↦ ?_)
        exact Sigma.ext rfl (heq_of_eq (Subtype.ext (Prod.ext (z.property i 0) rfl)))
    exact bijectiveUpTo_of_cech_pred h_sq hq.isCover hq'.isCover hv₁ fun m ↦
      ih (proj q m 0 ≫ q) (h_cech_pullback m) fun A z ↦ h_fib A _

/-! ### Universal points -/

variable (c u) in
/-- Let `u : Y' ⟶ c.functor ⋙ Y` and let `y` be a point of `Y A`. A pair `(z, f)` of a point `z` of
`Y' D` and a map `f : A ⟶ c.functor D` lies over `y` if `u z = f y`. The pair `(x, s)` over `B` is a
universal point if it is universal among these pairs, so that `B` represents the fibre of `u` over
`y`, and the coefficients `F A` and `F' B` agree along `s`. -/
structure IsUnivPoint {A : C} (y : Y.obj A) {B : C'} (x : Y'.obj B) (s : A ⟶ c.functor.obj B) :
  Prop where
  /-- The pair `(x, s)` lies over `y`. -/
  apply_eq_map : u B x = Y.map s y
  /-- Every pair `(z, f)` that lies over `y` comes from `(x, s)` by exactly one map `g`. -/
  existsUnique_hom (D : C') (z : Y'.obj D) (f : A ⟶ c.functor.obj D) (hz : u D z = Y.map f y) :
    ∃! g : B ⟶ D, Y'.map g x = z ∧ s ≫ c.functor.map g = f
  /-- The map `F A → F (c.functor B) → F' B` on coefficients is bijective. -/
  coeff_bijective : Bijective fun a : F.obj A ↦ c.coeffHom B (F.map s a)

variable (c u) in
/-- The map `u : Y' ⟶ c.functor ⋙ Y` has universal points: over every point of `Y` there is a
universal point (`New.Variety.Comparison.IsUnivPoint`), at which the coefficients agree. -/
def HasUniversalPoints : Prop :=
  ∀ (A : C) (y : Y.obj A), ∃ (B : C') (x : Y'.obj B) (s : A ⟶ c.functor.obj B),
    c.IsUnivPoint u y x s

/-- If u: Y' → Y∘φ has universal points (`New.Variety.Comparison.HasUniversalPoints`), then for
every t: E → Y the comparison is bijective in all degrees along the pull-back v: E' → E∘φ of u along
t, with p': E' → Y'. Indeed, for every point y of E the fibre of v over y is the fibre of u over
t y, which is represented by a universal point over t y. -/
lemma HasUniversalPoints.isBijective_of_isPullback (h_points : c.HasUniversalPoints u)
    (p' : E' ⟶ Y') (t : E ⟶ Y) (h_pb : IsPullback v p' (c.functor.whiskerLeft t) u) :
    c.IsBijective (freeAbMap v) := by
  -- The fibre of `u` over `t y` is represented by the universal point `(x, f)`.
  refine isBijective_of_fibres t h_pb fun A y ↦ ?_
  obtain ⟨B, x, f, h_univ⟩ :
      ∃ (B : C') (x : Y'.obj B) (f : A ⟶ c.functor.obj B), c.IsUnivPoint u (t A y) x f :=
    h_points A (t A y)
  refine isBijective_of_repr ⟨(x, ⟨f⟩), h_univ.apply_eq_map⟩
    (fun D ↦ (bijective_iff_existsUnique _).mpr fun z ↦ ?_) h_univ.coeff_bijective
  -- A point `z` of the fibre comes from `(x, f)` by exactly one map `B ⟶ D`.
  refine (Equiv.ulift.existsUnique_congr fun g ↦ ⟨?_, ?_⟩).mpr
    (h_univ.existsUnique_hom D _ _ z.property)
  · -- the map `g` carries the universal point to its image
    rintro rfl
    exact ⟨rfl, rfl⟩
  · -- the two equations determine the point of the fibre
    rintro ⟨h_map, h_comp⟩
    exact Subtype.ext (Prod.ext h_map (ULift.down_injective h_comp))

/-- If there are universal points on which the coefficients agree, the comparison along `u` is
bijective in all degrees. -/
lemma HasUniversalPoints.isBijective (h_points : c.HasUniversalPoints u) :
    c.IsBijective (freeAbMap u) :=
  h_points.isBijective_of_isPullback _ (𝟙 _) .of_id_snd

/-- If the comparison c has universal points for u: Y' → Y∘φ
(`New.Variety.Comparison.HasUniversalPoints`), then for every subfunctor U of Y the comparison is
bijective in all degrees along the restricted map u⁻¹(U∘φ) → U∘φ. -/
lemma HasUniversalPoints.isBijective_subfunctor (h_points : c.HasUniversalPoints u)
    (U : Subfunctor Y) :
    c.IsBijective (freeAbMap (Y := toFunctor U) ((U.whisker c.functor).fromPreimage u)) := by
  -- the map from the preimage of `U` to `U` is the base change of `u` along the inclusion
  refine h_points.isBijective_of_isPullback (Subfunctor.ι _) U.ι (isPullback_iff.mpr ?_)
  aesop (add simp [ExistsUnique, toFunctor])

/-- With universal points, a subfunctor `U` of `Y` has the cohomology of `Y` for `F` if and only
if its preimage `S` in `Y'` has the cohomology of `Y'` for `F'`. -/
lemma HasUniversalPoints.isCohomEquiv_incl_iff (h_points : c.HasUniversalPoints u)
    (U : Subfunctor Y) {S : Subfunctor Y'} (hS : S = (U.whisker c.functor).preimage u) :
    IsCohomEquiv F (freeAb.map U.ι) ↔ IsCohomEquiv F' (freeAb.map S.ι) := by
  subst hS
  -- the comparison is bijective on `Y` and on `U`, and commutes with the two restrictions
  have h_comm : freeAb.map ((U.whisker c.functor).preimage u).ι ≫ freeAbMap u =
      freeAbMap ((U.whisker c.functor).fromPreimage u) ≫ whiskerLeft c.functor (freeAb.map U.ι) :=
    freeAb.hom_ext fun _ _ ↦ rfl
  exact forall_congr' fun n ↦ bijective_iff_of_comm_sq (map_pull_eq_pull_map h_comm n)
    (h_points.isBijective n) (h_points.isBijective_subfunctor U n)

/-- For an adjunction `φ ⊣ U`, restriction along `U` followed by the counit identifies the
cohomology of `Y'` with coefficients `φ ⋙ F` and that of `U ⋙ Y'` with coefficients `F`. -/
lemma isBijective_of_adj {U : C ⥤ C'} (a : φ ⊣ U) :
    IsBijective (F := φ ⋙ F) ⟨U, whiskerRight a.counit F⟩ (freeAbMap (𝟙 (U ⋙ Y'))) := by
  -- Over `y` in `Y' A` the universal point is the image of `y` under the unit `A ⟶ U (φ A)`.
  refine HasUniversalPoints.isBijective fun A y ↦
    ⟨φ.obj A, Y'.map (a.unit.app A) y, a.unit.app A, rfl, fun D z f hz ↦ ?_, ?_⟩
  · -- by adjunction `f : A ⟶ U D` factors through the unit by a unique `g : φ A ⟶ D`
    obtain ⟨g, rfl, h_uniq⟩ : ∃! g : φ.obj A ⟶ D, a.unit.app A ≫ U.map g = f :=
      (a.homEquiv A D).bijective.existsUnique f
    -- and this `g` carries the universal point to `z = f y`
    exact ⟨g, ⟨by simpa using hz.symm, rfl⟩, fun g' ⟨_, h_comp⟩ ↦ h_uniq g' h_comp⟩
  · -- the map on coefficients is the identity, by the triangle identity
    have h_triangle (x : F.obj (φ.obj A)) :
        F.map (a.counit.app (φ.obj A)) (F.map (φ.map (a.unit.app A)) x) = x := by
      simp [← F.map_comp_apply]
    exact bijective_iff_has_inverse.mpr ⟨fun x ↦ x, h_triangle, h_triangle⟩

/-- If `p` and `p'` are equivalences for `F` and `F'` and `v` lifts `u` along them
(`w : p' ≫ u = v ≫ p`), the comparisons along `u` and along `v` satisfy the same conditions of
`New.Variety.BijectiveUpTo`. -/
lemma bijectiveUpTo_congr (w : p' ≫ u = v ≫ c.functor.whiskerLeft p)
    (hp_equiv : IsCohomEquiv F (freeAb.map p)) (hp'_equiv : IsCohomEquiv F' (freeAb.map p')) :
    BijectiveUpTo (fun n : ℕ ↦ c.pull (freeAbMap u) n) r ↔
      BijectiveUpTo (fun n : ℕ ↦ c.pull (freeAbMap v) n) r :=
  BijectiveUpTo.congr hp_equiv hp'_equiv (map_pull_eq_pull_map (freeAb.map_commSq ⟨w⟩).w)

/-- If `p` and `p'` are equivalences for `F` and `F'` and `v` lifts `u` along them
(`w : p' ≫ u = v ≫ p`), the comparison is bijective along `u` if and only if it is along `v`. -/
lemma isBijective_congr (w : p' ≫ u = v ≫ c.functor.whiskerLeft p)
    (hp_equiv : IsCohomEquiv F (freeAb.map p)) (hp'_equiv : IsCohomEquiv F' (freeAb.map p')) :
    c.IsBijective (freeAbMap u) ↔ c.IsBijective (freeAbMap v) := by
  calc c.IsBijective (freeAbMap u)
      ↔ ∀ r : ℕ, BijectiveUpTo (fun n : ℕ ↦ c.pull (freeAbMap u) n) r :=
        allBijective_iff_forall_bijectiveUpTo
    _ ↔ ∀ r : ℕ, BijectiveUpTo (fun n : ℕ ↦ c.pull (freeAbMap v) n) r :=
        forall_congr' fun r ↦ bijectiveUpTo_congr w hp_equiv hp'_equiv
    _ ↔ c.IsBijective (freeAbMap v) := allBijective_iff_forall_bijectiveUpTo.symm

end Comparison

end ComparisonDescent

end New.Variety

end
