import Lib.Cohomology.Etale.DenseSubfunctors
import Lib.Cohomology.Hodge.CupProduct

/-!
# Relative chains ℤ[V]/ℤ[U]: local isomorphisms, transfer, excision and gluing

This file provides tools for computing the groups Ext^n(N, F) (`New.Variety.H`) of functors from a
category C to abelian groups. For a subfunctor U of a set-valued functor V,
`New.Variety.relFreeAb U` is the quotient ℤ[V]/ℤ[U] of free abelian groups (`New.Variety.freeAb`).
Its Ext^n into F is the relative cohomology H^n(V, U). A map is an equivalence for F
(`New.Variety.IsCohomEquiv`) if it is bijective on all Ext^n(·, F). A subfunctor U of Y is dense
(`New.Variety.IsCohomDense`) if over every point h_A → Y its preimage gives an equivalence; with
these notions the file proves vanishing for locally zero functors, transfer, excision and gluing of
relative classes over finite covers.

## Main definitions and results

* `New.Variety.cohomology_eq_zero_of_locallyZero`, `New.Variety.isCohomEquiv_of_locallyZero`: a
  functor whose sections all die on dense sieves has no cohomology, so a map with such a kernel and
  cokernel is an equivalence.
* `New.Variety.exists_transfer_map`: the transfer attached to finitely many locally permuted maps
  (`New.Variety.permutedPairs`: the pairs on which they are permuted).
* `New.Variety.relFreeAb.shortExact_triple`, `New.Variety.relFreeAb.isCohomEquiv_of_le`,
  `New.Variety.relFreeAb.excision`: the exact sequence of a monomorphism, invariance under enlarging
  U′ to U when U′ is dense in U, and excision.
* `New.Variety.relFreeAb.exists_glued_class`: in the lowest degree where it may be nonzero, relative
  cohomology glues over a finite cover (a Mayer–Vietoris induction).
* `New.Variety.relFreeAb.prod`: the map of pairs that gives exterior products of relative classes.

Notions from other files:
* `New.Variety.isCohomEquiv_iff_subsingleton`, `New.Variety.isCohomEquiv_quotient_of_acyclic`: for
  0 → X₁ → X₂ → X₃ → 0 short exact, X₁ → X₂ is an equivalence for F exactly when all Ext^n(X₃, F)
  vanish, and X₂ → X₃ is one when all Ext^n(X₁, F) vanish.
* `New.Variety.pointMap`: The map h_A → Y from h_A = Hom(A,−) corresponding to a point y of Y(A) by
  the Yoneda lemma.

## Relation to the literature

Known; see `Lib.Cohomology.Etale.FilteredLimits` for sources.
-/

section RelativeChains

open CategoryTheory ShortComplex Function MonoidalCategory AddCommGrpCat QuotientAddGroup
  AddMonoidHom FreeAbelianGroup Fintype

namespace New.Variety

variable {C : Type 1} [Category C]
  {V V' V'' : C ⥤ Type 1} {F M N : AbFunctor C} {U : Subfunctor V} {U' : Subfunctor V'}
  {U'' : Subfunctor V''} {α : M ⟶ N}

/-- For a subfunctor `U` of `V`, the sequence `0 → ℤ[U] → ℤ[V] → ℤ[V]/ℤ[U] → 0` (inclusion, then the
quotient map `π U`) is short exact. -/
lemma relFreeAb.shortExact (U : Subfunctor V) :
    ∃ w : freeAb.map U.ι ≫ π U = 0, ShortExact ⟨freeAb.map U.ι, π U, w⟩ := by
  -- `delta` exposes `abCoker.π` and `free.map`, whose `Epi` and `Mono` instances the short exact
  -- structure needs; on each value the kernel of the quotient map is the image (`eq_zero_iff`).
  delta π relFreeAb freeAb
  exact ⟨_, ⟨(exact_of_app fun _ x ↦ eq_zero_iff x).2⟩⟩

/-- The inclusion `ℤ[U] → ℤ[V]` is an equivalence for `F` (bijective on all `Ext^n(·, F)`) exactly
when all the relative groups `H^n(V, U) = Ext^n(ℤ[V]/ℤ[U], F)` vanish. -/
lemma relFreeAb.isCohomEquiv_iff_subsingleton_rel (U : Subfunctor V) :
    IsCohomEquiv F (freeAb.map U.ι) ↔ ∀ n : ℕ, Subsingleton (H (relFreeAb U) F n) :=
  isCohomEquiv_iff_subsingleton (S := ⟨freeAb.map U.ι, π U, (shortExact U).1⟩) (shortExact U).2

variable (v : V'' ⟶ V') (u : V' ⟶ V) (h : U'' ≤ U'.preimage v) (h' : U' ≤ U.preimage u)

lemma relFreeAb.mk_eq_zero {A : C} {x : V.obj A} (hx : x ∈ U A) : mk U x = 0 :=
  (eq_zero_iff _).2 ⟨of ⟨x, hx⟩, rfl⟩

/-- The free abelian groups `ℤ[V(A)]` are flat, being free. -/
instance : HasFlatValues (freeAb V) := ⟨fun _ ↦ .of_linearEquiv (basis _).repr⟩

/-- The classes of the generators `[y]` generate `ℤ[V(A)] / ℤ[U(A)]`. -/
lemma relFreeAb.mem_of_mk_mem {A : C} (S : AddSubgroup (relFreeAb U A))
    (h_gen : ∀ y : V.obj A, mk U y ∈ S) :
    ∀ s : (relFreeAb U).obj A, s ∈ S := by
  rintro ⟨t⟩
  exact t.induction_on S.zero_mem h_gen (fun _ ↦ neg_mem) fun _ _ ↦ add_mem

/-- The groups `ℤ[V(A)]/ℤ[U(A)]` are flat: each is a direct summand of the free group `ℤ[V(A)]`. -/
instance : HasFlatValues (relFreeAb U) := by
  refine ⟨fun A ↦ ?_⟩
  -- The inclusion `ℤ[U A] → ℤ[V A]` has a retraction, so the quotient is a retract of `ℤ[V A]`.
  let incl : FreeAbelianGroup (U A) →ₗ[ℤ] FreeAbelianGroup (V A) := (map Subtype.val).toIntLinearMap
  let retr : FreeAbelianGroup (V A) →ₗ[ℤ] FreeAbelianGroup (U A) :=
    (lift (extend Subtype.val of 0)).toIntLinearMap
  have h_retr : retr ∘ₗ incl = LinearMap.id := (basis _).ext (by simp [basis, retr, incl])
  -- `s` is a section of the quotient map by the range of `incl`.
  obtain ⟨-, s, hs⟩ :=
    (incl.exact_map_mkQ_range.split_tfae'.out 2 1 rfl rfl).mp ⟨mk_surjective, retr, h_retr⟩
  exact .of_retract s _ hs

/-- For set-valued functors X, Y, the map ℤ[X × Y] → ℤ[X] ⊗ ℤ[Y] sending [(x, y)] to [x] ⊗ [y]. -/
def freeAb.prod (X Y : C ⥤ Type 1) : freeAb (X ⊗ Y : C ⥤ Type 1) ⟶ abTensor (freeAb X) (freeAb Y) :=
  desc (fun _ x ↦ FreeAbelianGroup.of x.1 ⊗ₜ FreeAbelianGroup.of x.2) fun _ _ _ _ ↦ rfl

/-- The map `ℤ[V × V'] → ℤ[V] ⊗ ℤ[V']`, `[(x, y)] ↦ [x] ⊗ [y]`, is an isomorphism. -/
instance : IsIso (freeAb.prod V V') := by
  refine (isoOfAppBijective _ fun A ↦ ?_).isIso_hom
  -- On each object the map sends the standard basis to the tensor product of the standard bases.
  -- `e : ℤ[V(A) × V'(A)] ≃ ℤ[V(A)] ⊗ ℤ[V'(A)]`; with its type written out, `aesop` no longer
  -- proves `he`.
  let e := (basis (V A × V' A)).repr.trans ((basis (V A)).tensorProduct (basis (V' A))).repr.symm
  have he : e.toAddMonoidHom = (freeAb.prod V V' A).hom := lift_ext _ _ (by aesop (add simp basis))
  have h_bij : Bijective e.toAddMonoidHom := e.bijective
  rwa [he] at h_bij

/-- Let u: V' → V, φ: ℤ[V'] → N and S ⊂ N(A) a subgroup containing φ[x] − φ[y] when u(x) = u(y)
and φ[x] when u(x) ∈ U(A). Then φ maps the kernel of ℤ[V'(A)] → ℤ[V(A)]/ℤ[U(A)] into S. -/
lemma relFreeAb.mem_of_map_eq_zero (φ : freeAb V' ⟶ N) {A : C} (S : AddSubgroup (N.obj A))
    (h_fib : ∀ x y : V'.obj A,
      u A x = u A y → φ A (FreeAbelianGroup.of x) - φ A (FreeAbelianGroup.of y) ∈ S)
    (h_over : ∀ x : V'.obj A, u A x ∈ U A → φ A (FreeAbelianGroup.of x) ∈ S)
    (t : (freeAb.obj V').obj A) (ht : (freeAb.map u ≫ π U) A t = 0) :
    φ A t ∈ S := by
  classical
  -- The map `x ↦ φ[x] mod S` is constant on the fibres of `u`, so it extends (by zero) to `V(A)`.
  -- The additive map `l` on `ℤ[V(A)]` so defined kills `ℤ[U(A)]`, where the image of `t` lies.
  let g : V' A → N A ⧸ S := fun x ↦ mk' S (φ A (of x))
  have hg : FactorsThrough g (u A) := fun x y hxy ↦ eq_iff_sub_mem.2 (h_fib x y hxy)
  let l : freeAb V A →+ N A ⧸ S := FreeAbelianGroup.lift (extend (u A) g 0)
  have h_fac : l.comp (freeAb.map u A).hom = (mk' S).comp (φ A).hom :=
    lift_ext _ _ fun x ↦ (lift_apply_of ..).trans (hg.extend_apply _ x)
  have h_kill : l.comp (freeAb.map U.ι A).hom = 0 := by
    refine lift_ext _ _ fun y ↦ (lift_apply_of _ y.val).trans ?_
    -- for `y` in `U(A)`, `l [y] = 0`: a preimage `x` of `y` under `u` has `u x ∈ U(A)`, and with no
    -- preimage `l [y] = 0` by definition
    refine dite_eq_right_iff.2 fun hx ↦ (eq_zero_iff _).2 (h_over _ ?_)
    rw [hx.choose_spec]
    exact y.property
  obtain ⟨s, hs⟩ : freeAb.map u A t ∈ (freeAb.map U.ι A).hom.range := (eq_zero_iff _).1 ht
  refine (eq_zero_iff _).1 ?_
  calc mk' S (φ A t) = l (freeAb.map u A t) := (DFunLike.congr_fun h_fac t).symm
    _ = l (freeAb.map U.ι A s) := congrArg l hs.symm
    _ = 0 := DFunLike.congr_fun h_kill s

/-! ### Locally zero functors, locally bijective maps and the transfer -/

/-- The zero section of N: the subfunctor c ↦ {0} of the set-valued functor underlying N. -/
def zeroSection (N : C ⥤ Ab) : Subfunctor (N ⋙ forget Ab) where
  obj _ := {0}
  map _ := OrderBot.bot_le (ker _)

/-- The subgroup of locally zero elements of N(A): the s such that the maps A → B killing s form
a subfunctor of h_A that is dense for F. -/
def locallyZero (F N : AbFunctor C) (A : C) : AddSubgroup (N.obj A) :=
  AddSubgroup.ofSub {s : N.obj A | IsCohomDense F ((zeroSection N).preimage (pointMap s))}
    -- `0` is locally zero: every map kills it.
    ⟨0, IsCohomDense.of_top_le fun _ _ _ ↦ map_zero (N.map _).hom⟩
    -- a difference dies where both sections die, and that intersection is dense
    fun _ hs _ ht ↦ (hs.inf ht).mono fun _ _ h_both ↦ (N.map _).hom.ker.add_mem h_both.1 (by aesop)

/-- If every section of N is locally zero for F (`New.Variety.locallyZero`), then Ext^n(N, F) = 0
for all n. -/
theorem cohomology_eq_zero_of_locallyZero {N : AbFunctor C}
    (h_zero : ∀ (A : C) (s : N.obj A), s ∈ locallyZero F N A) (n : ℕ) (x : H N F n) :
    x = 0 := by
  -- Let `M = ℤ[N] / ℤ[0]` and let `K` be the kernel of the onto map `π : M ⟶ N`. The zero section
  -- is dense in `N`, so `M` is acyclic; and `K` is again locally zero. Induct on `n`, for all `N`
  -- at once, along the long exact sequence of `0 ⟶ K ⟶ M ⟶ N ⟶ 0`.
  induction n using Nat.strong_induction_on generalizing N with | _ n ih
  let M := relFreeAb (zeroSection N)
  let π : M ⟶ N := abCoker.desc (freeAb.desc (fun _ ↦ id) (by simp))
    (freeAb.hom_ext fun _ s ↦ (add_zero _).trans s.property)
  have π_surj (A : C) : Surjective (π.app A) := fun s ↦ ⟨relFreeAb.mk _ s, add_zero _⟩
  have zero_dense : IsCohomDense F (zeroSection N) := fun A s ↦ (h_zero A s).isCohomEquiv
  have M_acyclic := (relFreeAb.isCohomEquiv_iff_subsingleton_rel _).1 zero_dense.isCohomEquiv n
  have M_zero (A : C) : ∀ s : M.obj A, s ∈ locallyZero F M A :=
    relFreeAb.mem_of_mk_mem _ fun s ↦ (h_zero A s).mono fun _ _ hs ↦ relFreeAb.mk_eq_zero hs
  have K_zero (A : C) (s : (kerComplex π).X₁.obj A) : s ∈ locallyZero F _ A :=
    (M_zero A s.val).mono fun _ _ hs ↦ Subtype.ext hs
  -- `Ext^n(N, F) → Ext^n(M, F)` is injective, as `Ext^m(K, F) = 0` for `m < n`
  have inj : Injective ((LongExactSeq.contravariant (kerComplex_shortExact π_surj) F).f n) :=
    LongExactSeq.f_injective_of_g_surjective _ fun m hm y ↦
      ⟨0, (map_zero _).trans (ih m hm K_zero y).symm⟩
  exact inj (M_acyclic.elim _ _)

/-- Let `α : M → N` be a map of functors from `C` to abelian groups. Call an element `s` of `M(c)`
locally zero for `F` if the maps `c → d` that kill `s` form a subfunctor of h_c that is dense for
`F`, meaning that its inclusion into h_c, pulled back along every point h_A → h_c, induces
bijections on all `Ext^n(−, F)`. If every section of the kernel of `α` is locally zero for `F`
(`h_ker`), and so is every section of its objectwise cokernel `abCoker α` (`h_coker`), then `α`
induces bijections on all `Ext^n(−, F)`. -/
lemma isCohomEquiv_of_locallyZero
    (h_ker : ∀ (c : C) (s : M.obj c), α c s = 0 → s ∈ locallyZero F M c)
    (h_coker : ∀ (c : C) (t : N.obj c), abCoker.π α c t ∈ locallyZero F (abCoker α) c) :
    IsCohomEquiv F α := by
  -- Factor `α` through its image `I`, the kernel of `abCoker.π α`. The map onto `I` has a locally
  -- zero kernel, and the inclusion of `I` has a locally zero cokernel; both are acyclic by
  -- `cohomology_eq_zero_of_locallyZero`.
  let I := (kerComplex (abCoker.π α)).X₁
  let onto : M ⟶ I :=
    ⟨fun A ↦ ofHom ((α.app A).1.codRestrict _ fun s ↦ (eq_zero_iff _).2 ⟨s, rfl⟩), fun _ _ f ↦
      ext fun s ↦ Subtype.ext (α.naturality_apply f s)⟩
  have onto_surj (A : C) : Surjective (onto.app A) :=
    fun y ↦ ((eq_zero_iff _).1 y.property).imp fun _ ↦ Subtype.ext
  have ker_acyclic : ∀ n (x : H (kerComplex onto).X₁ F n), x = 0 :=
    cohomology_eq_zero_of_locallyZero fun A s ↦
      (h_ker A s.val (congrArg Subtype.val s.property)).mono fun _ _ hs ↦ Subtype.ext hs
  have eqv_onto : IsCohomEquiv F onto :=
    -- The ascription `( … :)` elaborates the term before unifying with the goal; without it
    -- elaboration times out.
    (isCohomEquiv_quotient_of_acyclic (kerComplex_shortExact onto_surj) ker_acyclic :)
  have cok_acyclic n : Subsingleton (H (abCoker α) F n) :=
    subsingleton_of_forall_eq 0
      (cohomology_eq_zero_of_locallyZero (fun A ↦ Quot.ind (h_coker A)) n)
  have eqv_incl : IsCohomEquiv F (kerComplex (abCoker.π α)).f :=
    (isCohomEquiv_iff_subsingleton
      (kerComplex_shortExact (α := abCoker.π α) fun _ ↦ mk_surjective)).2 cok_acyclic
  exact (eqv_onto.comp_iff.2 eqv_incl : IsCohomEquiv F (onto ≫ (kerComplex (abCoker.π α)).f))

/-- `New.Variety.isCohomEquiv_of_locallyZero`, with its two hypotheses given as one conjunction. -/
lemma LocalIso.isCohomEquiv
    (h :
      (∀ (c : C) (s : M.obj c), α c s = 0 → s ∈ locallyZero F M c) ∧
      ∀ (c : C) (t : N.obj c), abCoker.π α c t ∈ locallyZero F (abCoker α) c) :
    IsCohomEquiv F α :=
  isCohomEquiv_of_locallyZero h.1 h.2

/-- The pairs `(w, w')` in a fibre of `p : V' → V` (points of `V' ×_V V'`) whose tuples `(f i w)ᵢ`
and `(f i w')ᵢ` agree up to a permutation of `ι`. -/
abbrev permutedPairs {ι : Type*} (f : ι → (V' ⟶ V'')) (p : V' ⟶ V) : Subfunctor (cech p 1) where
  obj (A : C) :=
    {x : (cech p 1).obj A | ∃ e : ι ≃ ι, ∀ i : ι, f i A (x.val 1) = f (e i) A (x.val 0)}
  -- the maps of `cech p 1` act on both points at once, so they keep the condition
  map := by
    delta cech
    aesop

/-- Transfer. Let `f i : V' → V''` (`i` in a finite type `ι`), `p : V' → V` and `p' : V'' → V`
satisfy `f i ≫ p' = p`. Then there are `Q` and `m : ℤ[V'] → Q`, `l : Q → ℤ[V]`, `ν : Q → ℤ[V'']`
with `m ≫ l = ℤ[p]`, `m ≫ ν = ∑ i, ℤ[f i]` and `ν ≫ ℤ[p'] = card ι • l`. Moreover `l` is an
equivalence for every `F` for which the image of `p` is dense in `V` and `permutedPairs f p` is
dense in `V' ×_V V'`. Here `permutedPairs f p` consists of the pairs `(w, w')` whose tuples
`(f i w)ᵢ` and `(f i w')ᵢ` agree up to a permutation of `ι`. -/
lemma exists_transfer_map {ι : Type*} [Fintype ι] {f : ι → (V' ⟶ V'')} {p : V' ⟶ V} {p' : V'' ⟶ V}
    (h : ∀ i : ι, f i ≫ p' = p) :
    ∃ (Q : AbFunctor C) (m : freeAb.obj V' ⟶ Q) (l : Q ⟶ freeAb.obj V) (ν : Q ⟶ freeAb.obj V''),
      m ≫ l = freeAb.map p ∧
      m ≫ ν = ∑ i : ι, freeAb.map (f i) ∧
      ν ≫ freeAb.map p' = card ι • l ∧
      ∀ F : AbFunctor C, IsCohomDense F (Subfunctor.range p) →
        IsCohomDense F (permutedPairs f p) → IsCohomEquiv F (N' := Q) l := by
  -- Let `Q` be the quotient of `ℤ[V']` by the differences `[w] - [w']` over the pairs in `P`.
  -- On such a pair both `p` and `∑ i, [f i ·]` agree, so they factor through `Q`.
  let P : Subfunctor (cech p 1) := permutedPairs f p
  let d (j : Fin (1 + 1)) : freeAb.obj P.toFunctor ⟶ freeAb.obj V' :=
    freeAb.map (P.ι ≫ cech.proj p 1 j)
  let Q := abCoker (d 0 - d 1)
  let m : freeAb.obj V' ⟶ Q := abCoker.π (d 0 - d 1)
  have p_kills : (d 0 - d 1) ≫ freeAb.map p = 0 :=
    freeAb.hom_ext fun _ x ↦ sub_eq_zero.2 (congrArg of (x.val.property 0 1))
  have sum_kills : (d 0 - d 1) ≫ ∑ i, freeAb.map (f i) = 0 := by
    refine freeAb.hom_ext fun A ⟨x, e, he⟩ ↦ ?_
    have permute : ∑ i, of ((f i).app A (x.val 1)) = ∑ i, of ((f i).app A (x.val 0)) :=
      sum_equiv e _ _ fun i ↦ congrArg of (he i)
    -- Both values of the sum are the sum over `i` of `[f i ·]`, at the two points of the pair.
    have h_sums : (∑ i, freeAb.map (f i)).app A (of (x.val 0)) =
        (∑ i, freeAb.map (f i)).app A (of (x.val 1)) :=
      sum_app_apply.trans (sum_app_apply.trans permute).symm
    exact (map_sub ..).trans (sub_eq_zero.2 h_sums)
  let l : Q ⟶ freeAb.obj V := abCoker.desc (freeAb.map p) p_kills
  let ν : Q ⟶ freeAb.obj V'' := abCoker.desc (∑ i, freeAb.map (f i)) sum_kills
  refine ⟨Q, m, l, ν, rfl, rfl, ?_, fun F range_dense P_dense ↦ isCohomEquiv_of_locallyZero ?_ ?_⟩
  · -- Both sides agree after the epimorphism `m`.
    refine (cancel_epi (abCoker.π _)).1 ((Preadditive.sum_comp _ _ (freeAb.map p')).trans ?_)
    have h_ml : abCoker.π (d 0 - d 1) ≫ l = freeAb.map p := rfl
    simp [← freeAb.map_comp, h, h_ml]
  · -- The kernel of `l` is spanned by the `m ([x] - [y])` with `p x = p y`; these die on `P`.
    have diff_zero (c : C) (x y : V'.obj c) (hxy : p.app c x = p.app c y) :
        m.app c (of x) - m.app c (of y) ∈ locallyZero F Q c :=
      P_dense.of_preimage_le (pointMap ⟨![x, y], by simp_all⟩) fun _ _ hs ↦
        (eq_zero_iff _).2 ⟨of ⟨_, hs⟩, rfl⟩
    rintro c ⟨t⟩ ht
    exact relFreeAb.mem_of_map_eq_zero (U := ⊥) p m _ (diff_zero c) (by simp) t (congrArg _ ht)
  · -- The cokernel of `l` is spanned by the classes `[y]`; these die on the image of `p`.
    have gen_zero (c : C) (y : V.obj c) : (abCoker.π l).app c (of y) ∈ locallyZero F _ c :=
      range_dense.of_preimage_le (pointMap y) fun _ _ ⟨x, hx⟩ ↦
        (eq_zero_iff _).2 ⟨⟦of x⟧, congrArg of hx⟩
    exact fun c t ↦ t.induction_on (zero_mem _) (gen_zero c) (fun _ ↦ neg_mem) fun _ _ ↦ add_mem

namespace relFreeAb

/-- For `u : V' → V` carrying `U'` into `U`, the induced morphism `ℤ[V']/ℤ[U'] → ℤ[V]/ℤ[U]`. -/
def map : relFreeAb U' ⟶ relFreeAb U :=
  abCoker.desc (freeAb.map u ≫ π U) (freeAb.hom_ext fun A x ↦ mk_eq_zero (U := U) (h' A x.2))

lemma π_map : π U' ≫ map u h' = freeAb.map u ≫ π U := rfl

@[simp]
lemma map_comp_map : map v h ≫ map u h' = map (v ≫ u) (by tauto) := hom_ext

/-- For a monomorphism u: V' → V and a subfunctor U ⊂ V, the natural maps form a short exact
sequence 0 → ℤ[V']/ℤ[u⁻¹U] → ℤ[V]/ℤ[U] → ℤ[V]/ℤ[u(V') ∪ U] → 0 of functors to abelian
groups. -/
lemma shortExact_triple (U : Subfunctor V) [Mono u] :
    ∃ w : map (U' := U.preimage u) u le_rfl ≫
        map (U' := U) (U := Subfunctor.range u ⊔ U) (𝟙 V) le_sup_right =
      (0 : relFreeAb (U.preimage u) ⟶ relFreeAb (Subfunctor.range u ⊔ U)),
      ShortExact ⟨map u le_rfl, map (𝟙 V) (U := Subfunctor.range u ⊔ U) le_sup_right, w⟩ := by
  refine shortExact_of_app (fun A ↦ ?_) (fun A ↦ ?_) fun A ↦ ?_
  · -- injective: apply `mem_of_map_eq_zero` to the projection onto `ℤ[V'] / ℤ[u⁻¹U]` with `S = ⊥`
    -- As `u` is injective, points with the same image under `u` are equal.
    have h_fib : ∀ x y : V'.obj A, u A x = u A y →
        π (U.preimage u) A (FreeAbelianGroup.of x) - π (U.preimage u) A (FreeAbelianGroup.of y) ∈
          (⊥ : AddSubgroup ((relFreeAb (U.preimage u)).obj A)) := by
      intro x y hxy
      simp [injective_of_mono _ hxy]
    exact (injective_iff_map_eq_zero _).2 (Quot.ind (mem_of_map_eq_zero u (π (U.preimage u)) ⊥
      h_fib fun _ hx ↦ mk_eq_zero hx))
  · refine .of_comp_of_mem_range (funext ?_) (Quot.ind ?_)
    · -- the composite vanishes on generators, which land in the image of `u`
      exact mem_of_mk_mem (.comap _ (ker _)) fun x ↦ mk_eq_zero (by simp)
    · -- the kernel lies in the image: apply `mem_of_map_eq_zero` to the identity of `V`
      refine mem_of_map_eq_zero (𝟙 V) (π U) (range _) (by bound) ?_
      rintro y (⟨x, rfl⟩ | hy)
      · exact ⟨mk _ x, rfl⟩
      · exact ⟨0, (mk_eq_zero hy).symm⟩
  · -- surjective: every generator is hit by the same generator
    exact mem_of_mk_mem (range _) fun y ↦ ⟨mk _ y, rfl⟩

/-- If U′ ≤ U are subfunctors of V and U′ is dense in U for F, then ℤ[V]/ℤ[U′] → ℤ[V]/ℤ[U] induces
bijections on Ext^n(·, F) for all n. -/
lemma isCohomEquiv_of_le {U' U : Subfunctor V} (h_le : U' ≤ U)
    (h_dense : IsCohomDense F (U'.preimage U.ι)) :
    IsCohomEquiv F (map (𝟙 V) h_le) := by
  -- By `shortExact_triple` for the inclusion of `U`, the kernel of the map is `ℤ[U] / ℤ[U']`, which
  -- is acyclic because `U'` is dense in `U`.
  have h_acyclic : ∀ n, Subsingleton (H (relFreeAb (U'.preimage U.ι)) F n) :=
    (isCohomEquiv_iff_subsingleton_rel _).1 h_dense.isCohomEquiv
  -- The third term of that sequence is `relFreeAb U`, since `U = range U.ι ⊔ U'` as `U' ≤ U`; every
  -- goal that `convert` and `congr` leave comes down to this identity and is closed by `simp_all`.
  convert isCohomEquiv_quotient_of_acyclic (shortExact_triple U.ι U').2
      fun n x ↦ (h_acyclic n).1 x 0 <;> congr <;> simp_all

/-- Excision: let u : V′ → V be a monomorphism, U′ = u⁻¹U, and u(V′) ∪ U dense in V for the
coefficient F. Then ℤ[V′]/ℤ[U′] → ℤ[V]/ℤ[U] induces bijections on Ext^n(·, F) for all n. -/
lemma excision (h : IsCohomDense F (Subfunctor.range u ⊔ U)) [m : Mono u]
    (h_pre : U' = U.preimage u) :
    IsCohomEquiv F (map u h_pre.le) := by
  -- By `shortExact_triple` the cokernel of the map is `ℤ[V] / ℤ[u(V') ∪ U]`, which is acyclic by
  -- density.
  subst h_pre
  exact (isCohomEquiv_iff_subsingleton (shortExact_triple u U).2).2
    ((isCohomEquiv_iff_subsingleton_rel _).1 h.isCohomEquiv)

end relFreeAb

end New.Variety

end RelativeChains

/-! ## Gluing relative classes over a finite cover and products of pairs -/

namespace New.Variety

open CategoryTheory Subfunctor CartesianMonoidalCategory Fin Comparison LongExactSeq

variable {C : Type _} [Category C]
  {V X : C ⥤ Type 1} (U : Subfunctor V) {A B : Subfunctor V} (h : A ≤ B)

/-- For subfunctors U and A ⊆ B of V, the map ℤ[A]/ℤ[U ∩ A] → ℤ[B]/ℤ[U ∩ B]. -/
abbrev relFreeAb.restrict : relFreeAb (U.preimage A.ι) ⟶ relFreeAb (U.preimage B.ι) :=
  map (homOfLe h) (id le_rfl)

/-- For subfunctors `A`, `B` of `V` with `A ⊓ B = D`, the restriction and quotient maps form a short
exact sequence `0 → ℤ[D]/ℤ[U ∩ D] → ℤ[B]/ℤ[U ∩ B] → ℤ[B]/ℤ[(A ∪ U) ∩ B] → 0`. -/
lemma relFreeAb.shortExact_restrict_of_inf_eq {A B D : Subfunctor V} (hD : A ⊓ B = D) :
    ∃ w, ShortComplex.ShortExact ⟨restrict U (hD.ge.trans inf_le_right),
      map (𝟙 B.toFunctor) (U := A.preimage B.ι ⊔ U.preimage B.ι) le_sup_right, w⟩ := by
  -- This is `shortExact_triple` for the inclusion of `D` in `B`, whose image is `A ∩ B`.
  have h_range : range (homOfLe (hD.ge.trans inf_le_right)) = A.preimage B.ι := by
    delta toFunctor homOfLe
    aesop
  rw [← h_range]
  exact shortExact_triple ..

/-- The inclusion of `A` in `B` followed by that of `B` in `D` is the inclusion of `A` in `D`. -/
private lemma homOfLe_comp_homOfLe {A B D : Subfunctor V} (h₁ : A ≤ B) (h₂ : B ≤ D) :
    homOfLe h₁ ≫ homOfLe h₂ = homOfLe (h₁.trans h₂) := rfl

/-- Gluing on the union of the `W i`. Let `S` be a set of subfunctors of `V`, closed under
intersection, whose members `A` have `H^n(A, U ∩ A) = 0` for `n < d`, and let the `W i` lie in `S`.
On the union `⨆ i, W i`: a class of degree `n ≤ d` that restricts to zero on every `W i` is zero;
and classes `x i` in `H^d(W i, U ∩ W i)` that agree on the intersections `W i ⊓ W j` are the
restrictions of one class. -/
lemma relFreeAb.eq_zero_and_exists_glued_of_iSup {F : AbFunctor C} {d : ℕ}
    (S : Set (Subfunctor V)) (hS : InfClosed S)
    (h_vanish : ∀ A ∈ S, ∀ n < d, Subsingleton (H (relFreeAb (U.preimage A.ι)) F n)) {r : ℕ}
    (W : Fin r → Subfunctor V) (hW : ∀ i : Fin r, W i ∈ S)
    (x : ∀ i : Fin r, H (relFreeAb (U.preimage (W i).ι)) F d)
    (hx : ∀ i j : Fin r,
      H.map F (restrict U inf_le_left) d (x i) = H.map F (restrict U inf_le_right) d (x j)) :
    (∀ n ≤ d, ∀ {z : H (relFreeAb (U.preimage (iSup W).ι)) F n},
      (∀ i : Fin r, H.map F (restrict U (le_iSup W i)) n z = 0) → z = 0) ∧
    ∃ y : H (relFreeAb (U.preimage (iSup W).ι)) F d,
      ∀ i : Fin r, H.map F (restrict U (le_iSup W i)) d y = x i := by
  -- By induction on the number of the `W i`, for all families at once.
  induction r with
  | zero =>
    -- the empty union has no points, so its relative chains and all its cohomology are zero
    exact ⟨fun n _ z _ ↦ (H.subsingleton_of_id_eq_zero (hom_ext nofun) ..).elim z 0, 0, nofun⟩
  | succ r ih =>
    -- Uniqueness on the union of the `W i.succ ⊓ W 0` (the family of zero classes is
    -- compatible); uniqueness and a glued class `y` on the union `A` of the `W i.succ`.
    let A : Subfunctor V := ⨆ i : Fin r, W i.succ
    have hW_inter : ∀ i : Fin r, W i.succ ⊓ W 0 ∈ S := fun i ↦ hS (hW i.succ) (hW 0)
    -- `inj_inter`, `inj_old` and `ladder` keep their inferred types; written out, they time out.
    have inj_inter := (ih _ hW_inter 0 (by simp)).1
    obtain ⟨inj_old, y, hy⟩ := ih _ (fun i ↦ hW i.succ) _ fun i j ↦ hx i.succ j.succ
    -- `ladder`: restriction maps the long exact sequence of `A` in the larger union to that of
    -- `A ⊓ W 0` in `W 0`.
    have h_inter : A ⊓ W 0 = ⨆ i : Fin r, W i.succ ⊓ W 0 := iSup_min ..
    have ladder :=
      pull_hom_contravariant
        (shortExact_restrict_of_inf_eq U (inf_of_le_left (iSup_comp_le W succ) : A ⊓ iSup W = A)).2
        (shortExact_restrict_of_inf_eq U h_inter).2 (.id F)
        ⟨restrict U (iSup_mono (by simp)), restrict U (le_iSup W 0),
          map (homOfLe (le_iSup ..)) le_rfl, hom_ext, hom_ext⟩
    simp at ladder
    -- The relative terms of the two sequences agree, by excision.
    have h_exc : IsCohomEquiv F (map (homOfLe (le_iSup W 0))
        (U := A.preimage (Subfunctor.ι _) ⊔ U.preimage (Subfunctor.ι _)) le_rfl) := by
      refine excision _ (.of_top_le fun _ v _ ↦ ?_) rfl
      have hv : v.val ∈ (W 0).obj _ ∨ v.val ∈ A.obj _ := by
        simpa [A, exists_fin_succ] using v.property
      exact hv.imp (fun hv ↦ ⟨⟨_, hv⟩, rfl⟩) .inl
    refine ⟨fun n hn z hz ↦ ?_, ?_⟩
    · -- Diagram chase: `z` dies on `W 0` and on `A`, so it comes from a relative class; that
      -- class is zero by excision and the vanishing in degree `n - 1` below.
      refine ladder.rotate.eq_zero_of_delta_eq_zero (fun t ↦ ⟨0, sub_eq_zero.1 ?_⟩)
        (h_exc n).injective z (hz 0)
        (inj_old n hn fun i ↦
          (H.map_comp ..).symm.trans (by simpa [homOfLe_comp_homOfLe] using hz i.succ))
      -- The group of `A ⊓ W 0` in degree `n - 1 < d` is zero, as those of its pieces are.
      cases n with
      | zero => rfl
      | succ n => exact inj_inter n (by lia) fun i ↦ (h_vanish _ (hW_inter i) _ hn).elim ..
    · -- The glued class `y` and `x 0` agree on `A ⊓ W 0`, since they agree on its pieces; so a
      -- diagram chase gives `z` on the larger union that restricts to both.
      -- `+instances`, `using!`: the goal contains `map (𝟙 _) le_sup_right`, which is well typed
      -- only after unfolding instances, so `rw` and plain `simpa` fail on it.
      obtain ⟨z, hz, rfl⟩ :=
        ladder.exists_preimage (h_exc d).surjective (h_exc _).injective (x 0) y <|
          sub_eq_zero.1 <| inj_inter d le_rfl fun i ↦ by
            simpa +instances [← hy, contravariant, ← H.map_comp, sub_eq_zero] using! hx i.succ 0
      refine ⟨z, fun i ↦ ?_⟩
      induction i using Fin.cases with
      | zero => exact hz
      | succ i => simpa [homOfLe_comp_homOfLe] using (H.map_comp ..).trans (hy i)

/-- Let `S` be a set of subfunctors of `V`, closed under intersection, whose members `A` have
`H^n(A, U ∩ A) = 0` for `n < d`. Let finitely many `W i` lie in `S`, with the union of `U` and the
`W i` dense for `F`. Then classes `x i` in `H^d(W i, U ∩ W i)` that agree on the intersections
`W i ⊓ W j` are the restrictions of one class in `H^d(V, U)`. -/
lemma relFreeAb.exists_glued_class {r : ℕ} {F : AbFunctor C} {d : ℕ} (S : Set (Subfunctor V))
    (hS : InfClosed S)
    (h_vanish : ∀ A ∈ S, ∀ n < d, Subsingleton (H (relFreeAb (U.preimage A.ι)) F n))
    (W : Fin r → Subfunctor V) (hW : ∀ i : Fin r, W i ∈ S) (hd : IsCohomDense F (iSup W ⊔ U))
    (x : ∀ i : Fin r, H (relFreeAb (U.preimage (W i).ι)) F d)
    (hx : ∀ i j : Fin r,
      H.map F (restrict U inf_le_left) d (x i) = H.map F (restrict U inf_le_right) d (x j)) :
    ∃ y : H (relFreeAb U) F d, ∀ i : Fin r, H.map F (map (W i).ι le_rfl) d y = x i := by
  -- The classes glue on the union of the `W i`; excision and the density `hd` pass from the union
  -- to `V`.
  obtain ⟨-, z, hz⟩ := eq_zero_and_exists_glued_of_iSup U S hS h_vanish W hW x hx
  have h_dense : IsCohomDense F (Subfunctor.range (iSup W).ι ⊔ U) := by simpa using hd
  obtain ⟨y, rfl⟩ := (excision (iSup W).ι (U := U) h_dense rfl d).surjective z
  exact ⟨y, fun i ↦ by simpa [← H.map_comp] using hz i⟩

/-- For `U ⊆ V` and `W ⊆ X`, the map `ℤ[V × X] / ℤ[U × X ∪ V × W] → ℤ[V] / ℤ[U] ⊗ ℤ[X] / ℤ[W]` that
sends `[(v, w)]` to `[v] ⊗ [w]`. -/
def relFreeAb.prod (W : Subfunctor X) :
    relFreeAb (U.preimage (fst V X) ⊔ Subfunctor.preimage W (snd V X)) ⟶
      (abTensor.obj (relFreeAb U)).obj (relFreeAb W) :=
  abCoker.desc
      (freeAb.prod V X ≫
        (abTensor.map (π U)).app (freeAb.obj X) ≫ (abTensor.obj (relFreeAb U)).map (π W)) <| by
    -- a pair with first entry in `U` or second entry in `W` has a zero factor
    refine freeAb.hom_ext fun A ⟨⟨v, w⟩, hx⟩ ↦ ?_
    change mk U v ⊗ₜ mk W w = 0
    obtain h | h : v ∈ U.obj A ∨ w ∈ W.obj A := hx <;> simp [mk_eq_zero h]

end New.Variety
