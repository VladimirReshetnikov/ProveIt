import Lib.Cohomology.Hodge.CupProduct

/-!
# The Leray–Hirsch map as a map of δ-functors, and dévissage from representable functors

A family θ of classes θ_i in Ext^{d_i}(Φ G, F), for an exact functor Φ, defines the Leray–Hirsch map
w ↦ Σ Φ(w_i) · θ_i. The file shows that its bijectivity at S can be proved by dévissage in S.

* `New.Variety.lerayHirsch`, `New.Variety.IsLerayHirschBasis`: the map, from finitely supported
  families in Ext(S, G) to Ext(Φ S, F), and its bijectivity.
* `New.Variety.isLerayHirschBasis_iff_allBijective_truncMap`: it is bijective iff its truncations to
  total degree below n all are.
* `New.Variety.Devissage.allBijective_of_allBijective_sigma_reprBy`: from disjoint unions of
  representable functors to all functors.
* `New.Variety.isLerayHirschBasis_of_reprBy`: from representable functors to all functors, for
  finitely many classes and Φ the restriction along a functor.

Notions from other files:
* `New.Variety.H`: The group Ext^n(N,F) in the category of functors from C to abelian groups;
  `TotalH N F` is their direct sum over n, `x.toTotalH` is x placed in its degree, and
  `mapThenComp Φ t x` is the Yoneda product t ∘ Φ(x).
* `New.Variety.freeAb`: The functor sending a set-valued functor Y to ℤ[Y], whose value at A is the
  free abelian group on Y(A).
* `New.Variety.Devissage`: The five and four lemmas for a family of maps f_{N,n} : A N n → B N n,
  indexed by functors N : D → Ab and degrees n, as for a map of contravariant δ-functors.

## Relation to the literature

Known result: Leray–Hirsch theorem that a local basis of cohomology classes is a global basis. The
theorem is stated abstractly for Ext groups of functors and finitely many classes. It says that if
the Leray–Hirsch map is bijective on ℤ[h_c] for every representable functor h_c, then it is
bijective on every functor. Source: Leray, Hirsch; Hatcher, Algebraic Topology, Thm 4D.1; SGA 5 VII
(projective bundle formula).
-/

noncomputable section

namespace New.Variety

open CategoryTheory Function DirectSum TotalH Finsupp H

variable {A C : Type 1} [Category A] [Category C]
  {Φ : (A ⥤ Ab) ⥤ AbFunctor C} [@IsExactFunctor A C _ _ Φ] {G : A ⥤ Ab} {S S' : AbFunctor A}
  {n e : ℕ} {F N M : AbFunctor C} {I : Type _} [DecidableEq I] {d : I → ℕ}
  (θ : ∀ i : I, H (Φ G) F (d i)) {X : ShortComplex (AbFunctor A)} (h : X.ShortExact)

/-! ### The map and its naturality -/

/-- For classes θ_i in Ext^{d_i}(ΦG, F), the Leray–Hirsch map w ↦ Σ θ_i∘Φ(w_i) from finitely
supported families in total Ext(S, G) to total Ext(ΦS, F). -/
def lerayHirsch (S : AbFunctor A) : (I →₀ TotalH S G) →ₗ[ℤ] TotalH (Φ S) F :=
  lsum ℤ fun i ↦ (mapThenComp Φ (θ i).toTotalH).toIntLinearMap

/-- The Leray–Hirsch property for S: the Leray–Hirsch map `New.Variety.lerayHirsch` of θ at S is
bijective. -/
abbrev IsLerayHirschBasis (S : AbFunctor A) : Prop := Bijective (lerayHirsch θ S)

section

omit [DecidableEq I]

lemma lerayHirsch_single (i : I) (x : TotalH S G) :
    lerayHirsch θ S (.single i x) = .comp (.map Φ x) (θ i).toTotalH := by
  simp [lerayHirsch, mapThenComp]

/-- Additive maps r, r' that intertwine the maps x ↦ Φ(x) · θ_i and x ↦ Φ'(x) · θ'_i for each i
intertwine the two Leray–Hirsch maps. -/
lemma lerayHirsch_naturality {A' C' : Type 1} [Category A'] [Category C']
    {Φ' : (A' ⥤ Ab) ⥤ AbFunctor C'} [@IsExactFunctor A' C' _ _ Φ'] {G' T : AbFunctor A'}
    {F' : AbFunctor C'} {θ' : (i : I) → H (Φ'.obj G') F' (d i)} (r : TotalH S G →+ TotalH T G')
    {r' : TotalH (Φ.obj S) F →+ TotalH (Φ'.obj T) F'} (h_intertwine : ∀ (i : I) (x : TotalH S G),
      mapThenComp Φ' (of (H (Φ'.obj G') F') (d i) (θ' i)) (r x) =
        r' (mapThenComp Φ (θ i).toTotalH x))
    (w : I →₀ TotalH S G) :
    lerayHirsch θ' T (w.mapRange r r.map_zero) = r' (lerayHirsch θ S w) := by
  simp_all [lerayHirsch, sum_mapRange_index, map_finsuppSum]

/-- The Leray–Hirsch map is natural in S for Yoneda products: precomposing each w_i with ξ
corresponds to precomposing the image with Φ(ξ). -/
lemma lerayHirsch_mapRange_comp {ξ : TotalH S' S} {ζ : TotalH (Φ.obj S') (Φ.obj S)}
    (hξ : TotalH.map Φ ξ = ζ) (w : I →₀ TotalH S G) :
    lerayHirsch θ S' (w.mapRange (TotalH.comp ξ) (TotalH.comp ξ).map_zero) =
      .comp ζ (lerayHirsch θ S w) :=
  -- precomposing with `ξ` before the product with `θ i` is precomposing with `ζ = Φ ξ` after it
  have h_inter : ∀ (i : I) (x : TotalH S G),
      mapThenComp Φ (of (H (Φ.obj G) F) (d i) (θ i)) (TotalH.comp ξ x) =
        TotalH.comp ζ (mapThenComp Φ (θ i).toTotalH x) := by
    simp [map_comp_assoc, hξ, mapThenComp]
  lerayHirsch_naturality _ _ h_inter w

end

/-! ### Truncation by total degree -/

open scoped Classical in
/-- The truncation of finitely supported families (w_i) in total Ext(S, G) to total degree below
n: in w_i, keep the components of degree e with e + d_i < n. It is a ℤ-linear endomorphism of the
families `I →₀ TotalH S G`. -/
@[aesop simp]
def degreeTrunc (d : I → ℕ) (n : ℕ) :=
  (finsuppLequivDFinsupp (M := TotalH S G) ℤ).symm.conj
    (DFinsupp.mapRange.linearMap fun i ↦ lmap fun m ↦ if m + d i < n then .id else 0)

/-- Precomposition with a class ξ of degree e commutes with truncation, up to the shift by e: for
the map `φ` of families `(I →₀ TotalH N F) → (I →₀ TotalH M F)` given by `ξ`, truncating below `n`
and then applying `φ` is applying `φ` and then truncating below `n + e`. -/
lemma degreeTrunc_comp_precomp (ξ : H (C := C) M N e) :
    have φ := mapRange.linearMap (TotalH.comp (F := F) ξ.toTotalH).toIntLinearMap
    φ ∘ₗ degreeTrunc d n = degreeTrunc d (n + e) ∘ₗ φ := by
  aesop (add simp [lof_eq_of, comp_of]) (add safe (by omega))

/-- The Leray–Hirsch map commutes with truncation. Its target is viewed as families indexed by one
point, with degree shift 0, so that `New.Variety.degreeTrunc` applies to it: `φ` is the map
`(I →₀ TotalH S G) → (Unit →₀ TotalH (Φ S) F)`. -/
lemma degreeTrunc_comp_lerayHirsch (S : AbFunctor A) (n : ℕ) :
    have φ := lsingle () ∘ₗ lerayHirsch θ S
    φ ∘ₗ degreeTrunc d n = degreeTrunc 0 n ∘ₗ φ := by
  aesop (add simp lerayHirsch) (add simp [mapThenComp, lof_eq_of, comp_of])

/-- For a linear map φ from families `I →₀ TotalH S G` to families `J →₀ TotalH N F`, commuting with
the truncations (below n with shifts d, below m with shifts b) `New.Variety.degreeTrunc`, its
restriction from families of total degree below n to families of total degree below m. -/
def truncMap {J b m φ} [DecidableEq J]
    (h : φ ∘ₗ degreeTrunc (A := A) (G := G) (S := S) (I := I) d n =
      degreeTrunc (A := C) (G := F) (S := N) (I := J) b m ∘ₗ φ) :
    (.of (degreeTrunc (A := A) (G := G) (S := S) (I := I) d n).range : Ab) →+
      (.of (degreeTrunc (A := C) (G := F) (S := N) (I := J) b m).range : Ab) :=
  -- `φ` sends `degreeTrunc d n w` to `degreeTrunc b m (φ w)`
  show (.of (degreeTrunc d n).range : Ab) →+ (.of (degreeTrunc b m).range : Ab) from
    (φ.restrict (by
      rintro _ ⟨w, rfl⟩
      exact ⟨φ w, congr($h w).symm⟩)).toAddMonoidHom

variable {θ}

/-- The Leray–Hirsch map at S is bijective iff, for every n, its restriction to families of total
degree below n is a bijection onto the classes of degree below n. Here `S`, `G` are functors
`A ⥤ Ab`, `F` is a functor `C ⥤ Ab`, and the classes `θ i` are indexed by a type `I`. -/
lemma isLerayHirschBasis_iff_allBijective_truncMap : IsLerayHirschBasis θ S ↔
    AllBijective fun n : ℕ ↦ truncMap (degreeTrunc_comp_lerayHirsch θ S n) := by
  -- The map `lerayHirsch θ S`, with values in families indexed by one point, commutes with the
  -- truncations.
  have comm (n : ℕ) (a : I →₀ TotalH S G) :
      single () (lerayHirsch θ S (degreeTrunc d n a)) =
        degreeTrunc 0 n (single () (lerayHirsch θ S a)) :=
    LinearMap.congr_fun (degreeTrunc_comp_lerayHirsch θ S n) a
  -- Unfold both sides on elements; the range of `degreeTrunc d n` is the part of degree below `n`.
  suffices key : ((∀ a : I →₀ TotalH S G, lerayHirsch θ S a = 0 → a = 0) ∧
        ∀ b : TotalH (Φ.obj S) F, ∃ a, lerayHirsch θ S a = b) ↔
      ∀ n : ℕ, (∀ a : I →₀ TotalH S G,
          lerayHirsch θ S (degreeTrunc d n a) = 0 → degreeTrunc d n a = 0) ∧
        ∀ z : Unit →₀ TotalH (Φ.obj S) F,
          ∃ a, single () (lerayHirsch θ S (degreeTrunc d n a)) = degreeTrunc 0 n z by
    simpa [AllBijective, Bijective, truncMap, injective_iff_map_eq_zero, Surjective,
      LinearMap.restrict_apply] using key
  refine ⟨fun ⟨h_inj, h_surj⟩ n ↦ ⟨fun a ↦ h_inj _, fun z ↦ ?_⟩,
    fun h_trunc ↦ ⟨fun a ha ↦ ?_, fun b ↦ ?_⟩⟩
  · -- Truncate a preimage of `z`.
    obtain ⟨a, ha⟩ := h_surj (z ())
    exact ⟨a, by rw [comm, ha, ← unique_single]⟩
  · -- If `lerayHirsch θ S a = 0`, every truncation of `a` is in the kernel, hence zero; the
    -- component of `a i` in degree `m` survives truncation at `m + d i + 1`.
    have h_zero (n : ℕ) : degreeTrunc d n a = 0 :=
      (h_trunc n).left a (by simpa [ha] using comm n a)
    ext i m
    have h_comp : degreeTrunc d (m + d i + 1) a i m = 0 := by simp [h_zero]
    simpa [degreeTrunc] using h_comp
  · -- The range is a submodule, so it is enough to reach a homogeneous class `z` of degree `n`,
    -- which is unchanged by truncation at `n + 1`.
    induction b using DirectSum.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | of n z =>
      obtain ⟨a, ha⟩ := (h_trunc (n + 1)).right (single () (of _ n z))
      refine ⟨degreeTrunc d (n + 1) a, ?_⟩
      have h_val : lerayHirsch θ S (degreeTrunc d (n + 1) a) =
          degreeTrunc 0 (n + 1) (single () (of (H (Φ.obj S) F) n z)) () := by simp [← ha]
      simpa [degreeTrunc] using h_val
    | add x y hx hy => exact (lerayHirsch θ S).range.add_mem hx hy

/-! ### Long exact sequences of truncated families -/

/-- If precomposition with ξ and with ζ is exact on total Ext groups, it is exact on the truncated
families. Here `S`, `M`, `N`, `F` are functors `C ⥤ Ab`, and `ξ`, `ζ` are classes of degrees `e`
and `n`. -/
lemma truncMap.exact_of_exact {S : AbFunctor C} {n e : ℕ} {F N M : AbFunctor C} {I : Type _}
    [DecidableEq I] {d : I → ℕ} {ξ : H M N e} {ζ : H S M n}
    (h_exact : Exact (TotalH.comp (F := F) (of (H M N) e ξ))
      (TotalH.comp (C := C) (of (H S M) n ζ))) (m : ℕ) :
    Exact (truncMap (degreeTrunc_comp_precomp (n := m) (F := F) (d := d) ξ))
      (truncMap (degreeTrunc_comp_precomp ζ)) := by
  -- On elements: a truncated family is killed by `ζ` iff it comes from a truncated family by `ξ`.
  suffices key : ∀ a : I →₀ TotalH M F,
    mapRange (TotalH.comp (of (H S M) n ζ)) (map_zero _) (degreeTrunc d (m + e) a) = 0 ↔
      ∃ y : I →₀ TotalH N F,
        mapRange (TotalH.comp (of (H M N) e ξ)) (map_zero _) (degreeTrunc d m y) =
          degreeTrunc d (m + e) a by simpa [Exact, truncMap, LinearMap.restrict_apply] using key
  refine fun a ↦ ⟨fun ha ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩
  · -- By `h_exact` each component of the truncation of `a` comes from a class by `ξ`.
    obtain ⟨y, hy⟩ :
        ∃ y, mapRange (TotalH.comp (of _ _ ξ)) (map_zero _) y = degreeTrunc d (m + e) a :=
      (range_mapRange _ _).ge fun i ↦ (h_exact _).mp (DFunLike.congr_fun ha i)
    -- Truncate the preimage: `ξ` shifts truncation by `e`, it carries `y` to the truncation of
    -- `a` (`hy`), and truncating twice is truncating once.
    refine ⟨y, (LinearMap.congr_fun (degreeTrunc_comp_precomp ξ) y).trans ?_⟩
    have h_idem : degreeTrunc d (m + e) (degreeTrunc d (m + e) a) = degreeTrunc d (m + e) a := by
      aesop
    simpa [hy] using h_idem
  · -- Conversely `ζ` kills what comes from `ξ`, component by component.
    simp [← hy, Finsupp.ext_iff, h_exact.apply_apply_eq_zero]

/-- For a short exact sequence X, the long exact sequence whose n-th terms are the finitely
supported families in total Ext(X₃, G), Ext(X₂, G), Ext(X₁, G) of total degree below n; its maps A
n → B n → C n → A (n+1) are precomposition with X.g, with X.f, and with the extension class of X
(degree 1). -/
def truncMap.longExact : LongExactSeq where
  -- the shifts `+ 0` are the degrees of the classes of `X.g` and `X.f`
  A n := .of (degreeTrunc (S := X.X₃) (G := G) d n).range
  B n := .of (degreeTrunc (S := X.X₂) (G := G) d (n + 0)).range
  C n := .of (degreeTrunc (S := X.X₁) (G := G) d (n + 0 + 0)).range
  f _ := truncMap (degreeTrunc_comp_precomp (.mk₀ X.g))
  g _ := truncMap (degreeTrunc_comp_precomp (.mk₀ X.f))
  δ _ := truncMap (degreeTrunc_comp_precomp h.extClass)
  -- a family of total degree below `0` is zero
  injective_f := by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩ -
    ext
    simp [degreeTrunc]
  exact_f_g := exact_of_exact (exact_triangle h G).1
  exact_g_delta := exact_of_exact (exact_triangle h G).2.1
  exact_delta_f := exact_of_exact (exact_triangle h G).2.2

/-- For a short exact sequence X, the Leray–Hirsch maps of θ, truncated to total degree below n,
form a morphism (the same maps t on all three kinds of terms, commuting with f, g and δ) from the
long exact sequence `New.Variety.truncMap.longExact` of families in Ext(X, G) to that of total
Ext(ΦX, F), truncated likewise. -/
lemma lerayHirsch.longExact_hom :
    have t {S : AbFunctor A} (n : ℕ) := truncMap (degreeTrunc_comp_lerayHirsch θ S n)
    (truncMap.longExact h).Hom (truncMap.longExact (h.map_of_exact Φ)) t t t := by
  -- Each square is `lerayHirsch_mapRange_comp`; it remains to see that `Φ` carries the classes of
  -- `X.g`, `X.f` and the extension class of `X` to the corresponding classes of `X.map Φ`.
  refine ⟨fun n x ↦ ?_, fun n x ↦ ?_, fun n x ↦ ?_⟩ <;>
    refine Subtype.ext <|
      (congrArg (single ()) (lerayHirsch_mapRange_comp θ ?_ _)).trans
        (mapRange_single (hf := map_zero _)).symm
  · exact map_homClass
  · exact map_homClass
  · -- `Φ` carries the extension class of `X` to that of `X.map Φ`
    aesop (add simp Abelian.Ext.mapExactFunctor_extClass)

/-- The Leray–Hirsch maps of θ, truncated to total degree below n, satisfy `New.Variety.Devissage`:
the five lemma and the four lemmas hold for them along short exact sequences of functors S. -/
lemma lerayHirsch.devissage :
    Devissage fun (S : A ⥤ Ab) (n : ℕ) ↦ truncMap (degreeTrunc_comp_lerayHirsch θ S n) := by
  -- The four lemma and the five lemma are applied to the ladder `longExact_hom`; the class must
  -- also contain the zero functors.
  refine
    { bijectiveUpTo_quotient := fun hX ↦ (longExact_hom hX).four_lemma
      isClosedClass :=
        ⟨fun S hS ↦ isLerayHirschBasis_iff_allBijective_truncMap.mp ?_, fun X hX ↦
          (longExact_hom hX).five_lemma⟩ }
  -- If `S = 0`, then `Φ S = 0` too, and both sides of `lerayHirsch θ S` are trivial.
  have h_src : ∀ (G : A ⥤ Ab) (n : ℕ), Subsingleton (H S G n) := subsingleton_of_id_eq_zero hS
  have h_id_zero : 𝟙 (Φ.obj S) = 0 := by simpa using Φ.congr_map hS
  have h_tgt : ∀ n : ℕ, Subsingleton (H (Φ S) F n) := subsingleton_of_id_eq_zero h_id_zero F
  -- a map between groups with one element is bijective
  aesop

/-- The functors `S` at which `θ` is a Leray–Hirsch basis form a closed class
(`New.Variety.IsClosedClass`): the class contains the zero functors, and along a short exact
sequence whose subobject is in it, the middle term is in it exactly when the quotient is. -/
lemma isClosedClass_isLerayHirschBasis : IsClosedClass fun S : A ⥤ Ab ↦ IsLerayHirschBasis θ S := by
  simp [isLerayHirschBasis_iff_allBijective_truncMap, lerayHirsch.devissage.isClosedClass]

/-! ### Dévissage from representable functors -/

/-- Dévissage. Let f(S, n) be maps with the five- and four-lemma properties `New.Variety.Devissage`.
If f(S, n) is bijective for all n whenever S = ℤ[Y] with Y a disjoint union of representable
functors, then f(S, n) is bijective for every S and n. -/
lemma Devissage.allBijective_of_allBijective_sigma_reprBy {A B : C ⥤ Ab → ℕ → Type _}
    {f : (N : C ⥤ Ab) → (n : ℕ) → A N n → B N n} (hf : Devissage (D := C) (A := A) (B := B) f)
    (h_sum : ∀ (ι : Type 1) (c : ι → C),
      AllBijective (f (freeAb.obj (sigma fun i : ι ↦ reprBy (c i))))) (S : C ⥤ Ab) :
    AllBijective (f S) := by
  -- Induction on the number `r` of conditions in `BijectiveUpTo`, for all functors at once.
  refine allBijective_iff_forall_bijectiveUpTo.mpr fun r ↦ ?_
  induction r generalizing S with
  | zero => tauto
  | succ r ih =>
    -- cover `S` by a sum of representables: the cover satisfies every condition, the kernel
    -- the first `r`, so `S` satisfies the first `r + 1`
    obtain ⟨ι, c, g, h_exact, -⟩ := exists_acyclic_cover S
    exact hf.bijectiveUpTo_quotient h_exact
      (allBijective_iff_forall_bijectiveUpTo.mp (h_sum ι c) (r + 1)) (ih _)

/-- Let θ be a finite family of classes in Ext(G∘φ, F), for a functor φ. If the Leray–Hirsch map
`New.Variety.lerayHirsch` is bijective at ℤ[h_c], the free abelian functor on h_c = Hom(c, −), for
every object c of the target of φ, it is bijective at every S. Here `S`, `G` are functors `A ⥤ Ab`,
`F` is a functor `C ⥤ Ab`, and `I` is the finite index type of the classes. -/
lemma isLerayHirschBasis_of_reprBy [Finite I] {φ : C ⥤ A}
    {θ : ∀ i : I, H (restrictAlong φ G) F (d i)}
    (h_repr : ∀ c : A, IsLerayHirschBasis θ (freeAb (reprBy c))) (S : AbFunctor A) :
    IsLerayHirschBasis θ S := by
  -- By dévissage it suffices to treat a disjoint union of representable functors `reprBy (X c)`.
  -- Restriction to the summands turns both sides into products, where `h_repr` applies factorwise.
  refine isLerayHirschBasis_iff_allBijective_truncMap.mpr
    (lerayHirsch.devissage.allBijective_of_allBijective_sigma_reprBy
      (fun ι X ↦ isLerayHirschBasis_iff_allBijective_truncMap.mp ?_) S)
  -- by `H.sigma_bijective` (cohomology turns disjoint unions into products), a total class on a
  -- disjoint union is determined by its restrictions to the summands
  have h_inj {D : Type 1} [Category D] (Y : ι → D ⥤ Type 1) (K : AbFunctor D) :
      Injective fun (x : TotalH (freeAb (sigma Y)) K) c ↦
        pullbackAlong (freeAb.map (sigma.ι Y c)) x := by
    intro x x' h_eq
    ext m
    refine (sigma_bijective Y K m).injective (funext fun c ↦ ?_)
    -- in degree `m`, the restrictions of `x` and `x'` to the summand `c` agree
    have h_eq_m : pullbackAlong (freeAb.map (sigma.ι Y c)) x m =
        pullbackAlong (freeAb.map (sigma.ι Y c)) x' m := DFunLike.congr_fun (congrFun h_eq c) m
    simpa [pullbackAlong_eq_map] using h_eq_m
  -- restriction of families of classes to the summands
  let Y (c : ι) : A ⥤ Type 1 := reprBy (X c)
  let restr (x : I →₀ TotalH (freeAb (sigma Y)) G) (c : ι) : I →₀ TotalH (freeAb (Y c)) G :=
    x.mapRange _ (pullbackAlong (freeAb.map (sigma.ι Y c))).map_zero
  have h_restr : Bijective restr := by
    refine ⟨fun x x' h_eq ↦ Finsupp.ext fun i ↦ ?_, fun w ↦ ?_⟩
    · exact h_inj _ _ (funext fun c ↦ DFunLike.congr_fun (congrFun h_eq c) i)
    -- representable functors have cohomology in degree 0 only, so glue the degree 0 parts;
    -- `I` is finite, so the glued family has finite support
    have h_glue (i : I) : ∃ y : H (freeAb (sigma Y)) G 0,
        (fun c ↦ H.map G (freeAb.map (sigma.ι Y c)) 0 y) = fun c ↦ w c i 0 :=
      (sigma_bijective Y G 0).surjective fun c ↦ w c i 0
    choose y hy using h_glue
    refine ⟨equivFunOnFinite.symm fun i ↦ of _ 0 (y i), ?_⟩
    ext c i (_ | m)
    · simpa [restr, pullbackAlong_eq_map] using congrFun (hy i) c
    · subsingleton
  -- `lerayHirsch θ` commutes with restriction
  have h_comm (x : I →₀ TotalH (freeAb (sigma Y)) G) (c : ι) : lerayHirsch θ _ (restr x c) =
      pullbackAlong (freeAb.map (sigma.ι (fun c ↦ φ ⋙ Y c) c)) (lerayHirsch θ _ x) :=
    lerayHirsch_mapRange_comp θ map_homClass x
  have h_prod : Bijective fun x c ↦ lerayHirsch θ _ (restr x c) :=
    (Bijective.piMap fun c ↦ h_repr (X c)).comp h_restr
  -- so `lerayHirsch θ` followed by the injective restriction map is bijective, hence so is
  -- `lerayHirsch θ`
  refine .of_comp_left ?_ (h_inj (fun c ↦ φ ⋙ Y c) F)
  rwa [funext₂ h_comm] at h_prod

end New.Variety

end
