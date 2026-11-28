import Lib.Adelic.Witt.WittTheorem

/-!
# Components of unitary adelic points at places; sums and moves of hermitian spaces

Elements of the finite adelic unitary group `New.Gf` of a CM field are studied through their
components `g.atPlace w`. The component at `w̄` is determined by the one at `w`, and is `1` exactly
when that one is, so supports have the form `S ∪ S̄`. Elements are cut along the idempotent
`New.idem` of a set of places. A hermitian space with a point `New.Space E n s` is a matrix `J` over
`E` together with `x` in `GL n (𝔸 E)` such that `xᴴ J x` is the diagonal matrix of the signs `s` at
infinity and `1` at the finite places.

## Main definitions and results

* `New.Gf.componentOn`: keeps the components at `S ∪ S̄` and replaces the others by `1`.
* `New.Gf.exists_supportedOn_mul_trivialOn`: splitting into a part supported on `S ∪ S̄` and one
  trivial there.
* `New.Gf.mem_of_stdLevel_le_of_supportedOn_le`: `New.stdLevel` and the elements supported at one
  pair `w, w̄` generate the group.
* `New.range_ofSplitPlace`, `New.ofSplitPlaces`: elements with prescribed components at split
  places.
* `New.U.sum`, `New.G.sum`, `New.Space.sum`: block diagonal sums.
* `New.G.neg`, `New.Space.neg`: passing from signs `s` to `-s` (and from `J` to `-J`).
* `New.signedSpace`: the standard space with matrix `diag(s)`.

Notions from other files:
* `New.idem`: The finite adele with component 1 at the places of a set and 0 elsewhere.
* `New.ofSplitPlace`: For a split place w, the homomorphism GL_n(E_w) → G_f sending g to the unitary
  element with component g at w and 1 off w, w̄.
* `New.G`: The adelic unitary group G = G_∞ × G_f (an element `g` has adelic matrix `g.adeleMatrix`)
  for signs s at the infinite places and the identity matrix at the finite places.
* `New.stdForm`: The diagonal adelic matrix that is diag(s) at infinity and 1 at the finite places.
-/

noncomputable section

/-!
## Components at sets of places and elements at split places

Conventions: `star` is complex conjugation, on places too; `New.Gf.supportedOn` is the subgroup
trivial outside `S ∪ S̄` and `New.Gf.trivialOn` the one trivial on `S`; `New.localIntGL` is
`GL_n(O_w)`, and `New.stdLevel` is the subgroup of `New.Gf` of integral matrices with integral
inverse.
-/

namespace New

open Gf NumberField Filter Matrix MonoidHom

section ComponentsAtPlaces

variable {E : Type*} [Field E] [NumberField E] {n : Type*} [Fintype n] [DecidableEq n]

/-- For a set `S` of places, cutting `g` along the idempotent of `S` (`cutGL`) keeps the component
`g.map (evalAt w)` at `w` if `w ∈ S` and replaces it by `1` otherwise. -/
lemma map_evalAt_cutGL (w : FinPlace E) (S : Set (FinPlace E)) [Decidable (w ∈ S)]
    (g : GL n (𝔸f E)) :
    (cutGL (idem_mul_self S) g).map (evalAt w) = if w ∈ S then g.map (evalAt w) else 1 := by
  aesop (add simp [cutGL, Matrix.one_apply])

/-- A matrix over the finite adeles lies in `intGL n (Ô E) = GL_n(Ô)` (entries of `g` and `g⁻¹` in
`Ô`), where `Ô` is the ring of integral finite adeles, if and only if its component at each place
`w` lies in `localIntGL n w = GL_n(O_w)`. -/
lemma mem_intGL_Ô {g : GL n (𝔸f E)} :
    g ∈ intGL n (Ô E) ↔ ∀ w : FinPlace E, g.map (evalAt w) ∈ localIntGL n w := by
  simp [Ô, ← map_inv, mem_intGL, forall_and, forall_comm (α := FinPlace E)]

lemma isOpen_localIntGL (w : FinPlace E) : (localIntGL n w).IsOpen :=
  isOpen_intGL (Valued.isOpen_integer _)

lemma isCompact_localIntGL (w : FinPlace E) :
    IsCompact (localIntGL n w : Set (GL n (LocField w))) :=
  isCompact_intGL (isCompact_LocInt w)

variable [IsCMField E] (S : Set (FinPlace E)) {g k : Gf E n} {u : FinPlace E} (w : FinPlace E)

/-- The set S ∪ S̄ of the finite places in S and their complex conjugates. -/
abbrev _root_.Set.conjClosure : Set (FinPlace E) := S ∪ star ⁻¹' S

lemma _root_.Set.Finite.conjClosure (hS : S.Finite) : S.conjClosure.Finite := hS.union hS.star

/-- The set S of finite places is disjoint from its complex conjugate: its places are not
self-conjugate, and it holds at most one place of each conjugate pair. -/
abbrev _root_.Set.IsConjDisjoint : Prop := Disjoint S (star ⁻¹' S)

@[fun_prop]
lemma Gf.continuous_atPlace : Continuous (Gf.atPlace (n := n) w) := by
  simp only [atPlace, MonoidHom.coe_comp]
  fun_prop

variable {S w}

@[ext]
lemma Gf.ext (h_eq : ∀ w : FinPlace E, g.atPlace w = k.atPlace w) : g = k :=
  Subtype.ext (GL_ext_evalAt h_eq)

/-! ### Integrality and supports in the unitary group -/

/-- For a unitary adelic matrix `g` and places with `ū = w`, the component at `w` is the
transpose of the conjugate (`conjLoc`, carrying `E_u` to `E_w`) of the inverse of the component
at `u`. -/
lemma Gf.atPlace_star (huw : star u = w) :
    g.atPlace w = ((g.atPlace u)⁻¹.val.map (conjLoc huw))ᵀ := by
  -- `g` is unitary, so `g = star g⁻¹`; take components at `w`
  change g.val.val.map (evalAt w) = _
  rw [show g.val.val = (g⁻¹).val.valᴴ from U.inv_val_eq_conjTranspose g⁻¹]
  exact evalAt_star_GL huw (g⁻¹).val

/-- The component of an element of the finite adelic unitary group lies in
`localIntGL n w = GL_n(O_w)` for all but finitely many places `w`. -/
lemma Gf.eventually_atPlace_mem_localIntGL :
    ∀ᶠ w : FinPlace E in cofinite, g.atPlace w ∈ localIntGL n w := by
  -- each entry of `g` and of `g⁻¹` is a finite adele, so integral at almost all places
  have h_entries (k : Gf E n) (i j : n) :
      ∀ᶠ w : FinPlace E in cofinite, (k.atPlace w).val i j ∈ LocInt w := (k.val i j).property
  -- keep `∀ᶠ` folded, and the inverse as a unit, so that `mem_intGL` applies
  simpa [-eventually_cofinite, -coe_units_inv, mem_intGL, map_inv]
    using And.intro (h_entries g) (h_entries g⁻¹)

/-- An element lies in the integral subgroup `stdLevel` if and only if each of its components lies
in `localIntGL n w = GL_n(O_w)`. -/
lemma mem_stdLevel_iff : g ∈ stdLevel E n ↔ ∀ w : FinPlace E, g.atPlace w ∈ localIntGL n w :=
  mem_intGL_Ô

/-- By unitarity, the component at `w̄` is integral if and only if the component at `w` is. -/
@[simp]
lemma Gf.atPlace_star_mem_iff :
    g.atPlace (star w) ∈ localIntGL n (star w) ↔ g.atPlace w ∈ localIntGL n w := by
  simp_all [iff_def, ← map_inv, atPlace_star, mem_LocInt, mem_intGL]

/-- `g` is supported on `S ∪ S̄` if and only if its component is `1` at every place `w` with
neither `w` nor `w̄` in `S`. -/
@[simp low]
lemma Gf.mem_supportedOn :
    g ∈ supportedOn n S ↔ ∀ w : FinPlace E, w ∉ S → star w ∉ S → g.atPlace w = 1 := by
  simp [supportedOn]

@[simp low]
lemma Gf.mem_trivialOn : g ∈ trivialOn n S ↔ ∀ w ∈ S, g.atPlace w = 1 := by simp [trivialOn]

/-- By unitarity, the component at `w̄` is `1` if and only if the component at `w` is. -/
lemma Gf.atPlace_star_eq_one_iff : g.atPlace (star w) = 1 ↔ g.atPlace w = 1 := by
  have h_imp (u v : FinPlace E) (huv : star u = v) (hu : g.atPlace u = 1) : g.atPlace v = 1 :=
    Units.ext (by simp [atPlace_star huv, hu])
  exact ⟨h_imp (star w) w (star_star w), h_imp w (star w) rfl⟩

lemma Gf.supportedOn_mono {T : Set (FinPlace E)} (hST : S ⊆ T) :
    supportedOn n S ≤ supportedOn n T := by
  grind [mem_supportedOn, IsConcreteLE.le_iff]

/-- If `g` is supported on `S ∪ S̄` and `k` is trivial on `S`, one of them is `1` at each place. -/
lemma Gf.atPlace_eq_one_or (hg : g ∈ supportedOn n S) (hk : k ∈ trivialOn n S) :
    ∀ u : FinPlace E, g.atPlace u = 1 ∨ k.atPlace u = 1 := by
  grind [mem_supportedOn, mem_trivialOn, atPlace_star_eq_one_iff]

/-- The elements supported outside `S ∪ S̄` are those whose components at the places of `S`
are `1`. -/
lemma Gf.supportedOn_compl : supportedOn n S.conjClosureᶜ = trivialOn n S := by
  ext g
  grind [mem_supportedOn, mem_trivialOn, atPlace_star_eq_one_iff, star_star]

/-- An element supported on `S ∪ S̄` commutes with one that is trivial on `S`. -/
lemma Gf.commute_supportedOn_trivialOn (hg : g ∈ supportedOn n S) (hk : k ∈ trivialOn n S) :
    Commute g k :=
  ext fun u ↦ by rcases atPlace_eq_one_or hg hk u with h_one | h_one <;> simp [h_one]

/-- Two elements supported on `S ∪ S̄` that agree at the places of `S` are equal. -/
lemma Gf.eq_of_supportedOn (hg : g ∈ supportedOn n S) (hk : k ∈ supportedOn n S)
    (h_eq : ∀ w ∈ S, g.atPlace w = k.atPlace w) : g = k := by
  ext1 u
  by_cases hu : u ∈ S
  · exact h_eq u hu
  by_cases hu_star : star u ∈ S
  · -- the component at `u` is determined by the one at its conjugate
    exact Units.ext (by simp only [atPlace_star (star_star u), h_eq (star u) hu_star])
  · rw [mem_supportedOn.1 hg u hu hu_star, mem_supportedOn.1 hk u hu hu_star]

/-- An element supported on `S ∪ S̄` is integral if and only if its components at the places
of `S` are integral. -/
lemma Gf.mem_stdLevel_iff_of_supportedOn (hg : g ∈ supportedOn n S) :
    g ∈ stdLevel E n ↔ ∀ w ∈ S, g.atPlace w ∈ localIntGL n w := by
  grind [atPlace_star_mem_iff, mem_stdLevel_iff, mem_supportedOn, one_mem]

/-! ### The part supported on `S ∪ S̄`, and generation by local elements -/

@[simp]
lemma star_idem_conjClosure : star (idem S.conjClosure) = idem S.conjClosure := by
  simp [star_idem, S.union_comm]

variable (n S) in
/-- The endomorphism of the finite adelic unitary group that keeps the components at the places
of S ∪ S̄ and replaces the others by 1. -/
def Gf.componentOn : Gf E n →* Gf E n := U.cutAt (idem_mul_self S.conjClosure) star_idem_conjClosure

open scoped Classical in
@[simp]
lemma Gf.atPlace_componentOn :
    (componentOn n S g).atPlace w = if w ∈ S.conjClosure then g.atPlace w else 1 :=
  map_evalAt_cutGL w S.conjClosure g.val

lemma Gf.componentOn_mem_supportedOn : componentOn n S g ∈ supportedOn n S := by simp_all

lemma Gf.componentOn_mem_stdLevel (hg : g ∈ stdLevel E n) : componentOn n S g ∈ stdLevel E n := by
  grind [atPlace_componentOn, mem_stdLevel_iff, one_mem]

/-- Every `g` in the finite adelic unitary group is a product `a * b` with `a` supported on `S ∪ S̄`
and `b` trivial at the places of `S`, such that `a` and `b` lie in the integral subgroup `stdLevel`
whenever `g` does. -/
lemma Gf.exists_supportedOn_mul_trivialOn (S : Set (FinPlace E)) (g : Gf E n) :
    ∃ a ∈ supportedOn n S, ∃ b ∈ trivialOn n S,
      g = a * b ∧ (g ∈ stdLevel E n → a ∈ stdLevel E n ∧ b ∈ stdLevel E n) := by
  -- at a place of `S` the component of the second factor is `g⁻¹ * g = 1`
  refine ⟨componentOn n S g, componentOn_mem_supportedOn, componentOn n S g⁻¹ * g, by simp_all,
    by simp [map_inv], fun hg ↦ ⟨componentOn_mem_stdLevel hg, ?_⟩⟩
  exact mul_mem (componentOn_mem_stdLevel (inv_mem hg)) hg

/-- A subgroup `H` of the finite adelic unitary group that contains the integral subgroup `stdLevel`
and, for every finite place `w`, all elements supported on `{w, w̄}` contains every element of the
group. -/
lemma Gf.mem_of_stdLevel_le_of_supportedOn_le {H : Subgroup (Gf E n)} (h_std : stdLevel E n ≤ H)
    (h_local : ∀ w : FinPlace E, supportedOn n ({w} : Set (FinPlace E)) ≤ H) (g : Gf E n) :
    g ∈ H := by
  -- `g` is integral outside a finite set `S` of places; induct on `S`.
  obtain ⟨S, hS, hg : ∀ w ∉ S, g.atPlace w ∈ localIntGL n w⟩ :=
    hasBasis_cofinite.eventually_iff.1 g.eventually_atPlace_mem_localIntGL
  induction S, hS using Set.Finite.induction_on generalizing g with
  | empty => exact h_std (mem_stdLevel_iff.2 fun w ↦ hg w (Set.notMem_empty w))
  | @insert v S _ _ ih =>
    -- Split off the components at `v` and its conjugate: `g = a * b`.
    obtain ⟨a, ha, b, hb, rfl, -⟩ := g.exists_supportedOn_mul_trivialOn {v}
    refine mul_mem (h_local v ha) (ih b fun w hwS ↦ ?_)
    -- Where `b` is not trivial, `w ≠ v` and `a` is trivial, so `b` agrees with `a * b`.
    by_cases hb1 : b.atPlace w = 1
    · simp [hb1]
    · have ha1 : a.atPlace w = 1 := (atPlace_eq_one_or ha hb w).resolve_right hb1
      have hwv : w ≠ v := fun h ↦ hb1 (mem_trivialOn.1 hb w h)
      simpa [ha1] using hg w (by simp [hwv, hwS])

end ComponentsAtPlaces

section SplitPlaces

variable {E : Type*} [Field E] [NumberField E] {n : Type*} [Fintype n] [DecidableEq n]
  [IsCMField E] {w : FinPlace E} (hw : star w ≠ w) (g : GL n (LocField w))

/-! ### Split places -/

/-- For a place `w ≠ w̄`, the component of `ofSplitPlace hw g` (the unitary element with component
`g` at `w`) at a place other than `w` and `w̄` is `1`. -/
@[local simp]
lemma atPlace_ofSplitPlace_of_ne {u : FinPlace E} (hu : u ≠ w) (hu_star : star u ≠ w) :
    (ofSplitPlace hw g).atPlace u = 1 := by
  simp_all [ofSplitPlace, atPlace, evalAt_star_singleGL]

@[simp]
lemma ofSplitPlace_mem_supportedOn :
    ofSplitPlace hw g ∈ supportedOn n ({w} : Set (FinPlace E)) := by aesop

/-- For a finite place `w` of the CM field `E` with `w̄ ≠ w`, the image of the homomorphism
`ofSplitPlace hw` from `GL_n(E_w)` to the finite adelic unitary group, which sends `g` to the
element with component `g` at `w` and `1` off `w, w̄`, is the subgroup `supportedOn n {w}` of
elements with component `1` at every place other than `w` and `w̄`. -/
lemma range_ofSplitPlace : (ofSplitPlace hw).range = supportedOn n ({w} : Set (FinPlace E)) := by
  refine le_antisymm (by aesop (add simp IsConcreteLE.le_iff)) fun k hk ↦ ⟨k.atPlace w, ?_⟩
  -- an element supported on `w` and its conjugate is determined by its component at `w`
  exact eq_of_supportedOn (ofSplitPlace_mem_supportedOn hw (k.atPlace w)) hk (by simp)

/-- For a split place `w`, the element `ofSplitPlace hw g` is integral if and only if
`g ∈ localIntGL n w = GL_n(O_w)`. -/
@[simp]
lemma ofSplitPlace_mem_stdLevel : ofSplitPlace hw g ∈ stdLevel E n ↔ g ∈ localIntGL n w := by
  simp [mem_stdLevel_iff_of_supportedOn (ofSplitPlace_mem_supportedOn hw g)]

/-- For a split place `w`, the embedding `ofSplitPlace hw` of `GL_n(E_w)` into the finite adelic
unitary group is continuous. -/
@[fun_prop]
lemma continuous_ofSplitPlace : Continuous (ofSplitPlace (n := n) hw) := by
  -- the matrix of `singleGL w g` is `1` plus the matrix `g - 1` embedded entrywise at `w`
  have h_locGL : Continuous (singleGL w : GL n (LocField w) → GL n (𝔸f E)) :=
    Continuous.units_map _
      (by fun_prop : Continuous fun g : Matrix n n (LocField w) ↦ 1 + (g - 1).map (singleAdele w))
  -- `ofSplitPlace hw g` is `singleGL w g * star (singleGL w g⁻¹)`
  exact Continuous.subtype_mk
    (f := fun g : GL n (LocField w) ↦ singleGL w g * star (singleGL w g⁻¹)) (by fun_prop) _

variable {S : Finset (FinPlace E)} (hS : ∀ w ∈ S, star w ∉ S)

/-- For a finite set `S` of finite places disjoint from `S̄`, the homomorphism sending a family
`(g_w)` in `∏ w ∈ S, GL_n(E_w)` to the unitary element with component `g_w` at each `w` in `S`
and `1` off `S ∪ S̄`. -/
def ofSplitPlaces : (∀ w : S, GL n (LocField w.val)) →* Gf E n :=
  -- the factors commute: at each place one of the two is trivial
  noncommPiCoprod (fun w : S ↦ ofSplitPlace (n := n) (w := w.val) (by grind)) fun v w hvw g h ↦
    commute_supportedOn_trivialOn (ofSplitPlace_mem_supportedOn _ _) (by simp (disch := grind))

/-- For a finite set `S` of places of the CM field `E` disjoint from `S̄` and a family
`g w ∈ GL_n(E_w)` for `w` in `S`, the component at `w ∈ S` of the finite adelic unitary element
`ofSplitPlaces hS g` (the product of the elements `ofSplitPlace _ (g w)` concentrated at `w, w̄`) is
`g w`. -/
@[simp]
lemma atPlace_ofSplitPlaces (g : (i : S) → GL n (LocField (i : FinPlace E))) (w : S) :
    (ofSplitPlaces (n := n) hS g).atPlace w = g w := by
  classical
  -- Take the factor at `w` out of the product; the other factors are trivial at `w`.
  have h_split : ∀ v : S, star (v : FinPlace E) ≠ v := by grind
  have h_other : ∀ v ∈ (Finset.univ : Finset S).erase w,
      (ofSplitPlace (n := n) (h_split v) (g v)).atPlace w = 1 :=
    fun v hv ↦ atPlace_ofSplitPlace_of_ne (h_split v) (g v) (by grind) (by grind)
  -- `erw`: the commutation proof in `ofSplitPlaces` has a type equal to `Pairwise …` only up to
  -- unfolding `Pairwise`, so `rw` does not find the pattern
  erw [noncommPiCoprod_apply, ← Finset.mul_noncommProd_erase (a := w) (h := Finset.mem_univ w)]
  simp only [map_mul, atPlace_ofSplitPlace, mul_eq_left]
  exact (Gf.atPlace (w : FinPlace E)).ker.noncommProd_mem _ h_other

/-- For a finite set `S` of places disjoint from `S̄`, the finite adelic unitary element
`ofSplitPlaces hS g` with component `g w` at each `w ∈ S` is `1` at every place outside `S ∪ S̄`. -/
lemma ofSplitPlaces_mem_supportedOn (g : (i : S) → GL n (LocField (i : FinPlace E))) :
    ofSplitPlaces hS g ∈ supportedOn n S := by
  -- the image is generated by the images of the factors, each supported on one `{w, w̄}`
  suffices h_le : (ofSplitPlaces (n := n) hS).range ≤ supportedOn n S from h_le ⟨g, rfl⟩
  exact (noncommPiCoprod_range _).trans_le
    (iSup_le fun w ↦ (range_ofSplitPlace _).trans_le (supportedOn_mono (by simp)))

/-- For a finite set `S` of places disjoint from `S̄`, the element `ofSplitPlaces hS g` with
component `g w` at each `w ∈ S` lies in the integral subgroup `stdLevel E n` if and only if every
`g w` lies in `localIntGL n w = GL_n(O_w)`. -/
lemma ofSplitPlaces_mem_stdLevel (g : (i : S) → GL n (LocField (i : FinPlace E))) :
    ofSplitPlaces hS g ∈ stdLevel E n ↔ ∀ w : S, g w ∈ localIntGL n w := by
  rw [mem_stdLevel_iff_of_supportedOn (ofSplitPlaces_mem_supportedOn _ _), Subtype.forall']
  simp

end SplitPlaces

end New

/-!
## Constructions on hermitian spaces with a point

Negation of spaces and the standard spaces need an element of norm `-1` in the integral finite
adeles (`New.Weil.normNegOne`), which exists under the hypothesis `New.HasPrimitiveRoot5040`: the
field contains a primitive root of unity of order `5040`.
-/

section SpaceOperations

open NumberField Matrix

namespace New

section

variable {m n R : Type*} [DecidableEq m] [DecidableEq n] [CommRing R]

/-! ### Sign matrices, and blocks and reindexing over a ring -/

/-- The homomorphism GL_m(R) × GL_n(R) → GL_{m+n}(R) sending (g, h) to the block diagonal matrix
diag(g, h). -/
@[simps! apply_val]
def blockGL [Fintype m] [Fintype n] : GL m R × GL n R →* GL (m ⊕ n) R where
  toFun g :=
    { val := fromBlocks g.1 0 0 g.2
      inv := fromBlocks ↑g.1⁻¹ 0 0 ↑g.2⁻¹
      val_inv := by simp [fromBlocks_multiply]
      inv_val := by simp [fromBlocks_multiply] }
  map_one' := by ext : 1; simp
  map_mul' g h := by ext : 1; simp [fromBlocks_multiply]

/-- The block diagonal sum of the sign matrices `signMatrix s = diag(s)` and `signMatrix t` of s and
t is that of the concatenated signs. -/
lemma signMatrix_sum (s : m → ℤˣ) (t : n → ℤˣ) :
    fromBlocks (signMatrix s) 0 0 (signMatrix t) = signMatrix (n := m ⊕ n) (s ⊕ᵥ t) := by
  simp [signMatrix]

@[simp]
lemma signMatrix_neg (s : n → ℤˣ) : signMatrix (-s) = -signMatrix (n := n) s := by simp [signMatrix]

variable [Fintype m] [Fintype n] [StarRing R] (e : m ≃ n) {J : Matrix m m R}

/-- For a bijection e of index sets, the isomorphism GL_m(R) ≅ GL_n(R) relabelling rows and
columns along e. -/
@[simps! apply_val]
def reindexGL : GL m R ≃* GL n R := Units.mapEquiv (reindexRingEquiv R e).toMulEquiv

/-- The block embedding `U J × U J' → U J''`, `(g, h) ↦ diag(g, h)`, where `J''` is the block
diagonal sum of `J` and `J'`. -/
def U.sum {J' : Matrix n n R} {J'' : Matrix (m ⊕ n) (m ⊕ n) R} (h : fromBlocks J 0 0 J' = J'') :
    U J × U J' →* U J'' :=
  (blockGL.comp ((U J).subtype.prodMap (U J').subtype)).codRestrict (U J'') <| by
    aesop (add simp [mem_U, fromBlocks_conjTranspose, fromBlocks_multiply])

/-- The block diagonal homomorphism U_m(R) × U_n(R) → U_{m+n}(R), (g, h) ↦ diag(g, h), between
the unitary groups of identity matrices. -/
abbrev U.blockSumOne :
    U (1 : Matrix m m R) × U (1 : Matrix n n R) →* U (1 : Matrix (m ⊕ n) (m ⊕ n) R) :=
  sum (fromBlocks_one (l := m) (m := n) (α := R))

/-- Renaming the basis by `e` identifies the unitary group of `J` with that of the form `J'`
obtained from `J` by the same renaming of rows and columns. -/
def U.reindex {J' : Matrix n n R} (h : J.submatrix e.symm e.symm = J') : U J ≃* U J' where
  toEquiv := (reindexGL e).subtypeEquiv <| by
    subst h
    simp [← ext_iff, reindex_equiv e.symm, mem_U]
  map_mul' := by simp

variable {l : Type*} [Fintype l] [DecidableEq l] (e : m ⊕ l ≃ n)

/-- The block diagonal embedding U(1_m) × U(1_l) → U(1_n) of unitary groups of identity
matrices, along a bijection of the disjoint union of m and l with n. -/
def U.block : U (1 : Matrix m m R) × U (1 : Matrix l l R) →* U (1 : Matrix n n R) :=
  (reindex e (submatrix_one_equiv e.symm)).toMonoidHom.comp blockSumOne

/-- The matrix of the image of a pair `g = (g₁, g₂)` of unitary matrices (`New.U J` is the unitary
group of the form `J`) under `New.U.block e` is diag(g₁, g₂) with rows and columns relabelled
along `e`. -/
@[simp]
lemma U.block_val (g : U (1 : Matrix m m R) × U (1 : Matrix l l R)) :
    (block e g).val.val = (fromBlocks g.1 0 0 g.2).submatrix e.symm e.symm := rfl

end

section

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]
  {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] {s : n → ℤˣ} {t : m → ℤˣ}

/-! ### The adelic unitary groups -/

/-- The block diagonal embedding of the product of the adelic unitary groups for signs s and t
into the one for the concatenated signs. -/
def G.sum : G E s × G E t →* G E (s ⊕ᵥ t) :=
  .prod (.mk' (fun g w ↦ U.sum (signMatrix_sum s t) (g.1.1 w, g.2.1 w))
      (by simp [← map_mul, funext_iff]))
    ((U.sum (by simp)).comp (.prodMap (.snd (GInf E s) (Gf E n)) (.snd (GInf E t) (Gf E m))))

/-- The adelic matrix (`New.G.adeleMatrix`) of the block sum of g₁ and g₂ is diag(g₁, g₂). -/
@[simp]
lemma G.adeleMatrix_sum (g : G E s × G E t) :
    (sum g).adeleMatrix = g.1.adeleMatrix.fromBlocks 0 0 g.2.adeleMatrix := by
  ext (i | i) (j | j) <;> rfl

/-- The isomorphism between the adelic unitary groups for signs s and −s that is the identity on
matrices, since U(J) = U(−J) at each infinite place. -/
def G.neg : G E s ≃* G E (-s) :=
  .prodCongr (.piCongrRight fun _ ↦ MulEquiv.subgroupCongr (by simp [U])) (.refl (Gf E n))

omit [IsCMField E] [Fintype m] [Fintype n] in
/-- The standard adelic forms for signs s and t have as block diagonal sum the standard form for
the concatenated signs. -/
lemma stdForm_sum : fromBlocks (stdForm E s) 0 0 (stdForm E t) = stdForm E (s ⊕ᵥ t) := by
  simp [stdForm]

end

variable {E : Type*} [Field E] [CMType E] {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
  [DecidableEq n] {s : n → ℤˣ} {t : m → ℤˣ} (V : Space E n s) (e : n ≃ m) (h : s ∘ e.symm = t)
  (g : G E s)

/-- If `a w` carries `J`, embedded in `ℂ` by the CM type, to the diagonal matrix of signs `s` at
each infinite place `w` and `b` carries `J` to `1` over the finite adeles, then the adelic matrix
with components `a` and `b` (`New.mkAdelicGL`) carries `J` to the standard form. Here `Φ w` is
the embedding of `E` chosen at `w` and `toAdele` is the diagonal embedding of `E`. -/
lemma gram_mkAdelicGL {J : Matrix n n E} {a : InfinitePlace E → GL n ℂ} {b : GL n (𝔸f E)}
    (ha : ∀ w : InfinitePlace E, (a w).valᴴ * map J (Φ w) * (a w).val = signMatrix s)
    (hb : b.valᴴ * J.map (algebraMap E (𝔸f E)) * b.val = 1) :
    (mkAdelicGL (a, b)).valᴴ * J.map toAdele * (mkAdelicGL (a, b)).val = stdForm E s := by
  apply matrix_ext_𝔸
  -- on the infinite components the identity is `ha`, on the finite one `hb`; `↓` maps the
  -- product factor by factor first
  · simpa [↓Matrix.map_mul, stdForm]
  · simpa [↓Matrix.map_mul, stdForm]

section

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] (e : n ≃ m) (h : s ∘ e.symm = t)
  (g : G E s)

@[simp]
lemma G.adeleMatrix_neg : (neg g).adeleMatrix = g.adeleMatrix := by ext <;> rfl

/-- For a bijection of index sets carrying signs s to signs t, the isomorphism of the
corresponding adelic unitary groups relabelling rows and columns in every component. -/
def G.reindex : G E s ≃* G E t :=
  toUnitary.trans ((U.reindex e (by simp [← h, stdForm])).trans toUnitary.symm)

@[simp]
lemma G.adeleMatrix_reindex :
    (reindex e h g).adeleMatrix = g.adeleMatrix.submatrix e.symm e.symm := rfl

end

variable [HasPrimitiveRoot5040 E]

/-! ### A unit of norm `-1` and the standard spaces -/

/-- For a field `E` with a primitive root of unity of order 5040, a chosen element ε of Ô with
ε̄ε = −1, as a unit with inverse −ε̄. It exists by `New.exists_unit_star_mul_self_eq`. -/
def Weil.normNegOne {E : Type*} [Field E] [NumberField E] [IsCMField E] [HasPrimitiveRoot5040 E] :
    (Ô E)ˣ :=
  have h_norm := exists_unit_star_mul_self_eq (u := -1) (by simp) (by simp)
  Units.mkOfMulEqOne h_norm.choose (-star h_norm.choose.1) (by
    ext1
    rw [mul_neg]
    change -(h_norm.choose.val.val * star h_norm.choose.val.val) = (1 : 𝔸f E)
    grind)

open Weil

@[simp]
lemma star_normNegOne_mul_self {E : Type*} [Field E] [NumberField E] [IsCMField E]
    [HasPrimitiveRoot5040 E] : star normNegOne.val.val * normNegOne.val.val = (-1 : 𝔸f E) := by
  simpa [normNegOne] using (exists_unit_star_mul_self_eq (E := E) (u := -1) (by simp)
    (by simp)).choose_spec

variable (E)

/-- The idele that is 1 at the infinite places and whose finite part is the unit
ε = `New.Weil.normNegOne` of Ô, with ε̄ε = −1. -/
def normNegOneIdele (E : Type*) [Field E] [NumberField E] [IsCMField E] [HasPrimitiveRoot5040 E] :
    (𝔸 E)ˣ := normNegOne.map (MonoidHom.prod 1 (Ô E).subtype.toMonoidHom)

/-- If `E` contains a primitive root of unity of order 5040, the standard space with matrix
diag(s). Its point is diagonal, with entry 1 where s_i = 1 and `normNegOneIdele E` (the idele
with finite part of norm −1) where s_i = −1. -/
def signedSpace (s : n → ℤˣ) : Space E n s where
  J := diagonal fun i ↦ s i
  x := diagGL fun i ↦ if s i = 1 then 1 else normNegOneIdele E
  gram_point := by
    -- where `s i = -1` the norm `-1` of the finite part cancels the sign
    simp_all [apply_ite, ite_apply, normNegOneIdele, funext_iff, stdForm, Prod.ext_iff,
      Int.units_ne_iff_eq_neg]

variable {E}

namespace Space

/-! ### Operations on spaces -/

/-- For spaces V, W with signs s, t, the space with concatenated signs whose matrix and point
are the block diagonal sums of those of V and W. -/
def sum (W : Space E m t) : Space E (n ⊕ m) (s ⊕ᵥ t) where
  J := V.J.fromBlocks 0 0 W.J
  x := blockGL (V.x, W.x)
  gram_point := by
    simp [fromBlocks_conjTranspose, fromBlocks_map, fromBlocks_multiply, gram_point, stdForm]

/-- For a space V with signs s and an index bijection carrying s to t, the space with signs t
obtained by relabelling its matrix and point. -/
def reindex : Space E m t where
  J := V.J.reindex e e
  x := reindexGL e V.x
  gram_point := by
    subst h
    simp [← submatrix_map, gram_point, stdForm]

/-- If `E` contains a primitive root of unity of order 5040 and (J, x) is a space with signs s,
the space with signs −s, matrix −J and point x multiplied by the scalar `normNegOneIdele E`, the
idele that is 1 at infinity and whose finite part has norm −1. -/
def neg : Space E n (-s) where
  J := -V.J
  x := normNegOneIdele E • V.x
  gram_point := by
    -- At the finite places the norm `-1` of the scaling factor cancels the sign of `-V.J`.
    simp [Matrix.map_neg, normNegOneIdele, Units.smul_def, ← diagonal_smul, gram_point, stdForm,
      Prod.ext_iff, funext_iff]
    grind [star_normNegOne_mul_self]

/-- For a space (J, x) and g in G, the space (J, xg): the same matrix with the point moved by g. -/
def move : Space E n s where
  J := V.J
  x := V.x * g.toUnitary.1
  gram_point := gram_mul_of_gram_eq V.gram_point g.toUnitary.2

attribute [simps J] signedSpace sum reindex neg move

end Space

end New

end SpaceOperations

end
