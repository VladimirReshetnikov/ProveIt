import Lib.Shimura.HeckeTower.HeckeData
import Lib.Weil.Unramified.SplitHecke

/-!
# Steps E'/E of base change and commuting families of Hecke operators

This file sets up base change along an extension `E'/E` of prime degree. It records
place-by-place properties of base change `New.baseChangeGf` and of the Galois action
`New.galoisGf` on the finite adelic unitary group. It defines matching pairs of test functions at
the places above a set `S` of places. It relates operators on fixed vectors to functions on the
group through a common element of the group ring, and builds commuting families of local and
spherical Hecke operators.

## Main definitions and results

* `New.IsStep`: the extension `E'/E` with a character `μ` of the finite ideles of `E` that detects
  norms: `μ (z z̄) = 1` exactly when `z` is a principal idele times a norm from `E'`.
* `New.IsMatched`: the places of `E` that split completely in `E'` and at which `μ` is trivial.
* `New.placesAbove E' S`: the places of `E'` above `S ∪ S̄`; `New.IsMatchingPairAbove`: matching
  pairs of functions (`New.IsMatchingPair`) at these places.
* `New.IsLocalRetraction`, `New.isLocalRetraction_ofSplitPlace`: a group `A` that is a retract of
  the finite adelic unitary group at a set `S` of places; GL_n of the completion at a split place is
  one.
* `New.exists_isHeckeFunctionRelation`: the Hecke operators of `A` and spherical operators away from
  `S` commute on the vectors fixed by the level, and their products are operators of functions.

Notions from other files:
* `New.adeleNorm`: for an extension `L/K` of number fields, the norm from the finite adeles of `L`
  to the finite adeles of `K`, as a multiplicative map.
* `New.Gf.supportedOn`, `New.Gf.trivialOn`: the elements with component `1` at every place outside
  `S ∪ S̄`, and those with component `1` at every place of `S`.
* `New.localLevel`: the elements whose component at each `w ∈ S` lies in `K w`; by default `K w` is
  `New.localIntGL`, the integral matrices with integral inverse.

## Relation to the literature

Known; see `Lib.GaloisRep.BaseChange.PrimeDegreeTransfer` and `Lib.Adelic.Hecke.ClassSums` for
sources.
-/

/-!
## Steps, compatible CM types and matched places

* `New.CMTypeOver`: a CM type of the larger field that restricts to the given one.
* `New.kerCompNorm`: the ideles of `E'` whose norm is killed by `μ`.
-/

section StepDefs

open NumberField

namespace New

variable {E : Type}
  (E' : Type) [Field E] [NumberField E] [IsCMField E] [Field E'] [NumberField E'] [Algebra E E']
  (μ : outParam ((𝔸f E)ˣ →* ℂˣ))

/-- A step `E'/E` with the character `μ` of the finite ideles of `E`: `E` contains a primitive root
of unity of order `5040`, and `E'` is a CM field Galois over `E` of prime degree. Some integer of
`E'` has trace `1`. The character `μ` has open kernel, is trivial on `E^×`, and `μ (z z̄) = 1`
exactly when `z` is a principal idele times a norm from `E'`. -/
class IsStep [IsCMField E'] extends HasPrimitiveRoot5040 E, IsGalois E E',
  Fact (Module.finrank E E').Prime where
  /-- The kernel of `μ` is open in the finite ideles of `E`. -/
  isOpen_ker : μ.ker.IsOpen
  /-- `μ` is trivial on the principal ideles. -/
  apply_principal (x : Eˣ) : μ (principalIdele x) = 1
  /-- `μ (z z̄) = 1` exactly when `z` is a principal idele times the norm of a finite idele of
  `E'`. -/
  apply_norm_eq_one_iff (z : (𝔸f E)ˣ) :
      μ (z * star z) = 1 ↔
        ∃ (x : Eˣ) (y : (𝔸f E')ˣ), z = principalIdele x * Units.map (adeleNorm E E') y
  /-- Some integer of `E'` has trace `1` down to `E`. -/
  exists_trace_eq_one : ∃ c : 𝓞 E', Algebra.trace E E' c = 1

/-- A CM type of `L` that restricts to the given CM type of `K`: the embedding chosen at a place
extends the one chosen at the place below. -/
class CMTypeOver (K L : Type*) [Field K] [Field L] [Algebra K L]
    [PlaceEmbedding K] extends CMType L where
  /-- An embedding of `L` is the one chosen at its place exactly when its restriction to `K` is the
  embedding chosen at the place below. -/
  eq_chosen_iff (σ : L →+* ℂ) :
      σ = Φ (InfinitePlace.mk σ) ↔
        σ.comp (algebraMap K L) = New.Φ (InfinitePlace.comap (InfinitePlace.mk σ) (algebraMap K L))

/-- The group of finite ideles of `E'` whose norm to `E` is killed by `μ`. -/
noncomputable abbrev kerCompNorm : Subgroup (𝔸f E')ˣ := (μ.comp (Units.map (adeleNorm E E'))).ker

/-- The place `w` of `E` is matched: `μ` is trivial on `E_w^×`, and every place `u` of `E'` above
`w` has the same norm as `w` (`u.q = w.q`, the sizes of the residue fields; so `u` has residue
degree `1`) and is moved by every `σ ≠ 1`. -/
def IsMatched (w : FinPlace E) : Prop :=
  -- (a) `μ` is trivial on the ideles supported at `w`
  (∀ x : (LocField w)ˣ, μ (locIdele w x) = 1) ∧
  -- (b) every place `u` above `w` has the norm of `w` and is moved by every `σ ≠ 1`
  ∀ u : FinPlace E', u.below E = w → u.q = w.q ∧ ∀ σ ≠ (1 : Gal(E'/E)), u.comap σ ≠ u

end New

end StepDefs

namespace New

/-!
## Base change and Galois action place by place

* `New.atPlace_galoisGf`, `New.atPlace_baseChangeGf`: local components;
  `New.baseChangeGf_mem_stdLevel`, `New.baseChangeGf_mem_supportedOn`: base change respects
  integrality and supports.

`g.atPlace w` is the component at `w`; `New.Gf.supportedOn n S` consists of the elements trivial
outside `S ∪ S̄`, `New.Gf.trivialOn n S` of those trivial on `S`; `New.idem S` is the indicator
adele of `S`.
-/

section BaseChangePlaces

open Matrix Valued Module Gf IsGalois

variable {E E' n : Type _} [Field E] [CMType E] [Field E'] [CMType E'] [Algebra E E'] [Fintype n]
  [DecidableEq n] (σ : Gal(E'/E)) (μ : (𝔸f E)ˣ →* ℂˣ) {w : FinPlace E} {u : FinPlace E'}
  (S : Set (FinPlace E)) (g : Gf E n)

/-! ### Places above `S` and local components -/

variable (E') in
/-- The set of finite places of `E'` lying above a place of `S` or above the complex conjugate of a
place of `S`. -/
def placesAbove : Set (FinPlace E') := FinPlace.below (L := E') E ⁻¹' S.conjClosure

omit [CMType E] in
/-- If `σ` pulls the place `u` back to `v`, the component of `σ g` at `u` is the image of the
component of `g` at `v` under `locMap σ h`, the map of completions given by `σ`, where
`h : u.comap σ = v`. -/
lemma atPlace_galoisGf (g : Gf E' n) {v : FinPlace E'} h :
    (galoisGf σ g).atPlace u = .map (locMap σ h) (g.atPlace v) := by
  subst h
  rfl

/-- The condition `New.IsMatchingPair` for `σ` on the finite adeles of `E'`, the degree `[E' : E]`,
the idempotent of the places above `S ∪ S̄`, the ideles killed by `μ ∘ Nm`, and the base change map
`New.baseChangeGf`. -/
abbrev IsMatchingPairAbove :
    Subgroup (U (1 : Matrix n n (𝔸f E'))) → (Gf E n → ℂ) → (U (1 : Matrix n n (𝔸f E')) → ℂ) →
      Prop :=
  IsMatchingPair (adeleMap_star σ) (finrank E E') (idem (placesAbove E' S)) (kerCompNorm E' μ)
    (baseChangeGf : Gf E n → Gf E' n)

lemma continuous_baseChangeGf : Continuous (baseChangeGf : Gf E n → Gf E' n) := U.continuous_map

/-- The component of the base change of `g` at `u` is the image of the component of `g` at the
place below `u`. -/
lemma atPlace_baseChangeGf :
    (baseChangeGf g).atPlace u =
      GeneralLinearGroup.map (locMap (algebraMap E E') rfl) (g.atPlace (u.below E)) := rfl

lemma atPlace_sub_one_apply (i j : n) : ((g.atPlace w).val - 1) i j = (g.val.val - 1) i j w := by
  aesop (add simp Matrix.one_apply)

variable {σ μ S g}

/-! ### Integrality and supports -/

@[simp]
lemma star_mem_placesAbove : star u ∈ placesAbove E' S ↔ u ∈ placesAbove E' S := by
  -- `star` exchanges the two parts of `S.conjClosure`.
  simp only [placesAbove, Set.mem_preimage, below_star, Set.conjClosure, Set.mem_union, star_star]
  exact or_comm

omit [Algebra E E'] in
/-- An invertible matrix over the completion at `w` is integral with integral inverse exactly when
its image at a place `u` above `w` is, under `locMap f h` with `h : u.comap f = w` (`v.integer`: the
valuation ring of `Valued.v`). -/
lemma map_locMap_mem_intGL_iff {f : E →+* E'} (h : u.comap f = w)
    {g : GL n (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w)} :
    .map (locMap f h) g ∈ intGL n v.integer ↔ g ∈ intGL n v.integer := by
  simp [mem_intGL, ← map_inv, v.mem_integer_iff]

lemma baseChangeGf_mem_stdLevel : baseChangeGf g ∈ stdLevel E' n ↔ g ∈ stdLevel E n := by
  simp [mem_stdLevel, baseChangeGf, U.map]

lemma baseChangeGf_mem_supportedOn :
    g ∈ supportedOn n S → baseChangeGf g ∈ supportedOn n (placesAbove E' S) := by
  simp_all [atPlace_baseChangeGf, placesAbove]

/-- `g` agrees with the identity matrix after multiplication by the idempotent of `S` exactly when
its components at the places of `S` are `1`. -/
lemma idem_smul_eq_iff_mem_trivialOn : idem S • g.val.val = idem S • 1 ↔ g ∈ trivialOn n S := by
  -- Both sides say that the entries of `g` are those of the identity at every place of `S`.
  simp +contextual [Units.ext_iff, Gf.atPlace, ← ext_iff, DFunLike.ext_iff, idem_apply, apply_ite,
    ite_prop_iff_and, Matrix.one_apply]
  grind

lemma trivialOn_le_localLevel {K : (w : FinPlace E) → Subgroup (GL n (LocField w))} :
    trivialOn n S ≤ localLevel n S K := by
  aesop_cat

lemma adeleMap_idem_placesAbove :
    adeleMap σ (idem (placesAbove E' S)) = idem (placesAbove E' S) := by
  -- A place `u` and its pullback under `σ` lie above the same place of `E`.
  ext1 u
  aesop (add simp [adeleMap_apply, idem_apply, placesAbove])

lemma IsStep.isClopen_kerCompNorm (hμ : IsStep E' μ) : IsClopen (kerCompNorm E' μ).carrier :=
  OpenSubgroup.isClopen ⟨kerCompNorm E' μ, hμ.isOpen_ker.preimage_of_continuous⟩

lemma IsStep.exists_gal_ne_one (hμ : IsStep E' μ) : ∃ σ : Gal(E'/E), σ ≠ 1 := by
  -- The order of the Galois group is the degree, which is prime.
  refine Fintype.exists_ne_of_one_lt_card ?_ 1
  simpa [← card_aut_eq_finrank] using hμ.out.one_lt

lemma adeleMap_pow_finrank_eq_one [IsGalois E E'] :
    adeleMap (σ : E' →+* E') ^ finrank E E' = 1 := by
  -- `σ ^ [E' : E] = 1`, as the order of the Galois group is the degree. The `erw` matches the
  -- identity ring map with the image of `1 : Gal(E'/E)`.
  ext
  simp [adeleMap_gal_pow, ← card_aut_eq_finrank]
  erw [adeleMap_id]

end BaseChangePlaces

/-!
## Operators on fixed vectors coming from one group ring element

Bookkeeping for the trace formula. For a representation `π` of `G` and a subgroup `K`,
`New.IsOperatorOf π K T f` says that the operator `T` on the `K`-fixed vectors and the function `f`
on `G` come from one element `a` of the group ring: `T` is the action of `a`, and `f` is read from
its image `New.Variety.cosetFn K a` in `ℂ[G ⧸ K]`.
-/

section HeckeOperatorOfFunction

open Set Variety

variable {G G' W : Type*} [Group G] [Group G'] [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ G W) (K : Subgroup G) {J : Subgroup G'} {f : G → ℂ} {F : G' → ℂ}
  (T : Module.End ℂ (levelSpace π K))

/-- The left regular representation of `G` on functions `G → ℂ`: `(g • F) x = F (g⁻¹ * x)`. -/
def Variety.leftTranslation : Representation ℂ G (G → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ fun x ↦ g⁻¹ * x
  map_one' := by aesop
  map_mul' := by aesop (add simp mul_assoc)

/-- There is `a` in the group ring such that `f g` is the coefficient of `gK` in the image of `a` in
`ℂ[G ⧸ K]`, and `T` is the action of `a` on the `K`-fixed vectors. So `f` is right `K`-invariant
and nonzero on finitely many cosets, and `T` is the operator `∑ g ∈ G ⧸ K, f g • π g`. -/
def IsOperatorOf (f : G → ℂ) : Prop :=
  ∃ a : MonoidAlgebra ℂ G,
    (f = fun g : G ↦ cosetFn K a g) ∧ ∀ v : ↥(levelSpace π K), T v = π.asAlgebraHom a v

variable {π K T}

lemma indicator_subgroup_mul_left {k g : G} :
    k ∈ K → indicator K 1 (k * g) = (indicator K 1 g : ℂ) := by
  aesop (add simp [indicator, mul_mem_cancel_left])

/-- Let `a : G' →* G` and let `F` live on finitely many cosets of `J`. If `T` is the operator of
`f`, then the Hecke sum `∑ q : G' ⧸ J, F q • π (a q)` composed with `T` is the operator of the
function `φ` obtained from `f` by the same sum of left translations. The hypothesis `s` says that
the Hecke sum keeps the `K`-fixed vectors. -/
lemma IsOperatorOf.heckeFun_mul {φ : G → ℂ} {a : G' →* G}
    {s : ∀ x ∈ levelSpace π K, (heckeFun (MonoidHom.comp π a) J F) x ∈ levelSpace π K}
    (hF : HasFiniteCosets J F) (hφ : φ = heckeFun (leftTranslation.comp a) J F f)
    (hTf : IsOperatorOf π K T f) :
    IsOperatorOf π K ((heckeFun (π.comp a) J F).restrict s * T) φ := by
  obtain ⟨b, hf, hT⟩ : ∃ b : MonoidAlgebra ℂ G,
      (f = fun g : G ↦ cosetFn K b g) ∧ ∀ v : ↥(levelSpace π K), T v = π.asAlgebraHom b v := hTf
  -- The new element of the group ring is the Hecke sum `∑ q, F q • a q` times `b`.
  refine ⟨(∑ q ∈ hF.toFinset, .single (a q.out) (F q.out)) * b, ?_, fun v ↦ ?_⟩
  · simp [hφ, hf, hF, cosetFn, funext_iff, leftTranslation, heckeFun_eq_sum_toFinset]
  · simp [hT, hF, heckeFun_eq_sum_toFinset]

end HeckeOperatorOfFunction

/-!
## Local retracts and commuting families of Hecke operators

* `New.exists_isHeckeFunctionRelation`: commuting local and spherical Hecke operators on the vectors
  fixed by the level, with the functions of their products.
* `New.exists_remaining_places`: the places not above `S ∪ S̄` are cut into those above `T ∪ T̄`,
  where the level is maximal, and the rest.
-/

section BaseChangeHeckeFamily

open LinearMap Gf Set Variety

variable {E E' n W A : Type*} [Field E] [CMType E] [Field E'] [CMType E'] [Algebra E E']
  [Fintype n] [DecidableEq n] [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (Gf E n) W}
  {S T : Set (FinPlace E)} (H : ∀ w ∈ T, w ∉ S ∧ star w ∉ S) [Group A] (a : A →* Gf E n)
  (r : Gf E n →* A)

/-- The group `A` is a retract of the finite adelic unitary group at `S`: the homomorphism `a` maps
`A` into the elements supported on `S ∪ S̄`, `r ∘ a` is the identity, and the kernel of `r` consists
of the elements trivial at the places of `S`. -/
def IsLocalRetraction (S : Set (FinPlace E)) : Prop :=
  (∀ g : A, a g ∈ supportedOn n S) ∧ (∀ g : A, r (a g) = g) ∧ r.ker = trivialOn n S

section LocalOperators

variable {G M : Type*} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)

/-- The Hecke operators of `φ` and `ψ` commute on the `L`-fixed vectors. -/
def HeckeCommute (L : Subgroup G) (φ ψ : G → ℂ) : Prop :=
  ∀ x ∈ levelSpace ρ L, heckeFun ρ L φ (heckeFun ρ L ψ x) = heckeFun ρ L ψ (heckeFun ρ L φ x)

@[simp]
lemma heckeCommute_self (L : Subgroup G) (φ : G → ℂ) : HeckeCommute ρ L φ φ :=
  fun _ _ ↦ rfl

/-- On the `L`-fixed vectors, the Hecke operator of `φ` composed with that of `ψ` is the Hecke
operator of `χ`. -/
def IsHeckeProduct (L : Subgroup G) (φ ψ χ : G → ℂ) : Prop :=
  ∀ x ∈ levelSpace ρ L, heckeFun ρ L φ (heckeFun ρ L ψ x) = heckeFun ρ L χ x

end LocalOperators

section Family

variable (π) (L : Subgroup (Gf E n)) (L₀ : Subgroup A) (B C : Subgroup (Gf E n)) {J X : Type*}
  (F : J → A → ℂ) {u : X → FinPlace E} (hu : ∀ x : X, (u x).IsSplit)

/-- The local Hecke operators of the functions `F j` on `A` at level `L₀`, indexed by `j`, together
with the spherical operators at the split places `u x`, indexed by `(x, i)`:
`heckeSplit π (hu x) i`, the Hecke operator of the indicator of `basicDoubleCoset n (u x) i` at
level `localIntGL n (u x)`. -/
noncomputable abbrev heckeFamily : J ⊕ X × ℕ → Module.End ℂ W :=
  Sum.elim (fun j : J ↦ heckeFun (π.comp a) L₀ (F j)) fun x : X × ℕ ↦ heckeSplit π (hu x.1) x.2

variable (S) in
/-- Fixed by `L` means fixed by `L₀` and by the part of `L` that is trivial on `S`. `A` preserves
the vectors fixed by that part and commutes with the spherical operators. The operators of
`New.heckeFamily` preserve the `L`-fixed vectors and commute there. -/
structure IsCommutingHeckeFamily : Prop where
  /-- Fixed by `L` means fixed by `L₀` and by the part of `L` that is trivial on `S`. -/
  levelSpace_eq : levelSpace π L = levelSpace (π.comp a) L₀ ⊓ levelSpace π (trivialOn n S ⊓ L)
  /-- `A` preserves the vectors fixed by the part of `L` that is trivial on `S`. -/
  apply_mem (g : A) :
    ∀ v ∈ levelSpace π (trivialOn n S ⊓ L), π (a g) v ∈ levelSpace π (trivialOn n S ⊓ L)
  /-- `A` commutes with the spherical operators. -/
  commute_heckeSplit (g : A) (x : X) (i : ℕ) : Commute (heckeSplit π (hu x) i) (π (a g))
  /-- The operators of the family preserve the `L`-fixed vectors. -/
  heckeFamily_mem (i : J ⊕ X × ℕ) :
    ∀ v ∈ levelSpace π L, heckeFamily π a L₀ F hu i v ∈ levelSpace π L
  /-- The operators of the family commute on the `L`-fixed vectors. -/
  commute_restrict (i j : J ⊕ X × ℕ) :
    Commute ((heckeFamily π a L₀ F hu i).restrict (heckeFamily_mem i))
      ((heckeFamily π a L₀ F hu j).restrict (heckeFamily_mem j))

/-- Let `family` be operators on the `L`-fixed vectors, indexed as in `New.heckeFamily`. The
relation `R k t φ` records operators `t` of the functions `(F k ∘ r) · φ · 1_C`. It holds for the
local operator of index `k` with `φ = 1_B`. Composing `t` with the local operator of index `i`
changes `k` to `j`, if the operator of `F i` composed with that of `F k` is that of `F j`. Composing
`t` with a spherical operator at `u x` applies it to `φ`, if the elements supported at `u x` lie in
`C`. -/
structure IsHeckeFunctionRelation (family : J ⊕ X × ℕ → Module.End ℂ (levelSpace π L))
    (R : J → Module.End ℂ (levelSpace π L) → (Gf E n → ℂ) → Prop) : Prop where
  /-- The local operator of index `k` is related to the indicator of `B`. -/
  base (k : J) : R k (family (.inl k)) (indicator B 1)
  /-- A related `t` is the operator of the function `(F k ∘ r) · φ · 1_C`. -/
  isOperatorOf {k : J} {t : Module.End ℂ (levelSpace π L)} {φ : Gf E n → ℂ} (h : R k t φ) :
    IsOperatorOf π L t (F k ∘ r * (φ * indicator C 1))
  /-- Composing with the local operator of index `i` changes `k` to `j`, if the operator of `F i`
  composed with that of `F k` is that of `F j`. -/
  local_mul {k : J} {t : Module.End ℂ (levelSpace π L)} {φ : Gf E n → ℂ} (h : R k t φ) {i j : J}
    (h_prod : IsHeckeProduct (π.comp a) L₀ (F i) (F k) (F j)) : R j (family (.inl i) * t) φ
  /-- Composing with a spherical operator at `u x` applies it to `φ`, if the elements supported
  at `u x` lie in `C`. -/
  spherical_mul {k : J} {t : Module.End ℂ (levelSpace π L)} {φ : Gf E n → ℂ} (h : R k t φ)
    (x : X) (i : ℕ) (hx : supportedOn n {u x} ≤ C) :
    R k (family (.inr (x, i)) * t) (heckeSplit leftTranslation (hu x) i φ)

variable {π L₀ B C F}

/-- Let `A` be a retract at `S`, and let `L ≤ New.stdLevel` be the level given by `L₀` through `r`
and by a subgroup `N` that contains the image of `a`. Let `F j` be `L₀`-bi-invariant functions with
commuting operators, and let `u x` be split places off `S ∪ S̄` where `L` is maximal. Then
`New.IsCommutingHeckeFamily` holds. In particular, the local and the spherical operators act on the
`L`-fixed vectors and commute. -/
lemma isCommutingHeckeFamily_of_isLocalRetraction {N : Subgroup (Gf E n)}
    (h_retract : IsLocalRetraction a r S)
    (hL : L = L₀.comap r ⊓ N) (hK : L ≤ stdLevel E n) (h_local : ∀ g : A, a g ∈ N)
    (hF : ∀ j : J, IsHeckeFunction L₀ (F j))
    (h_comm : ∀ i j : J, HeckeCommute (π.comp a) L₀ (F i) (F j))
    (h_off : ∀ x : X, u x ∉ S.conjClosure) (h_max : ∀ x : X, maxCompactAt n (u x) ≤ L) :
    IsCommutingHeckeFamily π S a L L₀ F hu := by
  obtain ⟨h_on, h_retr, h_ker⟩ : (∀ g : A, a g ∈ supportedOn n S) ∧ (∀ g : A, r (a g) = g) ∧
      r.ker = trivialOn n S := h_retract
  let ρ : Representation ℂ A W := π.comp a
  let V : Submodule ℂ W := levelSpace π (trivialOn n S ⊓ L)
  have h_mem (g : A) (hg : g ∈ L₀) : a g ∈ L := by
    have hg_comap : a g ∈ L₀.comap r := by simpa [h_retr] using hg
    exact hL.ge ⟨hg_comap, h_local g⟩
  -- An element `k` of `L` is `k * (a (r k))⁻¹`, which is trivial on `S`, times `a (r k)`.
  have h_fixed : levelSpace π L = levelSpace ρ L₀ ⊓ V := by
    apply le_antisymm
    · intro v hv
      have hv_local : v ∈ levelSpace ρ L₀ :=
        mem_levelSpace.2 fun g ↦ mem_levelSpace.1 hv ⟨a g, h_mem g g.prop⟩
      exact ⟨hv_local, levelSpace_anti inf_le_right hv⟩
    rintro v ⟨hv_local, hv_off⟩ ⟨k, hk⟩
    obtain ⟨hk_local, -⟩ : r k ∈ L₀ ∧ k ∈ N := Subgroup.mem_inf.1 (hL.le hk)
    have hk_ker : k * (a (r k))⁻¹ ∈ r.ker := by simp [h_retr]
    have hk_L : k * (a (r k))⁻¹ ∈ L := L.mul_mem hk (L.inv_mem (h_mem (r k) hk_local))
    have hk_off : k * (a (r k))⁻¹ ∈ trivialOn n S ⊓ L := ⟨h_ker.le hk_ker, hk_L⟩
    have h_fix_local : π (a (r k)) v = v := by
      simpa [ρ] using mem_levelSpace.1 hv_local ⟨r k, hk_local⟩
    calc π k v = π (k * (a (r k))⁻¹) (π (a (r k)) v) := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
      _ = π (k * (a (r k))⁻¹) v := by rw [h_fix_local]
      _ = (1 : ℂ) • v := mem_levelSpace.1 hv_off ⟨k * (a (r k))⁻¹, hk_off⟩
  have h_le_local : levelSpace π L ≤ levelSpace ρ L₀ := h_fixed.le.trans inf_le_left
  -- The image of `a` is supported on `S ∪ S̄`, so it commutes with the elements trivial on `S`.
  have h_apply_mem (g : A) : ∀ v ∈ V, π (a g) v ∈ V := by
    intro v hv
    refine map_mem_levelSpace_of_commute hv fun k ↦ ?_
    obtain ⟨hk_triv, -⟩ : (k : Gf E n) ∈ trivialOn n S ∧ (k : Gf E n) ∈ L := k.prop
    exact (commute_supportedOn_trivialOn (h_on g) hk_triv).symm.map π
  -- It is trivial at the places `u x`, so it commutes with the spherical operators there.
  have h_sph (g : A) (x : X) (i : ℕ) : Commute (heckeSplit π (hu x) i) (π (a g)) := by
    have hx_not_S : u x ∉ S := fun hxS ↦ h_off x (.inl hxS)
    have hx_star_not_S : star (u x) ∉ S := fun hxS ↦ h_off x (.inr hxS)
    have h_trivial : a g ∈ trivialOn n {u x} := by
      refine mem_trivialOn.2 ?_
      rintro w rfl
      exact mem_supportedOn.1 (h_on g) (u x) hx_not_S hx_star_not_S
    refine LinearMap.ext fun v ↦ ?_
    exact (heckeSplit_comm_of_trivialOn (hu x) i h_trivial).symm
  have h_stable : ∀ i : J ⊕ X × ℕ,
      ∀ v ∈ levelSpace π L, heckeFamily π a L₀ F hu i v ∈ levelSpace π L := by
    rintro (j | ⟨x, i⟩) v hv
    · -- the local operator is a finite sum of multiples of `π (a g)`, which preserve `V`
      rw [h_fixed] at hv ⊢
      obtain ⟨hv_local, hv_off⟩ : v ∈ levelSpace ρ L₀ ∧ v ∈ V := Submodule.mem_inf.1 hv
      refine Submodule.mem_inf.2 ⟨(hF j).heckeFun_mem hv_local, ?_⟩
      simp [hF, sum_mem, V.smul_mem, fun g : A ↦ h_apply_mem g v hv_off, heckeFun_eq_sum_toFinset]
    · exact heckeSplit_mem_levelSpace (hu x) i (levelSpace_anti (h_max x) hv) hK hv
  have h_mixed (j : J) (x : X) (i : ℕ) (v : W) :
      heckeSplit π (hu x) i (heckeFun ρ L₀ (F j) v) =
        heckeFun ρ L₀ (F j) (heckeSplit π (hu x) i v) := by
    obtain ⟨h_finite, -⟩ : HasFiniteCosets L₀ (F j) ∧ _ := hF j
    refine map_heckeFun (heckeSplit π (hu x) i) h_finite fun g ↦ ?_
    exact LinearMap.congr_fun (h_sph g x i).eq v
  refine ⟨h_fixed, h_apply_mem, h_sph, h_stable, ?_⟩
  rintro (i | ⟨x, m⟩) (j | ⟨y, m'⟩)
  · ext ⟨v, hv⟩
    exact h_comm i j v (h_le_local hv)
  · ext ⟨v, hv⟩
    exact (h_mixed i y m' v).symm
  · ext ⟨v, hv⟩
    exact h_mixed j x m v
  · ext ⟨v, hv⟩
    exact heckeSplit_comm (hu x) (hu y) m m'
      (levelSpace_anti (h_max x) hv) (levelSpace_anti (h_max y) hv)

/-- Let `A` be a retract at `S`, and let `L ≤ New.stdLevel` be `L₀.comap r ⊓ (B ⊓ C)`, where `a`
maps `A` into `B ⊓ C`. Let `F j` be `L₀`-bi-invariant functions with commuting operators, and let
`u x` be split places off `S ∪ S̄` where `L` is maximal. Then `New.IsCommutingHeckeFamily` holds, so
the local and the spherical operators act on the `L`-fixed vectors and commute. Also, some `R`
satisfies `New.IsHeckeFunctionRelation` for the restricted operators. That is, `R k t φ` records
operators `t` of the functions `(F k ∘ r) · φ · 1_C`, holds for the local operator of index `k` with
`φ = 1_B`, and is carried along by composing with local and spherical operators. -/
lemma exists_isHeckeFunctionRelation (h_retract : IsLocalRetraction a r S)
    (hL : L = L₀.comap r ⊓ (B ⊓ C)) (hK : L ≤ stdLevel E n) (h_local : ∀ g : A, a g ∈ B ⊓ C)
    (hF : ∀ j : J, IsHeckeFunction L₀ (F j))
    (h_comm : ∀ i j : J, HeckeCommute (π.comp a) L₀ (F i) (F j))
    (h_off : ∀ x : X, u x ∉ S.conjClosure) (h_max : ∀ x : X, maxCompactAt n (u x) ≤ L) :
    ∃ h : IsCommutingHeckeFamily π S a L L₀ F hu,
      ∃ R : J → Module.End ℂ (levelSpace π L) → (Gf E n → ℂ) → Prop,
        IsHeckeFunctionRelation π a r L L₀ B C F hu
          (fun i : J ⊕ X × ℕ ↦ (heckeFamily π a L₀ F hu i).restrict (h.heckeFamily_mem i)) R := by
  classical
  have h_family : IsCommutingHeckeFamily π S a L L₀ F hu :=
    isCommutingHeckeFamily_of_isLocalRetraction a r L hu h_retract hL hK h_local hF h_comm h_off
      h_max
  obtain ⟨-, h_retr, h_ker⟩ : (∀ g : A, a g ∈ supportedOn n S) ∧ (∀ g : A, r (a g) = g) ∧
      r.ker = trivialOn n S := h_retract
  let family (i : J ⊕ X × ℕ) : Module.End ℂ (levelSpace π L) :=
    (heckeFamily π a L₀ F hu i).restrict (h_family.heckeFamily_mem i)
  have h_commute (i j : J ⊕ X × ℕ) : Commute (family i) (family j) :=
    h_family.commute_restrict i j
  -- `R k t φ`: `t` is the local operator of index `k` times some `s`, and for all `i` the local
  -- operator of index `i` times `s` is that of the function `(F i ∘ r) · φ · 1_C`.
  let R (k : J) (t : Module.End ℂ (levelSpace π L)) (φ : Gf E n → ℂ) : Prop :=
    ∃ s : Module.End ℂ (levelSpace π L), t = family (.inl k) * s ∧
      ∀ i : J, IsOperatorOf π L (family (.inl i) * s) (F i ∘ r * (φ * indicator C 1))
  refine ⟨h_family, R, fun k ↦ ⟨1, rfl, fun i ↦ ?_⟩, ?_, ?_, ?_⟩
  · -- The identity is the operator of the indicator of `L`; apply the local operator of index `i`
    -- to that function.
    have h_one : IsOperatorOf π L 1 fun g : Gf E n ↦ cosetFn L 1 g := by
      refine ⟨1, rfl, fun v ↦ ?_⟩
      simp
    obtain ⟨h_finite, -⟩ : HasFiniteCosets L₀ (F i) ∧ _ := hF i
    refine .heckeFun_mul h_finite ?_ h_one
    -- The chosen representative of the coset of `g` is `g * c g`, with `c g ∈ L₀`.
    have h_out : ∀ g : A, ∃ h : L₀, (g : A ⧸ L₀).out = g * h := QuotientGroup.mk_out_eq_mul L₀
    choose c hc using h_out
    simp only [Subgroup.mem_inf, forall_and] at h_local
    subst hL
    simp [cosetFn, Finsupp.single_apply, QuotientGroup.eq, hF, hc, h_retr, h_local, indicator,
      mul_mem_cancel_left, ← QuotientGroup.eq (s := L₀), ite_and, leftTranslation,
        heckeFun_eq_sum_toFinset,
      funext_iff]
    -- What is left: both sides are `F i (r x)` on `B ∩ C` and `0` off it, as nested `if`s
    lia
  · rintro k t φ ⟨s, rfl, hs⟩
    exact hs k
  · rintro k t φ ⟨s, rfl, hs⟩ i j h_prod
    refine ⟨s, LinearMap.ext fun v ↦ Subtype.ext ?_, hs⟩
    have h_sv_local : (s v : W) ∈ levelSpace (π.comp a) L₀ :=
      (h_family.levelSpace_eq.le.trans inf_le_left) (s v).prop
    exact h_prod (s v) h_sv_local
  · rintro k t φ ⟨s, rfl, hs⟩ x m hx
    refine ⟨family (.inr (x, m)) * s, (h_commute _ _).left_comm s, fun i ↦ ?_⟩
    -- The factors `F i ∘ r` and `indicator C 1` are invariant under the group at `u x`, so
    -- multiplication by them commutes with the spherical operator.
    rw [(h_commute _ _).left_comm]
    obtain ⟨h_finite, -⟩ : HasFiniteCosets (localIntGL n (u x))
        ((basicDoubleCoset n (u x) m).indicator (1 : GL n (LocField (u x)) → ℂ)) ∧ _ :=
      isHeckeFunction_basicDoubleCoset m
    refine (hs i).heckeFun_mul h_finite (map_heckeSplit (hu x) m
      (mulLeft ℂ (F i ∘ r) * mulRight ℂ (indicator C 1)) fun g hg ↦ ?_)
    have h_subset : {u x} ⊆ S.conjClosureᶜ := singleton_subset_iff.2 (h_off x)
    have h_trivial : r g = 1 := h_ker.ge (supportedOn_compl.le (supportedOn_mono h_subset hg))
    simp [indicator_subgroup_mul_left, hx hg, h_trivial, leftTranslation, funext_iff]

end Family

/-- Let `u` be the only place of `E'` above `w`, both split. Then (a) `GL_n(E_w)` is a retract at
`{w}` (`New.IsLocalRetraction`), (b) `GL_n(E'_u)` is a retract at the places above `w` and its
conjugate, and (c) an element is integral at these places iff its component at `u` is integral. -/
lemma isLocalRetraction_ofSplitPlace (n : Type*) [Fintype n] [DecidableEq n] {w : FinPlace E}
    {u : FinPlace E'} (h_unique : ∀ v : FinPlace E', v.below E = w ↔ v = u) (hu : u.IsSplit)
    (hw : w.IsSplit) :
    -- (a), (b) the component at `w`, and at `u`, is a retraction of the local embedding
    IsLocalRetraction (n := n) (ofSplitPlace hw) (atPlace w) {w} ∧
    IsLocalRetraction (n := n) (ofSplitPlace hu) (atPlace u) (placesAbove E' {w}) ∧
    -- (c) integral above `w` and its conjugate means integral at `u`
    localLevel n (placesAbove E' {w}) = (intGL n Valued.v.integer).comap (atPlace u) := by
  -- As `u` is the only place above `w`, the set `placesAbove E' {w}` is `{u, star u}`, and the
  -- component of a unitary element at `star u` is determined by that at `u`.
  refine ⟨?_, ?_, ?_⟩
  · -- (a) `atPlace w` is a retraction of the embedding at `w`
    simp_all [IsLocalRetraction, SetLike.ext_iff]
  · -- (b) the places above `w` and `w̄` are `u` and `ū`
    simp_all [IsLocalRetraction, ← below_star, star_eq_iff_star_eq, atPlace_star_eq_one_iff,
      atPlace_ofSplitPlace_of_ne, SetLike.ext_iff, placesAbove]
  · -- (c) the component at `ū` is integral exactly when that at `u` is
    simp_all [← below_star, star_eq_iff_star_eq, SetLike.ext_iff, placesAbove, localLevel]
    -- what is left: `localIntGL n u` is `GL_n` of the valuation integers at `u`
    show ∀ x : Gf E' n, atPlace u x ∈ localIntGL n u ↔ atPlace u x ∈ intGL n Valued.v.integer
    exact fun x ↦ Iff.rfl

/-- If no place of `T` lies in `S` or in its conjugate, the elements supported on `S ∪ S̄` are
trivial at the places of `T`. -/
lemma Gf.supportedOn_le_trivialOn (H : ∀ w ∈ T, w ∉ S ∧ star w ∉ S) :
    supportedOn n S ≤ trivialOn n T :=
  biInf_mono H

/-- Let `T` avoid `S ∪ S̄`, and let the level `K` be maximal at the places above `T ∪ T̄`. Then
there is a set `Y` of places of `E` with these properties. (a) The places of `E'` above `T ∪ T̄`
and those above `Y ∪ Ȳ` are disjoint. (b) Elements supported above `T ∪ T̄` lie in the
level `K` above `Y`. (c), (d) Together the places above `T` and above `Y` are the places not above
`S ∪ S̄`, as sets and as idempotents. (e) The level `K` off `S` is the maximal level above `T`
intersected with `K` above `Y`. -/
lemma exists_remaining_places (H : ∀ w ∈ T, w ∉ S ∧ star w ∉ S)
    {K : (w : FinPlace E') → Subgroup (GL n (LocField w))}
    (h_max : ∀ x : T, ∀ u ∈ placesAbove E' {x.val}, K u = localIntGL n u) :
    ∃ Y : Set (FinPlace E),
      -- (a)
      idem (placesAbove E' T) * idem (placesAbove E' Y) = 0 ∧
      -- (b)
      supportedOn n (placesAbove E' T) ≤ localLevel n (placesAbove E' Y) K ∧
      -- (c), (d) together they are the places not above `S`, as sets and as idempotents
      placesAbove E' (T ∪ Y) = (placesAbove E' S)ᶜ ∧
      idem (placesAbove E' T) + idem (placesAbove E' Y) = 1 - idem (placesAbove E' S) ∧
      -- (e)
      localLevel n (placesAbove E' S)ᶜ K =
        localLevel n (placesAbove E' T) ⊓ localLevel n (placesAbove E' Y) K := by
  classical
  -- `Y` is the set of places outside `S`, `T` and their conjugates, so the places not above `S`
  -- are the disjoint union of those above `T` and those above `Y`.
  let Y : Set (FinPlace E) := (S ∪ T).conjClosureᶜ
  have h_mem_Y (u : FinPlace E') :
      u ∈ placesAbove E' Y ↔ u ∉ placesAbove E' S ∧ u ∉ placesAbove E' T := by
    simp only [placesAbove, Y, mem_preimage, mem_union, mem_compl_iff, star_star]
    tauto
  have h_notMem_S (u : FinPlace E') (hu : u ∈ placesAbove E' T) : u ∉ placesAbove E' S := by
    rcases hu with hu | hu
    · obtain ⟨h_not_S, h_star_not_S⟩ : u.below E ∉ S ∧ star (u.below E) ∉ S := H _ hu
      exact not_or.2 ⟨h_not_S, h_star_not_S⟩
    · obtain ⟨h_star_not_S, h_not_S⟩ :
          star (u.below E) ∉ S ∧ star (star (u.below E)) ∉ S := H _ hu
      rw [star_star] at h_not_S
      exact not_or.2 ⟨h_not_S, h_star_not_S⟩
  have h_compl : (placesAbove E' S)ᶜ = placesAbove E' T ∪ placesAbove E' Y := by
    ext u
    rw [mem_compl_iff, mem_union, h_mem_Y]
    constructor
    · intro hS
      by_cases hT : u ∈ placesAbove E' T
      · exact .inl hT
      · exact .inr ⟨hS, hT⟩
    · rintro (hT | ⟨hS, -⟩)
      · exact h_notMem_S u hT
      · exact hS
  refine ⟨Y, ?_, ?_, ?_, ?_, ?_⟩
  · refine DFunLike.ext _ _ fun u ↦ ?_
    by_cases hu : u ∈ placesAbove E' T
    · simp [h_mem_Y, hu]
    · simp [hu]
  · intro g hg u hu
    obtain ⟨-, hu_T⟩ : u ∉ placesAbove E' S ∧ u ∉ placesAbove E' T := (h_mem_Y u).1 hu
    have hu_star : star u ∉ placesAbove E' T := by
      simpa [below_star, and_comm] using hu_T
    rw [mem_supportedOn.1 hg u hu_T hu_star]
    exact one_mem _
  · rw [h_compl]
    ext u
    simp only [placesAbove, mem_preimage, mem_union]
    tauto
  · rw [← idem_compl, h_compl]
    refine DFunLike.ext _ _ fun u ↦ ?_
    by_cases hu : u ∈ placesAbove E' T
    · simp [h_mem_Y, hu]
    · simp [idem_apply, hu]
  · have h_level : localLevel n (placesAbove E' T) K = localLevel n (placesAbove E' T) := by
      have hK (u : FinPlace E') (hu : u ∈ placesAbove E' T) : K u = localIntGL n u := by
        rcases hu with hu | hu
        · exact h_max ⟨u.below E, hu⟩ u (.inl rfl)
        · exact h_max ⟨star (u.below E), hu⟩ u (.inr rfl)
      ext g
      refine forall₂_congr fun u hu ↦ ?_
      rw [hK u hu]
    rw [← h_level, h_compl]
    ext g
    simp only [Subgroup.mem_inf, mem_localLevel, mem_union, or_imp, forall_and]

end BaseChangeHeckeFamily

end New
