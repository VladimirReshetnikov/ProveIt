import Lib.Adelic.Adeles.IdeleModulus
import Lib.ClassField.LocalDuality.DualityInequality
import Lib.ClassField.Places.TameInertia

/-!
# Local and global Artin maps, algebraic Hecke characters and tame inertia

The file defines the local Artin map `New.artinAt` with values in `Γ^ab`, the global Artin map
`New.artinMap` of a number field `K`, and algebraic Hecke characters. In the parts on number fields,
`Γ` is the Galois group (`IsProGalois Γ K Ω`) of an algebraically closed field `Ω` over `K`; `Ω` has
no binder here (it is fixed elsewhere), and `New.ClosurePlace` is the type of valuation subrings of
`Ω`. For a local field, the file shows that the local Artin map sends uniformisers to inverse
Frobenii. At a place of a number field, it proves the main properties of the local Artin map
`New.localArtin`: the defining formula, compatibility with norms, its image, its relation to
`New.artinAt`, and tame inertia.

## Main definitions and results

* `New.artinAt`: the local Artin map at `v`, with values in the topological abelianisation of `Γ`.
* `New.artinMap`: the global Artin map from the finite ideles of `K` to the abelianised Galois
  group. It is chosen (`Classical.epsilon`) so that each character of `Γ` takes on it the product of
  its values on the local Artin maps. This file does not prove that such a map exists;
  `New.abelianLift_artinMap_eq_finprod_of_exists` gives the product formula when one does.
* `New.algHeckeChars`, `New.AlgHeckeChar`: algebraic Hecke characters, as characters of the finite
  ideles (`New.AlgHeckeChar.character`) together with their infinity type
  (`New.AlgHeckeChar.infinityType`).
* `New.IsPlaceOver.isLocalArtin_localArtin`: the formula holds; the local theory in `ℚ̄_p` then
  applies.
* `New.IsTameGenerator`, `New.IsPlaceOver.exists_eq_pow_and_apply_conj_eq_pow`: tame generators of
  inertia, and the values on inertia of a homomorphism of exponent prime to `w`.
* `New.IsPlaceOver.tameGenerator`, `New.IsPlaceOver.tame_inertia`,
  `New.IsPlaceOver.exists_isTameUnit`: a chosen tame generator, and a unit of `K_w`
  whose symbol it is and whose residue generates the units of the residue field.

Notions from other files:
* `New.localArtin Γ A w`: a chosen homomorphism from `K_w^×` to the topological abelianisation of
  the decomposition group of `A`, pinned down on `K^×` by `New.IsLocalArtin`.
* `New.IsCompletionEmb w p Γ A j`: embeddings of `K_w` and of `Ω` (by `j`) in `ℚ̄_p` that induce `A`
  and make the decomposition group of `A` the Galois group of `ℚ̄_p` over `K_w`.
* `New.IsLocalArtin`: The homomorphism `f : Lˣ → Γ^ab` satisfies `New.Cohomology.classOfInvariant (χ
  (f x)) = −(δχ ∪ x)` for all continuous characters `χ` and all `x` in `Lˣ`.
* `New.IsFrob`: `σ` stabilises the valuation subring `A` and `σ • x ≡ x ^ q` modulo the maximal
  ideal for all `x ∈ A`.
* `New.IsPlaceOver`: The valuation subring `A` of `Ω` lies over the prime `w` of `K`: an integer of
  `K` is in the maximal ideal of `A` exactly when it lies in `w`.
* `New.QZChar.abelianLift`: The homomorphism induced by the continuous character χ on the
  topological abelianisation of Γ, with values in ℚ/ℤ written multiplicatively.

## Relation to the literature

Known result: Local class field theory, with Brauer invariant, Artin map, norms and tame symbol. It
is proved for henselian fields such as fixed fields of decomposition groups, with the norm index in
prime degree coming from Tate's lemma on the Herbrand quotient. Source: J.-P. Serre, Local Fields
(1979), XII–XIV; J. S. Milne, Class Field Theory (v4.03), I and III 2.

See also `Lib.ClassField.Avatar.LocalGlobalCompatibility` and `Lib.ClassField.Places.LocalFields`.
-/

noncomputable section

/-!
## The global Artin map and algebraic Hecke characters

* `New.star_locIdele`: complex conjugation of a CM field carries an idele with one component at `v`
  to the idele with the conjugate component at the conjugate place.
-/

namespace New

/-- The complex conjugate of the idele with component `x` at `v` and `1` elsewhere is the idele
with the conjugate of `x` at the conjugate place `star v` and `1` elsewhere. -/
lemma star_locIdele {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E] {v : FinPlace E}
    (x : (LocField v)ˣ) :
    star (locIdele v x) = locIdele (star v) (x.map (conjLoc rfl).toMonoidHom) :=
  Units.ext (by simp [locIdele, star_singleAdele])

variable (Γ K : Type) [Group Γ] [TopologicalSpace Γ] [Field K] [NumberField K]

/-- The group of algebraic Hecke characters: pairs `(θ, n)` of a character `θ` of the finite
ideles with open kernel and an infinity type `n`, an integer for each embedding `σ : K → ℂ`,
such that `θ x = ∏ σ, σ x ^ (-n σ)` for all `x` in `Kˣ`. The condition is asked of all `x`, not
only of the totally positive ones, so this is the usual notion when `K` is totally complex. -/
def algHeckeChars : Subgroup (((𝔸f K)ˣ →* ℂˣ) × Multiplicative ((K →+* ℂ) → ℤ)) :=
  Subgroup.ofDiv
    {θ : ((𝔸f K)ˣ →* ℂˣ) × Multiplicative ((K →+* ℂ) → ℤ) |
      IsOpen (SetLike.coe θ.1.ker) ∧
      ∀ x : Kˣ, θ.1 (principalIdele x) = ∏ σ : K →+* ℂ, σ x ^ (-θ.2.toAdd σ)}
    ⟨1, by simp⟩ fun θ hθ η hη ↦ by
      constructor
      · -- The kernel of the quotient contains the open subgroup `θ.1.ker ⊓ η.1.ker`.
        exact Subgroup.isOpen_mono (H₁ := θ.1.ker ⊓ η.1.ker) (by aesop_cat) (hθ.1.inter hη.1)
      · simp_all [zpow_add₀, field, Finset.prod_mul_distrib]

/-- The type of algebraic Hecke characters of K: pairs (θ, n) of a character of the finite
ideles and its infinity type, as in `New.algHeckeChars`. -/
abbrev AlgHeckeChar : Type := ↥(algHeckeChars K)

/-- The character of the finite ideles of an algebraic Hecke character `θ = (χ, n)`: the map `χ`. -/
abbrev AlgHeckeChar.character {K : Type} [Field K] [NumberField K] (θ : AlgHeckeChar K) :
    (𝔸f K)ˣ →* ℂˣ :=
  θ.val.1

/-- The infinity type of an algebraic Hecke character `θ = (χ, n)`: the integer `n σ` for each
embedding `σ : K → ℂ`, with `χ x = ∏ σ, σ x ^ (-n σ)` for `x` in `Kˣ`. -/
abbrev AlgHeckeChar.infinityType {K : Type} [Field K] [NumberField K] (θ : AlgHeckeChar K) :
    (K →+* ℂ) → ℤ :=
  θ.val.2.toAdd

variable {K} [Algebra K Ω] [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω]

/-- The local Artin map `K_v^× → Γ^ab` at the finite place `v` of `K`: the local Artin map
`New.localArtin` to the abelianised decomposition group of `New.placeOver v`, the chosen place of
`Ω` above `v`, followed by the map that the inclusion of that group in `Γ` induces. -/
def artinAt (v : FinPlace K) :
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)ˣ →*
      Γ ⧸ (commutator Γ).topologicalClosure :=
  -- The inclusion of the decomposition group maps the closure of its commutator subgroup into
  -- that of `Γ`, so it passes to the abelianisations.
  (QuotientGroup.map _ (commutator Γ).topologicalClosure (decompGroup Γ (placeOver v)).subtype
      (Set.MapsTo.closure (fun g hg ↦
        map_derivedSeries_le_derivedSeries (decompGroup Γ (placeOver v)).subtype 1 ⟨g, hg, rfl⟩)
        (by fun_prop))).comp (localArtin Γ (placeOver v) v)

/-- The global Artin map from the finite ideles to the topological abelianisation of `Γ`: a
homomorphism `f`, chosen by `Classical.epsilon`, such that for every continuous character `χ` of `Γ`
the value of `χ` at `f a` is the product over the finite places `v` of its values at the local Artin
symbols of the components of `a`. This file does not prove that such an `f` exists; when one
does, `New.abelianLift_artinMap_eq_finprod_of_exists` gives that formula for `New.artinMap`. -/
def artinMap : (𝔸f K)ˣ →* TopologicalAbelianization Γ :=
  Classical.epsilon fun f : (𝔸f K)ˣ →* TopologicalAbelianization Γ ↦
    ∀ (χ : ↥(QZChar Γ)) (a : (𝔸f K)ˣ),
      QZChar.abelianLift χ (f a) =
        ∏ᶠ v : FinPlace K, QZChar.abelianLift χ (artinAt Γ v (ideleAt v a))

/-- If some homomorphism from the finite ideles of `K` to the topological abelianisation of `Γ`
takes, on every character `χ` of `Γ`, the product over the finite places `v` of the values of `χ`
at the local Artin symbols (`New.artinAt`), then `New.artinMap` is such a homomorphism. -/
theorem abelianLift_artinMap_eq_finprod_of_exists
    (h_exists : ∃ f : (𝔸f K)ˣ →* TopologicalAbelianization Γ,
      ∀ (χ : ↥(QZChar Γ)) (a : (𝔸f K)ˣ),
        QZChar.abelianLift χ (f a) =
          ∏ᶠ v : FinPlace K, QZChar.abelianLift χ (artinAt Γ v (ideleAt v a)))
    (χ : ↥(QZChar Γ)) (a : (𝔸f K)ˣ) :
    QZChar.abelianLift χ (artinMap Γ a) =
      ∏ᶠ v : FinPlace K, QZChar.abelianLift χ (artinAt Γ v (ideleAt v a)) :=
  Classical.epsilon_spec h_exists χ a

end New

/-!
## The local Artin map on uniformisers

One property of a homomorphism `F` with `New.IsLocalArtin Γ k A F`, the local Artin map of a local
field `k` with absolute Galois group `Γ` (`New.IsLocalGalois`).
-/

section LocalArtinMap

open QuotientGroup

/-- Let `F` be a local Artin map of the local field `k` (`New.IsLocalArtin`) and `π` a uniformiser
of `k`. Then `F π` is the class of `φ⁻¹` for some arithmetic Frobenius `φ` (`New.IsFrob` for
the order of the residue field of `k`). -/
lemma New.IsLocalArtin.exists_frob_of_isUniformiser {Γ k Ω : Type} [Group Γ] [TopologicalSpace Γ]
    [Field k] [Field Ω] [Algebra k Ω] [MulSemiringAction Γ Ω] {A : ValuationSubring Ω}
    [L : IsLocalGalois Γ k A] {π : kˣ} {F : kˣ →* TopologicalAbelianization Γ}
    (hF : IsLocalArtin Γ k A F) (h : IsUniformiser A π.val) :
    ∃ φ : Γ, IsFrob A (residueCard k A) φ ∧ F π = φ⁻¹ := by
  obtain ⟨⟨φ, hφ⟩, -, -⟩ := L.frobenius_spec
  obtain ⟨h_inj, h_unram⟩ := L.isClassOfInvariant_classOfInvariant
  -- An unramified character takes the same value at `φ⁻¹` and at `F π`, so `φ⁻¹ / F π` lies in the
  -- closed image of inertia (characters separate a closed subgroup from a point outside it).
  obtain ⟨τ, hτ, h_eq⟩ :
      ↑φ⁻¹ / F π ∈ (inertiaGroup Γ A).map (mk' (commutator Γ).topologicalClosure) := by
    refine QZChar.mem_of_forall_abelianLift (continuous_mk.isClosedMap _ isClosed_inertiaGroup) _
      fun χ hχ ↦ Multiplicative.ext (h_inj ?_)
    -- `χ` kills inertia, so by `h_unram` the cyclic class of `χ` and `π` is
    -- `classOfInvariant (χ φ)`, as `π` has order one; by `hF` it is also minus
    -- `classOfInvariant (χ (F π))`, and the two cancel.
    simp_all [IsLocalArtin, h.ordRat_eq_one, h_unram _ _ _ hφ _ 1]
  -- Correct `φ` by the element `τ` of inertia: `h_eq` says that the class of `τ` is `φ⁻¹ / F π`.
  refine ⟨φ * τ, by simpa using hφ.mul_iff.mpr hτ, ?_⟩
  calc F π = ↑φ⁻¹ / mk' (commutator Γ).topologicalClosure τ := by rw [h_eq, div_div_cancel]
    _ = ↑(φ * τ)⁻¹ := by simp [div_eq_mul_inv, mul_comm]

end LocalArtinMap

/-!
## The local Artin map at a place of a number field

Let `A` be a valuation subring of an algebraically closed `Ω` over the prime `w` of a number field
`K`, with decomposition group `D`. The map `New.localArtin` goes from `K_w^×` to `D^ab` and is
pinned down by `New.IsLocalArtin`: writing `Art` for `New.localArtin Γ A w`,
`χ (Art x) = -inv (χ, x)`, where `inv` is the local invariant (`New.Cohomology.classOfInvariant`
read backwards); so uniformisers go to inverse Frobenii.

`Γ` is the Galois group of `Ω / K`, and `(χ, x)` is the class `cyclicClass _ χ x` in `H²(D, Ω^×)`.
Valuations are multiplicative: `Valued.v x = exp (-n)` says that `x` has order `n` at `w`.
`New.FinPlace.q w`, written `w.q` or `q`, is the number of elements of the residue field.
-/

namespace New

open Filter WithZero Units Module LinearMap Subgroup Cohomology DFunLike QZChar
  IsProGalois Valued
open scoped Classical

variable {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [NumberField K] {w : FinPlace K}

/-! ### Continuity of homomorphisms on `K_w^×` -/

/-- For a finite place `w` of a number field `K` and `n ≠ 0`, every subgroup `T` of `K_w^×` that
contains all `n`-th powers is open. -/
lemma isOpen_of_forall_pow_mem {n : ℕ} (hn : n ≠ 0) {T : Subgroup (LocField w)ˣ}
    (h_pow : ∀ y : (LocField w)ˣ, y ^ n ∈ T) :
    T.IsOpen := by
  -- The map `y ↦ y ^ n` has derivative `n ≠ 0` at `1`, so its range is a neighbourhood of `1`.
  let : NontriviallyNormedField (LocField w) := toNontriviallyNormedField (LocField w) _
  have range_mem : Set.range (fun y : LocField w ↦ y ^ n) ∈ nhds (1 ^ n) :=
    ((hasStrictDerivAt_pow n 1).map_nhds_eq (by simpa using hn)).ge range_mem_map
  -- An `n`-th root `y` of a unit `x` is itself a unit.
  refine T.isOpen_of_mem_nhds <| mem_of_superset (continuous_val.tendsto (1 ^ n) range_mem) ?_
  rintro x ⟨y, hy⟩
  have root : x.ofPow y hn hy ^ n = x := ext hy
  simpa [root] using h_pow (x.ofPow y hn hy)

/-- Every homomorphism from `K_w^×` to the topological abelianisation of a profinite group `Γ`
(compact, totally disconnected) is continuous. -/
lemma continuous_hom_locField_units [IsTopologicalGroup Γ] [CompactSpace Γ]
    [TotallyDisconnectedSpace Γ] (f : (LocField w)ˣ →* TopologicalAbelianization Γ) :
    Continuous f := by
  -- For a character `χ`, `ker (abelianLift χ)` is open, so it has finite index `n` and contains all
  -- `n`-th powers. Hence so does the kernel of `abelianLift χ ∘ f`, which is therefore open.
  refine continuous_iff_forall_isOpen_ker_comp.mpr fun χ ↦ ?_
  have ker_open : IsOpen (SetLike.coe (abelianLift χ).ker) :=
    (continuous_abelianLift χ).isOpen_preimage {1} ⟨⟩
  refine isOpen_of_forall_pow_mem (quotient_finite_of_isOpen _ ker_open).card_pos.ne' fun y ↦ ?_
  simpa [Subgroup.index_eq_card] using (abelianLift χ).ker.pow_index_mem (f y)

section

variable [Algebra K Ω] [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω]
  {A : ClosurePlace} (h : IsPlaceOver A w)

/-- The union of all inertia groups in the Galois group of Ω over K at places of Ω above the
places in S. -/
def inertiaAbove (S : Set (FinPlace K)) : Set Gal(Ω/K) :=
  {g : Gal(Ω/K) | ∃ v ∈ S, ∃ A : ClosurePlace, IsPlaceOver A v ∧ g ∈ inertiaGroup Gal(Ω/K) A}

namespace IsPlaceOver

include h
/-! ### The defining formula and norms -/

/-- Let `A` lie over the finite place `w` of `K`, and let `emb` embed `K_w` continuously in `ℚ̄_p`
and give an equivariant `K`-embedding `j : Ω → ℚ̄_p` inducing `A` (`New.IsCompletionEmb`); write `D`
for the decomposition group of `A`. Suppose `f : K_wˣ → D^ab` is a local Artin map for `K_w`,
meaning `IsLocalArtin` holds with invariants taken relative to the valuation ring of `ℚ̄_p`:
`classOfInvariant (χ (f x)) = -cyclicClass χ x` for every continuous character `χ : D → ℚ/ℤ`. Then
the restriction of `f` to `Kˣ` satisfies the same identity for the fixed field of `D`, with
invariants taken relative to `A`, because `j` keeps a uniformiser and the order of the residue field
and so preserves invariants. -/
lemma isLocalArtin_comp_unitsMap {p : ℕ} [Fact p.Prime] [Algebra (LocField w) (PadicAlgCl p)]
    {j : Ω →+* PadicAlgCl p} (emb : IsCompletionEmb w p Γ A j)
    {f : (LocField w)ˣ →* TopologicalAbelianization (decompGroup Γ A)}
    (hf : IsLocalArtin (decompGroup Γ A) (LocField w) (intQpBar p) f) :
    IsLocalArtin (decompGroup Γ A) (fixedFieldOf (decompGroup Γ A)) A
      (f.comp (Units.map (algebraMap K (LocField w)).toMonoidHom)) := by
  obtain ⟨L, q_eq, -⟩ := h.isLocalGalois_and_residueCard_eq_and_isUniformiser Γ
  obtain ⟨π, hπ, π_unif⟩ := h.exists_uniformiser Γ
  let D := decompGroup Γ A
  intro χ x
  obtain ⟨r, hr⟩ :=
    L.classOfInvariant_bijective.surjective (-cyclicClass _ χ (DiscreteUnits.ofBase D Ω (.ofMul x)))
  -- `π` stays a uniformiser in `K_w`, so its image under `j` has order one.
  have π_unif_w : IsUniformiser (intQpBar p) (algebraMap K (LocField w) π) :=
    emb.isUniformiser_iff.mpr (by rw [v_algebraMap_eq_valuation, hπ])
  have π_ord : ordRat (LocField w) (intQpBar p)
      ((Units.map j).toAdditive (DiscreteUnits.ofBase D Ω (.ofMul π)).val) = 1 :=
    (congrArg _ (ext (emb.map_algebraMap π))).trans (π_unif_w.ordRat_eq_one emb.toIsLocalGalois
      (π := Units.map (algebraMap K (LocField w)).toMonoidHom π))
  obtain ⟨h_inj_w, -⟩ := emb.isClassOfInvariant_classOfInvariant
  have h_card : residueCard (LocField w) (intQpBar p) = residueCard (fixedFieldOf D) A ^ 1 := by
    rw [emb.residueCard_eq, q_eq, pow_one]
  -- The class of invariant `r` goes to the class of invariant `(1 * 1) • r`.
  -- (left untyped: its statement carries the equivariance proof that `pairMapH2` takes)
  have pair :=
    L.pairMapH2_classOfInvariant (L' := emb.toIsLocalGalois) (e := 1) (f := 1) (.id _) j
      emb.comap_eq emb.equivariant ⟨π_unif.ordRat_eq_one L, mod_cast π_ord⟩ h_card r
  rw [mul_one, one_nsmul] at pair
  -- By injectivity of the invariant of `K_w`, it is enough to compare the classes over `ℚ̄_p`.
  refine (congrArg _ (h_inj_w ?_)).trans hr
  -- It remains to see that `j` carries the cocycle of `(χ, x)` over `Ω` to the one over `ℚ̄_p`.
  rw [MonoidHom.comp_apply, hf, ← pair, hr, map_neg, neg_inj]
  -- both are classes of cocycles, which agree as `j` extends the embedding of `K` in `K_w`
  apply congrArg (Quotient.mk _)
  ext
  simp [emb.map_algebraMap]

/-- Let `A` lie over `w` (`h`) and let `emb` embed `K_w`, and `Ω` by `j`, in `ℚ̄_p`, inducing `A`
(`New.IsCompletionEmb`). Then `f = New.localArtin Γ A w` satisfies `χ (f x) = -inv (χ, x)` for every
character `χ` of the decomposition group: (a) for `x` in `K_w^×`, with the invariant of `K_w` read
in `ℚ̄_p`, relative to its valuation ring `intQpBar p`; (b) for `x` in `K^×`, with the invariant of
the fixed field of the decomposition group.

This is the characterisation of the local Artin map by invariants from the local reciprocity law,
for completions of number fields. -/
lemma isLocalArtin_localArtin {p : ℕ} [Fact p.Prime] [Algebra (LocField w) (PadicAlgCl p)]
    {j : Ω →+* PadicAlgCl p} (emb : IsCompletionEmb w p Γ A j) :
    let f := localArtin Γ A w
    -- (a)
    IsLocalArtin (decompGroup Γ A) (LocField w) (intQpBar p) f ∧
    -- (b)
    IsLocalArtin (decompGroup Γ A) (fixedFieldOf (decompGroup Γ A)) A
      (f.comp (Units.map (algebraMap K (LocField w)).toMonoidHom)) := by
  obtain ⟨L, -, -⟩ := h.isLocalGalois_and_residueCard_eq_and_isUniformiser Γ
  obtain ⟨h_inj, -⟩ := L.isClassOfInvariant_classOfInvariant
  let D := decompGroup Γ A
  -- Pontryagin duality gives `f` on `K_wˣ` with `χ (f x) = -inv (χ, x)`, the invariant of `K_w`.
  let inv := (AddEquiv.ofBijective _ emb.classOfInvariant_bijective).symm
  obtain ⟨f, hf_lift⟩ := exists_hom_abelianLift_eq
    (((-cyclicClass _).compr₂ inv.toAddMonoidHom).flip.comp
      (DiscreteUnits.ofBase D (K := LocField w) _))
  have hf : IsLocalArtin D (LocField w) (intQpBar p) f := fun χ x ↦ by simp [hf_lift, inv, D]
  -- On `Kˣ`, `f` obeys the formula `P` for the invariant of the decomposition field.
  let ι : Kˣ →* (LocField w)ˣ := map (algebraMap K (LocField w)).toMonoidHom
  let P (f : (LocField w)ˣ →* TopologicalAbelianization D) :=
    IsLocalArtin D (fixedFieldOf D) A (f.comp ι)
  have hf_fix : P f := h.isLocalArtin_comp_unitsMap emb hf
  -- `localArtin` is chosen with this property on `Kˣ`, and `f` shows that a choice exists.
  have spec : P (localArtin Γ A w) :=
    isLocalArtin_localArtin_comp_of_exists Γ A w ⟨f, hf_fix⟩
  -- So `localArtin` and `f` agree on the dense `Kˣ`, and both are continuous.
  have agree : localArtin Γ A w = f := by
    refine ext' <| (continuous_hom_locField_units _).ext_on ((w.denseRange_algebraMap K).preimage
      isOpenMap_val) (continuous_hom_locField_units f) fun y ⟨x, hx⟩ ↦ ?_
    have hy : ι (mk0 x (by grind [ne_zero])) = y := ext hx
    rw [← hy]
    exact abelianization_ext fun χ ↦ h_inj ((spec χ _).trans (hf_fix χ _).symm)
  rw [← agree] at hf
  exact ⟨hf, spec⟩

omit h [Algebra K Ω] in
/-- Let `k` be a number field below `K` and `u` the place of `k` below `w`. The completion `K_w` is
finite over `k_u`, along `New.locMap`, the map of completions induced by `k → K`, and the local norm
`New.localNorm k w` is the norm of this extension. -/
lemma finite_and_localNorm_eq_norm (k : Type) [Field k] [NumberField k] [Algebra k K]
    (w : FinPlace K) :
    letI : Algebra (LocField (w.below k)) (LocField w) := (locMap (algebraMap k K) rfl).toAlgebra
    Module.Finite (LocField (w.below k)) (LocField w) ∧
    ∀ y : (LocField w)ˣ, localNorm k w y = y.map (Algebra.norm (LocField (w.below k))) := by
  set u : FinPlace k := w.below k
  let V := LocField u
  let W := LocField w
  -- `K_w` is the quotient of `k_u ⊗[𝔸f k] 𝔸f K` by the kernel of `π`.
  algebraize [locMap _ (refl u), evalAt u, (locMap _ rfl).comp (evalAt u)]
  let evalAlg : 𝔸f K →ₐ[𝔸f k] LocField w := ⟨evalAt w, by aesop⟩
  let π : TensorProduct (𝔸f k) V (𝔸f K) →ₗ[V] LocField w := evalAlg.toLinearMap.liftBaseChange V
  have π_single (x : LocField w) : π ((1 : V) ⊗ₜ[𝔸f k] singleAdele w x) = x := by aesop
  let ε : (TensorProduct (𝔸f k) V (𝔸f K) ⧸ π.ker) ≃ₗ[V] LocField w :=
    π.quotKerEquivOfSurjective fun x ↦ ⟨_, π_single x⟩
  refine ⟨Finite.equiv ε, fun y ↦ ?_⟩
  -- Multiplication `M` by `locIdele w y` is the identity on `ker π` (the places other than `w`)
  -- and is multiplication by `y` on the quotient, so `det M` is the local norm.
  let M : TensorProduct (𝔸f k) V (𝔸f K) →ₗ[V] TensorProduct (𝔸f k) V (𝔸f K) :=
    (mulLeft (𝔸f k) (locIdele w y).val).baseChange V
  have one_tmul_surj : Function.Surjective (TensorProduct.mk (𝔸f k) V (𝔸f K) 1) :=
    TensorProduct.mk_surjective (R := 𝔸f k) (S := V) (M := 𝔸f K) fun x ↦
      ⟨singleAdele u x, dite_eq_left rfl⟩
  have fixes_ker : ∀ x ∈ π.ker, M x = x := by
    refine one_tmul_surj.forall.mpr fun z hz ↦ ?_
    -- `z` has component `0` at `w`, and `locIdele w y` has component `1` at the other places
    have h_fix : (locIdele w y).val * z = z := ext_iff.mpr ((and_forall_ne w).mp (by aesop))
    exact congrArg (TensorProduct.mk (𝔸f k) V (𝔸f K) 1) h_fix
  have stable : ∀ x ∈ π.ker, M x ∈ π.ker := by grind
  have on_ker : M.restrict stable = 1 :=
    LinearMap.ext fun x ↦ Subtype.ext (fixes_ker x x.property)
  have on_quot : π.ker.mapQ π.ker M stable = ε.symm ∘ₗ Algebra.lmul V W y ∘ₗ ε.symm.symm := by
    ext z
    have h_mul : π ((1 : V) ⊗ₜ[𝔸f k] ((locIdele w y).val * z)) =
        (y : LocField w) * π ((1 : V) ⊗ₜ[𝔸f k] z) := by aesop
    exact ε.eq_symm_apply.mpr h_mul
  -- `det M` is the determinant of multiplication by `y`, and it is the `u`-component of the adelic
  -- norm of `locIdele w y`.
  have h_det : M.det = (Algebra.lmul V W y).det := by
    rw [M.det_eq_det_mul_det π.ker stable, on_ker, on_quot, map_one, one_mul, det_conj]
  exact ext ((det_baseChange _).symm.trans h_det)

omit h in
/-- Let `j : Ω → Ω` extend `k → K`. An embedding of `K_w` in `ℚ̄_p` that induces `A` along `i`
restricts to an embedding of the completion of `k` below `w` that induces `A.comap j` along
`i ∘ j`. -/
lemma _root_.New.IsPadicAt.below {k : Type} [Field k] [EmbeddedNumberField k] [Algebra k K]
    {p : ℕ} [Fact p.Prime] [Algebra (LocField w) (PadicAlgCl p)] {i : Ω →+* PadicAlgCl p}
    (h_at : IsPadicAt w p A i) {j : Ω →+* Ω}
    (hj : ∀ x : k, j (algebraMap k Ω x) = algebraMap K Ω (algebraMap k K x)) :
    letI : Algebra (LocField (w.below k)) (PadicAlgCl p) :=
      ((algebraMap (LocField w) (PadicAlgCl p)).comp (locMap (algebraMap k K) rfl)).toAlgebra
    IsPadicAt (w.below k) p (A.comap j) (i.comp j) := by
  let ι : LocField (w.below k) →+* LocField w := locMap (algebraMap k K) rfl

  have ι_comm (x : k) : i (j (algebraMap k Ω x)) =
      algebraMap (LocField w) (PadicAlgCl p) (ι (algebraMap k (LocField (w.below k)) x)) := by
    simp [hj, h_at.map_algebraMap, ι]
  -- the integers of `ℚ̄_p` meet `K_w` in `LocInt w`, and `i` pulls them back to `A`
  have val_eq : (valRingBelow (LocField w) (intQpBar p)).comap ι = LocInt (w.below k) := by
    rw [h_at.valRingBelow_eq]
    exact SetLike.ext fun _ ↦ v_locMap_le_one_iff ..
  let : Algebra (LocField (w.below k)) (PadicAlgCl p) :=
    ((algebraMap (LocField w) (PadicAlgCl p)).comp ι).toAlgebra
  exact
    { continuous := h_at.continuous.comp (continuous_locMap ..)
      valRingBelow_eq := val_eq
      comap_eq := congrArg (·.comap j) h_at.comap_eq
      map_algebraMap := ι_comm }

section Norm

variable {Γ' k : Type} [Group Γ'] [TopologicalSpace Γ'] [Field k] [EmbeddedNumberField k]
  [MulSemiringAction Γ' Ω] [IsProGalois Γ' k Ω] [Algebra k K]

omit h in
/-- Let `K / k` be number fields with Galois groups `Γ` and `Γ'`, and let `ψ : Γ → Γ'` be the map
induced by `j : Ω → Ω`. The local Artin maps at `A` over `w` and at `A.comap j` over the place of
`k` below `w` are compatible with the local norm from `K_w`. -/
structure _root_.New.IsNormCompatible (A : ClosurePlace) (w : FinPlace K) (ψ : Γ →* Γ')
    (j : Ω →+* Ω) (hψ : ∀ (g : Γ) (x : Ω), j (ψ g • x) = g • j x) : Prop where
  /-- If `y` has the symbol `g`, then the norm of `y` has the symbol `ψ g`. -/
  localArtin_localNorm {y : (LocField w)ˣ} {g : decompGroup Γ A} (hy : localArtin Γ A w y = g) :
    localArtin Γ' (A.comap j) (w.below k) (localNorm k w y) =
      (⟨ψ g, decompGroup.map hψ g.property⟩ : decompGroup Γ' (A.comap j))
  /-- If the kernel of `χ` is the image of the decomposition group of `A` under `ψ` and `χ` kills
  the symbol of `x`, then `x` is a local norm. -/
  exists_localNorm_eq {χ : QZChar (decompGroup Γ' (A.comap j))} {x : (LocField (w.below k))ˣ}
    (hχ : ∀ g' : decompGroup Γ' (A.comap j), χ.val g' = 0 ↔ ∃ g : decompGroup Γ A, ψ g = g')
    (hx : abelianLift χ (localArtin Γ' (A.comap j) (w.below k) x) = 1) :
    ∃ y : (LocField w)ˣ, localNorm k w y = x

omit h in
/-- The symbol of a norm, computed in `ℚ̄_p`. Let `emb_w` and `emb_u` embed `K_w` and `k_u`, for the
place `u` of `k` below `w`, in `ℚ̄_p` through `i` and `i ∘ j`, and let `φ` be the inclusion of the
Galois group of `ℚ̄_p` over `K_w` in that over `k_u` (`hφ`, continuous by `φ_cont`). Let the local
norm be the field norm of `K_w` over `k_u` (`norm_eq`), and let both local Artin maps satisfy the
defining formula of `New.IsLocalArtin` (`art_w`, `art_u`). If `y` in `K_w^×` has the symbol `g`,
then its local norm has the symbol `φ g`. -/
lemma localArtin_localNorm_eq_of_isCompletionEmb {p : ℕ} [Fact p.Prime]
    [Algebra (LocField (w.below k)) (LocField w)]
    [Module.Finite (LocField (w.below k)) (LocField w)]
    [Algebra (LocField w) (PadicAlgCl p)] [Algebra (LocField (w.below k)) (PadicAlgCl p)]
    [IsScalarTower (LocField (w.below k)) (LocField w) (PadicAlgCl p)]
    {i : Ω →+* PadicAlgCl p} (emb_w : IsCompletionEmb w p Γ A i) {j : Ω →+* Ω}
    (emb_u : IsCompletionEmb (w.below k) p Γ' (A.comap j) (i.comp j))
    (φ : decompGroup Γ A →* decompGroup Γ' (A.comap j)) (φ_cont : Continuous φ)
    (hφ : ∀ (g : decompGroup Γ A) (x : PadicAlgCl p), φ g • x = g • x)
    (norm_eq : ∀ y : (LocField w)ˣ,
      localNorm k w y = y.map (Algebra.norm (LocField (w.below k))))
    (art_u : IsLocalArtin (decompGroup Γ' (A.comap j)) (LocField (w.below k)) (intQpBar p)
      (localArtin Γ' (A.comap j) (w.below k)))
    (art_w : IsLocalArtin (decompGroup Γ A) (LocField w) (intQpBar p) (localArtin Γ A w))
    {y : (LocField w)ˣ} {g : decompGroup Γ A} (hy : localArtin Γ A w y = g) :
    localArtin Γ' (A.comap j) (w.below k) (localNorm k w y) =
      ((φ g : decompGroup Γ' (A.comap j)) :
        TopologicalAbelianization (decompGroup Γ' (A.comap j))) := by
  -- Write `(χ|_U, y)` as the restriction of the class of invariant `r` over `k_u`, where `U` is
  -- the image of `φ`. Corestriction gives `inv (χ, N y) = n r` with `n` the index of `U`, and
  -- restriction multiplies invariants by `n`, so `inv (χ ∘ φ, y) = n r` over `K_w` as well.
  let V := LocField (w.below k)
  let W := LocField w
  let D := decompGroup Γ A
  let D' := decompGroup Γ' (A.comap j)
  have inj_u : Function.Injective (classOfInvariant D' V (intQpBar p)) :=
    emb_u.isClassOfInvariant_classOfInvariant.left
  have inj_w : Function.Injective (classOfInvariant D W (intQpBar p)) :=
    emb_w.isClassOfInvariant_classOfInvariant.left
  have gal_W : IsProGalois D W (PadicAlgCl p) := emb_w.toIsProGalois
  have gal_V : IsProGalois D' V (PadicAlgCl p) := emb_u.toIsProGalois
  -- The image `U` of `φ` is open, and it is the Galois group of `ℚ̄_p` over `K_w`.
  let U : OpenSubgroup D' :=
    ⟨φ.range, (isOpenEmbedding_galois_restrict (L := W) φ hφ).isOpen_range⟩
  have U_open : Fact (IsOpen U.toSubgroup.carrier) := ⟨U.isOpen'⟩
  obtain ⟨-, range_eq, -⟩ := isClosedEmbedding_galois_restrict (L := W) φ hφ
  have gal_U : IsProGalois φ.range W (PadicAlgCl p) := of_fixingSubgroup_eq (K := V) range_eq.symm
  refine abelianization_ext fun χ ↦ Multiplicative.ext (inj_u ?_)
  let Φ : D →ₜ* D' := ⟨φ, φ_cont⟩
  obtain ⟨r, hr⟩ := emb_u.exists_resH2_classOfInvariant_eq U
    (cyclicClass _ (comap (subgroupIncl U.1) χ) (DiscreteUnits.ofBase _ _ (.ofMul y)))
  have cor : cyclicClass _ χ (DiscreteUnits.ofBase _ _ (.ofMul (y.map (Algebra.norm V)))) =
      classOfInvariant D' V (intQpBar p) (U.1.index • r) :=
    (DiscreteModule.cyclicClass_corestrictH0 U χ _ (corestrictH0_ofBase_eq_norm U y) _ hr).trans
      (map_nsmul (classOfInvariant D' V (intQpBar p)) U.1.index r).symm
  -- `e` and `f` are the ramification index and residue degree of `K_w` over `k_u`; `e f = [D' : U]`
  obtain ⟨e, f, h_data, -⟩ := (emb_u.of_finite U W).exists_isRamificationData
  have unif_ord : ordRat (LocField (w.below k)) (intQpBar p)
      (DiscreteUnits.ofBase D' (PadicAlgCl p) (.ofMul (uniformizer (w.below k)))) = 1 :=
    (emb_u.isUniformiser_iff.mpr (v_uniformizer (w.below k))).ordRat_eq_one emb_u.toIsLocalGalois
  have res : cyclicClass _ (comap Φ χ) (DiscreteUnits.ofBase _ _ (.ofMul y)) =
      classOfInvariant D W (intQpBar p) (U.1.index • r) := by
    rw [← h_data.mul_eq, ← emb_u.pairMapH2_classOfInvariant Φ (.id _) rfl hφ
      ⟨unif_ord, by simp [h_data.ordRat_eq, unif_ord]⟩ h_data.residueCard_eq r]
    -- Pulling back along `φ` is restriction to `U` followed by the isomorphism onto `U`.
    let Φ' : D →ₜ* U.1 := ⟨φ.rangeRestrict, φ_cont.subtype_mk _⟩
    refine (congrArg (pairMapH2 (ρ' := unitsRep) Φ' .id fun g _ ↦ DiscreteUnits.ext (hφ g _))
      hr).symm.trans ?_
    obtain ⟨z, hz⟩ := Quot.exists_rep (classOfInvariant D' V (intQpBar p) r)
    rw [← hz]
    rfl
  -- So `χ` at the symbol of the norm of `y` and at `φ (Art y)` both have invariant `-n r`, over
  -- `k_u` and over `K_w`.
  have h_norm : classOfInvariant D' V (intQpBar p)
      (abelianLift χ (localArtin Γ' (A.comap j) (w.below k) (localNorm k w y))).toAdd =
        -classOfInvariant D' V (intQpBar p) (U.1.index • r) := by
    rw [norm_eq, art_u, cor]
  have h_sym : classOfInvariant D W (intQpBar p)
    (abelianLift (comap Φ χ) (localArtin Γ A w y)).toAdd =
      -classOfInvariant D W (intQpBar p) (U.1.index • r) := by
    rw [art_w, res]
  rw [h_norm, ← map_neg]
  congr 1
  apply inj_w
  rw [map_neg, ← h_sym, hy]
  -- `comap Φ χ` at `g` is `χ` at `φ g`, by definition
  rfl

/-- Let `K / k` be number fields, with `Γ` and `Γ'` acting on `Ω` as their Galois groups. Let
`j : Ω → Ω` extend `k → K` (`hj`) and induce `ψ : Γ → Γ'` (`hψ`), and let the valuation subring `A`
of `Ω` lie over the finite place `w` of `K` (`h`). Then local class field theory is norm functorial
here: the local Artin map at `A` over `w` and the local Artin map at `A.comap j` over the place of
`k` below `w` are compatible with the local norm from `K_w` and with `ψ`
(`New.IsNormCompatible`). -/
lemma isNormCompatible (ψ : Γ →* Γ') (j : Ω →+* Ω)
    (hψ : ∀ (g : Γ) (x : Ω), j (ψ g • x) = g • j x)
    (hj : ∀ x : k, j (algebraMap k Ω x) = algebraMap K Ω (algebraMap k K x)) :
    IsNormCompatible (k := k) A w ψ j hψ := by
  -- Both local Artin maps are computed in one `ℚ̄_p`, where they are given by invariants of cyclic
  -- classes. Compatibility with the norm is then the behaviour of invariants under corestriction
  -- and restriction; the criterion is that `(χ, x)` vanishes exactly on norms.
  set u : FinPlace k := w.below k
  let V := LocField u
  let W := LocField w
  algebraize [locMap _ (refl u)]
  obtain ⟨finite_W : Module.Finite V W,
      norm_eq : ∀ y : Wˣ, localNorm k w y = y.map (Algebra.norm V)⟩ :=
    finite_and_localNorm_eq_norm k w
  -- Embed `K_w`, and through it `k_u`, in `ℚ̄_p`; the decomposition groups become the Galois
  -- groups of `ℚ̄_p` over `K_w` and `k_u`, and `φ` is the inclusion of the first in the second.
  obtain ⟨p, p_prime, algebra_W, i, ⟨emb_w⟩⟩ := h.exists_isCompletionEmb Γ
  algebraize [(algebraMap W (PadicAlgCl p)).comp (algebraMap V W)]
  have padic_u : IsPadicAt u p (A.comap j) (i.comp j) := emb_w.toIsPadicAt.below hj
  obtain ⟨emb_u⟩ := nonempty_isCompletionEmb_of_isPadicAt Γ' (i.comp j) padic_u
  let D := decompGroup Γ A
  let D' := decompGroup Γ' (A.comap j)
  have gal_W : IsProGalois D W (PadicAlgCl p) := emb_w.toIsProGalois
  have gal_V : IsProGalois D' V (PadicAlgCl p) := emb_u.toIsProGalois
  obtain ⟨⟨φ, φ_cont⟩, hφ : ∀ (g : D) (x : PadicAlgCl p), φ g • x = g • x⟩ :=
    exists_galois_restrict D' (G := gal_V) D (L := W) (.id _)
      fun g _ ↦ smul_algebraMap g (_ : W)
  have over_u : IsPlaceOver (A.comap j) u := by
    simp [IsPlaceOver, hj, comap_apply_lt_one_iff, ← h _, u]
  have art_u : IsLocalArtin D' V (intQpBar p) (localArtin Γ' (A.comap j) u) :=
    (over_u.isLocalArtin_localArtin emb_u).left
  have art_w : IsLocalArtin D W (intQpBar p) (localArtin Γ A w) :=
    (h.isLocalArtin_localArtin emb_w).left
  -- On the decomposition group `ψ` is `φ`, as both act on `Ω` in the same way.
  have ψ_eq (g : D) : ψ g = φ g := by
    refine (IsGaloisGroup.faithful k).eq_of_smul_eq_smul fun x ↦ j.injective (i.injective ?_)
    have h_w : i (j (ψ g • x)) = g • i (j x) := (congrArg i (hψ g x)).trans (emb_w.equivariant g _)
    have h_u : i (j ((φ g : Γ') • x)) = φ g • i (j x) := emb_u.equivariant (φ g) x
    rw [h_w, h_u, hφ]
  -- The image of `φ` is open (hence closed), the Galois group of `ℚ̄_p` over `K_w`.
  have range_open : Fact (IsOpen φ.range.carrier) :=
    ⟨(isOpenEmbedding_galois_restrict (L := W) φ hφ).isOpen_range⟩
  obtain ⟨-, range_eq, -⟩ := isClosedEmbedding_galois_restrict (L := W) φ hφ
  have gal_U : IsProGalois φ.range W (PadicAlgCl p) := of_fixingSubgroup_eq (K := V) range_eq.symm
  refine ⟨fun {y g} hy ↦ ?_, fun {χ x} hχ hx ↦ ?_⟩
  · -- the symbol of the norm, computed in `ℚ̄_p`
    simp_rw [ψ_eq]
    exact localArtin_localNorm_eq_of_isCompletionEmb emb_w emb_u φ φ_cont hφ norm_eq art_u art_w hy
  · -- `ker χ` is the subgroup fixing `K_w`, and `χ (Art x) = 0` forces `(χ, x) = 0`, so `x` is a
    -- norm from `K_w`.
    simp_rw [ψ_eq] at hχ
    -- (`using!`: `hχ` matches the kernel and the range only after unfolding.)
    have ker_eq : QZChar.ker χ = φ.range := by
      ext g'
      simpa using! hχ g'
    have cyc_zero : cyclicClass _ χ (DiscreteUnits.ofBase _ (PadicAlgCl p) (.ofMul x)) = 0 := by
      simpa [u, hx] using art_u χ x
    have gal_ker : IsProGalois (QZChar.ker χ) W (PadicAlgCl p) := by rwa [ker_eq]
    obtain ⟨z, hz⟩ := (cyclicClass_eq_zero_iff_norm (J := gal_ker) x).mp cyc_zero
    exact ⟨z, (norm_eq z).trans hz⟩

/-- Norm compatibility of the local Artin maps (`New.IsNormCompatible`) at `A` over `w`, as in
`New.IsPlaceOver.isNormCompatible`; `j` is the identity of `Ω` unless given, and the two hypotheses
on `j` then default to the tactic proofs `by tauto` and `by simp`, which may fail. -/
lemma localArtin_localNorm (ψ : Γ →* Γ') (j : Ω →+* Ω := 1)
    (hψ : ∀ (g : Γ) (x : Ω), j (ψ g • x) = g • j x := by tauto)
    (hj : ∀ x : k, j (algebraMap k Ω x) = algebraMap K Ω (algebraMap k K x) := by simp) :
    IsNormCompatible (k := k) A w ψ j hψ :=
  h.isNormCompatible ψ j hψ hj

end Norm

/-! ### The image of the local Artin map -/

/-- If `A` lies over `w`, the local Artin map `New.localArtin Γ A w` from `K_w^×` to the abelianised
decomposition group of `A` has dense range.

A consequence of the local reciprocity law, stating only that the image is dense. -/
lemma denseRange_localArtin : DenseRange (localArtin Γ A w) := by
  -- By duality it is enough that a character `χ` killing the closure of the range is zero.
  obtain ⟨p, hp_prime, alg, j, ⟨emb⟩⟩ := h.exists_isCompletionEmb Γ
  rintro ⟨g⟩
  refine mem_of_forall_abelianLift (localArtin Γ A w).range.isClosed_topologicalClosure
    (g : TopologicalAbelianization (decompGroup Γ A)) fun χ hχ ↦ ?_
  -- The formula `classOfInvariant (χ (Art x)) = -(χ, x)` makes all classes `(χ, x)` vanish.
  have h_cyc (x : Additive (LocField w)ˣ) :
      cyclicClass unitsRep χ (DiscreteUnits.ofBase (decompGroup Γ A) (PadicAlgCl p) x) = 0 := by
    simpa [hχ _ (subset_closure ⟨x.toMul, rfl⟩)] using
      (h.isLocalArtin_localArtin emb).left χ x.toMul
  have h_zero : χ.val g = 0 :=
    char_eq_zero_of_cyclicClass_eq_zero (k := LocField w) (A := intQpBar p) h_cyc g
  simp [abelianLift_mk, h_zero]

/-- The local Artin symbol of a uniformiser of `K_w` is the class of the inverse of a Frobenius
element at `A`. This is the clause on uniformisers of the local reciprocity law, for completions of
number fields. -/
lemma exists_isFrob_localArtin_eq_inv {x : (LocField w)ˣ} (hx : v x.val = exp (-1)) :
    ∃ s : decompGroup Γ A, IsFrob A w.q s.val ∧ localArtin Γ A w x = s⁻¹ := by
  obtain ⟨p, p_prime, algebra_w, j, ⟨emb⟩⟩ := h.exists_isCompletionEmb Γ
  obtain ⟨s, hs, s_art⟩ := (h.isLocalArtin_localArtin emb).left.exists_frob_of_isUniformiser
    (emb.isUniformiser_iff.mpr hx)
  -- A Frobenius for `intQpBar p` in `ℚ̄_p` is one for `A = (intQpBar p).comap j`, for the same `q`.
  have frob : IsFrob ((intQpBar p).comap j) (residueCard (LocField w) (intQpBar p)) s.val :=
    hs.map emb.equivariant
  exact ⟨s, by rwa [emb.comap_eq, emb.residueCard_eq] at frob, s_art⟩

/-- The local Artin symbol of a unit of `K_w` is the class of an element of the inertia group of
`A`. This is the clause on units of the local reciprocity law, for completions of number fields. -/
lemma exists_mem_inertiaGroup_localArtin_eq {x : (LocField w)ˣ} (hx : v x.val = 1) :
    ∃ s : decompGroup Γ A, ↑s ∈ inertiaGroup Γ A ∧ localArtin Γ A w x = s := by
  -- The uniformisers `uniformizer w` and `x * uniformizer w` have symbols `φ⁻¹` and `ψ⁻¹` with `φ`,
  -- `ψ` Frobenii, so `x` has symbol `ψ⁻¹ * φ`, which lies in inertia.
  obtain ⟨φ, hφ, φ_art⟩ := h.exists_isFrob_localArtin_eq_inv (Γ := Γ) (v_uniformizer w)
  obtain ⟨ψ, hψ, ψ_art⟩ :=
    h.exists_isFrob_localArtin_eq_inv (Γ := Γ) (x := x * uniformizer w) (by simpa)
  rw [map_mul, φ_art] at ψ_art
  exact ⟨ψ⁻¹ * φ, hψ.inv_mul_mem_inertiaGroup hφ, by simpa using eq_mul_of_mul_inv_eq ψ_art⟩

/-- Let `g⁻¹` stabilise `A` and act on residues as `x ↦ x ^ q ^ n`, where `q` is the residue order
of `w`. Then the class of `g` is the local Artin symbol of an element of `K_wˣ` of order `n`.

This is the surjectivity part of the local reciprocity law, onto the image of the elements of the
Weil group of non-negative degree. -/
lemma exists_localArtin_eq_of_isFrob_pow {g : Γ} {n : ℕ} (hg : IsFrob A (w.q ^ n) g⁻¹) :
    ∃ x : (LocField w)ˣ, v x.val = exp (-(n : ℤ)) ∧
      localArtin Γ A w x = (⟨g, inv_mem_iff.mp hg.left⟩ : decompGroup Γ A) := by
  obtain ⟨local_galois, q_eq, -⟩ := h.isLocalGalois_and_residueCard_eq_and_isUniformiser Γ
  obtain ⟨φ, hφ : IsFrob A w.q φ.val, φ_art : localArtin Γ A w (uniformizer w) = φ⁻¹⟩ :=
    h.exists_isFrob_localArtin_eq_inv (Γ := Γ) (v_uniformizer w)
  -- `s = g φ ^ n` lies in inertia. If it is the symbol of a unit `u`, take
  -- `x = u * uniformizer w ^ n`.
  let s : decompGroup Γ A := ⟨g, inv_mem_iff.mp hg.left⟩ * φ ^ n
  have s_mem : s.val ∈ inertiaGroup Γ A := by simpa [s] using hg.inv_mul_mem_inertiaGroup (hφ.pow n)
  let H : Subgroup (TopologicalAbelianization (decompGroup Γ A)) :=
    ((idelesUnitOff ∅).map (ideleAt w)).map (localArtin Γ A w)
  suffices s_mem_H : ↑s ∈ H by
    obtain ⟨u, ⟨a, ha_unit, rfl⟩, hu_art⟩ := s_mem_H
    have hu_val : v (ideleAt w a).val = 1 := mem_idelesUnitOff.mp ha_unit w (Set.notMem_empty w)
    exact ⟨ideleAt w a * uniformizer w ^ n, by simp [hu_val], by simp [hu_art, φ_art, s]⟩
  -- The image `H` of the units is compact; test against a character `χ` that kills it.
  have H_compact : IsCompact H.carrier :=
    (isCompact_idelesUnitOff_empty.image (continuous_ideleAt w)).image
      (continuous_hom_locField_units _)
  refine mem_of_forall_abelianLift H_compact.isClosed _ fun χ hχ ↦ ?_
  -- The `ψ` that kills inertia and has `ψ φ = χ φ` agrees with `χ` on the symbols of
  -- `uniformizer w` and of all units, hence on the dense range of `localArtin`; so `χ s = ψ s = 0`.
  have hφ_residue : IsFrob A (residueCard (fixedFieldOf (K := K) (decompGroup Γ A)) A) φ := by
    rwa [q_eq]
  obtain ⟨ψ, ⟨ψ_unr, ψ_frob⟩, -⟩ : ∃! ψ : QZChar (decompGroup Γ A),
      (∀ t ∈ inertiaGroup (decompGroup Γ A) A, ψ.val t = 0) ∧ ψ.val φ = χ.val φ :=
    existsUnique_unramified_char hφ_residue (χ.val φ)
  let E : Subgroup (LocField w)ˣ :=
    ((abelianLift ψ).eqLocus (abelianLift χ)).comap (localArtin Γ A w)
  have unif_mem : uniformizer w ∈ E := by simpa [E, φ_art]
  have unit_mem (u : (LocField w)ˣ) (hu : v u.val = 1) : u ∈ E := by
    obtain ⟨t, ht, t_art⟩ := h.exists_mem_inertiaGroup_localArtin_eq (Γ := Γ) hu
    have hψu : abelianLift ψ (localArtin Γ A w u) = 1 := by
      rw [t_art]
      exact ψ_unr t ht
    have hχu : abelianLift χ (localArtin Γ A w u) = 1 :=
      hχ _ ⟨u, ⟨locIdele w u, locIdele_mem_idelesUnitOff hu, ideleAt_locIdele ..⟩, rfl⟩
    exact hψu.trans hχu.symm
  -- Every `x` is a unit times a power of `uniformizer w`.
  have cancel_log (x : (LocField w)ˣ) : v x.val * exp (-(v x.val).log) = 1 := by
    rw [exp_neg, exp_log (by simp), mul_inv_cancel₀ (by simp)]
  have mem_E (x : (LocField w)ˣ) : x ∈ E :=
    (mul_mem_cancel_right (zpow_mem unif_mem (v x.val).log)).mp
      (unit_mem _ (by simpa using cancel_log x))
  have agree : ∀ σ : TopologicalAbelianization (decompGroup Γ A),
      abelianLift ψ σ = abelianLift χ σ := h.denseRange_localArtin.eq mem_E
  exact (agree s).symm.trans (ψ_unr s s_mem)

/-- For a place `A` of `Ω` lying over the finite place `w` of the number field `K` (hypothesis `h`),
with `Γ` the Galois group of `Ω/K`, every `g` in the inertia group of `A` is hit by the local Artin
map on units. That is, there is a unit `x` of the completion `K_w` with `v x = 1` whose local Artin
symbol `localArtin Γ A w x` equals the image of `g` in the abelianised decomposition group of
`A`. -/
lemma exists_localArtin_eq_of_mem_inertiaGroup {g : Γ} (hg : g ∈ inertiaGroup Γ A) :
    ∃ x : (LocField w)ˣ, v x.val = 1 ∧
      localArtin Γ A w x = (⟨g, hg.left⟩ : decompGroup Γ A) :=
  h.exists_localArtin_eq_of_isFrob_pow (n := 0) (inv_mem hg : IsFrob A 1 g⁻¹)

/-- For a place `A` of `Ω` lying over the finite place `w` of the number field `K` (hypothesis `h`),
with `Γ` the Galois group of `Ω/K`, suppose `g⁻¹` is an arithmetic Frobenius at `A`, i.e.
`IsFrob A w.q g⁻¹` with `w.q` the size of the residue field. Then there is a uniformiser `x` of the
completion `K_w` (`v x = exp (-1)`) whose local Artin symbol `localArtin Γ A w x` equals
the image of `g` in the abelianised decomposition group of `A`. -/
lemma exists_localArtin_eq_of_isFrob {g : Γ} (hg : IsFrob A w.q g⁻¹) :
    ∃ x : (LocField w)ˣ, v x.val = exp (-1) ∧
      localArtin Γ A w x = (⟨g, inv_mem_iff.mp hg.left⟩ : decompGroup Γ A) :=
  h.exists_localArtin_eq_of_isFrob_pow (n := 1) (by rwa [pow_one])

/-- Let `g⁻¹` stabilise `A` and act on residues as `x ↦ x ^ q`, where `q = w.q ^ n`. Then the class
of `g` is the local Artin symbol of an element of `K_wˣ` of order `n`.

This is one inclusion of the local reciprocity law's description of the image of the Artin map:
classes of Weil group elements are attained. It covers completions of number fields and one sign of
the Frobenius exponent. -/
lemma exists_localArtin_eq {q : ℕ} {g : Γ} (hg : IsFrob A q g⁻¹) (n : ℕ)
    (hq : q = w.q ^ n := by simp) :
    ∃ x : (LocField w)ˣ, v x.val = exp (-(n : ℤ)) ∧
      localArtin Γ A w x = (⟨g, inv_mem_iff.mp hg.left⟩ : decompGroup Γ A) :=
  h.exists_localArtin_eq_of_isFrob_pow (by rwa [← hq])

/-! ### The map to the abelianised global group -/

/-- Let `A` lie over `w` and let the local Artin symbol of `x` be the class of `g` in the
abelianised decomposition group of `A`. Then `New.artinAt Γ w x` is the class of `g` in the
abelianisation of `Γ`: `New.artinAt Γ w` may be computed at any place over `w`. -/
lemma artinAt_eq_of_localArtin_eq {x : (IsDedekindDomain.HeightOneSpectrum.adicCompletion K w)ˣ}
    {g : decompGroup Γ A} (hg : localArtin Γ A w x = g) :
    artinAt Γ w x = g := by
  -- The chosen place above `w` is a conjugate of `A`: `ht : t • A = placeOver w`.
  obtain ⟨t, ht⟩ := h.exists_smul Γ w.isPlaceOver_placeOver
  -- `rw!` because the place occurs in the type of the decomposition group.
  rw! [New.artinAt, ← ht, smul_eq_comap]
  -- The local norm from `K_w` to itself is the identity, as the idele norm of `K / K` is.
  have h_at_w : adeleNorm K K (finAdeleIncl K K (locIdele w x).val) w =
      ((locIdele w x).val ^ finrank K K) w :=
    congrArg (fun a : 𝔸f K ↦ a w) (adeleNorm_finAdeleIncl K K (locIdele w x).val)
  have norm_self : x = localNorm K w x := by
    show x = ideleAt w (Units.map (adeleNorm K K) (locIdele w x))
    refine Units.ext ?_
    simpa [finAdeleIncl, ideleAt] using h_at_w.symm
  -- Transport of the local symbol along `t` is the case `k = K` of norm compatibility: the symbol
  -- of `x` at the conjugate place is the class of `t * g * t⁻¹`.
  let τ : Ω →+* Ω := MulSemiringAction.toRingHom Γ Ω t⁻¹
  have hτ : ∀ (g : Γ) (x : Ω), τ ((MulAut.conj t).toMonoidHom g • x) = g • τ x := by
    simp [τ, mul_smul]
  obtain ⟨h_conj_mem, h_conj⟩ : ∃ h_mem : t * g * t⁻¹ ∈ decompGroup Γ (A.comap τ),
      localArtin Γ (A.comap τ) (w.below K) (localNorm K w x) = ⟦⟨t * g * t⁻¹, h_mem⟩⟧ :=
    ⟨_, (h.isNormCompatible _ τ hτ (by simp [τ])).localArtin_localNorm hg⟩
  rw [← norm_self] at h_conj
  -- Conjugate elements have the same class in the abelianisation. (`congrArg _`: the map is the one
  -- of `New.artinAt`, and `h_conj` is stated at `w.below K`, which is `w` only after unfolding.)
  exact (congrArg _ h_conj).trans (mul_inv_cancel_comm (t : TopologicalAbelianization Γ) g)

/-- Let `A` lie over `w`. The value of a character `χ` of `Γ` at `New.artinAt Γ w x` equals the
value of its restriction `QZChar.comap (subgroupIncl _) χ` to the decomposition group of `A` at
the local symbol of `x`. -/
lemma abelianLift_artinAt (χ : ↥(QZChar Γ))
    (x : (IsDedekindDomain.HeightOneSpectrum.adicCompletion K w)ˣ) :
    abelianLift χ (New.artinAt Γ w x) =
      abelianLift (QZChar.comap (subgroupIncl (decompGroup Γ A)) χ) (localArtin Γ A w x) := by
  obtain ⟨g, hg⟩ := Quot.exists_rep (localArtin Γ A w x)
  rw [h.artinAt_eq_of_localArtin_eq hg.symm, ← hg]
  -- Both sides are `χ g`.
  rfl

/-- Let `A` lie over `w`, `χ` a character of `Γ` and `x` in `K^×`. The class (`classOfInvariant` of
the decomposition field) with invariant the value of `χ` at `New.artinAt Γ w x` is minus the
restriction (`resH2`) to the decomposition group of `A` of the global class `(χ, x) = δχ ∪ x` in
`H²(Γ, Ω^×)`. -/
lemma abelianLift_artinAt_principal (χ : ↥(QZChar Γ)) (x : Kˣ) :
    classOfInvariant (decompGroup Γ A) (fixedFieldOf (decompGroup Γ A)) A
        (abelianLift χ (New.artinAt Γ w (ideleAt w (principalIdele x)))).toAdd =
      -(unitsModule Γ).resH2 (decompGroup Γ A)
        (cyclicClass (unitsModule Γ).ρ χ (DiscreteUnits.ofBase Γ Ω (Additive.ofMul x))) := by
  obtain ⟨p, hp_prime, alg, j, ⟨emb⟩⟩ := h.exists_isCompletionEmb Γ
  rw [h.abelianLift_artinAt]
  -- The formula over the decomposition field, for the restriction of `χ`; restricting `(χ, x)` is
  -- the same as pairing the restricted character with `x`.
  exact (h.isLocalArtin_localArtin emb).right (QZChar.comap (subgroupIncl (decompGroup Γ A)) χ) x

/-- Let `A` lie over `w`, `χ` a character of `Γ` and `x` in `K^×`. Then `χ` kills
`New.artinAt Γ w x` if and only if the global class `(χ, x) = δχ ∪ x` restricts to zero on the
decomposition group of `A`. -/
lemma abelianLift_artinAt_eq_one_iff {χ : ↥(QZChar Γ)} {x : Kˣ} :
    abelianLift χ (New.artinAt Γ w (ideleAt w (principalIdele x))) = 1 ↔
      (unitsModule Γ).resH2 (decompGroup Γ A)
        (cyclicClass (unitsModule Γ).ρ χ (DiscreteUnits.ofBase Γ Ω (Additive.ofMul x))) = 0 := by
  -- `classOfInvariant` is injective, so the left side says that the class in
  -- `abelianLift_artinAt_principal` vanishes.
  rw [← neg_eq_zero, ← h.abelianLift_artinAt_principal]
  exact (map_eq_zero_iff _
    (h.isLocalGalois_decompGroup Γ).isClassOfInvariant_classOfInvariant.left).symm

open Valuation

/-! ### The tame symbol, the tame generator and tame inertia -/

omit h in
/-- The tame formula for a local field `k`, whose Galois group `G` acts on `E` with valuation ring
`B`, and a local Artin map `F` for it (`New.IsLocalArtin`). Let `q` be the number of residues of
`k`. If the unit `u` of `k` has symbol `F u = g` and `y ^ (q - 1) = π` for a uniformiser `π` of `k`,
then `g • y / y` is congruent to `u` modulo the maximal ideal of `B`. -/
lemma valuation_smul_div_sub_lt_one {G k E : Type} [Group G] [TopologicalSpace G] [Field k]
    [Field E] [Algebra k E]
    [MulSemiringAction G E] {B : ValuationSubring E} [L : IsLocalGalois G k B]
    {F : kˣ →* TopologicalAbelianization G} (hF : IsLocalArtin G k B F) {π u : kˣ}
    (hπ : IsUniformiser B π.val) (hu : B.valuation (algebraMap k E u) = 1) {g : G} (hg : F u = g)
    {y : E} (hy : y ^ (residueCard k B - 1) = algebraMap k E π) :
    B.valuation (g • y / y - algebraMap k E u) < 1 := by
  -- Write the residue order as `n + 1`; then `n` is a unit of `B`.
  obtain ⟨n, hq⟩ : ∃ n : ℕ, residueCard k B = n + 1 :=
    Nat.exists_eq_add_one.mpr L.finite_residue.card_pos
  have hn_unit : B.valuation n = 1 := by
    simpa [hq] using map_one_sub_of_lt _ (valuation_residueCard_lt_one (k := k) (A := B))
  rw [hq, Nat.add_sub_cancel] at hy
  obtain ⟨hy_ne, hn⟩ := ne_zero_of_tame_root hn_unit hy
  obtain ⟨φ, hφ, hFπ⟩ : ∃ φ : G, IsFrob B (residueCard k B) φ ∧ F π = φ⁻¹ :=
    hF.exists_frob_of_isUniformiser hπ
  -- `k` contains the `n`-th roots of unity: `cyclotomicCharMod` is trivial on inertia and at `φ`,
  -- and the products `φ ^ m * i` with `i` in inertia are dense.
  have h_cyc : ∀ g : G, cyclotomicCharMod E n g = 1 := by
    obtain ⟨-, h_dense, -⟩ := L.frobenius_spec
    refine (h_dense hφ).eq ?_ (.of_isOpen_ker _ isOpen_ker_cyclotomicCharMod.out)
    simp [cyclotomicCharMod_eq_one_of_mem_inertiaGroup _ hn_unit, hφ.cyclotomicCharMod_eq hn_unit,
      hq, ← val_inj, ZMod.natCast_self]
  -- For `x` in `kˣ`, `a x` is an `n`-th root of `x` and `f x : G → ZMod n` its Kummer character.
  let ι (x : kˣ) : unitsRep.invariants := DiscreteUnits.ofBase G E (Additive.ofMul x)
  have h_kummer_exists (x : kˣ) :
      ∃ (a : (unitsModule G).V) (f : Z1 (Representation.trivial ℤ G (ZMod n))), n • a = ι x ∧
        ∀ b : (unitsModule G).V, n • b = ι x → ∀ g : G,
          (rootPowHom E n).val (f.val g) = unitsRep g b - b :=
    exists_kummer_cocycle h_cyc (ι x)
  choose a f ha hf using h_kummer_exists
  -- `c` is the cup product for the pairing `(i, j) ↦ μ (i * j)` into the `n`-th roots of unity;
  -- `c (f x) ξ` is minus the class `δξ ∪ x` that defines the Artin map.
  let μ : ZMod n →+ DiscreteUnits E := (rootPowHom E n).val
  let T : DiscreteModule ℤ G := .of (.trivial ℤ G (ZMod n))
  have equiv (g : G) (i j : T) : μ (T.ρ g i * T.ρ g j) = (unitsModule G).ρ g (μ (i * j)) := by
    simp [T, ← map_cyclotomicCharMod_mul, h_cyc]
  let c : ↥(Z1 T.ρ) →+ ↥(Z1 T.ρ) →+ (unitsModule G).H2 :=
    cupProduct (unitsModule G) T T (.compr₂ .mul μ) equiv
  have h_cup (x : kˣ) (ξ : ↥(Z1 T.ρ)) :
      c (f x) ξ = -cyclicClass unitsRep (ofZModCocycle n ξ) (ι x) :=
    mk_eq_neg_cyclicClass_ofZModCocycle (ha x) ξ _ fun g₁ g₂ ↦ by
      simp [μ, T, ← hf x (a x) (ha x), ← map_nsmul, mul_comm]
  -- The cup product is anticommutative. Through `h_cup` and the definition of the Artin map this
  -- says that `f π` at `g` equals `f u` at `φ`.
  have h_anti : c (f u) (f π) = -c (f π) (f u) := by
    rw [← cupProduct_flip (W := unitsModule G) (M := T) (N := T) (.compr₂ .mul μ) equiv]
    -- The flipped pairing `(i, j) ↦ μ (j * i)` is the pairing itself, as `ZMod n` is commutative.
    have h_flip : (AddMonoidHom.compr₂ .mul μ : T →+ T →+ DiscreteUnits E).flip =
        .compr₂ .mul μ := by
      ext i j
      simp [mul_comm]
    simp only [c, h_flip]
  have h_symbol : (f π).val g = (f u).val φ := by
    -- By `h_cup` and the defining formula `hF` at `F u = g` and `F π = φ⁻¹`, `h_anti` says that two
    -- invariants agree; `classOfInvariant` and `QZ.ofZMod` are injective.
    have h_inv :
        classOfInvariant G k B (abelianLift (ofZModCocycle n (f π)) g).toAdd =
          -classOfInvariant G k B (abelianLift (ofZModCocycle n (f u)) (φ⁻¹ : G)).toAdd := by
      rw [← hg, ← hFπ, hF, hF, ← h_cup, ← h_cup, h_anti]
    obtain ⟨h_inj, -⟩ := L.isClassOfInvariant_classOfInvariant
    simpa [h_inj.eq_iff, QZ.ofZMod_injective.eq_iff] using h_inv
  -- In terms of the root `r = a u` of `u` in `E` this is `g • y / y = φ • r / r`.
  let r : E := (Additive.toMul (α := Eˣ) (a u)).val
  have hr_pow : r ^ n = algebraMap k E u := by simpa [ι, DiscreteUnits.ext_iff] using ha u
  have hr_unit : B.valuation r = 1 := by simpa [← hr_pow, hn.out] using hu
  have h_kummer : g • y / y = φ • r / r := by
    let Y : DiscreteUnits E := Additive.ofMul (mk0 y hy_ne)
    have h_Y : (rootPowHom E n).val ((f π).val g) = unitsRep g Y - Y := hf π Y (ext hy) g
    simpa [Y, r, DiscreteUnits.ext_iff, h_symbol, hf u (a u) (ha u)] using h_Y.symm
  -- `φ • r / r` is congruent to `r ^ n = u`, as `φ` is a Frobenius and `r` is a unit.
  have h_frob : B.valuation (φ • r - r ^ (n + 1)) < 1 := by simpa [hq] using hφ.right r hr_unit.le
  have h_eq : φ • r / r - algebraMap k E u = (φ • r - r ^ (n + 1)) / r := by
    rw [← hr_pow, sub_div, pow_succ, mul_div_cancel_right₀ _ (Units.ne_zero _)]
  rw [h_kummer, h_eq, map_div₀, hr_unit, div_one]
  exact h_frob

/-- Let `A` lie over `w`, let `π` in `K` be a uniformiser for `A` and `y ^ (w.q - 1) = π`, where
`w.q` is the number of residues of `w`, and let `u` be a unit of `K_w` (`v u = 1`, with `v` the
valuation of `K_w`) with local Artin symbol `s`. Then for `x` in `K`, `u` is congruent to `x` modulo
the maximal ideal of `K_w` if and only if `s • y / y` is congruent to `x` modulo the maximal ideal
of `A`.

A variant of the tame symbol congruence of local reciprocity. Residue classes are compared only
through elements of `K`. -/
lemma valuation_sub_lt_one_iff_of_localArtin_eq {π : K} (hπ : IsUniformiser A π)
    {s : decompGroup Γ A}
    {u : (IsDedekindDomain.HeightOneSpectrum.adicCompletion K w)ˣ} (hu : v u.val = 1)
    (hs : localArtin Γ A w u = s) {y : Ω} (hy : y ^ (w.q - 1) = algebraMap K Ω π) {x : K} :
    v (u.val - algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K w) x) < 1 ↔
      A.valuation (s.val • y / y - algebraMap K Ω x) < 1 := by
  have π_val : v (algebraMap K (LocField w) π) = exp (-1) := by
    rw [v_algebraMap_eq_valuation, h.isUniformiser_iff.mp hπ]
  obtain ⟨p, hp_prime, alg, j, ⟨emb⟩⟩ := h.exists_isCompletionEmb Γ
  obtain rfl : (intQpBar p).comap j = A := emb.comap_eq
  let ι : LocField w →+* PadicAlgCl p := algebraMap (LocField w) (PadicAlgCl p)
  -- The valuations of `K_w` and of `ℚ̄_p` restricted to `K_w` have the same valuation ring.
  have equiv : ((intQpBar p).valuation.comap ι).IsEquiv (Valued.v : Valuation (LocField w) _) :=
    (isEquiv_iff_valuationSubring ..).mpr emb.valRingBelow_eq
  have π_ne : algebraMap K (LocField w) π ≠ 0 := ne_zero_of_map (π_val.trans_ne exp_ne_zero)
  have hy_j : j y ^ (residueCard (LocField w) (intQpBar p) - 1) =
      ι (algebraMap K (LocField w) π) := by
    rw [emb.residueCard_eq, ← map_pow, hy, emb.map_algebraMap]
  -- The tame formula in `ℚ̄_p`: `s • j y / j y ≡ u` modulo the maximal ideal of `intQpBar p`.
  have tame : (intQpBar p).valuation (s • j y / j y - ι u) < 1 :=
    valuation_smul_div_sub_lt_one (L := emb.toIsLocalGalois) (h.isLocalArtin_localArtin emb).left
      (π := mk0 _ π_ne)
      (emb.isUniformiser_iff.mpr π_val) (equiv.eq_one_iff_eq_one.mpr hu) hs hy_j
  -- So `u ≡ x` if and only if `s • j y / j y ≡ x`, which `j` carries back to `Ω`.
  calc _ ↔ (intQpBar p).valuation (ι (u - algebraMap K _ x)) < 1 := equiv.lt_one_iff_lt_one.symm
    _ ↔ (intQpBar p).valuation (s • j y / j y - ι u + ι (u - algebraMap K _ x)) < 1 :=
      (((intQpBar p).valuation.ltAddSubgroup 1).add_mem_cancel_left tame).symm
    _ ↔ ((intQpBar p).comap j).valuation (s.val • y / y - algebraMap K Ω x) < 1 := by
      simp [ι, ← emb.equivariant, emb.map_algebraMap, Subgroup.smul_def, comap_apply_lt_one_iff]

end IsPlaceOver

end

/-- An element `γ` of the inertia group of `A` is a tame generator: for every `n` that is a unit at
`A` (prime to the residue characteristic) it multiplies an `n`-th root `y` of a uniformiser `π` of
`K` by a primitive `n`-th root of unity. -/
def IsTameGenerator [Algebra K Ω] {A : ClosurePlace} (γ : inertiaGroup Gal(Ω/K) A) : Prop :=
  ∀ n : ℕ, A.valuation n = 1 → ∃ (π : Kˣ) (y : Ω),
    IsUniformiser A π.val ∧ y ^ n = algebraMap K Ω π ∧ IsPrimitiveRoot (γ • y / y) n

namespace IsPlaceOver

open Valuation

variable {K : Type} [Field K] [NumberField K] {w : FinPlace K}
variable [Algebra K Ω] {A : ClosurePlace}
variable (h : IsPlaceOver A w) [IsGalois K Ω]

include h

/-- A tame generator exists: if `A` lies over `w`, some `γ` in the inertia group of `A` has the
following property for every `n` that is a unit at `A` (prime to the residue characteristic): there
are a uniformiser `π` of `K` and `y` with `y ^ n = π` such that `γ • y / y` is a primitive `n`-th
root of unity.

This is the existence of tame generators of inertia (Serre, Local Fields, IV §2), for one generator
at a place of a number field; the uniformiser may depend on `n` and the primitive root of unity is
not prescribed. -/
lemma exists_tameGenerator :
    ∃ γ : inertiaGroup Gal(Ω/K) A, ∀ n : ℕ, A.valuation n = 1 → ∃ π : Kˣ, ∃ y : Ω,
      IsUniformiser A π.val ∧ y ^ n = algebraMap K Ω π ∧ IsPrimitiveRoot (γ • y / y) n := by
  -- Fix a uniformiser `π` and, for each `n` prime to `w`, a root `y n ^ n = π`. The condition that
  -- `g • y n / y n` be a primitive `n`-th root of unity is closed and inertia is compact, so it
  -- is enough to meet finitely many conditions; one element for the product of the `n` does this.
  obtain ⟨π, hπ_val, hπ_unif⟩ := h.exists_uniformiser Gal(Ω/K)
  -- The exponents `n` that are units at `A`.
  let I : Type := {n : ℕ // A.valuation n = 1}
  have h_pos (n : I) : 0 < n.val := Nat.pos_of_ne_zero fun hn ↦ by simpa [hn] using n.property
  choose y hy using fun n : I ↦ IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω π) (h_pos n)
  have hy_ne (n : I) : y n ≠ 0 := (ne_zero_of_tame_root n.property (hy n)).1
  let good (n : I) : Set Gal(Ω/K) := {g | IsPrimitiveRoot (g • y n / y n) n}
  have h_closed (n : I) : IsClosed (good n) :=
    isClosed_setOf_smul (y n) fun z ↦ IsPrimitiveRoot (z / y n) n.val
  have h_finite (T : Finset I) : (↑(inertiaGroup Gal(Ω/K) A) ∩ ⋂ n ∈ T, good n).Nonempty := by
    let N : I := ⟨∏ n ∈ T, n.val, by
      rw [Nat.cast_prod, map_prod, T.prod_eq_one fun n _ ↦ n.property]⟩
    have hN_ne : NeZero N.val := ⟨(h_pos N).ne'⟩
    obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ N := HasEnoughRootsOfUnity.prim
    -- Inertia permutes the `N`-th roots of `π` transitively.
    obtain ⟨s, hs, hs_root⟩ : ∃ s ∈ inertiaGroup (decompGroup Gal(Ω/K) A) A, s • y N = ζ * y N :=
      (h.isLocalGalois_decompGroup _).exists_inertia_smul_eq_of_pow_eq hπ_unif (h_pos N) (hy N)
        (by rw [mul_pow, hζ.pow_eq_one, one_mul])
    refine ⟨s, hs, Set.mem_iInter₂.mpr fun n hn ↦ ?_⟩
    -- With `N = k n`, `y N ^ k` is another `n`-th root of `π`, and `s` multiplies both by `ζ ^ k`.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, N.val = k * n.val :=
      exists_eq_mul_left_of_dvd (T.dvd_prod_of_mem _ hn)
    have h_move : s • y n = s • y N ^ k / y N ^ k * y n :=
      smul_root_eq_ratio_mul hs n.property (by rw [← pow_mul, ← hk, hy]) (hy n)
    have h_ratio : s • y n / y n = ζ ^ k := by simp [h_move, hs_root, mul_pow, hy_ne]
    show IsPrimitiveRoot (s • y n / y n) n.val
    simpa only [h_ratio] using hζ.pow (h_pos N) hk
  obtain ⟨g, hg, hgood⟩ :=
    isClosed_inertiaGroup.isCompact.inter_iInter_nonempty good h_closed h_finite
  exact ⟨⟨g, hg⟩, fun n hn ↦ ⟨π, y ⟨n, hn⟩, h.isUniformiser_iff.mpr hπ_val, hy ⟨n, hn⟩,
    Set.mem_iInter.mp hgood ⟨n, hn⟩⟩⟩

/-- A chosen generator of tame inertia at the place `A` above `w`, as an element of the inertia
group. Its defining property is `New.IsPlaceOver.exists_isPrimitiveRoot_tameGenerator_smul_div`. -/
noncomputable def tameGenerator : inertiaGroup Gal(Ω/K) A := h.exists_tameGenerator.choose

/-- For every `n` that is a unit at `A`, the tame generator multiplies some `n`-th root `y` of a
uniformiser `π` of `K` at `A` by a primitive `n`-th root of unity. -/
lemma exists_isPrimitiveRoot_tameGenerator_smul_div {n : ℕ} (hn : A.valuation n = 1) :
    ∃ (π : Kˣ) (y : Ω), IsUniformiser A π.val ∧ y ^ n = algebraMap K Ω π ∧
      IsPrimitiveRoot (h.tameGenerator • y / y) n :=
  h.exists_tameGenerator.choose_spec n hn

/-- The chosen element `New.IsPlaceOver.tameGenerator` is a tame generator of inertia at `A`. -/
lemma isTameGenerator_tameGenerator : IsTameGenerator h.tameGenerator :=
  fun _ hn ↦ h.exists_isPrimitiveRoot_tameGenerator_smul_div hn

/-- The structure of tame inertia at a place of a number field. Let `γ` be a tame generator at `A`,
and let `f` kill the elements of inertia near `1` and have `f g ^ n = 1` on inertia, with `n` prime
to `w`. For `s` in inertia, `f s` is a power of `f γ`, and conjugation by a `q`-Frobenius raises
`f s` to the power `q`. -/
lemma exists_eq_pow_and_apply_conj_eq_pow {γ : inertiaGroup Gal(Ω/K) A} (hγ : IsTameGenerator γ)
    {P : Type*} [Monoid P] (f : Gal(Ω/K) →* P)
    (hf : ∀ᶠ g : Gal(Ω/K) in nhds 1, g ∈ inertiaGroup Gal(Ω/K) A → f g = 1)
    {n : ℕ} (hn : A.valuation n = 1) (hP : ∀ g ∈ inertiaGroup Gal(Ω/K) A, f g ^ n = 1)
    (s : inertiaGroup Gal(Ω/K) A) :
    -- (a) `f s` is a power of `f γ`
    (∃ i : ℕ, f s = f γ ^ i) ∧
    -- (b) conjugation by a `q`-Frobenius raises `f s` to the power `q`
    ∀ (q : ℕ) (φ : Gal(Ω/K)), IsFrob A q φ → f (φ * s * φ⁻¹) = f s ^ q := by
  -- Apply the local theorem `IsLocalGalois.tame_inertia` to the decomposition group `D` and its
  -- fixed field, with the root `y ^ n = π` on which the tame generator is primitive.
  obtain ⟨π, y, hπ, hy, h_prim⟩ := hγ n hn
  let D := decompGroup Gal(Ω/K) A
  let f' : inertiaGroup D A →* P := (f.domRestrict D).domRestrict _
  let incl (g : inertiaGroup Gal(Ω/K) A) : inertiaGroup D A := ⟨⟨g, g.property.left⟩, g.property⟩
  have h_open : IsOpen (SetLike.coe f'.ker) := isOpen_of_mem_nhds _ <|
    mem_of_superset (continuous_subtype_val.subtype_val.tendsto 1 hf) fun g hg ↦ hg g.property
  obtain ⟨h_galois, -, h_unif⟩ := h.isLocalGalois_and_residueCard_eq_and_isUniformiser Gal(Ω/K)
  have h_local : ∀ s : inertiaGroup D A,
      (IsPrimitiveRoot (s • y / y) n → ∀ g : inertiaGroup D A, ∃ i : ℕ, f' g = f' s ^ i) ∧
      ∀ (q : ℕ) (φ : D), IsFrob A q φ →
        ∃ h_mem : φ * s * φ⁻¹ ∈ inertiaGroup D A, f' ⟨φ * s * φ⁻¹, h_mem⟩ = f' s ^ q :=
    (h_galois.tame_inertia (h_unif hπ) hn hy f' h_open fun g ↦ hP _ g.property).right
  obtain ⟨h_gen, -⟩ := h_local (incl γ)
  obtain ⟨-, h_frob⟩ := h_local (incl s)
  refine ⟨h_gen h_prim (incl s), fun q φ hφ ↦ ?_⟩
  obtain ⟨h_mem, h_conj⟩ := h_frob q ⟨φ, hφ.left⟩ hφ
  exact h_conj

/-- The structure of tame inertia for the chosen tame generator. Let `f` kill the elements of
inertia near `1` and have `f g ^ n = 1` on inertia, with `n` prime to `w`. For `s` in inertia,
`f s` is a power of the image of the tame generator, and conjugation by a `q`-Frobenius raises
`f s` to the power `q`. -/
lemma tame_inertia {P : Type*} [Monoid P] (f : Gal(Ω/K) →* P)
    (hf : ∀ᶠ g : Gal(Ω/K) in nhds 1, g ∈ inertiaGroup Gal(Ω/K) A → f g = 1)
    {n : ℕ} (hn : A.valuation n = 1) (hP : ∀ g ∈ inertiaGroup Gal(Ω/K) A, f g ^ n = 1)
    (s : inertiaGroup Gal(Ω/K) A) :
    -- (a) `f s` is a power of `f` at the tame generator
    (∃ i : ℕ, f s = f h.tameGenerator ^ i) ∧
    -- (b) conjugation by a `q`-Frobenius raises `f s` to the power `q`
    ∀ (q : ℕ) (φ : Gal(Ω/K)), IsFrob A q φ → f (φ * s * φ⁻¹) = f s ^ q :=
  h.exists_eq_pow_and_apply_conj_eq_pow h.isTameGenerator_tameGenerator f hf hn hP s

/-- For `A` over `w`: `u` in `K_wˣ` is a unit of the valuation ring whose local Artin symbol is the
tame generator and whose residue generates the units of the residue field. -/
structure IsTameUnit (u : (LocField w)ˣ) : Prop where
  /-- `u` lies in the unit group of the valuation ring. -/
  mem_unitGroup : u ∈ (LocInt w).unitGroup
  /-- The symbol of `u` is the class of the tame generator. -/
  localArtin_eq : localArtin Gal(Ω/K) A w u =
    (⟨h.tameGenerator, h.tameGenerator.property.left⟩ : decompGroup Gal(Ω/K) A)
  /-- Every unit of the residue field is a power of the residue of `u`. -/
  mem_zpowers_residue (z : (ResField w)ˣ) :
    z ∈ zpowers ((LocInt w).unitGroupToResidueFieldUnits ⟨u, mem_unitGroup⟩)
  /-- `u` has valuation `1`. -/
  valuation_eq_one : Valued.v u.val = 1

/-- Let the valuation subring `A` of `Ω` lie over the finite place `w` of the number field `K`, with
`Ω / K` Galois. Then some unit `u` of `K_w` lies in the valuation ring, has local Artin symbol equal
to the tame generator at `A`, and has a residue that generates the multiplicative group of the
residue field (`New.IsPlaceOver.IsTameUnit`).

A consequence of local reciprocity (units correspond to inertia). Weaker than the tame symbol
formula (Serre, Local Fields, XIV), which determines the residue of such a unit; here it is only
shown to be a generator. -/
lemma exists_isTameUnit : ∃ u : (LocField w)ˣ, h.IsTameUnit u := by
  -- Take a unit `u` with symbol `γ = h.tameGenerator` and a root `y ^ (q - 1) = π`. By
  -- `valuation_sub_lt_one_iff_of_localArtin_eq`, `u ^ d ≡ 1` forces `(γ y / y) ^ d = 1`, so the
  -- residue of `u` has order at least `q - 1`.
  have hq : A.valuation (w.q - 1 : ℕ) = 1 := by
    simp [map_sub_eq_of_lt_right, h.valuation_q_lt_one]
  let γ : decompGroup Gal(Ω/K) A := ⟨h.tameGenerator, h.tameGenerator.property.left⟩
  obtain ⟨u, hu : v u.val = 1, hu_art : localArtin Gal(Ω/K) A w u = γ⟩ :=
    h.exists_localArtin_eq_of_mem_inertiaGroup h.tameGenerator.property
  obtain ⟨π, y, hπ, hy, h_prim : IsPrimitiveRoot (γ • y / y) (w.q - 1)⟩ :=
    h.exists_isPrimitiveRoot_tameGenerator_smul_div hq
  have hu_mem : u ∈ (LocInt w).unitGroup := (mem_unitGroup_iff ..).mpr hu
  let r : (ResField w)ˣ := (LocInt w).unitGroupToResidueFieldUnits ⟨u, hu_mem⟩
  let d : ℕ := orderOf r
  have u_cong : v ((u ^ d).val - algebraMap K (LocField w) 1) < 1 :=
    residue_eq_iff_valuation_sub_lt_one.mp (val_inj.mpr (pow_orderOf_eq_one r))
  have root_cong : A.valuation ((γ • y / y) ^ d - 1) < 1 := by
    rw [← inertia_pow_smul_div (s := γ) h.tameGenerator.property hq hy d,
      ← map_one (algebraMap K Ω)]
    exact (h.valuation_sub_lt_one_iff_of_localArtin_eq hπ (s := γ ^ d) (u := u ^ d)
      (by simp [hu]) (by simp [hu_art]) hy).mp u_cong
  -- Roots of unity of order dividing `q - 1` are distinct modulo the maximal ideal.
  have root_eq : (γ • y / y) ^ d = 1 := eq_of_val_sub_lt_one hq
    (by rw [pow_right_comm, h_prim.pow_eq_one, one_pow]) (one_pow _) root_cong
  have card_le : Nat.card (ResField w)ˣ ≤ Nat.card (zpowers r) := by
    rw [Nat.card_zpowers, Nat.card_units, card_ResField]
    exact Nat.le_of_dvd (orderOf_pos r) (h_prim.dvd_of_pow_eq_one d root_eq)
  exact ⟨u, hu_mem, hu_art, (eq_top_iff' _).mp (eq_top_of_le_card _ card_le), hu⟩

end IsPlaceOver

end New

end
