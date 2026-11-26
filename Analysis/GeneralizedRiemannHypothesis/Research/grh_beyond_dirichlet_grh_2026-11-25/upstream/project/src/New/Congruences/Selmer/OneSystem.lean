import Lib.General.Algebra.SharpMinors
import New.Congruences.Selmer.SelmerData

/-!
# The universal twist and one system of equations for all twists

For homomorphisms `h_j : G → ℤ / q` let `ψ_X(g) = ∏ (1 + X_j) ^ (h_j g)`, and let `Sel(x)` be the
Selmer module of the twist of a representation by the value `ψ_x` at a point `x`. The members of all
`Sel(x)` are functions on one finite quotient of the Galois group, and the cocycle rule and the
other conditions are linear equations over `O[X]` for their values.

* `New.Selmer.universalChar`, `New.Selmer.IsTiedPrimes.universalChar_frob`,
  `New.Selmer.IsTiedPrimes.universalChar_tame_gen`: the polynomial `ψ_X` and its values at the
  auxiliary primes.
* `New.Selmer.finite_selmerModule`: for finite `S` and `ρ` locally constant modulo `ℓ ^ M`, the
  Selmer module with coefficients in a finite `O / a`, `a ∣ ℓ ^ M`, is finite.
* `New.Selmer.exists_matrix_selmerAtPoint_equiv`: there is one matrix `A` over `O[X]` such that each
  `Sel(x)` is isomorphic to the kernel of `A(x)` on a power of `O' / ℓ ^ M`.
* `New.Selmer.exists_isLeast_length_selmerAtPoint`, `New.Selmer.exists_sharp_polynomial`: the
  valuations of a set of polynomials (in the proof, maximal minors) bound the lengths of `Sel(x)` at
  all points over discrete valuation rings of characteristic zero, and one is sharp at a given
  point.

Notions from other files:
* `New.selmerModule ρ S L B`: the locally constant cocycles for `ρ` with values in `B ^ n` that are
  unramified outside `S` and obey the relations `L`.
* `New.obeying`, `New.mapRel`: a relation is a finitely supported `f : Γ →₀ Matrix n n O`; a
  function `c` obeys it if `∑ γ, f γ • c γ = 0`, and `mapRel e f` applies `e` to all entries of `f`.
* `New.Selmer.IsTiedPrimes ℓ S₀ V W N P₀ J d`: a finite set `J` of primes that, with their
  conjugates, avoid `S₀`, and a first prime `P₀ ∈ J`. At `v ∈ J`, `(d v).1` holds a place, a
  Frobenius element `φ`, a tame generator `γ` and a character to `ℤ / ℓ ^ N`, and `(d v).2 i ∈ O` is
  the slope for the index `i : ι`. The Frobenius element of `P₀` lies in `W`, and where the slope
  for `i` is not zero, the condition `V i` holds at `φ` and at `(c φ c)⁻¹` for the complex
  conjugation `c`.
* `New.QuotSpan a`, `New.Selmer.reduceModPow ℓ M ρ`: the ring `O / a`, and `ρ` modulo `ℓ ^ M`.

## Relation to the literature

See `New.Congruences.Selmer.TwistingTheorem` for related work.
-/

noncomputable section

namespace New.Selmer

open IsDiscreteValuationRing Module MvPolynomial Matrix.Module

/-- A matrix over `O` acts on `(O / a) ^ n` as its reduction modulo `a` does; `QuotSpan a` is the
ring `O / a`. -/
lemma map_mk_smul {n O : Type} [Fintype n] [DecidableEq n] [CommRing O] {a : O}
    (A : Matrix n n O) (u : n → QuotSpan a) :
    A.map (Ideal.Quotient.mk (Ideal.span {a})) • u = A • u := by
  ext j
  simp [Algebra.smul_def]

section UniversalTwist

open Finset

variable {G R σ : Type} [Monoid G] [CommRing R] [Fintype σ] {q : ℕ}
  (h : σ → G →* Multiplicative (ZMod q))

/-- The polynomial `ψ_X(g) = ∏ (1 + X_j) ^ (h_j g)` attached to homomorphisms `h_j : G → ℤ / q`;
for `q ≠ 0` the exponents are taken in the interval `[0, q)`. -/
def universalChar (g : G) : MvPolynomial σ R :=
  ∏ j : σ, (1 + X j) ^ (h j g).toAdd.val

lemma aeval_universalChar {A : Type*} [CommRing A] [Algebra R A] (x : σ → A) (g : G) :
    aeval x (universalChar (R := R) h g) = ∏ j : σ, (1 + x j) ^ (h j g).toAdd.val := by
  simp [universalChar]

lemma eval_universalChar (x : σ → R) (g : G) :
    eval x (universalChar h g) = ∏ j : σ, (1 + x j) ^ (h j g).toAdd.val := by
  simp [universalChar]

/-- At the point `(ζ_j - 1)_j` for `q`-th roots of unity `ζ_j`, the polynomial
`universalChar h g = ∏ (1 + X_j) ^ (h_j g)` takes the value at `g` of the character
`pointChar h ζ hζ = ∏ ζ_j ^ h_j`. -/
lemma aeval_sub_one_universalChar [NeZero q] {A : Type} [CommRing A] [Algebra R A] {ζ : σ → A}
    (hζ : ∀ j : σ, ζ j ^ q = 1) (g : G) :
    aeval (fun j : σ ↦ ζ j - 1) (universalChar (R := R) h g) = pointChar h ζ hζ g := by
  simp [aeval_universalChar]

variable {ℓ : ℕ} [ThePrime ℓ] {E ι O : Type} [Field E]
  [EmbeddedNumberField E] [NumberField.IsCMField E] [CommRing O]
  {V : ι → Gal(Ω/E) → Prop} {W : Set Gal(Ω/E)} {N : ℕ} {P₀ : FinPlace E}
  {S₀ J : Finset (FinPlace E)} {d : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)}

open scoped Classical in
/-- Let `ℓ` be prime and `N ≠ 0`. Let `J` be a finite set of primes of the CM field `E` with data
`d` as in `IsTiedPrimes`: each `w ∈ J` carries an anticyclotomic character `h_w = (d w).1.character`
of `Gal(Ω/E)` to `ℤ / ℓ ^ N`. Let `ψ_X = ∏ (1 + X_w) ^ h_w` be the polynomial over a commutative
ring `R` in variables `X_w`, `w ∈ J`. If `h_v(g) = 1 ∈ ℤ / ℓ ^ N` and the other `h_w` vanish at `g`,
then `ψ_X` is `1 + X_v` at `idOrConjInv b g`, that is, at `g` and at `(c g c)⁻¹` for the complex
conjugation `c`. -/
lemma IsTiedPrimes.universalChar_eq_one_add_X (hJ : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hN : N ≠ 0)
    {g : Gal(Ω/E)} (v : J)
    (hg : ∀ w ∈ J, (d w).1.character g = if w = v then Multiplicative.ofAdd 1 else 1) (b : Bool) :
    universalChar (R := R) (fun j : J ↦ (d j).1.character) (idOrConjInv b g) = 1 + X v := by
  have : Fact (1 < ℓ ^ N) := ⟨Nat.one_lt_pow hN (Fact.out : ℓ.Prime).one_lt⟩
  -- The characters are anticyclotomic, so they take the same value at `g` and at `(c g c)⁻¹`.
  have h_val (w : J) : (d w).1.character (idOrConjInv b g) = (d w).1.character g :=
    (hJ.isAuxPrimeDataAt w w.property).apply_idOrConjInv b g
  rw [universalChar, prod_eq_single_of_mem v (mem_univ v)]
  · simp [h_val, hg v v.property, ZMod.val_one]
  · intro w _ hw
    simp [h_val, hg w w.property, Subtype.coe_ne_coe.2 hw]

/-- Let `ℓ` be prime and `N ≠ 0`. Let `J` be a finite set of primes of the CM field `E` with data
`d` as in `IsTiedPrimes`: each `w ∈ J` carries an anticyclotomic character
`h_w = (d w).1.character` to `ℤ / ℓ ^ N`, and at the Frobenius element `φ = (d v).1.frob` of a prime
`v ∈ J` other than the distinguished prime `P₀ ∈ J`, the character `h_{P₀}` is `1` and the other
`h_w` vanish; `S₀`, `V`, `W` and the slopes play no part. Then at `φ` and at `(c φ c)⁻¹` for the
complex conjugation `c`, the two values of `idOrConjInv b φ`, the polynomial
`ψ_X = ∏ (1 + X_w) ^ h_w` over `R` in variables `X_w`, `w ∈ J`, is `1 + X_{P₀}`. -/
lemma IsTiedPrimes.universalChar_frob (hJ : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hN : N ≠ 0)
    {v : FinPlace E} (hv : v ∈ J) (hv_ne : v ≠ P₀) (b : Bool) :
    universalChar (R := R) (fun j : J ↦ (d j).1.character) (idOrConjInv b (d v).1.frob) =
      1 + X ⟨P₀, hJ.first_mem⟩ :=
  hJ.universalChar_eq_one_add_X hN ⟨P₀, hJ.first_mem⟩ (hJ.char_frob_eq_ite v hv hv_ne) b

/-- Let `ℓ` be prime and `N ≠ 0`. Let `J` be a finite set of primes of the CM field `E` with data
`d` as in `IsTiedPrimes`: each `w ∈ J` carries an anticyclotomic character
`h_w = (d w).1.character` to `ℤ / ℓ ^ N` and a tame generator of inertia; `P₀`, `S₀`, `V`, `W` and
the slopes do not enter the claim. Let `γ = (d v).1.tameGenerator` be the tame generator at a prime
`v` of `J`. At `γ` and at `(c γ c)⁻¹` for the complex conjugation `c`, the two values of
`idOrConjInv b γ`, the polynomial `ψ_X = ∏ (1 + X_w) ^ h_w` over `R` in variables `X_w`, `w ∈ J`, is
`1 + X_v`. -/
lemma IsTiedPrimes.universalChar_tame_gen (hJ : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hN : N ≠ 0)
    (v : J) (b : Bool) :
    universalChar (R := R) (fun j : J ↦ (d j).1.character) (idOrConjInv b (d v).1.tameGenerator) =
      1 + X v :=
  hJ.universalChar_eq_one_add_X hN v (hJ.character_tameGenerator_eq_ite v.property) b

end UniversalTwist

section Finite

variable {E n O : Type} [Field E] [EmbeddedNumberField E] [Fintype n] [DecidableEq n] [CommRing O]
  {ℓ M : ℕ} {ρ : Gal(Ω/E) →* Matrix n n O} {S : Set (FinPlace E)}

/-- Let `E` be a number field embedded in the algebraic closure `Ω` of `ℚ`, let `ρ` be a
representation of `Gal(Ω/E)` by matrices over `O` that is locally constant modulo `ℓ ^ M`, and let
`S` be a finite set of primes of `E`. Let `a ∣ ℓ ^ M` with `QuotSpan a = O / a` finite, and let `L`
be a set of relations `∑ γ, f γ • c γ = 0` on functions `c`. Then the Selmer module of `ρ` with
coefficients in `O / a` is finite. -/
theorem finite_selmerModule {a : O} [Finite (QuotSpan a)] (ha : a ∣ ℓ ^ M)
    (hρ : IsLocallyConstant (reduceModPow ℓ M ρ)) (hS : S.Finite)
    (L : Set (Gal(Ω/E) →₀ Matrix n n O)) : Finite (selmerModule ρ S L (QuotSpan a)) := by
  let : TopologicalSpace (QuotSpan a) := ⊥
  have : DiscreteTopology (QuotSpan a) := ⟨rfl⟩
  -- The ring `O / ℓ ^ M` acts on `O / a`, so `ρ` acts through its reduction, hence continuously.
  let : Module (QuotSpan (ℓ ^ M : O)) (QuotSpan a) :=
    Module.IsTorsionBy.module (smul_quot_eq_zero_of_dvd ha)
  have h_cont (b : n → QuotSpan a) : IsLocallyConstant fun g : Gal(Ω/E) ↦ ρ g • b :=
    hρ.comp fun m : Matrix n n (QuotSpan (ℓ ^ M : O)) ↦ m • b
  let V : DiscreteModule O Gal(Ω/E) := .of (actionRep O (n → QuotSpan a) ρ)
    (continuous_prod_of_discrete_right.2 fun b ↦ (h_cont b).continuous)
  -- The Selmer module lies in the finite set of cocycles in `V` unramified outside `S`.
  change (selmerModule ρ S L (QuotSpan a) : Set (Gal(Ω/E) → n → QuotSpan a)).Finite
  refine (finite_cocycles_unramified_outside V hS).subset fun z hz ↦ ?_
  obtain ⟨h_cocycle, h_unr, -, h_const⟩ := mem_selmerModule_iff.1 hz
  exact ⟨⟨h_const.continuous, h_cocycle⟩, fun v hv A hA g hg ↦ h_unr g ⟨v, hv, A, hA, hg⟩⟩

end Finite

section Relations

variable {Γ 𝒢 n Λ O B : Type} [Fintype 𝒢] [Fintype n] [DecidableEq n] [CommRing Λ] [CommRing O]
  [AddCommGroup B] [Module O B]

lemma mapRel_single (ev : Λ →+* O) (g : Γ) (m : Matrix n n Λ) :
    mapRel ev (.single g m) = .single g (m.map ev) := Finsupp.mapRange_single

/-- Mapping the entries of a relation by `e` and then by `ev` is mapping them by `ev ∘ e`. -/
lemma mapRel_mapRel {Λ' : Type} [CommRing Λ'] (e : Λ' →+* Λ) (ev : Λ →+* O)
    (f : Γ →₀ Matrix n n Λ') : mapRel ev (mapRel e f) = mapRel (ev.comp e) f :=
  Finsupp.ext fun _ ↦ Matrix.map_map

/-- Applying `ev` to all matrix entries carries the relations that express the cocycle identity for
`ρ` onto those that express it for `g ↦ ev (ρ g)`. -/
lemma mapRel_image_cocycleRelations [Mul Γ] (ev : Λ →+* O) (ρ : Γ → Matrix n n Λ) :
    mapRel ev '' cocycleRelations ρ = cocycleRelations fun g : Γ ↦ (ρ g).map ev := by
  have h_rel (g g' : Γ) : mapRel ev (.single (g * g') 1 - .single g 1 - .single g' (ρ g)) =
      .single (g * g') 1 - .single g 1 - .single g' ((ρ g).map ev) := by
    simp [mapRel, Finsupp.mapRange_sub']
  simp only [Set.ext_iff, Set.mem_image, cocycleRelations, Set.mem_ofPred_eq]
  grind

/-- The linear equations that a set `R` of relations imposes on the functions on `Γ` that factor
through `π : Γ → 𝒢`. The unknowns are the coordinates of the values on `𝒢`, and there is one
equation for each relation and each coordinate. -/
def relationMatrix (π : Γ → 𝒢) (R : Set (Γ →₀ Matrix n n Λ)) : Matrix (R × n) (𝒢 × n) Λ :=
  .of fun (f, i) (c, j) ↦ f.1.mapDomain π c i j

lemma relationMatrix_apply {Γ 𝒢 n Λ : Type} [CommRing Λ] (π : Γ → 𝒢)
    (R : Set (Γ →₀ Matrix n n Λ)) (f : R) (i : n) (c : 𝒢 × n) :
    relationMatrix π R (f, i) c = (f : Γ →₀ Matrix n n Λ).mapDomain π c.1 i c.2 := rfl

/-- For `π : Γ → 𝒢`, let `f.mapDomain π` be `f` pushed forward along `π`, adding the matrices over
each fibre. Then `∑ c, ev (f.mapDomain π c.1 i c.2) • w c` is coordinate `i` of
`relEval B (mapRel ev f)` applied to `g ↦ w (π g, ·)`, that is, of `∑ g, ev (f g) • w (π g, ·)`. -/
lemma sum_mapDomain_smul_eq_relEval (π : Γ → 𝒢) (ev : Λ →+* O) (w : 𝒢 × n → B)
    (f : Γ →₀ Matrix n n Λ) (i : n) :
    ∑ c : 𝒢 × n, ev (f.mapDomain π c.1 i c.2) • w c =
      relEval B (mapRel ev f) (fun (g : Γ) (j : n) ↦ w (π g, j)) i := by
  induction f using Finsupp.induction_linear with
  | zero => simp [mapRel]
  | add f f' hf hf' =>
    simp [mapRel, Finsupp.mapRange_add', Finsupp.mapDomain_add, add_smul,
      Finset.sum_add_distrib, hf, hf']
  | single g m =>
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (π g)]
    · simp [mapRel]
    · simp +contextual
    · simp

/-- A vector `w` solves the linear system `relationMatrix π R`, with entries mapped by `ev`, if and
only if the function `g ↦ w (π g, ·)` obeys the relations of `R` mapped by `ev`. -/
lemma mem_matrixKernel_relationMatrix (π : Γ → 𝒢) (R : Set (Γ →₀ Matrix n n Λ)) (ev : Λ →+* O)
    (w : 𝒢 × n → B) :
    w ∈ matrixKernel ((relationMatrix π R).map ev) B ↔
      (fun (g : Γ) (i : n) ↦ w (π g, i)) ∈ obeying (mapRel ev '' R) B := by
  simp only [mem_matrixKernel, mem_obeying, Set.forall_mem_image, Prod.forall, Subtype.forall,
    funext_iff, ← sum_mapDomain_smul_eq_relEval, Matrix.map_apply, relationMatrix_apply,
    Pi.zero_apply]

end Relations

variable {E G n σ Λ O O' : Type} [Field E] [EmbeddedNumberField E] [Monoid G] [Fintype n]
  [DecidableEq n] [Fintype σ] [CommRing Λ] [CommRing O] [CommRing O'] {q : ℕ} {S : Set (FinPlace E)}

/-- Let `B` be an abelian group killed by `m ≠ 0`. An element of `B` that is killed by every
homomorphism `B → ℤ / m` is zero. -/
lemma eq_zero_of_forall_hom_zmod_eq_zero {B : Type} [AddCommGroup B] {m : ℕ} [NeZero m]
    (hm : ∀ b : B, m • b = 0) {b : B} (hb : ∀ χ : B →+ ZMod m, χ b = 0) : b = 0 := by
  refine QZ.eq_zero_of_forall_hom_eq_zero fun u ↦ ?_
  obtain ⟨χ, rfl⟩ := (QZ.bijective_ofZMod_comp hm).surjective u
  simp [hb]

/-- Finitely many locally constant functions on an open subgroup `G'` of `Gal(Ω/E)` are all constant
on some open normal subgroup `G''` of `Gal(Ω/E)` that is contained in `G'`. -/
lemma exists_openNormalSubgroup_forall_apply_eq_apply_one (G' : OpenSubgroup Gal(Ω/E)) {V : Type}
    {Y : Set (G'.toSubgroup → V)} (hY : Y.Finite) (hY_const : ∀ y ∈ Y, IsLocallyConstant y) :
    ∃ G'' : OpenNormalSubgroup Gal(Ω/E),
      ∀ g ∈ G'', ∃ hg : g ∈ G'.toSubgroup, ∀ y ∈ Y, y ⟨g, hg⟩ = y 1 := by
  have h_nhds : {u : G'.toSubgroup | ∀ y ∈ Y, y u = y 1} ∈ nhds 1 :=
    hY.eventually_all.2 fun y hy ↦ (hY_const y hy).eventually_eq 1
  obtain ⟨W, hW_sub, hW_open, hW_one⟩ :=
    mem_nhds_iff.1 (G'.isOpen.isOpenMap_subtype_val.image_mem_nhds h_nhds)
  obtain ⟨G'', hG''⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW_open hW_one
  refine ⟨G'', fun g hg ↦ ?_⟩
  obtain ⟨u, hu, rfl⟩ := hW_sub (hG'' hg)
  exact ⟨u.property, hu⟩

/-- Let `G'` be an open subgroup of `Gal(Ω/E)`, let `m ≠ 0` and let `S` be a finite set of primes of
the number field `E`. There is one open normal subgroup `G''` such that, for every abelian group `B`
killed by `m`, each locally constant `z : Gal(Ω/E) → B` that is additive on `G'` and vanishes on
`inertiaAbove Sᶜ`, the union of the inertia groups above the primes outside `S`, vanishes on
`G''`. -/
lemma exists_openNormalSubgroup_forall_eq_zero (G' : OpenSubgroup Gal(Ω/E)) (m : ℕ) [NeZero m]
    (hS : S.Finite) :
    ∃ G'' : OpenNormalSubgroup Gal(Ω/E),
      ∀ (B : Type) [AddCommGroup B], (∀ b : B, m • b = 0) → ∀ z : Gal(Ω/E) → B,
        IsLocallyConstant z →
        (∀ g ∈ G', ∀ g' ∈ G', z (g * g') = z g + z g') →
        (∀ g ∈ inertiaAbove Sᶜ, z g = 0) →
        ∀ g ∈ G'', z g = 0 := by
  -- The continuous homomorphisms `G' → ℤ / m` that are unramified outside the primes above `S`
  -- form a finite set `Y`.
  let : TopologicalSpace (ZMod m) := ⊥
  have : DiscreteTopology (ZMod m) := ⟨rfl⟩
  let H : Subgroup Gal(Ω/E) := G'.toSubgroup
  let V : DiscreteModule ℤ H := .of (.trivial ℤ H (ZMod m))
  let S' : Set (FinPlace (fixedFieldOf H)) := FinPlace.below E ⁻¹' S
  have hS' : S'.Finite := by
    simpa [S'] using
      tendsto_place_comap_cofinite (algebraMap E (fixedFieldOf H)) hS.compl_mem_cofinite
  let Y : Set (H → V) := {y ∈ Z1 V.ρ | ∀ w ∉ S', ∀ A : ClosurePlace, IsPlaceOver A w →
    ∀ g ∈ inertiaGroup H A, y g = 0}
  -- So they are all constant on an open normal subgroup `G''` of `Gal(Ω/E)`.
  obtain ⟨G'', hG''⟩ := exists_openNormalSubgroup_forall_apply_eq_apply_one G'
    (finite_cocycles_unramified_outside V hS' : Y.Finite)
    fun y ⟨⟨hy_cont, _⟩, _⟩ ↦ (IsLocallyConstant.iff_continuous y).2 hy_cont
  refine ⟨G'', fun B _ hm z hz_const hz_add hz_unr g hg ↦ ?_⟩
  have hz_one : z 1 = 0 := by simpa using hz_add 1 (one_mem G') 1 (one_mem G')
  -- The homomorphisms `χ : B → ℤ / m` separate the points of `B`, and `χ ∘ z` lies in `Y`.
  refine eq_zero_of_forall_hom_zmod_eq_zero hm fun χ ↦ ?_
  have h_cocycle : (fun u : H ↦ χ (z u)) ∈ Z1 V.ρ := by
    refine ⟨(hz_const.comp χ).continuous.comp continuous_subtype_val, fun u u' ↦ ?_⟩
    simp [V, hz_add u u.property u' u'.property]
  have h_mem : (fun u : H ↦ χ (z u)) ∈ Y := by
    refine ⟨h_cocycle, fun w hw A hA u hu ↦ ?_⟩
    have hz_zero : z u = 0 := hz_unr u ⟨w.below E, hw, A, hA.isPlaceOver_below, hu⟩
    simp [hz_zero]
  obtain ⟨hg_mem, h_const⟩ : ∃ hg : g ∈ H, ∀ y ∈ Y, y ⟨g, hg⟩ = y 1 := hG'' g hg
  have h_value : χ (z g) = χ (z 1) := h_const _ h_mem
  rw [h_value, hz_one, map_zero]

/-- Let `ρ` be a function from `Gal(Ω/E)` to matrices over a ring `Λ`, let `L` be a set of relations
`∑ γ, f γ • c γ = 0` with matrix coefficients over `Λ`, let `G'` be an open subgroup, let `m ≠ 0`
and let `S` be a finite set of primes of `E`. There is one matrix `A` over `Λ`, with columns indexed
by a finite type `k`, such that for every `ev : Λ → O'` and every `O'`-module `B` killed by `m`, if
`G'` acts trivially on `B ^ n` through `ev ρ`, the Selmer module of `ev ρ` in `B ^ n` is isomorphic
to the kernel of `ev A` on `B ^ k`. -/
theorem exists_matrix_selmerModule_equiv (ρ : Gal(Ω/E) → Matrix n n Λ)
    (G' : OpenSubgroup Gal(Ω/E)) (m : ℕ) [NeZero m] (hS : S.Finite)
    (L : Set (Gal(Ω/E) →₀ Matrix n n Λ)) :
    ∃ (r k : Type) (_ : Fintype k) (A : Matrix r k Λ),
      ∀ (O' : Type) [CommRing O'] (ev : Λ →+* O') (B : Type) [AddCommGroup B] [Module O' B],
        (∀ b : B, m • b = 0) →
        (∀ g ∈ G', ∀ b : n → B, (ρ g).map ev • b = b) →
        Nonempty (selmerModule (fun g : Gal(Ω/E) ↦ (ρ g).map ev) S (mapRel ev '' L) B ≃ₗ[O']
          matrixKernel (A.map ev) B) := by
  -- The cocycles factor through one finite quotient `𝒢` of `Gal(Ω/E)`, and `A` is the matrix of
  -- the equations that define the Selmer module among the functions on `𝒢`.
  obtain ⟨G'', h_zero⟩ := exists_openNormalSubgroup_forall_eq_zero G' m hS
  let H : Subgroup Gal(Ω/E) := G''.toSubgroup
  let 𝒢 : Type := Gal(Ω/E) ⧸ H
  let : Fintype 𝒢 := .ofFinite 𝒢
  let π : Gal(Ω/E) → 𝒢 := QuotientGroup.mk
  -- The equations: the cocycle rule, vanishing on inertia outside `S`, and the relations `L`.
  let R : Set (Gal(Ω/E) →₀ Matrix n n Λ) :=
    cocycleRelations ρ ∪ (fun g ↦ Finsupp.single g 1) '' inertiaAbove Sᶜ ∪ L
  refine ⟨R × n, 𝒢 × n, inferInstance, relationMatrix π R, fun O' _ ev B _ _ hm h_triv ↦ ?_⟩
  let Sel := selmerModule (fun g ↦ (ρ g).map ev) S (mapRel ev '' L) B
  let Ker : Submodule O' (𝒢 × n → B) := matrixKernel ((relationMatrix π R).map ev) B
  -- The members of `Sel` are additive on `G'`, so they vanish on `G''` and are functions on `𝒢`.
  have h_inv (z : Gal(Ω/E) → n → B) (hz : z ∈ Sel) (g : Gal(Ω/E)) (g'' : H) :
      z (g * g'') = z g := by
    obtain ⟨h_cocycle, h_unr, -, h_const⟩ := mem_selmerModule_iff.1 hz
    have h_add : ∀ u ∈ G', ∀ u' ∈ G', z (u * u') = z u + z u' :=
      fun u hu u' _ ↦ by rw [h_cocycle, h_triv u hu]
    have h_vanish : z g'' = 0 :=
      h_zero (n → B) (fun b ↦ funext fun i ↦ hm (b i)) z h_const h_add h_unr g'' g''.property
    rw [h_cocycle, h_vanish, smul_zero, add_zero]
  -- A function on `𝒢` is a vector `w` with coordinates in `B`; it gives a member of `Sel` if and
  -- only if it satisfies the equations.
  let pull : (𝒢 × n → B) →ₗ[O'] Gal(Ω/E) → n → B := .pi fun g ↦ .pi fun i ↦ .proj (π g, i)
  have h_rel : mapRel ev '' R = cocycleRelations (fun g ↦ (ρ g).map ev) ∪
      (fun g ↦ Finsupp.single g 1) '' inertiaAbove Sᶜ ∪ mapRel ev '' L := by
    simp [R, Set.image_union, mapRel_image_cocycleRelations, Set.image_image, mapRel_single]
  have h_mem (w : 𝒢 × n → B) : w ∈ Ker ↔ pull w ∈ Sel := by
    have h_const : IsLocallyConstant (pull w) :=
      (IsLocallyConstant.of_discrete w.curry).comp_continuous QuotientGroup.continuous_mk
    have h_Sel : pull w ∈ Sel ↔
        pull w ∈ obeying (mapRel ev '' R) B ∧ IsLocallyConstant (pull w) := by
      rw [h_rel]
      exact Submodule.mem_inf
    rw [h_Sel, and_iff_left h_const]
    exact mem_matrixKernel_relationMatrix π R ev w
  have h_inj : Function.Injective pull := fun w w' h_eq ↦ funext fun (c, i) ↦ by
    obtain ⟨g, rfl⟩ : ∃ g : Gal(Ω/E), π g = c := QuotientGroup.mk_surjective c
    exact congr_fun₂ h_eq g i
  have h_map : Ker.map pull = Sel := by
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun w hw ↦ (h_mem w).1 hw) fun z hz ↦ ?_
    have h_pull : pull (fun (c, i) ↦ z c.out i) = z := by
      funext g
      obtain ⟨g'', hg''⟩ : ∃ g'' : H, (π g).out = g * g'' := QuotientGroup.mk_out_eq_mul H g
      change z (π g).out = z g
      rw [hg'', h_inv z hz]
    exact ⟨_, (h_mem _).2 (by rwa [h_pull]), h_pull⟩
  exact ⟨((Submodule.equivMapOfInjective pull h_inj Ker).trans (.ofEq _ Sel h_map)).symm⟩

/-- The matrices `ψ_x(g) ρ(g)` over `O'`, where `ψ_x(g)` is the value of
`ψ_X(g) = universalChar h g` at the point `x` and `ρ(g)` is mapped by `e`. The function `ψ_x` need
not be multiplicative. -/
def pointTwist (h : σ → G →* Multiplicative (ZMod q)) (x : σ → O') (e : O →+* O')
    (ρ : G → Matrix n n O) (g : G) : Matrix n n O' :=
  eval x (universalChar h g) • (ρ g).map e

/-- Let `h j : G → ℤ / q` be finitely many homomorphisms, `ρ` a representation of `G` by matrices
over `O`, `e : O → O'` a ring homomorphism and `x` a point with coordinates `x j ∈ O'`. If all
`h j` vanish at `g` and `ρ g` is the identity modulo `ℓ ^ M`, then the twisted matrix
`pointTwist h x e ρ g = (∏ (1 + x_j) ^ (h_j g)) • e (ρ g)` acts trivially on `(O' / ℓ ^ M) ^ n`. -/
lemma pointTwist_smul_eq_self {ℓ M : ℕ} {h : σ → G →* Multiplicative (ZMod q)}
    {ρ : G →* Matrix n n O} {g : G} (hg_char : ∀ j : σ, h j g = 1)
    (hg_red : reduceModPow ℓ M ρ g = 1) (x : σ → O') (e : O →+* O')
    (b : n → QuotSpan (ℓ ^ M : O')) : pointTwist h x e ρ g • b = b := by
  have h_char : eval x (universalChar h g) = 1 := by simp [eval_universalChar, hg_char]
  -- The reduction of `e (ρ g)` is the image of that of `ρ g` under `O / ℓ ^ M → O' / ℓ ^ M`.
  let ē : QuotSpan (ℓ ^ M : O) →+* QuotSpan (ℓ ^ M : O') := Ideal.quotientMap _ e (by simp)
  have h_red : ((ρ g).map e).map (Ideal.Quotient.mk (.span {(ℓ ^ M : O')})) =
      (reduceModPow ℓ M ρ g).map ē := by
    ext i j
    simp [ē, reduceModPow]
  rw [pointTwist, h_char, one_smul, ← map_mk_smul, h_red, hg_red,
    Matrix.map_one ē ē.map_zero ē.map_one, one_smul]

/-- The module `Sel(x)`: the locally constant cocycles in `(O' / ℓ ^ M) ^ n` for the twist
`pointTwist h x e ρ` of `ρ` by `ψ_x` that are unramified outside `S` and obey the relations `L`,
with coefficients mapped by `e`. -/
def selmerAtPoint (ℓ M : ℕ) (h : σ → Gal(Ω/E) →* Multiplicative (ZMod q))
    (ρ : Gal(Ω/E) → Matrix n n O) (S : Set (FinPlace E)) (L : Set (Gal(Ω/E) →₀ Matrix n n O))
    (e : O →+* O') (x : σ → O') : Submodule O' (Gal(Ω/E) → n → QuotSpan (ℓ ^ M : O')) :=
  selmerModule (pointTwist h x e ρ) S (mapRel e '' L) (QuotSpan (ℓ ^ M : O'))

variable {ℓ M : ℕ} [NeZero ℓ] {h : σ → Gal(Ω/E) →* Multiplicative (ZMod q)}
  {ρ : Gal(Ω/E) →* Matrix n n O}

/-- Let `ℓ ≠ 0` and `q` be natural numbers, let `h j : Gal(Ω/E) → ℤ / q` be finitely many locally
constant homomorphisms, and let `ρ` be a representation of `Gal(Ω/E)` by matrices over `O` that is
locally constant modulo `ℓ ^ M`. Let `S` be a finite set of finite places of `E`. There is a matrix
`A` over `MvPolynomial σ O`, with finitely many columns and possibly infinitely many rows, such that
`Sel(x)` is isomorphic to the kernel of `A` evaluated at `x` on a power of `O' / ℓ ^ M`. This holds
for all `e : O → O'` and all points `x : σ → O'`. -/
theorem exists_matrix_selmerAtPoint_equiv (h_char_const : ∀ j : σ, IsLocallyConstant (h j))
    (hρ : IsLocallyConstant (reduceModPow ℓ M ρ)) (hS : S.Finite)
    (L : Set (Gal(Ω/E) →₀ Matrix n n O)) :
    ∃ (r k : Type) (_ : Fintype k) (A : Matrix r k (MvPolynomial σ O)),
      ∀ (O' : Type) [CommRing O'] (e : O →+* O') (x : σ → O'),
        Nonempty (selmerAtPoint ℓ M h ρ S L e x ≃ₗ[O']
          matrixKernel (A.map (eval₂Hom e x)) (QuotSpan (ℓ ^ M : O'))) := by
  -- On the open subgroup `G'` the characters `h j` are trivial, and so is `ρ` modulo `ℓ ^ M`.
  let G' : OpenSubgroup Gal(Ω/E) := ⟨(⨅ j : σ, (h j).ker) ⊓ (reduceModPow ℓ M ρ).ker, by
    change IsOpen (((⨅ j : σ, (h j).ker : Subgroup Gal(Ω/E)) : Set Gal(Ω/E)) ∩ _)
    rw [Subgroup.coe_iInf]
    exact (isOpen_iInter_of_finite fun j ↦ (h_char_const j).isOpen_fiber 1).inter
      (hρ.isOpen_fiber 1)⟩
  let ρX (g : Gal(Ω/E)) : Matrix n n (MvPolynomial σ O) := universalChar (R := O) h g • (ρ g).map C
  obtain ⟨r, k, _, A, hA⟩ := exists_matrix_selmerModule_equiv ρX G' (ℓ ^ M) hS (mapRel C '' L)
  refine ⟨r, k, inferInstance, A, fun O' _ e x ↦ ?_⟩
  -- At `X = x` the matrices `ρX g` and the relations are those of `Sel(x)`.
  have h_twist (g : Gal(Ω/E)) : (ρX g).map (eval₂Hom e x) = pointTwist h x e ρ g := by
    ext i j
    simp [ρX, pointTwist, universalChar]
  rw [selmerAtPoint, ← funext h_twist,
    show mapRel e '' L = mapRel (eval₂Hom e x) '' (mapRel C '' L) by
      simp [Set.image_image, mapRel_mapRel]]
  refine hA O' (eval₂Hom e x) (QuotSpan (ℓ ^ M : O')) (nsmul_quot_eq_zero dvd_rfl) fun g hg b ↦ ?_
  obtain ⟨hg_char, hg_red⟩ := Subgroup.mem_inf.1 hg
  rw [h_twist, pointTwist_smul_eq_self (Subgroup.mem_iInf.1 hg_char) (MonoidHom.mem_ker.1 hg_red)]

/-- Let `ℓ ≠ 0`, let the homomorphisms `h j : Gal(Ω/E) → ℤ / q` and the representation `ρ` over `O`,
taken modulo `ℓ ^ M`, be locally constant, let `S` be a finite set of primes of `E` and let `L` be
any set of relations `∑ γ, f γ • c γ = 0` on cocycles `c`. There is a set `𝓜` of polynomials over
`O` such that, at every point `x` over a discrete valuation ring `O'` of characteristic zero, the
length of `Sel(x)` is the least valuation of a value `P(x)`, `P ∈ 𝓜`. -/
theorem exists_isLeast_length_selmerAtPoint (h_char_const : ∀ j : σ, IsLocallyConstant (h j))
    (hρ : IsLocallyConstant (reduceModPow ℓ M ρ)) (hS : S.Finite)
    (L : Set (Gal(Ω/E) →₀ Matrix n n O)) :
    ∃ 𝓜 : Set (MvPolynomial σ O),
      ∀ (O' : Type) [CommRing O'] [DVR O'] [CharZero O'] (e : O →+* O') (x : σ → O'),
        IsLeast ((fun P : MvPolynomial σ O ↦ addVal O' (eval₂ e x P)) '' 𝓜)
          (length O' (selmerAtPoint ℓ M h ρ S L e x)) := by
  classical
  obtain ⟨r, k, _, A, hA⟩ := exists_matrix_selmerAtPoint_equiv h_char_const hρ hS L
  refine ⟨maximalMinors A (ℓ ^ M), fun O' _ _ _ e x ↦ ?_⟩
  obtain ⟨φ⟩ := hA O' e x
  rw [φ.length_eq, ← show eval₂Hom e x (ℓ ^ M : MvPolynomial σ O) = ℓ ^ M by simp]
  exact isLeast_length_matrixKernel A (ℓ ^ M) (eval₂Hom e x) (by simp [NeZero.ne])

/-- Let `ℓ ≠ 0`, let the homomorphisms `h j : Gal(Ω/E) → ℤ / q` and the representation `ρ` over `O`,
taken modulo `ℓ ^ M`, be locally constant, let `S` be a finite set of primes of `E` and let `L` be
any set of relations `∑ γ, f γ • c γ = 0` on cocycles `c`. Let `x₀` be a point over a discrete
valuation ring `O₀` of characteristic zero, with `e₀ : O → O₀`. There is a polynomial `P` over `O`
such that the valuation of `P(x₀)` is the length of `Sel(x₀)`, and the valuation of `P(x)` is at
least the length of `Sel(x)` at every point `x` over a ring of the same kind. -/
theorem exists_sharp_polynomial (h_char_const : ∀ j : σ, IsLocallyConstant (h j))
    (hρ : IsLocallyConstant (reduceModPow ℓ M ρ)) (hS : S.Finite)
    (L : Set (Gal(Ω/E) →₀ Matrix n n O)) {O₀ : Type} [CommRing O₀] [DVR O₀] [CharZero O₀]
    (e₀ : O →+* O₀) (x₀ : σ → O₀) :
    ∃ P : MvPolynomial σ O,
      addVal O₀ (eval₂ e₀ x₀ P) = length O₀ (selmerAtPoint ℓ M h ρ S L e₀ x₀) ∧
      ∀ (O' : Type) [CommRing O'] [DVR O'] [CharZero O'] (e : O →+* O') (x : σ → O'),
        length O' (selmerAtPoint ℓ M h ρ S L e x) ≤ addVal O' (eval₂ e x P) := by
  obtain ⟨𝓜, h_least⟩ := exists_isLeast_length_selmerAtPoint h_char_const hρ hS L
  obtain ⟨P, hP, h_sharp⟩ := (h_least O₀ e₀ x₀).1
  exact ⟨P, h_sharp, fun O' _ _ _ e x ↦ (h_least O' e x).2 (Set.mem_image_of_mem _ hP)⟩

end New.Selmer

end
