import Lib.Adelic.Adeles.LocalFactors
import Lib.ClassField.Global.AlbertBrauerHasseNoether
import Lib.Cyclotomic.Voronoi
import Lib.General.Algebra.FittingIdealsAndLengths

/-!
# Selmer modules, Tate twists, components of cocycles and places above a prime

`E` is a CM field and `Ω ⊇ E` is an algebraic closure of `ℚ`. The class `New.CMFieldWithRoot5040`
bundles these hypotheses on `E` with a primitive root of unity of order `5040`. Linear conditions on
functions `Gal(Ω/E) → n → B` are sets of relations, and `New.obeying R B` is the module of functions
that obey all of `R`. Over `ℚ` we define modules of cocycles for the inverses of characters
`Υ = cyc ^ e * ψ`, into which Selmer groups over cyclotomic fields decompose, and we prove basic
facts on places of `Ω` above a rational prime for use with Gauss sums.

## Main definitions and results

* `New.IsFromU1`: Galois characters that come from idele class characters through `x ↦ x / x̄`.
* `New.selmerModule`: locally constant cocycles, unramified outside `S`, that obey the relations
  `L`.
* `New.Selmer.tateTwist`, `New.Selmer.shaOdd`: the Tate twist `Λ(-e)` and a module of cocycles that
  for `e ≠ 0` describes the odd part of `Ш¹`.
* `New.cyclotomicPowDirichlet l e ψ`: the character of `Gal(Ω/ℚ)` with values in `Oˣ` that is the
  `e`-th power of the `l`-adic cyclotomic character times the Dirichlet character `ψ` modulo `N`.
  The latter is read through the action on `N`-th roots of unity.
* `New.OddPart.component l e ψ ν`: the component for `Υ = cyc ^ e * ψ`, with values in `O / l ^ ν`.

Notions from other files:
* `New.cyclotomicChar`, `New.cyclotomicCharIn Λ`: the `ℓ`-adic cyclotomic character `cyc`, with
  values in `ℤ_[ℓ]ˣ` and in `Λˣ`.
* `New.cycloGalGroup`: The subgroup of Gal(ℚ̄/ℚ) fixing all N-th roots of unity: the absolute Galois
  group of ℚ(ζ_N).
* `New.IsPlaceOver`: The valuation subring A of Ω lies over the prime w of E: an integer of E is in
  the maximal ideal of A exactly when it lies in w.
* `Set.conjClosure`: The set S ∪ S̄ of the finite places in S and their complex conjugates.

## Relation to the literature

Known; see `Lib.Cyclotomic.OddSha`, `Lib.ClassField.Global.CMSplittingCharacters`,
`Lib.Cyclotomic.Kolyvagin.ReciprocityComponentBounds`,
`Lib.ClassField.GaloisCohomology.KummerCyclicClasses` and `Lib.ClassField.Places.LocalFields` for
sources.
-/

noncomputable section

/-!
## Selmer modules, Tate twists and the odd part of Ш

* `New.cmConj`, `New.conjGal`: a chosen complex conjugation `c` and the map `g ↦ c g c`.
-/

namespace New

variable {ℓ : ℕ} [Fact ℓ.Prime]
  (E : Type) [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E] {C : Type*} [CommMonoid C]

/-- `E` is a CM number field with an embedding into the algebraic closure `Ω` of `ℚ`, and it
contains a primitive root of unity of order `7! = 5040` (`New.HasPrimitiveRoot5040`). -/
class CMFieldWithRoot5040 (E : Type*) [Field E] extends EmbeddedNumberField E,
  NumberField.IsCMField E, HasPrimitiveRoot5040 E

/-! ### Valuation, places and complex conjugation -/

/-- The valuation −log_ℓ|x| in [0, ∞], normalised by v(ℓ) = 1; it is ∞ at 0, and 0 for |x| ≥ 1. -/
def ellVal (x : PadicAlgCl ℓ) : ENNReal := if ‖x‖ = 0 then ⊤ else ENNReal.ofReal (-Real.logb ℓ ‖x‖)

/-- A chosen complex conjugation `c` in Gal(Ω/ℚ). -/
def cmConj : Gal(Ω/ℚ) := (exists_isComplexConj Gal(Ω/ℚ) Rat.isReal_infinitePlace).choose

/-- Here `Ω` is the fixed algebraic closure of ℚ into which `E` is embedded, and `cmConj` is the
chosen element of Gal(Ω/ℚ). The lemma says `cmConj` is a complex conjugation: for some embedding
`j : Ω → ℂ`, `j (cmConj x)` is the complex conjugate of `j x` for all `x`. -/
lemma isComplexConj_cmConj : IsComplexConj cmConj :=
  (exists_isComplexConj Gal(Ω/ℚ) Rat.isReal_infinitePlace).choose_spec

/-- For a natural number N, the set of finite places of E whose prime ideal contains N. -/
def placesDividing (N : ℕ) : Set (FinPlace E) := {v : FinPlace E | ↑N ∈ v.asIdeal}

/-- Only finitely many places of `E` divide the prime `ℓ`. -/
instance : Fintype (placesDividing E ℓ) := (finite_natCast_mem ℓ).fintype

variable {E} {G O O' n : Type _} [CommRing O] [CommRing O'] [Fintype n] [DecidableEq n] [Monoid G]

/-- The chosen complex conjugation `cmConj` of `Ω` is an involution. -/
@[simp]
lemma cmConj_cmConj (x : Ω) : cmConj (cmConj x) = x := by
  rw [← AlgEquiv.mul_apply, isComplexConj_cmConj.mul_self, AlgEquiv.one_apply]

/-- On the CM field `E ⊆ Ω`, the chosen complex conjugation `cmConj` of `Ω` restricts to the complex
conjugation `star` of `E`. -/
@[simp]
lemma cmConj_algebraMap (x : E) : cmConj (algebraMap E Ω x) = algebraMap E Ω (star x) := by
  -- Compare both sides under a complex embedding `j` that turns `cmConj` into complex conjugation.
  obtain ⟨j, hj⟩ : ∃ j : Ω →+* ℂ, ∀ y : Ω, j (cmConj y) = star (j y) := isComplexConj_cmConj
  have h_star : j (algebraMap E Ω (star x)) = star (j (algebraMap E Ω x)) :=
    map_star_complex (j.comp (algebraMap E Ω)) x
  exact j.injective (by rw [hj, h_star])

/-- The endomorphism `g ↦ c g c` of `Gal(Ω/E)`, where `c` is the chosen complex conjugation
`New.cmConj`. -/
def conjGal : Gal(Ω/E) →* Gal(Ω/E) :=
  MonoidHom.mk' (fun g ↦ { cmConj * g.restrictScalars ℚ * cmConj with commutes' := by simp })
    (by aesop)

/-! ### Characters that come from the norm-one torus -/

/-- The Galois character `χ` comes from the norm-one torus: `χ(Art x) = η(x / x̄)` for an idele
class character `η` of modulus `I` that is trivial on the local components at `S ∪ S̄`. Here `S`
and `I` are sets of finite places of `E`, `S ∪ S̄` is `Set.conjClosure S`, `x̄` is `star x` and
`Art` is the Artin map `New.artinMap`. -/
structure IsFromU1 (S I : Set (FinPlace E)) (χ : Gal(Ω/E) →* C) where
  /-- `χ` is locally constant. -/
  isLocallyConstant : IsLocallyConstant χ
  /-- `χ(Art x) = η(x / x̄)` for a character `η` of the finite ideles that is trivial on `Eˣ` and on
  the ideles that are units off `S ∪ S̄` and `≡ 1` at the places of `I` off `S ∪ S̄`. -/
  exists_ideleChar : ∃ η : (𝔸f E)ˣ →* C,
    (∀ x : Eˣ, η (principalIdele x) = 1) ∧
    (∀ a ∈ idelesUnitOff (Set.conjClosure S),
      (∀ w ∈ I \ S.conjClosure, Valued.v ((ideleAt w a).val - 1) < 1) → η a = 1) ∧
    ∀ (x : (𝔸f E)ˣ) (g : Gal(Ω/E)), artinMap Gal(Ω/E) x = g → χ g = η (x / star x)

/-! ### Twists and Selmer modules -/

/-- Given a ring map e:O→O', a character ψ:G→O' and a matrix representation ρ over O, the
representation g ↦ ψ(g)·e(ρ(g)) over O'. -/
def twistRep (e : O →+* O') (ψ : G →* O') (ρ : G →* Matrix n n O) : G →* Matrix n n O' :=
  smulMonoidHom.comp (ψ.prod (e.mapMatrix.toMonoidHom.comp ρ))

variable (ρ : Gal(Ω/E) → Matrix n n O) (S : Set (FinPlace E)) (L : Set (Gal(Ω/E) →₀ Matrix n n O))
  (B : Type*) [AddCommGroup B] [Module O B]

/-- The O-submodule of functions from a topological space G to an O-module B consisting of the
locally constant functions. -/
def locConst [TopologicalSpace G] : Submodule O (G → B) where
  carrier := {f | IsLocallyConstant f}
  add_mem' hf hg := hf.add hg
  zero_mem' := IsLocallyConstant.const 0
  smul_mem' c _ hf := hf.comp fun b ↦ c • b

/-- The Selmer module: locally constant cocycles for ρ with values in B^n, unramified outside S
(zero on the inertia groups above the other places) and obeying the relations L. -/
def selmerModule : Submodule O (Gal(Ω/E) → n → B) :=
  obeying (cocycleRelations ρ ∪ (fun g ↦ Finsupp.single g 1) '' inertiaAbove Sᶜ ∪ L) B ⊓
    locConst (n → B)

end New

namespace New.Selmer

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [EmbeddedNumberField E]
  [NumberField.IsCMField E] (Λ : Type) [CommRing Λ] [Algebra ℤ_[ℓ] Λ] (e ν : ℕ)

/-! ### Tate twists and the odd part of Ш -/

/-- The inverse of the ℓ-adic cyclotomic character of Gal(Ω/E), with values in the ℤ_ℓ-algebra
Λ. -/
def cyclotomicInv : Gal(Ω/E) →* Λ :=
  (Units.coeHom Λ).comp (cyclotomicCharIn (Γ := Gal(Ω/E)) Λ Ω ℓ)⁻¹

/-- The rank-one representation `Λ(-e)`: the `e`-th power of the inverse cyclotomic character
`cyclotomicInv`, written as `1 × 1` matrices (indexed by `Unit`). -/
def tateTwist : Gal(Ω/E) →* Matrix Unit Unit Λ :=
  (Matrix.scalar Unit).toMonoidHom.comp (cyclotomicInv ℓ E Λ ^ e)

/-- The single entry of the matrix `tateTwist ℓ E Λ e g` is `cyclotomicInv ℓ E Λ g ^ e`. -/
lemma tateTwist_apply (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [EmbeddedNumberField E]
    (Λ : Type) [CommRing Λ] [Algebra ℤ_[ℓ] Λ] (e : ℕ) (g : Gal(Ω/E)) :
    tateTwist ℓ E Λ e g () () = cyclotomicInv ℓ E Λ g ^ e := by
  simp [tateTwist]
/-- The elements of `Gal(Ω/E)` on which the local condition above `ℓ` is imposed. For `e = 0` they
form the union of the inertia groups at the places `A` of `Ω` above `ℓ`. For `e ≠ 0` they are the
elements of the decomposition groups at these places with trivial cyclotomic character. -/
def shaLocalSet : Set Gal(Ω/E) :=
  {g : Gal(Ω/E) | ∃ A : ClosurePlace, A.valuation ℓ < 1 ∧
    if e = 0 then g ∈ inertiaGroup Gal(Ω/E) A
    else g ∈ decompGroup Gal(Ω/E) A ∧ cyclotomicChar Ω ℓ g = 1}

/-- The module that for `e ≠ 0` describes the odd part of `Ш¹(E, Λ/ℓ^ν(-e))`: the functions `z` on
`Gal(Ω/E)` (with values vectors of length one) such that `z` vanishes on `shaLocalSet ℓ E e`, `z`
is odd under `conjGal` if `e ≠ 0`, and `z` is a continuous cocycle for `Λ(-e)` unramified outside
`ℓ`. For `e = 0` these are the continuous homomorphisms that are unramified everywhere. -/
def shaOdd : Submodule Λ (Gal(Ω/E) → Unit → QuotSpan (ℓ ^ ν : Λ)) where
  carrier := {z : Gal(Ω/E) → Unit → QuotSpan ((ℓ : Λ) ^ ν) | (∀ g ∈ shaLocalSet ℓ E e, z g = 0) ∧
    (e ≠ 0 → ∀ g : Gal(Ω/E), z (conjGal g) = -z g) ∧
    z ∈ selmerModule (tateTwist ℓ E Λ e) (placesDividing E ℓ) ∅ (QuotSpan (ℓ ^ ν : Λ))}
  add_mem' := by
    rintro z z' ⟨hz_local, hz_odd, hz_sel⟩ ⟨hz'_local, hz'_odd, hz'_sel⟩
    exact ⟨fun g hg ↦ by simp [hz_local g hg, hz'_local g hg],
      fun he g ↦ by simp [hz_odd he g, hz'_odd he g, add_comm], add_mem hz_sel hz'_sel⟩
  zero_mem' := ⟨fun _ _ ↦ rfl, fun _ _ ↦ neg_zero.symm, zero_mem _⟩
  smul_mem' := by
    rintro c z ⟨hz_local, hz_odd, hz_sel⟩
    exact ⟨fun g hg ↦ by simp [hz_local g hg], fun he g ↦ by simp [hz_odd he g],
      Submodule.smul_mem _ c hz_sel⟩

/-- `z` lies in `shaOdd ℓ E Λ e ν` exactly when `z` vanishes on `shaLocalSet ℓ E e`, `z` is odd
under `conjGal` if `e ≠ 0`, and `z` lies in the Selmer module of `Λ(-e)` unramified outside the
places above `ℓ`, with no further relations. Here `shaLocalSet` holds the local elements above `ℓ`,
`conjGal g = c g c` for complex conjugation `c`, and `QuotSpan a` is the quotient by `a`. -/
lemma mem_shaOdd {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [EmbeddedNumberField E]
    [NumberField.IsCMField E] {Λ : Type} [CommRing Λ] [Algebra ℤ_[ℓ] Λ] {e ν : ℕ}
    {z : Gal(Ω/E) → Unit → QuotSpan (ℓ ^ ν : Λ)} :
    z ∈ shaOdd ℓ E Λ e ν ↔
      (∀ g ∈ shaLocalSet ℓ E e, z g = 0) ∧
      (e ≠ 0 → ∀ g : Gal(Ω/E), z (conjGal g) = -z g) ∧
      z ∈ selmerModule (tateTwist ℓ E Λ e) (placesDividing E ℓ) ∅ (QuotSpan (ℓ ^ ν : Λ)) :=
  Iff.rfl

end New.Selmer

namespace New.OddPart

/-!
## Locally constant cocycles and the components for `Υ = cyc ^ e * ψ`

* `New.OddPart.inertiaOff N l T`: inertia over `ℚ(μ_N)` at the places above neither `l` nor a prime
  of `T`.
-/

section

variable {O : Type*} [CommRing O] {N : ℕ} (l e : ℕ) [NeZero N] [Fact l.Prime] [Algebra ℤ_[l] O]
  (ψ : DirichletCharacter O N)

/-- The character Υ = cyc^e·ψ of Gal(ℚ̄/ℚ) with values in O^×, for a prime `l`, a `ℤ_l`-algebra `O`
and a Dirichlet character `ψ` modulo `N` with values in `O`: cyc is the l-adic cyclotomic
character, and ψ is read through the action on N-th roots of unity. -/
def _root_.New.cyclotomicPowDirichlet : Gal(Ω/ℚ) →* Oˣ :=
  cyclotomicCharIn (Γ := Gal(Ω/ℚ)) O Ω l ^ e * ψ.toUnitHom.comp (cyclotomicCharMod Ω N)

/-- The O-module of locally constant maps x : Gal(Ω/ℚ) → B with x(gh) = x(g) + χ(g)x(h) (cocycles
for the character χ) that vanish on the set s. -/
def vanishingCocycles (χ : Gal(Ω/ℚ) →* Oˣ) (B : Type*) [AddCommGroup B] [Module O B]
    (s : Set Gal(Ω/ℚ)) : Submodule O (Gal(Ω/ℚ) → B) :=
  locConst B ⊓
    { carrier := {x : Gal(Ω/ℚ) → B |
        (∀ g h : Gal(Ω/ℚ), x (g * h) = x g + (χ g).val • x h) ∧ ∀ g ∈ s, x g = 0}
      add_mem' := by simp_all [add_add_add_comm]
      zero_mem' := by simp
      smul_mem' := by simp_all [smul_comm (χ _).1] }

/-- The elements of Gal(Ω/ℚ(μ_N)) lying in the inertia group of some place above neither l nor
any prime of T. -/
def inertiaOff (N l : ℕ) [NeZero N] (T : Finset Nat.Primes) : Set Gal(Ω/ℚ) :=
  {g : Gal(Ω/ℚ) | ∃ A : ClosurePlace,
    (g ∈ cycloGalGroup N ∧ A.valuation l = 1 ∧ g ∈ inertiaGroup Gal(Ω/ℚ) A) ∧
    ∀ r ∈ T, ¬A.valuation (r : Ω) < 1}

/-- The component attached to the character `Υ = cyc ^ e * ψ` (`New.cyclotomicPowDirichlet l e ψ`).
It consists of the locally constant cocycles for `Υ⁻¹` on the absolute Galois group of `ℚ`, with
values in `O / l ^ ν`. They vanish at `New.cmConj` and at the elements of `New.cycloGalGroup N` that
lie in an inertia group at a place prime to `l` or in `New.Selmer.shaLocalSet l ℚ 1`. -/
abbrev component (ν : ℕ) : Submodule O (Gal(Ω/ℚ) → QuotSpan ((l : O) ^ ν)) :=
  vanishingCocycles (cyclotomicPowDirichlet l e ψ)⁻¹ (QuotSpan (l ^ ν : O))
    (insert cmConj
      (cycloGalGroup N ∩ (inertiaAbove (placesDividing ℚ l)ᶜ ∪ Selmer.shaLocalSet l ℚ 1)))

end

/-!
## Places of ℚ̄ above a rational prime

Places are valuation subrings `B`, and `B.valuation q < 1` says that `B` lies above `q`.
-/

section LocalBasics

/-- The action of `Gal(Ω/ℚ)` on `Ω^×`, written additively. -/
noncomputable abbrev galUnitsRep : Representation ℤ Gal(Ω/ℚ) (DiscreteUnits Ω) := unitsRep

/-- The principal units of the valuation subring B of ℚ̄ (elements congruent to 1 modulo its
maximal ideal), as a subgroup of ℚ̄^× written additively. -/
noncomputable def principalUnits (B : ClosurePlace) : AddSubgroup (DiscreteUnits Ω) :=
  B.principalUnitGroup.toAddSubgroup

/-- Let `B` be a place of `Ω` above the prime `q`, that is, `q` is not a unit at `B`. Then `B` lies
over a finite place `v` of `ℚ` (`IsPlaceOver B v`) of norm `v.q = q`, and `q`, written
`DiscreteUnits.ofNeZero q _` in the additive group `Ωˣ`, has order one at `B`, for the order
`ordRat ℚ B` normalised on `ℚ`. -/
lemma exists_isPlaceOver_prime {q : ℕ} {B : ClosurePlace} [Fact q.Prime]
    (hq_nonunit : B.valuation (q : Ω) < 1) :
    ∃ v : FinPlace ℚ,
      IsPlaceOver B v ∧ v.q = q ∧ ordRat ℚ B (DiscreteUnits.ofNeZero q NeZero.out) = 1 := by
  obtain ⟨v, ⟨hv_norm, -⟩, hv_unif, hv_over⟩ := exists_rat_place_of_prime (Fact.out : q.Prime)
  refine ⟨v, hv_over B hq_nonunit, hv_norm, ?_⟩
  -- On `ℚ` the order is minus the logarithm of the `v`-adic valuation, which is `exp (-1)` at `q`.
  have h_ofBase : DiscreteUnits.ofNeZero (q : Ω) NeZero.out =
      DiscreteUnits.ofBase Gal(Ω/ℚ) Ω (Additive.ofMul (Units.mk0 (q : ℚ) NeZero.out)) :=
    Additive.toMul.injective (Units.ext (by simp))
  rw [h_ofBase, (hv_over B hq_nonunit).ordRat_ofBase, Units.val_mk0, hv_unif, WithZero.log_exp]
  norm_num

/-- Let `B` be a place of `Ω` above the prime `q` (`q` is not a unit at `B`), and let
`q ≡ 1` mod `m`. Then the decomposition group of `B` in `Gal(Ω/ℚ)` fixes the `m`-th roots of unity:
it lies in `cycloGalGroup m`, the kernel of the cyclotomic character modulo `m`. -/
lemma decompGroup_le_cycloGalGroup {q m : ℕ} [NeZero m] {B : ClosurePlace} [Fact q.Prime]
    (hq_nonunit : B.valuation (q : Ω) < 1) (hq_modEq : q ≡ 1 [MOD m]) :
    decompGroup Gal(Ω/ℚ) B ≤ cycloGalGroup m := by
  -- The decomposition group is generated topologically by inertia and a Frobenius; the open
  -- subgroup `cycloGalGroup m` contains both, since `m` is a unit at `B` and `q ≡ 1` mod `m`.
  obtain ⟨v, hB_over, rfl, -⟩ := exists_isPlaceOver_prime hq_nonunit
  have hm_unit : B.valuation (m : Ω) = 1 :=
    hq_modEq.coprime_of_modEq_one.valuation_eq_one hq_nonunit
  obtain ⟨frob, hfrob⟩ : ∃ frob : Gal(Ω/ℚ), IsFrob B v.q frob := hB_over.exists_isFrob Gal(Ω/ℚ)
  have h_inertia_le : inertiaGroup Gal(Ω/ℚ) B ≤ cycloGalGroup m :=
    fun σ hσ ↦ cyclotomicCharMod_eq_one_of_mem_inertiaGroup hσ hm_unit
  exact hB_over.decompGroup_le hfrob Fact.out h_inertia_le
    ((hfrob.mem_ker_cyclotomicCharMod_iff hm_unit).mpr hq_modEq)

end LocalBasics

end New.OddPart

end
