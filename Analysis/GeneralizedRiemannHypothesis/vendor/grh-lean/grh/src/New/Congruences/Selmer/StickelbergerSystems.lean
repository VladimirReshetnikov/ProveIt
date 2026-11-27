import Lib.GaloisRep.Main.AttachedRepresentations
import Lib.General.NumberTheory.GaussValuation
import New.Congruences.Selmer.AuxiliaryPrimes

/-!
# Stickelberger systems

A Stickelberger system consists of elements `Θ_Q` of the group rings over `ℤ̄_ℓ` of the class groups
`Cl_Q` of norm-one finite ideles, one for each finite set `Q` of places. Their values under
characters for `Q` change by Euler factors when `Q` grows to an auxiliary set. A character for
`Q` is a Galois character with `IsFromU1 (placesDividing E ℓ) Q`; it is read on `Cl_Q` through
`y / ȳ ↦ Art y`. Its order is not assumed to be a power of `ℓ`.

* `New.Selmer.U1ClassGroup`, `New.Selmer.groupRingEval`: the group `Cl_Q`, and the value of a
  function on the Galois group at an element of its group ring.
* `New.Selmer.StickelbergerSystem`, `New.Selmer.StickelbergerSystem.β`: the systems and their
  constant.

Notions from other files:
* `New.Ω`: the algebraic closure of `ℚ` into which every number field in this file is embedded;
  `Gal(Ω/E)` is the absolute Galois group of `E`, and `New.ClosurePlace` is the type of places
  (valuation subrings) of `Ω`.
* `New.IsFromU1 S I χ`, for sets `S` and `I` of finite places of a CM field `E`: the Galois
  character `χ` is locally constant and satisfies `χ(Art y) = η(y / ȳ)` for an idele class
  character `η` that is trivial on the local components at `S` and its conjugates and has
  modulus `I` away from these places.
* `New.IsAuxiliary S Q`: the places of `Q` have prime norm, neither they nor their conjugates lie in
  `S`, and their conjugates lie outside `Q`.
* `New.ellVal`: the valuation `v` on `ℚ̄_ℓ` with `v ℓ = 1`, cut off below at `0`; `New.intQpBar ℓ`
  is the ring `ℤ̄_ℓ` of integral elements.
* `New.artinMap`: the Artin map from the finite ideles to the abelianised Galois group.

## Relation to the literature

See `New.Congruences.Selmer.TwistingTheorem` for related work.
-/

noncomputable section

namespace New

open Finset

open scoped ENNReal

section Characters

variable {E : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E] {C C' : Type*}
  [CommMonoid C] [CommMonoid C'] {S I I' : Set (FinPlace E)} {χ χ' : Gal(Ω/E) →* C}

/-- Enlarging the modulus: let the character `χ` of the absolute Galois group `Gal(Ω/E)` satisfy
`χ(Art y) = η(y / ȳ)` for an idele class character `η` of modulus `I` that is trivial at the places
of `S` and their conjugates (`IsFromU1 S I χ`). Then the same holds for any modulus `I'` that
contains `I`. -/
lemma IsFromU1.mono (hχ : IsFromU1 S I χ) (h_subset : I ⊆ I') : IsFromU1 S I' χ := by
  obtain ⟨η, η_principal, η_unit, η_artin⟩ := hχ.exists_ideleChar
  exact ⟨hχ.isLocallyConstant, η, η_principal,
    fun a ha h_one ↦ η_unit a ha fun w ⟨hw_mem, hw⟩ ↦ h_one w ⟨h_subset hw_mem, hw⟩, η_artin⟩

/-- Let the Galois character `χ` with values in a commutative monoid `C` satisfy
`χ(Art y) = η(y / ȳ)` for an idele class character `η` of modulus `I` that is trivial at the places
of `S` and their conjugates (`IsFromU1 S I χ`). For a homomorphism `f : C → C'` the same holds for
`f ∘ χ`, with `f ∘ η` in place of `η`. -/
lemma IsFromU1.map (hχ : IsFromU1 S I χ) (f : C →* C') : IsFromU1 S I (f.comp χ) := by
  obtain ⟨η, η_principal, η_unit, η_artin⟩ := hχ.exists_ideleChar
  exact ⟨hχ.isLocallyConstant.comp f, f.comp η, fun x ↦ by simp [η_principal],
    fun a ha h_one ↦ by simp [η_unit a ha h_one], fun x g hx ↦ by simp [η_artin x g hx]⟩

/-- The trivial Galois character comes from the trivial idele class character, so it satisfies
`IsFromU1 S I` for all sets `S` and `I` of places. -/
lemma IsFromU1.one : IsFromU1 S I (1 : Gal(Ω/E) →* C) :=
  ⟨IsLocallyConstant.const 1, 1, by simp⟩

/-- If the Galois characters `χ` and `χ'` of `Gal(Ω/E)` both satisfy `IsFromU1 S I`, that is, they
come by `y ↦ y / ȳ` from idele class characters of modulus `I` that are trivial at the places of `S`
and their conjugates, then so does their product `χ * χ'`; it comes from the product of these idele
class characters. -/
lemma IsFromU1.mul (hχ : IsFromU1 S I χ) (hχ' : IsFromU1 S I χ') : IsFromU1 S I (χ * χ') := by
  obtain ⟨η, η_principal, η_unit, η_artin⟩ := hχ.exists_ideleChar
  obtain ⟨η', η'_principal, η'_unit, η'_artin⟩ := hχ'.exists_ideleChar
  exact ⟨hχ.isLocallyConstant.mul hχ'.isLocallyConstant, η * η', by simp [*],
    fun a ha h_one ↦ by simp [η_unit a ha h_one, η'_unit a ha h_one],
    fun x g hx ↦ by simp [η_artin x g hx, η'_artin x g hx]⟩

end Characters

/-- Let `I'` be a finite set of places of a CM field that is auxiliary for `S`: its places have
prime norm, neither they nor their conjugates lie in `S`, and their conjugates lie outside `I'`.
Then every subset `I` of `I'` is auxiliary for `S`. -/
lemma IsAuxiliary.mono {E : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]
    {S I I' : Finset (FinPlace E)} (h_aux : IsAuxiliary S I') (h_subset : I ⊆ I') :
    IsAuxiliary S I := by
  intro v hv
  obtain ⟨hvS, h_prime, h_star_notMem, h_starS⟩ := h_aux v (h_subset hv)
  exact ⟨hvS, h_prime, fun h_mem ↦ h_star_notMem (h_subset h_mem), h_starS⟩

namespace Selmer

section ClassGroup

variable {E : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]
  (Q : Finset (FinPlace E))

/-- The group `Cl_Q`: finite ideles `u` with `u ū = 1`, modulo those in `Eˣ` and the units that
are `≡ 1` at the primes of `Q`. -/
abbrev U1ClassGroup : Type :=
  unitary (𝔸f E) ⧸ Subgroup.closure {u : unitary (𝔸f E) |
    Unitary.toUnits u ∈ principalIdele.range ∨ Unitary.toUnits u ∈ idelesUnitOff ∅ ∧
      ∀ w ∈ Q, Valued.v ((ideleAt w (Unitary.toUnits u)).1 - 1) < 1}

/-- The class of `y / ȳ` in `Cl_Q`, for a finite idele `y`. -/
def divStarClass : (𝔸f E)ˣ →* U1ClassGroup Q := (QuotientGroup.mk' _).comp divStar.toMonoidHom

/-- Let `E` be a CM field, with complex conjugation `y ↦ ȳ`, and `Q` a finite set of finite places
of `E`. The map `divStarClass Q`, which sends a finite idele `y` to the class of `y / ȳ` in `Cl_Q`,
is surjective, by Hilbert's Theorem 90 for finite ideles. -/
lemma divStarClass_surjective (Q : Finset (FinPlace E)) :
    Function.Surjective (divStarClass Q : (𝔸f E)ˣ → U1ClassGroup Q) := by
  refine QuotientGroup.mk_surjective.forall.2 fun u ↦ ?_
  let σ : Gal(E/NumberField.maximalRealSubfield E) := NumberField.IsCMField.complexConj E
  -- The adele map of complex conjugation is, by definition, the involution `star`.
  have h_star_mul : adeleMap σ u.1 * u.1 = 1 := Unitary.coe_star_mul_self u
  have h_norm : ∏ i ∈ range (orderOf σ), adeleMap (↑(σ ^ i) : E →+* E) u.1 = 1 := by
    simpa [σ, NumberField.IsCMField.orderOf_complexConj, range, AlgEquiv.aut_one] using h_star_mul
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := hilbert90_finite_idele h_norm
  have h_eq : u.1 * star y.1 = y.1 := hy
  have h_divStar : y.1 * star y⁻¹.1 = u.1 := by
    nth_rw 1 [← h_eq, mul_assoc, ← star_mul', Units.mul_inv, star_one, mul_one]
  exact ⟨y, congrArg QuotientGroup.mk (Subtype.ext h_divStar)⟩

variable {Q}

/-- A chosen element of the Galois group that lifts `Art y`, for a chosen finite idele `y` with
`y / ȳ` in the class `c`. -/
def galoisLift (c : U1ClassGroup Q) : Gal(Ω/E) :=
  (artinMap Gal(Ω/E) (Function.surjInv (divStarClass_surjective Q) c)).out

/-- Let `E` be a CM field, `Gal(Ω/E)` its absolute Galois group, and `Q` a finite set of places of
`E`. Let the character `χ` of `Gal(Ω/E)` satisfy `χ(Art y) = η(y / ȳ)` for an idele class character
`η` of modulus `Q` that is trivial at the places of `S` and their conjugates (`IsFromU1 S Q χ`). If
the image of `g` in the abelianised Galois group is the Artin symbol of the idele `y`, then `χ` has
the same value at `g` and at `galoisLift (divStarClass Q y)`, the chosen Galois element for the
class of `y / ȳ` in `Cl_Q`. -/
lemma _root_.New.IsFromU1.apply_galoisLift {C : Type*} [CommMonoid C] {S : Set (FinPlace E)}
    {χ : Gal(Ω/E) →* C} (hχ : IsFromU1 S Q χ) {y : (𝔸f E)ˣ} {g : Gal(Ω/E)}
    (hy : artinMap Gal(Ω/E) y = g) : χ (galoisLift (divStarClass Q y)) = χ g := by
  -- On norm-one ideles the idele character of `χ` factors through a homomorphism `η'` on `Cl_Q`;
  -- both sides are the value of `η'` at the class of `y / ȳ`.
  obtain ⟨η, η_principal, η_unit, η_artin⟩ : ∃ η : (𝔸f E)ˣ →* C,
      (∀ x : Eˣ, η (principalIdele x) = 1) ∧ (∀ a ∈ idelesUnitOff (Set.conjClosure S),
        (∀ w ∈ (Q : Set _) \ S.conjClosure, Valued.v ((ideleAt w a).val - 1) < 1) → η a = 1) ∧
      ∀ (x : (𝔸f E)ˣ) (h : Gal(Ω/E)), artinMap Gal(Ω/E) x = h → χ h = η (x / star x) :=
    hχ.exists_ideleChar
  let η' : U1ClassGroup Q →* C := QuotientGroup.lift _ (η.comp Unitary.toUnits) <| by
    refine (Subgroup.closure_le (MonoidHom.ker _)).2 ?_
    rintro u (⟨x, hx⟩ | ⟨h_unit, h_one⟩)
    · simpa [← hx] using η_principal x
    · exact η_unit _ (idelesUnitOff_mono bot_le h_unit) fun w ⟨hw, _⟩ ↦ h_one w hw
  have hη' (x : (𝔸f E)ˣ) : η' (divStarClass Q x) = η (x / star x) :=
    congrArg η (Units.ext rfl : Unitary.toUnits (divStar x) = x / star x)
  -- By definition, `galoisLift` lifts the Artin symbol of a chosen preimage `z` of the class.
  let z : (𝔸f E)ˣ := Function.surjInv (divStarClass_surjective Q) (divStarClass Q y)
  have h_lift : artinMap Gal(Ω/E) z = galoisLift (divStarClass Q y) := (Quotient.out_eq _).symm
  calc χ (galoisLift (divStarClass Q y)) = η (z / star z) := η_artin z _ h_lift
    _ = η' (divStarClass Q y) := by rw [← hη', Function.surjInv_eq (divStarClass_surjective Q)]
    _ = χ g := by rw [hη', η_artin y g hy]

variable {O R R' : Type*} [CommSemiring O] [AddCommMonoid R] [Module O R] [AddCommMonoid R']
  [Module O R']

/-- The value of a function `f` on the Galois group, read on `Cl_Q` through `galoisLift` and
extended linearly, at an element of the group ring of `Cl_Q`. -/
def groupRingEval (f : Gal(Ω/E) → R) (a : MonoidAlgebra O (U1ClassGroup Q)) : R :=
  Finsupp.linearCombination O (fun c ↦ f (galoisLift c)) a.coeff

/-- A linear map `L` commutes with the evaluation of group-ring elements: applying it to the value
of `f` gives the value of `L ∘ f`. -/
lemma map_groupRingEval (L : R →ₗ[O] R') (f : Gal(Ω/E) → R)
    (a : MonoidAlgebra O (U1ClassGroup Q)) :
    L (groupRingEval f a) = groupRingEval (fun g : Gal(Ω/E) ↦ L (f g)) a :=
  Finsupp.apply_linearCombination O L _ a.coeff

/-- The value of `f` at an element `∑ i ∈ s, c i • [u i]` of the group ring of `Cl_Q` is the sum
of the `c i • f (galoisLift (u i))`. -/
lemma groupRingEval_sum_single {α : Type*} (s : Finset α) (f : Gal(Ω/E) → R)
    (u : α → U1ClassGroup Q) (c : α → O) :
    groupRingEval f (∑ i ∈ s, MonoidAlgebra.single (u i) (c i)) =
      ∑ i ∈ s, c i • f (galoisLift (u i)) := by simp [groupRingEval, map_sum]

end ClassGroup

section EulerFactor

variable {K : Type*} [Field K] (exps : List ℤ) (a : K) (q : ℕ)

/-- The product of the factors `1 - a ^ (±1) q ^ (-e)` over a list of integers `e` and both
signs. -/
def eulerFactor : K :=
  (exps.map fun e ↦ ∏ ε : ℤˣ, (1 - a ^ (ε : ℤ) * (q : K) ^ (-e))).prod

lemma eulerFactor_nil : eulerFactor [] a q = 1 := rfl

lemma eulerFactor_cons (e : ℤ) : eulerFactor (e :: exps) a q =
    (1 - a * (q : K) ^ (-e)) * (1 - a⁻¹ * (q : K) ^ (-e)) * eulerFactor exps a q := by
  simp [eulerFactor]

/-- The product of Euler factors at `a` is symmetric in `a` and `a⁻¹`. -/
lemma eulerFactor_zpow_units (δ : ℤˣ) :
    eulerFactor exps (a ^ (δ : ℤ)) q = eulerFactor exps a q := by
  rcases Int.units_eq_one_or δ with rfl | rfl <;> simp [eulerFactor, mul_comm]

end EulerFactor

variable (ℓ : ℕ) [ThePrime ℓ] {E : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]

open scoped Classical in
/-- A Stickelberger system for a finite set `S₀` of places of the CM field `E` and an element `g₀`
of `Gal(Ω/E)` consists of a character `ϑ = twistChar` unramified outside `S₀` with `ϑ g₀ ≠ 1`, a
list of integers `exponents`, and an element `Θ_Q = element Q` of the group ring of `Cl_Q` over
`ℤ̄_ℓ` for every finite set `Q` of places, whose values under characters for `Q` change by Euler
factors when a place is added to `Q` such that the enlarged set is auxiliary for `S₀`. -/
structure StickelbergerSystem (S₀ : Finset (FinPlace E)) (g₀ : Gal(Ω/E)) where
  /-- The character `ϑ` by which the characters `ψ` are twisted in the Euler factors. -/
  twistChar : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ
  /-- `ϑ` is continuous; so its values are `ℓ`-adic units. -/
  continuous_twistChar : Continuous twistChar
  /-- `ϑ` is unramified outside `S₀`. -/
  unramified : ∀ g ∈ inertiaAbove (S₀ : Set (FinPlace E))ᶜ, twistChar g = 1
  /-- `ϑ` is not trivial at `g₀`. -/
  twistChar_apply_ne_one : twistChar g₀ ≠ 1
  /-- The list of exponents `e` of `(N P)⁻¹` in the Euler factors. -/
  exponents : List ℤ
  /-- The element `Θ_Q` of the group ring of `Cl_Q` attached to a finite set `Q` of places. -/
  element (Q : Finset (FinPlace E)) : MonoidAlgebra (intQpBar ℓ) (U1ClassGroup Q)
  /-- The trivial character does not vanish at the element for the empty set. -/
  one_element_empty_ne_zero : groupRingEval (1 : Gal(Ω/E) →* PadicAlgCl ℓ) (element ∅) ≠ 0
  /-- The norm relation: for a character `ψ` for `Q`, adding a prime `P` to `Q` multiplies the
  value of `ψ` by the factors `1 - (ϑ ψ)(φ) ^ (±1) (N P) ^ (-e)`, where `φ` is any Frobenius
  element at `P`. As both signs occur, arithmetic and geometric Frobenius elements give the same
  product. -/
  element_insert (Q : Finset (FinPlace E)) (P : FinPlace E) (hP : P ∉ Q)
    (hQ : IsAuxiliary S₀ (insert P Q)) (ψ : Gal(Ω/E) →* PadicAlgCl ℓ)
    (hψ : IsFromU1 (placesDividing E ℓ) Q ψ) (A : ClosurePlace) (hA : IsPlaceOver A P)
    (φ : Gal(Ω/E)) (hφ : IsFrob A P.q φ) :
    groupRingEval ψ (element (insert P Q)) =
      groupRingEval ψ (element Q) * eulerFactor exponents ((twistChar φ : PadicAlgCl ℓ) * ψ φ) P.q

namespace StickelbergerSystem

variable {ℓ} {S₀ : Finset (FinPlace E)} {g₀ : Gal(Ω/E)} (Y : StickelbergerSystem ℓ S₀ g₀)

/-- For a Stickelberger system `Y`, the number `β = v(1(Θ_∅)) + ∑_e 2 v(ϑ(g₀) - 1)`. Here `v` is
the `ℓ`-adic valuation `ellVal`, `ϑ = Y.twistChar`, `g₀` is the Galois element at which the system
has `ϑ(g₀) ≠ 1`, `e` runs over the list `Y.exponents`, and `1(Θ_∅)` is the value of the trivial
character at the group-ring element `Θ_∅ = Y.element ∅`. -/
def β : ℝ≥0∞ :=
  ellVal (groupRingEval (1 : Gal(Ω/E) →* PadicAlgCl ℓ) (Y.element ∅)) +
    Y.exponents.length * (2 * ellVal (Y.twistChar g₀ - 1 : PadicAlgCl ℓ))

/-- The values of the character `Y.twistChar` (written `ϑ`), read in `PadicAlgCl ℓ`, have norm one,
as `ϑ` is continuous on a compact group. -/
lemma norm_twistChar (g : Gal(Ω/E)) : ‖(Y.twistChar g : PadicAlgCl ℓ)‖ = 1 :=
  norm_eq_one_of_continuous Y.continuous_twistChar g

/-- Let `Y` be a Stickelberger system, so `Θ_Q = Y.element Q` is an element of the group ring over
`ℤ̄_ℓ` of the group `Cl_Q` of norm-one idele classes. The value of the trivial character at `Θ_Q`
has norm at most one, as it is the image of an element of `ℤ̄_ℓ`. -/
lemma norm_groupRingEval_one_element_le_one (Q : Finset (FinPlace E)) :
    ‖groupRingEval (1 : Gal(Ω/E) →* PadicAlgCl ℓ) (Y.element Q)‖ ≤ 1 := by
  have h_coe : ((groupRingEval (fun _ ↦ 1) (Y.element Q) : intQpBar ℓ) : PadicAlgCl ℓ) =
      groupRingEval (1 : Gal(Ω/E) →* PadicAlgCl ℓ) (Y.element Q) :=
    map_groupRingEval (Algebra.linearMap (intQpBar ℓ) (PadicAlgCl ℓ)) (fun _ ↦ 1) (Y.element Q)
  rw [← h_coe]
  exact norm_coe_le_one _

/-- For a Stickelberger system `Y` for `S₀` and `g₀`, the number
`β = v(1(Θ_∅)) + ∑_e 2 v(ϑ(g₀) - 1)` is finite. Here `v` is the `ℓ`-adic valuation, infinite only
at `0`, `ϑ = Y.twistChar`, `e` runs over `Y.exponents`, and `1(Θ_∅)` is the value of the trivial
character at the group-ring element `Y.element ∅`; by the axioms of the system this value is not
`0` and `ϑ(g₀) ≠ 1`. -/
lemma β_ne_top : Y.β ≠ ⊤ := by
  have h_ϑ : (Y.twistChar g₀ - 1 : PadicAlgCl ℓ) ≠ 0 :=
    sub_ne_zero.2 (Units.val_eq_one.not.2 Y.twistChar_apply_ne_one)
  simp [β, ENNReal.mul_eq_top, ellVal_eq_top_iff, Y.one_element_empty_ne_zero, h_ϑ]

open scoped Classical in
/-- The norm relation for several primes. Let `E` be a CM field with absolute Galois group
`Gal(Ω/E)`, and `Y` a Stickelberger system for a finite set `S₀` of places and `g₀ ∈ Gal(Ω/E)`: a
character `ϑ = Y.twistChar` unramified outside `S₀` with `ϑ g₀ ≠ 1`, a list `Y.exponents` of
integers, and group-ring elements `Θ_Q = Y.element Q` with a norm relation. Let `Q` and `I` be
disjoint with `Q ∪ I` auxiliary for `S₀`, let the Galois character `ψ` come from an idele class
character of modulus `Q` trivial above `ℓ` (`IsFromU1`), and for `v` in `I`, of norm `v.q`, let
`φ v` be a Frobenius element at a place (valuation subring) `A v : ClosurePlace` of `Ω` over `v`.
Then the value of `ψ` at `Θ_{Q ∪ I}` is its value at `Θ_Q` times the factors
`1 - (ϑ ψ)(φ v) ^ (±1) (v.q) ^ (-e)` for `v` in `I`, `e` in the list and both signs. -/
lemma groupRingEval_element_union (Y : StickelbergerSystem ℓ S₀ g₀)
    {Q I : Finset (FinPlace E)} (h_disj : Disjoint Q I) (h_aux : IsAuxiliary S₀ (Q ∪ I))
    {ψ : Gal(Ω/E) →* PadicAlgCl ℓ} (hψ : IsFromU1 (placesDividing E ℓ) Q ψ)
    {A : FinPlace E → ClosurePlace} (hA : ∀ v ∈ I, IsPlaceOver (A v) v)
    {φ : FinPlace E → Gal(Ω/E)} (hφ : ∀ v ∈ I, IsFrob (A v) v.q (φ v)) :
    groupRingEval ψ (Y.element (Q ∪ I)) = groupRingEval ψ (Y.element Q) *
      ∏ v ∈ I, eulerFactor Y.exponents ((Y.twistChar (φ v) : PadicAlgCl ℓ) * ψ (φ v)) v.q := by
  induction I using Finset.induction_on with
  | empty => rw [union_empty, prod_empty, mul_one]
  | insert v I hv ih =>
    obtain ⟨hvQ, h_disj'⟩ := disjoint_insert_right.1 h_disj
    obtain ⟨hAv, hA⟩ := (forall_mem_insert ..).1 hA
    obtain ⟨hφv, hφ⟩ := (forall_mem_insert ..).1 hφ
    rw [union_insert] at h_aux ⊢
    have h_insert : groupRingEval ψ (Y.element (insert v (Q ∪ I))) =
        groupRingEval ψ (Y.element (Q ∪ I)) *
          eulerFactor Y.exponents ((Y.twistChar (φ v) : PadicAlgCl ℓ) * ψ (φ v)) v.q :=
      Y.element_insert (Q ∪ I) v (notMem_union.2 ⟨hvQ, hv⟩) h_aux ψ
        (hψ.mono (coe_subset.2 subset_union_left)) (A v) hAv (φ v) hφv
    rw [h_insert, prod_insert hv, ih h_disj' (h_aux.mono (subset_insert _ _)) hA hφ]
    ring

end StickelbergerSystem

end Selmer

end New

end
