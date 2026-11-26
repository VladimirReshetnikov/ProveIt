import Lib.GaloisRep.LocalGlobal.LabelCompatibility
import Lib.GaloisRep.Main.DivisibleSelmerModules
import New.Congruences.LocalLoss.Basic
import New.OneLift.TestedForms
import New.UpperBound.Objects.Rows

/-!
# Bad places, ℓ-adic avatars and hypotheses on conjugate self-dual representations

Fix data `D`, a prime `ℓ` and a descent pair `O` (`New.DescentPair`) with chosen places
`O.chosenPlace`. This file introduces the bad places and the `ℓ`-adic avatars of characters of
`U(1)`. It states the hypotheses on conjugate self-dual `ℓ`-adic representations `R` of the
absolute Galois group of the CM field `D.E` under which Selmer groups are bounded: conjugate
self-dual representations of given level, main summands and representations of a type. It also
defines lift settings and the idempotents of tuples of types acting on forms. The two primes
`p₀`, `p₁` of the data are `D.levelPrime 0` and `D.levelPrime 1`.

## Main definitions and results

* `New.Selmer.IsConjSelfDual`: `R` is continuous, has a non-degenerate trace form on the span of its
  image, and is conjugate self-dual up to a twist.
* `New.Selmer.IsConjSelfDualOfLevel`: moreover `R` has given jumps and is of finite type at the
  places off a set `S` and at those above `ℓ p₀ p₁`, and has good reduction at those of them prime
  to `p₀ p₁`.
* `New.Selmer.IsMainSummandLike`: the case `S = ∅`, with conditions on the jumps, the ramification
  above `p₀ p₁` and the size of the image.
* `New.Selmer.IsLiftSetting`, `New.Selmer.typeProjection`: descent pairs with type polynomials
  suited to a twist, and the idempotents of tuples of types acting on forms.

Notions from other files:
* `New.DescentPair`: A descent pair: places M and Q, a space W of rank r with numbered basis
  vectors, an embedding of its r indices into a set of n > r indices, weights k⁺ and k⁻, and a
  character μ whose tame part is trivial off these places.
* `New.DescentPair.FormV`: the algebraic forms on the definite space `V = I_n` with the weight and
  level of `O`; the product of the groups `GL_r(k_w)` at the chosen places acts on them.
* `New.conjGal`: The map `g ↦ g^c = c g c`, with `c` complex conjugation.

## Relation to the literature

See `Lib.ClassField.Avatar.LocalGlobalCompatibility` for sources.
-/

noncomputable section

/-!
## Bad places and ℓ-adic avatars of characters of U(1)

For the data `D`, an embedding of `D.E` in `ℚ̄` (`New.Ω`) is fixed.

* `New.Selmer.avatar_conjGal_mul_avatar`: `μ(g^c) μ(g) = cyc(g)^{2j - k}`.
-/

namespace New.Selmer

open Matrix.GeneralLinearGroup Polynomial Units GaloisRep AlgHeckeChar WeilData AutChar.HasWeight

variable {P : Parameters} (D : Data P) (ℓ : ℕ) [ThePrime ℓ]

/-- `D.E` is a `New.CMFieldWithRoot5040`. Its embedding in `Ω` factors through the cyclotomic field
of conductor `D.cyclotomicConductor`. -/
noncomputable instance : CMFieldWithRoot5040 D.E :=
  {((cycloField _).val.comp P.toCycloField).toAlgebra with}

lemma _root_.New.Data.algebraMap_mem_cycloField (x : D.E) :
    algebraMap D.E Ω x ∈ cycloField D.cyclotomicConductor :=
  Subtype.prop (P.toCycloField x)

/-! ### The Galois group and the bad places -/

/-- The absolute Galois group of the field E of the data D: automorphisms of an algebraic
closure of E fixing E. -/
abbrev AbsGal : Type := Gal(Ω/D.E)

/-- The set of finite places of E above one of the two primes p₀, p₁ of the data. -/
def placesAboveM : Set (FinPlace D.E) :=
  {v : FinPlace D.E | ∃ i : Fin 2, ↑(D.levelPrime i) ∈ v.asIdeal}

/-- The finite set of places of E dividing `ℓ p₀ p₁ N`, with `N` the level of the data; these are
the bad places. -/
noncomputable def badPlaces : Finset (FinPlace D.E) :=
  (finite_natCast_mem (K := D.E) (ℓ * (D.M * D.N))).toFinset

/-- The places dividing `ℓ` and the places above `p₀` or `p₁` are bad places. -/
lemma placesDividing_union_subset_badPlaces :
    placesDividing D.E ℓ ∪ placesAboveM D ⊆ badPlaces D ℓ := by
  intro w hw
  -- A prime ideal contains `ℓ p₀ p₁ N` as soon as it contains one of the factors.
  suffices h_mem : ↑(ℓ * (D.M * D.N)) ∈ w.asIdeal by simpa [badPlaces] using h_mem
  obtain hℓ | ⟨i, hi⟩ := hw
  · simpa using w.asIdeal.mul_mem_right _ hℓ
  · have h_dvd : D.levelPrime i ∣ D.M := by fin_cases i <;> simp [Data.M]
    exact w.asIdeal.mem_of_dvd (Nat.cast_dvd_cast ((h_dvd.mul_right D.N).mul_left ℓ)) hi

variable {D ℓ}

/-- A chosen place (`New.Data.IsChosen`) lies above `p₀` or `p₁`. -/
lemma _root_.New.Data.IsChosen.mem_placesAboveM {v : FinPlace D.E} (hv : D.IsChosen v) :
    v ∈ placesAboveM D :=
  let ⟨i, _, h_above⟩ := D.isChosen_iff.1 hv
  ⟨i, h_above⟩

@[simp, grind =]
lemma star_mem_placesAboveM {v : FinPlace D.E} : star v ∈ placesAboveM D ↔ v ∈ placesAboveM D := by
  simp [placesAboveM]

/-- Two distinct `N`-th roots of unity in `ℚ̄_ℓ` have distance at least `‖N‖`. -/
lemma norm_natCast_le_norm_sub_of_pow_eq_one {x y : PadicAlgCl ℓ} {N : ℕ} :
    x ^ N = 1 → y ^ N = 1 → x ≠ y → ‖(N : PadicAlgCl ℓ)‖ ≤ ‖x - y‖ := by
  intro hx hy hxy
  by_contra! h_lt
  -- Roots of unity closer than `N` in the valuation are equal.
  have h_val : intQpBar ℓ (x - y) < intQpBar ℓ N :=
    lt_of_not_ge fun h_le ↦ h_lt.not_ge ((valuation_intQpBar_le_iff _ _).1 h_le)
  exact hxy (eq_of_pow_eq_one_of_val_sub_lt hx hy h_val)

@[fun_prop]
lemma continuous_cyclotomicInv : Continuous (cyclotomicInv ℓ D.E (PadicAlgCl ℓ)) :=
  continuous_coe_inv.comp continuous_cyclotomicCharIn

/-- For a Frobenius datum `x` whose place `x.place` does not divide `ℓ`, the inverse cyclotomic
character `cyclotomicInv ℓ D.E (PadicAlgCl ℓ)` takes the value `x.place.q`, the norm of `x.place`,
at `x.frob`, a geometric Frobenius at `x.place`. -/
lemma cyclotomicInv_frob (x : FrobeniusDatum D.E) (hℓ : ↑ℓ ∉ x.place.asIdeal) :
    cyclotomicInv ℓ D.E (PadicAlgCl ℓ) x.frob = x.place.q := by
  have h_unit : x.valuationSubring.valuation (ℓ : Ω) = 1 :=
    x.isPlaceOver.valuation_natCast_eq_one_iff.2 hℓ
  simp [cyclotomicInv, ← map_inv, x.isFrob_inv.cyclotomicChar_eq ℓ h_unit]

variable [PadicIso ℓ]

/-! ### Avatars and the cyclotomic character -/

/-- The ℓ-adic avatar, through ι, of the base change to E of ϑ⁻¹: a character of the absolute
Galois group of E with values in ℚ̄_ℓ. Here ι is the isomorphism of ℂ with ℚ̄_ℓ that the instance
`New.PadicIso ℓ` fixes. -/
noncomputable def _root_.New.Data.TameChar.invAvatar (ϑ : D.TameChar) : AbsGal D →* PadicAlgCl ℓ :=
  (coeHom (PadicAlgCl ℓ)).comp (ϑ.hasWeight.inv.toAlgebraic 0 0).avatar

/-- Let `x` be a Frobenius datum whose place does not divide `ℓ`, with the tame part `ψ` of `a`
trivial at the place and at its conjugate, and let `μ` be the avatar of the algebraic Hecke
character `y ↦ a(y / ȳ) υ(y)^{-k} |y|^{j - k/2}`, with `υ` the fixed splitting character. At the
element `g` of the datum, `μ(g^c) μ(g) = cyc(g)^{2j - k}`. -/
lemma avatar_conjGal_mul_frob {a : AutChar D.E} {e : NumberField.InfinitePlace D.E → ℤ}
    {ψ : (w : FinPlace D.E) → MulChar (ResField w) ℂ} (ha : a.HasWeight e ψ) (k j : ℤ)
    (x : FrobeniusDatum D.E) (hψ : ψ x.place = 1) (hψ_star : ψ (star x.place) = 1)
    (hℓ : ↑ℓ ∉ x.place.asIdeal) :
    (ha.toAlgebraic k j).avatar (conjGal x.frob) * (ha.toAlgebraic k j).avatar x.frob =
      cyclotomicCharIn (PadicAlgCl ℓ) Ω ℓ x.frob ^ (2 * j - k) := by
  -- `conjGal x.frob` is a Frobenius at `star x.place`. The avatar at a Frobenius is `ιℓ` of the
  -- value of the Hecke character at the uniformiser.
  let coeff : FinPlace D.E → ℂ := heckeCoeff (ha.toAlgebraic k j).val.1 ∅
  -- In the product of the values at `star x.place` and `x.place` the factors from `a.baseChange`
  -- and `υ` cancel.
  have value_mul : coeff (star x.place) * coeff x.place = (x.place.q : ℂ) ^ (k - 2 * j) := by
    have bc_star : a.baseChange.atUniformizer (star x.place) =
      (a.baseChange.atUniformizer x.place)⁻¹ := atUniformizer_star hψ hψ_star
    have value (v : FinPlace D.E) :
        coeff v = a.baseChange.atUniformizer v * (υ.atUniformizer v ^ k)⁻¹ *
          (√v.q : ℂ) ^ (k - 2 * j) := by
      simp [coeff, HeckeChar.atUniformizer, heckeCoeff, toAlgebraic]
    have bc_ne : a.baseChange.atUniformizer x.place ≠ 0 := Units.ne_zero _
    have υ_cancel : υ.atUniformizer (star x.place) * υ.atUniformizer x.place = 1 := by
      rw [mul_comm, upsilon_atUniformizer_mul_star]
    simp [value, bc_star, υ_cancel, field, sq, ← mul_zpow, ← Complex.ofReal_mul]
  have cyc_eq : (cyclotomicCharIn (PadicAlgCl ℓ) Ω ℓ x.frob).val =
      (x.place.q : PadicAlgCl ℓ)⁻¹ := by
    simp [← cyclotomicInv_frob x hℓ, cyclotomicInv]
  have avatar_at : ((ha.toAlgebraic k j).avatar x.frob).val = ιℓ (coeff x.place) :=
    avatar_frob _ x.isPlaceOver hℓ (charUnramifiedAt_toAlgebraic hψ hψ_star k j) x.isFrob_inv
  have avatar_at_star :
      ((ha.toAlgebraic k j).avatar (conjGal x.frob)).val = ιℓ (coeff (star x.place)) :=
    avatar_frob _ x.isPlaceOver.conjPlace_star (by simpa)
      (charUnramifiedAt_toAlgebraic hψ_star (by rwa [star_star]) k j)
      (by simpa using x.isFrob_inv.conjPlace_conjGal)
  ext
  rw [val_mul, avatar_at, avatar_at_star, ← map_mul, value_mul, val_zpow_eq_zpow_val, cyc_eq]
  simp

/-- The ℓ-adic avatar μ of the algebraic Hecke character `a(x / x̄) υ(x)^{-k} |x|^{j - k/2}`
satisfies `μ(g^c) μ(g) = cyc(g)^{2j - k}` for all g. Here `a` is a character of `U(1)` of weight
`e` and tame part `ψ`, `υ` is the fixed splitting character, `cyc` is the cyclotomic character and
`g^c` is `New.conjGal g`. -/
lemma avatar_conjGal_mul_avatar {a : AutChar D.E} {e : NumberField.InfinitePlace D.E → ℤ}
    {ψ : (w : FinPlace D.E) → MulChar (ResField w) ℂ} (ha : a.HasWeight e ψ) (k j : ℤ)
    (g : Gal(Ω/D.E)) :
    (ha.toAlgebraic k j).avatar (conjGal g) * (ha.toAlgebraic k j).avatar g =
      cyclotomicCharIn (PadicAlgCl ℓ) Ω ℓ g ^ (2 * j - k) := by
  -- Both sides are continuous, so by density it suffices to check most Frobenius elements.
  have h_frob : ∀ᶠ x in mostFrobenii D.E,
      (ha.toAlgebraic k j).avatar (conjGal x.frob) * (ha.toAlgebraic k j).avatar x.frob =
        cyclotomicCharIn (PadicAlgCl ℓ) Ω ℓ x.frob ^ (2 * j - k) := by
    refine eventually_mostFrobenii
      (eventually_notMem_star_notMem ℓ ha.finite_ramification.toFinset) ?_
    intro x ⟨hw, hw_star, hℓ⟩
    have hψ : ψ x.place = 1 := by simpa using hw
    have hψ_star : ψ (star x.place) = 1 := by simpa using hw_star
    exact avatar_conjGal_mul_frob ha k j x hψ hψ_star hℓ
  exact (dense_of_mostFrobenii h_frob).induction (fun _ hg ↦ hg)
    (isClosed_eq (by fun_prop) (by fun_prop)) g

/-- Let `w` be a split place, `A` a place of `Ω`, and `a` a character of `U(1)` whose tame part `ψ`
is trivial at `w̄`. Let `μ` be the avatar of `y ↦ a(y / ȳ) υ(y)^{-k} |y|^{j - k/2}`, with `υ` the
fixed splitting character. Then inertia at `A` acts on `μ` through the label of `ψ w`, the element
of the residue field that names this character (`New.charName`) through
`T = faithfulChar (ResField w)`: an element with tame exponent `i` of level `f` at `A` over `w` is
killed by `X - ι (T^i label)`. -/
lemma isLabelledAt_avatar {a : AutChar D.E} {e : NumberField.InfinitePlace D.E → ℤ}
    {ψ : (w : FinPlace D.E) → MulChar (ResField w) ℂ} (ha : a.HasWeight e ψ) (k j : ℤ)
    {w : FinPlace D.E} {A : ClosurePlace} {f : ℕ} (hψ_star : ψ (star w) = 1) (hw : w.IsSplit) :
    let T : MulChar (AlgebraicClosure (ResField w)) ℂ := faithfulChar (ResField w)
    IsLabelledAt A T f (PolyKillsAt ((scalar (Fin 1)).comp (ha.toAlgebraic k j).avatar) A)
      (X - C (charName T (ψ w)).val) := by
  -- Let `s` have tame exponent `y`; it lies in inertia. By
  -- `avatarCompatAt_of_hasPrimitiveRoot5040`, `s` is the Artin image of a local unit `x` and is
  -- killed by `X - C (ιℓ c)`, with `c` the value of the character at `x`. This value is `ψ w` at
  -- the residue of `x`, which `IsTameExponent.pow_apply_charName` expresses by the label.
  intro T s y hy
  have ⟨hA, _, hs, _⟩ := hy
  obtain ⟨-, -, weil⟩ := avatarCompatAt_of_hasPrimitiveRoot5040 (ha.toAlgebraic k j) hA
  obtain ⟨x, hx : Valued.v x.1 = 1, hxs,
      (kills : PolyKillsAt ((scalar (Fin 1)).comp (ha.toAlgebraic k j).avatar) A s
        (X - C (ιℓ ((ha.toAlgebraic k j).val.1 (locIdele w x) : ℂ))))⟩ :=
    weil s 0 bot_le (inv_mem hs)
  have value : ((ha.toAlgebraic k j).val.1 (locIdele w x) : ℂ) =
      (T ^ y) (algebraMap _ (AlgebraicClosure (ResField w)) (charName T (ψ w)).val) := by
    rw [hy.pow_apply_charName _ hx hxs (ψ w)]
    simp [toAlgebraic, ha.baseChange_finPart_locIdele hw hψ_star hx,
      charUnramifiedAt_upsilon w x hx, hx]
  -- The only root of `X - C (charName T (ψ w))` is that name.
  simpa [T, value] using kills

end New.Selmer

/-!
## The chosen places of the level places

For the level places L = `D.levelPlaces ϑ`, the chosen places of L are chosen in the sense of
`New.Data.IsChosen`, lie above p₀ or p₁ and are outside the modulus of ϑ.
-/

/-- The tame part of a tame character `ϑ` is trivial at every chosen place
(`New.Data.IsChosen`). -/
lemma New.Data.TameChar.tamePart_eq_one_of_isChosen {P : Parameters} {D : Data P} (ϑ : D.TameChar)
    {v : FinPlace D.E} (hv : D.IsChosen v) : ϑ.tamePart v = 1 := by
  refine ϑ.tamePart_eq_one v fun hQ ↦ ?_
  -- The places of the modulus `ϑ.Q` are not chosen.
  obtain ⟨-, h_not_chosen, -⟩ := D.normQ_mem_and_notMem_of_mem_Q ϑ (.inl hQ)
  exact h_not_chosen hv

/-- Each chosen place of the level places `D.levelPlaces ϑ` is chosen in the sense of
`New.Data.IsChosen`. -/
lemma New.Data.isChosen_levelPlaces_chosenPlace {P : Parameters} (D : Data P) (ϑ : D.TameChar)
    (i : (D.levelPlaces ϑ).ChosenIndex) : D.IsChosen ((D.levelPlaces ϑ).chosenPlace i) := by
  obtain ⟨k, w, hw, -⟩ := i
  exact hw

/-- Each chosen place of the level places `D.levelPlaces ϑ` is chosen in the sense of
`New.Data.IsChosen`, the tame part of `ϑ` is trivial there, and it lies above `p₀` or `p₁`. -/
lemma New.Selmer.isChosen_chosenPlace {P : Parameters} {D : Data P} (ϑ : D.TameChar)
    (i : (D.levelPlaces ϑ).ChosenIndex) :
    D.IsChosen ((D.levelPlaces ϑ).chosenPlace i) ∧
    ϑ.tamePart ((D.levelPlaces ϑ).chosenPlace i) = 1 ∧
    (D.levelPlaces ϑ).chosenPlace i ∈ placesAboveM D :=
  have h_chosen : D.IsChosen ((D.levelPlaces ϑ).chosenPlace i) :=
    D.isChosen_levelPlaces_chosenPlace ϑ i
  ⟨h_chosen, ϑ.tamePart_eq_one_of_isChosen h_chosen, h_chosen.mem_placesAboveM⟩

namespace New.Selmer

/-!
## Hypotheses on conjugate self-dual representations for Selmer bounds

* `New.Selmer.twistError`: the number `e'_ℓ` of the twisting theorem.

`New.CoeffRing ℓ` are the rings of integers of finite Galois extensions of `ℚ_ℓ`, and
`∀ᶠ O in .atTop` means for all large ones; `New.ellVal` and `New.CoeffRing.normLength` are
normalised so that `ℓ` counts one.
-/

section RowColumnDefs

open Fintype GaloisRep Set

variable {ℓ : ℕ} [ThePrime ℓ] {P : Parameters} {D : Data P} [PadicIso ℓ]
  {n : Type} [Fintype n] [DecidableEq n]
  (t : ℕ) (J : (D.E →+* ℂ) → Multiset ℤ) (ψ : AbsGal D →* PadicAlgCl ℓ) (S : Set (FinPlace D.E))
  (R : GalRep ℓ D.E n)

/-- `R` is continuous, has non-degenerate trace form, and is conjugate self-dual up to twist,
`R^c ≅ R^∨(1 − t)`. Self-duality is stated on traces: `tr R(g^c) = cyc(g)^{1−t} tr R(g⁻¹)` for all
`g`, where `t = 0` is read as `t = 1`. -/
structure IsConjSelfDual : Prop where
  /-- `R` is continuous. -/
  continuous : Continuous R
  /-- The trace form on the span of the image of `R` is non-degenerate. -/
  nondeg : IsTraceNondeg R
  /-- Conjugate self-duality on traces: `tr R(g^c) = cyc(g)^{1 - t} tr R(g⁻¹)`, where
  `cyclotomicInv` is the inverse of the cyclotomic character `cyc`; `t = 0` is read as `t = 1`. -/
  trace_conj (g : Gal(Ω/D.E)) :
      (R (conjGal g)).1.trace = cyclotomicInv ℓ D.E (PadicAlgCl ℓ) g ^ (t - 1) * (R g⁻¹).1.trace

variable (ℓ D) in
/-- The negligible number `e'_ℓ = (4 f + 3) r v_ℓ(D.chosenGroupOrder) + 2 ^ (-ℓ)` that bounds the
Selmer groups, the ramification and the valuations of the `L`-values of a good twist. The integer
`New.Data.chosenGroupOrder` is the order of the product of `GL (D.r * D.t)` over the residue fields
at the chosen places. -/
noncomputable def twistError : NNReal :=
  (4 * D.f + 3) * D.r * padicValNat ℓ D.chosenGroupOrder + (1 / 2) ^ ℓ

/-- The Selmer group of a lattice `ρ` modulo `ℓ ^ m`: the continuous cocycles that are unramified
off `ℓ p₀ p₁`, `Q` and `Q̄`, lie in `H¹_f` above `ℓ` and vanish at the given element `γ`. The last
condition singles out one cocycle in each class when `ρ γ - 1` is invertible. -/
noncomputable def selmerCocycles {O : CoeffRing ℓ} (ρ : AbsGal D →* Matrix n n O)
    (Q : Finset (FinPlace D.E)) (m : ℕ)
    (γ : AbsGal D) : Submodule O (AbsGal D → n → QuotSpan (ℓ ^ m : ↑O)) :=
  selmerModule ρ (placesDividing D.E ℓ ∪ placesAboveM D ∪ .conjClosure Q) (crysRelations ρ)
    (QuotSpan (ℓ ^ m : ↑O)) ⊓ (LinearMap.proj γ).ker

section SelmerLength

variable (γ : AbsGal D) (ζ : intQpBar ℓ)

/-- `u`, `ψ'` and `ζ'` are models over `O` of `R`, `ψ` and `ζ`, and on the twisted lattice `ψ' u`
the element `γ` is the scalar `ζ'`. -/
structure IsTwistedLattice {O : CoeffRing ℓ} (u : AbsGal D →* Matrix n n O) (ψ' : AbsGal D →* O)
    (ζ' : ↑O) : Prop where
  /-- `ζ'` is `ζ`. -/
  scalar_eq : ζ'.1 = ζ
  /-- `u` is a lattice in `R`. -/
  isLatticeIn : IsLatticeIn R u
  /-- `ψ'` is `ψ`. -/
  twist_eq (g : AbsGal D) : ψ' g = ψ g
  /-- `γ` acts on the twisted lattice by the scalar `ζ'`. -/
  apply_eq_smul : twistRep (.id O) ψ' u γ = ζ' • 1
  /-- `ζ' - 1` is a unit. -/
  isUnit_sub_one : IsUnit (ζ' - 1)
  /-- `γ` lies in an inertia group above a place that does not divide `ℓ`. -/
  mem_inertiaAbove : γ ∈ inertiaAbove (placesDividing D.E ℓ)ᶜ

variable {ψ R γ ζ} in
omit [PadicIso ℓ] in
/-- The cyclotomic character is `1` at `γ`, which lies in inertia at a place not above `ℓ`. -/
lemma IsTwistedLattice.cyclotomicChar_eq_one {O : CoeffRing ℓ} {u : AbsGal D →* Matrix n n O}
    {ψ' : AbsGal D →* O} {ζ' : ↑O} (h : IsTwistedLattice ψ R γ ζ u ψ' ζ') :
    cyclotomicChar Ω ℓ γ = 1 :=
  cyclotomicChar_eq_one_of_mem_inertiaAbove h.mem_inertiaAbove

/-- Over all large coefficient rings, `R`, `ψ` and `ζ` have models `u`, `ψ'`, `ζ'` on whose twisted
lattice `γ` acts by the scalar `ζ'` (`IsTwistedLattice`). -/
def HasTwistedLattice : Prop :=
  ∀ᶠ O : CoeffRing ℓ in Filter.atTop,
    ∃ (u : AbsGal D →* Matrix n n O) (ψ' : AbsGal D →* O) (ζ' : ↑O),
      IsTwistedLattice ψ R γ ζ u ψ' ζ'

end SelmerLength

/-- The length of the Selmer group of a lattice `ρ` with coefficients in `Frac(O) / O`: the
continuous cocycles that are unramified off `ℓ p₀ p₁`, `Q` and `Q̄`, lie in `H¹_f` above `ℓ` and
vanish at `γ`. -/
noncomputable def crystallineSelmerLength {n : Type} [Fintype n] [DecidableEq n] {O : CoeffRing ℓ}
    (ρ : AbsGal D →* Matrix n n O) (Q : Finset (FinPlace D.E)) (γ : AbsGal D) : ℕ∞ :=
  divisibleSelmerLength ρ (placesDividing D.E ℓ ∪ placesAboveM D ∪ .conjClosure Q)
    (crysRelations ρ ∪ {Finsupp.single γ 1})

/-- Over all large coefficient rings `O` there are models `u`, `ψ'` and `ζ'` of `R`, `ψ` and `ζ`
such that `γ` acts on the twisted lattice `ψ' u` by the scalar `ζ'` (see `IsTwistedLattice`) and the
Selmer group of `ψ' u` with coefficients in `Frac(O) / O` has length at most `sel`, normalised by
`len O / ℓ = 1`. -/
def HasDivisibleSelmerLengthLe {n : Type} [Fintype n] [DecidableEq n]
    (ψ : AbsGal D →* PadicAlgCl ℓ) (R : GalRep ℓ D.E n) (Q : Finset (FinPlace D.E)) (γ : AbsGal D)
    (ζ : intQpBar ℓ) (sel : ENNReal) : Prop :=
  ∀ᶠ O : CoeffRing ℓ in Filter.atTop,
    ∃ (u : AbsGal D →* Matrix n n O) (ψ' : AbsGal D →* O) (ζ' : ↑O),
      IsTwistedLattice ψ R γ ζ u ψ' ζ' ∧
      O.normLength (crystallineSelmerLength (twistRep (.id O) ψ' u) Q γ) ≤ sel

omit [PadicIso ℓ] in
/-- Let `ρ` be a matrix representation over `O` of the absolute Galois group of `E = D.E`, `Q` a
finite set of places of `E` and `γ` an element of the Galois group. Consider the locally constant
cocycles for `ρ` that are unramified at the places prime to `ℓ p₀ p₁` and outside `Q` and `Q̄`, obey
the relations of the crystalline cocycles above `ℓ` (`crysRelations ρ`) and vanish at `γ`. The
module of those with coefficients in `O / ℓ ^ M` (`selmerCocycles`) is at most as long as the module
of those with coefficients in `Frac(O) / O`, whose length is `crystallineSelmerLength`. -/
lemma length_selmerCocycles_le_crystallineSelmerLength {n : Type} [Fintype n] [DecidableEq n]
    {O : CoeffRing ℓ} (ρ : AbsGal D →* Matrix n n O) (Q : Finset (FinPlace D.E)) (M : ℕ)
    (γ : AbsGal D) :
    Module.length O (selmerCocycles ρ Q M γ) ≤ crystallineSelmerLength ρ Q γ := by
  have h_sub : selmerCocycles ρ Q M γ ≤
      selmerModule ρ (placesDividing D.E ℓ ∪ placesAboveM D ∪ .conjClosure Q)
        (crysRelations ρ ∪ {Finsupp.single γ 1}) (QuotSpan (ℓ ^ M : ↑O)) := by
    rintro z ⟨⟨hz_obey, hz_const⟩, hzγ⟩
    refine ⟨mem_obeying.2 ?_, hz_const⟩
    rintro f (hf | hf | rfl)
    · exact mem_obeying.1 hz_obey f (.inl hf)
    · exact mem_obeying.1 hz_obey f (.inr hf)
    · simpa using hzγ
  exact (length_mono h_sub).trans (length_le_divisibleSelmerLength (NeZero.ne _))

omit [PadicIso ℓ] in
/-- A bound for the Selmer group with divisible coefficients comes with a twisted lattice. -/
lemma HasDivisibleSelmerLengthLe.hasTwistedLattice {n : Type} [Fintype n] [DecidableEq n]
    {ψ : AbsGal D →* PadicAlgCl ℓ} {R : GalRep ℓ D.E n} {Q : Finset (FinPlace D.E)} {γ : AbsGal D}
    {ζ : intQpBar ℓ} {sel : ENNReal} (h : HasDivisibleSelmerLengthLe ψ R Q γ ζ sel) :
    HasTwistedLattice ψ R γ ζ :=
  Filter.Eventually.mono h fun _ ⟨u, ψ', ζ', h_lattice, _⟩ ↦ ⟨u, ψ', ζ', h_lattice⟩

omit [PadicIso ℓ] in
/-- A bound for the Selmer group with divisible coefficients holds for every larger bound. -/
lemma HasDivisibleSelmerLengthLe.mono {n : Type} [Fintype n] [DecidableEq n]
    {ψ : AbsGal D →* PadicAlgCl ℓ} {R : GalRep ℓ D.E n} {Q : Finset (FinPlace D.E)} {γ : AbsGal D}
    {ζ : intQpBar ℓ} {sel sel' : ENNReal} (h : HasDivisibleSelmerLengthLe ψ R Q γ ζ sel)
    (h_le : sel ≤ sel') : HasDivisibleSelmerLengthLe ψ R Q γ ζ sel' :=
  Filter.Eventually.mono h fun _ ⟨u, ψ', ζ', h_lattice, h_len⟩ ↦
    ⟨u, ψ', ζ', h_lattice, h_len.trans h_le⟩

variable (D)

/-- A conjugate self-dual representation of level `S`: `R` satisfies `IsConjSelfDual`, and three
local conditions hold at every place `v` that is outside `S` or divides `ℓ p₀ p₁`. -/
structure IsConjSelfDualOfLevel : Prop extends IsConjSelfDual t R where
  /-- At every place `v` off `S` or above `ℓ p₀ p₁`, and every `A` over `v`: `R` is trivial on
  inertia near `1` (potentially crystalline above `ℓ`), has jumps `J` (`HasJumpsAt R A J`, read
  through the isomorphism fixed by the instance `New.PadicIso ℓ`), and is unramified (crystalline
  above `ℓ`) if `v` is prime to `p₀ p₁`. -/
  local_conditions : ∀ v ∉ S \ (placesDividing D.E ℓ ∪ placesAboveM D), ∀ ⦃A : ClosurePlace⦄,
    IsPlaceOver A v →
    IsFiniteTypeAt R A ∧ HasJumpsAt R A J ∧ (v ∉ placesAboveM D → GaloisRep.IsGoodAt R A)

/-- A main summand: a conjugate self-dual representation of empty level whose jumps satisfy
`IsMainSummandWeights`, with four more conditions. At the places above `p₀ p₁` prime to `ℓ`, a power
prime to the place kills the image of inertia and two determinants have bounded valuation. The image
of a lattice spans all matrices, and it contains a scalar with prescribed cyclotomic character. Some
inertia element acts by a scalar of large order modulo the maximal ideal. -/
structure IsMainSummandLike : Prop extends IsConjSelfDualOfLevel D t J ∅ R,
  IsMainSummandWeights D (card n) t J where
  /-- At every `A` over a place `v ∣ p₀ p₁` prime to `ℓ`, there are an inertia element `γ` and an
  integer `N` prime to `v` such that `R` is trivial on the `N`-th powers of inertia, and
  `det (R γ - 1)` and `det (R (γ^c)⁻¹ - 1)` have valuation at most `card n` times that of
  `D.chosenGroupOrder`. If `v` is a chosen place, `γ` is the tame generator `hA.tameGenerator`. -/
  inertia_above_M : ∀ v ∈ placesAboveM D \ placesDividing D.E ℓ,
    ∀ ⦃A : ClosurePlace⦄ (hA : IsPlaceOver A v), ∃ (γ : inertiaGroup Gal(Ω/D.E) A) (N : ℕ),
    (D.IsChosen v → γ = hA.tameGenerator) ∧
    A.valuation N.cast = 1 ∧
    (∀ s ∈ inertiaGroup Gal(Ω/D.E) A, R (s ^ N) = 1) ∧
    ellVal ((R γ).val - 1).det ≤ card n * padicValNat ℓ D.chosenGroupOrder ∧
    ellVal ((R (conjGal γ.val)⁻¹).val - 1).det ≤ card n * padicValNat ℓ D.chosenGroupOrder
  /-- For all large coefficient rings `O`, the image of every lattice `u` in `R` spans all matrices
  over `O`. -/
  span_eq_top : ∀ᶠ O : CoeffRing ℓ in Filter.atTop, ∀ u : Gal(Ω/D.E) →* Matrix n n O,
    IsLatticeIn R u → Submodule.span O (Set.range u) = ⊤
  /-- For all large coefficient rings `O` and every lattice `u` in `R` over `O`, some `g` with
  cyclotomic character `p₀ ^ card n` or `p₁ ^ card n` acts on `u` by a scalar. -/
  exists_scalar_cyclotomicChar : ∀ᶠ O : CoeffRing ℓ in Filter.atTop,
    ∀ u : Gal(Ω/D.E) →* Matrix n n O, IsLatticeIn R u →
    ∃ (g : Gal(Ω/D.E)) (i : Fin 2) (α : ↑O),
      (cyclotomicChar Ω ℓ g).val = D.levelPrime i ^ card n ∧ u g = α • 1
  /-- Some inertia element at a place above `p₀` or `p₁` and prime to `ℓ` acts by a scalar `y` such
  that `y ^ (ℓ ^ a * j) - 1` is a unit for all `a` and `1 ≤ j ≤ 4 * card n + 2`. -/
  exists_scalar_inertia :
      ∃ᵉ (γ ∈ inertiaAbove (placesAboveM D \ placesDividing D.E ℓ)) (y : PadicAlgCl ℓ),
        (R γ).val = y • 1 ∧ ∀ᵉ (a : ℕ) (j ∈ Icc 1 (4 * card n + 2)), ‖y ^ (ℓ ^ a * j) - 1‖ = 1

variable {D t J R}

/-- Let `R` be a main summand (`IsMainSummandLike`) of rank `card n`. For all large coefficient
rings `O`, the image of every lattice `u` in `R` spans all matrices over `O`, and some `g` with
cyclotomic character `p₀ ^ card n` or `p₁ ^ card n` acts on `u` by a scalar. -/
theorem IsMainSummandLike.eventually_span_eq_top_and_exists_eq_smul_one
    (hR : IsMainSummandLike D t J R) :
    ∀ᶠ O : CoeffRing ℓ in Filter.atTop, ∀ u : Gal(Ω/D.E) →* Matrix n n O, IsLatticeIn R u →
      Submodule.span O (Set.range u) = ⊤ ∧
      ∃ (g : Gal(Ω/D.E)) (i : Fin 2) (α : ↑O),
        (cyclotomicChar Ω ℓ g).val = D.levelPrime i ^ card n ∧ u g = α • 1 := by
  filter_upwards [hR.span_eq_top, hR.exists_scalar_cyclotomicChar] with O h_span h_scalar u hu
  exact ⟨h_span u hu, h_scalar u hu⟩

/-- A main summand `R` (`IsMainSummandLike`) is residually absolutely irreducible: for all large
coefficient rings `O`, every lattice `u` in `R` and every ring map `f` from `O` to a field `k`, the
only subspaces of `kⁿ` stable under all `f (u g)` are `0` and `kⁿ`. -/
theorem IsMainSummandLike.eventually_eq_bot_or_eq_top (hR : IsMainSummandLike D t J R) :
    ∀ᶠ O : CoeffRing ℓ in Filter.atTop, ∀ u : Gal(Ω/D.E) →* Matrix n n O, IsLatticeIn R u →
      ∀ (k : Type) [Field k] (f : O →+* k) (U : Submodule k (n → k)),
        (∀ g : Gal(Ω/D.E), ∀ v ∈ U, ((u g).map f).mulVec v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  filter_upwards [hR.span_eq_top] with O h_span u hu k _ f U h_stable
  exact eq_bot_or_eq_top_of_span_eq_top f (h_span u hu) U h_stable

/-- Let `R` be a main summand: an `ℓ`-adic representation of the Galois group of `D.E` with
`R^c ≅ R^∨(1 - t)` on traces and Hodge–Tate jumps `J`, such that, among other conditions, the image
of each lattice over a large coefficient ring `O` spans all matrices. Then the stable lattice is
unique up to scalars, for all large `O`: if `R` has matrices `u g` over `O` in the basis `Q` and
`u' g` over `O` in the basis `Q'`, then `Q' = α Q k` with a scalar `α` and `k` in `GL_n(O)`. -/
theorem IsMainSummandLike.eventually_lattice_unique {ℓ : ℕ} [ThePrime ℓ] {P : Parameters}
    {D : Data P} [PadicIso ℓ] {n : Type} [Fintype n] [DecidableEq n] {t : ℕ}
    {J : (D.E →+* ℂ) → Multiset ℤ} {R : GalRep ℓ D.E n} (hR : IsMainSummandLike D t J R) :
    ∀ᶠ O : CoeffRing ℓ in Filter.atTop,
      ∀ (u u' : Gal(Ω/D.E) →* Matrix n n O) (Q Q' : GL n (PadicAlgCl ℓ)),
        (∀ g : Gal(Ω/D.E), (Q⁻¹ * R g * Q).val = (u g).map O.val.val) →
        (∀ g : Gal(Ω/D.E), (Q'⁻¹ * R g * Q').val = (u' g).map O.val.val) →
        ∃ (α : (PadicAlgCl ℓ)ˣ) (k : GL n O), Q'.val = α.val • (Q.val * k.val.map O.val.val) := by
  -- The change of basis `Q⁻¹ * Q'` conjugates `u` to `u'`, and `u` spans all matrices over `O`.
  filter_upwards [hR.span_eq_top] with O h_span u u' Q Q' hQ hQ'
  have h_conj (g : Gal(Ω/D.E)) :
      (Q⁻¹ * Q')⁻¹.val * (u g).map O.val.val * (Q⁻¹ * Q').val = (u' g).map O.val.val := by
    have h_group : (Q⁻¹ * Q')⁻¹ * (Q⁻¹ * R g * Q) * (Q⁻¹ * Q') = Q'⁻¹ * R g * Q' := by group
    rw [← hQ g, ← hQ' g, ← h_group, ← Units.val_mul, ← Units.val_mul]
  obtain ⟨α, k, h_eq⟩ := exists_eq_smul_of_conj_eq (h_span u ⟨Q, hQ⟩) (Q⁻¹ * Q') h_conj
  exact ⟨α, k, by rw [← Matrix.mul_smul, ← h_eq, Units.val_mul, Units.mul_inv_cancel_left]⟩

end RowColumnDefs

/-!
## The normalising character, lift settings, main summands and representations of a type

Conventions: a label is a polynomial over the residue field at a place of `O.chosenPlace`.

* `New.Selmer.normalizingAvatar`, `New.Selmer.normalizingAvatar_eq_of_isFrob_inv`,
  `New.Selmer.normalisedRep`: the normalising character, its Frobenius values, and the twist of a
  representation by it.
-/

section AptTupleDefs

open Polynomial Fintype Set GaloisRep AlgHeckeChar AutChar

variable {ℓ : ℕ} [ThePrime ℓ] {P : Parameters} {D : Data P} [PadicIso ℓ] {r n : Type}
  {m : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-! ### The normalising character -/

/-- The ℓ-adic avatar of the algebraic Hecke character built from the inverse of the character
`O.charW`, with weight `-card r`. Here `card r` is the dimension of the space `W` of `O`. It
normalises the representations attached to forms on `V`, which has dimension `card n`. -/
abbrev normalizingAvatar (O : DescentPair D.E r n) : Gal(Ω/D.E) →* (PadicAlgCl ℓ)ˣ :=
  ((HasWeight.inv (μ := O.charW)).toAlgebraic (-card r) 0).avatar

omit [DecidableEq n] in
/-- The value of the normalising character `New.Selmer.normalizingAvatar O` at `s` when `s⁻¹` fixes
a place `A` over `w ∤ ℓ` and acts there as the `d`-th power of Frobenius: it is the `d`-th power of
the image under the fixed isomorphism `ιℓ` of the inverse of `O.charW.frobValue r w`, the value at a
uniformiser at `w` of the Hecke character of `W` made from `O.charW`, times `q_w ^ (card r / 2)`. -/
lemma normalizingAvatar_eq_of_isFrob_inv {O : DescentPair D.E r n} {w : FinPlace D.E}
    {A : ClosurePlace} (hA : IsPlaceOver A w) (hℓ : ↑ℓ ∉ w.asIdeal) (d : ℕ) {s : AbsGal D}
    (hs : IsFrob A (w.q ^ d) s⁻¹) :
    normalizingAvatar O s = ιℓ (O.charW.frobValue r w)⁻¹ ^ d := by
  -- `s` is the local Artin symbol of some `z` of valuation `exp (-d)`. Off `ℓ` the avatar at `s` is
  -- `ιℓ` of the character at `z`. The character is unramified, so this is the `d`-th power of its
  -- value at the uniformiser `uniformizer w`, and that value unfolds to `frobValue⁻¹`.
  obtain ⟨z, hz : Valued.v z.val = WithZero.exp (-(d : ℤ)), h_art⟩ :=
    hA.exists_localArtin_eq_of_isFrob_pow hs
  let θ := (HasWeight.inv (μ := O.charW)).toAlgebraic (-card r) 0
  have h_unif : ((θ.val.1 (locIdele w (uniformizer w)) : ℂˣ) : ℂ) = (O.charW.frobValue r w)⁻¹ := by
    -- Both sides are the same product of values of `O.charW`, `υ` and `√q_w`.
    simp [θ, frobValue, AutChar.spaceChar, HasWeight.toAlgebraic, HeckeChar.atUniformizer]
    ring
  have h_unr : CharUnramifiedAt θ.val.1 w :=
    HasWeight.charUnramifiedAt_toAlgebraic (by simp) (by simp) _ _
  rw [avatar_localArtin _ hA (.inl hℓ) h_art, h_unr.apply_locIdele_eq_zpow z, hz]
  simp [θ, ← h_unif]

variable (O : DescentPair D.E r n) (k : ℕ) (J : (D.E →+* ℂ) → Multiset ℤ)
  (c : ∀ i : O.ChosenIndex, (ResField (O.chosenPlace i))[X]) (S : Set (FinPlace D.E))
  (R : GalRep ℓ D.E m)

/-- The normalised representation: R twisted by the character `New.Selmer.normalizingAvatar`. -/
abbrev normalisedRep (R : Gal(Ω/D.E) →* GL n (PadicAlgCl ℓ)) : Gal(Ω/D.E) →* GL n (PadicAlgCl ℓ) :=
  twistByChar (m := n) (normalizingAvatar O) R

/-! ### Scaled type polynomials -/

/-- The label c_i with its roots multiplied by the element of the residue field that names
(`New.charName`) the character `(O.tamePart w)⁻¹`, where `w = O.chosenPlace i`. -/
def scaledTypePoly (i : O.ChosenIndex) : (ResField (O.chosenPlace i))[X] :=
  (c i).scaleRoots
    (charName (faithfulChar (ResField (O.chosenPlace i))) (O.tamePart (O.chosenPlace i))⁻¹).1

/-- The descent pair `O` with the labels `c` is a lift setting for the twist `ϑ`. Conditions on the
pair: its places are `D.levelPlaces ϑ`. Its character `O.tamePart` is `D.chiMLocal ^ j * ϑ.tamePart`
with `1 ≤ j ≤ D.m`. The numbers `card r` and `O.rankDiff` are odd, with `card r ≤ D.r` and
`O.rankDiff ≤ D.t`. Conditions on the labels: each `c i` is a label of degree `card r`. Its scaled
type polynomial (`New.Selmer.scaledTypePoly`) does not have `1` as a root. Over each prime
`D.levelPrime k`, one of the labels is primitive with `card r = D.r`, or is `X - 1` with
`card r = 1`. -/
structure IsLiftSetting (ϑ : D.Twist) where
  /-- The places of `O` are those of `D.levelPlaces ϑ`. -/
  toLevelPlaces_eq : O.toLevelPlaces = D.levelPlaces ϑ
  /-- The character `O.tamePart` is `D.chiMLocal ^ j * ϑ.tamePart` for some `1 ≤ j ≤ D.m`. -/
  exists_tamePart_eq_chiMLocal_zpow_mul : ∃ j ∈ Icc 1 D.m,
    O.tamePart = D.chiMLocal ^ (j : ℤ) * ϑ.tamePart
  /-- The rank `card r` and the number `O.rankDiff` are odd. -/
  odd : Odd (card r) ∧ Odd O.rankDiff
  /-- `card r ≤ D.r` and `O.rankDiff ≤ D.t`. -/
  rank_le : card r ≤ D.r ∧ O.rankDiff ≤ D.t
  /-- Each `c i` is a label of degree `card r`. -/
  isLabel (i : O.ChosenIndex) : IsLabel (card r) (c i)
  /-- Over each prime `D.levelPrime k` there is a place `O.chosenPlace i` where either
  `card r = D.r` and `c i` is a primitive polynomial (`IsPrimitivePolynomial`), or `card r = 1` and
  `c i = X - 1`. -/
  exists_primitive_or_one (k : Fin 2) : ∃ i : O.ChosenIndex,
    ↑(D.levelPrime k) ∈ (O.chosenPlace i).1 ∧
    (card r = D.r ∧ IsPrimitivePolynomial (card r) (c i) ∨ card r = 1 ∧ c i = X - 1)
  /-- The scaled type polynomial `New.Selmer.scaledTypePoly O c i` does not have `1` as a root. -/
  not_isRoot_scaledTypePoly (i : O.ChosenIndex) : ¬(scaledTypePoly O c i).IsRoot 1

open scoped Classical in
/-- The endomorphism of the space of forms given by the action of the group-algebra idempotent
attached to the tuple of labels c. -/
abbrev typeProjection : Module.End ℂ O.FormV := O.groupAlgAction (tupleIdem r c)

/-- The trace of `u` is `ψ · tr R + ∑_{e < t} cyc⁻¹ ^ e`: on traces, `u` is the sum of the twist
`ψ R` and the first `t` powers of the inverse cyclotomic character. -/
def HasLiftTrace (ψ : AbsGal D →* PadicAlgCl ℓ) (R : GalRep ℓ D.E m) (t : ℕ)
    (u : GalRep ℓ D.E n) : Prop :=
  ∀ g : AbsGal D, (u g).val.trace =
    ψ g * (R g).val.trace + ∑ e ∈ Finset.range t, cyclotomicInv ℓ D.E (PadicAlgCl ℓ) g ^ e

/-- `R` is a main summand (`IsMainSummandLike`), and it serves all twists of `O`: if the character
of a descent pair `V` is `O.u1Char` twisted by `ϑ` and the eigenform `y` for `V` lifts the system of
Hecke eigenvalues `z`, then on traces the normalised representation attached to `y` is the sum of
`ψ R` and the first `V.rankDiff` powers of the inverse cyclotomic character (`HasLiftTrace`), with
`ψ` the avatar of `ϑ⁻¹`. -/
def IsMainSummand (z : FinPlace D.E → ℕ → ℂ) (R : GalRep ℓ D.E r) : Prop :=
  -- (a) `R` is a main summand for some jumps `τ`
  (∃ τ : (D.E →+* ℂ) → Multiset ℤ, IsMainSummandLike D O.rankDiff τ R) ∧
  -- (b) the trace identity, for all data `V` whose character is `O.u1Char` twisted by `ϑ`
  ∀ {ϑ : D.TameChar} {V : DescentPair D.E r n} {y : V.FormV} {H : FinPlace D.E → ℂ[X]}
    {S : GalRep ℓ D.E n},
    V.u1Char = O.u1Char * ϑ.toAutChar → V.HasLiftHeckePolynomial y z → IsEigenform y H →
      Attached H S → HasLiftTrace ϑ.invAvatar R V.rankDiff (normalisedRep V S)

/-- A representation of a type: `R` is conjugate self-dual of twist `1 - k`, jumps `J` and level `S`
(`New.Selmer.IsConjSelfDualOfLevel`), and inertia at the place `O.chosenPlace i` acts through the
roots of the label `c i`, a polynomial over the residue field. -/
structure IsRepOfType extends IsConjSelfDualOfLevel (n := m) D k J S R where
  /-- At each place `A`, an element of inertia over `O.chosenPlace i` is killed by the polynomial
  that `IsLabelledAt` makes from the label `c i` and the tame exponent at level `(card r)!`. -/
  labelled ⦃i : O.ChosenIndex⦄ ⦃A : ClosurePlace⦄ :
      IsLabelledAt A (faithfulChar (ResField (O.chosenPlace i))) (card r).factorial
        (PolyKillsAt R A) (c i)

end AptTupleDefs

/-!
## Lift settings, label idempotents, and split places off the level

Small facts used with a descent pair `O` (`New.DescentPair`) and a tuple `c` of polynomials over the
residue fields at the places `O.chosenPlace i`. Only `New.Selmer.IsLiftSetting.card_le` and
`New.Selmer.IsLiftSetting.isChosen_chosenPlace` assume that the tuple is a lift setting for a twist
(`New.Selmer.IsLiftSetting`). The other facts hold for any tuple `c`.

* `New.Selmer.IsLiftSetting.isSymmetric_typeProjection`,
  `New.Selmer.IsLiftSetting.typeProjection_eq_self_of_mem_range`,
  `New.Selmer.IsLiftSetting.range_typeProjection_mem_invtSubmodule`: the idempotent
  `typeProjection O c` is self-adjoint and fixes its range. Its range is stable under the Hecke
  polynomials `O.heckePolyOnForms` off the level.
-/

section AptTuples

open Fintype GaloisRep Gf Module.End LinearMap

variable {P : Parameters} {D : Data P}
  {r n : Type} [Fintype r] [DecidableEq r] [Fintype n]

section Labels

variable {O : DescentPair D.E r n}
  {c : (i : O.ChosenIndex) → Polynomial (ResField (O.chosenPlace i))} {ϑ : D.Twist}

/-- If the labels `c` form a lift setting for the twist `ϑ` (`New.Selmer.IsLiftSetting`), the
dimension `card n` of the space `V` of the descent pair is at most twice the rank
`D.n D.m = D.k + D.m * (D.t + 1)`. -/
lemma IsLiftSetting.card_le (hc : IsLiftSetting O c ϑ) : card n ≤ 2 * D.n D.m := by
  -- `card n ≤ D.r + D.t` with `D.t = 5 * D.r`, while `D.n D.m ≥ D.m * D.t ≥ 10000 * D.t`.
  have h_card : card n ≤ D.r + D.t := by grind [hc.rank_le]
  grind [Data.n, mul_le_mul_left D.ten_thousand_le_m D.t]

/-- If the labels `c` form a lift setting for the twist `ϑ` (`New.Selmer.IsLiftSetting`), every
place `O.chosenPlace i` of the descent pair is chosen in the sense of `New.Data.IsChosen`. -/
lemma IsLiftSetting.isChosen_chosenPlace (hc : IsLiftSetting O c ϑ) (i : O.ChosenIndex) :
    D.IsChosen (O.chosenPlace i) := by
  obtain ⟨j, hj⟩ : O.chosenPlace i ∈ Set.range (D.levelPlaces ϑ).chosenPlace := by
    rw [← hc.toLevelPlaces_eq]
    exact Set.mem_range_self i
  exact hj.subst (D.isChosen_levelPlaces_chosenPlace ϑ j)

open scoped Classical in
/-- The idempotent `typeProjection O c`, by which the tuple of labels `c` acts on the forms on the
space `V` of the descent pair `O`, is self-adjoint. -/
lemma IsLiftSetting.isSymmetric_typeProjection [DecidableEq n] : (typeProjection O c).IsSymmetric :=
  O.innerAt_groupAlgAction (isCentralProj_tupleIdem c) _

open scoped Classical in
/-- The idempotent `typeProjection O c` fixes every form `y` in its range. -/
lemma IsLiftSetting.typeProjection_eq_self_of_mem_range [DecidableEq n] {y : O.FormV}
    (hy : y ∈ (typeProjection O c).range) : typeProjection O c y = y :=
  (LinearMap.IsIdempotentElem.mem_range_iff ((isCentralProj_tupleIdem c).1.map _)).1 hy

end Labels

/-- Let `c` be a tuple of polynomials over the residue fields at the chosen places of the descent
pair `O`, and `typeProjection O c` the idempotent by which the tensor product of their label
idempotents (`New.tupleIdem`) acts on the forms on `V`. Let `w` be a split place such that neither
`w` nor its conjugate is among the places of `O`. For every complex number `x`, the range of
`typeProjection O c` is stable under the Hecke polynomial at `w` evaluated at `x`, the operator
`∑_{i ≤ card n} (-x) ^ i q ^ (i (i - 1) / 2) T_{w,i}`, with `q` the norm of `w` and `T_{w,i}` the
Hecke operators at `w`. -/
lemma IsLiftSetting.range_typeProjection_mem_invtSubmodule {O : DescentPair D.E r n}
    {c : (i : O.ChosenIndex) → Polynomial (ResField (O.chosenPlace i))} [DecidableEq n]
    {w : FinPlace D.E} (hw : star w ≠ w) (hw_places : w ∉ O.places.conjClosure) (x : ℂ) :
    (typeProjection O c).range ∈ (O.heckePolyOnForms hw hw_places x).invtSubmodule := by
  -- It suffices that the action of each group element `g` on forms commutes with the Hecke
  -- polynomial. Up to a scalar it is translation by an element that is trivial at `w` and `star w`;
  -- this commutes with the translations by elements `u` supported there, which is enough by
  -- `map_heckePolyOp`.
  refine O.range_groupAlgAction_mem_invtSubmodule fun g ↦ LinearMap.ext fun y ↦ Subtype.ext ?_
  have h_off : ↑(liftResidue (firstBlockHom O.toLevelPlaces O.incl g)) ∈ trivialOn n {w} := by
    grind [liftResidue, mem_trivialOn, mem_supportedOn]
  have h_comm (u : Gf D.E n) (hu : u ∈ supportedOn n {w}) :
      Commute u ↑(liftResidue (firstBlockHom O.toLevelPlaces O.incl g)) :=
    commute_supportedOn_trivialOn hu h_off
  -- The action of `g` is a scalar multiple of this translation, so both pass through the operator.
  refine (map_smul ..).trans (congrArg _ (map_heckePolyOp (algFormRep _ _ _) x fun u hu ↦ ?_).symm)
  rw [← mul_apply, ← (h_comm u hu).map, mul_apply]

/-- Infinitely many places of `E` are split and are, with their conjugates, outside the places of
the descent pair `O`. -/
lemma frequently_isSplit_notMem_places (O : DescentPair D.E r n) :
    ∃ᶠ w : FinPlace D.E in Filter.cofinite, w.IsSplit ∧ w ∉ O.places.conjClosure := by
  classical
  -- Places of prime norm are split and infinite in number; finitely many lie in
  -- `O.places.conjClosure`.
  exact frequently_prime_q.mp ((eventually_notMem_star_notMem 1 O.places.toFinset).mono
    fun w h_off h_prime ↦ ⟨isSplit_of_q_prime h_prime, by grind⟩)

end AptTuples

end New.Selmer

end
