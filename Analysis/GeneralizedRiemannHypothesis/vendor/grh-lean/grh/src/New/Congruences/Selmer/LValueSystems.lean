import New.Congruences.Selmer.ClassSums
import New.Congruences.Selmer.StickelbergerSystems

/-!
# The Stickelberger systems of the L-values

The integral measure of a ramified pair is mapped to the group rings of the class groups `Cl_Q`. Its
Euler factors give the norm relation, and its values at twists give the ratios of `L`-values. In
this file `ϑ` is the character of the system, `τ` a tame character and `ξ` a twist.

* `New.Data.CriticalPair.stickelbergerChar`: the character `ϑ` of the system.
* `New.Selmer.exists_stickelbergerSystem_β_le_and_norm_eq`: the system of a ramified pair and a
  sign.

Notions from other files:
* `New.Selmer.StickelbergerSystem`: elements `Θ_Q` of the group rings of the class groups `Cl_Q`
  with a norm relation. Its number `β` is `v(1(Θ_∅)) + ∑_e 2 v(ϑ(g) - 1)`, over the exponents `e`,
  where `g` is the Galois element of the system and `v` is `ellVal`, the `ℓ`-adic valuation
  truncated below at `0`.
* `badPlaces D ℓ`: for the data `D` (a number field `E` and primes `p₀`, `p₁`, `N`), the finite
  set of places of `E` dividing `ℓ p₀ p₁ N`. A modulus is auxiliary if its places have prime norm
  and it is disjoint from this set, from the conjugate of this set and from its own conjugate.
* `New.Data.CriticalPair.ratio`: the ratio |L(z, (ντ^δ)⁻¹)| / |L(z, ν⁻¹)| for a tame character τ and
  a sign δ. Both L-functions omit the Euler factors at the chosen places and their conjugates; the
  numerator also omits those at the places of the modulus of τ and their conjugates.
* `New.IsFromU1`: a Galois character `ψ` is a character for `Q` if `ψ(Art x) = η(x / x̄)` for an
  idele class character `η` of modulus `Q` that is trivial at the places over `ℓ`.
* `New.Data.CriticalPair.IsTwistMeasure`: values, one for each tame character, that are an integral
  measure, take Euler factors when a place is added and give powers of the ratio at twists.

## Relation to the literature

See `New.Congruences.Selmer.TwistingTheorem` for related work.
-/

open New Finset WeilData HeckeChar Data AlgHeckeChar AutChar HasWeight Unitary
open scoped NumberField

namespace New.Selmer

variable {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ]

omit [PadicIso ℓ] in
/-- Let `p₀`, `p₁` and `N` be the three primes of the data `D` and `E` its number field. A place `v`
of `E` outside `badPlaces D ℓ`, the finite set of places dividing `ℓ p₀ p₁ N`, does not lie over
`ℓ`, and neither `v` nor its conjugate is chosen (the chosen places divide a fixed integer of norm
`p₀ p₁`). -/
lemma not_isChosen_of_notMem_badPlaces {v : FinPlace D.E} (hv : v ∉ badPlaces D ℓ) :
    (ℓ : 𝓞 D.E) ∉ v.asIdeal ∧ ¬D.IsChosen v ∧ ¬D.IsChosen (star v) := by
  have h_bad : v ∉ placesDividing D.E ℓ ∪ placesAboveM D :=
    fun h ↦ hv (placesDividing_union_subset_badPlaces D ℓ h)
  exact ⟨fun h ↦ h_bad (.inl h), fun h ↦ h_bad (.inr h.mem_placesAboveM),
    fun h ↦ h_bad (.inr (star_mem_placesAboveM.1 h.mem_placesAboveM))⟩

/-- A pair `p = (ν, z)` consists of a character `ν` of `U(1)(𝔸)` and an integer `z`. For such a pair
and a sign `δ` this is `ϑ`: the `ℓ`-adic Galois character (avatar) that class field theory attaches
to the algebraic Hecke character of `E` given by the base change of `ν ^ (-δ)`. -/
noncomputable def _root_.New.Data.CriticalPair.stickelbergerChar (p : D.CriticalPair) (δ : ℤˣ) :
    AbsGal D →* (PadicAlgCl ℓ)ˣ :=
  ((p.hasWeight.zpow (-δ : ℤˣ)).toAlgebraic 0 0).avatar

omit [PadicIso ℓ] in
/-- Let `p = (ν, z)` be a pair, so that the residue characters of `ν` are trivial outside the chosen
places, and `δ` a sign. The algebraic Hecke character of the base change of `ν ^ (-δ)` to the field
`E` of the data `D` is unramified at every place outside `badPlaces D ℓ`, the places dividing
`ℓ p₀ p₁ N`, where `p₀`, `p₁` and `N` are the three primes of `D`. -/
lemma charUnramifiedAt_zpow_neg_of_notMem_badPlaces (p : D.CriticalPair) (δ : ℤˣ) {v : FinPlace D.E}
    (hv : v ∉ badPlaces D ℓ) :
    CharUnramifiedAt ((p.hasWeight.zpow (-δ : ℤˣ)).toAlgebraic 0 0).character v := by
  obtain ⟨-, hv_not_chosen, hv_star_not_chosen⟩ := not_isChosen_of_notMem_badPlaces hv
  exact (p.hasWeight.zpow _).charUnramifiedAt_toAlgebraic
    (by simp [p.tamePart_eq_one, hv_not_chosen])
    (by simp [p.tamePart_eq_one, hv_star_not_chosen]) 0 0

/-- Let `ℓ` be a prime, `p = (ν, z)` a pair and `δ` a sign, and let `ϑ = p.stickelbergerChar δ` be
the `ℓ`-adic Galois character attached to the base change of `ν ^ (-δ)` to the field `E` of the data
`D`. Then `ϑ` is trivial on the inertia groups at all places outside `badPlaces D ℓ`, the places
dividing `ℓ p₀ p₁ N`, where `p₀`, `p₁` and `N` are the three primes of `D`. -/
lemma stickelbergerChar_eq_one_of_mem_inertiaAbove (p : D.CriticalPair) (δ : ℤˣ) {g : AbsGal D}
    (hg : g ∈ inertiaAbove (badPlaces D ℓ : Set (FinPlace D.E))ᶜ) :
    p.stickelbergerChar (ℓ := ℓ) δ g = 1 := by
  obtain ⟨v, hv, A, hA, hg⟩ := hg
  -- The class of `g` is the local Artin symbol of a unit `x` at `v`.
  obtain ⟨x, hx_unit, hx⟩ := hA.exists_localArtin_eq (inv_mem hg) 0
  have hx_one : ((p.hasWeight.zpow (-δ : ℤˣ)).toAlgebraic 0 0).character (locIdele v x) = 1 :=
    charUnramifiedAt_zpow_neg_of_notMem_badPlaces p δ hv x (by simpa using hx_unit)
  ext
  rw [CriticalPair.stickelbergerChar, avatar_localArtin _ hA
    (.inl (not_isChosen_of_notMem_badPlaces hv).1) hx,
    hx_one]
  simp

/-- Let `p = (ν, z)` be a ramified pair: the residue characters of `ν` are nontrivial exactly at the
chosen places, which divide a fixed integer of norm `p₀ p₁`. Let `w` be a chosen place not above
`ℓ`, let `δ` be a sign and let `ϑ = p.stickelbergerChar δ` be the `ℓ`-adic Galois character attached
to the base change of `ν ^ (-δ)`. At the tame generator of `w` (an inertia element) the value of
`ϑ` is not `1` and is a root of unity of order dividing `N w - 1`, with `N w` the norm of `w`. -/
lemma stickelbergerChar_tameGenerator_ne_one_and_pow_eq_one {w : FinPlace D.E} (hw : D.IsChosen w)
    (hℓ : w ∉ placesDividing D.E ℓ) {p : D.CriticalPair} (hp : p.IsRamified) (δ : ℤˣ) :
    p.stickelbergerChar (ℓ := ℓ) δ w.isPlaceOver_placeOver.tameGenerator ≠ 1 ∧
      p.stickelbergerChar (ℓ := ℓ) δ w.isPlaceOver_placeOver.tameGenerator ^ (w.q - 1) = 1 := by
  -- `x` is a local unit with Artin symbol the tame generator; its residue `γ` generates the units
  -- of the residue field.
  obtain ⟨x, hx_mem, hx_art, hx_gen, hx_unit⟩ :=
    w.isPlaceOver_placeOver.exists_isTameUnit
  set γ : (ResField w)ˣ := (LocInt w).unitGroupToResidueFieldUnits ⟨x, hx_mem⟩
  have h_base : p.character.baseChange.finPart (locIdele w x) = p.tamePart w γ :=
    p.hasWeight.baseChange_finPart_locIdele (fun h ↦ hw.not_star (h.substr hw))
      (p.tamePart_eq_one _ hw.not_star) hx_unit
  have h_value : (p.stickelbergerChar (ℓ := ℓ) δ w.isPlaceOver_placeOver.tameGenerator).1 =
      ιℓ (p.tamePart w γ) ^ (-δ).1 := by
    simp [CriticalPair.stickelbergerChar,
      avatar_localArtin _ w.isPlaceOver_placeOver (.inl hℓ) hx_art,
      toAlgebraic, h_base]
  have hγ_ne : p.tamePart w γ ≠ 1 := by simpa [MulChar.eq_iff hx_gen] using (hp w).2 hw
  have hγ_pow : p.tamePart w γ ^ (w.q - 1) = 1 := by
    simp [← map_pow, ← Units.val_pow_eq_pow_val, ← card_ResField, ← Nat.card_units]
  simp only [Ne, Units.ext_iff, Units.val_pow_eq_pow_val, h_value, Units.val_one]
  -- As `δ` is a sign, both claims follow from those for `p.tamePart w γ`.
  fin_cases δ <;> simp [← map_pow, ιℓ.map_eq_one_iff, hγ_ne, hγ_pow]

/-- Let `p = (ν, z)` be a pair, `δ` a sign and `τ` a tame character: a character of `U(1)(𝔸)` of
weight `0` with residue characters trivial outside a finite set `τ.Q` of places, its modulus. Let
`ϑ = p.stickelbergerChar δ` and `ψ = τ.invAvatar` be the `ℓ`-adic Galois characters (avatars)
attached to the base changes of `ν ^ (-δ)` and `τ⁻¹` to `E`. Let `v` be a place not dividing
`ℓ p₀ p₁ N`, with `v` and its conjugate outside `τ.Q`, and let `φ` be an arithmetic Frobenius
element at a place `A` over `v`. Then `ϑ(φ) ψ(φ) = ι(y) ^ δ`, where `ι` is the fixed isomorphism of
`ℂ` with `ℚ̄_ℓ` and `y` is the value of the base change to `E` of `ν τ ^ δ` at the chosen
uniformiser at `v`. -/
lemma stickelbergerChar_mul_invAvatar_frob (p : D.CriticalPair) (δ : ℤˣ) (τ : D.TameChar)
    {v : FinPlace D.E}
    (hv : v ∉ badPlaces D ℓ) (hvQ : v ∉ τ.Q) (hv'Q : star v ∉ τ.Q) {A : ClosurePlace}
    (hA : IsPlaceOver A v) {φ : AbsGal D} (hφ : IsFrob A v.q φ) :
    (p.stickelbergerChar δ φ : PadicAlgCl ℓ) * τ.invAvatar φ =
      ιℓ ((p.character * τ.toAutChar ^ δ.1).baseChange.atUniformizer v) ^ δ.1 := by
  have hvℓ : (ℓ : 𝓞 D.E) ∉ v.asIdeal := (not_isChosen_of_notMem_badPlaces hv).1
  -- After this substitution `φ` is a geometric Frobenius element, where the avatar is known.
  obtain ⟨φ, rfl⟩ := inv_surjective φ
  have h_unr_τ : CharUnramifiedAt (τ.hasWeight.inv.toAlgebraic 0 0).character v :=
    τ.hasWeight.inv.charUnramifiedAt_toAlgebraic
      (by simp [τ.tamePart_eq_one, hvQ]) (by simp [τ.tamePart_eq_one, hv'Q]) 0 0
  have h_ν : (p.stickelbergerChar (ℓ := ℓ) δ φ⁻¹ : PadicAlgCl ℓ) =
      (ιℓ (heckeCoeff ((p.hasWeight.zpow (-δ : ℤˣ)).toAlgebraic 0 0).character ∅ v))⁻¹ := by
    rw [CriticalPair.stickelbergerChar,
      ← avatar_frob _ hA hvℓ (charUnramifiedAt_zpow_neg_of_notMem_badPlaces p δ hv) hφ]
    simp
  have h_τ : τ.invAvatar (ℓ := ℓ) φ⁻¹ =
      (ιℓ (heckeCoeff (τ.hasWeight.inv.toAlgebraic 0 0).character ∅ v))⁻¹ := by
    simp [TameChar.invAvatar, avatar_frob _ hA hvℓ h_unr_τ hφ]
  rw [h_ν, h_τ]
  simp [HeckeChar.atUniformizer, heckeCoeff, toAlgebraic, mul_zpow, ← _root_.zpow_mul]

/-- For every point `x` of `U(1)(𝔸)` there is a finite idele `y` such that every tame character
takes at `x` the value of its base change at `y`. -/
lemma exists_finPart_baseChange_eq (x : unitary (𝔸 D.E)) :
    ∃ y : (𝔸f D.E)ˣ,
      ∀ τ : D.TameChar, τ.toAutChar.1 x = (τ.toAutChar.baseChange.finPart y).1 := by
  refine (exists_snd_div_divStar_finIdeleIncl_eq_one x).imp fun y hy τ ↦ ?_
  -- `τ` is trivial on `x / divStar y`, whose finite part is `1`, as its weight is `0`.
  have h_one : (τ.toAutChar.1 (x / divStar (finIdeleIncl y))).1 = 1 := by
    simpa using
      eq_of_mem_integralU1 τ.tamePart_eq_one τ.hasWeight.2 _ (mem_integralU1_of_snd_eq_one _ hy)
  change (τ.toAutChar.1 x).1 = (τ.toAutChar.1 (divStar (finIdeleIncl y))).1
  simpa [field] using h_one

omit [PadicIso ℓ] in
/-- The power `τ ^ δ` of a tame character `τ`, as a tame character of modulus `I`, where `I` is an
auxiliary set outside which the residue characters of `τ` are trivial. -/
noncomputable abbrev _root_.New.Data.TameChar.zpowOfAuxiliary (τ : D.TameChar) (δ : ℤˣ)
    {I : Finset (FinPlace D.E)} (hI : IsAuxiliary (badPlaces D ℓ) I)
    (hτ : ∀ v : FinPlace D.E, v ∉ I → τ.tamePart v = 1) : D.TameChar :=
  tameCharOfAuxiliary I hI (⟨(τ.toAutChar, τ.tamePart), τ.hasWeight, hτ⟩ ^ δ.1)

/-- Let `F` be a function on tame characters `τ` that is an integral measure: on each modulus `I` it
is `τ ↦ ∑ j, α j τ(u j)` for finitely many points `u j` and coefficients `α j` that are integral
away from the norm of `I`. Write `Cl_I` for `U1ClassGroup I`, the finite ideles `x` of `E` with
`x x̄ = 1` modulo those in `Eˣ` and the units `≡ 1` at `I`, and `ι` for the isomorphism of `ℂ` with
`ℚ̄_ℓ`. There are elements `Θ_I` of the group rings of the `Cl_I` such that `Θ_∅` has the value
`ι F(1)` at the trivial character and the following holds. Let `I` be auxiliary: its places have
prime norm, and it is disjoint from the places dividing `ℓ p₀ p₁ N`, their conjugates and its own
conjugate. Let the residue characters of `τ` be trivial outside `I`, and let `ψ`, the `ℓ`-adic
Galois character of `τ⁻¹`, be a character for `I` (`IsFromU1`): `ψ(Art x) = η(x / x̄)` for an idele
class character `η` of modulus `I` trivial at the places over `ℓ`. Then `ψ(Θ_I) = ι F(τ ^ δ)`, where
`τ ^ δ` is regarded as a tame character of modulus `I` (`zpowOfAuxiliary`). -/
lemma exists_groupRingEval_eq_of_isIntegralMeasure {F : D.TameChar → ℂ}
    (hF : ∀ τ : D.TameChar, τ.IsIntegralMeasure F) (δ : ℤˣ) :
    ∃ Θ : ∀ I : Finset (FinPlace D.E), MonoidAlgebra (intQpBar ℓ) (U1ClassGroup I),
      groupRingEval (1 : AbsGal D →* PadicAlgCl ℓ) (Θ ∅) = ιℓ (F .one) ∧
      ∀ (I : Finset (FinPlace D.E)) (hI : IsAuxiliary (badPlaces D ℓ) I) (τ : D.TameChar)
        (hτ : ∀ v : FinPlace D.E, v ∉ I → τ.tamePart v = 1),
        IsFromU1 (placesDividing D.E ℓ) I τ.invAvatar →
          groupRingEval τ.invAvatar (Θ I) = ιℓ (F (τ.zpowOfAuxiliary δ hI hτ)) := by
  classical
  -- At an auxiliary modulus `I`, the measure is given by points `u j` and coefficients `α j`.
  have h_meas (I : Finset (FinPlace D.E)) (hI : IsAuxiliary (badPlaces D ℓ) I) :
      ∃ (J : Type) (_ : Fintype J) (u : J → unitary (𝔸 D.E)) (α : J → ℂ),
        (∀ j, α j ∈ Seesaw.integralAway (∏ v ∈ I, v.q)) ∧
        ∀ τ : D.TameChar, τ.Q = I → F τ = ∑ j, α j * τ.toAutChar.1 (u j) :=
    hF (tameCharOfAuxiliary I hI 1)
  choose J _ u α hα h_sum using h_meas
  -- The coefficients are integral at `ιℓ`, since the places of `I` have norm prime to `ℓ`.
  have hα_int (I : Finset (FinPlace D.E)) (hI : IsAuxiliary (badPlaces D ℓ) I) (j : J I hI) :
      ‖ιℓ (α I hI j)‖ ≤ 1 := by
    simpa using hα I hI j ℓ (coprime_prod_q_of_isAuxiliary hI).1 (complexToCp ιℓ)
  choose y hy using exists_finPart_baseChange_eq (D := D)
  -- `Θ I` is the image of the combination of points under `u ↦ u ^ (-δ)`.
  let Θ (I : Finset (FinPlace D.E)) : MonoidAlgebra (intQpBar ℓ) (U1ClassGroup I) :=
    if hI : IsAuxiliary (badPlaces D ℓ) I then
      ∑ j, .single (divStarClass I (y (u I hI j) ^ (-δ.1))) ⟨ιℓ (α I hI j), hα_int I hI j⟩
    else 0
  have hΘ (I : Finset (FinPlace D.E)) (hI : IsAuxiliary (badPlaces D ℓ) I)
      (ψ : AbsGal D →* PadicAlgCl ℓ) : groupRingEval ψ (Θ I) =
        ∑ j, ιℓ (α I hI j) * ψ (galoisLift (divStarClass I (y (u I hI j) ^ (-δ.1)))) := by
    simp only [Θ, dite_eq_left hI, groupRingEval_sum_single]
    rfl
  refine ⟨Θ, ?_, fun I hI τ hτ hψ ↦ ?_⟩
  · simp [hΘ ∅ (nofun : IsAuxiliary (badPlaces D ℓ) ∅), h_sum ∅ nofun,
      toAutChar_one_and_toTwist_one_and_Q_one]
  · have h_lift (z : (𝔸f D.E)ˣ) : τ.invAvatar (galoisLift (divStarClass I z)) =
        ιℓ (τ.toAutChar.baseChange.finPart z)⁻¹ :=
      (hψ.apply_galoisLift (Quotient.out_eq _).symm).trans
        (invAvatar_eq_of_artinMap_eq (Quotient.out_eq _).symm)
    have h_char (j : J I hI) :
        τ.invAvatar (galoisLift (divStarClass I (y (u I hI j) ^ (-δ.1)))) =
          ιℓ ((τ.zpowOfAuxiliary δ hI hτ).toAutChar.1 (u I hI j)).1 := by
      rw [h_lift, hy]
      simp
    rw [hΘ I hI, h_sum I hI _ rfl]
    simp only [map_sum, map_mul, h_char]

/-- Let `p = (ν, z)` be a ramified pair (the residue characters of `ν` are nontrivial exactly at the
chosen places), `δ` a sign, `w` a chosen place not above `ℓ` and `ϑ = p.stickelbergerChar δ`, the
`ℓ`-adic Galois character attached to the base change of `ν ^ (-δ)`. At the tame generator `g₀` of
`w` the valuation `ellVal` of `ϑ(g₀) - 1` is at most that of `N w - 1`, with `N w` the norm of
`w`. -/
lemma ellVal_stickelbergerChar_tameGenerator_sub_one_le {w : FinPlace D.E} (hw : D.IsChosen w)
    (hℓ : w ∉ placesDividing D.E ℓ) {p : D.CriticalPair} (hp : p.IsRamified) (δ : ℤˣ) :
    ellVal (p.stickelbergerChar δ w.isPlaceOver_placeOver.tameGenerator - 1 : PadicAlgCl ℓ) ≤
      ellVal (w.q - 1 : PadicAlgCl ℓ) := by
  obtain ⟨hϑ_ne, hϑ_pow⟩ := stickelbergerChar_tameGenerator_ne_one_and_pow_eq_one hw hℓ hp δ
  -- Distinct roots of unity of order dividing `n` are at distance at least `‖n‖`.
  rw [← Nat.cast_pred w.one_lt_q.pos]
  exact ellVal_le_ellVal (norm_natCast_le_norm_sub_of_pow_eq_one (congrArg Units.val hϑ_pow)
    (one_pow _) (Units.val_eq_one.not.2 hϑ_ne))

open scoped Classical in
/-- Let `p = (ν, z)` be a pair, and let `F` be a twist measure of `p` with Euler exponents `K`: a
function on tame characters which, when a place `v` is added to the modulus of `τ`, is multiplied by
the factors `1 - y ^ (±1) (N v) ^ (-e)`, `e ∈ K`, with `y` the value of `ν τ` at `v`. Let `δ` be a
sign, `v` a place outside the modulus `Q` of `τ` such that `Q` and `insert v Q` are auxiliary, and
`φ` an arithmetic Frobenius element at a place over `v`. Then, in passing from modulus `Q` to
`insert v Q`, the value `ι F(τ ^ δ)` is multiplied by the product of `1 - a ^ (±1) (N v) ^ (-e)`
over `e ∈ K` and both signs. Here `a = ϑ(φ) ψ(φ)`, where `ϑ = p.stickelbergerChar δ` and
`ψ = τ.invAvatar` are the `ℓ`-adic Galois characters attached to `ν ^ (-δ)` and `τ⁻¹`. -/
lemma apply_insert_eq_mul_eulerFactor {p : D.CriticalPair} {K : Finset ℕ} {m : ℕ}
    {F : D.TameChar → ℂ} (hF : p.IsTwistMeasure K m F) (δ : ℤˣ) (τ : D.TameChar) {v : FinPlace D.E}
    (hv : v ∉ τ.Q) (hQ : IsAuxiliary (badPlaces D ℓ) τ.Q)
    (hQ_insert : IsAuxiliary (badPlaces D ℓ) (insert v τ.Q))
    (hτ : ∀ u : FinPlace D.E, u ∉ insert v τ.Q → τ.tamePart u = 1)
    {A : ClosurePlace} (hA : IsPlaceOver A v) {φ : AbsGal D} (hφ : IsFrob A v.q φ) :
    ιℓ (F (τ.zpowOfAuxiliary δ hQ_insert hτ)) =
      ιℓ (F (τ.zpowOfAuxiliary δ hQ τ.tamePart_eq_one)) *
        eulerFactor (K.toList.map Nat.cast)
          ((p.stickelbergerChar δ φ : PadicAlgCl ℓ) * τ.invAvatar φ) v.q := by
  obtain ⟨hv_bad, -, hv_star, -⟩ := hQ_insert v (mem_insert_self v τ.Q)
  have h_insert : F (τ.zpowOfAuxiliary δ hQ_insert hτ) =
      F (τ.zpowOfAuxiliary δ hQ τ.tamePart_eq_one) * ∏ l ∈ K, ∏ ε : ℤˣ,
        (1 - (p.character * τ.toAutChar ^ δ.1).baseChange.atUniformizer v ^ ε.val / v.q ^ l) :=
    hF.apply_insert _ _ v hv rfl rfl rfl
  rw [h_insert, map_mul, stickelbergerChar_mul_invAvatar_frob p δ τ hv_bad hv
    (notMem_mono (subset_insert v τ.Q) hv_star) hA hφ, eulerFactor_zpow_units]
  simp [eulerFactor, div_eq_mul_inv]

/-- Let `p = (ν, z)` be a pair and `F` a twist measure of `p` with parameter `m`: at a twist `ξ` of
modulus `Q` it has the value `F(1) (N Q) ^ m r(ξ) ^ (m + 1)`, where
`r(ξ) = |L(z, (ν ξ)⁻¹)| / |L(z, ν⁻¹)|` is the ratio of `L`-values without Euler factors at the
chosen places and, above, at `Q`. A twist is a tame character whose residue characters are
nontrivial at every place of the modulus. If `Q` is auxiliary, then `N Q` is an `ℓ`-adic unit, and
the norm of `ι F(ξ ^ δ)` is that of `ι F(1)` times the `(m + 1)`-th power of that of `p.ratio ξ δ`,
the ratio `r(ξ ^ δ)`. -/
lemma norm_apply_twist {p : D.CriticalPair} {K : Finset ℕ} {m : ℕ} {F : D.TameChar → ℂ}
    (hF : p.IsTwistMeasure K m F) (δ : ℤˣ) (ξ : D.Twist)
    (hξ : IsAuxiliary (badPlaces D ℓ) ξ.Q) :
    ‖ιℓ (F (ξ.toTameChar.zpowOfAuxiliary δ hξ ξ.tamePart_eq_one))‖ =
      ‖ιℓ (F .one)‖ * ‖ιℓ (p.ratio ξ δ)‖ ^ (m + 1) := by
  -- `ξ ^ δ` is again a twist.
  have h_ne : ∀ u ∈ ξ.Q, (ξ.toTameChar.zpowOfAuxiliary δ hξ ξ.tamePart_eq_one).tamePart u ≠ 1 := by
    fin_cases δ <;> simpa using ξ.tamePart_ne_one
  rw [hF.apply_twist ⟨_, h_ne⟩]
  -- The norm of the modulus is an `ℓ`-adic unit. `-Nat.cast_prod` and `-map_div₀` keep it and the
  -- ratio in one piece.
  simp [(coprime_prod_q_of_isAuxiliary hξ).1.norm_natCast_eq_one, CriticalPair.ratio,
    -Nat.cast_prod,
    -map_div₀]

/-- Let `D` be the data, `ℓ` a prime with an isomorphism `ιℓ` of `ℂ` with `ℚ̄_ℓ` (`PadicIso ℓ`), `δ`
a sign, and `p = (ν, z)` a ramified pair: the residue characters of the character `ν` of `U(1)(𝔸)`
are nontrivial exactly at the chosen places, which divide a fixed integer of norm `p₀ p₁`. Let `w`
be a chosen place not above `ℓ` and `g₀` its tame generator, an inertia element.

Then there is a Stickelberger system for `badPlaces D ℓ` and `g₀`: a Galois character `ϑ`, exponents
`e`, and for every finite set `Q` of places an element `Θ_Q` of the group ring of the class group
`Cl_Q` of `U(1)` of modulus `Q`, such that adding a place to `Q` multiplies the values by Euler
factors in `ϑ` and the `e`. Its number `β = v(1(Θ_∅)) + ∑_e 2 v(ϑ(g₀) - 1)`, with `v = ellVal` the
`ℓ`-adic valuation truncated below at `0`, is at most `v(1(Θ_∅)) + 4 v(N w - 1)`.

Let `ξ` be a twist (a weight `0` character of `U(1)(𝔸)` with residue characters nontrivial exactly
at a finite set `Q`, its modulus). Suppose that `Q` is auxiliary and that `ψ`, the `ℓ`-adic Galois
character of `ξ⁻¹`, is a character for `Q`. Let `r = p.ratio ξ δ`, the ratio
`|L(z, (ν ξ^δ)⁻¹)| / |L(z, ν⁻¹)|` without Euler factors at chosen places and, above, at `Q`. Then
`‖ψ(Θ_Q)‖ = ‖1(Θ_∅)‖ ‖ιℓ(r)‖ ^ i`, where `i = 2` if `z = 1` and `i = 1` otherwise. -/
theorem exists_stickelbergerSystem_β_le_and_norm_eq {w : FinPlace D.E} (hw : D.IsChosen w)
    (hℓ : w ∉ placesDividing D.E ℓ) {p : D.CriticalPair} (hp : p.IsRamified) (δ : ℤˣ) :
    ∃ Y : StickelbergerSystem ℓ (badPlaces D ℓ) w.isPlaceOver_placeOver.tameGenerator,
      Y.β ≤ ellVal (groupRingEval (1 : AbsGal D →* PadicAlgCl ℓ) (Y.element ∅)) +
        4 * ellVal (w.q - 1 : PadicAlgCl ℓ) ∧
      ∀ ξ : D.Twist, IsAuxiliary (badPlaces D ℓ) ξ.Q →
        IsFromU1 (placesDividing D.E ℓ) ξ.Q ξ.invAvatar →
        ‖groupRingEval ξ.invAvatar (Y.element ξ.Q)‖ =
          ‖groupRingEval (1 : AbsGal D →* PadicAlgCl ℓ) (Y.element ∅)‖ *
            ‖ιℓ (p.ratio ξ δ)‖ ^ (if p.z = 1 then 2 else 1) := by
  classical
  -- The elements come from an integral measure `F`, the norm relation from its Euler factors and
  -- the norms at twists from its values there.
  set K : Finset ℕ := if p.z = 1 then {0, 1} else {p.z} with hK
  obtain ⟨F, -, hF : p.IsTwistMeasure K (if p.z = 1 then 1 else 0) F⟩ :=
    CriticalPair.exists_isTwistMeasure hp
  obtain ⟨Θ, hΘ_one, hΘ⟩ := exists_groupRingEval_eq_of_isIntegralMeasure (ℓ := ℓ)
    hF.isIntegralMeasure δ
  refine ⟨{
    twistChar := p.stickelbergerChar δ
    continuous_twistChar := continuous_avatar _
    unramified := fun _ ↦ stickelbergerChar_eq_one_of_mem_inertiaAbove p δ
    twistChar_apply_ne_one := (stickelbergerChar_tameGenerator_ne_one_and_pow_eq_one hw hℓ hp δ).1
    exponents := K.toList.map Nat.cast
    element := Θ
    one_element_empty_ne_zero := by simpa [hΘ_one] using hF.apply_one_ne_zero
    element_insert := fun Q v hv hQ_insert ψ hψ A hA φ hφ ↦ ?_ }, ?_, fun ξ hξ hψ ↦ ?_⟩
  · -- The norm relation.
    have hQ : IsAuxiliary (badPlaces D ℓ) Q := hQ_insert.mono (subset_insert v Q)
    obtain ⟨τ, rfl, rfl⟩ := exists_tameChar_invAvatar_eq hQ hψ
    have hτ : ∀ u ∉ insert v τ.Q, τ.tamePart u = 1 := by simp +contextual [τ.tamePart_eq_one]
    rw [hΘ _ hQ_insert τ hτ (hψ.mono (coe_subset.2 (subset_insert v τ.Q))),
      hΘ _ hQ τ τ.tamePart_eq_one hψ]
    exact apply_insert_eq_mul_eulerFactor hF δ τ hv hQ hQ_insert hτ hA hφ
  · -- The bound for `β`: there are at most two exponents.
    have h_card : #K ≤ 2 := by
      rw [hK]
      split_ifs
      · exact card_le_two
      · simp
    refine add_le_add le_rfl ?_
    calc ((K.toList.map (Nat.cast : ℕ → ℤ)).length : ENNReal) *
          (2 * ellVal (p.stickelbergerChar δ w.isPlaceOver_placeOver.tameGenerator - 1 :
            PadicAlgCl ℓ))
        ≤ 2 * (2 * ellVal (w.q - 1 : PadicAlgCl ℓ)) := by
          gcongr
          · simpa using h_card
          · exact ellVal_stickelbergerChar_tameGenerator_sub_one_le hw hℓ hp δ
      _ = 4 * ellVal (w.q - 1 : PadicAlgCl ℓ) := by ring
  · -- The norms at twists.
    have h_exp : (if p.z = 1 then 1 else 0) + 1 = if p.z = 1 then 2 else 1 := by
      split_ifs <;> rfl
    simp only [hΘ_one, hΘ ξ.Q hξ ξ ξ.tamePart_eq_one hψ, norm_apply_twist hF δ ξ hξ, h_exp]

omit [PadicIso ℓ] in
/-- Let `‖x‖ = ‖x₀‖ ‖r‖ ^ i` with `x₀ ≠ 0` integral and `i ≥ 1`. If `v(x) ≤ v(x₀) + c`, then
`v(r) ≤ c`, where `v` is the valuation `ellVal`. -/
lemma ellVal_le_of_norm_eq_mul_pow {x x₀ r : PadicAlgCl ℓ} {i : ℕ} {c : ENNReal} (hi : i ≠ 0)
    (hx₀ : x₀ ≠ 0) (hx₀_int : ‖x₀‖ ≤ 1) (hx : ‖x‖ = ‖x₀‖ * ‖r‖ ^ i)
    (h_le : ellVal x ≤ ellVal x₀ + c) : ellVal r ≤ c := by
  obtain hr | hr := le_total ‖r‖ 1
  · have h_eq : ellVal x = ellVal x₀ + i * ellVal r := by
      rw [ellVal_congr_norm (y := x₀ * r ^ i) (by simp [hx]), ← ellVal_pow]
      simpa using ellVal_val_mul (⟨x₀, hx₀_int⟩ : intQpBar ℓ) ((⟨r, hr⟩ : intQpBar ℓ) ^ i)
    rw [h_eq, ENNReal.add_le_add_iff_left (ellVal_eq_top_iff.not.2 hx₀)] at h_le
    calc ellVal r ≤ i * ellVal r :=
          le_mul_of_one_le_left zero_le (mod_cast Nat.one_le_iff_ne_zero.2 hi)
      _ ≤ c := h_le
  · -- `ellVal` is truncated at `0`, so it vanishes on elements of norm at least `1`.
    calc ellVal r ≤ ellVal (1 : PadicAlgCl ℓ) := ellVal_le_ellVal (norm_one.trans_le hr)
      _ ≤ c := by simp [ellVal]

/-- Let `D` be the data, `ℓ` a prime with an isomorphism `ιℓ` of `ℂ` with `ℚ̄_ℓ` (`PadicIso ℓ`), and
`v = ellVal` the `ℓ`-adic valuation truncated below at `0`. Let `δ` be a sign, `p = (ν, z)` a
ramified pair (residue characters of `ν` nontrivial exactly at the chosen places) and `w` a chosen
place not above `ℓ`.

There is a Stickelberger system, with number `β = v(1(Θ_∅)) + ∑_e 2 v(ϑ(g₀) - 1)` (`e` over the
Euler exponents, `g₀` the tame generator of `w`), with the following property. Let `ξ` be a twist
(residue characters nontrivial exactly at its modulus `Q`) such that `Q` is auxiliary and the Galois
character `ψ` of `ξ⁻¹` is a character for `Q`. If `v(ψ(Θ_Q)) ≤ β + c`, then
`v(ιℓ(r)) ≤ 4 v(w.q - 1) + c`, where `w.q` is the norm of `w`, for the ratio
`r = |L(z, (ν ξ^δ)⁻¹)| / |L(z, ν⁻¹)|` of `L`-values without Euler factors at chosen places and,
above, at `Q` (`p.ratio ξ δ`). -/
lemma exists_stickelbergerSystem_ellVal_ratio_le {w : FinPlace D.E} (hw : D.IsChosen w)
    (hℓ : w ∉ placesDividing D.E ℓ) {p : D.CriticalPair} (hp : p.IsRamified) (δ : ℤˣ) :
    ∃ Y : StickelbergerSystem ℓ (badPlaces D ℓ) w.isPlaceOver_placeOver.tameGenerator,
      ∀ ξ : D.Twist, IsAuxiliary (badPlaces D ℓ) ξ.Q →
        IsFromU1 (placesDividing D.E ℓ) ξ.Q ξ.invAvatar → ∀ c : ENNReal,
        ellVal (groupRingEval ξ.invAvatar (Y.element ξ.Q)) ≤ Y.β + c →
        ellVal (ιℓ (p.ratio ξ δ)) ≤ 4 * ellVal (w.q - 1 : PadicAlgCl ℓ) + c := by
  obtain ⟨Y, hβ, hY⟩ := exists_stickelbergerSystem_β_le_and_norm_eq hw hℓ hp δ
  refine ⟨Y, fun ξ hξ hψ c h_le ↦ ellVal_le_of_norm_eq_mul_pow (by split_ifs <;> simp)
    Y.one_element_empty_ne_zero (Y.norm_groupRingEval_one_element_le_one ∅) (hY ξ hξ hψ) ?_⟩
  exact h_le.trans (by grw [hβ, add_assoc])

end New.Selmer
