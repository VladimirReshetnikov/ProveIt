import Lib.ClassField.GaloisCohomology.TameSelmerCocycles
import Lib.General.NumberTheory.PadicLimitsValuation
import New.Congruences.Selmer.AuxiliaryPrimes

/-!
# Even classes and auxiliary places for Selmer cocycles

The file concerns cocycles of `Gal(Ω/E)` in the twists `O/ℓ^ν(-e)`. Here `Ω` is the algebraic
closure of `ℚ`, `E ⊆ Ω` is a CM field containing the `5040`-th roots of unity
(`New.CMFieldWithRoot5040`), and `O` is the ring of integers of a finite Galois extension of `ℚ_ℓ`
(`New.CoeffRing`). Further, `cyc` is the `ℓ`-adic cyclotomic character (`New.cyclotomicChar`),
`cyc mod N` is the one modulo `N` (`New.cyclotomicCharMod`), and `g^c = conjGal g` is the conjugate
of `g` by the chosen complex conjugation. The reciprocity law for even classes is in
`New.Congruences.FirstOrder.KummerMaps`.

## Main definitions and results

* `New.Selmer.evenClasses`: the even classes, that is the cocycles unramified off `ℓ` and a set of
  places and its conjugate that are invariant under `g ↦ g^c` and zero on the kernel of
  `cyclotomicChar` in the decomposition groups above `ℓ`.
* `New.Selmer.IsTameGeneratorFamily`: places `w j` off `ℓ`, tame generators `τ j`, and `φ j` fixing
  `μ_{ℓ^ν}`; `New.Selmer.withConjInv f` doubles a family by the `(f j ^ c)⁻¹`, which serve the
  conjugate places.
* `New.Selmer.IsPrimeTriangle`: an even class that kills the earlier elements `τ i`, and `φ i` of
  the same exponent, is killed at `τ j` up to a bounded power of `ℓ`.
* `New.Selmer.IsAuxTwist`: an auxiliary set of places with an anticyclotomic character whose values
  at tame generators are not too close to `1`.
* `New.Selmer.IsTameGeneratorFamily.mem_selmerModule_of_tame_eq_zero`: killing the doubled tame
  generators removes the ramification at the places `w j` and their conjugates.
* `New.Selmer.eq_zero_of_forall_mem_Z1_of_mem_evenClasses`: to show that an element `b` of
  `O / ℓ ^ ν` vanishes, given an even class `c`, it is enough to test `b` with the additive maps `u`
  to `ℤ/ℓ ^ ν` for which `u ∘ c` is a cocycle of the twist `-e`; in fact every `u` has this
  property.

Notions from other files:
* `New.selmerModule ρ S L B`: the locally constant cocycles of `ρ` with values in `B` that
  are unramified outside `S` and satisfy the relations `L`.
* `New.Selmer.tateTwist ℓ E O e`: the character `cyclotomicInv ℓ E O ^ e` as `1 × 1` matrices, where
  `cyclotomicInv` is `cyc⁻¹` with values in `O`.
* `New.Selmer.shaLocalSet ℓ E 1`: the elements of decomposition groups above `ℓ` with `cyc = 1`.
* `New.Z1` and `New.charRep`: the continuous cocycles of a representation, and the representation
  given by scalars through a character.
-/

namespace New.Selmer

open PadicInt

variable {ℓ : ℕ} [ThePrime ℓ] {E J : Type} [Field E] [CMFieldWithRoot5040 E]

/-- The even classes of exponent `e` for a set `S` of places: the locally constant cocycles
`c : Gal(Ω/E) → O/ℓ^ν(-e)` (values indexed by `Unit`) that are unramified outside the places above
`ℓ`, `S` and its conjugate, satisfy `c (conjGal g) = c g` (where `conjGal g` is the conjugate of `g`
by complex conjugation), and vanish on the elements with trivial cyclotomic character of the
decomposition groups above `ℓ` (`shaLocalSet ℓ E 1`). -/
def evenClasses (O : CoeffRing ℓ) (S : Set (FinPlace E)) (ν : ℕ) (e : ℕ) :
    Set (Gal(Ω/E) → Unit → QuotSpan ((ℓ : (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ))) ^ ν)) :=
  {c ∈ selmerModule (tateTwist ℓ E O e) (placesDividing E ℓ ∪ Set.conjClosure S) ∅
    (QuotSpan (ℓ ^ ν : ↑O)) |
    (∀ g : Gal(Ω/E), c (conjGal g) = c g) ∧ ∀ g ∈ shaLocalSet ℓ E 1, c g = 0}

/-- The `τ j` are tame generators at the places `w j` of `E`, with auxiliary elements `φ j`: each
`w j` is a finite place not above `ℓ`, `φ j` fixes the `ℓ ^ ν`-th roots of unity, and `τ j` is the
chosen generator of tame inertia at some place of the algebraic closure `Ω` over `w j`. -/
def IsTameGeneratorFamily (ν : ℕ) (w : J → FinPlace E) (τ φ : J → Gal(Ω/E)) : Prop :=
  ∀ j : J,
    w j ∉ placesDividing E ℓ ∧
    cyclotomicCharMod Ω (ℓ ^ ν) (φ j) = 1 ∧
    ∃ A : ValuationSubring Ω, ∃ h : IsPlaceOver A (w j), h.tameGenerator = τ j

/-- The family indexed by two copies `J × Bool` of `J`, with value `τ j` at `(j, true)` and
`(conjGal (τ j))⁻¹` at `(j, false)`; see `withConjInv_true` and `withConjInv_false`. -/
noncomputable abbrev withConjInv (τ : J → Gal(Ω/E)) (k : J × Bool) : Gal(Ω/E) :=
  idOrConjInv k.2 (τ k.1)

lemma withConjInv_true (τ : J → Gal(Ω/E)) (j : J) : withConjInv τ (j, true) = τ j := rfl

lemma withConjInv_false (τ : J → Gal(Ω/E)) (j : J) :
    withConjInv τ (j, false) = (conjGal (τ j))⁻¹ :=
  rfl

/-- A triangle of primes: places `w j` off `ℓ`, with elements `τ j` and `φ j`, indexed by a finite
linear order `J`. The place `w j` serves the exponent `ty j`, where `0 < ty j < t` and `ty` is
monotone, and `a` is a fixed element of `Gal(Ω/E)`. In the application `a` generates this group
modulo the kernel of the cyclotomic character, and `φ j` is a Frobenius element at the place of the
tame generator `τ j`.
* `exists_test_points`: a finite set `s` of elements with trivial cyclotomic character, with
`(#J + #s + 1) * h ≤ c`, detects together with `a` the cocycles unramified off `ℓ`; for each
exponent and each `g` in `s`, the even classes unramified off `ℓ` take at some `φ j` of that
exponent twice their value at `g`.
* `prod_dvd`: the element `a` separates the powers `u ^ e`, `e < t`, of
`u = cyclotomicChar Ω ℓ a⁻¹`, up to `ℓ ^ h`. -/
structure IsPrimeTriangle (ν : ℕ) (w : J → FinPlace E) (τ φ : J → Gal(Ω/E)) (a : Gal(Ω/E))
    [LinearOrder J] [Fintype J] (t : ℕ) (ty : J →o {e : Fin t // 0 < (e : ℕ)}) (h c : ℕ) :
    Prop where
  /-- The `w j` are places off `ℓ` with tame generators `τ j`, and the `φ j` fix the `ℓ ^ ν`-th
  roots of unity (`New.Selmer.IsTameGeneratorFamily`). -/
  isTameGeneratorFamily : IsTameGeneratorFamily ν w τ φ
  /-- There is a finite set `s` of test points with trivial cyclotomic character and
  `(#J + (#s + 1)) h ≤ c`. A locally constant cocycle in `O/ℓ^ν(-e)` unramified off `ℓ` that
  vanishes at `a` and on `s` is zero, for all `O` and `e`. For each exponent `e` and each `g` in `s`
  there is a `j` of exponent `e` with `z (φ j) = 2 z(g)` for all even classes `z` unramified off
  `ℓ`. -/
  exists_test_points : ∃ s : Finset Gal(Ω/E),
    (∀ g ∈ s, cyclotomicChar Ω ℓ g = 1) ∧
    (Fintype.card J + (s.card + 1)) * h ≤ c ∧
    (∀ (O : CoeffRing ℓ) (e : ℕ),
      ∀ z ∈ selmerModule (tateTwist ℓ E O e) (placesDividing E ℓ) ∅ (QuotSpan (ℓ ^ ν : ↑O)),
      z a = 0 → (∀ g ∈ s, z g = 0) → z = 0) ∧
    ∀ e : {e : Fin t // 0 < (e : ℕ)}, ∀ g ∈ s, ∃ j : J, ty j = e ∧
      ∀ O : CoeffRing ℓ, ∀ z ∈ evenClasses O ∅ ν e, z (φ j) = 2 • z g
  /-- For `e < t` and `u = cyclotomicChar Ω ℓ a⁻¹`, the product in `ℤ_[ℓ]` of `u ^ e - u ^ k` over
  `k < t`, `k ≠ e`, divides `ℓ ^ h`. -/
  prod_dvd (e : Fin t) :
    ∏ k ∈ ({e}ᶜ : Finset (Fin t)),
      ((cyclotomicChar Ω ℓ a⁻¹ ^ (e : ℕ)).val - (cyclotomicChar Ω ℓ a⁻¹ ^ (k : ℕ)).val) ∣ ℓ ^ h
  /-- If an even class `z` of exponent `ty j` for the places `w` kills `τ i` for all `i < j`, and
  `φ i` for the `i < j` with the same exponent as `j`, then `ℓ ^ h` kills `z (τ j)`. -/
  pow_smul_eq_zero (O : CoeffRing ℓ) (j : J) : ∀ z ∈ evenClasses O (Set.range w) ν (ty j),
    (∀ i < j, z (τ i) = 0 ∧ (ty i = ty j → z (φ i) = 0)) → ℓ ^ h • z (τ j) = 0
  /-- For `0 < e < t`, the element `4 (cyclotomicInv ℓ E O a ^ e - 1)²` of `O` divides `ℓ ^ h`. -/
  four_mul_sq_dvd (O : CoeffRing ℓ) (e : {e : Fin t // 0 < (e : ℕ)}) :
    4 * (cyclotomicInv ℓ E O a ^ (e : ℕ) - 1) ^ 2 ∣ (ℓ ^ h : ↑O)

/-- The set of places `Q` is auxiliary for `S` (`New.IsAuxiliary`: its places have prime norm, they
and their conjugates are off `S`, and their conjugates are off `Q`), no place of `Q` lies above `ℓ`,
and `ψ` is anticyclotomic of modulus `Q` (`New.IsFromU1`: it comes from the norm-one torus).
Moreover, for some choice of tame generators `σ P` at places over the `P` in `Q`, the sum of the
`ℓ`-adic valuations of `ψ (σ P) - 1` is at most `c`. -/
def IsAuxTwist (S : Finset (FinPlace E)) (Q : Finset (FinPlace E)) (ψ : Gal(Ω/E) →* PadicAlgCl ℓ)
    (c : ENNReal) :
    Prop :=
  IsAuxiliary S Q ∧
  IsFromU1 (placesDividing E ℓ) Q ψ ∧
  ∃ σ : Q → Gal(Ω/E), IsTameGeneratorFamily 0 ((↑) : Q → _) σ 1 ∧ ∑ k : Q, ellVal (ψ (σ k) - 1) ≤ c

/-- Let `ℓ` be a prime and `E` a CM field, embedded in the algebraic closure `Ω` of `ℚ`, that
contains the `5040`-th roots of unity. The value of the `ℓ`-adic cyclotomic character at any element
`a` of `Gal(Ω/E)` is congruent to `1` modulo `4` in `ℤ_[ℓ]`. -/
lemma four_dvd_cyclotomicChar_sub_one {ℓ : ℕ} [ThePrime ℓ] {E : Type} [Field E]
    [CMFieldWithRoot5040 E] (a : Gal(Ω/E)) :
    (2 ^ 2 : ℤ_[ℓ]) ∣ (cyclotomicChar Ω ℓ a).val - 1 := by
  obtain rfl | h_odd := (Fact.out : ℓ.Prime).eq_two_or_odd'
  · -- `E` contains a primitive `5040`-th root of unity, which `a` fixes, and `4 ∣ 5040`.
    obtain ⟨ζ, hζ⟩ := HasPrimitiveRoot5040.exists_primitive_root (E := E)
    have h_fix : (cyclotomicCharMod Ω 5040 a).1 = (1 : ℕ) :=
      cyclotomicCharMod_eq_of_isPrimitiveRoot (hζ.map_of_injective (algebraMap E Ω).injective)
        (by simp)
    exact (pow_dvd_cyclotomicChar_sub_iff 2).2 (cyclotomicCharMod_eq_of_dvd (by norm_num) h_fix)
  · -- For odd `ℓ`, `2` is a unit of `ℤ_[ℓ]`.
    have h_unit : IsUnit ((2 : ℕ) : ℤ_[ℓ]) :=
      isUnit_iff.2 (norm_natCast_eq_one_iff.2 (Nat.coprime_two_right.2 h_odd))
    exact (h_unit.pow 2).dvd

/-- The Tate twist `cyc^(-e)` with values in a `ℤ_[ℓ]`-algebra `Λ` is trivial on the kernel of the
`ℓ`-adic cyclotomic character `cyc`. -/
lemma tateTwist_eq_one_of_cyclotomicChar_eq_one {ℓ : ℕ} [ThePrime ℓ] {E Λ : Type} [Field E]
    [CMFieldWithRoot5040 E] [CommRing Λ] {e : ℕ} [Algebra ℤ_[ℓ] Λ] {g : Gal(Ω/E)}
    (hg : cyclotomicChar Ω ℓ g = 1) : tateTwist ℓ E Λ e g = 1 := by
  simp [tateTwist, cyclotomicInv, hg]

/-- Let the places `w j` of `E` be off `ℓ`, each `τ j` a generator of tame inertia at `w j`, and
each `φ j` an element fixing the `ℓ ^ ν`-th roots of unity (`hw`). Then the inverse `ℓ`-adic
cyclotomic character with values in `O` is trivial on `withConjInv τ`, and all its powers are
congruent to `1` modulo `ℓ ^ ν` on `withConjInv φ`. -/
lemma IsTameGeneratorFamily.cyclotomicInv_withConjInv_eq_one_and_dvd {ℓ : ℕ} [ThePrime ℓ]
    {E J : Type} [Field E] [CMFieldWithRoot5040 E] {ν : ℕ} {w : J → FinPlace E} {τ φ : J → Gal(Ω/E)}
    (hw : IsTameGeneratorFamily ν w τ φ) (O : CoeffRing ℓ) (k : J × Bool) :
    cyclotomicInv ℓ E O (withConjInv τ k) = 1 ∧
    ∀ e : ℕ, (ℓ ^ ν : ↑O) ∣ cyclotomicInv ℓ E O (withConjInv φ k) ^ e - 1 := by
  -- The cyclotomic character is invariant under `conjGal`, so only `τ j` and `φ j` matter.
  obtain ⟨h_off, h_fix, A, hA, hτ⟩ := hw k.1
  refine ⟨?_, fun e ↦ ?_⟩
  · -- `τ j` lies in an inertia group at `w j`, which is not above `ℓ`.
    have h_cyc_τ : cyclotomicChar Ω ℓ (τ k.1) = 1 := by
      rw [← hτ]
      exact cyclotomicChar_eq_one_of_mem_inertiaAbove ⟨w k.1, h_off, A, hA, hA.tameGenerator.2⟩
    cases hk : k.2 <;> simp [idOrConjInv, cyclotomicInv, hk, h_cyc_τ]
  · -- `φ j` fixes the roots of unity of order `ℓ ^ ν`.
    have h_mod : (cyclotomicCharMod Ω (ℓ ^ ν) ((withConjInv φ k)⁻¹ ^ e)).1 = (1 : ℕ) := by
      cases hk : k.2 <;> simp_all [idOrConjInv, cyclotomicCharMod_prime_pow_eq]
    have h_dvd : (ℓ : ℤ_[ℓ]) ^ ν ∣ (cyclotomicChar Ω ℓ ((withConjInv φ k)⁻¹ ^ e)).val - (1 : ℕ) :=
      (pow_dvd_cyclotomicChar_sub_iff ν).2 h_mod
    simpa [cyclotomicInv] using map_dvd (algebraMap ℤ_[ℓ] O) h_dvd

/-- Killing tame generators removes ramification. Let `E` be a CM field in the algebraic closure `Ω`
of `ℚ`, let the places `w j` of `E` be off the prime `ℓ`, with generators `τ j` of tame inertia
(`hw`), and let the representation `ρ` over `Λ` be trivial on those elements of inertia groups off
`S` that have trivial `ℓ`-adic cyclotomic character. The Selmer module `selmerModule ρ T L B`
consists of the locally constant cocycles `c` of `ρ` with values in `B ^ n` that are unramified off
`T` and obey the linear relations `∑ g, r g • c g = 0` for `r` in `L`. Let `c` be such a cocycle
modulo `ℓ ^ e`, where `T` is contained in the union of `S`, the `w j` and their complex conjugates.
If `c` vanishes at the `τ j` and the `(conjGal (τ j))⁻¹` (`conjGal` is conjugation by complex
conjugation), then `c` is unramified off `S`, so it lies in the Selmer module of `S` and `L`. -/
lemma IsTameGeneratorFamily.mem_selmerModule_of_tame_eq_zero {ℓ : ℕ} [ThePrime ℓ] {E Λ J : Type}
    [Field E] [CMFieldWithRoot5040 E] [CommRing Λ] {e ν : ℕ} {w : J → FinPlace E}
    {τ φ : J → Gal(Ω/E)} (hw : IsTameGeneratorFamily ν w τ φ) {n : Type} [Fintype n]
    [DecidableEq n] {ρ : Gal(Ω/E) →* Matrix n n Λ}
    {c : Gal(Ω/E) → n → QuotSpan ((ℓ : Λ) ^ e)} {S T : Set (FinPlace E)}
    {L : Set (Gal(Ω/E) →₀ Matrix n n Λ)} (hc : c ∈ selmerModule ρ T L (QuotSpan (ℓ ^ e : Λ)))
    (hτ_zero : ∀ i : J × Bool, c (withConjInv τ i) = 0)
    (hT : T ⊆ S ∪ Set.conjClosure (Set.range w))
    (hρ_inertia_cyc_ker : ∀ g ∈ inertiaAbove Sᶜ, cyclotomicChar Ω ℓ g = 1 → ρ g = 1) :
    c ∈ selmerModule ρ S L (QuotSpan (ℓ ^ e : Λ)) := by
  -- Only the places `v = w j` and `v = star (w j)` off `S` have to be removed.
  refine mem_selmerModule_of_eq_zero_on_inertiaAbove hc Set.Subset.rfl fun v hv ↦ ?_
  have hv_new : v ∈ Set.conjClosure (Set.range w) := (hT hv.1).resolve_left hv.2
  obtain ⟨j, hvj⟩ : ∃ j : J, v = w j ∨ v = star (w j) := by grind [star_star]
  obtain ⟨h_off, -, A, hA, hτ⟩ := hw j
  -- Such a place is not above `ℓ` (`star_mem_placesDividing`), so the cyclotomic character and
  -- hence `ρ` are unramified there.
  have hv_off : v ∉ placesDividing E ℓ := by grind
  have h_unram : ∀ g ∈ inertiaAbove {v}, ρ g = 1 := by
    rintro g ⟨v', rfl, B, hB, hgB⟩
    exact hρ_inertia_cyc_ker g ⟨v', hv.2, B, hB, hgB⟩
      (cyclotomicChar_eq_one_of_mem_inertiaAbove ⟨v', hv_off, B, hB, hgB⟩)
  -- By `exists_conj_side_detects`, for one of the two elements `withConjInv τ (j, b)` a cocycle
  -- that kills it vanishes on inertia above `v`; and `c` kills both.
  have h_torsion : ∀ x : QuotSpan (ℓ ^ e : Λ), ℓ ^ e • x = 0 := nsmul_quot_eq_zero dvd_rfl
  obtain ⟨b, A', -, h_side⟩ := exists_conj_side_detects h_torsion hA h_off h_unram hvj
  rw [hτ] at h_side
  exact (h_side c hc (hτ_zero (j, b))).1

end New.Selmer

/-! ## Detecting even classes modulo ℓ^ν -/

/-- Let `c` be an even class of exponent `e`: a locally constant cocycle of `Gal(Ω/E)` in
`O / ℓ ^ ν` for the `-e`-th power of the cyclotomic character, unramified outside `ℓ`, `S` and their
conjugates, invariant under conjugation by complex conjugation, and zero on the kernel of the
cyclotomic character in the decomposition groups above `ℓ`. If an element `b` of `O / ℓ ^ ν` is
killed by every additive map `u` to `ℤ/ℓ ^ ν` for which `u ∘ c` is a continuous cocycle (`New.Z1`)
for the `-e`-th power of the cyclotomic character modulo `ℓ ^ ν`, then `b = 0`. -/
lemma New.Selmer.eq_zero_of_forall_mem_Z1_of_mem_evenClasses {ℓ : ℕ} [ThePrime ℓ] {E : Type}
    [Field E] [CMFieldWithRoot5040 E] {O : CoeffRing ℓ} {S : Set (FinPlace E)} {ν e : ℕ}
    {b : Unit → QuotSpan ((ℓ : (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ))) ^ ν)}
    {c : Gal(Ω/E) → Unit → QuotSpan ((ℓ : (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ))) ^ ν)}
    (hc : c ∈ evenClasses (E := E) O S ν e)
    (h_hom_zero : ∀ u : (Unit → QuotSpan ((ℓ : (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ))) ^ ν)) →+
        ZMod (ℓ ^ ν),
      (fun g : Gal(Ω/E) ↦ u (c g)) ∈
          Z1 (charRep (ZMod (ℓ ^ ν)) (cyclotomicCharMod Ω (ℓ ^ ν) ^ e)⁻¹) →
        u b = 0) :
    b = 0 := by
  -- Characters with values in `ℚ/ℤ` separate points, and on an `ℓ ^ ν`-torsion group each of them
  -- factors through `ℤ/ℓ ^ ν`. So it is enough that `u b = 0` for all `u` to `ℤ/ℓ ^ ν`.
  have h_torsion (x : Unit → QuotSpan (ℓ ^ ν : ↑O)) : ℓ ^ ν • x = 0 :=
    funext fun j ↦ nsmul_quot_eq_zero dvd_rfl (x j)
  obtain ⟨h_cocycle, -, -, h_const⟩ := mem_selmerModule_iff.1 hc.1
  refine QZ.eq_zero_of_forall_hom_eq_zero fun v ↦ ?_
  obtain ⟨u, rfl⟩ := (QZ.bijective_ofZMod_comp h_torsion).2 v
  -- It remains to see that `u ∘ c` is a continuous cocycle for the `-e`-th power of the cyclotomic
  -- character modulo `ℓ ^ ν`.
  suffices hu : u b = 0 by simp [hu]
  refine h_hom_zero u ⟨(IsLocallyConstant.comp h_const u).continuous, fun g g' ↦ ?_⟩
  -- The `ℓ`-adic character acts on `ℤ/ℓ ^ ν` through the one modulo `ℓ ^ ν`; both are taken
  -- at `g⁻¹ ^ e`.
  have h_twist : u ((cyclotomicChar Ω ℓ g⁻¹).val ^ e • c g') =
      (cyclotomicCharMod Ω (ℓ ^ ν) (g ^ e)⁻¹).val * u (c g') := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, inv_pow,
      map_cyclotomicChar_smul u ν (fun y ↦ by simp [CharP.cast_eq_zero]), nsmul_eq_mul,
      ZMod.natCast_zmod_val]
  simpa [h_cocycle, tateTwist, cyclotomicInv, charRep, ← map_pow, ← map_inv, -map_smul] using
    h_twist
