import Lib.ClassField.Places.DecompositionCyclotomic
import Lib.General.NumberTheory.ImaginaryQuadraticField

/-!
# The parameters q₀ and d, the field E = K(ζ), its infinite places and its roots of unity

Fix a multiple `q₀` of `18480` and a prime `d ≡ q₀/2 - 1 mod q₀`. Let `K = ℚ(√-d)`, and let
`E = K(ζ)` with `ζ` of order `q₁ = q₀ * towerDeg s`. The file counts the places, describes how they
act on `ζ`, shows that every root of unity of `E` is a power of `ζ`, and writes norms from `E` to
`K` as products over the embeddings `Φ v`. In the comments `c = ⌊log₃ s⌋ + 5`, so that
`towerDeg s = 3^c 2^s`, `φ` is Euler's totient function, and `P.Φ s` is the type of infinite places
of `E`.

## Main definitions and results

* `New.Parameters`: a multiple `q₀` of `18480` and a prime `d ≡ q₀/2 - 1 mod q₀`. Then `d ≡ 7 mod 8`
  and `(p / d) = 1` for each prime `p ∣ q₁` (`New.Parameters.chiK_eq_one_of_dvd`).
* `New.Parameters.irreducible_cyclotomic`: the cyclotomic polynomial of order `q₁` is irreducible
  over `K`, so `Gal(E/K) = (ℤ/q₁)ˣ`. `E` embeds in `ℚ(ζ_{q₁ d})`, hence is abelian over `ℚ`.
* `New.Parameters.galOfPlace`, `New.Parameters.placeMulEquiv`: the infinite places of `E` form a
  group, identified with `Gal(E/K)` and `(ℤ/q₁)ˣ`. Composing a fixed embedding of `E` in `ℂ` over
  `K` with these automorphisms gives one embedding for each infinite place, the CM type of `E`.
* `New.Parameters.numInfPlaces_E`, `New.Parameters.card_placeClass_eq_one_eq_towerDeg`: there are
  `towerDeg s * φ(q₀)` places, `towerDeg s` of them of class `1` modulo `q₀`; this rests on
  `cyclotomic q₁ = (cyclotomic q₀)(X ^ towerDeg s)` (`New.Parameters.expand_towerDeg_cyclotomic`).
* `New.Parameters.exists_zeta_pow_eq`: every root of unity of `E` is a power of `ζ`.
* `New.Parameters.prod_phi_eq_norm`: the product of the images of `y` under the `K`-embeddings `Φ v`
  of `E` in `ℂ` is the norm of `y` from `E` to `K`.

The basic facts on the field `E` are proved in `Lib` or in
`New.Derivatives.Field.PrimeDecomposition`:
* the ring of integers: `New.Parameters.adjoin_betaKInE_zetaInt_eq_top`, in the latter file;
* the different of `E` over its real subfield and the places fixed by conjugation:
  `New.differentIdeal_eq_top_of_add_star_eq_one`, `New.two_notMem_of_star_eq` and
  `New.exists_sq_eq_q_of_star_eq` in `Lib`, `New.Parameters.natCast_eq_neg_one_of_star_eq` in the
  latter file.

Notions from other files:
* `New.chiK d` is the Legendre symbol `(· / d)`, the character of `ℚ(√-d)` for `d ≡ 3 mod 4`.
* `New.CMType E` is a choice, for each infinite place of the CM field `E`, of an embedding in `ℂ`
  that induces it; `Φ v` is the embedding chosen at `v`.
-/

noncomputable section

/-!
## The parameters q₀, d, the field E and its group Φ of infinite places

* `New.Parameters.q₂` and `New.Parameters.bigOmega`: the number `(q₀ d) ^ (s + 6)`, and a real
  constant built from `L'/L(1, χ_K)` and the root discriminant of `E`.
-/

section Parameters

open NumberField Polynomial IsCyclotomicExtension jacobiSym InfinitePlace IsAlgClosed cyclotomic
  NeZero IsMulCommutative

/-- The fixed parameters: a multiple `q₀` of `18480 = 16 · 3 · 5 · 7 · 11` and a prime `d` with
`d ≡ q₀/2 - 1 mod q₀`. The congruence is stated as: `q₀` divides `2 (d + 1)` but not `d + 1`.
The first part forces `q₀ ≠ 0`; as `q₀` is even, it says that `q₀/2` divides `d + 1`, and the
second part says that the quotient is odd. The exponent `ε` of the scales is not a field: it enters
only the existence of admissible data (`New.eventually_exists_data`). -/
@[local grind]
structure New.Parameters where
  /-- The modulus `q₀`. -/
  q₀ : ℕ
  /-- The prime `d` with `K = ℚ(√-d)`. -/
  d : ℕ
  /-- `q₀` is a multiple of `18480 = 16 · 3 · 5 · 7 · 11`. -/
  dvd_q₀ : 18480 ∣ q₀
  /-- `d` is prime. -/
  d_prime : d.Prime
  /-- `d ≡ q₀/2 - 1 mod q₀`, stated as: `q₀` divides `2 (d + 1)` but not `d + 1`. -/
  q₀_dvd_and_not_dvd : q₀ ∣ 2 * (d + 1) ∧ ¬q₀ ∣ d + 1

namespace New.Parameters

variable (P : Parameters) (s : ℕ)

instance : NeZero P.q₀ := ⟨by grind [zero_dvd_iff]⟩

/-- The prime `d` is congruent to 7 modulo 8: `d + 1` is an odd multiple of `q₀/2`, and `16` divides
`q₀`. -/
@[local grind! .]
instance instPrimeSevenModEight : PrimeSevenModEight P.d where
  out := P.d_prime
  mod_eight := by grind [→ dvd_trans]

/-- The number `l₀`: for `s ≥ 1`, the least power of `3` above `27 s`. -/
def _root_.New.l₀ (s : ℕ) : ℕ := 3 ^ (Nat.log 3 s + 4)

lemma _root_.New.mul_lt_l₀ (s : ℕ) : 27 * s < l₀ s := by
  have h_log : s < 3 ^ (Nat.log 3 s + 1) := Nat.lt_pow_succ_log_self (by norm_num) s
  rw [l₀, pow_add] at *
  omega

lemma _root_.New.l₀_le_mul {s : ℕ} (hs : s ≠ 0) : l₀ s ≤ 81 * s := by
  have h_log : 3 ^ Nat.log 3 s ≤ s := Nat.pow_log_le_self 3 hs
  rw [l₀, pow_add]
  omega

/-- The ratio `q₁ / q₀ = 3 l₀ 2 ^ s`; see `towerDeg_eq`. -/
def _root_.New.towerDeg : ℕ := 3 ^ (Nat.log 3 s + 5) * 2 ^ s
  deriving NeZero

lemma _root_.New.towerDeg_eq (s : ℕ) : towerDeg s = 3 * l₀ s * 2 ^ s := by
  rw [towerDeg, l₀, ← pow_succ']

/-- The order `q₁ = q₀ * towerDeg s` of the root of unity `ζ` that generates `E` over `K`. -/
abbrev q₁ : ℕ := P.q₀ * towerDeg s

lemma two_dvd_q₀ : 2 ∣ P.q₀ := (by norm_num : 2 ∣ 18480).trans P.dvd_q₀

lemma three_dvd_q₀ : 3 ∣ P.q₀ := (by norm_num : 3 ∣ 18480).trans P.dvd_q₀

/-- Let `P : Parameters` consist of the modulus `q₀` and the prime `d ≡ q₀/2 - 1 mod q₀`. Every
prime `p` dividing `P.q₁ s = q₀ * towerDeg s`, where `towerDeg s` is a power of `3` times `2 ^ s`,
divides `(d + 1) / 4`, the norm of `(1 + √-d) / 2`. -/
lemma dvd_d_add_one_div_four_of_dvd_q₁ {p s : ℕ} (hp : p.Prime) (hp_dvd : p ∣ P.q₁ s) :
    p ∣ (P.d + 1) / 4 := by
  -- The primes of `towerDeg s` are among `2` and `3`, and both divide `q₀`.
  have h_dvd_q₀ : p ∣ P.q₀ := by
    obtain h_left | h_three | h_two := (hp.dvd_mul.1 hp_dvd).imp_right hp.dvd_mul.1
    · exact h_left
    · exact (hp.dvd_of_dvd_pow h_three).trans P.three_dvd_q₀
    · exact (hp.dvd_of_dvd_pow h_two).trans P.two_dvd_q₀
  have h_mod_eight : P.d % 8 = 7 := PrimeSevenModEight.mod_eight
  have h_dvd : p ∣ 2 * (P.d + 1) := h_dvd_q₀.trans P.q₀_dvd_and_not_dvd.1
  -- As `d % 8 = 7`, this number is `2 ^ 3` times the even number `(d + 1) / 4`.
  rw [show 2 * (P.d + 1) = 2 ^ 3 * ((P.d + 1) / 4) by omega] at h_dvd
  obtain h_two | h_quot := hp.dvd_mul.1 h_dvd
  · exact (hp.dvd_of_dvd_pow h_two).trans (by omega)
  · exact h_quot

/-- The prime `d` exceeds `64`, as `2 (d + 1)` is a positive multiple of `q₀ ≥ 18480`. -/
lemma sixty_four_lt_d : 64 < P.d := by
  have h_le : 18480 ≤ 2 * (P.d + 1) := Nat.le_of_dvd (by omega)
    (P.dvd_q₀.trans P.q₀_dvd_and_not_dvd.1)
  omega

/-- Let `P : Parameters` consist of the modulus `q₀` and the prime `d ≡ q₀/2 - 1 mod q₀`. For every
prime `p` dividing `P.q₁ s = q₀ * towerDeg s`, the Legendre symbol `chiK d p = (p / d)` is `1`,
which is the criterion for `p` to split in `K = ℚ(√-d)`. -/
lemma chiK_eq_one_of_dvd {p s : ℕ} (hp : p.Prime) (hp_dvd : p ∣ P.q₁ s) : chiK P.d p = 1 := by
  -- The Jacobi symbol `(p / d)` depends on `d` only modulo `4 p`, and `d ≡ -1 mod 4 p`.
  have hp_pos : 0 < p := hp.pos
  have h_mod_eight : P.d % 8 = 7 := PrimeSevenModEight.mod_eight
  have h_dvd : 4 * p ∣ P.d + 1 := Nat.mul_dvd_of_dvd_div (by omega)
    (P.dvd_d_add_one_div_four_of_dvd_q₁ hp hp_dvd)
  have h_mod : P.d % (4 * p) = 4 * p - 1 := (Nat.mod_eq_sub_iff one_pos (by omega)).2 h_dvd
  have h_cast : (4 * p : ℤ) = 1 + (4 * p - 1 : ℕ) := by omega
  calc chiK P.d p = jacobiSym p (4 * p - 1) := by
        rw [chiK_eq_legendreSym, legendreSym.to_jacobiSym,
          mod_right' p (Nat.odd_iff.2 (by omega)), h_mod]
    -- the factor `4` is a square prime to the odd modulus
    _ = jacobiSym (4 * p : ℤ) (4 * p - 1) := by
        rw [← div_four_left (a := 4 * p) (by omega) (by omega),
          Int.mul_ediv_cancel_left _ four_ne_zero]
    _ = 1 := by rw [h_cast, mod_left' (Int.add_emod_right 1 _), one_left]

/-- A prime that does not split in `K = ℚ(√-d)`, that is `χ_K(p) ≠ 1`, is at least `13`. -/
lemma thirteen_le_of_chiK_ne_one {p : ℕ} (hp : p.Prime) (h_ne : chiK P.d p ≠ 1) : 13 ≤ p := by
  -- Every prime below `13` divides `18480`, hence `q₀` and `q₁`.
  by_contra h_lt
  have h_dvd : p ∣ 18480 := by interval_cases p <;> trivial
  exact h_ne (P.chiK_eq_one_of_dvd hp (h_dvd.trans (P.dvd_q₀.mul_right (towerDeg 0))))

/-! ### The fields `K` and `E` -/

/-- The imaginary quadratic field K = ℚ(i√d), as a subfield of ℂ. -/
abbrev K : IntermediateField ℚ ℂ := QuadField P.d

/-- The number `q₂ = (q₀ d) ^ (s + 6)`, a multiple of `q₁ d`; the three primes of the data are `≡ 1`
modulo its square. -/
def q₂ : ℕ := (P.q₀ * P.d) ^ (s + 6)
  deriving NeZero

/-- Let `P` consist of the modulus `q₀` and the prime `d`. The product `q₁ d`, where
`q₁ = q₀ * towerDeg s = q₀ * 3 ^ (⌊log₃ s⌋ + 5) * 2 ^ s` is the order of `ζ`, divides
`q₂ = (q₀ d) ^ (s + 6)`. -/
lemma q₁_mul_d_dvd_q₂ {P : Parameters} {s : ℕ} : q₁ P s * P.d ∣ P.q₂ s := by
  have h_six : 3 * 2 ∣ P.q₀ * P.d := ((by norm_num : 3 * 2 ∣ 18480).trans P.dvd_q₀).mul_right _
  calc P.q₁ s * P.d = P.q₀ * P.d * (3 ^ (Nat.log 3 s + 5) * 2 ^ s) := mul_right_comm ..
    _ ∣ P.q₀ * P.d * (3 ^ (s + 5) * 2 ^ (s + 5)) := by grw [Nat.log_le_self, ← s.le_add_right 5]
    _ ∣ P.q₀ * P.d * (P.q₀ * P.d) ^ (s + 5) := by grw [← mul_pow, h_six]
    _ = P.q₂ s := (pow_succ' ..).symm

lemma coprime_q₁_d : (P.q₁ s).Coprime P.d := by
  -- If the prime `d` divided `q₁` then `chiK d d = 1`, but the character vanishes at `d`.
  refine (P.d_prime.coprime_iff_not_dvd.2 fun h_dvd ↦ ?_).symm
  simpa [chiK, ZMod.natCast_self] using P.chiK_eq_one_of_dvd P.d_prime h_dvd

/-- The field E = K(ζ) obtained from K by adjoining a primitive root of unity ζ of order q₁ = 3^c
2^s q₀. -/
def E : Type := CyclotomicField (P.q₁ s) P.K
  deriving Field, Algebra P.K, NumberField

/-- The infinite places of the field E = K(ζ) at level s; they carry the group structure of
Gal(E/K) (`New.Parameters.galOfPlace`). -/
protected abbrev Φ : Type := InfinitePlace (P.E s)

/-- The real number exp(γ − Re L′/L(1, χ_K))·2π/rd_E, with γ Euler's constant and rd_E the
root discriminant of E. -/
def bigOmega : ℝ := Real.exp (chowlaSelbergConst P.d) * (2 * Real.pi / rootDiscr (P.E s))

instance : IsCyclotomicExtension {P.q₁ s} P.K (P.E s) := CyclotomicField.isCyclotomicExtension ..

/-- Let `P : Parameters` consist of the modulus `q₀` and the prime `d`, and let `s` be a natural
number. For `P.q₁ s = q₀ * towerDeg s`, the cyclotomic polynomial of order `P.q₁ s` is irreducible
over the quadratic field `P.K = ℚ(√-d)`. -/
lemma irreducible_cyclotomic : Irreducible (cyclotomic (P.q₁ s) P.K) := by
  -- Embed `K` in `M = ℚ(ζ_d)` and prove irreducibility over `M`: as `q₁` is prime to `d`, the field
  -- `L = M(ζ_{q₁})` has degree at least `φ(d) φ(q₁)` over `ℚ`, so at least `φ(q₁)` over `M`.
  let M : IntermediateField ℚ Ω := cycloField P.d
  let L : Type := CyclotomicField (P.q₁ s) M
  have hζ : IsPrimitiveRoot (zeta (P.q₁ s) M L) (P.q₁ s) := zeta_spec (P.q₁ s) M L
  have h_deg : P.d.totient * (P.q₁ s).totient ≤ P.d.totient * Module.finrank M L := by
    rw [← IsCyclotomicExtension.Rat.finrank P.d M, Module.finrank_mul_finrank,
      IsCyclotomicExtension.Rat.finrank P.d M]
    exact totient_mul_totient_le_finrank _ _ (P.coprime_q₁_d s) hζ
      ((zeta_spec P.d ℚ M).map_of_injective (algebraMap M L).injective)
  have h_finrank : Module.finrank M L = (minpoly M (zeta (P.q₁ s) M L)).natDegree := by
    simp [(hζ.powerBasis M).finrank]
  -- Hence the cyclotomic polynomial is the minimal polynomial of `ζ_{q₁}` over `M`.
  have h_assoc : Associated (minpoly M (zeta (P.q₁ s) M L)) (cyclotomic (P.q₁ s) M) := by
    apply associated_of_dvd_of_natDegree_le (minpoly.dvd_iff.2 (aeval_zeta ..)) (monic ..).ne_zero
    rw [natDegree_cyclotomic, ← h_finrank]
    exact Nat.le_of_mul_le_mul_left h_deg (Nat.totient_pos.2 (NeZero.pos P.d))
  -- Irreducibility descends along the embedding of `K` in `M` given by the Gauss sum.
  refine (monic (P.q₁ s) P.K).irreducible_of_irreducible_map
    (QuadField.embOfPrimitiveRoot P.d (zeta_spec P.d ℚ M)).toRingHom (cyclotomic (P.q₁ s) P.K) ?_
  simpa using h_assoc.irreducible (minpoly.irreducible (.of_finite M _))

/-- A chosen ℚ-algebra embedding of E = K(ζ), ζ of order q₁, into the cyclotomic field
ℚ(ζ_{q₁d}). -/
def toCycloField {P : Parameters} {s : ℕ} : E P s →ₐ[ℚ] cycloField (P.q₁ s * P.d) :=
  have hζ := zeta_spec (P.q₁ s * P.d) ℚ (cycloField (P.q₁ s * P.d))
  -- `ζ ^ q₁` is a primitive `d`-th root of unity, so the Gauss sum embeds `K`.
  let := (QuadField.embOfPrimitiveRoot P.d (hζ.pow NeZero.one_le rfl)).toAlgebra
  -- `ζ ^ d` is a primitive `q₁`-th root of unity: the cyclotomic polynomial of order `q₁` splits.
  (SplittingField.lift _ (by
    simp [cyclotomic_eq_prod_X_sub_primitiveRoots (hζ.pow one_le (mul_comm ..))])).toRatAlgHom

instance : IsAbelianGalois ℚ (P.E s) := (isAbelianGalois {P.q₁ s * P.d} ..).of_algHom toCycloField

instance : IsAbelianGalois P.K (P.E s) := .tower_top ℚ ..

instance : IsTotallyComplex (P.E s) := isTotallyComplex_of_algebra P.K _

/-! ### The infinite places of `E` as a group -/

/-- Two `K`-embeddings of `E` in `ℂ` that induce the same infinite place are equal. -/
lemma algHom_eq_of_mk_eq {φ ψ : P.E s →ₐ[P.K] ℂ}
    (h_mk : InfinitePlace.mk φ.toRingHom = InfinitePlace.mk ψ.toRingHom) : φ = ψ := by
  obtain h_eq | h_conj := mk_eq_iff.1 h_mk
  · exact AlgHom.toRingHom_injective h_eq
  · -- Restricted to `K`, this says that the embedding of the imaginary field `K` is real.
    have h_real : ComplexEmbedding.IsReal (algebraMap P.K ℂ) := RingHom.ext fun x ↦ by
      simpa using RingHom.congr_fun h_conj (algebraMap P.K (P.E s) x)
    exact absurd h_real (IsTotallyComplex.complexEmbedding_not_isReal _)

/-- The infinite places of E form a commutative group. The law is transported from Gal(E/K) along
the bijection that sends g to the place of a fixed embedding of E over K composed with g. -/
instance : CommGroup (P.Φ s) :=
  (Equiv.ofBijective (fun g : Gal(P.E s/P.K) ↦ InfinitePlace.mk (lift.comp g.toAlgHom).toRingHom)
    (by
      refine ⟨fun g g' h ↦ AlgEquiv.ext fun x ↦ ?_, fun w ↦ ?_⟩
      · exact lift.injective (AlgHom.congr_fun (P.algHom_eq_of_mk_eq s h) x)
      · -- All infinite places of `E` lie above the one infinite place of `K`, so they are
        -- conjugate, and `g` sends the place of an embedding `φ` to that of `φ ∘ g⁻¹`.
        obtain ⟨g, hg⟩ : ∃ g : Gal(P.E s/P.K),
            g • InfinitePlace.mk (lift : P.E s →ₐ[P.K] ℂ).toRingHom = w :=
          exists_smul_eq_of_comap_eq (k := P.K) (by subsingleton)
        exact ⟨g⁻¹, hg⟩)).symm.commGroup

/-- The isomorphism v ↦ σ_v from the group of infinite places of E to Gal(E/K). The place that
corresponds to a in (ℤ/q₁)^× goes to the automorphism ζ ↦ ζ^a. -/
def galOfPlace : P.Φ s ≃* Gal(P.E s/P.K) := Equiv.mulEquiv _

/-- The group isomorphism from the group of infinite places of E to (ℤ/q₁)^×. It is the composite of
`New.Parameters.galOfPlace` with the isomorphism Gal(E/K) ≅ (ℤ/q₁)^× given by the action on ζ. -/
def placeMulEquiv : P.Φ s ≃* (ZMod (P.q₁ s))ˣ :=
  (P.galOfPlace s).trans (autEquivPow (P.E s) (P.irreducible_cyclotomic s))

/-- The infinite place of E named by the class of the integer ν modulo q₁ if ν is prime to q₁, and
the identity place otherwise. -/
def placeOfInt (ν : ℤ) : P.Φ s :=
  if h : IsUnit (Int.cast ν) then (P.placeMulEquiv s).symm h.unit else 1

/-- For a divisor m of q₁, the homomorphism from the group of infinite places of E, identified with
(ℤ/q₁)^×, to (ℤ/m)^× given by reduction modulo m. -/
def placeClass {s m : ℕ} (d : m ∣ P.q₁ s) : P.Φ s →* (ZMod m)ˣ :=
  (ZMod.unitsMap d).comp (P.placeMulEquiv s).toMonoidHom

/-- A chosen primitive q₁-th root of unity ζ in E. -/
def ζ : P.E s := zeta (P.q₁ s) P.K (P.E s)

/-- The CM type of E: the embedding at the place v is a fixed embedding of E over K composed with
the automorphism `New.Parameters.galOfPlace` s v. -/
instance : CMType (P.E s) where
  Φ v := (lift.comp (P.galOfPlace s v).toAlgHom).toRingHom
  mk_Φ := (P.galOfPlace s).left_inv

/-- For each infinite place `v` of `E`, the embedding `Φ v` of `E` into `ℂ` chosen at `v` restricts
on `K` to the inclusion of `K` in `ℂ`: `Φ v (algebraMap K E x) = x`. -/
@[simp]
lemma phi_algebraMap (v : InfinitePlace (P.E s)) (x : P.K) :
    Φ v (algebraMap P.K (P.E s) x) = x := by simp [Φ]

end New.Parameters

end Parameters

/-!
## The order of Φ, classes of places and the action on roots of unity

`New.Parameters.placeClass` is the class of a place modulo a divisor of `q₁`, and
`New.Parameters.placeOfInt` is the place named by an integer prime to `q₁` (the identity for other
integers).

* `New.Parameters.galOfPlace_zeta`, `New.Parameters.galOfPlace_placeOfInt_zeta`: a place acts on `ζ`
  by raising it to the power that names it.
-/

section InfinitePlaces

open IsCyclotomicExtension Finset Polynomial Complex Fintype ZMod NeZero

namespace New.Parameters

variable {P : Parameters} {s : ℕ}

/-- If the prime `p` divides `N`, then substituting `X ^ (p ^ k)` in the cyclotomic polynomial of
order `N` gives that of order `N p ^ k`, over any commutative ring `R`. -/
lemma expand_pow_cyclotomic {p N : ℕ} (hp : p.Prime) (hpN : p ∣ N) (k : ℕ) (R : Type*)
    [CommRing R] : expand R (p ^ k) (cyclotomic N R) = cyclotomic (N * p ^ k) R := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- One more factor `p`: substituting `X ^ p` in `cyclotomic M` gives `cyclotomic (M p)` for
    -- `p ∣ M = N p ^ k`.
    rw [pow_succ', expand_mul, ih, cyclotomic_expand_eq_cyclotomic hp (hpN.mul_right _)]
    ring_nf

lemma expand_towerDeg_cyclotomic :
    expand ℂ (towerDeg s) (cyclotomic P.q₀ ℂ) = cyclotomic (P.q₁ s) ℂ := by
  -- `towerDeg s` is a power of 3 times a power of 2, and both primes divide `q₀`.
  rw [q₁, towerDeg, expand_mul, expand_pow_cyclotomic Nat.prime_two P.two_dvd_q₀,
    expand_pow_cyclotomic Nat.prime_three (P.three_dvd_q₀.mul_right _), mul_right_comm, mul_assoc]

/-- The number of infinite places `Core.numInfPlaces` of E = K(ζ), ζ of order q₁ = 3^c 2^s q₀, is
3^c 2^s φ(q₀), where 3^c 2^s = `New.towerDeg` s and φ is Euler's totient function. -/
lemma numInfPlaces_E (s : ℕ) : Core.numInfPlaces (P.E s) = towerDeg s * P.q₀.totient := by
  -- The places correspond to `(ZMod q₁)ˣ`; compare degrees in `expand_towerDeg_cyclotomic`.
  have h_deg : (P.q₁ s).totient = P.q₀.totient * towerDeg s := by
    simp [← natDegree_cyclotomic _ ℂ, ← expand_towerDeg_cyclotomic, natDegree_expand]
  simp [card_congr (P.placeMulEquiv s).toEquiv, h_deg, mul_comm]

/-- Given that `P.q₀` divides `P.q₁ s` (`h_dvd`), exactly `towerDeg s = P.q₁ s / P.q₀` elements `v`
of `P.Φ s`, the infinite places of `P.E s`, have class `1` modulo `P.q₀`
(`New.Parameters.placeClass`). -/
lemma card_placeClass_eq_one_eq_towerDeg (h_dvd : P.q₀ ∣ P.q₁ s) :
    #{v : P.Φ s | P.placeClass h_dvd v = 1} = towerDeg s := by
  -- The homomorphism `P.placeClass h_dvd` is onto `(ZMod q₀)ˣ`, so its kernel has index `φ(q₀)` in
  -- the group of the `towerDeg s * φ(q₀)` infinite places.
  have h_index : (P.placeClass h_dvd).ker.index = P.q₀.totient := by
    simp [placeClass, Subgroup.index_ker, unitsMap_surjective]
  simpa [h_index, numInfPlaces_E, ne, Fintype.card_subtype] using
    (P.placeClass h_dvd).ker.card_mul_index

lemma isPrimitiveRoot_zeta : IsPrimitiveRoot (P.ζ s) (P.q₁ s) := zeta_spec ..

/-! ### The action on the root of unity, and places named by integers -/

/-- The embedding `Φ (v * v')` at the place `v * v'` is `Φ v` composed with the automorphism
`P.galOfPlace s v'` of `P.E s` attached to `v'`: `Φ (v * v') x = Φ v (P.galOfPlace s v' x)`. -/
lemma phi_mul (v v' : P.Φ s) (x : P.E s) : Φ (v * v') x = Φ v (P.galOfPlace s v' x) := by simp [Φ]

/-- The involution `star` of the CM field `E` inverts `ζ`. -/
@[simp]
lemma star_zeta : star (P.ζ s) = (P.ζ s)⁻¹ := by
  -- Under an embedding in `ℂ` a root of unity has norm `1`, so its inverse is its conjugate.
  have h_norm : ‖Φ 1 (P.ζ s)‖ = 1 :=
    (isPrimitiveRoot_zeta.map_of_injective (Φ 1).injective).norm'_eq_one out
  exact (Φ 1).injective (by simp [inv_eq_conj h_norm])

/-- The automorphism attached to the place `v` raises `ζ` to the residue modulo `q₁` that names
`v`, that is, the image of `v` in `(ℤ/q₁)ˣ` under `New.Parameters.placeMulEquiv`. -/
lemma galOfPlace_zeta (v : P.Φ s) :
    P.galOfPlace s v (P.ζ s) = P.ζ s ^ (P.placeMulEquiv s v : ZMod (P.q₁ s)).val := by
  simp [placeMulEquiv, ζ]

lemma two_pow_dvd_q₁ : 2 ^ (s + 1) ∣ P.q₁ s :=
  (dvd_of_eq (pow_succ' 2 s)).trans (mul_dvd_mul P.two_dvd_q₀ (dvd_mul_left _ _))

/-- The `i`-th power of the place named by `ν` is the place named by `ν ^ i`. This holds also for
`ν` not prime to `q₁`, when both sides are the identity place. -/
lemma placeOfInt_pow {ν : ℤ} (i : ℕ) : P.placeOfInt s ν ^ i = P.placeOfInt s (ν ^ i) := by
  by_cases h_unit : IsUnit (ν : ZMod (P.q₁ s))
  · have h_eq : (h_unit.pow i).unit = h_unit.unit ^ i := Units.ext (by simp)
    simp [placeOfInt, h_unit, h_unit.pow i, h_eq]
  · cases i <;> simp [placeOfInt, h_unit]

/-- For `ν` prime to `q₀`, the place named by `ν` (`New.Parameters.placeOfInt`) corresponds to the
residue of `ν` under the isomorphism of the group of places with `(ℤ/q₁)ˣ`. -/
lemma placeMulEquiv_placeOfInt {ν : ℤ} (h_cop : IsCoprime ν P.q₀) :
    (P.placeMulEquiv s (P.placeOfInt s ν) : ZMod (P.q₁ s)) = ν := by
  -- `ν` is prime to `2` and `3`, which divide `q₀`, hence to `q₁ = q₀ 3 ^ c 2 ^ s`.
  have h_two : IsCoprime 2 ν := h_cop.symm.mono (mod_cast P.two_dvd_q₀) dvd_rfl
  have h_three : IsCoprime 3 ν := h_cop.symm.mono (mod_cast P.three_dvd_q₀) dvd_rfl
  have h_unit : IsUnit (ν : ZMod (P.q₁ s)) := by
    simp [towerDeg, coe_int_isUnit_iff_isCoprime, IsCoprime.mul_left_iff, IsCoprime.pow_left,
      h_cop.symm, h_two, h_three]
  simp [placeOfInt, h_unit]

/-- For `ν` prime to `q₀`, the place named by `ν` (`New.Parameters.placeOfInt`) has class `ν` modulo
each divisor `m` of `q₁`, `placeClass` being the reduction to `(ℤ/m)ˣ` of `(ℤ/q₁)ˣ`. -/
lemma placeClass_placeOfInt {ν : ℤ} (h_cop : IsCoprime ν P.q₀) {m : ℕ} {h_dvd : m ∣ P.q₁ s} :
    (P.placeClass h_dvd (P.placeOfInt s ν) : ZMod m) = ν := by
  simp [placeClass, unitsMap_val, placeMulEquiv_placeOfInt h_cop, h_dvd]

/-- For an integer ν prime to q₀, the element of Gal(E/K) attached to the infinite place named by ν
(`New.Parameters.placeOfInt`) sends the chosen primitive q₁-th root of unity ζ to ζ^ν. -/
lemma galOfPlace_placeOfInt_zeta {ν : ℤ} (h_cop : IsCoprime ν P.q₀) :
    P.galOfPlace s (P.placeOfInt s ν) (P.ζ s) = P.ζ s ^ ν := by
  -- The exponent in `galOfPlace_zeta` is `ν % q₁`, and `ζ ^ q₁ = 1`.
  calc P.galOfPlace s (P.placeOfInt s ν) (P.ζ s) = P.ζ s ^ (ν % (P.q₁ s : ℤ)) := by
        rw [galOfPlace_zeta, placeMulEquiv_placeOfInt h_cop, ← zpow_natCast, val_intCast]
    _ = P.ζ s ^ ν := by
        rw [Int.emod_def, zpow_sub₀ (isPrimitiveRoot_zeta.ne_zero (NeZero.ne _)), zpow_mul,
          isPrimitiveRoot_zeta.zpow_eq_one, one_zpow, div_one]

/-- For parameters `P`, no power of the prime `d` is congruent to `-1` modulo `q₀`. As `d` is odd
and `q₀` divides `2 (d + 1)` but not `d + 1`, we have `d ^ 2 = 1` in `ZMod q₀`, and the powers `1`
and `d` of `d` both differ from `-1`. -/
lemma d_pow_ne_neg_one (n : ℕ) : (P.d : ZMod P.q₀) ^ n ≠ -1 := by
  -- In `ZMod q₀` we have `2 (d + 1) = 0` and `d + 1 ≠ 0`, with `d = 2 w + 1` odd. So `d ^ 2 = 1`,
  -- and the powers of `d` are `1` and `d`, both different from `-1`.
  obtain ⟨w, hw⟩ : Odd P.d := P.d_prime.odd_of_ne_two (P.sixty_four_lt_d.trans' (by norm_num)).ne'
  have hd : (P.d : ZMod P.q₀) = 2 * w + 1 := by simp [hw]
  have h_zero : 2 * (P.d + 1 : ZMod P.q₀) = 0 :=
    mod_cast (natCast_eq_zero_iff _ _).2 P.q₀_dvd_and_not_dvd.1
  have h_ne : (P.d + 1 : ZMod P.q₀) ≠ 0 :=
    mod_cast (natCast_eq_zero_iff _ _).not.2 P.q₀_dvd_and_not_dvd.2
  have h_sq : (P.d : ZMod P.q₀) ^ 2 = 1 := by linear_combination (P.d + 1) * hd + w * h_zero
  induction n using Nat.twoStepInduction with
  | zero =>
    -- If `1 = -1` then `2 = 0`, so `d + 1 = 2 (w + 1) = 0`.
    exact fun h_one ↦ h_ne (by linear_combination hd + (w + 1) * h_one)
  | one => exact fun h_one ↦ h_ne (by linear_combination h_one)
  | more n ih _ => simpa [pow_add, h_sq] using ih

/-- Let `ν` be an integer and suppose `q₀ ∣ q₁`. The place `P.placeOfInt s ν` of `E` is the one that
corresponds to `ν mod q₁` under the isomorphism of the group of places with `(ℤ/q₁)ˣ` if `ν` is a
unit modulo `q₁`, and the identity place otherwise; `P.placeClass h_dvd` reduces the element of
`(ℤ/q₁)ˣ` of a place modulo `q₀`. This class is `-1` if and only if `ν ≡ -1` modulo `q₀`. -/
@[simp]
lemma placeClass_placeOfInt_eq_neg_one_iff {ν : ℤ} (h_dvd : P.q₀ ∣ P.q₁ s) :
    P.placeClass h_dvd (P.placeOfInt s ν) = -1 ↔ (ν : ZMod P.q₀) = -1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- If `ν` is no unit mod `q₁` then `P.placeOfInt s ν = 1`, whose class is `1 ≠ -1`.
    have h_val : (if IsUnit (ν : ZMod (P.q₁ s)) then (ν : ZMod P.q₀) else 1) = -1 := by
      simpa [placeOfInt, apply_dite, placeClass, Units.ext_iff, unitsMap_val] using h
    split_ifs at h_val
    · exact h_val
    · exact absurd h_val (by simpa using P.d_pow_ne_neg_one 0)
  · have h_cop : IsCoprime ν P.q₀ := ((coe_int_isUnit_iff_isCoprime ..).1 (by simp [h])).symm
    simp [Units.ext_iff, placeClass_placeOfInt h_cop, h]

end New.Parameters

end InfinitePlaces

/-! ## Roots of unity of E and norms to K -/

namespace New.Parameters

variable {P : Parameters} {s : ℕ}

/-- For parameters `P : Parameters` and a level `s` (both implicit), every root of unity `y`
(element of finite order) of the field `P.E s` is a power `ζ P s ^ k` with `k < P.q₁ s`. -/
lemma exists_zeta_pow_eq {y : P.E s} (hy : IsOfFinOrder y) : ∃ k < P.q₁ s, ζ P s ^ k = y := by
  -- Embed `E` in `ℚ(ζ_{q₁ d})` to get `y ^ (q₁ d) = 1`. If `y ^ q₁ ≠ 1`, then `E` contains
  -- primitive roots of unity of orders `q₁` and `d`, which is too much for its degree.
  refine isPrimitiveRoot_zeta.eq_pow_of_pow_eq_one ?_
  by_contra h_ne
  have : NeZero (orderOf y) := ⟨hy.orderOf_pos.ne'⟩
  -- The roots of unity of `ℚ(ζ_{q₁ d})` form a group of order `q₁ d`, this number being even.
  have h_dvd : orderOf y ∣ P.q₁ s * P.d := by
    simpa [IsCyclotomicExtension.Rat.torsionOrder_eq (n := P.q₁ s * P.d), parity_simps,
      even_iff_two_dvd.2 P.two_dvd_q₀] using NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot
        ((IsPrimitiveRoot.orderOf y).map_of_injective toCycloField.injective)
  -- As `d` is prime and `y ^ q₁ ≠ 1`, the order of `y ^ q₁` is exactly `d`.
  have h_prim : IsPrimitiveRoot (y ^ P.q₁ s) P.d :=
    .iff_orderOf.2 (orderOf_eq_prime (by rwa [← pow_mul, ← orderOf_dvd_iff_pow_eq_one]) h_ne)
  -- `φ(d) φ(q₁) ≤ [E : ℚ] = 2 φ(q₁)`, while `64 < d`.
  have h_finrank : Module.finrank ℚ (P.E s) = 2 * (P.q₁ s).totient := by
    simp [finrank_eq_two_mul_card_infinitePlace, Fintype.card_congr (P.placeMulEquiv s).toEquiv]
  have h_mul : P.d.totient * (P.q₁ s).totient ≤ 2 * (P.q₁ s).totient :=
    (totient_mul_totient_le_finrank _ _ (P.coprime_q₁_d s) isPrimitiveRoot_zeta h_prim).trans
      h_finrank.le
  rw [Nat.totient_prime P.d_prime] at h_mul
  have h_le : P.d - 1 ≤ 2 := Nat.le_of_mul_le_mul_right h_mul (Nat.totient_pos.2 (NeZero.pos _))
  exact absurd P.sixty_four_lt_d (by omega)

/-- The norm of `ζ` from `E` to `K` is `1`, as `q₁ ≠ 2`. -/
lemma norm_zeta_eq_one : Algebra.norm P.K (ζ P s) = 1 := by
  have h_le : 18480 ≤ P.q₁ s := Nat.le_of_dvd (NeZero.pos _) (P.dvd_q₀.mul_right _)
  exact isPrimitiveRoot_zeta.norm_eq_one (by omega) (P.irreducible_cyclotomic s)

/-- Let `Φ v` be the embedding of `E` in `ℂ` chosen at the infinite place `v`: it induces `v` and
fixes `K = ℚ(√-d)`, and each `K`-embedding of `E` is `Φ v` for exactly one place `v`. The product
over all `v` of the images `Φ v y` is the norm of `y` from `E` to `K`, seen in `ℂ`. -/
lemma prod_phi_eq_norm {y : P.E s} :
    ∏ v : NumberField.InfinitePlace (P.E s), Φ v y = Algebra.norm P.K y := by
  -- The norm is the product of the Galois conjugates `galOfPlace v y`; apply the embedding `Φ 1`,
  -- which fixes `K` and carries `galOfPlace v y` to `Φ v y`.
  have h_conj (v : P.Φ s) : Φ v y = Φ 1 (P.galOfPlace s v y) := by simpa using phi_mul 1 v y
  have h_norm : algebraMap P.K (P.E s) (Algebra.norm P.K y) = ∏ v, P.galOfPlace s v y := by
    rw [Algebra.norm_eq_prod_automorphisms]
    exact ((P.galOfPlace s).toEquiv.prod_comp (· y)).symm
  simp [← phi_algebraMap P s 1 (Algebra.norm P.K y), h_norm, h_conj]

end New.Parameters

end
