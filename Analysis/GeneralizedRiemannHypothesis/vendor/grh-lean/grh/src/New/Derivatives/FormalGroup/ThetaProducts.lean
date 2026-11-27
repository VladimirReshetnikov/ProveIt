import New.Derivatives.Divisibility.NormalForm
import New.Derivatives.FormalGroup.Exponent
import New.Derivatives.FormalGroup.Resolution
import New.Derivatives.Vacuum.TightFrames

/-!
# The normal form of theta products at non-split primes

The file treats products of theta functions at a prime `p` that is not split in `K = ℚ(√-d)`. Here
`θ` is the theta function of the CM curve, `y` the parameter `C.translatedY` of the curve, composed
with the forms `u† z`, and `E` is `K` with a root of unity adjoined.

The vectors `u` of `Eⁿ` form a resolution of the identity and are integral above `p`. The partner of
an infinite place `τ` of `E` is `-p ^ e τ`, and `Γ_e` is the coupling of the places with their
partners. Congruences modulo `π_p` between powers at a place and conjugation at its partner lead to
a normal form for `∏ θ(u_j† z) ^ m j` times an integral series in the `y(u† z)`.

## Main definitions and results

* `New.Parameters.norm_pow_sub_conj_partner_le`: for `e` in `I_p°`, modulo `π_p`, the `p ^ e`-th
  power at a place `τ` is complex conjugation at its partner `-p ^ e τ`.
* `New.Parameters.piPrimeInt_dvd_sum_linearSeries_sub_coupling`: at a non-split `p`, for a
  resolution of the identity by vectors `u` integral above `p`, the sum
  `∑ m j * (u_j† z) ^ p ^ e * (u_j† z)` is the coupling `Γ_e` modulo `π_p` for `e` in `I_p°`.
* `New.Parameters.exists_hasNormalForm`: at a non-split prime `p`, for a resolution of the identity
  by vectors `u` integral above `p`, the product `∏ θ(u_j† z) ^ m j` times an integral series in the
  `y(u† z)` has the normal form.

Notions from other files:
* `New.piPrime`, `New.piPrimeInt`: the number `π_p`, which is `√-d` if `p = d` and `p` otherwise, in
  `ℂ` and in the valuation ring (through the embedding `ιₚ : ℂ → ℂ_p`).
* `New.chiK`, `New.partnerExponents`: the character `χ_K`, with `χ_K(p) ≠ 1` at non-split `p`, and
  the set `I_p°` of exponents `e`: the odd ones if `p` is inert, all if `p = d`, none if `p` splits.
* `New.IsResolution`: the vectors `u` with multiplicities `m` satisfy `z = ∑ m j (u_j† z) u_j`,
  where `u† z = ∑ conj (τ(u_c)) z_(τ,c)`.
* `New.coupling`, `New.HasNormalForm`: `Γ_e = ∑ z_(τ,c) ^ p ^ e * z_(τ',c)` with `τ'` the partner
  of `τ`, and `F(ϖ z) = W exp (c_ϖ ∑ λ_{e j} Γ_e ^ p ^ j)` with `W` integral.
-/

/-! ## Substitution of a linear form -/

section LinearForm

open Finset MvPowerSeries Nat Finsupp

namespace New

variable {p : ℕ} [Fact p.Prime] {X : Type} [Fintype X]

open MvPolynomial

/-- The coefficient of `z ^ D` in `g(∑ c_x z_x)` is `c ^ D g⁽ⁿ⁾(0) / D!` with `n = |D|`, where
`c ^ D = ∏ c_x ^ D_x`, `D! = ∏ D_x!` and `g⁽ⁿ⁾(0)` is `n!` times the `n`-th coefficient of `g`. -/
@[simp] lemma coeff_subst_linearSeries {D : X →₀ ℕ} (c : X → ℂ_[p]) (g : PowerSeries ℂ_[p]) :
    (g.subst (linearSeries c)).coeff D =
      (∏ x : X, c x ^ D x) * (D.degree ! * g.coeff D.degree) / ∏ x : X, ((D x)! : ℂ_[p]) := by
  -- Apply the chain rule to the jet along the monomial `z ^ D`, and evaluate both jets.
  have h_monomial : linSubst (fun _ : Unit ↦ c) (monomial D 1) =
      (∏ x : X, c x ^ D x) • MvPolynomial.X () ^ D.degree := by
    simp only [linSubst, aeval_monomial]
    simp [prod_fintype, smul_pow, prod_smul, prod_pow_eq_pow_sum, degree_eq_sum]
  have h_chain : jet ℂ_[p] (monomial D 1) (g.subst (linearSeries c)) =
      jet ℂ_[p] (linSubst (fun _ : Unit ↦ c) (monomial D 1)) g :=
    jet_subst_linearSeries (fun _ : Unit ↦ c) (monomial D 1) g
  rw [h_monomial, X_pow_eq_monomial, map_smul, LinearMap.smul_apply, jet_monomial,
    jet_monomial] at h_chain
  rw [eq_div_iff (Finset.prod_ne_zero_iff.2 fun x _ ↦ mod_cast factorial_ne_zero (D x)), mul_comm]
  simpa [prod_fintype, PowerSeries.coeff] using h_chain

/-- Scaling all variables of `g(∑ c_x z_x)` by `a` is scaling the variable of `g` by `a`. -/
@[simp] lemma rescale_subst_linearSeries {a : ℂ_[p]} (c : X → ℂ_[p]) (g : PowerSeries ℂ_[p]) :
    rescale (fun _ : X ↦ a) (g.subst (linearSeries c)) = (g.rescale a).subst (linearSeries c) := by
  ext D
  simp [coeff_subst_linearSeries, prod_pow_eq_pow_sum, degree_eq_sum, field,
    -subst_rescale_eq_subst_smul]

end New

end LinearForm

/-!
## Partners of places and couplings

The congruence for powers at partners compares two ring maps on generators of `𝓞 E`. It turns the
identity `∑ m_j τ(u_{j,c}) (u_j† z) = z_(τ,c)` into the congruence for the coupling.
-/

section Partner

open MvPowerSeries ComplexConjugate NumberField Finset

namespace New

/-- An element of the valuation ring of `ℂ_p` is divisible by `π_p` (`√-d` if `p = d`, else `p`)
exactly when its norm is at most that of `π_p`. -/
lemma piPrimeInt_dvd_iff {d p : ℕ} [PrimeSevenModEight d] [Fact p.Prime] [PadicPlace p]
    {x : valRingCp p} : piPrimeInt d ∣ x ↔ ‖(x : ℂ_[p])‖ ≤ ‖ιₚ (piPrime d p)‖ :=
  dvd_iff_norm_le

namespace Parameters

/-- The partner `-p ^ e τ` of an infinite place `τ` of `E`. Here `P` fixes the prime `d` and the
modulus `q₀`, and `E = P.E s` is `K = ℚ(√-d)` with a root of unity of order `q₁ = P.q₁ s` adjoined,
`s` being the level in the tower of these fields. The infinite places `P.Φ s` of `E` form the group
`Gal(E/K) = (ℤ/q₁)ˣ`, and the partner is the product of `τ` with `P.placeOfInt s (-p ^ e)`, the
place of the class of `-p ^ e` modulo `q₁` (the identity if this class is not a unit). -/
noncomputable def partner (P : Parameters) (s p e : ℕ) (τ : P.Φ s) : P.Φ s :=
  P.placeOfInt s (-p ^ e) * τ

/-- Let `p` be non-split in `K = ℚ(√-d)` (`χ_K(p) ≠ 1`) and let `ϖ` have valuation
`ρ_p = varpiValuation P.d p`, which is `1 / (p² - 1)` if `p` is inert and `1 / (2 p - 2)` if
`p = d`. Then `c_ϖ π_p` has valuation `1 / (p - 1)`, where `c_ϖ = ϖ ^ (p + 1) / p` and `π_p` is
`√-d` if `p = d` and `p` otherwise. -/
lemma norm_pow_succ_div_mul_piPrimeInt (P : Parameters) {p : ℕ} [Fact p.Prime] [PadicPlace p]
    (hp : chiK P.d p ≠ 1) {ϖ : ℂ_[p]} (hϖ : ‖ϖ‖ = p ^ (-varpiValuation P.d p)) :
    ‖ϖ ^ (p + 1) / p * (piPrimeInt P.d : valRingCp p)‖ = p ^ (-(1 / (p - 1)) : ℝ) := by
  -- The valuations of `ϖ ^ (p + 1)`, `1 / p` and `π_p` add up to `1 / (p - 1)`.
  have hp_gt : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  have h_exponent :
      -varpiValuation P.d p * (p + 1) + 1 + -piPrimeValuation P.d p = -(1 / (p - 1)) := by
    have hp_sub : (p : ℝ) - 1 ≠ 0 := by linarith
    obtain ⟨rfl, -⟩ | ⟨h_ne, h_split | h_inert⟩ := chiK_cases P.d p
    · grind [varpiValuation_self, piPrimeValuation_self]
    · exact absurd h_split hp
    · have hp_sq : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
      rw [varpiValuation_of_inert h_inert, piPrimeValuation_of_ne h_ne]
      field
  rw [norm_mul, norm_div, norm_pow, hϖ, norm_p_eq_inv, norm_piPrimeInt, ← h_exponent,
    Real.rpow_add (by positivity), Real.rpow_add (by positivity), Real.rpow_one, div_inv_eq_mul,
    ← Real.rpow_mul_natCast (by positivity), Nat.cast_add, Nat.cast_one]

/-- Let `E = P.E s` be `K = ℚ(√-d)` (`d = P.d`) with a root of unity of order `q₁ = P.q₁ s`
adjoined, `s` being the level in the tower of these fields. Let `e` be in
`I_p° = partnerExponents P.d p`. Let `τ : P.Φ s` be an infinite place of `E`, and
`τ' = -p ^ e τ = P.partner s p e τ` its partner: the product of `τ` with the class of `-p ^ e` in
the group `Gal(E/K) = (ℤ/q₁)ˣ` of places. Then `τ(α) ^ p ^ e ≡ conj (τ'(α))` modulo `π_p` for `α` in
`𝓞 E`. -/
lemma norm_pow_sub_conj_partner_le {P : Parameters} {s p : ℕ} [Fact p.Prime] [PadicPlace p] {e : ℕ}
    (he : e ∈ partnerExponents P.d p) (τ : P.Φ s) (α : 𝓞 (P.E s)) :
    ‖ιₚ (Φ τ α) ^ p ^ e - ιₚ (conj (Φ (P.partner s p e τ) α))‖ ≤ ‖ιₚ (piPrime P.d p)‖ := by
  classical
  -- Both sides are ring maps to `𝒪 / π_p`. By `forall_map_galOfPlaceInt_eq_pow_iff` it suffices
  -- that they agree at the root of unity, which holds by the choice of the partner, and at `√-d`.
  let toValRing : 𝓞 (P.E s) →+* valRingCp p :=
    ((ιₚ.comp (Φ τ)).comp (algebraMap (𝓞 (P.E s)) (P.E s))).codRestrict (valRingCp p)
      fun x ↦ (norm_ringOfIntegers_le (ιₚ.comp (Φ τ)) x :)
  have h_coe (x : 𝓞 (P.E s)) : (toValRing x : ℂ_[p]) = ιₚ (Φ τ x) := rfl
  let modPiPrime : valRingCp p →+* valRingCp p ⧸ Ideal.span {piPrimeInt P.d} := reducePiPrime P.d
  have h_mod_eq_zero (x : valRingCp p) :
      modPiPrime x = 0 ↔ ‖(x : ℂ_[p])‖ ≤ ‖ιₚ (piPrime P.d p)‖ := by
    rw [Ideal.Quotient.eq_zero_iff_dvd, piPrimeInt_dvd_iff]
  have h_sqrt :
      (chiK P.d p : valRingCp p ⧸ Ideal.span {piPrimeInt P.d}) ^ e * (-1 : ℤ) *
        modPiPrime (toValRing (P.sqrtNegDInE s)) = modPiPrime (toValRing (P.sqrtNegDInE s)) := by
    obtain h_eq | ⟨h_inert, h_odd⟩ := mem_partnerExponents.1 he
    · -- For `p = d` the image of `√-d` is `π_p`; for inert `p` the symbol is `-1` and `e` is odd.
      have h_zero : modPiPrime (toValRing (P.sqrtNegDInE s)) = 0 := by
        rw [h_mod_eq_zero, h_coe, coe_sqrtNegDInE, phi_algebraMap, QuadField.sqrtNegD_coe, piPrime,
          ite_eq_left h_eq]
      rw [h_zero, mul_zero]
    · simp [h_inert, h_odd.neg_one_pow]
  have h_frob : modPiPrime (toValRing (galOfPlaceInt (P.placeOfInt s (-p ^ e)) (star α))) =
      modPiPrime (toValRing α) ^ p ^ e := by
    have hp_not_dvd : ¬p ∣ P.q₁ s := fun h_dvd ↦
      chiK_ne_one_of_mem_partnerExponents he (P.chiK_eq_one_of_dvd Fact.out h_dvd)
    simpa using (forall_map_galOfPlaceInt_eq_pow_iff hp_not_dvd (modPiPrime.comp toValRing) e
      (.inr ⟨rfl, rfl⟩ : IsIdOrConjWithSign (starRingAut (R := 𝓞 (P.E s))) (-1))).2
      ⟨by rw [neg_one_mul], h_sqrt⟩ (star α)
  have h_partner : (toValRing (galOfPlaceInt (P.placeOfInt s (-p ^ e)) (star α)) : ℂ_[p]) =
      ιₚ (conj (Φ (P.partner s p e τ) α)) := by
    rw [h_coe, coe_galOfPlaceInt, ← phi_mul, coe_star_ringOfIntegers, map_star_complex, partner,
      mul_comm τ, starRingEnd_apply]
  rw [← h_partner]
  exact (h_mod_eq_zero (toValRing α ^ p ^ e - _)).1 (by rw [map_sub, map_pow, h_frob, sub_self])

/-- Let `E = P.E s` be `K = ℚ(√-d)` (`d = P.d`) with a root of unity of order `q₁ = P.q₁ s`
adjoined, `s` being the level in the tower of these fields. Let `e` be in
`I_p° = partnerExponents P.d p`. Let `τ : P.Φ s` be an infinite place of `E`, and
`τ' = -p ^ e τ = P.partner s p e τ` its partner: the product of `τ` with the class of `-p ^ e` in
the group `Gal(E/K) = (ℤ/q₁)ˣ` of places. Then `conj (τ(y)) ^ p ^ e ≡ τ'(y)` modulo `π_p` for `y` in
`E` integral at all primes above `p`. -/
lemma norm_conj_pow_sub_partner_le {P : Parameters} {s p : ℕ} [Fact p.Prime] [PadicPlace p] {e : ℕ}
    (he : e ∈ partnerExponents P.d p) (τ : P.Φ s) {y : P.E s} (hy : IsIntegralAbove p y) :
    ‖ιₚ (conj (Φ τ y)) ^ p ^ e - ιₚ (Φ (P.partner s p e τ) y)‖ ≤ ‖ιₚ (piPrime P.d p)‖ := by
  -- Write `y = α / N` with `N` prime to `p`, use the congruence for `conj α`, and cancel the unit
  -- `N ^ p ^ e ≡ N`.
  obtain ⟨N, α, hN, hα⟩ : ∃ (N : ℕ) (α : 𝓞 (P.E s)), p.Coprime N ∧ N * y = α := hy.exists_mul_eq
  let a : valRingCp p := ⟨ιₚ (conj (Φ τ y)), hy.norm_conj_le_one _⟩
  let b : valRingCp p := ⟨ιₚ (Φ (P.partner s p e τ) y), hy.norm_le_one (ιₚ.comp _)⟩
  have h_int : piPrimeInt P.d ∣ (N * a) ^ p ^ e - N * b := by
    simpa [piPrimeInt_dvd_iff, a, b, ← hα, coe_star_ringOfIntegers, map_star_complex] using
      norm_pow_sub_conj_partner_le he τ (star α)
  have h_fermat : piPrimeInt P.d ∣ (N : valRingCp p) ^ p ^ e - N := by
    have h_mod : (p : ℤ) ∣ (N : ℤ) ^ p ^ e - N :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (by simp [ZMod.pow_card_pow])
    exact (piPrimeInt_dvd_natCast P.d).trans
      (mod_cast map_dvd (Int.castRingHom (valRingCp p)) h_mod)
  have h_unit : IsUnit ((N : valRingCp p) ^ p ^ e) :=
    (isUnit_integer_iff_norm_eq_one.2 (hN.norm_natCast_eq_one ℂ_[p])).pow _
  have h_mul : piPrimeInt P.d ∣ (N : valRingCp p) ^ p ^ e * (a ^ p ^ e - b) := by
    have h_split : (N : valRingCp p) ^ p ^ e * (a ^ p ^ e - b) =
        (N * a) ^ p ^ e - N * b - (N ^ p ^ e - N) * b := by ring
    rw [h_split]
    exact h_int.sub (h_fermat.mul_right b)
  exact (piPrimeInt_dvd_iff (x := a ^ p ^ e - b)).1 (h_unit.dvd_mul_left.1 h_mul)

/-- Let `E = P.E s` be `K = ℚ(√-d)` with a root of unity of order `q₁ = P.q₁ s` adjoined, `e` in
`I_p° = partnerExponents P.d p` and `y` a vector over `E` integral above `p`. Then the `p ^ e`-th
power of the linear form `y† z = ∑ conj (τ(y_c)) z_(τ,c)` is `∑ τ'(y_c) z_(τ,c) ^ p ^ e` modulo
`π_p`; the sum runs over infinite places `τ` in `P.Φ s` and coordinates `c`.
`τ' = -p ^ e τ = P.partner s p e τ` is the product of `τ` with the class of `-p ^ e` in the group
`Gal(E/K) = (ℤ/q₁)ˣ` of places. `μ`, `ν` are the coefficients of the form and of the sum, read as
integers of `ℂ_p` through the embedding `ιₚ : ℂ → ℂ_p`. -/
lemma dvd_pow_sub_sum_partner {P : Parameters} {s p : ℕ} [Fact p.Prime] [PadicPlace p] {e : ℕ}
    {n : Type} [Fintype n] (he : e ∈ partnerExponents P.d p)
    {y : n → P.E s} (hy : ∀ i : n, IsIntegralAbove p (y i))
    {μ ν : P.Φ s × n → valRingCp p} (hμ : ∀ x : P.Φ s × n, (μ x : ℂ_[p]) = ιₚ (dagger y x))
    (hν : ∀ x : P.Φ s × n, (ν x : ℂ_[p]) = ιₚ (Φ (P.partner s p e x.1) (y x.2))) :
    C (piPrimeInt P.d) ∣ linearSeries μ ^ p ^ e - ∑ x : P.Φ s × n, ν x • X x ^ p ^ e := by
  have h_add : C (piPrimeInt P.d) ∣ linearSeries μ ^ p ^ e - ∑ x, (μ x • X x) ^ p ^ e :=
    dvd_sum_pow_sub_sum (mod_cast map_dvd C (piPrimeInt_dvd_natCast P.d)) _ _ e
  have h_coeff (x : P.Φ s × n) : piPrimeInt P.d ∣ μ x ^ p ^ e - ν x := by
    rw [piPrimeInt_dvd_iff, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, hμ, hν]
    exact norm_conj_pow_sub_partner_le he x.1 (hy x.2)
  rw [← sub_add_sub_cancel _ (∑ x, (μ x • X x) ^ p ^ e), ← sum_sub_distrib]
  refine h_add.add (dvd_sum fun x _ ↦ ?_)
  rw [smul_pow, ← sub_smul, smul_eq_C_mul]
  exact (map_dvd C (h_coeff x)).mul_right _

/-- For vectors `u_j` over `E = P.E s` integral above `p`, the linear forms `u_j† z`, whose
coefficient at `z_(τ,c)` is `conj (τ(u_{j,c}))` read in `ℂ_p` through the embedding `ιₚ` of `ℂ`,
have integral coefficients. -/
lemma norm_daggerForms_le_one (P : Parameters) (s : ℕ) {p : ℕ} [Fact p.Prime] [PadicPlace p]
    {n J : Type} {u : J → n → P.E s}
    (hu : ∀ (j : J) (i : n), IsIntegralAbove p (u j i)) (j : J) (x : P.Φ s × n) :
    ‖(daggerForms u j x : ℂ_[p])‖ ≤ 1 :=
  (hu j x.2).norm_conj_le_one _

/-- Let `E = P.E s` be `K = ℚ(√-d)` (`d = P.d`) with a root of unity of order `q₁ = P.q₁ s`
adjoined, `s` being the tower level, and let `e` be in `I_p° = partnerExponents P.d p`. Let the
vectors `u_j` of `Eⁿ`, integral above `p` and each taken `m_j` times, be a resolution of the
identity: `z = ∑ m_j (u_j† z) u_j`. Then `∑ m_j (u_j† z) ^ p ^ e * (u_j† z)` is the coupling
`Γ_e = ∑ z_(τ,c) ^ p ^ e * z_(τ',c)` modulo `π_p`. -/
lemma piPrimeInt_dvd_sum_linearSeries_sub_coupling (P : Parameters) (s : ℕ) {p : ℕ} [Fact p.Prime]
    [PadicPlace p]
    {n J : Type} [Fintype n] [Fintype J] {u : J → n → P.E s} {m : J → ℕ} [DecidableEq n]
    {e : ℕ} (he : e ∈ partnerExponents P.d p)
    (h_res : IsResolution u m) (hu : ∀ (j : J) (i : n), IsIntegralAbove p (u j i))
    {μ : J → P.Φ s × n → valRingCp p}
    (hμ : ∀ (j : J) (x : P.Φ s × n), (μ j x : ℂ_[p]) = daggerForms u j x) :
    C (piPrimeInt P.d) ∣
      ∑ j : J, m j * (linearSeries (μ j) ^ p ^ e * linearSeries (μ j)) -
        coupling (P.partner s p) e := by
  -- `ν j (τ, c)` is the coordinate `c` of `u j` at the partner of `τ`.
  let ν (j : J) (x : P.Φ s × n) : valRingCp p :=
    ⟨ιₚ (Φ (P.partner s p e x.1) (u j x.2)), (hu j x.2).norm_le_one (ιₚ.comp _)⟩
  have h_pow (j : J) :
      C (piPrimeInt P.d) ∣ linearSeries (μ j) ^ p ^ e - ∑ x, ν j x • X x ^ p ^ e :=
    dvd_pow_sub_sum_partner he (hu j) (hμ j) fun _ ↦ rfl
  have h_identity (x : P.Φ s × n) :
      ∑ j, (m j * ν j x) • linearSeries (μ j) = X (P.partner s p e x.1, x.2) :=
    h_res.sum_smul_linearSeries (P.partner s p e x.1, x.2) (fun _ ↦ rfl) hμ
  have h_coupling : coupling (P.partner s p) e =
      ∑ j, (m j : MvPowerSeries (P.Φ s × n) (valRingCp p)) *
        ((∑ x, ν j x • X x ^ p ^ e) * linearSeries (μ j)) := by
    simp only [coupling, ← h_identity, mul_sum, sum_mul, smul_eq_C_mul, map_mul, map_natCast]
    rw [sum_comm]
    exact sum_congr rfl fun j _ ↦ sum_congr rfl fun x _ ↦ by ring
  rw [h_coupling, ← sum_sub_distrib]
  refine dvd_sum fun j _ ↦ ?_
  rw [← mul_sub, ← sub_mul]
  exact ((h_pow j).mul_right _).mul_left _

end Parameters

end New

end Partner

/-!
## The normal form of products of theta functions

Each theta factor at `ϖ z` is an integral series times `exp (c_ϖ Ξ(u† z))`. Modulo `π_p` the
`p`-th power is additive, so the exponents add up to a combination of powers of the couplings.
-/

section NormalForm

open MvPowerSeries WithPiTopology

namespace New
variable {p : ℕ} [Fact p.Prime]

/-- Let `π ∣ p`, let `Ξ` be a series in one variable congruent to
`∑ λ_{e j} (z ^ p ^ e * z) ^ p ^ j` modulo `π`, the sum over `e ∈ S` and `j` with
`λ_{e j} = l e j`, and let `partner e` be a self-map of the set `Φ` of places, with
`Γ_e = coupling partner e = ∑ z_(τ,c) ^ p ^ e * z_(partner e τ,c)` summed over `(τ, c)` in `Φ × n`.
If series `L_i` without constant term are such that `∑ m_i L_i ^ p ^ e * L_i` is `Γ_e` modulo `π`
for `e ∈ S`, then the `Ξ(L_i)`, each taken `m_i` times, add up to
`couplingSum S partner l = ∑ λ_{e j} Γ_e ^ p ^ j` modulo `π`. -/
lemma dvd_sum_subst_sub_couplingSum {Φ n J : Type} [Fintype Φ] [Fintype n] [Fintype J]
    {S : Set ℕ} {partner : ℕ → Φ → Φ} {l : ℕ → ℕ → valRingCp p} {π : valRingCp p} (hπ : π ∣ p)
    {Ξ : PowerSeries (valRingCp p)}
    (hΞ : C π ∣ Ξ -
      ∑' x : S × ℕ, l x.1 x.2 • (PowerSeries.X ^ p ^ (x.1 : ℕ) * PowerSeries.X) ^ p ^ x.2)
    {L : J → MvPowerSeries (Φ × n) (valRingCp p)} (hL : ∀ i : J, constantCoeff (L i) = 0)
    {m : J → ℕ} (hΓ : ∀ e ∈ S, C π ∣ ∑ i : J, m i * (L i ^ p ^ e * L i) - coupling partner e) :
    C π ∣ ∑ i : J, m i • Ξ.subst (L i) - couplingSum S partner l := by
  classical
  have h_subst (i : J) : PowerSeries.HasSubst (L i) := .of_constantCoeff_zero (hL i)
  set T : PowerSeries (valRingCp p) :=
    ∑' x : S × ℕ, l x.1 x.2 • (PowerSeries.X ^ p ^ (x.1 : ℕ) * PowerSeries.X) ^ p ^ x.2
  have h_replace (i : J) : C π ∣ Ξ.subst (L i) - T.subst (L i) := by
    obtain ⟨G, hG⟩ : C π ∣ Ξ - T := hΞ
    exact ⟨PowerSeries.subst (L i) G, by rw [← PowerSeries.subst_sub (h_subst i), hG,
      ← smul_eq_C_mul, ← smul_eq_C_mul, PowerSeries.subst_smul (h_subst i)]⟩
  have h_sum (i : J) :
      HasSum (fun x : S × ℕ ↦ l x.1 x.2 • (L i ^ p ^ (x.1 : ℕ) * L i) ^ p ^ x.2)
        (T.subst (L i)) := by
    -- Substitution is continuous, so it maps the sum `T` term by term.
    have h_cont : Continuous (PowerSeries.substAlgHom (R := valRingCp p) (h_subst i)) := by
      rw [PowerSeries.coe_substAlgHom]
      exact continuous_subst_of_constantCoeff_eq_zero fun _ ↦ hL i
    rw [← PowerSeries.coe_substAlgHom (h_subst i)]
    simpa only [Function.comp_def, map_smul, map_pow, map_mul, PowerSeries.substAlgHom_X] using
      (summable_smul_X_pow_mul_X_pow S l).hasSum.map _ h_cont
  -- Term by term: `p ^ j`-th powers are additive modulo `π`.
  have h_tsum_congr : C π ∣ ∑ i, m i * T.subst (L i) - couplingSum S partner l := by
    refine C_dvd_of_hasSum ((hasSum_sum fun i _ ↦ (h_sum i).mul_left _).sub hasSum_couplingSum) ?_
    rintro ⟨⟨e, he⟩, j⟩
    -- A sum with multiplicities is a sum over the pairs `(i, k)` with `k < m i`.
    have h_add : C π ∣
        (∑ i, m i * (L i ^ p ^ e * L i)) ^ p ^ j - ∑ i, m i * (L i ^ p ^ e * L i) ^ p ^ j := by
      simpa [Fintype.sum_sigma] using dvd_sum_pow_sub_sum (mod_cast map_dvd C hπ) .univ
        (fun x : Σ i, Fin (m i) ↦ L x.1 ^ p ^ e * L x.1) j
    have h_diff : C π ∣ ∑ i, m i * (L i ^ p ^ e * L i) ^ p ^ j - coupling partner e ^ p ^ j := by
      simpa only [sub_sub_sub_cancel_left] using
        ((hΓ e he).trans (sub_dvd_pow_sub_pow _ _ (p ^ j))).sub h_add
    -- The common factor `λ_{e j}` comes out of the sum.
    simp only [smul_eq_C_mul, mul_left_comm _ (C (l e j)), ← Finset.mul_sum, ← mul_sub]
    exact h_diff.mul_left _
  have h_sum_replace : C π ∣
      ∑ i, (m i : MvPowerSeries (Φ × n) (valRingCp p)) * (Ξ.subst (L i) - T.subst (L i)) :=
    Finset.dvd_sum fun i _ ↦ (h_replace i).mul_left _
  simpa only [nsmul_eq_mul, mul_sub, Finset.sum_sub_distrib, sub_add_sub_cancel] using
    h_sum_replace.add h_tsum_congr

/-- For a series `g` without constant term, `exp (n g) = exp(g) ^ n`. -/
lemma expSubst_nsmul {σ : Type} {g : MvPowerSeries σ ℂ_[p]} (hg : constantCoeff g = 0) (n : ℕ) :
    expSubst (n • g) = expSubst g ^ n := by
  simpa using expSubst_sum (t := Finset.range n) (a := fun _ ↦ g) fun _ ↦ hg

/-- For a linear form `L = ∑ ν_x z_x` with integral coefficients, `g(L)` at `ϖ z` is the series
`g(ϖ t)` at `t = L`. -/
lemma rescale_subst_linearSeries_coe {X : Type} [Fintype X] (ϖ : ℂ_[p]) (g : PowerSeries ℂ_[p])
    (ν : X → valRingCp p) :
    (g.subst (linearSeries fun x : X ↦ (ν x : ℂ_[p]))).rescale (fun _ : X ↦ ϖ) =
      (g.rescale ϖ).subst (seriesToCp (linearSeries ν)) := by
  rw [rescale_subst_linearSeries]
  simp [linearSeries]

/-- The inclusion `seriesToCp` of integral series commutes with substituting a series `L` without
constant term into a series `G` in one variable. -/
lemma seriesToCp_subst {X : Type} {L : MvPowerSeries X (valRingCp p)} (hL : constantCoeff L = 0)
    (G : PowerSeries (valRingCp p)) :
    seriesToCp (G.subst L) = PowerSeries.subst (seriesToCp L) (seriesToCp G) :=
  PowerSeries.map_subst (.of_constantCoeff_zero hL) G

namespace CMLattice
variable {d : ℕ} (C : CMLattice d) [PadicPlace p] {I X : Type} [Fintype I]
  [Fintype X] {μ : I → X → valRingCp p} {ϖ : ℂ_[p]}

/-- Let `d ≡ 7 mod 8` be prime, `C` a lattice with complex multiplication by the integers of
`ℚ(√-d)` and a point `t` of order two with `a₁² = 12 ℘(t)`, and `y` the Taylor series at `0`, read
in `ℂ_p` by `ιₚ`, of `C.translatedY z = (℘'(z + t) - a₁ (℘(z + t) - ℘(t))) / 2`. Let `μ_i` be
integral linear forms and `v(ϖ) ≥ ρ_p = varpiValuation d p`. Then a series `H` in
`C.multiSeriesRing`, the ring of integral series in the `y(μ_i z)`, is integral at `ϖ z`: `H(ϖ z)`
is in the range of `seriesToCp`, the inclusion of series over the integers of `ℂ_p`. -/
lemma rescale_mem_range_of_mem_multiSeriesRing [PrimeSevenModEight d]
    (hϖ : ‖ϖ‖ ≤ p ^ (-varpiValuation d p))
    {H : MvPowerSeries X ℂ_[p]} (hH : H ∈ C.multiSeriesRing fun (i : I) (x : X) ↦ (μ i x : ℂ_[p])) :
    H.rescale (fun _ : X ↦ ϖ) ∈ seriesToCp.range := by
  -- `y(ϖ w) = Y(w)` with `Y` integral, so `G(y(μ z))` at `ϖ z` is `G(Y(μ z))`.
  obtain ⟨G, rfl⟩ := hH
  obtain ⟨Y, hY⟩ : PowerSeries.rescale ϖ (taylorVia ιₚ C.translatedY) ∈ seriesToCp.range :=
    C.rescale_mem_range_seriesToCp hϖ C.isSeriesGenerator_translatedY.generator_mem
  have hY_zero : constantCoeff Y = 0 := by simpa using congrArg constantCoeff hY
  let Z (i : I) : MvPowerSeries X (valRingCp p) := PowerSeries.subst (linearSeries (μ i)) Y
  have hZ (i : I) : seriesToCp (Z i) = rescale (fun _ ↦ ϖ)
      ((taylorVia ιₚ C.translatedY).subst (linearSeries fun x ↦ (μ i x : ℂ_[p]))) := by
    rw [rescale_subst_linearSeries_coe, ← hY, seriesToCp_subst (constantCoeff_linearSeries _)]
  have h_subst : HasSubst Z := hasSubst_of_constantCoeff_zero fun i ↦
    PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_linearSeries _) Y hY_zero
  refine ⟨G.subst Z, ?_⟩
  -- Scaling is a substitution, and substitutions compose.
  simp only [map_subst h_subst, hZ, rescale_eq_subst]
  rw [← subst_comp_subst_apply (C.hasSubst_translatedY_subst _) (HasSubst.smul_X _)]
  simp [Function.comp_def]

/-- Let `C` be a lattice with complex multiplication by the integers of `ℚ(√-d)` and a point of
order two, and `θ = taylorVia ιₚ C.θ` the Taylor series of its theta function, read in `ℂ_p` by the
embedding `ιₚ` of `ℂ`. Let `θ(ϖ z) = W exp (κ Ξ)` with integral series `W`, `Ξ` and `Ξ(0) = 0`. Then
`C.thetaProd`, the product `∏ θ(μ_i z) ^ m_i` for integral linear forms `μ_i`, is at `ϖ z` the
integral series `∏ W(μ_i z) ^ m_i` times `exp (κ ∑ m_i Ξ(μ_i z))`. -/
lemma rescale_thetaProd_eq_mul_expSubst {κ : ℂ_[p]} {W Ξ : PowerSeries (valRingCp p)}
    (hΞ : PowerSeries.constantCoeff Ξ = 0)
    (h_theta : (taylorVia ιₚ C.θ).rescale ϖ = seriesToCp W * expSubst (κ • seriesToCp Ξ))
    (m : I → ℕ) :
    (C.thetaProd (fun (i : I) (x : X) ↦ (μ i x : ℂ_[p])) m).rescale (fun _ : X ↦ ϖ) =
      seriesToCp (∏ i : I, W.subst (linearSeries (μ i)) ^ m i) *
        expSubst (κ • seriesToCp (∑ i : I, m i • Ξ.subst (linearSeries (μ i)))) := by
  have hL (i : I) : constantCoeff (linearSeries (μ i)) = 0 := constantCoeff_linearSeries _
  have h_zero (i : I) : constantCoeff (κ • seriesToCp (Ξ.subst (linearSeries (μ i)))) = 0 := by
    simp [PowerSeries.constantCoeff_subst_eq_zero (hL i) Ξ hΞ]
  have h_factor (i : I) :
      ((taylorVia ιₚ C.θ).subst (linearSeries fun x ↦ (μ i x : ℂ_[p]))).rescale (fun _ ↦ ϖ) =
        seriesToCp (W.subst (linearSeries (μ i))) *
          expSubst (κ • seriesToCp (Ξ.subst (linearSeries (μ i)))) := by
    have h_subst : PowerSeries.HasSubst (seriesToCp (linearSeries (μ i))) :=
      .of_constantCoeff_zero (by simp [hL])
    rw [rescale_subst_linearSeries_coe, h_theta, PowerSeries.subst_mul h_subst,
      seriesToCp_subst (hL i), seriesToCp_subst (hL i), ← PowerSeries.subst_smul h_subst]
    -- It remains that substitution into an exponential is substitution into the exponent.
    exact congrArg _ (subst_expSubst (by simpa using .inr hΞ) h_subst.const)
  rw [thetaProd, map_prod, map_prod, map_sum, Finset.smul_sum, expSubst_sum fun i ↦ ?_,
    ← Finset.prod_mul_distrib]
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [map_pow, h_factor, mul_pow, map_pow, map_nsmul, smul_comm κ, expSubst_nsmul (h_zero i)]
  · rw [map_nsmul, smul_comm κ, map_nsmul, h_zero i, smul_zero]

end CMLattice

namespace Parameters

/-- Let `E = P.E s` be `K = ℚ(√-d)` with a root of unity of order `q₁ = P.q₁ s` adjoined, `p` a
prime not split in `K` (`chiK P.d p ≠ 1`), `I_p° = partnerExponents P.d p`, and for an infinite
place `τ` of `E` let its partner `τ' = -p ^ e τ` be the product of `τ` with the class of `-p ^ e` in
the group `Gal(E/K) = (ℤ/q₁)ˣ` of places. There are `ϖ` of valuation `ρ_p = varpiValuation P.d p`
and integers `λ_{e j}` of `ℂ_p`, with the `λ_{e 0}` for odd `e` units if `p` is inert, such that the
following holds. Take any resolution of the identity by vectors `u_j` of `Eⁿ`, taken `m_j` times and
integral above `p`. Then the product `∏ θ(u_j† z) ^ m_j` times an integral series in the `y(u_j† z)`
has the normal form. -/
lemma exists_hasNormalForm (P : Parameters) (s : ℕ) [PadicPlace p] (hp : chiK P.d p ≠ 1) :
    ∃ (ϖ : ℂ_[p]) (l : ℕ → ℕ → valRingCp p),
    ‖ϖ‖ = p ^ (-varpiValuation P.d p) ∧
    (chiK P.d p = -1 → ∀ e : ℕ, Odd e → IsUnit (l e 0)) ∧
    ∀ {n J : Type} [Fintype n] [DecidableEq n] [Fintype J] (u : J → n → P.E s) (m : J → ℕ),
      IsResolution u m → (∀ (j : J) (i : n), IsIntegralAbove p (u j i)) →
        ∀ H ∈ P.cmCurve.multiSeriesRing (daggerForms u),
          HasNormalForm (partnerExponents P.d p) (P.partner s p) ϖ l
            (P.cmCurve.thetaProd (daggerForms u) m * H) := by
  -- On one curve: `θ(ϖ z) = W exp (c_ϖ Ξ)` with `Ξ ≡ ∑ λ_{e j} (z ^ p ^ e * z) ^ p ^ j`.
  obtain ⟨ϖ, Ξ, W, l, hϖ, hΞ_zero, h_theta, hΞ, h_unit⟩ := P.cmCurve.exists_exponent_tsum hp
  refine ⟨ϖ, l, hϖ, h_unit, ?_⟩
  intro n J _ _ _ u m h_res hu H hH
  -- The linear forms `u† z` are integral, so at `ϖ z` the series is an integral series times
  -- the exponential of `c_ϖ ∑ m_j Ξ(u_j† z)`.
  let μ (j : J) (x : P.Φ s × n) : valRingCp p :=
    ⟨daggerForms u j x, P.norm_daggerForms_le_one s hu j x⟩
  have hL (j : J) : constantCoeff (linearSeries (μ j)) = 0 := constantCoeff_linearSeries _
  obtain ⟨V, hV⟩ : H.rescale (fun _ : P.Φ s × n ↦ ϖ) ∈ seriesToCp.range :=
    P.cmCurve.rescale_mem_range_of_mem_multiSeriesRing (μ := μ) hϖ.le hH
  have h_prod : (P.cmCurve.thetaProd (daggerForms u) m * H).rescale (fun _ ↦ ϖ) =
      seriesToCp ((∏ j, W.subst (linearSeries (μ j)) ^ m j) * V) *
        expSubst ((ϖ ^ (p + 1) / p) • seriesToCp (∑ j, m j • Ξ.subst (linearSeries (μ j)))) := by
    rw [map_mul, map_mul, hV, mul_right_comm,
      ← P.cmCurve.rescale_thetaProd_eq_mul_expSubst hΞ_zero h_theta m]
  have h_congr : C (piPrimeInt P.d) ∣ ∑ j, m j • Ξ.subst (linearSeries (μ j)) -
      couplingSum (partnerExponents P.d p) (P.partner s p) l :=
    dvd_sum_subst_sub_couplingSum (piPrimeInt_dvd_natCast P.d) hΞ hL fun e he ↦
      P.piPrimeInt_dvd_sum_linearSeries_sub_coupling s he h_res hu fun _ _ ↦ rfl
  refine .of_dvd_sub (P.norm_pow_succ_div_mul_piPrimeInt hp hϖ).le ?_ h_congr h_prod
  simp [PowerSeries.constantCoeff_subst_eq_zero (hL _) Ξ hΞ_zero]

end Parameters

end New

end NormalForm
