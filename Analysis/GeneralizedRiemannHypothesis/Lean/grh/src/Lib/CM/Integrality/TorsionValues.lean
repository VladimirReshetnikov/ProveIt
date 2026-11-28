import Lib.CM.GoodReduction
import Lib.CM.Integrality.Doubling

/-!
# Integrality of values of sections at torsion points

The file defines the value `torsionValue` at a point of a function with a degree `n` (the function
value times an exponential factor that depends on `n`), which is used for sections at torsion
points, and the property `HasIntegralValues`. For a prime `d ≡ 7 (mod 8)` the file shows that `a₁`
is integral, that `max (|σ[u]|_p, |θ[u]|_p) = 1` at torsion points, and that monomials in `θ`, `σ²`
and the section `translatedYThetaCube` have integral torsion values. Here `translatedYThetaCube` is
`y θ³`, where `y` is the coordinate `translatedY` in the cubic `y² + a₁ x y = x³ + x`.

Notions from other files:
* `CMLattice d`: a lattice `Λ` with a point `t` of order two in `ℂ / Λ` and a coefficient `a₁` of
  its cubic. For `d ≠ 0` the lattice has complex multiplication by the integers of `ℚ(√-d)`.
* `σ` and `θ`: the sigma function of `Λ`, normalised so that twisted translation by a period
  multiplies it by a sign, and the theta function that vanishes exactly on `-t + Λ`.
* `twistedTranslate n v G`: the translate of a function `G` by `v`, multiplied by the exponential
  factor of `n` times the Hermitian form `H(l, z) = (π / area Λ) l̄ z`.
* `ιₚ`: the fixed embedding of `ℂ` into `ℂ_p` (`PadicPlace p`); integral means of norm at most `1`,
  that is, lying in `valRingCp p`, the set of elements of `ℂ_p` of norm at most `1`.

## Main definitions and results

* `New.CMLattice.torsionValue`, `New.CMLattice.HasIntegralValues`: the torsion value `G[u]` and the
  property that all of these are integral at torsion points.
* `New.CMLattice.norm_a₁_le_one`: `a₁` is integral, because `a₁ ^ 4 - 64` is a unit.
* `New.CMLattice.torsionValue_mul`, `New.CMLattice.torsionValue_comp_isogeny`,
  `New.CMLattice.torsionValue_twistedTranslate`: the rules for products, pull-backs and translates.
* `New.CMLattice.max_norm_torsionValue`: `max (|σ[u]|_p, |θ[u]|_p) = 1` at torsion points.
* `New.CMLattice.hasIntegralValues_monomialSection`: monomials have integral torsion values.

## Relation to the literature

Known result: the Weber invariants of discriminant `-d` with `d ≡ 7 mod 8` are integral. Source:
Birch, *Weber's class invariants*.

Known result: the integrality of Siegel functions at torsion points. Source: Kubert and Lang,
*Modular Units*.
-/

/-! ## Integrality of the coefficient `a₁` -/

namespace New.CMLattice

variable {d : ℕ} [PrimeSevenModEight d] (C : CMLattice d) {p : ℕ} [Fact p.Prime]

lemma mem_valRingCp_iff_norm_le_one {x : ℂ_[p]} : x ∈ valRingCp p ↔ ‖x‖ ≤ 1 := Iff.rfl

/-- If `g ^ 2 + u g = v` in `ℂ_p` and `‖u‖, ‖v‖ ≤ 1`, then `‖g‖ ≤ 1`: a root of a monic quadratic
with integral coefficients is integral. -/
lemma norm_le_one_of_sq_add_mul_eq {g u v : ℂ_[p]} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hg : g ^ 2 + u * g = v) : ‖g‖ ≤ 1 := by
  by_contra! h_lt
  have h_eq : g ^ 2 = u * -g + v := by linear_combination hg
  have h_sq : ‖g‖ ^ 2 ≤ ‖g‖ := calc
    ‖g‖ ^ 2 = ‖u * -g + v‖ := by rw [← norm_pow, h_eq]
    _ ≤ max (‖u‖ * ‖g‖) ‖v‖ := by grw [IsUltrametricDist.norm_add_le_max, norm_mul, norm_neg]
    _ ≤ ‖g‖ := by grw [hu, hv, one_mul, max_eq_left h_lt.le]
  exact (lt_self_pow₀ h_lt one_lt_two).not_ge h_sq

/-- For a prime `d ≡ 7 (mod 8)` the coefficient `a₁` of the cubic of a CM lattice is integral in
`ℂ_p`. -/
lemma norm_a₁_le_one [PadicPlace p] : ‖ιₚ C.a₁‖ ≤ 1 := by
  -- `a₁ ^ 4 = (a₁ ^ 4 - 64) + 64` is a sum of two integral elements.
  have h_pow : ιₚ C.a₁ ^ 4 - 64 + 64 ∈ valRingCp p :=
    add_mem (mem_valRingCp_iff_norm_le_one.2 (C.norm_disc_eq_one ιₚ).le) (ofNat_mem _ 64)
  rwa [sub_add_cancel, mem_valRingCp_iff_norm_le_one, norm_pow,
    pow_le_one_iff_of_nonneg (norm_nonneg _) four_ne_zero] at h_pow

end New.CMLattice

/-!
## Torsion values and their norms

The proof of `max_norm_torsionValue` rests on three facts: doubling raises the norm of the nonzero
pair `(θ[u]², σ[u]²)` to the fourth power, this norm depends only on `u` modulo `Λ`, and modulo
`Λ` the orbit of a torsion point under doubling is finite.
-/

section TorsionValues

open Complex ComplexConjugate
open scoped Real

namespace New.CMLattice
variable {d : ℕ} (C : CMLattice d)

/-- `u` lies in `ℚ Λ`, that is, it represents a torsion point of `ℂ / Λ`. -/
def IsTorsion (u : ℂ) : Prop := ∃ n : ℕ, n ≠ 0 ∧ n * u ∈ C.Λ

/-- The torsion value `G[u]` of a function `G` with the degree `n`: the value at `0` of the twisted
translate of `G` by `u` for `n` times the Hermitian form of the lattice. -/
noncomputable def torsionValue (n : ℕ) (G : ℂ → ℂ) (u : ℂ) : ℂ := C.twistedTranslate n u G 0

lemma IsTorsion.of_mem {C : CMLattice d} {u : ℂ} (hu : u ∈ C.Λ) : C.IsTorsion u :=
  ⟨1, one_ne_zero, by simpa⟩

lemma IsTorsion.natCast_mul {C : CMLattice d} {u : ℂ} (hu : C.IsTorsion u) (k : ℕ) :
    C.IsTorsion (k * u) := by
  obtain ⟨n, hn, hnu⟩ := hu
  exact ⟨n, hn, by simpa only [nsmul_eq_mul, mul_left_comm] using nsmul_mem hnu k⟩

lemma IsTorsion.neg {C : CMLattice d} {u : ℂ} (hu : C.IsTorsion u) : C.IsTorsion (-u) := by
  obtain ⟨n, hn, hnu⟩ := hu
  exact ⟨n, hn, by simpa only [mul_neg] using neg_mem hnu⟩

/-- The sum of two torsion points is a torsion point. -/
lemma IsTorsion.add {C : CMLattice d} {u v : ℂ} (hu : C.IsTorsion u) (hv : C.IsTorsion v) :
    C.IsTorsion (u + v) := by
  obtain ⟨m, hm, hmu⟩ := hu
  obtain ⟨n, hn, hnv⟩ := hv
  have h_eq : (m * n : ℕ) * (u + v) = n • (m * u) + m • (n * v) := by
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring
  refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
  rw [h_eq]
  exact add_mem (nsmul_mem hmu n) (nsmul_mem hnv m)

/-- An isogeny `z ↦ a z` between the lattices takes torsion points to torsion points. -/
lemma IsTorsion.mul_of_isogeny {C C' : CMLattice d} {a u : ℂ} {N : ℕ}
    (h : C.IsIsogeny C'.periodPair a N) (hu : C.IsTorsion u) : C'.IsTorsion (a * u) := by
  obtain ⟨h_lattice, -⟩ := h
  obtain ⟨n, hn, hnu⟩ := hu
  exact ⟨n, hn, by simpa only [mul_left_comm] using h_lattice _ hnu⟩

/-- The torsion value of `G` at `u` is `G(u) exp (-n π |u|² / (2 area Λ))`. -/
lemma torsionValue_eq (n : ℕ) (G : ℂ → ℂ) (u : ℂ) :
    C.torsionValue n G u = G u * exp (-(π * ‖u‖ ^ 2 / (2 * C.area))) ^ n := by
  have h_exponent : -((n • C.hermitianForm) u u / 2) = n * -(π * ‖u‖ ^ 2 / (2 * C.area)) := by
    change -(n • C.hermitianForm u u / 2) = _
    rw [nsmul_eq_mul, hermitianForm_apply, mul_conj']
    ring
  simp only [torsionValue, thetaShift_apply, zero_add, neg_zero, add_zero, map_zero, ← exp_nat_mul,
    ← h_exponent, mul_comm (G u)]

/-- Products: degrees add and torsion values multiply. -/
lemma torsionValue_mul (m n : ℕ) (F G : ℂ → ℂ) (u : ℂ) :
    C.torsionValue (m + n) (F * G) u = C.torsionValue m F u * C.torsionValue n G u := by
  simp only [torsionValue_eq, Pi.mul_apply]
  ring

lemma torsionValue_pow (k n : ℕ) (G : ℂ → ℂ) (u : ℂ) :
    C.torsionValue (k * n) (G ^ k) u = C.torsionValue n G u ^ k := by
  simp only [torsionValue_eq, Pi.pow_apply]
  ring

/-- If `G(u) = θ(u) ^ n c`, then `G[u] = θ[u] ^ n c` for the torsion values in the degrees `n` of
`G` and `1` of `θ`; so `G[u] / θ[u] ^ n = G(u) / θ(u) ^ n` off the zeros of `θ`. -/
lemma torsionValue_eq_mul_theta_pow {n : ℕ} {G : ℂ → ℂ} {u c : ℂ} (h : G u = C.θ u ^ n * c) :
    C.torsionValue n G u = C.torsionValue 1 C.θ u ^ n * c := by
  simp only [torsionValue_eq, h]
  ring

/-- Pull-backs: if `z ↦ a z` is an isogeny of degree `N` from the lattice of `C` to that of `C'`,
then with the degree `n N` the function `G(a z)` has at `u` the torsion value `G[a u]`. -/
lemma torsionValue_comp_isogeny {C' : CMLattice d} {a : ℂ} {N : ℕ}
    (h : C.IsIsogeny C'.periodPair a N) (n : ℕ) (G : ℂ → ℂ) (u : ℂ) :
    C.torsionValue (n * N) (fun z : ℂ ↦ G (a * z)) u = C'.torsionValue n G (a * u) := by
  simp only [torsionValue, C.twistedTranslate_comp_isogeny h, mul_zero]

/-- `π i` times the Riemann form (the alternating form) of `n` times the Hermitian form of the
lattice, at `(u, v)`, is `-n π i Im (u v̄) / area Λ`. -/
lemma pi_mul_I_mul_riemannForm_eq (n : ℕ) (u v : ℂ) :
    π * I * (n • C.hermitianForm).riemannForm u v = -(n * π * I * (u * conj v).im / C.area) := by
  have h_im : (conj u * v).im = -(u * conj v).im := by
    rw [← conj_im, map_mul, conj_conj]
  rw [map_nsmul, LinearMap.smul_apply, LinearMap.smul_apply, riemannForm_hermitianForm]
  simp only [h_im, nsmul_eq_mul]
  push_cast
  ring

/-- Translates: the twisted translate of `G` by `v` (for `n` times the Hermitian form) has at `u`
the torsion value `G[u + v]` times `exp (-n π i Im (u v̄) / area Λ)`. -/
lemma torsionValue_twistedTranslate (n : ℕ) (G : ℂ → ℂ) (u v : ℂ) :
    C.torsionValue n (C.twistedTranslate n v G) u =
      exp (-(n * π * I * (u * conj v).im / C.area)) * C.torsionValue n G (u + v) := by
  rw [← pi_mul_I_mul_riemannForm_eq]
  -- Translating by `v` and then by `u` is translating by `u + v`, up to the exponential factor.
  have h_shift : C.twistedTranslate n u (C.twistedTranslate n v G) =
      exp (π * I * (n • C.hermitianForm).riemannForm u v) • C.twistedTranslate n (u + v) G :=
    (C.isAppellHumbert_multiplier.nsmul n).thetaShift_thetaShift u v
  simp only [torsionValue, h_shift, Pi.smul_apply, smul_eq_mul]

variable {p : ℕ} [Fact p.Prime] [PadicPlace p]

/-- For torsion points `u`, `v` the twisted translate of `G` by `v` has at `u` a torsion value of
the same `p`-adic norm as `G[u + v]`: the two differ by a root of unity. -/
lemma norm_torsionValue_twistedTranslate (n : ℕ) (G : ℂ → ℂ) {u v : ℂ} (hu : C.IsTorsion u)
    (hv : C.IsTorsion v) :
    ‖ιₚ (C.torsionValue n (C.twistedTranslate n v G) u)‖ = ‖ιₚ (C.torsionValue n G (u + v))‖ := by
  obtain ⟨k, hk, hku⟩ := hu
  obtain ⟨l, hl, hlv⟩ := hv
  rw [← nsmul_eq_mul] at hku hlv
  set c : ℂ := exp (π * I * (n • C.hermitianForm).riemannForm u v)
  have h_root : IsOfFinOrder c :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨2 * k * l, by positivity,
      (C.isAppellHumbert_multiplier.nsmul n).exp_riemannForm_pow_eq_one hku hlv⟩
  have h_norm : ‖ιₚ c‖ = 1 := ((ιₚ : ℂ →+* ℂ_[p]).toMonoidHom.isOfFinOrder h_root).norm_eq_one
  rw [torsionValue_twistedTranslate, ← pi_mul_I_mul_riemannForm_eq, map_mul, norm_mul, h_norm,
    one_mul]

/-- The torsion values of `G` with the degree `n` are all integral in `ℂ_p`: for every torsion
point `u`, the image of `G[u]` under `ιₚ` has norm at most `1`. -/
def HasIntegralValues (n : ℕ) (G : ℂ → ℂ) : Prop :=
  ∀ u : ℂ, C.IsTorsion u → ‖ιₚ (C.torsionValue n G u)‖ ≤ 1

section
variable {C}

/-- If `F` and `G` have integral torsion values (`HasIntegralValues`) in the degrees `m` and `n`,
so has `F G` in the degree `m + n`. -/
lemma HasIntegralValues.mul {m n : ℕ} {F G : ℂ → ℂ} (hF : C.HasIntegralValues (p := p) m F)
    (hG : C.HasIntegralValues (p := p) n G) : C.HasIntegralValues (p := p) (m + n) (F * G) := by
  intro u hu
  rw [torsionValue_mul, map_mul, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hF u hu)).trans (hG u hu)

/-- If `G` has integral torsion values in the degree `n`, so has `G ^ k` in the degree `k n`. -/
lemma HasIntegralValues.pow {n : ℕ} {G : ℂ → ℂ} (hG : C.HasIntegralValues (p := p) n G) (k : ℕ) :
    C.HasIntegralValues (p := p) (k * n) (G ^ k) := by
  intro u hu
  rw [torsionValue_pow, map_pow, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (hG u hu)

/-- If `G` has integral torsion values on the target of an isogeny `z ↦ a z` of degree `N`, so has
`G(a z)` on the source, with the degree multiplied by `N`. -/
lemma HasIntegralValues.comp_isogeny {C' : CMLattice d} {a : ℂ} {N n : ℕ} {G : ℂ → ℂ}
    (h : C.IsIsogeny C'.periodPair a N) (hG : C'.HasIntegralValues (p := p) n G) :
    C.HasIntegralValues (p := p) (n * N) fun z : ℂ ↦ G (a * z) := by
  intro u hu
  rw [C.torsionValue_comp_isogeny h]
  exact hG _ (hu.mul_of_isogeny h)

/-- If `G` has integral torsion values in the degree `n`, so has its twisted translate by a torsion
point `v`. -/
lemma HasIntegralValues.translate {n : ℕ} {G : ℂ → ℂ} (hG : C.HasIntegralValues (p := p) n G)
    {v : ℂ} (hv : C.IsTorsion v) :
    C.HasIntegralValues (p := p) n (C.twistedTranslate n v G) := by
  intro u hu
  rw [C.norm_torsionValue_twistedTranslate n G hu hv]
  exact hG _ (hu.add hv)

end
/-- The pair `w(u) = (θ[u]², σ[u]²)` of squared torsion values of degree `1`, read in `ℂ_p`. -/
noncomputable def squarePair (u : ℂ) : ℂ_[p] × ℂ_[p] :=
  (ιₚ (C.torsionValue 1 C.θ u) ^ 2, ιₚ (C.torsionValue 1 C.σ u) ^ 2)

lemma squarePair_fst_eq_zero_iff {u : ℂ} : (C.squarePair u).1 = 0 ↔ u + C.t ∈ C.Λ := by
  simp [squarePair, torsionValue_eq, theta_eq_zero_iff]

lemma squarePair_snd_eq_zero_iff {u : ℂ} : (C.squarePair u).2 = 0 ↔ u ∈ C.Λ := by
  simp [squarePair, torsionValue_eq, sigma_eq_zero_iff]

/-- The pair `w(u)` is never zero, because `t ∉ Λ`. -/
lemma squarePair_ne_zero (u : ℂ) : C.squarePair u ≠ 0 := by
  intro h
  obtain ⟨h_fst, h_snd⟩ := Prod.ext_iff.1 h
  exact C.t_notMem <|
    (add_mem_cancel_left (C.squarePair_snd_eq_zero_iff.1 h_snd)).1
      (C.squarePair_fst_eq_zero_iff.1 h_fst)

/-- For a torsion point `u` the norm in `ℂ_p × ℂ_p` of `w(u) = (θ[u]², σ[u]²)` depends only on `u`
modulo `Λ`: twisted translation by a period multiplies `θ` and `σ` by a sign. -/
lemma norm_squarePair_add_of_mem {u l : ℂ} (hu : C.IsTorsion u) (hl : l ∈ C.Λ) :
    ‖C.squarePair (p := p) (u + l)‖ = ‖C.squarePair (p := p) u‖ := by
  have h_sign {G : ℂ → ℂ} {s : ℂ} (hs : s = 1 ∨ s = -1) (hG : C.twistedTranslate 1 l G = s • G) :
      ‖ιₚ (C.torsionValue 1 G (u + l))‖ = ‖ιₚ (C.torsionValue 1 G u)‖ := by
    rw [← C.norm_torsionValue_twistedTranslate 1 G hu (.of_mem hl), hG]
    obtain rfl | rfl := hs
    · rw [one_smul]
    · simp [torsionValue_eq]
  have hθ : C.twistedTranslate 1 l C.θ = C.multiplier l • C.θ := C.twistedTranslate_theta_of_mem hl
  have hσ : C.twistedTranslate 1 l C.σ = sigmaSign C.periodPair l • C.σ := by
    simpa only [twistedTranslate, one_smul, pow_one] using thetaShift_of_mem sigma_mem_thetaSpace hl
  have h_sigmaSign (v : ℂ) : sigmaSign C.periodPair v = 1 ∨ sigmaSign C.periodPair v = -1 := by
    unfold sigmaSign
    split_ifs <;> simp
  have hχ : C.multiplier l = 1 ∨ C.multiplier l = -1 := by
    simpa [C.multiplier_eq_neg_sigmaSign hl, neg_eq_iff_eq_neg, or_comm] using h_sigmaSign _
  simp only [squarePair, Prod.norm_mk, norm_pow, h_sign hχ hθ, h_sign (h_sigmaSign l) hσ]

/-- In the degree `1` the torsion value of `G` at `2 u` is that of `G(2 z)`, with the degree `4`,
at `u`. -/
lemma torsionValue_two_mul (G : ℂ → ℂ) (u : ℂ) :
    C.torsionValue 1 G (2 * u) = C.torsionValue 4 (fun z : ℂ ↦ G (2 * z)) u :=
  (C.torsionValue_comp_isogeny C.isIsogeny_two 1 G u).symm

/-- For a prime `d ≡ 7 (mod 8)` the doubling formula for `θ` holds for torsion values:
`θ[2 u] = θ[u] ^ 4 - σ[u] ^ 4`. -/
lemma torsionValue_theta_two_mul [PrimeSevenModEight d] (u : ℂ) :
    C.torsionValue 1 C.θ (2 * u) = C.torsionValue 1 C.θ u ^ 4 - C.torsionValue 1 C.σ u ^ 4 := by
  rw [torsionValue_two_mul]
  simp only [torsionValue_eq, theta_two_mul]
  ring

/-- For a prime `d ≡ 7 (mod 8)` the doubling formula for `σ²` holds for torsion values:
`σ[2 u]² = θ[u]² σ[u]² (4 θ[u] ^ 4 + a₁² θ[u]² σ[u]² + 4 σ[u] ^ 4)`. -/
lemma torsionValue_sigma_two_mul_sq [PrimeSevenModEight d] (u : ℂ) :
    C.torsionValue 1 C.σ (2 * u) ^ 2 =
      C.torsionValue 1 C.θ u ^ 2 * C.torsionValue 1 C.σ u ^ 2 *
        (4 * C.torsionValue 1 C.θ u ^ 4 +
          C.a₁ ^ 2 * C.torsionValue 1 C.θ u ^ 2 * C.torsionValue 1 C.σ u ^ 2 +
          4 * C.torsionValue 1 C.σ u ^ 4) := by
  rw [torsionValue_two_mul]
  simp only [torsionValue_eq, mul_pow, sigma_two_mul_sq]
  ring

/-- For a prime `d ≡ 7 (mod 8)`, doubling acts on `w(u) = (θ[u]², σ[u]²)` through `doublingForms`,
the quartic forms `(w₀² - w₁²)²` and `w₀ w₁ (4 w₀² + a₁² w₀ w₁ + 4 w₁²)`. -/
lemma squarePair_two_mul [PrimeSevenModEight d] (u : ℂ) :
    C.squarePair (2 * u) = doublingForms (ιₚ C.a₁) (C.squarePair u) := by
  ext
  · simp only [squarePair, doublingForms, C.torsionValue_theta_two_mul u, map_sub, map_pow,
      ← pow_mul]
  · simpa only [squarePair, doublingForms, map_mul, map_add, map_pow, map_ofNat, ← pow_mul]
      using congrArg ιₚ (C.torsionValue_sigma_two_mul_sq u)

/-- For a prime `d ≡ 7 (mod 8)` the pair `w(2 ^ j u)` is the `j`-th iterate of the map
`doublingForms (ιₚ C.a₁)`, whose two quartic forms are given in `squarePair_two_mul`, at
`w(u) = (θ[u]², σ[u]²)`. -/
lemma squarePair_two_pow_mul [PrimeSevenModEight d] (u : ℂ) (j : ℕ) :
    C.squarePair (2 ^ j * u) = (doublingForms (ιₚ C.a₁))^[j] (C.squarePair u) := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', ← ih, ← squarePair_two_mul, pow_succ', mul_assoc]

/-- For a prime `d ≡ 7 (mod 8)`, doubling `j` times raises the norm of `w(u) = (θ[u]², σ[u]²)` to
the power `4 ^ j`. -/
lemma norm_squarePair_two_pow_mul [PrimeSevenModEight d] (u : ℂ) (j : ℕ) :
    ‖C.squarePair (2 ^ j * u)‖ = ‖C.squarePair u‖ ^ 4 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc, squarePair_two_mul,
      norm_doublingForms C.norm_a₁_le_one (C.norm_disc_eq_one ιₚ), ih, ← pow_mul, pow_succ]

/-- Among the powers of `2`, two with different exponents are congruent modulo `n ≠ 0`. -/
lemma exists_ne_two_pow_modEq {n : ℕ} (hn : n ≠ 0) :
    ∃ i j : ℕ, i ≠ j ∧ (2 ^ i : ℤ) ≡ 2 ^ j [ZMOD n] := by
  have : NeZero n := ⟨hn⟩
  obtain ⟨i, j, hij, h_eq⟩ :=
    Finite.exists_ne_map_eq_of_infinite fun i : ℕ ↦ ((2 ^ i : ℤ) : ZMod n)
  exact ⟨i, j, hij, (ZMod.intCast_eq_intCast_iff _ _ n).1 h_eq⟩

/-- For a prime `d ≡ 7 (mod 8)` the pair `w(u) = (θ[u]², σ[u]²)` has norm `1` in `ℂ_p × ℂ_p` at
every torsion point `u`. -/
lemma norm_squarePair [PrimeSevenModEight d] {u : ℂ} (hu : C.IsTorsion u) :
    ‖C.squarePair (p := p) u‖ = 1 := by
  have ⟨n, hn, hnu⟩ := hu
  -- The points `2 ^ i u` form a finite set modulo `Λ`, so two of them are congruent; doubling
  -- raises the norm to the fourth power, so two different powers of it are equal.
  obtain ⟨i, j, hij, h_mod⟩ := exists_ne_two_pow_modEq hn
  obtain ⟨k, hk⟩ : ∃ k : ℤ, 2 ^ j - 2 ^ i = (n : ℤ) * k := h_mod.dvd
  have h_shift : 2 ^ j * u = 2 ^ i * u + k • (n * u) := by
    rw [zsmul_eq_mul]
    have hk' : (2 ^ j - 2 ^ i : ℂ) = n * k := by exact_mod_cast hk
    linear_combination u * hk'
  have h_pow : ‖C.squarePair u‖ ^ 4 ^ j = ‖C.squarePair u‖ ^ 4 ^ i := by
    rw [← norm_squarePair_two_pow_mul, ← norm_squarePair_two_pow_mul, h_shift,
      C.norm_squarePair_add_of_mem (by exact_mod_cast hu.natCast_mul (2 ^ i)) (zsmul_mem hnu k)]
  by_contra h_ne
  have h_exp : 4 ^ j = 4 ^ i :=
    pow_right_injective₀ (norm_pos_iff.2 (C.squarePair_ne_zero u)) h_ne h_pow
  exact hij (Nat.pow_right_injective (by norm_num) h_exp).symm

/-- For `d` a prime `≡ 7 (mod 8)`, a `p`-adic place `ιₚ` and a torsion point `u` (`u ∈ ℚ Λ`),
consider the degree-`1` torsion values `σ[u]` and `θ[u]` of the sigma function `σ` and of `C.θ`.
These are the values at `0` of their twisted translates by `u` for the Hermitian form of the
lattice. The larger of `‖ιₚ σ[u]‖` and `‖ιₚ θ[u]‖` is `1`. This is a form of the integrality of
Siegel functions at torsion points. -/
lemma max_norm_torsionValue [PrimeSevenModEight d] {u : ℂ} (hu : C.IsTorsion u) :
    max ‖ιₚ (C.torsionValue 1 C.σ u)‖ ‖ιₚ (C.torsionValue 1 C.θ u)‖ = 1 := by
  have h_sq : max ‖ιₚ (C.torsionValue 1 C.σ u)‖ ‖ιₚ (C.torsionValue 1 C.θ u)‖ ^ 2 = 1 := by
    rw [← C.norm_squarePair hu, max_comm]
    simp only [squarePair, Prod.norm_mk, norm_pow]
    exact pow_left_monotoneOn.map_max (norm_nonneg _) (norm_nonneg _)
  exact (pow_eq_one_iff_of_nonneg (le_max_of_le_left (norm_nonneg _)) two_ne_zero).1 h_sq

/-- For a CM lattice `C` with `d` a prime `≡ 7 (mod 8)`, the sigma function `C.σ` has integral
torsion values in degree `1` at the chosen place `ιₚ` above `p`: for every torsion point `u`, the
image of `σ[u]` under `ιₚ` has norm at most `1` in `ℂ_p`.

This is a local analogue of the integrality of the Siegel function at torsion points (Ramachandra,
Robert): only at the chosen place above `p`, for these CM lattices, and with the normalization of
`torsionValue`. -/
lemma hasIntegralValues_sigma [PrimeSevenModEight d] : C.HasIntegralValues (p := p) 1 C.σ :=
  fun _ hu ↦ le_of_max_le_left (C.max_norm_torsionValue hu).le

/-- For a prime `d ≡ 7 (mod 8)` the theta function has integral torsion values in the degree `1`. -/
lemma hasIntegralValues_theta [PrimeSevenModEight d] : C.HasIntegralValues (p := p) 1 C.θ :=
  fun _ hu ↦ le_of_max_le_right (C.max_norm_torsionValue hu).le

/-- For a prime `d ≡ 7 (mod 8)` the torsion values of `y θ³` (`translatedYThetaCube`) satisfy the
monic quadratic equation that the cubic gives after multiplication by `θ ^ 6`. -/
lemma torsionValue_translatedYThetaCube_sq_add [PrimeSevenModEight d] (u : ℂ) :
    C.torsionValue 3 C.translatedYThetaCube u ^ 2 +
      C.a₁ * C.torsionValue 1 C.θ u * C.torsionValue 1 C.σ u ^ 2 *
        C.torsionValue 3 C.translatedYThetaCube u =
      C.torsionValue 1 C.σ u ^ 6 + C.torsionValue 1 C.θ u ^ 4 * C.torsionValue 1 C.σ u ^ 2 := by
  simp only [torsionValue_eq]
  linear_combination exp (-(π * ‖u‖ ^ 2 / (2 * C.area))) ^ 6 * C.translatedYThetaCube_sq_add u

/-- For a prime `d ≡ 7 (mod 8)` the section `y θ³` has integral torsion values in the degree `3`,
as roots of monic quadratic equations with integral coefficients. -/
lemma hasIntegralValues_translatedYThetaCube [PrimeSevenModEight d] :
    C.HasIntegralValues (p := p) 3 C.translatedYThetaCube := by
  intro u hu
  set θu : ℂ_[p] := ιₚ (C.torsionValue 1 C.θ u)
  set σu : ℂ_[p] := ιₚ (C.torsionValue 1 C.σ u)
  have hθ : ‖θu‖ ≤ 1 := C.hasIntegralValues_theta u hu
  have hσ : ‖σu‖ ≤ 1 := C.hasIntegralValues_sigma u hu
  -- Both coefficients of the quadratic equation for the image in `ℂ_p` are integral.
  have h_linear : ‖ιₚ C.a₁ * θu * σu ^ 2‖ ≤ 1 := by
    grw [norm_mul, norm_mul, norm_pow, C.norm_a₁_le_one, hθ, hσ]
    norm_num
  have h_const : ‖σu ^ 6 + θu ^ 4 * σu ^ 2‖ ≤ 1 := by
    grw [IsUltrametricDist.norm_add_le_max, norm_mul, norm_pow, norm_pow, norm_pow, hθ, hσ]
    norm_num
  exact norm_le_one_of_sq_add_mul_eq h_linear h_const <| by
    simpa only [map_add, map_mul, map_pow] using
      congrArg ιₚ (C.torsionValue_translatedYThetaCube_sq_add u)

/-- For `d` a prime `≡ 7 (mod 8)` and a `p`-adic place `ιₚ`, take a triple `(a, b, c)` and the
monomial `θ^a (σ²)^b G^c` (`monomialSection`), a section of degree `a + 2b + 3c`. Here `σ` is the
sigma function of the lattice and `G = translatedYThetaCube` is the entire function equal to `y θ³`
off `t + Λ`. For every torsion point `u`, the torsion value of this monomial in degree `a + 2b + 3c`
at `u` has `ιₚ`-image of norm at most `1`. -/
lemma hasIntegralValues_monomialSection [PrimeSevenModEight d] (x : ℕ × ℕ × ℕ) :
    C.HasIntegralValues (p := p) (monomialDeg x) (C.monomialSection x) := by
  obtain ⟨a, b, c⟩ := x
  simpa only [monomialDeg, monomialSection, mul_one, add_assoc] using
    (C.hasIntegralValues_theta.pow a).mul <| ((C.hasIntegralValues_sigma.pow 2).pow b).mul
      (C.hasIntegralValues_translatedYThetaCube.pow c)

end New.CMLattice

end TorsionValues
