import New.UpperBound.Divisibility.HeckeEdges

/-!
# Elementary divisors of one scaled Hecke operator on the integral source forms

Let `l` be a place of a marked set `Λ` above a prime `p`, and write `o₀ = D.o₀ p`. This file
applies the theorem on elementary divisors, `New.FrobeniusCycle.elementary_divisors`, to the
normalised Hecke operator `New.Data.IsMarked.scaledHeckeOperator` at `l`, acting on the integral
source forms `New.Data.integralSourceForms`. The a-places that induce `l` or its conjugate form one
orbit under the place named by `-p ^ o₀` (`New.Data.exists_orbit_of_mem_aPlaces`), where the place
named by an integer acts on infinite places by multiplication. This orbit gives a Frobenius cycle.

## Main definitions and results

* `New.Data.IsMarked.exists_frobeniusCycle`: such a Frobenius cycle exists.
* `New.Data.IsMarked.isOntoUpToColength_scaledHeckeOperator`: the operator keeps the integral source
  forms and is onto modulo `p ^ j₀` up to a bounded colength.

Notions from other files:
* `New.IsOntoUpToColength`: The endomorphism `y` keeps `M`, and for some natural number `i ≤ c` the
  sum `y (M) + p ^ j₀ • M` has index dividing `p ^ i` in `M` (in the sense of `New.ColengthDvd`):
  `y` is onto on `M` modulo `p ^ j₀` up to an index `p ^ i`.
* `New.Data.IsMarked`: a marked set `Λ` of primes of `E` is disjoint from its complex conjugate,
  each of its primes is induced by an a-place (an element of `D.aPlaces`), `p` is exceptional
  (`New.Data.IsExceptional`), and `p` is below `D.x₁` and not split in the imaginary quadratic
  field.
* `New.Data.integralSourceForms`: the module of the elements of `D.SourceForm` of gauge at most `1`.
* `New.FrobeniusCycle`: ring maps `T.embedding i : W → R` for `i` in `ℤ/N`, alternately even and
  odd, with `T.embedding (i + 1) ≡ T.embedding i ^ P` modulo `p`, where `P = p ^ frobExp` and the
  residue field of `W` has `P ^ N` elements.

## Relation to the literature

An integrally scaled Hecke operator above p, acting on forms at a-places linked in a circle by
Frobenius and conjugation, has elementary divisors of small mean exponent outside a small share. So
using it once per theta lift, to keep divisibility when the partner of an a-place is an a-place,
costs little colength. Slopes of T_p of at most about k/(p+1) for GL(2) over Q and regular p, and
integral scalings of Hecke operators, are known. Related work: Arsovski, Limiting measures of
supersingularities, 2019; Liu–Truong–Xiao–Zhao, Slopes of modular forms and geometry of eigencurves,
2023; Fakhruddin–Pilloni, Hecke operators and the coherent cohomology of Shimura varieties, 2021.
-/

namespace New.Data

open Finset ZMod Nat Columns Parameters RingHom Module Real IsLocalization AtPrime NumberField

/-- Let `T` be a Frobenius cycle with `N` letters: a cycle of `N` ring maps from a local ring `W`,
each congruent modulo the prime `p = T.p` to the `P`-th power of the one before, with
`P = p ^ T.frobExp`; put `q = P ^ N`, the size of the residue field. Let `13 ≤ p < D.x₁`, let
`0 < T.frobExp ≤ r`, where `r = D.ceilLogLifts p` is the least natural number with `D.m ≤ p ^ r`,
let `N` be at most the number of infinite places, and let `D.m ≤ T.frobExp * N`. With `k = D.k`,
`a = D.a` and `θ = 1 / (m ^ 2 f)` for the numerical parameters `m = D.m`, `f = D.f` of the data, the
size conditions `IsLargeDegree` then hold: `0 < r`, `2 r ≤ k`, `0 < θ ≤ 1`, `a ^ 4 ≤ q` and
`(N k log q / θ) ^ 5 P ^ (3 r) ≤ a`. -/
theorem isLargeDegree_of_le_card {P : Parameters} (D : Data P) {N : ℕ} [NeZero N] {W O : Type}
    [CommRing W] [IsLocalRing W] [CommRing O] (T : FrobeniusCycle N W O) (h13 : 13 ≤ T.p)
    (hp : T.p < D.x₁) (hfrobExp_pos : 0 < T.frobExp)
    (hfrobExp_le : T.frobExp ≤ D.ceilLogLifts T.p)
    (hN_le : N ≤ Fintype.card D.Φ) (hm_le : D.m ≤ T.frobExp * N) :
    T.IsLargeDegree D.k D.a (D.ceilLogLifts T.p) (1 / (D.m ^ 2 * D.f)) := by
  have : Fact T.p.Prime := ⟨T.prime⟩
  have hq : T.q = T.p ^ (T.frobExp * N) := (pow_mul _ _ _).symm
  refine
    { block_pos := hfrobExp_pos.trans_le hfrobExp_le
      two_mul_block_le := D.nat_le_of_hasLogBound
      proportion_pos := one_div_pos.2 (HasLogBound.pos D)
      proportion_le_one := D.le_of_hasLogBound
      degree_pow_le := ?_
      le_degree := ?_ }
  · -- `q = p ^ (frobExp * N) ≥ 3 ^ m ≥ exp m ≥ exp (logB * 5)`
    have h_three : 3 ^ D.m ≤ T.q := by
      rw [hq]
      exact (Nat.pow_le_pow_right (by norm_num) hm_le).trans (Nat.pow_le_pow_left (by lia) _)
    rw [← Nat.cast_le (α := ℝ), Nat.cast_pow]
    calc (D.a : ℝ) ^ 4 ≤ exp (D.logB * 5) := D.le_of_hasLogBound
      _ ≤ exp 1 ^ D.m := (exp_le_exp.2 D.le_of_hasLogBound).trans_eq (exp_one_pow _).symm
      _ ≤ 3 ^ D.m := by grw [exp_one_lt_three.le]
      _ ≤ T.q := mod_cast h_three
  · -- `log q ≤ frobExp N log x₁` and `T.P ^ (3 * ceilLogLifts p) ≤ √b`, since `p < x₁`.
    -- The final bound compares magnitudes; it uses `hfrobExp_upper` and `hN_upper`.
    have hfrobExp_upper : D.HasLogUpper T.frobExp (Real.log D.logX₁) :=
      D.hasLogUpper_of_le hfrobExp_le
    have hN_upper : D.HasLogUpper N (11 * D.logX + (Real.log D.logB / 5 + P.constantBound)) :=
      D.hasLogUpper_of_le hN_le
    have h_logX₁ : 0 < D.logX₁ := HasLogBound.pos D
    have h_log : Real.log T.q ≤ T.frobExp * N * D.logX₁ := by
      rw [hq, Nat.cast_pow, Real.log_pow, Nat.cast_mul]
      gcongr
      exact (log_le_iff_le_exp (by positivity)).2 hp.le
    have h_pow : (D.x₁ ^ T.frobExp) ^ (3 * D.ceilLogLifts T.p) ≤ √D.b := by
      have h_exp : T.frobExp * (3 * D.ceilLogLifts T.p) ≤ 3 * l₀ D.towerExp ^ 2 := by
        grw [hfrobExp_le, (ceilLogLifts_le_l₀ : D.ceilLogLifts T.p ≤ l₀ D.towerExp), sq,
          mul_left_comm]
      calc (D.x₁ ^ T.frobExp) ^ (3 * D.ceilLogLifts T.p) = D.x₁ ^
             (T.frobExp * (3 * D.ceilLogLifts T.p)) :=
            (pow_mul _ _ _).symm
        _ ≤ D.x₁ ^ (3 * l₀ D.towerExp ^ 2) := pow_le_pow_right₀ (one_le_exp h_logX₁.le) h_exp
        _ ≤ √D.b := D.x₁_pow_le_sqrt_b
    calc ((N : ℝ) * D.k * Real.log T.q / (1 / (D.m ^ 2 * D.f))) ^ 5 *
          (T.P : ℝ) ^ (3 * D.ceilLogLifts T.p)
        ≤ ((N : ℝ) * D.k * (T.frobExp * N * D.logX₁) / (1 / (D.m ^ 2 * D.f))) ^ 5 * √D.b := by
          grw [h_log, T.p.cast_pow, hp, h_pow]
      _ ≤ (D.a : ℝ) := D.le_of_hasLogBound

/-- For a Frobenius cycle with `N = ℓ + ℓ` letters, prime `p = T.p` and `P = p ^ T.frobExp`, where
`0 < T.frobExp ≤ r` and `r = D.ceilLogLifts p` is the least natural number with `D.m ≤ p ^ r`, the
divisor constant `c = T.divisorConstant D.k a r = N a (P ^ (-2 r) + r ^ 2 / (k P))` for `k = D.k`
and `a = D.a` satisfies `3 c ≤ 12 a ℓ / (m p)`, with `m = D.m`. -/
theorem three_mul_divisorConstant_le {P : Parameters} (D : Data P) {N ℓ : ℕ} [NeZero N] {W O : Type}
    [CommRing W] [IsLocalRing W] [CommRing O] (T : FrobeniusCycle N W O)
    (hfrobExp_pos : 0 < T.frobExp) (hfrobExp_le : T.frobExp ≤ D.ceilLogLifts T.p) (hℓ : ℓ + ℓ = N) :
    3 * T.divisorConstant D.k D.a (D.ceilLogLifts T.p) ≤ 12 * (D.a * ℓ : ℕ) / (D.m * T.p) := by
  -- Each of the two terms of the bracket in `T.divisorConstant` is at most `1 / (m p)`.
  have : Fact T.p.Prime := ⟨T.prime⟩
  set r : ℕ := D.ceilLogLifts T.p
  have hp_pos : (0 : ℝ) < T.p := mod_cast T.prime.pos
  have hm_pos : (0 : ℝ) < D.m := HasLogBound.pos D
  have hk_pos : (0 : ℝ) < D.k := HasLogBound.pos D
  have hp_le : T.p ≤ T.P := Nat.le_self_pow hfrobExp_pos.ne' T.p
  have hP_pos : (0 : ℝ) < T.P := hp_pos.trans_le (mod_cast hp_le)
  have h_first : D.m * T.p ≤ T.P ^ (2 * r) :=
    calc D.m * T.p ≤ T.p ^ r * T.p ^ r :=
          Nat.mul_le_mul (le_pow_clog T.prime.one_lt D.m)
            (Nat.le_self_pow (hfrobExp_pos.trans_le hfrobExp_le).ne' T.p)
      _ = T.p ^ (2 * r) := by rw [two_mul, pow_add]
      _ ≤ T.P ^ (2 * r) := Nat.pow_le_pow_left hp_le _
  have h_second : (r ^ 2 / (D.k * T.P) : ℝ) ≤ 1 / (D.m * T.p) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_assoc]
    exact mul_le_mul (D.le_of_hasLogBound : (r ^ 2 * D.m : ℝ) ≤ D.k) (mod_cast hp_le) hp_pos.le
      hk_pos.le
  calc 3 * T.divisorConstant D.k D.a r
      = 3 * (N * D.a * (1 / T.P ^ (2 * r) + r ^ 2 / (D.k * T.P))) := by
        rw [FrobeniusCycle.divisorConstant]
    _ ≤ 3 * (N * D.a * (1 / (D.m * T.p) + 1 / (D.m * T.p))) := by
      gcongr
      exact_mod_cast h_first
    _ = 12 * (D.a * ℓ : ℕ) / (D.m * T.p) := by
      rw [show (N : ℝ) = ℓ + ℓ by exact_mod_cast hℓ.symm]
      push_cast
      ring

/-- Let `p` be inert in the imaginary quadratic field of discriminant datum `P.d`
(`chiK P.d p = -1`), let `o₀` be odd, let `τ` be an a-place and let `N` be the order of the `o₀`-th
power of the place named by `-p`. Then some injective family `t` of places, indexed modulo `N`, goes
from each member to the next by multiplication with the place named by `-p ^ o₀` and consists of
exactly the a-places that induce the same prime as `τ` or its conjugate prime. -/
theorem exists_orbit_of_mem_aPlaces {P : Parameters} {p : ℕ} (D : Data P) [Fact p.Prime]
    [PadicPlace p]
    (h_inert : chiK P.d p = -1) (ho₀_odd : Odd (D.o₀ p)) {τ : D.Φ} (hτ : τ ∈ D.aPlaces)
    [NeZero (orderOf (D.placeOfInt (-p) ^ D.o₀ p))] :
    ∃ t : ZMod (orderOf (D.placeOfInt (-p) ^ D.o₀ p)) → D.Φ,
      t.Injective ∧
      (∀ i : ZMod (orderOf (D.placeOfInt (-p) ^ D.o₀ p)),
        t (i + 1) = D.placeOfInt (-p ^ D.o₀ p) * t i) ∧
      ∀ σ : D.Φ,
        σ ∈ Set.range t ↔
          σ ∈ D.aPlaces ∧
          (inducedPlace σ = inducedPlace τ ∨ inducedPlace σ = star (inducedPlace τ)) := by
  set o : ℕ := D.o₀ p
  let c : D.Φ := D.placeOfInt (-p) ^ o
  refine ⟨fun i ↦ c ^ i.val * τ, fun _ _ ↦ ?_, fun i ↦ ?_, fun σ ↦ ?_⟩
  · simp [c, pow_inj_mod, ← natCast_eq_natCast_iff']
  · simp [← ho₀_odd.neg_pow, ← placeOfInt_pow, c, _root_.pow_succ', val_add, val_one_eq_one_mod,
      mul_assoc]
  · -- The places inducing `inducedPlace τ` or its conjugate are the `placeOfInt (-p) ^ i * τ`, and
    -- such a place is an a-place exactly if `o ∣ i`.
    have h_aPlace_iff (i : ℕ) : D.placeOfInt (-p) ^ i * τ ∈ D.aPlaces ↔ o ∣ i := by
      simp_all [o, aPlaces, o₀, orderOf_dvd_iff_pow_eq_one]
    have h_range : σ ∈ Set.range (fun i : ZMod (orderOf c) ↦ c ^ i.val * τ) ↔
        ∃ k : ℕ, D.placeOfInt (-p) ^ (o * k) * τ = σ := by
      simp [natCast_zmod_surjective.exists, c, pow_mul]
    rw [h_range, inducedPlace_eq_or_star_iff h_inert]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨(h_aPlace_iff _).2 (dvd_mul_right o k), o * k, rfl⟩
    · rintro ⟨h_mem, i, rfl⟩
      obtain ⟨k, rfl⟩ := (h_aPlace_iff i).1 h_mem
      exact ⟨k, rfl⟩

section Ring

open ComplexConjugate

variable {P : Parameters} {D : Data P} {p : ℕ} [Fact p.Prime] [PadicPlace p] {l : FinPlace D.E}

open scoped Classical in
/-- The embedding at the infinite place `σ`, composed with conjugation if `σ` does not induce the
prime `l`. -/
noncomputable def embeddingToward (l : FinPlace D.E) (σ : D.Φ) : D.E →+* ℂ :=
  if inducedPlace σ = l then Φ σ else (Φ σ).comp conj

/-- If `σ` induces `l` or its conjugate, then `embeddingToward l σ` induces `l`. -/
lemma placeOfEmb_embeddingToward {σ : D.Φ} (hσ : inducedPlace σ = l ∨ inducedPlace σ = star l) :
    placeOfEmb (ιₚ.comp (embeddingToward l σ)) = l := by
  rw [embeddingToward]
  split_ifs with h
  · exact h
  · rw [← comp_assoc, placeOfEmb_comp_star]
    exact star_eq_iff_star_eq.1 (hσ.resolve_left h).symm

/-- If `σ` induces `l` or its conjugate, then `embeddingToward l σ` maps the valuation ring of `l`
into `embValRing`. -/
lemma embeddingToward_mem_embValRing {σ : D.Φ} (hσ : inducedPlace σ = l ∨ inducedPlace σ = star l)
    {x : D.E} (hx : x ∈ l.valuationSubringAtPrime D.E) : embeddingToward l σ x ∈ embValRing := by
  rw [l.valuationSubringAtPrime_eq_valuationSubring, Valuation.mem_valuationSubring_iff,
    ← placeOfEmb_embeddingToward hσ] at hx
  exact (isEquiv_placeOfEmb (ιₚ.comp (embeddingToward l σ))).le_one_iff_le_one.2 hx

/-- For an infinite place `σ` that induces `l` or its conjugate, `embeddingToward l σ` as a map
from the valuation ring of `l` to `embValRing`. -/
noncomputable def letterEmbedding (σ : D.Φ) (hσ : inducedPlace σ = l ∨ inducedPlace σ = star l) :
    l.valuationSubringAtPrime D.E →+* embValRing :=
  (embeddingToward l σ).restrict _ _ fun _ ↦ embeddingToward_mem_embValRing hσ

lemma coe_letterEmbedding (σ : D.Φ) (hσ : inducedPlace σ = l ∨ inducedPlace σ = star l)
    (x : l.valuationSubringAtPrime D.E) : (letterEmbedding σ hσ x : ℂ) = embeddingToward l σ x :=
  rfl

lemma not_isUnit_natCast_embValRing : ¬IsUnit (p : embValRing) := by
  rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, Valuation.mem_maximalIdeal_iff]
  change ‖ιₚ (p : ℂ)‖ < 1
  simpa using norm_p_lt_one

/-- Let `D` be data for the parameters `P`, let `p` be inert in the imaginary quadratic field, let
`l` be a split finite place of `D.E` and let `e` be odd. The infinite places form a group `(ℤ/q₁)ˣ`,
in which an integer prime to `q₁` names its class; let `σ'` be the product of `σ` and the place
named by `-p ^ e`, and let the primes induced by both through `ιₚ : ℂ → ℂ_p` be `l` or its
conjugate. For every `x` in the valuation ring of `l`, the image of `x` under `letterEmbedding σ'`
is congruent modulo `p` to the `p ^ e`-th power of its image under `letterEmbedding σ`. -/
lemma dvd_letterEmbedding_sub_pow {P : Parameters} {D : Data P} {p : ℕ} [Fact p.Prime]
    [PadicPlace p] {l : FinPlace D.E} (h_inert : chiK P.d p = -1) (hl : l.IsSplit) {e : ℕ}
    (he : Odd e) {σ σ' : D.Φ} (h_next : σ' = D.placeOfInt (-p ^ e) * σ)
    (hσ : inducedPlace σ = l ∨ inducedPlace σ = star l)
    (hσ' : inducedPlace σ' = l ∨ inducedPlace σ' = star l) (x : l.valuationSubringAtPrime D.E) :
    (p : embValRing) ∣ letterEmbedding σ' hσ' x - letterEmbedding σ hσ x ^ p ^ e := by
  -- Reduce modulo `p`. It is enough to compare the two ring maps on the integers of `E`. There
  -- the automorphism `g` named by `-p ^ e` satisfies `g a ≡ (star a) ^ p ^ e`.
  have : CharP (embValRing ⧸ Ideal.span {(p : embValRing)}) p :=
    CharP.quotient _ p not_isUnit_natCast_embValRing
  let red : embValRing →+* embValRing ⧸ Ideal.span {(p : embValRing)} := Ideal.Quotient.mk _
  let j : 𝓞 D.E →+* l.valuationSubringAtPrime D.E := algebraMap _ _
  let ψ : 𝓞 D.E →+* embValRing ⧸ Ideal.span {(p : embValRing)} :=
    (red.comp (letterEmbedding σ hσ)).comp j
  let g : 𝓞 D.E →+* 𝓞 D.E := galOfPlaceInt (P.placeOfInt D.towerExp (-p ^ e))
  have h_frob (a : 𝓞 D.E) : ψ (g a) = ψ (star a) ^ p ^ e := by
    have h_dvd : ψ p ∣ ψ (star a ^ p ^ e - g (star (star a))) :=
      map_dvd ψ (natCast_dvd_pow_sub_galOfPlaceInt_star h_inert he (star a))
    have hp_zero : ψ p = 0 := (map_natCast ψ p).trans (CharP.cast_eq_zero _ p)
    rwa [hp_zero, zero_dvd_iff, map_sub, map_pow, star_star, sub_eq_zero, eq_comm] at h_dvd
  -- Exactly one of `σ` and `σ'` induces `l`, so exactly one embedding is conjugated.
  have h_shift (a : 𝓞 D.E) :
      letterEmbedding σ' hσ' (j (star a)) = letterEmbedding σ hσ (j (g a)) := by
    have hl_ne : star l ≠ l := hl
    have h_conj : inducedPlace σ' = star (inducedPlace σ) := by
      rw [h_next, D.inducedPlace_neg_pow_mul_of_odd h_inert he]
    have h_emb : Φ σ (g a : D.E) = Φ σ' a := by
      rw [h_next, mul_comm _ σ, phi_mul]
      rfl
    ext
    rw [coe_letterEmbedding, coe_letterEmbedding, embeddingToward, embeddingToward, h_conj]
    obtain h | h := hσ
    · rw [h, ite_eq_right hl_ne, ite_eq_left rfl]
      change Φ σ' (star (star (a : D.E))) = Φ σ (g a : D.E)
      rw [star_star, h_emb]
    · rw [h, star_star, ite_eq_left rfl, ite_eq_right hl_ne]
      change Φ σ' (star (a : D.E)) = Φ σ (star (g a : D.E))
      rw [map_star_complex, map_star_complex, h_emb]
  have h_hom : red.comp (letterEmbedding σ' hσ') =
      (iterateFrobenius _ p e).comp (red.comp (letterEmbedding σ hσ)) := by
    refine ringHom_ext l.asIdeal.primeCompl (RingHom.ext fun a ↦ ?_)
    obtain ⟨b, rfl⟩ : ∃ b : 𝓞 D.E, star b = a := star_involutive.surjective a
    change red (letterEmbedding σ' hσ' (j (star b))) = ψ (star b) ^ p ^ e
    rw [h_shift, ← h_frob b]
    rfl
  exact Ideal.mk_span_eq_iff_dvd_sub.1 (RingHom.congr_fun h_hom x)

omit [PadicPlace p] in
/-- Let `p` be exceptional: inert in the imaginary quadratic field, not `±1` modulo the number `D.m`
of lifts, and with `D.o₀ p` odd and at most `D.ceilLogLifts p`. Then the residue field of a prime
`l` of `D.E` above `p` has `p ^ o` elements, where `o = orderOf (D.placeOfInt (-p))` is the order of
the infinite place named by `-p`. -/
lemma IsExceptional.card_residueField (h_served : D.IsExceptional p)
    (hpl : (p : 𝓞 D.E) ∈ l.asIdeal) :
    Nat.card (IsLocalRing.ResidueField (l.valuationSubringAtPrime D.E)) =
      p ^ orderOf (D.placeOfInt (-p)) := by
  have h_even : 2 ∣ orderOf (D.placeOfInt (-p)) := D.m_even.two_dvd.trans h_served.m_dvd_orderOf
  calc Nat.card (IsLocalRing.ResidueField (l.valuationSubringAtPrime D.E))
      = l.q := (Nat.card_congr (equivQuotMaximalIdeal l.asIdeal _).toEquiv).symm
    _ = p ^ (orderOf (D.placeOfInt (-p))).lcm 2 :=
      q_eq_pow_lcm_of_inert hpl h_served.chiK_eq_neg_one
    _ = p ^ orderOf (D.placeOfInt (-p)) := by rw [Nat.lcm_eq_left h_even]

/-- Let `Λ` be a marked set for `p`, let `l ∈ Λ`, and let `o₀ = D.o₀ p`, the order modulo `q₀` of
the place named by the integer `-p`. Let `o₀ N` be the order of this place itself, and let `t i`,
for `i` modulo `N`, be infinite places that induce `l` or its conjugate, with `t (i + 1)` the place
named by `-p ^ o₀` times `t i`. Then the maps `New.Data.letterEmbedding (t i)` from the valuation
ring of `l` to the ring `embValRing` of `p`-integral complex numbers form a Frobenius cycle for the
prime `p` and the exponent `o₀`: each is congruent modulo `p` to the `p ^ o₀`-th power of the one
before, and a letter `i` is flagged as even (`isEven`) exactly if `t i` induces `l`, so parities
alternate. -/
theorem IsMarked.exists_frobeniusCycle {P : Parameters} {D : Data P} {p : ℕ} [Fact p.Prime]
    [PadicPlace p] {l : FinPlace D.E} {Λ : Finset (FinPlace D.E)} (hΛ : D.IsMarked Λ) (hl : l ∈ Λ)
    {N : ℕ} (h_order : orderOf (D.placeOfInt (-p)) = D.o₀ p * N) {t : ZMod N → D.Φ}
    (ht_succ : ∀ i : ZMod N, t (i + 1) = D.placeOfInt (-p ^ D.o₀ p) * t i)
    (ht_ind : ∀ i : ZMod N, inducedPlace (t i) = l ∨ inducedPlace (t i) = star l) :
    ∃ T : FrobeniusCycle N (l.valuationSubringAtPrime D.E) embValRing,
      T.p = p ∧
      T.frobExp = D.o₀ p ∧
      (∀ i : ZMod N, T.isEven i ↔ inducedPlace (t i) = l) ∧
      ∀ i : ZMod N, T.embedding i = letterEmbedding (t i) (ht_ind i) := by
  classical
  obtain ⟨h_inert, -, h_odd, -⟩ : D.IsExceptional p := hΛ.isExceptional
  have h_split : l.IsSplit := hΛ.isSplit hl
  have h13 : 13 ≤ p := P.thirteen_le_of_chiK_ne_one Fact.out hΛ.isSmallNonsplit.2
  obtain ⟨w, hw⟩ : ∃ w : ℂ, p = w ^ 2 := (Complex.isSquare p).exists_sq
  have hw_mem : w ∈ embValRing := by simpa [hw, pow_le_one_iff] using natCast_mem embValRing p
  refine ⟨{
    p := p
    frobExp := D.o₀ p
    embedding i := letterEmbedding (t i) (ht_ind i)
    isEven i := decide (inducedPlace (t i) = l)
    sqrtPrime := ⟨w, hw_mem⟩
    prime := Fact.out
    five_le_P := (by lia : 5 ≤ p).trans (Nat.le_self_pow h_odd.pos.ne' p)
    sqrtPrime_sq := Subtype.ext hw.symm
    frobenius_congr i := dvd_letterEmbedding_sub_pow h_inert h_split h_odd (ht_succ i) _ _
    isEven_succ i := ?_
    card_residueField := ?_ }, rfl, rfl, fun i ↦ decide_eq_true_iff, fun i ↦ rfl⟩
  · -- Multiplication with the place named by `-p ^ o₀` exchanges `l` and `star l`.
    rw [ht_succ, D.inducedPlace_neg_pow_mul_of_odd h_inert h_odd]
    obtain h | h := ht_ind i <;> simp [h, h_split]
  · rw [hΛ.isExceptional.card_residueField (hΛ.natCast_mem_asIdeal hl), h_order, pow_mul]

end Ring

/-- Let `Λ` be a marked set of finite places above `p`, let `l ∈ Λ`, and let `j₀` be a natural
number. The scaled Hecke operator at `l` acts on `D.SourceForm`, the forms of weight `D.columnCount`
and level `D.levelX 0`; it is `p ^ A` times the Hecke operator of index `r` at `l`, where
`A = D.heckeScalingExponent l` is `D.a` times the number of a-places inducing `l` and
`r = D.ceilLogLifts p` is least with `m ≤ p ^ r`. It maps the module of integral source forms (gauge
at most `1`) to itself, and it is onto modulo `p ^ j₀` up to an index dividing `p ^ i` for some
natural `i ≤ (12 A / (m p) + j₀ / (m ^ 2 f)) * dim`, the divisions being those of real numbers. Here
`m = D.m` and `f = D.f` are the numerical parameters of `D`, and `dim` is the complex dimension of
`D.SourceForm`. -/
theorem IsMarked.isOntoUpToColength_scaledHeckeOperator {P : Parameters} {p : ℕ} {D : Data P}
    [Fact p.Prime] [PadicPlace p] {Λ : Finset (FinPlace D.E)} (hΛ : D.IsMarked Λ) (j₀ : ℕ)
    {l : FinPlace D.E} (hl : l ∈ Λ) :
    IsOntoUpToColength (p : embValRing) D.integralSourceForms j₀ (hΛ.scaledHeckeOperator ⟨l, hl⟩)
      ((12 * D.heckeScalingExponent l / (D.m * p) + 1 / (D.m ^ 2 * D.f) * j₀) *
        finrank ℂ D.SourceForm) := by
  classical
  -- The a-places that induce `l` or `star l` form one orbit `t` under the place named by `-p ^ o₀`.
  -- Apply the bound for the edge Hecke operator to the Frobenius cycle of this orbit.
  have h_orbits : D.HasExceptionalOrbits p := hΛ.isExceptional.hasExceptionalOrbits
  have h_odd : Odd (D.o₀ p) := h_orbits.odd_o₀
  obtain ⟨hp_lt, h_nonsplit⟩ : D.IsSmallNonsplit p := hΛ.isSmallNonsplit
  obtain ⟨τ, hτ, hτl⟩ : ∃ τ ∈ D.aPlaces, inducedPlace τ = l := hΛ.induced_by_aPlace l hl
  set N : ℕ := orderOf (D.placeOfInt (-p) ^ D.o₀ p) with hN_def
  have hN : orderOf (D.placeOfInt (-p)) = D.o₀ p * N := by
    have h_dvd : D.o₀ p ∣ orderOf (D.placeOfInt (-p)) := orderOf_map_dvd _ _
    rw [hN_def, orderOf_pow_of_dvd h_odd.pos.ne' h_dvd, Nat.mul_div_cancel' h_dvd]
  have : NeZero N := .of_pos (orderOf_pos _)
  obtain ⟨t, ht_inj, ht_succ, ht_range⟩ : ∃ t : ZMod N → D.Φ, t.Injective ∧
      (∀ i : ZMod N, t (i + 1) = D.placeOfInt (-p ^ D.o₀ p) * t i) ∧
      ∀ σ : D.Φ, σ ∈ Set.range t ↔
        σ ∈ D.aPlaces ∧ (inducedPlace σ = l ∨ inducedPlace σ = star l) := by
    simpa only [hτl] using D.exists_orbit_of_mem_aPlaces hΛ.isExceptional.chiK_eq_neg_one h_odd hτ
  have ht_ind (i : ZMod N) : inducedPlace (t i) = l ∨ inducedPlace (t i) = star l :=
    ((ht_range _).1 ⟨i, rfl⟩).2
  obtain ⟨T, hT_p, hT_o₀, hT_even, hT_ι⟩ :
      ∃ T : FrobeniusCycle N (l.valuationSubringAtPrime D.E) embValRing,
        T.p = p ∧ T.frobExp = D.o₀ p ∧
        (∀ i : ZMod N, T.isEven i ↔ inducedPlace (t i) = l) ∧
        ∀ i : ZMod N, T.embedding i = letterEmbedding (t i) (ht_ind i) :=
    hΛ.exists_frobeniusCycle hl hN ht_succ ht_ind
  have h_nonunit : ¬IsUnit (T.p : embValRing) := by
    simpa only [hT_p] using not_isUnit_natCast_embValRing
  have hι (i : ZMod N) (x : l.valuationSubringAtPrime D.E) :
      T.embedding i x = (if T.isEven i then Φ (t i) else (Φ (t i)).comp (starRingEnd D.E)) x := by
    simp only [hT_ι, hT_even, coe_letterEmbedding, embeddingToward]
  have h_exponent : heckeScalingExponent l = D.a * #{i : ZMod N | T.isEven i} := by
    have h_image : {σ ∈ D.aPlaces | inducedPlace σ = l} = image t {i : ZMod N | T.isEven i} := by
      ext σ
      simp only [mem_filter, mem_image, mem_univ, true_and, hT_even]
      constructor
      · rintro ⟨hσ_top, hσ_ind⟩
        obtain ⟨i, rfl⟩ : σ ∈ Set.range t := (ht_range σ).2 ⟨hσ_top, .inl hσ_ind⟩
        exact ⟨i, hσ_ind, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨((ht_range (t i)).1 ⟨i, rfl⟩).1, hi⟩
    rw [heckeScalingExponent, h_image, card_image_of_injective _ ht_inj]
  have hfrobExp_pos : 0 < T.frobExp := h_odd.pos.trans_eq hT_o₀.symm
  have hfrobExp_le : T.frobExp ≤ D.ceilLogLifts T.p := by
    simpa only [hT_o₀, hT_p] using h_orbits.o₀_le_ceilLogLifts
  have h_large : T.IsLargeDegree D.k D.a (D.ceilLogLifts p) (1 / (D.m ^ 2 * D.f)) := by
    have hm : D.m ≤ T.frobExp * N :=
      (le_of_dvd (orderOf_pos _) h_orbits.m_dvd_orderOf).trans_eq (by rw [hN, hT_o₀])
    have h13 : 13 ≤ p := P.thirteen_le_of_chiK_ne_one Fact.out h_nonsplit
    rw [← hT_p] at h13 hp_lt
    simpa only [hT_p] using
      D.isLargeDegree_of_le_card T h13 hp_lt hfrobExp_pos hfrobExp_le orderOf_le_card_univ hm
  have h_cost : 3 * T.divisorConstant D.k D.a (D.ceilLogLifts p) ≤
      12 * D.heckeScalingExponent l / (D.m * p) := by
    simpa only [hT_p, h_exponent] using
      D.three_mul_divisorConstant_le T hfrobExp_pos hfrobExp_le T.card_isEven_add_self
  -- The constant of the Frobenius cycle is at most the stated one.
  obtain ⟨h_stable, i, hi, h_index⟩ :
      IsOntoUpToColength (p : embValRing) D.integralSourceForms j₀ (hΛ.scaledHeckeOperator ⟨l, hl⟩)
        ((3 * T.divisorConstant D.k D.a (D.ceilLogLifts p) + 1 / (D.m ^ 2 * D.f) * j₀) *
          finrank ℂ D.SourceForm) := by
    simpa only [hT_p] using Columns.isOntoUpToColength_scaledHeckeOperator_of_frobeniusCycle hΛ hl
      l.valuationSubringAtPrime_eq_valuationSubring T h_nonunit hT_p (.ofInjective t ht_inj)
      ht_range hι h_exponent h_large j₀
  exact ⟨h_stable, i, hi.trans (by grw [h_cost]), h_index⟩

end New.Data
