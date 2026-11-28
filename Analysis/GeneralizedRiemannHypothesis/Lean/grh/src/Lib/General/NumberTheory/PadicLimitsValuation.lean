import Lib.GaloisRep.Main.SelmerModules
import Lib.General.Geometry.GaloisCovers
import Lib.General.NumberTheory.CoefficientRings

/-!
# Algebraicity from ℓ-adic bounds, roots of unity as limits, and the ℓ-adic valuation

This file proves three groups of facts. `New.isAlgebraic_of_norm_complexToCp_le` shows that a
complex number that stays ℓ-adically bounded under all isomorphisms ℂ ≅ ℚ̄_ℓ, for one prime ℓ, is
algebraic. The second section approximates the roots of unity ζ in ℂ_p with ζ^{q_p} = ζ by images of
integers of K = ℚ(√−d); the third collects properties of the ℓ-adic valuation and of coefficient
rings.

* `quadInt d` is the ring of integers of K inside ℂ, and a `PadicPlace p` fixes a map ιₚ : ℂ → ℂ_p.
* `primeNorm d p` is the number q_p, equal to p² if the Legendre symbol `chiK d p` = (p/d) is −1 and
  to p otherwise.
* v = `New.ellVal` is the normalised valuation on ℚ̄_ℓ = `PadicAlgCl ℓ`, truncated to 0 on elements
  of norm at least 1, so that its values lie in [0, ∞].
* O denotes a ring in `New.CoeffRing ℓ`: the ring of integers of a finite Galois extension of ℚ_ℓ
  inside ℚ̄_ℓ. `ThePrime ℓ` says that ℓ is prime.

## Main definitions and results

* `New.mem_normPairClosure_of_pow_eq`: an element `ζ` of `ℂ_p` of norm 1 with `ζ ^ q_p = ζ` is a
  limit of images of integers `α` of `K`, in such a way that the image of `α ᾱ` tends to
  `ζ ^ (p + 1)`.
* `New.CoeffRing.normLength`, `New.CoeffRing.normLength_addVal`: the rescaling of lengths of
  O-modules that sends the additive valuation of x to v(x), so that they become comparable for
  different O.
* `New.CoeffRing.eventually_exists_isPrimitiveRoot`: all large O hold a primitive k-th root of
  unity.

## Relation to the literature

Known result: Teichmüller representatives as limits of powers. Source: Serre, Local Fields, Chapter
II.
-/

/-!
## An ℓ-adic criterion for algebraicity of complex numbers

A transcendental number can be sent to any transcendental element of `PadicAlgCl ℓ` by
`New.exists_ringEquiv_extend`, and these elements have unbounded norm.
-/

/-- Let `ℓ` be a prime. If the `ℓ`-adic norms of the images of `x : ℂ` under all field isomorphisms
`ι` from `ℂ` onto the algebraic closure of `ℚ_ℓ` have a common bound `c`, then `x` is algebraic over
`ℚ`. The norm is taken in `ℂ_[ℓ]`: `complexToCp ι` is `ι` followed by the isometric embedding into
`ℂ_[ℓ]`. -/
lemma New.isAlgebraic_of_norm_complexToCp_le {ℓ : ℕ} [Fact ℓ.Prime] {x : ℂ} {c : ℝ}
    (h_bound : ∀ ι : ℂ ≃+* PadicAlgCl ℓ, ‖complexToCp (p := ℓ) ι x‖ ≤ c) : IsAlgebraic ℚ x := by
  by_contra hx
  -- The elements algebraic over `ℚ` are countable, so the others are dense; take one of norm `> c`.
  obtain ⟨y, hy, hcy⟩ : ∃ y : PadicAlgCl ℓ, ¬IsAlgebraic ℚ y ∧ c < ‖y‖ :=
    ((Algebraic.countable ℚ (PadicAlgCl ℓ)).dense_compl ℚ_[ℓ]).exists_mem_open
      (isOpen_Ioi.preimage continuous_norm) (NormedField.exists_lt_norm _ c)
  -- Evaluation at `x` and at `y` embed the countable ring `ℚ[X]` in two algebraically closed fields
  -- of the same uncountable cardinality; an isomorphism `ι` matching them sends `x` to `y`.
  have : Countable (Polynomial ℚ) := (Polynomial.basisMonomials ℚ).repr.injective.countable
  rw [isAlgebraic_iff_not_injective, not_not] at hx hy
  obtain ⟨ι, hι⟩ : ∃ ι : ℂ ≃+* PadicAlgCl ℓ, ∀ P : Polynomial ℚ,
      ι (Polynomial.aeval x P) = Polynomial.aeval y P :=
    exists_ringEquiv_extend mk_complex_eq_mk_padicAlgCl _ _ hx hy
  exact hcy.not_ge (by simpa [show ι x = y by simpa using hι .X] using h_bound ι)

namespace New

/-!
## Roots of unity as limits of integers of `K`

Proof idea: lift the residue of `ζ` to an integer `a` of `K` and take the powers `a ^ q_p ^ n`.
-/

section TeichmullerLimits

open NumberField Complex IsLocalRing PadicInt QuadField AddChar ComplexConjugate
variable {p : ℕ} [hp : Fact p.Prime]

/-- The residue field of the valuation ring of `ℂ_[p]` has characteristic `p`, since `‖p‖ < 1`. -/
instance : CharP (ResidueField (valRingCp p)) p := by
  refine (CharP.charP_iff_prime_eq_zero hp.out).2 (residue_eq_iff_valuation_sub_lt_one.2 ?_)
  change ‖(p : valRingCp p).val - 0‖₊ < 1
  simpa [← NNReal.coe_lt_coe] using norm_p_lt_one

/-- If `‖u - 1‖ < 1` in `ℂ_p` and `p ∣ q`, then `u ^ q ^ n` tends to `1` as `n → ∞`. -/
lemma tendsto_pow_pow_of_norm_sub_one_lt {u : ℂ_[p]} (hu : ‖u - 1‖ < 1) {q : ℕ} (hq : p ∣ q) :
    Filter.Tendsto (fun n : ℕ ↦ u ^ q ^ n) Filter.atTop (nhds 1) := by
  -- `k ↦ u ^ k` extends to a continuous character `κ` of `ℤ_p`, the one attached to `u - 1`,
  -- and `q ^ n → 0` in `ℤ_p`. The correspondence needs a bounded action of `ℤ_p` on `ℂ_p`.
  let alg : Algebra ℤ_[p] ℂ_[p] := .compHom _ Coe.ringHom
  let _ : SMul ℤ_[p] ℂ_[p] := alg.toSMul
  have : IsBoundedSMul ℤ_[p] ℂ_[p] :=
    ⟨fun a ↦ dist_smul_pair a.val, fun a b ↦ dist_pair_smul a.val b.val⟩
  let κ : {κ : AddChar ℤ_[p] ℂ_[p] // Continuous κ} :=
    (continuousAddCharEquiv_of_norm_mul p ℂ_[p]).symm ⟨u - 1, hu⟩
  have hκ (k : ℕ) : κ.val k = u ^ k := by simpa [κ] using κ.val.map_nsmul_eq_pow k 1
  -- by continuity, `κ (q ^ n) → κ 0 = 1`, as `q ^ n → 0`
  simpa [Function.comp_def, ← hκ] using (κ.prop.tendsto 0).comp
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (norm_natCast_lt_one_iff.mpr hq))

/-- If `x` and `y` in the valuation ring of `ℂ_p` have the same residue, `‖y‖ = 1`, `p ∣ q` and
`y ^ q ^ n = y` for all `n`, then `x ^ q ^ n` tends to `y`. -/
lemma tendsto_pow_pow_of_residue_eq {q : ℕ} (hq : p ∣ q) {x y : valRingCp p}
    (hxy : residue (valRingCp p) x = residue (valRingCp p) y) (hy : ‖y.val‖ = 1)
    (hy_fixed : ∀ n : ℕ, y.val ^ q ^ n = y.val) :
    Filter.Tendsto (fun n : ℕ ↦ x.val ^ q ^ n) Filter.atTop (nhds y.val) := by
  have hy_ne : y.val ≠ 0 := norm_pos_iff.1 (one_pos.trans_eq hy.symm)
  have h_sub : ‖x.val - y.val‖ < 1 := residue_eq_iff_valuation_sub_lt_one.1 hxy
  have h_div : ‖x.val / y.val - 1‖ < 1 := by simpa [div_sub_one hy_ne, hy] using h_sub
  simpa [div_pow, hy_fixed, hy_ne] using
    (tendsto_pow_pow_of_norm_sub_one_lt h_div hq).mul_const y.val

variable (d : ℕ) [PrimeSevenModEight d]

lemma I_mul_sqrt_mem_quadInt : I * √d ∈ quadInt d := ⟨sqrtNegDInt d, by simp [two_mul]⟩

/-- Let `p` be a prime, `d` a prime congruent to 7 modulo 8, and let `φ` map the integers of
`K = ℚ(√-d)` to a field of characteristic `p`. An element `z` with `z ^ q_p = z`, where
`q_p = primeNorm d p` is `p ^ 2` if the Legendre symbol `chiK d p = (p/d)` is `-1` and `p`
otherwise, is the image of an integer whose conjugate has the image `z ^ p`. -/
lemma QuadField.exists_map_eq_and_map_star_eq_pow {k : Type*} [Field k] [CharP k p]
    (φ : 𝓞 (QuadField d) →+* k) (z : k) (hz_pow : z ^ primeNorm d p = z) :
    ∃ a : 𝓞 (QuadField d), φ a = z ∧ φ (star a) = z ^ p := by
  -- The fixed points of Frobenius lie in the prime field, so they are images of integers.
  have prime_field (x : k) (hx : frobenius k p x = x) : ∃ n : ℤ, n = x :=
    (mem_bot_iff_intCast p k).1 ((Subfield.mem_bot_iff_pow_eq_self _ p).2 hx)
  rw [← frobenius_def]
  obtain h_not_inert | h_inert := em' (chiK d p = -1)
  · -- `q_p = p`: Frobenius fixes `z`, so a rational integer will do.
    obtain ⟨n, rfl⟩ := prime_field z (by simpa [h_not_inert, frobenius_def] using hz_pow)
    exact ⟨n, by simp⟩
  -- `q_p = p²`: Frobenius applied twice fixes `z`, and it acts as conjugation on `e = φ betaK`,
  -- where `betaK = (1 + √-d) / 2`. We write `z = m + n e` with `m`, `n` fixed by Frobenius and take
  -- `a = m + n betaK`.
  have hp_ne_two : p ≠ 2 := fun h_two ↦ by simp [h_two, chiK_two] at h_inert
  have hz : frobenius k p (frobenius k p z) = z := by
    simpa [h_inert, frobenius_def, sq, pow_mul] using hz_pow
  have he : frobenius k p (φ (betaK d)) = 1 - φ (betaK d) := by
    rw [frobenius_def, ← pow_one p, eq_comm, eq_map_betaK_pow_iff hp_ne_two, h_inert,
      show φ (sqrtNegDInt d) = 2 * φ (betaK d) - 1 by simp [map_ofNat]]
    ring
  -- `2 e - 1`, a square root of `-d`, has the `(p - 1)`-st power `-1`, so it is not `0`.
  have hδ_ne : 2 * φ (betaK d) - 1 ≠ 0 := fun h_zero ↦ by
    simpa [h_inert, h_zero, map_ofNat, Nat.sub_ne_zero_of_lt hp.out.one_lt]
      using chiK_eq_pow_of_sq_eq_neg hp_ne_two (map_sqrtNegDInt_sq φ)
  -- Frobenius negates both `z - z ^ p` and `2 e - 1`, so it fixes their quotient `n`.
  have hδ_frob : frobenius k p (2 * φ (betaK d) - 1) = -(2 * φ (betaK d) - 1) := by
    rw [map_sub, map_mul, map_one, he, map_ofNat]
    ring
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = (z - frobenius k p z) / (2 * φ (betaK d) - 1) :=
    prime_field _ (by rw [map_div₀, map_sub, hz, hδ_frob, div_neg, ← neg_div, neg_sub])
  rw [eq_div_iff hδ_ne] at hn
  -- Frobenius sends `z - n e` to `z ^ p - n (1 - e)`, and `z - z ^ p = n (2 e - 1)`.
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = z - n * φ (betaK d) := prime_field _ <| by
    rw [map_sub, map_mul, map_intCast, he]
    linear_combination hn
  -- Frobenius sends `z` to `z - n (2 e - 1)`, which is `m + n (1 - e)`, the image of `star a`.
  have h_frob_z : frobenius k p z = m + n * (1 - φ (betaK d)) := by linear_combination hn - hm
  exact ⟨m + n * betaK d, by simp [hm], by simp [h_frob_z, star_add, star_mul']⟩

variable [PadicPlace p]

omit [PrimeSevenModEight d] in
lemma map_I_mul_sqrt_sq : ιₚ (I * √d) ^ 2 = -d := by
  simpa using congrArg (fun w : QuadField d ↦ ιₚ (w : ℂ)) (sqrtNegD_sq d)

/-- The closure in `ℂ_p²` of the set of images under `ιₚ` of the pairs `(α, α ᾱ)`, with `α` an
integer of `K = ℚ(√-d)`. -/
def normPairClosure : Set (ℂ_[p] × ℂ_[p]) := closure {(ιₚ a, ιₚ (a * conj a)) | a ∈ quadInt d}

/-- If `ζ` is an element of `ℂ_p` of norm `1` with `ζ ^ q_p = ζ`, where `q_p = primeNorm d p`
(`p ^ 2` if `chiK d p = -1`, else `p`), then `(ζ, ζ ^ (p + 1))` lies in `normPairClosure d`: it is a
limit of images under `ιₚ` of pairs `(α, α ᾱ)` with `α` an integer of `K = ℚ(√-d)`. -/
lemma mem_normPairClosure_of_pow_eq {ζ : ℂ_[p]} (hζ_norm : ‖ζ‖ = 1)
    (hζ_pow : ζ ^ primeNorm d p = ζ) : (ζ, ζ ^ (p + 1)) ∈ normPairClosure d := by
  -- Lift the residue of `ζ` to an integer `a` of `K` whose conjugate lifts that of `ζ ^ p`.
  -- With `q = q_p`, the powers `a ^ q ^ n` tend to `ζ` and their conjugates to `ζ ^ p`.
  let φ : 𝓞 (QuadField d) →+* valRingCp p :=
    ((ιₚ.domRestrict (QuadField d)).comp (algebraMap _ _)).codRestrict (valRingCp p)
      (norm_ringOfIntegers_le (ιₚ.domRestrict (QuadField d)))
  let z : valRingCp p := ⟨ζ, hζ_norm.le⟩
  obtain ⟨a, ha, ha_star⟩ : ∃ a : 𝓞 (QuadField d),
      residue (valRingCp p) (φ a) = residue (valRingCp p) z ∧
      residue (valRingCp p) (φ (star a)) = residue (valRingCp p) z ^ p :=
    exists_map_eq_and_map_star_eq_pow d ((residue (valRingCp p)).comp φ) _
      (by rw [← map_pow]; exact congrArg _ (Subtype.ext hζ_pow))
  set q : ℕ := primeNorm d p
  have hq : p ∣ q := by simp [q, apply_ite]
  have hζ_fixed (n : ℕ) : ζ ^ q ^ n = ζ := by
    simpa using Function.iterate_fixed (f := fun w : ℂ_[p] ↦ w ^ q) hζ_pow n
  have lim_a : Filter.Tendsto (fun n : ℕ ↦ (φ a).val ^ q ^ n) Filter.atTop (nhds ζ) :=
    tendsto_pow_pow_of_residue_eq hq ha hζ_norm hζ_fixed
  have lim_star : Filter.Tendsto (fun n : ℕ ↦ (φ (star a)).val ^ q ^ n) .atTop (nhds (ζ ^ p)) :=
    tendsto_pow_pow_of_residue_eq (y := z ^ p) hq ha_star (by simp [z, hζ_norm])
      (by simp [z, pow_right_comm _ p, hζ_fixed])
  -- The approximating integers are `b n = a ^ q ^ n`.
  let b : ℕ → ℂ := fun n ↦ ((a ^ q ^ n : 𝓞 (QuadField d)) : QuadField d)
  refine mem_closure_iff_seq_limit.2
    ⟨fun n ↦ (ιₚ (b n), ιₚ (b n * conj (b n))), fun n ↦ ⟨b n, ⟨a ^ q ^ n, rfl⟩, rfl⟩, ?_⟩
  simpa [b, φ, RingHom.codRestrict, pow_succ'] using lim_a.prodMk_nhds (lim_a.mul lim_star)

end TeichmullerLimits

/-!
## The normalised ℓ-adic valuation and normalised lengths

We have v(x) = −log_ℓ |x| for |x| ≤ 1, with v(ℓ) = 1 and v(0) = ∞, and v(x) = 0 for |x| ≥ 1.
By this truncation, v is in general only subadditive on products (`New.ellVal_mul_le`). Each O is an
instance of `New.PadicIntegerRing`; in particular O/x is finite for x ≠ 0.
-/

section Valuation

open IsDiscreteValuationRing Real ENNReal NeZero

variable {ℓ : ℕ} [ThePrime ℓ] {O : CoeffRing ℓ} {x y : PadicAlgCl ℓ} {c : NNReal}

/-! ### The valuation on ℚ̄_ℓ -/

/-- For `x`, `y` in ℚ̄_ℓ with `‖y‖ ≤ 1` and a real `c ≥ 0`, the inequality v(x) ≤ c + v(y) means
`ℓ ^ (-c) * ‖y‖ ≤ ‖x‖`, where v = `ellVal` is the normalised valuation. -/
lemma ellVal_le_add_iff (hy : ‖y‖ ≤ 1) :
    ellVal x ≤ c + ellVal y ↔ ℓ ^ (-c.toReal) * ‖y‖ ≤ ‖x‖ := by
  have hℓ : (1 : ℝ) < ℓ := mod_cast (Fact.out : ℓ.Prime).one_lt
  -- the cases `y = 0` and `x = 0` are immediate
  obtain rfl | hy_ne := eq_or_ne y 0
  · simp [ellVal]
  have hy_pos : 0 < ‖y‖ := norm_pos_iff.2 hy_ne
  obtain rfl | hx_ne := eq_or_ne x 0
  · simpa [ellVal, hy_ne] using (by positivity : 0 < (ℓ : ℝ) ^ (-c.toReal) * ‖y‖)
  -- away from `0`, take logarithms in base `ℓ`
  have hy_log : 0 ≤ -logb ℓ ‖y‖ := neg_nonneg.2 (logb_nonpos hℓ hy_pos.le hy)
  have h_val : ellVal x ≤ c + ellVal y ↔ -logb ℓ ‖x‖ ≤ c.toReal + -logb ℓ ‖y‖ := by
    simp [ellVal, hx_ne, hy_ne, ofReal_le_iff_le_toReal, toReal_add, toReal_ofReal hy_log]
  rw [h_val, ← le_div_iff₀ hy_pos, ← le_logb_iff_rpow_le hℓ (by positivity),
    logb_div (by simpa) hy_pos.ne']
  grind

/-- For `c ≥ 0`, the inequality v(x) ≤ c means `ℓ ^ (-c) ≤ ‖x‖`, where v = `ellVal`. -/
lemma ellVal_le_iff : ellVal x ≤ c ↔ ℓ ^ (-c.toReal) ≤ ‖x‖ := by
  simpa [ellVal] using ellVal_le_add_iff norm_one.le

/-- For `x`, `y` in `intQpBar ℓ`, the valuation ring of ℚ̄_ℓ, `x` divides `y` exactly if
v(x) ≤ v(y), where v = `ellVal` is the normalised valuation. -/
lemma Selmer.dvd_iff_ellVal_le {x y : intQpBar ℓ} : x ∣ y ↔ ellVal x.val ≤ ellVal y.val :=
  calc x ∣ y ↔ ‖y.val‖ ≤ ‖x.val‖ := (Valuation.integer.integers _).dvd_iff_le
    _ ↔ _ := by simpa using (ellVal_le_add_iff (x := x.val) (c := 0) y.prop).symm

/-- The valuation v = `ellVal` is antitone in the norm: if `‖y‖ ≤ ‖x‖`, then v(x) ≤ v(y). -/
lemma ellVal_le_ellVal (h_le : ‖y‖ ≤ ‖x‖) : ellVal x ≤ ellVal y := by
  obtain rfl | hy_ne := eq_or_ne y 0
  · simp [ellVal]
  have hy_pos : 0 < ‖y‖ := norm_pos_iff.2 hy_ne
  rw [ellVal, ellVal, ite_eq_right (hy_pos.trans_le h_le).ne', ite_eq_right hy_pos.ne']
  gcongr
  exact mod_cast (Fact.out : ℓ.Prime).one_lt

/-- The normalised valuation v = `ellVal` on ℚ̄_ℓ (v(x) is the positive part of −log_ℓ ‖x‖, and v(0)
= ∞) is subadditive on products: v(xy) ≤ v(x) + v(y). -/
lemma ellVal_mul_le : ellVal (x * y) ≤ ellVal x + ellVal y := by
  -- if a factor is `0`, the right side is `∞`
  obtain hx | hx := eq_or_ne ‖x‖ 0
  · simp [ellVal, hx]
  obtain hy | hy := eq_or_ne ‖y‖ 0
  · simp [ellVal, hy]
  -- for nonzero arguments this is subadditivity of the positive part, applied to logarithms
  rw [ellVal, ellVal, ellVal, norm_mul, ite_eq_right hx, ite_eq_right hy,
    ite_eq_right (mul_ne_zero hx hy), logb_mul hx hy, neg_add]
  exact ofReal_add_le

@[simp]
lemma ellVal_pow (k : ℕ) : ellVal (x ^ k) = k * ellVal x := by
  obtain rfl | hk := eq_or_ne k 0
  · simp [ellVal]
  obtain rfl | hx_ne := eq_or_ne x 0
  · simp [ellVal, hk]
  · simp [← mul_neg, ellVal, logb_pow, hx_ne]

/-- The normalised valuation of a nonzero natural number `n` in ℚ̄_ℓ is its ℓ-adic valuation. -/
lemma ellVal_natCast {n : ℕ} (hn : n ≠ 0) : ellVal (ℓ := ℓ) n = padicValNat ℓ n := by
  have h_norm : ‖(n : PadicAlgCl ℓ)‖ = ‖(n : ℚ_[ℓ])‖ := mod_cast PadicAlgCl.norm_extends ℓ n
  simp [hn, h_norm, Padic.norm_eq_zpow_neg_valuation, ellVal, logb_pow, Fact.out, NeZero.ne]

@[simp]
lemma ellVal_ell : ellVal (ℓ : PadicAlgCl ℓ) = 1 := by
  simp [norm_p_eq_inv, ellVal, NeZero.ne, Fact.out]

namespace CoeffRing

/-! ### Coefficient rings: units, lengths, roots of unity and finite quotients -/

lemma isUnit_iff_norm_eq_one (x : ↑O) : IsUnit x ↔ ‖x.val‖ = 1 := by
  simp [isUnit_iff_dvd_one, dvd_iff_norm_le, le_antisymm_iff]

variable (O) in
/-- A chosen uniformiser of the discrete valuation ring `O`. -/
protected noncomputable def uniformizer : ↑O := (exists_irreducible O).choose

variable (O) in
lemma irreducible_uniformizer : Irreducible O.uniformizer := (exists_irreducible O).choose_spec

/-- Normalised length: the additive map sending n to n·v(ϖ) and ∞ to ∞, where ϖ is the chosen
uniformiser `O.uniformizer` and v(ℓ) = 1. The value does not depend on the choice of ϖ
(`normLength_natCast_of_irreducible`). -/
noncomputable def normLength : ℕ∞ →+ ℝ≥0∞ :=
  AddMonoidHom.ENatMap
    { toFun n := n * (-logb ℓ ‖O.uniformizer.val‖).toNNReal
      map_zero' := by simp
      map_add' := by simp [add_mul] }

lemma normLength_top : O.normLength ⊤ = ∞ := rfl

/-- The normalised length of `n` is `-n log_ℓ ‖ϖ‖`, with `ϖ` the chosen uniformiser of `O`. -/
lemma normLength_natCast (n : ℕ) :
    O.normLength n = n * ENNReal.ofReal (-logb ℓ ‖O.uniformizer.val‖) := rfl

/-- Let `O` be a coefficient ring, the ring of integers of a finite Galois extension of ℚ_ℓ inside
ℚ̄_ℓ, with chosen uniformiser ϖ. For x ∈ O, let `addVal O x` be the number of factors of ϖ in x, and
let the normalised length `normLength` send n to n·v(ϖ) (and ∞ to ∞). Then the normalised length of
`addVal O x` equals v(x), where v = `ellVal` equals −log_ℓ|·| on elements of ℚ̄_ℓ of norm ≤ 1,
normalised by v(ℓ) = 1. -/
@[simp]
lemma normLength_addVal (x : ↑O) : O.normLength (addVal O x) = ellVal x.val := by
  have hϖ : Irreducible O.uniformizer := O.irreducible_uniformizer
  obtain rfl | hx := eq_or_ne x 0
  · simp [ellVal, normLength_top]
  -- `x = u * ϖ ^ n` with `‖u‖ = 1`, and both sides are `n` times the valuation of `ϖ`
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  have hu_norm : ‖(u : ↑O).val‖ = 1 := (isUnit_iff_norm_eq_one _).1 u.isUnit
  have h_ellVal : ellVal (u * O.uniformizer ^ n : ↑O).val =
      n * ENNReal.ofReal (-logb ℓ ‖O.uniformizer.val‖) := by
    simp [← mul_neg, hϖ.ne_zero, hu_norm, ellVal, logb_pow]
  rw [addVal_def' u hϖ n, h_ellVal, normLength_natCast]

/-- The normalised length of `n` is `n v(ϖ)` for every uniformiser `ϖ` of `O`, where v = `ellVal`
is the normalised valuation on ℚ̄_ℓ. -/
lemma normLength_natCast_of_irreducible {ϖ : ↑O} (hϖ : Irreducible ϖ) (n : ℕ) :
    O.normLength n = n * ellVal ϖ.val := by
  rw [← hϖ.addVal_pow n, normLength_addVal, SubmonoidClass.coe_pow, ellVal_pow]

@[simp]
lemma normLength_natCast_mul (k : ℕ) (g : ℕ∞) : O.normLength (k * g) = k * O.normLength g := by
  simp [← nsmul_eq_mul]

@[gcongr]
lemma normLength_mono : Monotone O.normLength := fun a b hab ↦ by
  obtain ⟨c, rfl⟩ := le_iff_exists_add.1 hab
  simp

/-- For `k ≠ 0`, all coefficient rings `O` (rings of integers of finite Galois extensions of ℚ_ℓ
inside ℚ̄_ℓ) that are sufficiently large with respect to inclusion contain a primitive `k`-th root
of unity. -/
lemma eventually_exists_isPrimitiveRoot (k : ℕ) [NeZero k] :
    ∀ᶠ O : CoeffRing ℓ in Filter.atTop, ∃ ζ : ↑O, IsPrimitiveRoot ζ k := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (PadicAlgCl ℓ) k
  -- a root of unity has norm `1`, so it lies in all large enough `O`
  filter_upwards [eventually_mem (hζ.isOfFinOrder (NeZero.ne k)).norm_eq_one.le] with O hO
  exact ⟨⟨ζ, hO⟩, .coe_submonoidClass_iff.1 hζ⟩

/-- A coefficient ring is an ℓ-adic integer ring; its quotients by nonzero ideals are finite, as
these ideals are open and the ring is compact. -/
noncomputable instance : PadicIntegerRing O ℓ where
  finiteQuotient hI := AddSubgroup.quotient_finite_of_isOpen _ (isOpen_iff.mpr hI)

end CoeffRing

end Valuation

end New
