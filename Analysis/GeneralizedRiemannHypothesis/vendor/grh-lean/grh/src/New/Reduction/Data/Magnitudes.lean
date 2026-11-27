import New.Reduction.Data.AdmissibleData

/-!
# Logarithmic bounds for the sizes of the data

The class `New.Data.HasLogBound D u F l` says `|F| ≤ exp l` for `u = true` (`New.Data.HasLogUpper`)
and `exp l ≤ F` for `u = false` (`New.Data.HasLogLower`). Instance search computes the exponent `l`
from the shape of `F`, and comparing exponents then proves inequalities between the numbers attached
to the data `D`. A table of the sizes is in `New.Reduction.Data.Sizes`.

## Main definitions and results

* `New.Data.HasLogBound.of_mem_Icc`: a quantity between two others inherits their exponents,
  weakened to a given one. `New.Data.HasLogBound.of_lower_of_upper` weakens the exponents of one
  quantity.
* `New.Data.lt_of_hasLogBound`, `New.Data.le_of_hasLogBound`, `New.Data.nat_lt_of_hasLogBound`,
  `New.Data.nat_le_of_hasLogBound`: an upper exponent of `F` below a lower exponent of `G` gives
  `F < G`, and so also `F ≤ G`. The comparison of exponents is a default argument, a linear problem
  in `log x`, `log x₁`, `log b`, `log log b`, `log log x₁` and `New.Parameters.constantBound` that
  `grind` decides from `New.Data.scale_inequalities`. So `D.le_of_hasLogBound` or
  `D.nat_le_of_hasLogBound` alone proves such an inequality.
* `New.Data.k_add_t_add_one_le_halfGap`: at the end, inequalities and parities of the ranks `m`,
  `k`, `r`, `t`, `n j` and of `halfGap`.

Notions from other files:
* `New.Data P`: the data for the parameters `P = (q₀, d)`, with `q₀` a modulus and `d` a prime,
  among them the scales `x`, `x₁`, `b` (`D.natX`, `D.natX₁`, `D.natB` as natural numbers) with their
  logarithms `logX`, `logX₁`, `logB`, the ranks `m`, `r`, the exponent `s = D.towerExp` with
  `2 ^ s = m ^ 22` and the primes `p₀`, `p₁` (`D.levelPrime`).
* `D.q₁ = q₀ * towerDeg s`: the order of the root of unity that generates the number field
  `E = P.E s` over `K = ℚ(√-d)`; `P.q₂ s = (q₀ d) ^ (s + 6)` is a multiple of `q₁ d`.
* `D.weight`: the weight at the places `D.Φ`; it is `b` on the set `D.bPlaces` of `b`-places and
  `offWeight = a / x₁` elsewhere, where `a = x b`.
-/

noncomputable section

open Real Set Finset Nat NeZero

namespace New.Data

variable {P : Parameters} (D : Data P) {F G l l' c : ℝ} {A B : ℕ} {u : Bool}

/-- A bound on the size of the real `F` on a logarithmic scale: the upper bound `|F| ≤ exp l` if `u`
is `true` (see `hasLogUpper_iff`), the lower bound `exp l ≤ F` if `u` is `false` (see
`hasLogLower_iff`). An instance for general `u` gives both bounds; the exponent `if u then a else b`
is `a` in the upper bound and `b` in the lower bound. The inequality does not depend on `D`; the
argument lets instances and default proofs use the data. -/
class HasLogBound (D : Data P) (u : Bool) (F : ℝ) (l : outParam ℝ) where
  /-- The upper bound `|F| ≤ exp l` if `u` is `true`, the lower bound `exp l ≤ F` otherwise. -/
  out : if u then |F| ≤ exp l else exp l ≤ F

/-- The constant `P.constantBound`, which bounds the constants that depend only on the parameters
`P` (a modulus `q₀ = P.q₀` and a prime `d = P.d`), is at least each of the four numbers `64`, `q₀`,
`d` and the totient `φ q₀`. -/
lemma le_constantBound :
    64 ≤ P.constantBound ∧
    P.q₀ ≤ P.constantBound ∧
    P.d ≤ P.constantBound ∧
    φ P.q₀ ≤ P.constantBound := by
  have hq₀ : (0 : ℝ) ≤ P.q₀ := P.q₀.cast_nonneg
  have hd : (64 : ℝ) < P.d := mod_cast P.sixty_four_lt_d
  have hφ : (φ P.q₀ : ℝ) ≤ P.q₀ := mod_cast totient_le P.q₀
  -- `P.constantBound` is `q₀ + 2 d + 6` plus nonnegative terms
  have h_le : P.q₀ + (2 * P.d + 6) ≤ P.constantBound := by
    have h_const : (0 : ℝ) ≤ P.vacuumBoundConst := P.vacuumBoundConst.cast_nonneg
    have h_sum : 0 ≤ ∑ w ∈ primitiveRoots P.q₀ ℂ,
        |Real.log ‖(Polynomial.cyclotomic P.q₀ ℂ).derivative.eval w‖| :=
      sum_nonneg fun w _ ↦ abs_nonneg _
    rw [Parameters.constantBound]
    linarith [abs_nonneg (chowlaSelbergConst P.d)]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The five inequalities between the scales of the data, as one statement. They say that
`10¹² P.constantBound ≤ log log b`, `(log b) ^ 100 ≤ x`, `x ^ 10⁶ ≤ x₁`, `x₁ ^ 10⁶ ≤ b` and
`(log x₁) ^ 6 ≤ log b`. -/
lemma scale_inequalities :
    1e12 * P.constantBound ≤ log D.logB ∧
    100 * log D.logB ≤ D.logX ∧
    1e6 * D.logX ≤ D.logX₁ ∧
    1e6 * D.logX₁ ≤ D.logB ∧
    6 * log D.logX₁ ≤ log D.logB :=
  ⟨D.constantBound_le, D.mul_log_logB_le_logX, D.logX_le_logX₁, D.logX₁_le_logB,
    D.log_logX₁_le_log_logB⟩

/-- As a real number, `D.a` is the product of the scales `D.x` and `D.b`. -/
lemma cast_a : (D.a : ℝ) = D.x * D.b := by
  rw [a, cast_mul, ← D.exp_logX, ← D.exp_logB]

/-- `q₁ x₁` divides `a = x b`. Here `x₁ = D.natX₁` is the second scale of the data and
`q₁ = D.q₁` is the order of the root of unity that generates the field `E` of the data over `K`. -/
lemma q₁_mul_natX₁_dvd_a : D.q₁ * D.natX₁ ∣ D.a := D.dvd_natB.mul_left D.natX

/-- The division in `offWeight = a / x₁` is exact, so `offWeight` is this quotient as a real
number. -/
lemma cast_offWeight : (D.offWeight : ℝ) = D.a / D.x₁ := by
  rw [offWeight, cast_div_charZero ((dvd_mul_left D.natX₁ D.q₁).trans D.q₁_mul_natX₁_dvd_a),
    ← D.exp_logX₁]

/-- The natural number `D.natB` is the scale `D.b` as a real number. -/
lemma cast_natB : (D.natB : ℝ) = D.b := D.exp_logB.symm

/-- At an infinite place `σ` of the number field `E` of the data (`D.Φ` is the type of these
places), the weight is `b` if `σ` lies in the set `D.bPlaces` of `b`-places and
`offWeight = a / x₁` otherwise. -/
lemma weight_eq_ite (σ : D.Φ) : D.weight σ = if σ ∈ D.bPlaces then D.natB else D.offWeight :=
  D.weight_eq σ

/-- Let `σ` be an infinite place of the number field `E` of the data, let `x`, `x₁`, `b` be the
three scales of the data and `a = x b`. As a real number, the weight of `σ` is `a / x` if `σ` lies
in the chosen set `D.bPlaces` of places, the `b`-places, and `a / x₁` otherwise. -/
lemma cast_weight (σ : D.Φ) : (D.weight σ : ℝ) = D.a / if σ ∈ D.bPlaces then D.x else D.x₁ := by
  rw [weight_eq_ite]
  split
  · rw [cast_natB, cast_a, mul_div_cancel_left₀ _ (exp_ne_zero _)]
  · exact D.cast_offWeight

/-- Every weight `D.weight σ` is at most `D.natB + D.offWeight`, the sum of its two possible values:
`D.natB` (the scale `b` as a natural number) and `D.offWeight`. -/
lemma weight_le_natB_add_offWeight (σ : D.Φ) : D.weight σ ≤ D.natB + D.offWeight := by
  rw [weight_eq_ite]
  split <;> omega

/-- The weight `D.weight σ` of an infinite place `σ` of the number field `E` of the data is a
multiple of `q₁ = D.q₁`, the order of the root of unity that generates `E` over the imaginary
quadratic field `K = ℚ(√-d)`. -/
lemma q₁_dvd_weight (σ : D.Φ) : D.q₁ ∣ D.weight σ := by
  rw [weight_eq_ite]
  split
  · exact (dvd_mul_right D.q₁ D.natX₁).trans D.dvd_natB
  · exact Nat.dvd_div_of_mul_dvd ((mul_comm D.natX₁ D.q₁).dvd.trans D.q₁_mul_natX₁_dvd_a)

/-- Let `σ` be an infinite place of the number field `E` of the data and `κ(σ) = D.weight σ` the
natural number that the data assign to it. The number `D.liftWeight j σ`, the weight at `σ` of the
character used in step `j` of the chain of theta lifts, is `κ(σ) + j Δ + Δ / 2`, where
`Δ = D.gap = 2 r ^ 8` and `Δ / 2 = D.halfGap`. -/
lemma liftWeight_eq (j : ℕ) (σ : D.Φ) : D.liftWeight j σ = D.weight σ + j * D.gap + D.halfGap := by
  rw [liftWeight, shiftedWeight, gap]
  ring

/-- The primes `p₀ = D.levelPrime 0`, `p₁ = D.levelPrime 1` are `≡ 1` modulo `q₁ d`. Here `q₀` and
`d` are the modulus and the prime of the parameters `P`, `s = D.towerExp` is the exponent of the
data with `2 ^ s = m ^ 22`, and `q₁ = P.q₁ s` is `q₀ * 3 ^ (Nat.log 3 s + 5) * 2 ^ s`. -/
lemma levelPrime_modEq_one (i : Fin 2) : D.levelPrime i ≡ 1 [MOD P.q₁ D.towerExp * P.d] :=
  (D.levelPrime_modEq_one_q₂_sq i).of_dvd (Parameters.q₁_mul_d_dvd_q₂.pow two_ne_zero)

/-- For the exponent `s = D.towerExp` of the data, the square of `P.q₂ s = (q₀ d) ^ (s + 6)`
divides `p₀ - 1` and `p₁ - 1`, where `p₀`, `p₁` are the primes `D.levelPrime i`. -/
lemma dvd_levelPrime_sub_one (i : Fin 2) : P.q₂ D.towerExp ^ 2 ∣ D.levelPrime i - 1 :=
  (Nat.modEq_iff_dvd' (D.levelPrime_prime i).one_le).1 (D.levelPrime_modEq_one_q₂_sq i).symm

/-- The rank `r` is odd, since it is a power of `3`. -/
lemma r_odd : Odd D.r := by
  obtain ⟨e, hr⟩ : ∃ e : ℕ, D.r = 3 ^ (e + 1) := D.exists_r_eq_three_pow
  rw [hr]
  exact Odd.pow (by decide)

/-- The rank `m` is even, since it is a power of `2` with positive exponent. -/
lemma m_even : Even D.m := by
  obtain ⟨e, hm, -⟩ : ∃ e : ℕ, D.m = 2 ^ (e + 1) ∧ D.towerExp = (e + 1) * 22 :=
    D.exists_m_eq_two_pow
  simp [hm, parity_simps]

attribute [grind! .] le_constantBound r_odd m_even

/-! ### Upper and lower bounds, and the rules for arithmetic operations -/

/-- The upper bound `|F| ≤ exp l`; see `hasLogUpper_iff`. -/
abbrev HasLogUpper : ℝ → outParam ℝ → Prop := D.HasLogBound true

/-- The lower bound `exp l ≤ F`; see `hasLogLower_iff`. -/
abbrev HasLogLower : ℝ → outParam ℝ → Prop := D.HasLogBound false

/-- `l` is an upper exponent of `F` if and only if `|F| ≤ exp l`. -/
lemma hasLogUpper_iff : D.HasLogUpper F l ↔ |F| ≤ exp l :=
  ⟨fun h ↦ h.out, fun h ↦ ⟨h⟩⟩

/-- `l` is a lower exponent of `F` if and only if `exp l ≤ F`. -/
lemma hasLogLower_iff : D.HasLogLower F l ↔ exp l ≤ F :=
  ⟨fun h ↦ h.out, fun h ↦ ⟨h⟩⟩

/-- A number with a lower bound `exp l` is positive. -/
lemma HasLogBound.pos [D.HasLogLower F l] : 0 < F :=
  (exp_pos l).trans_le (D.hasLogLower_iff.1 inferInstance)

section

variable {D}

/-- Let `G ≤ F ≤ H` with `exp l ≤ G` and `|H| ≤ exp l'`. The Boolean `u` selects the bound. If `u`
is `true` and `l' ≤ c`, then `c` is an upper exponent of `F`. If `u` is `false` and `c ≤ l`, then
`c` is a lower exponent of `F`. -/
lemma HasLogBound.of_mem_Icc {F l l' c : ℝ} {u : Bool} (G H : ℝ)
    [D.HasLogLower G l] [D.HasLogUpper H l']
    (h_mem : F ∈ Set.Icc G H) (h_exp : if u then l' ≤ c else c ≤ l) :
    HasLogBound D u F c := by
  obtain ⟨hG, hH⟩ : G ≤ F ∧ F ≤ H := h_mem
  have h_lower : exp l ≤ F := (D.hasLogLower_iff.1 inferInstance).trans hG
  have h_upper : F ≤ exp l' :=
    hH.trans ((le_abs_self H).trans (D.hasLogUpper_iff.1 inferInstance))
  cases u
  · exact D.hasLogLower_iff.2 ((exp_le_exp.2 h_exp).trans h_lower)
  · have h_abs : |F| = F := abs_of_pos ((exp_pos l).trans_le h_lower)
    exact D.hasLogUpper_iff.2 (h_abs.trans_le (h_upper.trans (exp_le_exp.2 h_exp)))

/-- Let `exp l ≤ F` and `|F| ≤ exp l'`. If `u` is `true` and `l' ≤ c`, then `|F| ≤ exp c`. If `u` is
`false` and `c ≤ l`, then `exp c ≤ F`. -/
lemma HasLogBound.of_lower_of_upper {F l l' c : ℝ} {u : Bool}
    [D.HasLogLower F l] [D.HasLogUpper F l']
    (h_exp : if u then l' ≤ c else c ≤ l) : HasLogBound D u F c :=
  .of_mem_Icc F F ⟨le_rfl, le_rfl⟩ h_exp


/-- A non-zero natural number `A` lies between `exp 0` and `exp A`. -/
instance (priority := low) hasLogBound_natCast [NeZero A] :
    HasLogBound D u A (if u then A else 0) := by
  cases u
  · refine D.hasLogLower_iff.2 ?_
    simpa using NeZero.one_le (n := A)
  · refine D.hasLogUpper_iff.2 ?_
    have h_le : (A : ℝ) + 1 ≤ exp A := add_one_le_exp A
    rw [abs_of_nonneg A.cast_nonneg, ite_eq_left rfl]
    linarith

/-- A numeral `A ≥ 2` lies between `exp 0` and `exp A`. -/
instance (priority := low) [A.AtLeastTwo] : HasLogBound D u ofNat(A) (if u then ofNat(A) else 0) :=
  hasLogBound_natCast

/-- The exponent of `1` is `0`, in both directions. -/
instance : HasLogBound D u 1 0 := ⟨by cases u <;> simp⟩

/-- The exponent of `exp c` is `c`, in both directions. -/
instance : HasLogBound D u (Real.exp c) c := ⟨by cases u <;> simp⟩

variable [HasLogBound D u F l]

/-- Exponents are multiplied by `A` under taking `A`-th powers. -/
instance : HasLogBound D u (F ^ A) (A * l) := by
  cases u
  · refine D.hasLogLower_iff.2 ?_
    rw [exp_nat_mul]
    exact pow_le_pow_left₀ (exp_pos l).le (D.hasLogLower_iff.1 inferInstance) A
  · refine D.hasLogUpper_iff.2 ?_
    rw [exp_nat_mul, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg F) (D.hasLogUpper_iff.1 inferInstance) A

/-- Exponents are halved under taking square roots. -/
instance : HasLogBound D u √F (l / 2) := by
  cases u
  · refine D.hasLogLower_iff.2 ?_
    rw [exp_half]
    exact sqrt_le_sqrt (D.hasLogLower_iff.1 inferInstance)
  · refine D.hasLogUpper_iff.2 ?_
    rw [exp_half, abs_of_nonneg (sqrt_nonneg F)]
    exact sqrt_le_sqrt ((le_abs_self F).trans (D.hasLogUpper_iff.1 inferInstance))

variable [HasLogBound D u G l']

/-- Exponents of the same kind add under products: if `l` is an exponent of `F` and `l'` one of `G`,
then `l + l'` is an exponent of `F * G`. -/
instance hasLogBound_mul : HasLogBound D u (F * G) (l + l') := by
  cases u
  · have hF : exp l ≤ F := D.hasLogLower_iff.1 inferInstance
    have hG : exp l' ≤ G := D.hasLogLower_iff.1 inferInstance
    refine D.hasLogLower_iff.2 ?_
    rw [exp_add]
    exact mul_le_mul hF hG (exp_pos l').le ((exp_pos l).le.trans hF)
  · have hF : |F| ≤ exp l := D.hasLogUpper_iff.1 inferInstance
    have hG : |G| ≤ exp l' := D.hasLogUpper_iff.1 inferInstance
    refine D.hasLogUpper_iff.2 ?_
    rw [exp_add, abs_mul]
    exact mul_le_mul hF hG (abs_nonneg G) (exp_pos l).le

/-- For sums, the larger of the two exponents is a lower exponent of `F + G`, and that exponent plus
`1` is an upper exponent of `F + G`. -/
instance hasLogBound_add : HasLogBound D u (F + G) (max l l' + if u then 1 else 0) := by
  cases u
  · have hF : exp l ≤ F := D.hasLogLower_iff.1 inferInstance
    have hG : exp l' ≤ G := D.hasLogLower_iff.1 inferInstance
    refine D.hasLogLower_iff.2 ?_
    simp only [Bool.false_eq_true, ite_false, add_zero]
    calc exp (max l l') = max (exp l) (exp l') := exp_monotone.map_max
      _ ≤ exp l + exp l' := max_le_add_of_nonneg (exp_pos l).le (exp_pos l').le
      _ ≤ F + G := add_le_add hF hG
  · have hF : |F| ≤ exp l := D.hasLogUpper_iff.1 inferInstance
    have hG : |G| ≤ exp l' := D.hasLogUpper_iff.1 inferInstance
    refine D.hasLogUpper_iff.2 ?_
    simp only [ite_true]
    calc |F + G| ≤ |F| + |G| := abs_add_le F G
      _ ≤ exp (max l l') + exp (max l l') :=
        add_le_add (hF.trans (exp_le_exp.2 (le_max_left l l')))
          (hG.trans (exp_le_exp.2 (le_max_right l l')))
      _ = exp (max l l') * 2 := (mul_two _).symm
      _ ≤ exp (max l l') * exp 1 := by gcongr; exact exp_one_gt_two.le
      _ = exp (max l l' + 1) := (exp_add (max l l') 1).symm

/-- The negative of a lower exponent of `F` is an upper exponent of `F⁻¹`. -/
instance [D.HasLogLower F l] : D.HasLogUpper F⁻¹ (-l) := by
  refine D.hasLogUpper_iff.2 ?_
  rw [abs_of_pos (inv_pos.2 (HasLogBound.pos D)), exp_neg]
  exact inv_anti₀ (exp_pos l) (D.hasLogLower_iff.1 inferInstance)

/-- The negative of an upper exponent of a positive `F` is a lower exponent of `F⁻¹`. -/
instance [D.HasLogUpper F l] [D.HasLogLower F l'] : D.HasLogLower F⁻¹ (-l) := by
  refine D.hasLogLower_iff.2 ?_
  rw [exp_neg]
  exact inv_anti₀ (HasLogBound.pos D) ((le_abs_self F).trans (D.hasLogUpper_iff.1 inferInstance))

/-- An exponent of `F` plus one of `G⁻¹` is one of `F / G`. -/
instance [HasLogBound D u G⁻¹ l'] : HasLogBound D u (F / G) (l + l') := hasLogBound_mul

/-- An exponent of the real product of `A` and `B` is one of the cast of `A * B`. -/
instance [HasLogBound D u (A * B) l] : HasLogBound D u ↑(A * B) l := by simpa

/-- An exponent of the real sum of `A` and `B` is one of the cast of `A + B`. -/
instance [HasLogBound D u (A + B) l] : HasLogBound D u ↑(A + B) l := by simpa

/-- An exponent of the real power `A ^ B` is one of the cast of `A ^ B`. -/
instance [HasLogBound D u (A ^ B) l] : HasLogBound D u ↑(A ^ B) l := by simpa

/-- Let `l` be an exponent of `F` of kind `u` (the instance `HasLogBound D u F l` among the
variables) and `c` an upper exponent of `|F| + 1`. Then `⌈F⌉₊` has the upper exponent `c` if `u` is
`true`, and the lower exponent `l` otherwise. -/
instance [D.HasLogUpper (|F| + 1) c] : HasLogBound D u ⌈F⌉₊ (if u then c else l) := by
  grind [HasLogBound, one_le_cast, ceil_lt_add_one, le_ceil, ceil_eq_zero]

/-- `log b` has the exponent `log log b`, in both directions. -/
instance : HasLogBound D u D.logB (Real.log D.logB) := by
  grind [D.scale_inequalities, HasLogBound, exp_log]

/-- `log x₁` has the exponent `log log x₁`, in both directions. -/
instance : HasLogBound D u D.logX₁ (Real.log D.logX₁) := by
  grind [D.scale_inequalities, HasLogBound, exp_log]

/-- The exponent `s = D.towerExp`, which satisfies `2 ^ s = m ^ 22`, is at most `log x₁`, since
`s ≤ 32 log x` and `10⁶ log x ≤ log x₁`. -/
instance : D.HasLogUpper D.towerExp (Real.log D.logX₁) := by
  grind [D.scale_inequalities, HasLogBound, exp_log, towerExp_le]

/-- If `|F| ≤ exp l` and `|G| ≤ F`, then `|G| ≤ exp l`: an upper exponent of `F` is one of `G`. -/
lemma hasLogUpper_of_abs_le [D.HasLogUpper F l] (hGF : |G| ≤ F) : D.HasLogUpper G l :=
  D.hasLogUpper_iff.2 (hGF.trans ((le_abs_self F).trans (D.hasLogUpper_iff.1 inferInstance)))

/-- If `|F| ≤ exp l` and `0 ≤ G ≤ F`, then `|G| ≤ exp l`: an upper exponent of `F` is one of
`G`. -/
lemma hasLogUpper_of_le_of_nonneg [D.HasLogUpper F l] (hGF : G ≤ F) (hG : 0 ≤ G) :
    D.HasLogUpper G l :=
  hasLogUpper_of_abs_le ((abs_of_nonneg hG).trans_le hGF)

/-- An upper exponent of `F` is one of `|F|`. -/
instance [D.HasLogUpper F l] : D.HasLogUpper |F| l := by grind [HasLogBound]

/-- The larger of the upper exponents of `F` and `G`, plus `1`, is an upper exponent of `F - G`. -/
instance [D.HasLogUpper F l] [D.HasLogUpper G l'] : D.HasLogUpper (F - G) (max l l' + 1) :=
  hasLogUpper_of_abs_le (abs_sub F G)

/-- If `exp l' ≤ F ≤ exp l`, then `|log F| ≤ max l (-l')`. The upper exponent given here for
`log F` comes from the bound `max l (-l') ≤ 99 log b + exp (max l (-l') - 99 log b)`. -/
instance (priority := low) [D.HasLogUpper F l] [D.HasLogLower F l'] :
    D.HasLogUpper (Real.log F) (max (99 + Real.log D.logB) (max l (-l') - 99 * D.logB) + 1) := by
  have h_pos : 0 < F := HasLogBound.pos D
  have h_lower : l' ≤ Real.log F :=
    (le_log_iff_exp_le h_pos).2 (D.hasLogLower_iff.1 inferInstance)
  have h_upper : Real.log F ≤ l :=
    (log_le_iff_le_exp h_pos).2 ((le_abs_self F).trans (D.hasLogUpper_iff.1 inferInstance))
  have h_abs : |Real.log F| ≤ max l (-l') :=
    abs_le.2 ⟨by linarith [le_max_right l (-l')], h_upper.trans (le_max_left l (-l'))⟩
  -- `y ≤ exp y` for `y = max l (-l') - 99 * logB`
  have h_le : |Real.log F| ≤ 99 * D.logB + exp (max l (-l') - 99 * D.logB) := by
    linarith [add_one_le_exp (max l (-l') - 99 * D.logB)]
  exact hasLogUpper_of_abs_le h_le

end

/-- If `|A| ≤ exp l` and `B ≤ A` for natural numbers, then `|B| ≤ exp l`: an upper exponent of `A`
is one of every `B ≤ A`. -/
lemma hasLogUpper_of_le [D.HasLogUpper A l] (hBA : B ≤ A) : D.HasLogUpper B l :=
  hasLogUpper_of_le_of_nonneg (cast_le.2 hBA) B.cast_nonneg

/-- If `exp l' ≤ G ≤ F`, then `exp l' ≤ F`: a lower exponent of `G` is one of `F`. -/
lemma hasLogLower_of_le [D.HasLogLower G l'] (hGF : G ≤ F) : D.HasLogLower F l' :=
  D.hasLogLower_iff.2 ((D.hasLogLower_iff.1 inferInstance).trans hGF)

/-! ### Comparing two quantities by their exponents -/

section

-- The default proof of `l < l'` first clears all hypotheses but `D`, which keeps `grind` fast.
variable [D.HasLogUpper F l] [D.HasLogLower G l'] [D.HasLogUpper A l] [D.HasLogLower B l']
  (h_exp : l < l' := by
    clear_aux_decl
    clear * - D
    repeat clear ‹_›
    grind (splits := 99) [D.scale_inequalities])

include D h_exp
/-- If `|F| ≤ exp l`, `exp l' ≤ G` and `l < l'`, then `F < G`. -/
protected lemma lt_of_hasLogBound : F < G :=
  calc F ≤ |F| := le_abs_self F
    _ ≤ exp l := D.hasLogUpper_iff.1 inferInstance
    _ < exp l' := exp_lt_exp.2 h_exp
    _ ≤ G := D.hasLogLower_iff.1 inferInstance

/-- If `|F| ≤ exp l`, `exp l' ≤ G` and `l < l'`, then `F ≤ G`. -/
protected lemma le_of_hasLogBound : F ≤ G := (D.lt_of_hasLogBound h_exp).le

/-- If natural numbers `A`, `B` satisfy `A ≤ exp l`, `exp l' ≤ B` and `l < l'`, then `A < B`. -/
lemma nat_lt_of_hasLogBound : A < B := cast_lt.mp (D.lt_of_hasLogBound h_exp)

/-- If natural numbers `A`, `B` satisfy `A ≤ exp l`, `exp l' ≤ B` and `l < l'`, then `A ≤ B`. -/
lemma nat_le_of_hasLogBound : A ≤ B := (D.nat_lt_of_hasLogBound h_exp).le

end

/-- `exp 0 ≤ π ≤ exp 4`. -/
instance : HasLogBound D u π (if u then 4 else 0) := by
  grind [two_le_pi, pi_le_four, HasLogBound, exp_zero, add_one_le_exp]

/-- The number `m` of lifts lies between `x^(1/2)` and `2 x^(1/2)`. -/
instance : HasLogBound D u D.m (D.logX / 2 + (if u then 2 else 0)) :=
  .of_mem_Icc (exp (D.logX / 2)) (2 * exp (D.logX / 2)) D.m_mem
    (by cases u <;> grind [D.scale_inequalities])

/-- The rank `r` lies between `x⁵` and `3 x⁵`. -/
instance : HasLogBound D u D.r (5 * D.logX + (if u then 3 else 0)) :=
  .of_mem_Icc (exp (5 * D.logX)) (3 * exp (5 * D.logX)) D.r_mem
    (by cases u <;> grind [D.scale_inequalities])

/-- The constant `P.constantBound` is at most `log b`, since `10¹² P.constantBound ≤ log log b`. -/
instance : D.HasLogUpper P.constantBound (Real.log D.logB) := by
  grind [scale_inequalities, HasLogBound, exp_log]

/-! ### Sizes of the derived parameters -/

/-- The rank `m` is at least `10000`. -/
lemma ten_thousand_le_m : 10000 ≤ D.m := D.nat_le_of_hasLogBound

/-- `r + 1 = k + m`, as the subtraction in `k = r + 1 - m` is exact. -/
@[grind! .]
lemma r_add_one : D.r + 1 = D.k + D.m := by
  have h_le : D.m ≤ D.r + 1 := D.nat_le_of_hasLogBound
  rw [k, Nat.sub_add_cancel h_le]

/-- The rank `k = r + 1 - m` is at most the rank `r`. -/
lemma k_le_r : D.k ≤ D.r := by grind [ten_thousand_le_m]

/-- The rank `k` lies between `e⁻² x⁵` and `e³ x⁵`. -/
instance : HasLogBound D u D.k (5 * D.logX + (if u then 3 else -2)) := by
  -- `k = r + 1 - m` lies between `r / 2` and `r`, since `1 ≤ m ≤ r / 2`
  have m_le : D.m ≤ (D.r / 2 : ℝ) := D.le_of_hasLogBound
  have h_mem : (D.k : ℝ) ∈ Set.Icc (D.r / 2 : ℝ) D.r := by
    grind [ten_thousand_le_m, k, cast_sub, one_le_cast]
  exact .of_mem_Icc (D.r / 2) D.r h_mem (by cases u <;> grind [D.scale_inequalities])

/-- The number `t = 5 r` lies between `x⁵` and `e⁸ x⁵`. -/
instance : HasLogBound D u D.t (5 * D.logX + (if u then 8 else 0)) := by
  rw [t]
  exact .of_lower_of_upper (by cases u <;> grind [D.scale_inequalities])

/-- The exponents of `m ^ 22` are those of `2 ^ s`, for the exponent `s = D.towerExp` of the data,
which satisfies `2 ^ s = m ^ 22`. -/
instance [HasLogBound D u (D.m ^ 22) l] : HasLogBound D u (ofNat(2) ^ D.towerExp) l := by
  -- `m = 2 ^ (e + 1)` and `s = 22 * (e + 1)`, so `2 ^ s = m ^ 22`
  obtain ⟨e, hm, hs⟩ : ∃ e : ℕ, D.m = 2 ^ (e + 1) ∧ D.towerExp = (e + 1) * 22 :=
    D.exists_m_eq_two_pow
  have h_pow : (2 : ℝ) ^ D.towerExp = D.m ^ 22 := by simp [hm, hs, pow_mul]
  rwa [h_pow]

/-- `x¹¹ ≤ towerDeg s ≤ x¹¹ (log b)^{1/5}`, where `s = D.towerExp` and
`towerDeg s = 3 ^ (Nat.log 3 s + 5) * 2 ^ s` is the ratio `q₁ / q₀` of the orders of the roots of
unity. -/
instance :
    HasLogBound D u (towerDeg D.towerExp)
      (11 * D.logX + (if u then Real.log D.logB / 5 else 0)) := by
  -- the power of `3` in `towerDeg D.towerExp` is controlled by
  -- `3 ^ Nat.log 3 D.towerExp ≤ D.towerExp + 1`
  have h_succ : D.HasLogUpper (D.towerExp + 1 : ℕ) (max (Real.log D.logX₁) 1 + 1) :=
    .of_lower_of_upper (by grind [D.scale_inequalities])
  have h_pow : D.HasLogUpper (3 ^ Nat.log 3 D.towerExp : ℕ) (max (Real.log D.logX₁) 1 + 1) :=
    D.hasLogUpper_of_le (pow_log_le_add_one 3 D.towerExp)
  -- so instance search has an exponent for each factor of `3 ^ (Nat.log 3 s + 5) * 2 ^ s`
  rw [towerDeg, pow_add]
  exact .of_lower_of_upper (by cases u <;> grind [D.scale_inequalities])

/-- `x¹¹ ≤ f ≤ exp P.constantBound * x¹¹ (log b)^{1/5}` for the number `f` of infinite places of
the number field `E = P.E D.towerExp` of the data. -/
instance hasLogBound_f :
    HasLogBound D u D.f (11 * D.logX + if u then Real.log D.logB / 5 + P.constantBound else 0) := by
  rw [f, P.numInfPlaces_E]
  exact .of_lower_of_upper (by cases u <;> grind [D.scale_inequalities])

/-- An upper exponent of the number `f` of infinite places of `E` is one of `#S` for every set `S`
of such places. -/
instance {S : Finset D.Φ} [D.HasLogUpper D.f l] : D.HasLogUpper #S l :=
  D.hasLogUpper_of_le (card_le_univ S)

/-- The last rank `n m = k + m (t + 1)` lies between `x^{5.5}` and `e^{12} x^{5.5}`. -/
instance : HasLogBound D u (D.n D.m) (5.5 * D.logX + (if u then 12 else 0)) := by
  rw [n]
  exact .of_lower_of_upper (by cases u <;> grind [D.scale_inequalities])

/-- The primes `p₀`, `p₁` lie between `b¹⁰` and `b¹¹`. -/
instance (i : Fin 2) : HasLogBound D u (D.levelPrime i) ((if u then 11 else 10) * D.logB) :=
  .of_mem_Icc (D.b ^ 10) (D.b ^ 11) (D.levelPrime_mem i)
    (by cases u <;> grind [D.scale_inequalities])

/-- `b²⁰ ≤ M ≤ b²²` for `M = p₀ p₁`. -/
lemma M_mem_Icc : (D.M : ℝ) ∈ Set.Icc (D.b ^ 20) (D.b ^ 22) := by
  rw [M, cast_mul]
  constructor
  · grw [← (D.levelPrime_mem 0).1, ← (D.levelPrime_mem 1).1, ← pow_add]
  · grw [(D.levelPrime_mem 0).2, (D.levelPrime_mem 1).2, ← pow_add]

/-- `D.M`, the product `p₀ p₁` of the two primes `D.levelPrime i`, lies between `b²⁰` and `b²²`. -/
instance : HasLogBound D u D.M ((if u then 22 else 20) * D.logB) := by
  rw [M]
  exact .of_lower_of_upper (by cases u <;> grind [D.scale_inequalities])

/-- The half-gap `halfGap = r ^ 8` lies between `x⁴⁰` and `e²⁵ x⁴⁰`. -/
instance : HasLogBound D u D.halfGap (40 * D.logX + (if u then 25 else 0)) := by
  rw [halfGap]
  exact .of_lower_of_upper (by cases u <;> grind [D.scale_inequalities])

/-- The gap `Δ = 2 r ^ 8` lies between `x⁴⁰` and `e²⁷ x⁴⁰`. -/
instance : HasLogBound D u D.gap (40 * D.logX + (if u then 27 else 0)) := by
  rw [gap]
  exact .of_lower_of_upper (by cases u <;> grind [D.scale_inequalities])

/-- `a = x b` has the exponent `log b + log x`. -/
instance : HasLogBound D u D.a (D.logB + D.logX) := by
  rw [cast_a]
  exact .of_lower_of_upper (by cases u <;> grind [D.scale_inequalities])

/-- The weight `D.natB` at the `b`-places, which is the scale `b`, has the exponent `log b`. -/
instance : HasLogBound D u D.natB D.logB := by
  rw [cast_natB]
  exact .of_lower_of_upper (by cases u <;> grind [D.scale_inequalities])

/-- `offWeight = a / x₁` has the exponent `log b - log x₁ + log x`. -/
instance : HasLogBound D u D.offWeight (D.logB - D.logX₁ + D.logX) := by
  rw [cast_offWeight]
  exact .of_lower_of_upper (by cases u <;> grind [D.scale_inequalities])

/-- If `l` is an upper exponent of `#S` and `l'` one of every term `v y`, then `l + l'` is an upper
exponent of `∑ y ∈ S, v y`. -/
instance {κ : Type*} {S : Finset κ} {v : κ → ℝ} [D.HasLogUpper #S l]
    [hv : ∀ y : κ, D.HasLogUpper (v y) l'] :
    D.HasLogUpper (∑ y ∈ S, v y) (l + l') := by
  -- compare with `#S * exp l'`
  have h_term : ∀ y ∈ S, |v y| ≤ exp l' := fun y _ ↦ D.hasLogUpper_iff.1 (hv y)
  have h_sum : |∑ y ∈ S, v y| ≤ #S * exp l' :=
    calc |∑ y ∈ S, v y| ≤ ∑ y ∈ S, |v y| := abs_sum_le_sum_abs v S
      _ ≤ ∑ _y ∈ S, exp l' := sum_le_sum h_term
      _ = #S * exp l' := by simp
  exact hasLogUpper_of_abs_le h_sum

/-- An upper exponent of `|log F| + |log G|` is one of `log (F * G)`, also if `F` or `G` is zero. -/
instance [D.HasLogUpper (|log F| + |log G|) l] : D.HasLogUpper (Real.log (F * G)) l := by
  grind [HasLogBound, log_mul]

/-- An upper exponent of `A log F` is one of `log (F ^ A)`. -/
instance [D.HasLogUpper (A * log F) l] : D.HasLogUpper (Real.log (F ^ A)) l := by simpa

/-- An upper exponent of `A log A` is one of `log A!`. -/
instance [D.HasLogUpper (A * Real.log A) l] : D.HasLogUpper (Real.log A !) l := by
  have h_le : Real.log A ! ≤ Real.log (A ^ A) := by grw [factorial_le_pow, cast_pow]
  exact hasLogUpper_of_le_of_nonneg h_le (log_natCast_nonneg A !)

/-! ### Inequalities and parities of the ranks -/

/-- The rank `k = r + 1 - m` is at least `100 m`, for the number `m` of lifts. -/
lemma hundred_mul_m_le_k : 100 * D.m ≤ D.k := D.nat_le_of_hasLogBound

/-- The rank `k = r + 1 - m` is positive. -/
@[simp]
lemma k_pos : 0 < D.k := by
  have h_one : 1 ≤ D.k := D.nat_le_of_hasLogBound
  exact h_one

/-- The ranks `n j = k + j (t + 1)` increase with `j`. -/
lemma n_mono : Monotone D.n := fun i j hij ↦ by
  simp only [n]
  gcongr

/-- `k = r + 1 - m` is even, as `r` is odd and `m` is even. -/
lemma k_even : Even D.k := by grind

attribute [grind] t gap

attribute [grind =] liftWeight_eq

/-- `t = 5 r` is odd, as `r` is. -/
lemma t_odd : Odd D.t := by grind

/-- `r + 6 ≤ t`, as `t = 5 r` and `r` is a positive power of `3`. -/
lemma r_add_six_le_t : D.r + 6 ≤ D.t := by
  obtain ⟨e, hr⟩ : ∃ e : ℕ, D.r = 3 ^ (e + 1) := D.exists_r_eq_three_pow
  have h_three : 3 ≤ D.r := by
    rw [hr]
    exact Nat.le_self_pow e.succ_ne_zero 3
  rw [t]
  omega

/-- The number `k + t + 1` is at most the half-gap `halfGap = r ^ 8`. -/
lemma k_add_t_add_one_le_halfGap : D.k + D.t + 1 ≤ D.halfGap := D.nat_le_of_hasLogBound

attribute [grind! .] k_add_t_add_one_le_halfGap k_pos hundred_mul_m_le_k k_even t_odd k_le_r
  r_add_six_le_t

end New.Data

end
