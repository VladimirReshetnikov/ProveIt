import Lib.ClassField.HeckeCharacter.SplitTameCharacters
import New.Derivatives.Field.ChosenPlaces

/-!
# Weight bounds, the level N, and twists and m-fold twists for chains of lifts

The data `D` (`New.Data`) fix a CM field `E = D.E`, scales `x ≤ x₁ ≤ b`, a number `m` of lifts,
weights `κ` and `κ_j = D.liftWeight j` at the infinite places and a level `N`. The file bounds the
weight `κ` (`New.Data.weight`) and the numbers `κ_s` (`New.Data.shiftedWeight`,
`New.Data.liftWeight`). For a chain of lifts one takes powers `ϑ ^ j` of an m-fold twist `ϑ`, whose
powers of exponent `1, …, m` are all twists.

## Main definitions and results

* `New.Data.targetParameter`: the row parameter, a sequence of integers at each infinite place.
  `New.Data.targetParameter_eq` writes its later entries as `Δ / 2 - κ_j`.
* `New.Data.logLevelTarget`: the logarithm of the lower end of the range for the level, between
  `m log b` and `24 m log b`. `New.Data.log_N_mem_Icc_logLevelTarget` puts `log N` within `√(log b)`
  above it, so `log N` lies between `m log b` and `30 m log b`. `New.Data.N_modEq_one` gives `N ≡ 1`
  modulo `New.Data.cyclotomicConductor`.
* `New.Data.TameChar`, `New.Data.Twist`: characters of `U(1)(𝔸)` of weight `0` with tame part
  `tamePart` supported on a finite set `Q` of places; a twist has `tamePart w ≠ 1` on `Q`.
* `New.Data.untwistedLiftChar`, `New.Data.liftChar`: the characters `μ_j⁰` and `μ_j⁰ ϑ` of weight
  `-κ_j`.
* `New.Data.MFoldTwist`: twists whose powers of exponent `1, …, m` are twists
  (`New.Data.MFoldTwist.powTwist`).
* `New.Data.chainChar`: the character `μ_j⁰ ϑ ^ j` of lift `j` of a chain. It is given by
  `New.Data.liftChar` applied to `ϑ ^ j` and `j`.

Notions from other files:
* `New.Data.weight`: the weight `κ` of an infinite place of `E`. It is `b = a / x` at the
  `b`-places, which form a chosen finite set `D.bPlaces`, and `a / x₁` at the others; `a = x b`.
* `New.Data.shiftedWeight`, `New.Data.liftWeight`: `D.shiftedWeight i σ` is `κ_s = κ + (s + 1/2) Δ`
  at `s = i / 2`, and `D.liftWeight j σ` is `κ_j`; the gap is `Δ = D.gap = 2 * D.halfGap`.
* `New.Data.HasLogBound`: `D.HasLogBound u F l` is `|F| ≤ exp l` if `u` is true (`D.HasLogUpper`)
  and `exp l ≤ F` if `u` is false (`D.HasLogLower`).
* `New.AutChar`: the group of automorphic characters of `U(1)(𝔸)`.
* `New.AutChar.HasWeight`: `μ.HasWeight e ψ` says that the character `μ` has weight `e` and tame
  part `ψ`, that is, almost all residue characters `ψ_w` are trivial and
  `μ(u) = ∏_v u_v ^ e(v) * ∏_w ψ_w(u mod w)` whenever `u` has integral finite part.
-/

noncomputable section

/-! ## Bounds for the weights κ and κ_j -/

section Weights

open Real Set

namespace New.Data

variable {P : Parameters} (D : Data P) {j : ℕ} (σ : D.Φ)

/-- The weight `κ = D.weight σ` of an infinite place `σ : D.Φ` of the field `E = D.E` satisfies
`a / x₁ ≤ κ ≤ a / x`, where `x ≤ x₁ ≤ b` are the scales of the data and `a = x b`. -/
lemma weight_mem_Icc : (D.weight σ : ℝ) ∈ Icc (D.a / D.x₁) (D.a / D.x) := by
  have h_le : (D.a / D.x₁ : ℝ) ≤ D.a / D.x := D.le_of_hasLogBound
  rw [cast_weight]
  split_ifs
  exacts [⟨h_le, le_rfl⟩, ⟨le_rfl, h_le⟩]

/-- The size of the weight: `b / x₁ ≤ κ ≤ b` (upper bound for `u` true, lower for `u` false). -/
instance {u : Bool} : D.HasLogBound u (D.weight σ) (D.logB + if u then 0 else -D.logX₁) :=
  .of_mem_Icc (D.a / D.x₁) (D.a / D.x) (D.weight_mem_Icc σ)
    (by cases u <;> grind [D.scale_inequalities])

/-- The weight `κ = D.weight σ` of an infinite place is at most the scale `b`. -/
lemma weight_le_b : (D.weight σ : ℝ) ≤ D.b :=
  (D.weight_mem_Icc σ).2.trans_eq <| by rw [cast_a, mul_div_cancel_left₀ _ (exp_ne_zero D.logX)]

/-- The weight `κ = D.weight σ` satisfies `κ + x⁴² ≤ 2 b`, for the scales `x ≤ b`. -/
lemma weight_add_x_pow_le_two_mul_b : (D.weight σ : ℝ) + D.x ^ 42 ≤ 2 * D.b := by
  have h_pow : D.x ^ 42 ≤ D.b := D.le_of_hasLogBound
  linarith [D.weight_le_b σ]

/-- The weight `κ = D.weight σ` is at most `κ_j - Δ / 2`, where
`κ_j = D.liftWeight j σ = κ + (j + 1/2) Δ` and `Δ / 2 = D.halfGap` is half the gap. -/
lemma weight_le_liftWeight_sub (j : ℕ) (σ : D.Φ) :
    (D.weight σ : ℝ) ≤ D.liftWeight j σ - D.halfGap := by
  have h_nonneg : (0 : ℝ) ≤ j * D.gap := by positivity
  rw [liftWeight_eq]
  push_cast
  linarith

/-- For `i ≤ 4 m` the shifted weight `D.shiftedWeight i σ = κ + (i + 1) Δ / 2` lies between `κ` and
`κ + x⁴²`, where `κ = D.weight σ` and `Δ / 2 = D.halfGap` is half the gap. -/
lemma shiftedWeight_mem_Icc {i : ℕ} (hi : i ≤ 4 * D.m) (σ : D.Φ) :
    (D.shiftedWeight i σ : ℝ) ∈ Icc (D.weight σ : ℝ) (D.weight σ + D.x ^ 42) := by
  have h_gap : ((4 * D.m + 1) * D.halfGap : ℝ) ≤ D.x ^ 42 := D.le_of_hasLogBound
  have hi_real : (i : ℝ) ≤ 4 * D.m := mod_cast hi
  rw [shiftedWeight]
  push_cast
  exact ⟨le_add_of_nonneg_right (by positivity), by grw [hi_real, h_gap]⟩

/-- For `i ≤ 4 m` one has `log (D.shiftedWeight i σ) ≤ log κ + 1 / x`. -/
lemma log_shiftedWeight_le {i : ℕ} (hi : i ≤ 4 * D.m) (σ : D.Φ) :
    log (D.shiftedWeight i σ) ≤ log (D.weight σ) + D.x⁻¹ := by
  have h_pos : (0 : ℝ) < D.weight σ := HasLogBound.pos D
  have h_pow : D.x ^ 42 ≤ D.weight σ * D.x⁻¹ := D.le_of_hasLogBound
  obtain ⟨h_lower, h_upper⟩ := D.shiftedWeight_mem_Icc hi σ
  rw [log_le_iff_le_exp (h_pos.trans_le h_lower), exp_add, exp_log h_pos]
  calc (D.shiftedWeight i σ : ℝ) ≤ D.weight σ + D.x ^ 42 := h_upper
    _ ≤ D.weight σ * (D.x⁻¹ + 1) := by linarith
    _ ≤ D.weight σ * exp D.x⁻¹ := by grw [add_one_le_exp]

/-- For `j ≤ 2 m` the shifted weight `κ_j = D.liftWeight j σ` is at most `κ + x⁴²`, with
`κ = D.weight σ`. -/
lemma liftWeight_le_weight_add {j : ℕ} (hj : j ≤ 2 * D.m) (σ : D.Φ) :
    (D.liftWeight j σ : ℝ) ≤ D.weight σ + D.x ^ 42 :=
  (D.shiftedWeight_mem_Icc (by omega) σ).2

/-- For `j ≤ 2 m` the shifted weight `κ_j = D.liftWeight j σ` is at most `2 b`. -/
lemma liftWeight_le_two_mul_b {j : ℕ} (hj : j ≤ 2 * D.m) (σ : D.Φ) :
    (D.liftWeight j σ : ℝ) ≤ 2 * D.b :=
  (D.liftWeight_le_weight_add hj σ).trans (D.weight_add_x_pow_le_two_mul_b σ)

/-- The size of `κ₀ = D.liftWeight 0 σ`: it is at most `2 b`, so at most `exp (2 + log b)`. -/
instance : D.HasLogUpper (D.liftWeight 0 σ) (2 + D.logB) :=
  hasLogUpper_of_le_of_nonneg (D.liftWeight_le_two_mul_b (Nat.zero_le (2 * D.m)) σ)
    (D.liftWeight 0 σ).cast_nonneg

/-- A lower bound `exp l ≤ κ` for the weight `κ = D.weight σ` gives `exp l ≤ κ_j` for the shifted
weight `κ_j = D.liftWeight j σ`, because `κ ≤ κ_j`. -/
instance {l : ℝ} [D.HasLogLower (D.weight σ) l] : D.HasLogLower (D.liftWeight j σ) l :=
  D.hasLogLower_of_le <| (D.weight_le_liftWeight_sub j σ).trans
    (sub_le_self _ D.halfGap.cast_nonneg)

/-- For `j ≤ 2 m` the shifted weight `κ_j = D.liftWeight j σ` has `log κ_j ≤ log κ + 1 / x`, with
`κ = D.weight σ`. -/
lemma log_liftWeight_le {j : ℕ} (hj : j ≤ 2 * D.m) (σ : D.Φ) :
    log (D.liftWeight j σ) ≤ log (D.weight σ) + D.x⁻¹ :=
  D.log_shiftedWeight_le (by omega) σ

end New.Data

end Weights

namespace New.Data

/-!
## The row parameter, the level N, twists and the characters of the lifts

`New.Data.le_of_hasLogBound` proves an inequality by comparing bounds `New.Data.HasLogBound`, so
sizes are recorded here as instances.
-/

section Level

open NumberField Set Nat WeilData Parameters

variable {P : Parameters} (D : Data P)

/-- The row parameter `(k/2 - 1, k/2 - 2, …; -κ_{1/2}, -κ_{3/2}, …)` at the infinite place `v` of
`E`, the sequence from which the Harish-Chandra parameters at `v` of the unitary groups in the chain
of lifts are read off. Entries are numbered from `0`, with `k - 1` entries before the semicolon.
Here `k = D.k = r + 1 - m` is the rank of the source, for the rank `r = D.r` of the target and the
number `m = D.m` of lifts; `k/2` is integer division; and `κ_s = D.shiftedWeight (2 s) v` is the
shifted weight `κ + (s + 1/2) Δ`. The rank `k` is even (`New.Data.k_even`). -/
def targetParameter (v : D.Φ) (i : ℕ) : ℤ :=
  if i + 1 < D.k then D.k / 2 - 1 - i else -D.shiftedWeight (2 * (i + 1 - D.k) + 1) v

/-- A formula for entry `i` of the row parameter `D.targetParameter v`, the integer sequence
`(k/2 - 1, k/2 - 2, …, 1 - k/2; -κ_{1/2}, -κ_{3/2}, …)` at the infinite place `v` of `E = D.E` from
which the Harish-Chandra parameters in the chain of lifts are read off. The entries with
`i < k - 1` are `k/2 - 1 - i`, and entry `i ≥ k - 1` is `Δ / 2 - κ_j` with `j = i + 2 - k`. Here the
rank `k = D.k` of the source is even (`New.Data.k_even`), so the division `k / 2` is exact;
`Δ / 2 = D.halfGap` is half the gap; and `κ_j = D.liftWeight j v = κ + (j + 1/2) Δ` is the shifted
weight, for the weight `κ` of `v`. -/
lemma targetParameter_eq (v : D.Φ) (i : ℕ) :
    D.targetParameter v i =
      if i + 1 < D.k then (D.k / 2 - 1 - i : ℤ) else D.halfGap - D.liftWeight (i + 2 - D.k) v := by
  rw [targetParameter]
  split_ifs with hi
  · rfl
  · rw [liftWeight, shiftedWeight, shiftedWeight, show i + 2 - D.k = i + 1 - D.k + 1 by omega]
    push_cast
    ring

/-- The size of `Ω = exp (γ - Re L'/L(1, χ_K)) * (2 π / rd_E)`: one has `x⁻¹³ ≤ Ω ≤ 1` (upper bound
for `u` true, lower for `u` false). Here `γ` is Euler's constant, `χ_K` is the quadratic character
of `K = ℚ(√-d)` for the prime `d = P.d`, and `rd_E` is the root discriminant of the field
`E = P.E s` of the data, where `s = D.towerExp` is the exponent with `2 ^ s = m ^ 22`. -/
instance {u : Bool} : D.HasLogBound u (P.bigOmega D.towerExp) (if u then 0 else -13 * D.logX) := by
  -- instance search finds `1 ≤ 2 π ≤ exp 6` and `x ^ 10 ≤ rd_E ≤ x ^ 12`; it remains to
  -- compare exponents, and the constants are small against `log x`
  have h_small : |chowlaSelbergConst P.d| + 6 ≤ D.logX := by
    grind [constantBound, Finset.sum_nonneg, D.scale_inequalities]
  unfold bigOmega
  exact .of_lower_of_upper (by grind)

/-! ### The size and the residue class of the level `N` -/

/-- The logarithm of `N₋ = κ̄ ^ m (M rd_E / 2π) ^ (m - 1) b ^ (-15 / 2)`, the lower end of the range
for the level. Here `κ̄` is the geometric mean of the weights at the `f = D.f` infinite places of
`E`, the principal level `M = D.M` is the product of the two primes `D.levelPrime 0` and
`D.levelPrime 1`, and `rd_E = D.rootDisc` is the root discriminant of `E`. -/
def logLevelTarget : ℝ :=
  D.m * ((∑ v : D.Φ, Real.log (D.weight v)) / D.f) +
    (D.m - 1) * Real.log (D.M * D.rootDisc / (2 * Real.pi)) - 15 / 2 * D.logB

/-- The number `D.logLevelTarget` is `New.Parameters.logLevelMin` at the values given by the
data. -/
lemma logLevelTarget_eq_logLevelMin :
    D.logLevelTarget = P.logLevelMin D.towerExp D.m D.weight D.M D.logB :=
  rfl

/-- The prime level `N` of the data is chosen with `log N₋ ≤ log N ≤ log N₋ + √(log b)`, where
`log N₋ = D.logLevelTarget` is the logarithm of `κ̄ ^ m (M rd_E / 2π) ^ (m - 1) b ^ (-15 / 2)`. This
lower end satisfies `m log b ≤ log N₋ ≤ 24 m log b`, for the number `m = D.m` of lifts and
`log b = D.logB`. -/
lemma logLevelTarget_mem_Icc : D.logLevelTarget ∈ Icc (D.m * D.logB) (24 * D.m * D.logB) := by
  have h_one_le_weight (τ : D.Φ) : (1 : ℝ) ≤ D.weight τ := D.le_of_hasLogBound
  have h_two_le_m : 2 ≤ D.m := by linarith [D.ten_thousand_le_m]
  rw [logLevelTarget_eq_logLevelMin]
  exact P.logLevelMin_mem_Icc h_two_le_m D.le_of_hasLogBound
    (fun τ ↦ ⟨h_one_le_weight τ, D.weight_le_b τ⟩) D.M_mem_Icc D.le_of_hasLogBound

/-- The level `N` is `≡ 1` modulo `n = D.cyclotomicConductor = q₁ d`. Here `d` is the prime with
`K = ℚ(√-d)` and `q₁` is the order of the root of unity that generates `E` over `K`, so `E` lies in
`ℚ(ζ_n)`. -/
lemma N_modEq_one : D.N ≡ 1 [MOD D.cyclotomicConductor] :=
  D.N_modEq_one_q₂_sq.of_dvd ((q₁_mul_d_dvd_q₂ : D.cyclotomicConductor ∣ P.q₂ D.towerExp).pow
    two_ne_zero)

/-- The level `N` satisfies `log N₋ ≤ log N ≤ log N₋ + √(log b)`, where
`log N₋ = D.logLevelTarget`. -/
lemma log_N_mem_Icc_logLevelTarget :
    Real.log D.N ∈ Icc D.logLevelTarget (D.logLevelTarget + √D.logB) := by
  rw [logLevelTarget_eq_logLevelMin, M]
  exact D.log_N_mem

/-- The level `N` satisfies `m log b ≤ log N ≤ 30 m log b`. -/
lemma log_N_mem_Icc : Real.log D.N ∈ Icc (D.m * D.logB) (30 * D.m * D.logB) := by
  have h_sqrt : √D.logB ≤ 6 * D.m * D.logB := D.le_of_hasLogBound
  obtain ⟨h_min_ge, h_min_le⟩ := D.logLevelTarget_mem_Icc
  obtain ⟨h_log_ge, h_log_le⟩ := D.log_N_mem_Icc_logLevelTarget
  constructor <;> linarith

/-- The size of `log N`: `√x log b ≤ log N ≤ e³² √x log b` (upper bound for `u` true, lower for `u`
false), from `m log b ≤ log N ≤ 30 m log b` and `√x ≤ m ≤ 2 √x`. -/
instance {u : Bool} :
    D.HasLogBound u (Real.log D.N) (D.logX / 2 + Real.log D.logB + (if u then 32 else 0)) :=
  .of_mem_Icc (D.m * D.logB) (30 * D.m * D.logB) D.log_N_mem_Icc
    (by cases u <;> grind [D.scale_inequalities])

/-- The level `N` is prime. -/
instance : Fact D.N.Prime := ⟨D.N_prime⟩

/-- The level is large: `b¹⁰¹ ≤ N`. -/
instance : D.HasLogLower D.N (101 * D.logB) := by
  have h_log : 101 * D.logB ≤ Real.log D.N := D.le_of_hasLogBound
  exact D.hasLogLower_iff.2 ((Real.le_log_iff_exp_le (HasLogBound.pos D)).1 h_log)

/-! ### Tame characters and twists -/

/-- A character of U(1)(𝔸) of weight 0 whose tame part is supported on a finite set Q of places. The
places of Q have norm prime to M N, with M = `D.M` and N the level, and Q is disjoint from its
conjugate. -/
structure TameChar where
  /-- The automorphic character `ϑ` of `U(1)(𝔸)`. -/
  toAutChar : AutChar D.E
  /-- The modulus: a finite set of finite places of `E`. -/
  Q : Finset (New.FinPlace D.E)
  /-- The tame part: one character of the residue field at each finite place. -/
  tamePart : (w : New.FinPlace D.E) → MulChar (ResField w) ℂ
  /-- The character has weight `0` and tame part `tamePart`. -/
  hasWeight : toAutChar.HasWeight 0 tamePart
  /-- The tame part is trivial outside `Q`. -/
  tamePart_eq_one : ∀ w ∉ Q, tamePart w = 1
  /-- `Q` is disjoint from its complex conjugate. -/
  star_notMem : ∀ w ∈ Q, star w ∉ Q
  /-- The places of `Q` have norm prime to `M N`, where `M = D.M` and `N` is the level. -/
  coprime : (D.M * D.N).Coprime (∏ w ∈ Q, w.q)

/-- The product of the norms of the places in the finite set Q of the tame character ϑ. -/
abbrev TameChar.normQ {D : Data P} (ϑ : D.TameChar) : ℕ := ∏ w ∈ ϑ.Q, w.q

/-- A twist: a tame character (`New.Data.TameChar`) whose tame part is non-trivial at every place of
its set Q. -/
structure Twist extends D.TameChar where
  /-- The tame part is non-trivial at every place of `Q`. -/
  tamePart_ne_one : ∀ w ∈ Q, tamePart w ≠ 1

/-- The trivial twist, with empty set Q and trivial tame part. -/
instance : One D.Twist where
  one :=
    { toAutChar := 1
      Q := ∅
      tamePart := 1
      hasWeight := .one
      tamePart_eq_one := by simp
      star_notMem := by simp
      coprime := by simp
      tamePart_ne_one := by simp }

/-- A twist is read as its tame character. -/
instance : Coe D.Twist D.TameChar := ⟨Twist.toTameChar⟩

/-- The trivial character, as a tame character with empty set Q and trivial tame part. -/
abbrev TameChar.one {D : Data P} : D.TameChar := Twist.toTameChar 1

/-! ### The characters of the lifts -/

/-- The character μ_j⁰ = μ♭(υ^{−Δ}χ)^j of U(1)(𝔸). Here μ♭ = `D.chiZero` has weight −κ₀ and trivial
tame part, χ = `D.chiM` has weight 0 and tame part `D.chiMLocal`, υ is the restricted splitting
character `New.WeilData.upsilonU1` and Δ = `D.gap` is the gap. -/
def untwistedLiftChar (j : ℕ) : AutChar D.E := D.chiZero * (upsilonU1 ^ (-D.gap : ℤ) * D.chiM) ^ j

/-- The character μ_j⁰ = `D.untwistedLiftChar j` of U(1)(𝔸), for the field E = `D.E`, has weight
−κ_j and tame part ω^j (`HasWeight`): almost all ω_w^j are trivial, and μ_j⁰(u) = ∏_v
u_v^{−κ_j(v)} · ∏_w ω_w^j(u mod w) whenever u has integral finite part, with v running over the
infinite places `InfinitePlace D.E` and w over the finite places of E. Here
κ_j = `D.liftWeight j` = κ₀ + jΔ for the gap Δ = `D.gap`, and μ_j⁰ = μ♭(υ^{−Δ}χ)^j, where
μ♭ = `D.chiZero` has weight −κ₀ and trivial tame part, υ = `upsilonU1` has weight 1 and trivial tame
part, and χ = `D.chiM` has weight 0 and tame part ω = `D.chiMLocal`, a family of characters ω_w of
the residue fields. -/
lemma untwistedLiftChar_hasWeight (j : ℕ) :
    (D.untwistedLiftChar j).HasWeight (fun v : InfinitePlace D.E ↦ -D.liftWeight j v)
      (D.chiMLocal ^ (j : ℤ)) := by
  -- weights add and tame parts multiply
  have h_step : (upsilonU1 ^ (-D.gap : ℤ) * D.chiM).HasWeight (fun _ ↦ -D.gap) D.chiMLocal := by
    simpa only [add_zero, one_mul] using (hasWeight_upsilonU1_zpow (-D.gap : ℤ)).mul
      D.chiM_hasWeight
  have h_weight : (fun v : InfinitePlace D.E ↦ (-D.liftWeight j v : ℤ)) =
      (fun v : InfinitePlace D.E ↦ (-D.liftWeight 0 v : ℤ)) + (j : ℤ) • fun _ ↦ (-D.gap : ℤ) :=
    funext fun v ↦ by simp [liftWeight_eq, add_comm, add_left_comm]
  rw [h_weight, untwistedLiftChar, ← zpow_natCast]
  simpa only [one_mul] using D.chiZero_hasWeight.mul (h_step.zpow j)

/-- For a tame character ϑ and a natural number j, the character μ_j⁰ϑ of U(1)(𝔸). -/
def liftChar (ϑ : D.TameChar) (j : ℕ) : AutChar D.E := D.untwistedLiftChar j * ϑ.toAutChar

/-- The family of residue field characters ω_w^j ψ_w, with ω = `D.chiMLocal` and
ψ = `ϑ.tamePart`; it is the tame part of μ_j⁰ϑ. -/
def liftTamePart (ϑ : D.TameChar) (j : ℕ) : (w : New.FinPlace D.E) → MulChar (ResField w) ℂ :=
  D.chiMLocal ^ (j : ℤ) * ϑ.tamePart

/-- For a tame character ϑ, the character μ_j⁰ϑ = `D.liftChar ϑ j` has weight −κ_j, with
κ_j = `D.liftWeight j`, and tame part `D.liftTamePart ϑ j`, the product of `D.chiMLocal ^ j` and
`ϑ.tamePart`. -/
instance hasWeight_liftChar {ϑ : D.TameChar} {j : ℕ} :
    (D.liftChar ϑ j).HasWeight (fun v : InfinitePlace D.E ↦ -D.liftWeight j v)
      (D.liftTamePart ϑ j) := by
  simpa only [liftChar, liftTamePart, add_zero] using (D.untwistedLiftChar_hasWeight j).mul
    ϑ.hasWeight

/-- The natural numbers j with 1 ≤ j ≤ m, for the number m of the data; they index the lifts. -/
abbrev LiftIndex : Set ℕ := Icc 1 D.m

end Level

/-! ## Powers of tame characters and m-fold twists -/

section MFoldTwists

variable {P : Parameters} (D : Data P)

/-- For a tame character ϑ and a natural number n, the tame character ϑⁿ, with the same set Q and
tame part `ϑ.tamePart ^ n`. -/
def TameChar.pow {D : Data P} (ϑ : D.TameChar) (n : ℕ) : D.TameChar where
  toAutChar := ϑ.toAutChar ^ n
  Q := ϑ.Q
  tamePart := ϑ.tamePart ^ n
  hasWeight := by simpa only [zpow_natCast, smul_zero] using ϑ.hasWeight.zpow n
  tamePart_eq_one w hw := by rw [Pi.pow_apply, ϑ.tamePart_eq_one w hw, one_pow]
  star_notMem := ϑ.star_notMem
  coprime := ϑ.coprime

/-- An m-fold twist: a twist ϑ whose tame part has `tamePart w ^ n ≠ 1` for all w in Q and
1 ≤ n ≤ m. -/
structure MFoldTwist extends D.Twist where
  /-- For `1 ≤ n ≤ m` the `n`-th power of the tame part is non-trivial at every place of `Q`. -/
  pow_ne_one : ∀ n ∈ D.LiftIndex, ∀ w ∈ Q, tamePart w ^ n ≠ 1

/-- For a tame character ϑ and a natural number j, the character μ_j⁰ϑ^j of U(1)(𝔸), used for
lift j of a chain. -/
abbrev chainChar (ϑ : D.TameChar) (j : ℕ) : AutChar D.E := D.liftChar (ϑ.pow j) j

/-- The trivial twist is an m-fold twist, since its set Q is empty. -/
instance : One D.MFoldTwist := ⟨⟨1, fun _ _ w hw ↦ absurd hw (Finset.notMem_empty w)⟩⟩

/-- An m-fold twist is read as its underlying twist. -/
instance : Coe D.MFoldTwist D.Twist := ⟨MFoldTwist.toTwist⟩

/-- For an m-fold twist ϑ and 1 ≤ n ≤ m, the power ϑⁿ as a twist. -/
def MFoldTwist.powTwist {D : Data P} (ϑ : D.MFoldTwist) (n : LiftIndex D) : D.Twist where
  toTameChar := ϑ.pow n
  tamePart_ne_one := ϑ.pow_ne_one n n.property

end MFoldTwists

end New.Data

end
