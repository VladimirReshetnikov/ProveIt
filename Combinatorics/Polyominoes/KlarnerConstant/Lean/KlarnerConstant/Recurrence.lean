import KlarnerConstant.Certificate
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Monotone iteration of Bui's polyomino recurrence

`KlarnerConstant.Certificate` checks the finite rational supersolution.  This
module supplies the analytic order-theoretic bridge: Bui's polynomial map is
monotone on nonnegative profiles, so every iterate from zero lies below every
nonnegative supersolution.

For actual coefficient sequences, simultaneous Picard iteration is not quite
the right truncation.  The `advance` operator evaluates the nonlinear right
sides on the preceding weighted prefix and then closes the five linear
dependencies in topological order.  `PrefixRecurrence` records the resulting
finite induction, while `CoefficientProfile` exposes the exact remaining
coefficient-algebra hypothesis.  No convergence or formal-power-series limit
is used.
-/

namespace LeanProofs.KlarnerConstant

/-- The zero profile, from which the least nonnegative recurrence solution is
approximated. -/
def zeroProfile : Profile where
  c := 0
  d := 0
  e := 0
  f := 0
  g := 0
  h := 0
  p := 0
  q := 0
  r := 0
  s := 0
  t := 0
  u := 0
  v := 0
  w := 0
  x := 0
  y := 0
  z := 0

/-- The finite monotone approximants to Bui's recurrence solution. -/
def buiIterate (ζ : ℚ) : ℕ → Profile
  | 0 => zeroProfile
  | n + 1 => buiMap ζ (buiIterate ζ n)

theorem zeroProfile_nonnegative : zeroProfile.Nonnegative := by
  norm_num [zeroProfile, Profile.Nonnegative]

theorem zeroProfile_le (a : Profile) (ha : a.Nonnegative) :
    zeroProfile.ComponentwiseLE a := by
  simpa [zeroProfile, Profile.Nonnegative, Profile.ComponentwiseLE] using ha

theorem componentwiseLE_refl (a : Profile) : a.ComponentwiseLE a := by
  simp [Profile.ComponentwiseLE]

theorem componentwiseLE_trans {a b c : Profile}
    (hab : a.ComponentwiseLE b) (hbc : b.ComponentwiseLE c) :
    a.ComponentwiseLE c := by
  rcases hab with
    ⟨hac, had, hae, haf, hag, hah, hap, haq, har, has, hat, hau, hav, haw,
      hax, hay, haz⟩
  rcases hbc with
    ⟨hbc, hbd, hbe, hbf, hbg, hbh, hbp, hbq, hbr, hbs, hbt, hbu, hbv, hbw,
      hbx, hby, hbz⟩
  exact
    ⟨hac.trans hbc, had.trans hbd, hae.trans hbe, haf.trans hbf,
      hag.trans hbg, hah.trans hbh, hap.trans hbp, haq.trans hbq,
      har.trans hbr, has.trans hbs, hat.trans hbt, hau.trans hbu,
      hav.trans hbv, haw.trans hbw, hax.trans hbx, hay.trans hby,
      haz.trans hbz⟩

theorem nonnegative_of_componentwiseLE {a b : Profile}
    (ha : a.Nonnegative) (hab : a.ComponentwiseLE b) : b.Nonnegative := by
  rcases ha with
    ⟨hac, had, hae, haf, hag, hah, hap, haq, har, has, hat, hau, hav, haw,
      hax, hay, haz⟩
  rcases hab with
    ⟨hbc, hbd, hbe, hbf, hbg, hbh, hbp, hbq, hbr, hbs, hbt, hbu, hbv, hbw,
      hbx, hby, hbz⟩
  exact
    ⟨hac.trans hbc, had.trans hbd, hae.trans hbe, haf.trans hbf,
      hag.trans hbg, hah.trans hbh, hap.trans hbp, haq.trans hbq,
      har.trans hbr, has.trans hbs, hat.trans hbt, hau.trans hbu,
      hav.trans hbv, haw.trans hbw, hax.trans hbx, hay.trans hby,
      haz.trans hbz⟩

theorem componentwiseLE_g {a b : Profile} (h : a.ComponentwiseLE b) :
    a.g ≤ b.g := by
  exact h.2.2.2.2.1

/-- Bui's polynomial map preserves the nonnegative cone when `ζ ≥ 0`. -/
theorem buiMap_nonnegative {ζ : ℚ} (hζ : 0 ≤ ζ) {a : Profile}
    (ha : a.Nonnegative) : (buiMap ζ a).Nonnegative := by
  rcases ha with
    ⟨hc, hd, he, hf, hg, hh, hp, hq, hr, hs, ht, hu, hv, hw, hx, hy, hz⟩
  simp only [Profile.Nonnegative, buiMap]
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  · positivity

/-- Bui's polynomial map is componentwise monotone on nonnegative profiles. -/
theorem buiMap_mono {ζ : ℚ} (hζ : 0 ≤ ζ) {a b : Profile}
    (ha : a.Nonnegative) (hab : a.ComponentwiseLE b) :
    (buiMap ζ a).ComponentwiseLE (buiMap ζ b) := by
  have hb : b.Nonnegative := nonnegative_of_componentwiseLE ha hab
  rcases ha with
    ⟨hac, had, hae, haf, hag, hah, hap, haq, har, has, hat, hau, hav, haw,
      hax, hay, haz⟩
  rcases hb with
    ⟨hbc, hbd, hbe, hbf, hbg, hbh, hbp, hbq, hbr, hbs, hbt, hbu, hbv, hbw,
      hbx, hby, hbz⟩
  rcases hab with
    ⟨hc, hd, he, hf, hg, hh, hp, hq, hr, hs, ht, hu, hv, hw, hx, hy, hz⟩
  simp only [Profile.ComponentwiseLE, buiMap]
  constructor
  · gcongr
  constructor
  · gcongr
  constructor
  · gcongr
  constructor
  · gcongr
  constructor
  · gcongr
  constructor
  · gcongr
  constructor
  · gcongr
  constructor
  · gcongr
  constructor
  · gcongr
  constructor
  · gcongr
  constructor
  · gcongr
  constructor
  · gcongr
  constructor
  · gcongr
  constructor
  · gcongr
  constructor
  · gcongr
  constructor
  · gcongr
  · gcongr

/-!
The simultaneous map above is the right object for checking a numerical
supersolution.  Truncated coefficient sums obey a slightly different update:
the twelve genuinely recursive right-hand sides are evaluated at the previous
prefix, after which the five linear identities are closed in topological
order.  This is Bui's finite-prefix operator.
-/

/-- One finite-prefix step in Bui's recurrence system. -/
def advance (ζ : ℚ) (prev : Profile) : Profile :=
  let c := ζ + ζ * prev.e
  let d := ζ + ζ * prev.g
  let e := ζ + ζ * prev.f
  let p := prev.e * prev.h + prev.q * prev.d + prev.x * prev.r +
    prev.v * prev.y + prev.u * prev.y * prev.z
  let q := ζ * prev.g + ζ * prev.g * prev.e +
    ζ ^ 2 * (prev.u + prev.t * prev.g + prev.r * prev.u)
  let s := ζ * prev.g + ζ * prev.e ^ 2 + ζ ^ 2 * prev.t +
    ζ ^ 2 * prev.x * prev.g + ζ ^ 2 * prev.y * prev.u
  let u := prev.d * prev.h + prev.s * prev.d + prev.y * prev.r +
    prev.w * prev.y + prev.u * prev.z ^ 2
  let v := ζ * prev.s + ζ ^ 2 * (prev.g ^ 2 + prev.t * prev.e + prev.r * prev.t)
  let w := ζ * prev.s + ζ ^ 2 * (prev.e * prev.g + prev.x * prev.e + prev.y * prev.t)
  let x := ζ * prev.d + ζ ^ 2 * (prev.g + prev.u)
  let y := ζ * prev.c + ζ ^ 2 * (prev.g + prev.t)
  let z := ζ * prev.c + ζ ^ 2 * (prev.e + prev.x)
  let g := e + q
  let f := g + p
  let h := d + s
  let t := x + v
  let r := y + w
  { c := c, d := d, e := e, f := f, g := g, h := h, p := p, q := q,
    r := r, s := s, t := t, u := u, v := v, w := w, x := x, y := y, z := z }

theorem advance_nonnegative {ζ : ℚ} (hζ : 0 ≤ ζ) {a : Profile}
    (ha : a.Nonnegative) : (advance ζ a).Nonnegative := by
  have hm := buiMap_nonnegative hζ ha
  simp only [Profile.Nonnegative, buiMap] at hm
  rcases hm with
    ⟨hc, hd, he, _, _, _, hp, hq, _, hs, _, hu, hv, hw, hx, hy, hz⟩
  have hg := add_nonneg he hq
  have hf := add_nonneg hg hp
  have hh := add_nonneg hd hs
  have ht := add_nonneg hx hv
  have hr := add_nonneg hy hw
  simpa only [Profile.Nonnegative, advance] using
    And.intro hc <| And.intro hd <| And.intro he <| And.intro hf <|
    And.intro hg <| And.intro hh <| And.intro hp <| And.intro hq <|
    And.intro hr <| And.intro hs <| And.intro ht <| And.intro hu <|
    And.intro hv <| And.intro hw <| And.intro hx <| And.intro hy hz

/-- The finite-prefix operator is monotone on the nonnegative cone. -/
theorem advance_mono {ζ : ℚ} (hζ : 0 ≤ ζ) {a b : Profile}
    (ha : a.Nonnegative) (hab : a.ComponentwiseLE b) :
    (advance ζ a).ComponentwiseLE (advance ζ b) := by
  have hm := buiMap_mono hζ ha hab
  simp only [Profile.ComponentwiseLE, buiMap] at hm
  rcases hm with
    ⟨hc, hd, he, _, _, _, hp, hq, _, hs, _, hu, hv, hw, hx, hy, hz⟩
  have hg := add_le_add he hq
  have hf := add_le_add hg hp
  have hh := add_le_add hd hs
  have ht := add_le_add hx hv
  have hr := add_le_add hy hw
  simpa only [Profile.ComponentwiseLE, advance] using
    And.intro hc <| And.intro hd <| And.intro he <| And.intro hf <|
    And.intro hg <| And.intro hh <| And.intro hp <| And.intro hq <|
    And.intro hr <| And.intro hs <| And.intro ht <| And.intro hu <|
    And.intro hv <| And.intro hw <| And.intro hx <| And.intro hy hz

/-- A simultaneous supersolution also bounds the topologically closed prefix
step.  This is the exact bridge that permits the finite certificate to be used
without appealing to a limit of formal power series. -/
theorem advance_le_of_buiMap_le {ζ : ℚ} {a : Profile}
    (h : (buiMap ζ a).ComponentwiseLE a) :
    (advance ζ a).ComponentwiseLE a := by
  simp only [Profile.ComponentwiseLE, buiMap] at h
  rcases h with
    ⟨hc, hd, he, hf₀, hg₀, hh₀, hp, hq, hr₀, hs, ht₀, hu, hv, hw,
      hx, hy, hz⟩
  have hg := (add_le_add he hq).trans hg₀
  have hf := (add_le_add hg hp).trans hf₀
  have hh := (add_le_add hd hs).trans hh₀
  have ht := (add_le_add hx hv).trans ht₀
  have hr := (add_le_add hy hw).trans hr₀
  simpa only [Profile.ComponentwiseLE, advance] using
    And.intro hc <| And.intro hd <| And.intro he <| And.intro hf <|
    And.intro hg <| And.intro hh <| And.intro hp <| And.intro hq <|
    And.intro hr <| And.intro hs <| And.intro ht <| And.intro hu <|
    And.intro hv <| And.intro hw <| And.intro hx <| And.intro hy hz

theorem advance_le_of_isSupersolution {ζ : ℚ} {a : Profile}
    (h : IsSupersolution ζ a) : (advance ζ a).ComponentwiseLE a :=
  advance_le_of_buiMap_le h

theorem buiIterate_nonnegative {ζ : ℚ} (hζ : 0 ≤ ζ) :
    ∀ n, (buiIterate ζ n).Nonnegative
  | 0 => zeroProfile_nonnegative
  | n + 1 => buiMap_nonnegative hζ (buiIterate_nonnegative hζ n)

/-- Every finite iterate from zero lies below a nonnegative supersolution. -/
theorem buiIterate_le_supersolution {ζ : ℚ} (hζ : 0 ≤ ζ) {a : Profile}
    (ha : a.Nonnegative) (hsuper : IsSupersolution ζ a) :
    ∀ n, (buiIterate ζ n).ComponentwiseLE a
  | 0 => zeroProfile_le a ha
  | n + 1 => by
      exact componentwiseLE_trans
        (buiMap_mono hζ (buiIterate_nonnegative hζ n)
          (buiIterate_le_supersolution hζ ha hsuper n))
        hsuper

/--
A concrete finite-prefix recurrence.  Its profiles start at zero, remain in the
nonnegative cone, and each next prefix is bounded by `advance` of the preceding
one.  These are structural recurrence hypotheses, not a restatement of the
desired coefficient bound.
-/
structure PrefixRecurrence (ζ : ℚ) where
  profiles : ℕ → Profile
  zero_eq : profiles 0 = zeroProfile
  nonnegative : ∀ n, (profiles n).Nonnegative
  step : ∀ n, (profiles (n + 1)).ComponentwiseLE (advance ζ (profiles n))

namespace PrefixRecurrence

/-- Every profile in a prefix recurrence is bounded by every nonnegative Bui
supersolution. -/
theorem le_supersolution {ζ : ℚ} (R : PrefixRecurrence ζ) (hζ : 0 ≤ ζ)
    {a : Profile} (ha : a.Nonnegative) (hsuper : IsSupersolution ζ a) :
    ∀ n, (R.profiles n).ComponentwiseLE a
  | 0 => by simpa [R.zero_eq] using zeroProfile_le a ha
  | n + 1 => by
      exact componentwiseLE_trans (R.step n) <|
        componentwiseLE_trans
          (advance_mono hζ (R.nonnegative n) (le_supersolution R hζ ha hsuper n))
          (advance_le_of_isSupersolution hsuper)

/-- Every `g` prefix governed by the recurrence is below the checked rational
certificate. -/
theorem g_le_certificate (R : PrefixRecurrence certificateZeta) (n : ℕ) :
    (R.profiles n).g ≤ certificate.g := by
  exact componentwiseLE_g <|
    R.le_supersolution (le_of_lt certificateZeta_pos)
      certificate_nonnegative certificate_isSupersolution n

theorem g_lt_one (R : PrefixRecurrence certificateZeta) (n : ℕ) :
    (R.profiles n).g < 1 :=
  (R.g_le_certificate n).trans_lt certificate_g_lt_one

end PrefixRecurrence

/-- The weighted sum of the first `N` coefficients (indices `< N`).  The
exclusive upper bound makes the zero prefix definitionally empty. -/
def weightedPrefix (ζ : ℚ) (coeff : ℕ → ℚ) (N : ℕ) : ℚ :=
  ∑ i ∈ Finset.range N, coeff i * ζ ^ i

@[simp] theorem weightedPrefix_zero (ζ : ℚ) (coeff : ℕ → ℚ) :
    weightedPrefix ζ coeff 0 = 0 := by
  simp [weightedPrefix]

/-- Seventeen coefficient sequences, in the same coordinate order as
`Profile`. -/
structure CoefficientProfile where
  c : ℕ → ℚ
  d : ℕ → ℚ
  e : ℕ → ℚ
  f : ℕ → ℚ
  g : ℕ → ℚ
  h : ℕ → ℚ
  p : ℕ → ℚ
  q : ℕ → ℚ
  r : ℕ → ℚ
  s : ℕ → ℚ
  t : ℕ → ℚ
  u : ℕ → ℚ
  v : ℕ → ℚ
  w : ℕ → ℚ
  x : ℕ → ℚ
  y : ℕ → ℚ
  z : ℕ → ℚ

namespace CoefficientProfile

/-- Coordinatewise nonnegativity of all coefficient sequences. -/
def Nonnegative (S : CoefficientProfile) : Prop :=
  (∀ n, 0 ≤ S.c n) ∧ (∀ n, 0 ≤ S.d n) ∧ (∀ n, 0 ≤ S.e n) ∧
  (∀ n, 0 ≤ S.f n) ∧ (∀ n, 0 ≤ S.g n) ∧ (∀ n, 0 ≤ S.h n) ∧
  (∀ n, 0 ≤ S.p n) ∧ (∀ n, 0 ≤ S.q n) ∧ (∀ n, 0 ≤ S.r n) ∧
  (∀ n, 0 ≤ S.s n) ∧ (∀ n, 0 ≤ S.t n) ∧ (∀ n, 0 ≤ S.u n) ∧
  (∀ n, 0 ≤ S.v n) ∧ (∀ n, 0 ≤ S.w n) ∧ (∀ n, 0 ≤ S.x n) ∧
  (∀ n, 0 ≤ S.y n) ∧ (∀ n, 0 ≤ S.z n)

/-- The seventeen weighted prefixes, bundled as one profile. -/
def prefixProfile (S : CoefficientProfile) (ζ : ℚ) (N : ℕ) : Profile where
  c := weightedPrefix ζ S.c N
  d := weightedPrefix ζ S.d N
  e := weightedPrefix ζ S.e N
  f := weightedPrefix ζ S.f N
  g := weightedPrefix ζ S.g N
  h := weightedPrefix ζ S.h N
  p := weightedPrefix ζ S.p N
  q := weightedPrefix ζ S.q N
  r := weightedPrefix ζ S.r N
  s := weightedPrefix ζ S.s N
  t := weightedPrefix ζ S.t N
  u := weightedPrefix ζ S.u N
  v := weightedPrefix ζ S.v N
  w := weightedPrefix ζ S.w N
  x := weightedPrefix ζ S.x N
  y := weightedPrefix ζ S.y N
  z := weightedPrefix ζ S.z N

@[simp] theorem prefixProfile_zero (ζ : ℚ) (S : CoefficientProfile) :
    S.prefixProfile ζ 0 = zeroProfile := by
  cases S <;> simp [prefixProfile, zeroProfile, weightedPrefix]

theorem prefixProfile_nonnegative {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (hS : S.Nonnegative) (N : ℕ) : (S.prefixProfile ζ N).Nonnegative := by
  rcases hS with
    ⟨hc, hd, he, hf, hg, hh, hp, hq, hr, hs, ht, hu, hv, hw, hx, hy, hz⟩
  simp only [Profile.Nonnegative, prefixProfile, weightedPrefix]
  repeat' apply And.intro
  all_goals
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · first | exact hc i | exact hd i | exact he i | exact hf i | exact hg i |
        exact hh i | exact hp i | exact hq i | exact hr i | exact hs i |
        exact ht i | exact hu i | exact hv i | exact hw i | exact hx i |
        exact hy i | exact hz i
    · exact pow_nonneg hζ i

/--
The exact remaining hypothesis for the coefficient algebra: the weighted
prefixes satisfy Bui's seventeen one-step inequalities.  Expanding convolution
coefficients and proving this property is independent of both the numerical
certificate and the order-theoretic argument formalized here.
-/
def SatisfiesPrefixRecurrence (S : CoefficientProfile) (ζ : ℚ) : Prop :=
  ∀ N, (S.prefixProfile ζ (N + 1)).ComponentwiseLE
    (advance ζ (S.prefixProfile ζ N))

def toPrefixRecurrence (S : CoefficientProfile) {ζ : ℚ} (hζ : 0 ≤ ζ)
    (hS : S.Nonnegative) (hrec : S.SatisfiesPrefixRecurrence ζ) :
    PrefixRecurrence ζ where
  profiles := S.prefixProfile ζ
  zero_eq := S.prefixProfile_zero ζ
  nonnegative := S.prefixProfile_nonnegative hζ hS
  step := hrec

/-- A nonnegative coefficient is one summand of the prefix ending immediately
after it. -/
theorem weightedTerm_le_prefix {ζ : ℚ} (hζ : 0 ≤ ζ) {coeff : ℕ → ℚ}
    (hcoeff : ∀ n, 0 ≤ coeff n) (n : ℕ) :
    coeff n * ζ ^ n ≤ weightedPrefix ζ coeff (n + 1) := by
  rw [weightedPrefix, Finset.sum_range_succ]
  exact le_add_of_nonneg_left <|
    Finset.sum_nonneg fun i _ => mul_nonneg (hcoeff i) (pow_nonneg hζ i)

set_option maxHeartbeats 800000 in
/-- The checked certificate bounds every coefficient system satisfying the
concrete weighted-prefix recurrence. -/
theorem g_mul_pow_lt_one (S : CoefficientProfile) (hS : S.Nonnegative)
    (hrec : S.SatisfiesPrefixRecurrence certificateZeta) (n : ℕ) :
    S.g n * certificateZeta ^ n < 1 := by
  have hg_nonnegative : ∀ k, 0 ≤ S.g k := hS.2.2.2.2.1
  have hterm : S.g n * certificateZeta ^ n ≤
      (S.prefixProfile certificateZeta (n + 1)).g := by
    exact weightedTerm_le_prefix (le_of_lt certificateZeta_pos)
      hg_nonnegative n
  let R : PrefixRecurrence certificateZeta :=
    S.toPrefixRecurrence (le_of_lt certificateZeta_pos) hS hrec
  have hprefix : (R.profiles (n + 1)).g < 1 := R.g_lt_one (n + 1)
  exact hterm.trans_lt hprefix

theorem g_lt_9047_div_2000_pow (S : CoefficientProfile) (hS : S.Nonnegative)
    (hrec : S.SatisfiesPrefixRecurrence certificateZeta) (n : ℕ) :
    S.g n < (9047 / 2000 : ℚ) ^ n := by
  have hquotient : S.g n < 1 / certificateZeta ^ n :=
    (lt_div_iff₀ (pow_pos certificateZeta_pos n)).2 <| by
      simpa using S.g_mul_pow_lt_one hS hrec n
  have hinv : certificateZeta⁻¹ = (9047 / 2000 : ℚ) := by
    norm_num [certificateZeta]
  calc
    S.g n < 1 / certificateZeta ^ n := hquotient
    _ = certificateZeta⁻¹ ^ n := by simp only [one_div, inv_pow]
    _ = (9047 / 2000 : ℚ) ^ n := by rw [hinv]

end CoefficientProfile

/--
Final rational pointwise bound.  Its hypotheses now expose the real
combinatorial obligation: `G` must be the `g` sequence of a nonnegative
seventeen-sequence system whose weighted prefixes satisfy Bui's recurrence.
-/
theorem dominatedCoefficient_le_9047_div_2000_pow
    {A : ℕ → ℚ} (S : CoefficientProfile) (hA : ∀ n, A n ≤ S.g n)
    (hS : S.Nonnegative) (hrec : S.SatisfiesPrefixRecurrence certificateZeta)
    (n : ℕ) : A n ≤ (9047 / 2000 : ℚ) ^ n :=
  (hA n).trans (S.g_lt_9047_div_2000_pow hS hrec n).le

end LeanProofs.KlarnerConstant
