import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.Tactic.LinearCombination
import Surreal.HahnSeries.InfiniteProducts

/-!
# Three lemmas on the Tate cubic

This file proves three lemmas of the second proof of Hahn--Tate uniformization in
`docs/surcomplex/hahn-tate-uniformization/article.tex`.

* `tate:node:lem:generic` (Tate's generic-pair lemma): `map_mul_of_generic`, for a
  map `ψ` from any semigroup to an abelian group with infinite image, and the bundled
  homomorphism `homOfGeneric` for a monoid. The source states it for a group; the
  proof only uses associativity.
* `tate:node:lem:infinityvalues` (valuation pattern at infinity):
  `valuation_pattern_at_infinity` and `localParams_valuation` for an arbitrary field
  with an additive valuation in `WithTop Γ`, `Γ` any linearly ordered abelian group,
  and a Tate-normal-form cubic `y² + xy = x³ + a₄x + a₆` with `v(a₄), v(a₆) ≥ 0`. The
  source's proof uses `v(a₄(q)), v(a₆(q)) > 0` (proved here as `orderTop_tateA4_pos`,
  `orderTop_tateA6_pos`); the generic theorem needs only `≥ 0`.
  The instance at the source's curve is `tate_infinity_values`: over
  `K = k⟦Γ⟧` with `v` the least exponent (`orderTop`), the Tate sums `tateSum`
  (`tate:eq:sk`), the coefficients `tateA4`, `tateA6` (`tate:eq:ak`) and the
  Weierstrass curve `tateCurve` (`tate:eq:curve`) are defined here as strong Hahn
  sums, and `orderTop_tateA4_pos`, `orderTop_tateA6_pos` prove `v(a₄(q)), v(a₆(q)) > 0`.
  The Lean statement holds for every field `k` and every `q`, but `tateCurve q` is the
  source's `E_q` only when `v(q) > 0` and `k` has characteristic other than `2` and `3`
  (in particular in the source's characteristic-zero setting). For `v(q) ≤ 0` it is the
  junk cubic `y² + xy = x³` (`tateCurve_of_not_pos`). In characteristic `2` or `3`,
  `(12 : k⟦Γ⟧) = 0`, so `tateA6 q` is Lean's junk value `0` rather than the image of
  Tate's integral series with coefficients `(5m³ + 7m⁵)/12`; the instance there lies
  outside the source's setting, although `valuation_pattern_at_infinity` still applies
  to any genuine integral `a₆`.
  The value `ε` is produced by integer linear combinations, without division in `Γ`.
* `tate:node:lem:nodalnormalization` (normalization of the special cubic):
  `existsUnique_specialCubic_param`, `specialCubic_param_eq` and the equivalence
  `nodalNormalization` between `k^× \ {1}` and the points `≠ (0,0)` of
  `y² + xy = x³`, with inverse `(x, y) ↦ y/(x + y)`, over an arbitrary field `k`
  (the source's standing hypothesis of characteristic zero is not needed).

The Tate sums are defined for every `q`: the period enters through `cutPeriod q`,
which is `q` when `v(q) > 0` (the source's standing hypothesis) and `0` otherwise, so
that `tateFamily_apply_of_pos` recovers the source's summands
`n^j q^n/(1 - q^n)`, `n ≥ 1`, exactly when `v(q) > 0`. Summability of the family is
`Surreal.HahnSeries.ratioFamily` (positive-support calculus).

Nothing is pending for these three lemmas. Their uses (the formal inverse at infinity
`tate:node:prop:infinity`, the smooth-residue inverse `tate:node:prop:smooth`, the
constructive surjectivity `tate:node:thm:surjectivity` and the group law
`tate:node:thm:group`) are not formalized here. Neither is `tate:prop:discriminant`
(`Δ(q) ≠ 0`), which makes `E_q` an elliptic curve: `tateCurve q` is only a
`WeierstrassCurve`.
-/

namespace Surreal.TateNode

open _root_.HahnSeries

/-! ### Tate's generic-pair lemma -/

section GenericPair

variable {G A : Type*} [AddCommGroup A]

/-- `tate:node:lem:generic` (Tate's generic-pair lemma), at semigroup generality: if
`ψ : G → A` has infinite image and `ψ (a * b) = ψ a + ψ b` whenever `ψ a ≠ ± ψ b`,
then `ψ (a * b) = ψ a + ψ b` for all `a, b`. The proof chooses `c` whose image avoids
`± ψ a`, `± ψ b - ψ a` and `± ψ (a * b)`, and cancels `ψ c`. -/
theorem map_mul_of_generic [Semigroup G] (ψ : G → A) (hinf : (Set.range ψ).Infinite)
    (h : ∀ a b, ψ a ≠ ψ b → ψ a ≠ -ψ b → ψ (a * b) = ψ a + ψ b) (a b : G) :
    ψ (a * b) = ψ a + ψ b := by
  classical
  obtain ⟨_, ⟨c, rfl⟩, hc⟩ := hinf.exists_notMem_finset
    {ψ a, -ψ a, ψ b - ψ a, -ψ b - ψ a, ψ (a * b), -ψ (a * b)}
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
  have hca : ψ (c * a) = ψ c + ψ a := h c a h1 h2
  have hcab : ψ (c * a * b) = ψ (c * a) + ψ b := by
    refine h _ b ?_ ?_ <;> rw [hca] <;> intro e
    · exact h3 (eq_sub_of_add_eq e)
    · exact h4 (eq_sub_of_add_eq e)
  have hc_ab : ψ (c * (a * b)) = ψ c + ψ (a * b) := h c _ h5 h6
  rw [mul_assoc, hc_ab, hca, add_assoc] at hcab
  exact add_left_cancel hcab

/-- `tate:node:lem:generic`, bundled: under the hypotheses of the generic-pair lemma,
a map from a monoid to an abelian group is a monoid homomorphism into
`Multiplicative A`. -/
def homOfGeneric [Monoid G] (ψ : G → A) (hinf : (Set.range ψ).Infinite)
    (h : ∀ a b, ψ a ≠ ψ b → ψ a ≠ -ψ b → ψ (a * b) = ψ a + ψ b) : G →* Multiplicative A :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd (ψ g)) fun a b => by
    rw [map_mul_of_generic ψ hinf h a b, ofAdd_add]

@[simp]
theorem homOfGeneric_apply [Monoid G] (ψ : G → A) (hinf : (Set.range ψ).Infinite)
    (h : ∀ a b, ψ a ≠ ψ b → ψ a ≠ -ψ b → ψ (a * b) = ψ a + ψ b) (g : G) :
    homOfGeneric ψ hinf h g = Multiplicative.ofAdd (ψ g) :=
  rfl

end GenericPair

/-! ### The valuation pattern at infinity -/

section InfinityValues

variable {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- `tate:node:lem:infinityvalues`, for any additively valued field: if
`y² + xy = x³ + a₄x + a₆` with `v(a₄), v(a₆) ≥ 0` and one of `x, y` has negative
valuation, then `v(x) = -2ε` and `v(y) = -3ε` for some `ε > 0`. -/
theorem valuation_pattern_at_infinity (v : AddValuation K (WithTop Γ)) {a₄ a₆ x y : K}
    (h₄ : 0 ≤ v a₄) (h₆ : 0 ≤ v a₆) (hE : y ^ 2 + x * y = x ^ 3 + a₄ * x + a₆)
    (hneg : v x < 0 ∨ v y < 0) :
    ∃ ε : Γ, 0 < ε ∧ v x = ((-(2 • ε) : Γ) : WithTop Γ) ∧
      v y = ((-(3 • ε) : Γ) : WithTop Γ) := by
  have hE' : y * y + x * y = x * x * x + a₄ * x + a₆ := by
    rw [show y * y = y ^ 2 by ring, show x * x * x = x ^ 3 by ring]
    exact hE
  -- A negative coordinate forces `v x < 0`.
  have hx : v x < 0 := by
    by_contra hx0
    rw [not_lt] at hx0
    have hy : v y < 0 := hneg.resolve_left (not_lt.mpr hx0)
    have hR : 0 ≤ v (x * x * x + a₄ * x + a₆) := by
      refine v.map_le_add (v.map_le_add ?_ ?_) h₆
      · rw [v.map_mul, v.map_mul]
        exact add_nonneg (add_nonneg hx0 hx0) hx0
      · rw [v.map_mul]
        exact add_nonneg h₄ hx0
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hy.ne_top
    rw [← hb] at hy
    have hb0 : b < 0 := by exact_mod_cast hy
    have hlt : v (y * y) < v (x * y) := by
      rw [v.map_mul, v.map_mul, ← hb]
      exact WithTop.add_lt_add_right WithTop.coe_ne_top (hy.trans_le hx0)
    rw [← hE', v.map_add_eq_of_lt_left hlt, v.map_mul, ← hb] at hR
    have : (0 : Γ) ≤ b + b := by exact_mod_cast hR
    exact absurd this (not_le.mpr (add_neg hb0 hb0))
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hx.ne_top
  have ha0 : a < 0 := by
    rw [← ha] at hx
    exact_mod_cast hx
  -- The right side has valuation `3a`.
  have hR : v (x * x * x + a₄ * x + a₆) = ((a + a + a : Γ) : WithTop Γ) := by
    have h3 : v (x * x * x) = ((a + a + a : Γ) : WithTop Γ) := by
      rw [v.map_mul, v.map_mul, ← ha]
      norm_cast
    have hlt1 : v (x * x * x) < v (a₄ * x) := by
      rw [h3, v.map_mul, ← ha]
      calc ((a + a + a : Γ) : WithTop Γ) < (a : WithTop Γ) := by
            exact_mod_cast add_lt_of_neg_left a (add_neg ha0 ha0)
        _ ≤ v a₄ + a := le_add_of_nonneg_left h₄
    have hlt2 : v (x * x * x + a₄ * x) < v a₆ := by
      rw [v.map_add_eq_of_lt_left hlt1, h3]
      refine lt_of_lt_of_le ?_ h₆
      exact_mod_cast add_neg (add_neg ha0 ha0) ha0
    rw [v.map_add_eq_of_lt_left hlt2, v.map_add_eq_of_lt_left hlt1, h3]
  -- Hence `y ≠ 0`.
  have hyne : v y ≠ ⊤ := by
    intro hy
    have hy0 : y = 0 := v.top_iff.mp hy
    have h0 : v (x * x * x + a₄ * x + a₆) = ⊤ := by
      rw [← hE', hy0, mul_zero, mul_zero, add_zero, v.map_zero]
    rw [hR] at h0
    exact WithTop.coe_ne_top h0
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hyne
  -- `v y < v x`, otherwise the left side would have valuation at least `2a > 3a`.
  have hba : b < a := by
    by_contra hab
    rw [not_lt] at hab
    have hL : ((a + a : Γ) : WithTop Γ) ≤ v (y * y + x * y) := by
      refine v.map_le_add ?_ ?_
      · rw [v.map_mul, ← hb]
        exact_mod_cast add_le_add hab hab
      · rw [v.map_mul, ← ha, ← hb]
        exact_mod_cast add_le_add_right hab a
    rw [hE', hR] at hL
    have : a + a ≤ a + a + a := by exact_mod_cast hL
    exact absurd this (not_le.mpr (add_lt_of_neg_right _ ha0))
  -- Therefore `y²` dominates and `2b = 3a`.
  have hL : v (y * y + x * y) = ((b + b : Γ) : WithTop Γ) := by
    have hlt : v (y * y) < v (x * y) := by
      rw [v.map_mul, v.map_mul, ← ha, ← hb]
      exact_mod_cast add_lt_add_of_lt_of_le hba le_rfl
    rw [v.map_add_eq_of_lt_left hlt, v.map_mul, ← hb]
    norm_cast
  have hab : b + b = a + a + a := by
    rw [hE', hR] at hL
    exact (WithTop.coe_eq_coe.mp hL).symm
  refine ⟨a - b, sub_pos.mpr hba, ?_, ?_⟩
  · rw [← ha]
    refine congrArg _ ?_
    calc a = (a + a + a) - (a + a) := by abel
      _ = (b + b) - (a + a) := by rw [hab]
      _ = -(2 • (a - b)) := by abel
  · rw [← hb]
    refine congrArg _ ?_
    calc b = (b + b + b) - (b + b) := by abel
      _ = (b + b + b) - (a + a + a) := by rw [hab]
      _ = -(3 • (a - b)) := by abel

/-- `tate:node:lem:infinityvalues`, second clause, with exact values: in the situation
of `valuation_pattern_at_infinity`, the local parameters `z = -x/y` and `r = -1/y` at
infinity have valuations `ε` and `3ε`. -/
theorem localParams_valuation (v : AddValuation K (WithTop Γ)) {a₄ a₆ x y : K}
    (h₄ : 0 ≤ v a₄) (h₆ : 0 ≤ v a₆) (hE : y ^ 2 + x * y = x ^ 3 + a₄ * x + a₆)
    (hneg : v x < 0 ∨ v y < 0) :
    ∃ ε : Γ, 0 < ε ∧ v x = ((-(2 • ε) : Γ) : WithTop Γ) ∧
      v y = ((-(3 • ε) : Γ) : WithTop Γ) ∧ v (-x / y) = (ε : WithTop Γ) ∧
      v (-1 / y) = ((3 • ε : Γ) : WithTop Γ) := by
  obtain ⟨ε, hε, hx, hy⟩ := valuation_pattern_at_infinity v h₄ h₆ hE hneg
  refine ⟨ε, hε, hx, hy, ?_, ?_⟩
  · rw [v.map_div, v.map_neg, hx, hy, ← WithTop.LinearOrderedAddCommGroup.coe_sub]
    refine congrArg _ ?_
    abel
  · rw [v.map_div, v.map_neg, v.map_one, hy, ← WithTop.coe_zero,
      ← WithTop.LinearOrderedAddCommGroup.coe_sub]
    refine congrArg _ ?_
    abel

/-- `tate:node:lem:infinityvalues`, second clause: `z = -x/y` and `r = -1/y` lie in the
maximal ideal `𝔪_v`. -/
theorem localParams_pos (v : AddValuation K (WithTop Γ)) {a₄ a₆ x y : K}
    (h₄ : 0 ≤ v a₄) (h₆ : 0 ≤ v a₆) (hE : y ^ 2 + x * y = x ^ 3 + a₄ * x + a₆)
    (hneg : v x < 0 ∨ v y < 0) :
    0 < v (-x / y) ∧ 0 < v (-1 / y) := by
  obtain ⟨ε, hε, -, -, hz, hr⟩ := localParams_valuation v h₄ h₆ hE hneg
  rw [hz, hr]
  exact ⟨by exact_mod_cast hε, by exact_mod_cast nsmul_pos hε three_ne_zero⟩

end InfinityValues

/-! ### The Tate coefficients over a Hahn field -/

section TateCoefficients

variable {Γ k : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field k]

noncomputable section

/-- The period entering the Tate sums: `q` when `v(q) > 0`, the source's standing
hypothesis, and `0` otherwise (a junk value that makes the sums total). -/
def cutPeriod (q : k⟦Γ⟧) : k⟦Γ⟧ := if 0 < q.orderTop then q else 0

omit [IsOrderedAddMonoid Γ] in
theorem cutPeriod_of_pos {q : k⟦Γ⟧} (hq : 0 < q.orderTop) : cutPeriod q = q :=
  if_pos hq

omit [IsOrderedAddMonoid Γ] in
theorem orderTop_cutPeriod_pos (q : k⟦Γ⟧) : 0 < (cutPeriod q).orderTop := by
  unfold cutPeriod
  split_ifs with hq
  · exact hq
  · rw [orderTop_zero]
    exact WithTop.top_pos

/-- The strongly summable family `n ↦ q^(n+1)` of positive powers of the period. -/
def periodPowers (q : k⟦Γ⟧) : SummableFamily Γ k ℕ :=
  cutPeriod q • SummableFamily.powers (cutPeriod q)

theorem periodPowers_apply (q : k⟦Γ⟧) (n : ℕ) : periodPowers q n = cutPeriod q ^ (n + 1) := by
  rw [periodPowers, SummableFamily.smul_apply, of_symm_smul_of_eq_mul,
    SummableFamily.powers_of_orderTop_pos (orderTop_cutPeriod_pos q), pow_succ']

theorem orderTop_periodPowers_pos (q : k⟦Γ⟧) (n : ℕ) : 0 < (periodPowers q n).orderTop := by
  rw [periodPowers_apply, pow_succ', ← addVal_apply, AddValuation.map_mul,
    AddValuation.map_pow, addVal_apply]
  exact add_pos_of_pos_of_nonneg (orderTop_cutPeriod_pos q)
    (nsmul_nonneg (orderTop_cutPeriod_pos q).le n)

/-- The strongly summable family `n ↦ (n + 1)^j q^(n+1)/(1 - q^(n+1))` whose sum is the
Tate sum `s_j(q)` of `tate:eq:sk`. -/
def tateFamily (j : ℕ) (q : k⟦Γ⟧) : SummableFamily Γ k ℕ :=
  SummableFamily.smulFamily (fun n : ℕ => ((n + 1 : ℕ) : k) ^ j)
    (Surreal.HahnSeries.ratioFamily (periodPowers q) (orderTop_periodPowers_pos q) id)

theorem tateFamily_apply (j : ℕ) (q : k⟦Γ⟧) (n : ℕ) :
    tateFamily j q n =
      ((n + 1 : ℕ) : k) ^ j • (cutPeriod q ^ (n + 1) / (1 - cutPeriod q ^ (n + 1))) := by
  change ((n + 1 : ℕ) : k) ^ j • Surreal.HahnSeries.ratioFamily (periodPowers q)
    (orderTop_periodPowers_pos q) id n = _
  rw [Surreal.HahnSeries.ratioFamily_id_apply, periodPowers_apply, div_eq_mul_inv]

/-- For `v(q) > 0` the summands are the source's `n^j q^n/(1 - q^n)`, `n ≥ 1`. -/
theorem tateFamily_apply_of_pos (j : ℕ) {q : k⟦Γ⟧} (hq : 0 < q.orderTop) (n : ℕ) :
    tateFamily j q n = ((n + 1 : ℕ) : k) ^ j • (q ^ (n + 1) / (1 - q ^ (n + 1))) := by
  rw [tateFamily_apply, cutPeriod_of_pos hq]

theorem orderTop_tateFamily_pos (j : ℕ) (q : k⟦Γ⟧) (n : ℕ) :
    0 < (tateFamily j q n).orderTop := by
  rw [tateFamily_apply]
  refine lt_of_lt_of_le ?_ (not_lt.mp (orderTop_smul_not_lt _ _))
  have hp := orderTop_periodPowers_pos q n
  rw [periodPowers_apply] at hp
  set p := cutPeriod q ^ (n + 1)
  have h1 : addVal Γ k (1 - p) = 0 := by
    rw [AddValuation.map_sub_eq_of_lt_left _ (by rw [AddValuation.map_one, addVal_apply]; exact hp),
      AddValuation.map_one]
  rw [← addVal_apply, AddValuation.map_div, h1, sub_zero, addVal_apply]
  exact hp

/-- `tate:eq:sk`: the Tate sum `s_j(q) = ∑_{n ≥ 1} n^j q^n/(1 - q^n)`, a strong Hahn
sum, for `v(q) > 0`; for `v(q) ≤ 0` it is `0` by the convention of `cutPeriod`
(`tateSum_of_not_pos`). -/
def tateSum (j : ℕ) (q : k⟦Γ⟧) : k⟦Γ⟧ := (tateFamily j q).hsum

theorem orderTop_tateSum_pos (j : ℕ) (q : k⟦Γ⟧) : 0 < (tateSum j q).orderTop :=
  Surreal.HahnSeries.orderTop_pos_of_support_pos fun g hg => by
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (SummableFamily.support_hsum_subset hg)
    exact Surreal.HahnSeries.support_pos_of_orderTop_pos (orderTop_tateFamily_pos j q n) g hn

/-- `tate:eq:ak`: `a₄(q) = -5 s₃(q)`. -/
def tateA4 (q : k⟦Γ⟧) : k⟦Γ⟧ := -5 * tateSum 3 q

/-- `tate:eq:ak`: `a₆(q) = -(5 s₃(q) + 7 s₅(q))/12`. The source works in characteristic
zero; in characteristic `2` or `3` we have `12 = 0`, so the division is Lean's junk
value `0` (not the image of Tate's integral series), and the positivity
`orderTop_tateA6_pos` still holds. -/
def tateA6 (q : k⟦Γ⟧) : k⟦Γ⟧ := -(5 * tateSum 3 q + 7 * tateSum 5 q) / 12

/-- `tate:eq:curve`: the Tate cubic `E_q : y² + xy = x³ + a₄(q)x + a₆(q)`. It is the
source's `E_q` when `v(q) > 0` and `k` has characteristic other than `2` and `3`; for
`v(q) ≤ 0` it is the junk cubic `y² + xy = x³` (`tateCurve_of_not_pos`). -/
def tateCurve (q : k⟦Γ⟧) : WeierstrassCurve k⟦Γ⟧ := ⟨1, 0, 0, tateA4 q, tateA6 q⟩

/-- For `v(q) ≤ 0` the Tate sums vanish (the junk convention of `cutPeriod`). -/
theorem tateSum_of_not_pos (j : ℕ) {q : k⟦Γ⟧} (hq : ¬0 < q.orderTop) : tateSum j q = 0 := by
  have h : tateFamily j q = 0 := by
    ext n : 1
    rw [SummableFamily.zero_apply, tateFamily_apply, cutPeriod, if_neg hq,
      zero_pow n.succ_ne_zero, zero_div, smul_zero]
  rw [tateSum, h, SummableFamily.hsum_zero]

/-- For `v(q) ≤ 0`, `tateCurve q` is the junk cubic `y² + xy = x³`, not a Tate curve. -/
theorem tateCurve_of_not_pos {q : k⟦Γ⟧} (hq : ¬0 < q.orderTop) :
    tateCurve q = ⟨1, 0, 0, 0, 0⟩ := by
  rw [tateCurve, tateA4, tateA6, tateSum_of_not_pos 3 hq, tateSum_of_not_pos 5 hq]
  simp

theorem tateCurve_equation_iff (q x y : k⟦Γ⟧) :
    (tateCurve q).toAffine.Equation x y ↔ y ^ 2 + x * y = x ^ 3 + tateA4 q * x + tateA6 q := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [tateCurve, one_mul, zero_mul, add_zero]

theorem orderTop_C_mul_pos (r : k) {x : k⟦Γ⟧} (hx : 0 < x.orderTop) :
    0 < (C r * x).orderTop := by
  rw [C_mul_eq_smul]
  exact lt_of_lt_of_le hx (not_lt.mp (orderTop_smul_not_lt _ _))

/-- The coefficient `a₄(q)` has positive valuation. -/
theorem orderTop_tateA4_pos (q : k⟦Γ⟧) : 0 < (tateA4 q).orderTop := by
  have h : tateA4 q = C (-5 : k) * tateSum 3 q := by
    rw [tateA4, map_neg, map_ofNat]
  rw [h]
  exact orderTop_C_mul_pos _ (orderTop_tateSum_pos 3 q)

/-- The coefficient `a₆(q)` has positive valuation. -/
theorem orderTop_tateA6_pos (q : k⟦Γ⟧) : 0 < (tateA6 q).orderTop := by
  have h : tateA6 q = C (-(12 : k)⁻¹) * (C 5 * tateSum 3 q + C 7 * tateSum 5 q) := by
    rw [tateA6, map_neg, map_inv₀, map_ofNat, map_ofNat, map_ofNat]
    ring
  rw [h]
  refine orderTop_C_mul_pos _ (lt_of_lt_of_le ?_ min_orderTop_le_orderTop_add)
  exact lt_min (orderTop_C_mul_pos _ (orderTop_tateSum_pos 3 q))
    (orderTop_C_mul_pos _ (orderTop_tateSum_pos 5 q))

/-- `tate:node:lem:infinityvalues` over `K = k⟦Γ⟧` with `v` the least exponent: if an
affine point `(x, y)` of the Tate cubic `tateCurve q` has a coordinate of negative
valuation, then `v(x) = -2ε`, `v(y) = -3ε` for some `ε > 0`, and `z = -x/y`, `r = -1/y`
have valuations `ε` and `3ε`, in particular they lie in `𝔪_v`. For `0 < v(q)`, the
source's standing hypothesis, and `k` of characteristic other than `2` and `3`,
`tateCurve q` is the source's `E_q` (see `cutPeriod_of_pos` and
`tateFamily_apply_of_pos`); otherwise it is a junk cubic (for `v(q) ≤ 0` it is
`y² + xy = x³`, `tateCurve_of_not_pos`) and the statement still holds. -/
theorem tate_infinity_values {q x y : k⟦Γ⟧} (hE : (tateCurve q).toAffine.Equation x y)
    (hneg : x.orderTop < 0 ∨ y.orderTop < 0) :
    ∃ ε : Γ, 0 < ε ∧ x.orderTop = ((-(2 • ε) : Γ) : WithTop Γ) ∧
      y.orderTop = ((-(3 • ε) : Γ) : WithTop Γ) ∧ (-x / y).orderTop = (ε : WithTop Γ) ∧
      (-1 / y).orderTop = ((3 • ε : Γ) : WithTop Γ) := by
  rw [tateCurve_equation_iff] at hE
  have h₄ : 0 ≤ addVal Γ k (tateA4 q) := by
    rw [addVal_apply]
    exact (orderTop_tateA4_pos q).le
  have h₆ : 0 ≤ addVal Γ k (tateA6 q) := by
    rw [addVal_apply]
    exact (orderTop_tateA6_pos q).le
  simpa only [addVal_apply] using
    localParams_valuation (addVal Γ k) h₄ h₆ hE (by simpa only [addVal_apply] using hneg)

/-- `tate:node:lem:infinityvalues` over `K = k⟦Γ⟧`, second clause: for an affine point
`(x, y)` of `tateCurve q` with a coordinate of negative valuation, `z = -x/y` and
`r = -1/y` lie in `𝔪_v`. As in `tate_infinity_values`, `tateCurve q` is the source's
`E_q` for `0 < v(q)` and `k` of characteristic other than `2` and `3`; otherwise it is a
junk cubic (for `v(q) ≤ 0` it is `y² + xy = x³`) and the statement still holds. -/
theorem tate_localParams_pos {q x y : k⟦Γ⟧} (hE : (tateCurve q).toAffine.Equation x y)
    (hneg : x.orderTop < 0 ∨ y.orderTop < 0) :
    0 < (-x / y).orderTop ∧ 0 < (-1 / y).orderTop := by
  obtain ⟨ε, hε, -, -, hz, hr⟩ := tate_infinity_values hE hneg
  rw [hz, hr]
  exact ⟨by exact_mod_cast hε, by exact_mod_cast nsmul_pos hε three_ne_zero⟩

end

end TateCoefficients

/-! ### Normalization of the special nodal cubic -/

section NodalNormalization

variable {k : Type*} [Field k]

/-- Away from the node, a point of `y² + xy = x³` has `x`, `y` and `x + y` nonzero. -/
theorem specialCubic_ne_zero {x y : k} (h : y ^ 2 + x * y = x ^ 3) (hne : (x, y) ≠ (0, 0)) :
    x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 := by
  have hx : x ≠ 0 := by
    rintro rfl
    apply hne
    have hy : y ^ 2 = 0 := by simpa using h
    rw [pow_eq_zero_iff two_ne_zero] at hy
    rw [hy]
  refine ⟨hx, ?_, ?_⟩
  · rintro rfl
    apply hx
    have h3 : x ^ 3 = 0 := by simpa using h.symm
    exact (pow_eq_zero_iff three_ne_zero).mp h3
  · intro hxy
    apply hx
    have h3 : x ^ 3 = 0 := by linear_combination -h + y * hxy
    exact (pow_eq_zero_iff three_ne_zero).mp h3

/-- Every `c ≠ 0, 1` gives the point `(c/(1-c)², c²/(1-c)³) ≠ (0,0)` of `y² + xy = x³`,
and `c` is recovered as `y/(x + y)`. -/
theorem specialCubic_param {c : k} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    (c ^ 2 / (1 - c) ^ 3) ^ 2 + c / (1 - c) ^ 2 * (c ^ 2 / (1 - c) ^ 3) =
        (c / (1 - c) ^ 2) ^ 3 ∧
      (c / (1 - c) ^ 2, c ^ 2 / (1 - c) ^ 3) ≠ ((0 : k), (0 : k)) ∧
      c ^ 2 / (1 - c) ^ 3 / (c / (1 - c) ^ 2 + c ^ 2 / (1 - c) ^ 3) = c := by
  have hd : 1 - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    ring
  · intro h
    exact div_ne_zero hc0 (pow_ne_zero 2 hd) (Prod.mk.inj h).1
  · have hs : c / (1 - c) ^ 2 + c ^ 2 / (1 - c) ^ 3 = c / (1 - c) ^ 3 := by
      field_simp
      ring
    rw [hs, div_div_div_cancel_right₀ (pow_ne_zero 3 hd), sq, mul_div_cancel_right₀ _ hc0]

/-- Every point `≠ (0,0)` of `y² + xy = x³` is `(c/(1-c)², c²/(1-c)³)` for the parameter
`c = y/(x + y)`, which is neither `0` nor `1`. -/
theorem specialCubic_eq_param {x y : k} (h : y ^ 2 + x * y = x ^ 3) (hne : (x, y) ≠ (0, 0)) :
    y / (x + y) ≠ 0 ∧ y / (x + y) ≠ 1 ∧
      x = y / (x + y) / (1 - y / (x + y)) ^ 2 ∧
      y = (y / (x + y)) ^ 2 / (1 - y / (x + y)) ^ 3 := by
  obtain ⟨hx, hy, hs⟩ := specialCubic_ne_zero h hne
  have h1 : 1 - y / (x + y) = x / (x + y) := by
    rw [one_sub_div hs, add_sub_cancel_right]
  refine ⟨div_ne_zero hy hs, ?_, ?_, ?_⟩
  · intro h1'
    rw [div_eq_one_iff_eq hs] at h1'
    exact hx (by linear_combination -h1')
  · rw [h1]
    field_simp
    linear_combination -h
  · rw [h1]
    field_simp
    linear_combination -h

/-- `tate:node:lem:nodalnormalization`, the parameter: if `c ≠ 0, 1` and
`(x, y) = (c/(1-c)², c²/(1-c)³)`, then `c = y/(x + y)`. -/
theorem specialCubic_param_eq {c x y : k} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (hx : x = c / (1 - c) ^ 2) (hy : y = c ^ 2 / (1 - c) ^ 3) : c = y / (x + y) := by
  rw [hx, hy]
  exact ((specialCubic_param hc0 hc1).2.2).symm

/-- `tate:node:lem:nodalnormalization`: every point `(x, y) ≠ (0,0)` of `y² + xy = x³`
over a field is uniquely of the form `(c/(1-c)², c²/(1-c)³)` with `c ∈ k^× \ {1}`; the
parameter is `c = y/(x + y)` (`specialCubic_param_eq`). -/
theorem existsUnique_specialCubic_param {x y : k} (h : y ^ 2 + x * y = x ^ 3)
    (hne : (x, y) ≠ (0, 0)) :
    ∃! c : k, c ≠ 0 ∧ c ≠ 1 ∧ x = c / (1 - c) ^ 2 ∧ y = c ^ 2 / (1 - c) ^ 3 := by
  obtain ⟨h0, h1, hx, hy⟩ := specialCubic_eq_param h hne
  refine ⟨y / (x + y), ⟨h0, h1, hx, hy⟩, ?_⟩
  rintro c ⟨hc0, hc1, hcx, hcy⟩
  exact specialCubic_param_eq hc0 hc1 hcx hcy

/-- `tate:node:lem:nodalnormalization`, bundled: `c ↦ (c/(1-c)², c²/(1-c)³)` is a bijection
from `k^× \ {1}` onto the points `≠ (0,0)` of `y² + xy = x³`, with inverse
`(x, y) ↦ y/(x + y)`. -/
def nodalNormalization (k : Type*) [Field k] :
    {c : k // c ≠ 0 ∧ c ≠ 1} ≃
      {p : k × k // p.2 ^ 2 + p.1 * p.2 = p.1 ^ 3 ∧ p ≠ (0, 0)} where
  toFun c := ⟨(c.1 / (1 - c.1) ^ 2, c.1 ^ 2 / (1 - c.1) ^ 3),
    (specialCubic_param c.2.1 c.2.2).1, (specialCubic_param c.2.1 c.2.2).2.1⟩
  invFun p := ⟨p.1.2 / (p.1.1 + p.1.2), (specialCubic_eq_param p.2.1 p.2.2).1,
    (specialCubic_eq_param p.2.1 p.2.2).2.1⟩
  left_inv c := Subtype.ext (specialCubic_param c.2.1 c.2.2).2.2
  right_inv p := Subtype.ext (Prod.ext (specialCubic_eq_param p.2.1 p.2.2).2.2.1.symm
    (specialCubic_eq_param p.2.1 p.2.2).2.2.2.symm)

@[simp]
theorem nodalNormalization_apply (c : {c : k // c ≠ 0 ∧ c ≠ 1}) :
    (nodalNormalization k c : k × k) = (c.1 / (1 - c.1) ^ 2, c.1 ^ 2 / (1 - c.1) ^ 3) :=
  rfl

@[simp]
theorem nodalNormalization_symm_apply
    (p : {p : k × k // p.2 ^ 2 + p.1 * p.2 = p.1 ^ 3 ∧ p ≠ (0, 0)}) :
    ((nodalNormalization k).symm p : k) = p.1.2 / (p.1.1 + p.1.2) :=
  rfl

end NodalNormalization

end Surreal.TateNode
