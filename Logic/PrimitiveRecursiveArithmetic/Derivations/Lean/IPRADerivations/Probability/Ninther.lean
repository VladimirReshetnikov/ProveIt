import IPRADerivations.Probability.MedianCounts

/-!
# Median of three and Tukey's ninther

Packet: `probability/median_ipra_constructive_proofs`, Theorem `thm:ninther` (and the
median-of-three network before it). With `max(a, b) = a + (b ∸ a)`, `min(a, b) = a ∸ (a ∸ b)` and
the compare-swap network

  `med3(a, b, c) = max(min(a, b), min(max(a, b), c))`,

and the indicator `[a ≤ b] = 1 ∸ sg(a ∸ b)`:

* `med3_spec`: at least two of `a, b, c` are `≤ med3(a, b, c)` and at least two are `≥` it;
* `triple_low`, `triple_high`: for a triple with such a median `m` and any `M`,
  `2 [m ≤ M] ≤ #{triple ≤ M}` and `2 [M ≤ m] ≤ #{triple ≥ M}`;
* `ninther_low`, `ninther_high` (`thm:ninther`): for nine inputs, the ninther
  `M = med3(med3(x₀, x₁, x₂), med3(x₃, x₄, x₅), med3(x₆, x₇, x₈))` has at least four inputs `≤ M`
  and at least four `≥ M`, so for distinct inputs its one-based rank is `4`, `5` or `6`.

Distinctness is not needed for the two count bounds.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.Ninther

open_ipra
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Maximum, minimum and the network -/

/-- `max(a, b) = a + (b ∸ a)`. -/
abbrev mx (a b : PTm n) : PTm n := a + monus b a
/-- `min(a, b) = a ∸ (a ∸ b)`. -/
abbrev mn (a b : PTm n) : PTm n := monus a (monus a b)
/-- The median-of-three compare-swap network. -/
abbrev med3 (a b c : PTm n) : PTm n := mx (mn a b) (mn (mx a b) c)

theorem congrMx {a a' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] mx a b ≐ mx a' b' := congrAdd h₁ (congrMonus h₂ h₁)

theorem congrMn {a a' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] mn a b ≐ mn a' b' := congrMonus h₁ (congrMonus h₁ h₂)

theorem mx_le {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] mx a b ≐ b := (eq_add_of_le h).eqSymm

theorem mx_ge {a b : PTm n} (h : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx] mx a b ≐ a :=
  (congrAdd (.eqRefl _) h).eqTrans (add_zero _)

theorem mn_le {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] mn a b ≐ a :=
  (congrMonus (.eqRefl _) h).eqTrans (monus_zero _)

theorem mn_ge {a b : PTm n} (h : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx] mn a b ≐ b :=
  (congrMonus (eq_add_of_le h) ((congrMonus (eq_add_of_le h) (.eqRefl _)).eqTrans (add_monus' _ _))).eqTrans
    (add_monus _ _)

/-! ## The indicator `[a ≤ b]` -/

/-- `[a ≤ b] = 1 ∸ sg(a ∸ b)`. -/
abbrev leb (a b : PTm n) : PTm n := monus one (sg (monus a b))

theorem leb_one {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] leb a b ≐ one :=
  (congrMonus (.eqRefl _) (sg_le h)).eqTrans (monus_zero _)

theorem leb_zero {a b : PTm n} (h : Γ ⊢[PRAAx] lt b a) : Γ ⊢[PRAAx] leb a b ≐ zero :=
  (congrMonus (.eqRefl _) (sg_lt h)).eqTrans (monus_self _)

/-- `[a ≤ m] ≤ [a ≤ M]` for `m ≤ M`. -/
theorem leb_mono_r {a m M : PTm n} (h : Γ ⊢[PRAAx] le m M) : Γ ⊢[PRAAx] le (leb a m) (leb a M) := by
  refine .orE (lt_or_le m a) ?_ ?_
  · exact le_congr (leb_zero Prf.hyp0).eqSymm (.eqRefl _) (zero_le _)
  · exact le_congr (leb_one Prf.hyp0).eqSymm (leb_one (le_trans Prf.hyp0 h.wk)).eqSymm (le_refl _)

/-- `[m ≤ a] ≤ [M ≤ a]` for `M ≤ m`. -/
theorem leb_mono_l {a m M : PTm n} (h : Γ ⊢[PRAAx] le M m) : Γ ⊢[PRAAx] le (leb m a) (leb M a) := by
  refine .orE (lt_or_le a m) ?_ ?_
  · exact le_congr (leb_zero Prf.hyp0).eqSymm (.eqRefl _) (zero_le _)
  · exact le_congr (leb_one Prf.hyp0).eqSymm (leb_one (le_trans h.wk Prf.hyp0)).eqSymm (le_refl _)

theorem two12 {x y z : PTm n} (hx : Γ ⊢[PRAAx] x ≐ one) (hy : Γ ⊢[PRAAx] y ≐ one) : Γ ⊢[PRAAx] le two (x + y + z) := by
  have a := natEq hx; have b := natEq hy
  refine le_of_eq_add (d := z) ?_
  ipra_lc a + b

theorem two13 {x y z : PTm n} (hx : Γ ⊢[PRAAx] x ≐ one) (hz : Γ ⊢[PRAAx] z ≐ one) : Γ ⊢[PRAAx] le two (x + y + z) := by
  have a := natEq hx; have b := natEq hz
  refine le_of_eq_add (d := y) ?_
  ipra_lc a + b

theorem two23 {x y z : PTm n} (hy : Γ ⊢[PRAAx] y ≐ one) (hz : Γ ⊢[PRAAx] z ≐ one) : Γ ⊢[PRAAx] le two (x + y + z) := by
  have a := natEq hy; have b := natEq hz
  refine le_of_eq_add (d := x) ?_
  ipra_lc a + b

/-- `m` has at least two of `a, b, c` below it and at least two above it. -/
abbrev isMed3 (m a b c : PTm n) : Fm PTm n :=
  le two (leb a m + leb b m + leb c m) ⋏ le two (leb m a + leb m b + leb m c)

/-- `[u ≤ m]` from `u ≤ v` and `m = v`. -/
theorem lo {u v m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ v) (h : Γ ⊢[PRAAx] le u v) : Γ ⊢[PRAAx] leb u m ≐ one :=
  leb_one (le_congr (.eqRefl _) hm.eqSymm h)

/-- `[m ≤ u]` from `v ≤ u` and `m = v`. -/
theorem hi {u v m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ v) (h : Γ ⊢[PRAAx] le v u) : Γ ⊢[PRAAx] leb m u ≐ one :=
  leb_one (le_congr hm.eqSymm (.eqRefl _) h)

/-! ## The six orderings -/

theorem caseA1 {a b c : PTm n} (hab : Γ ⊢[PRAAx] le a b) (hbc : Γ ⊢[PRAAx] le b c) :
    Γ ⊢[PRAAx] isMed3 (med3 a b c) a b c := by
  have hm : Γ ⊢[PRAAx] med3 a b c ≐ b :=
    (congrMx (mn_le hab) ((congrMn (mx_le hab) (.eqRefl _)).eqTrans (mn_le hbc))).eqTrans (mx_le hab)
  exact .andI (two12 (lo hm hab) (lo hm (le_refl b))) (two23 (hi hm (le_refl b)) (hi hm hbc))

theorem caseA2a {a b c : PTm n} (hab : Γ ⊢[PRAAx] le a b) (hcb : Γ ⊢[PRAAx] le c b) (hac : Γ ⊢[PRAAx] le a c) :
    Γ ⊢[PRAAx] isMed3 (med3 a b c) a b c := by
  have hm : Γ ⊢[PRAAx] med3 a b c ≐ c :=
    (congrMx (mn_le hab) ((congrMn (mx_le hab) (.eqRefl _)).eqTrans (mn_ge hcb))).eqTrans (mx_le hac)
  exact .andI (two13 (lo hm hac) (lo hm (le_refl c))) (two23 (hi hm hcb) (hi hm (le_refl c)))

theorem caseA2b {a b c : PTm n} (hab : Γ ⊢[PRAAx] le a b) (hcb : Γ ⊢[PRAAx] le c b) (hca : Γ ⊢[PRAAx] le c a) :
    Γ ⊢[PRAAx] isMed3 (med3 a b c) a b c := by
  have hm : Γ ⊢[PRAAx] med3 a b c ≐ a :=
    (congrMx (mn_le hab) ((congrMn (mx_le hab) (.eqRefl _)).eqTrans (mn_ge hcb))).eqTrans (mx_ge hca)
  exact .andI (two13 (lo hm (le_refl a)) (lo hm hca)) (two12 (hi hm (le_refl a)) (hi hm hab))

theorem caseB1 {a b c : PTm n} (hba : Γ ⊢[PRAAx] le b a) (hac : Γ ⊢[PRAAx] le a c) :
    Γ ⊢[PRAAx] isMed3 (med3 a b c) a b c := by
  have hm : Γ ⊢[PRAAx] med3 a b c ≐ a :=
    (congrMx (mn_ge hba) ((congrMn (mx_ge hba) (.eqRefl _)).eqTrans (mn_le hac))).eqTrans (mx_le hba)
  exact .andI (two12 (lo hm (le_refl a)) (lo hm hba)) (two13 (hi hm (le_refl a)) (hi hm hac))

theorem caseB2a {a b c : PTm n} (hba : Γ ⊢[PRAAx] le b a) (hca : Γ ⊢[PRAAx] le c a) (hbc : Γ ⊢[PRAAx] le b c) :
    Γ ⊢[PRAAx] isMed3 (med3 a b c) a b c := by
  have hm : Γ ⊢[PRAAx] med3 a b c ≐ c :=
    (congrMx (mn_ge hba) ((congrMn (mx_ge hba) (.eqRefl _)).eqTrans (mn_ge hca))).eqTrans (mx_le hbc)
  exact .andI (two23 (lo hm hbc) (lo hm (le_refl c))) (two13 (hi hm hca) (hi hm (le_refl c)))

theorem caseB2b {a b c : PTm n} (hba : Γ ⊢[PRAAx] le b a) (hca : Γ ⊢[PRAAx] le c a) (hcb : Γ ⊢[PRAAx] le c b) :
    Γ ⊢[PRAAx] isMed3 (med3 a b c) a b c := by
  have hm : Γ ⊢[PRAAx] med3 a b c ≐ b :=
    (congrMx (mn_ge hba) ((congrMn (mx_ge hba) (.eqRefl _)).eqTrans (mn_ge hca))).eqTrans (mx_ge hcb)
  exact .andI (two23 (lo hm (le_refl b)) (lo hm hcb)) (two12 (hi hm hba) (hi hm (le_refl b)))

/-- The network computes a median of three: two inputs below and two above. -/
theorem med3_spec (a b c : PTm n) : Γ ⊢[PRAAx] isMed3 (med3 a b c) a b c := by
  refine .orE (le_total a b) ?_ ?_
  · refine .orE (le_total b c) (caseA1 Prf.hyp1 Prf.hyp0) ?_
    exact .orE (le_total a c) (caseA2a Prf.hyp1.wk Prf.hyp1 Prf.hyp0) (caseA2b Prf.hyp1.wk Prf.hyp1 Prf.hyp0)
  · refine .orE (le_total a c) (caseB1 Prf.hyp1 Prf.hyp0) ?_
    exact .orE (le_total b c) (caseB2a Prf.hyp1.wk Prf.hyp1 Prf.hyp0) (caseB2b Prf.hyp1.wk Prf.hyp1 Prf.hyp0)

/-! ## Triples and the ninther -/

/-- `2 [m ≤ M] ≤ [a ≤ M] + [b ≤ M] + [c ≤ M]` when `m` has two of `a, b, c` below it. -/
theorem triple_low {m a b c : PTm n} (hm : Γ ⊢[PRAAx] le two (leb a m + leb b m + leb c m)) (M : PTm n) :
    Γ ⊢[PRAAx] le (two * leb m M) (leb a M + leb b M + leb c M) := by
  refine .orE (lt_or_le M m) ?_ ?_
  · exact le_congr ((congrMul (.eqRefl _) (leb_zero Prf.hyp0)).eqTrans (mul_zero _)).eqSymm (.eqRefl _) (zero_le _)
  · refine le_congr (((congrMul (.eqRefl _) (leb_one Prf.hyp0)).eqTrans (by ipra_ring))).eqSymm (.eqRefl _)
      (le_trans hm.wk ?_)
    exact add_le_add₂ (add_le_add₂ (leb_mono_r Prf.hyp0) (leb_mono_r Prf.hyp0)) (leb_mono_r Prf.hyp0)

/-- `2 [M ≤ m] ≤ [M ≤ a] + [M ≤ b] + [M ≤ c]` when `m` has two of `a, b, c` above it. -/
theorem triple_high {m a b c : PTm n} (hm : Γ ⊢[PRAAx] le two (leb m a + leb m b + leb m c)) (M : PTm n) :
    Γ ⊢[PRAAx] le (two * leb M m) (leb M a + leb M b + leb M c) := by
  refine .orE (lt_or_le m M) ?_ ?_
  · exact le_congr ((congrMul (.eqRefl _) (leb_zero Prf.hyp0)).eqTrans (mul_zero _)).eqSymm (.eqRefl _) (zero_le _)
  · refine le_congr (((congrMul (.eqRefl _) (leb_one Prf.hyp0)).eqTrans (by ipra_ring))).eqSymm (.eqRefl _)
      (le_trans hm.wk ?_)
    exact add_le_add₂ (add_le_add₂ (leb_mono_l Prf.hyp0) (leb_mono_l Prf.hyp0)) (leb_mono_l Prf.hyp0)

theorem combine {T₁ T₂ T₃ l₁ l₂ l₃ : PTm n} (h₁ : Γ ⊢[PRAAx] le (two * l₁) T₁) (h₂ : Γ ⊢[PRAAx] le (two * l₂) T₂)
    (h₃ : Γ ⊢[PRAAx] le (two * l₃) T₃) (h : Γ ⊢[PRAAx] le two (l₁ + l₂ + l₃)) :
    Γ ⊢[PRAAx] le (two * two) (T₁ + T₂ + T₃) := by
  have e₁ := natEq (eq_add_of_le h₁); have e₂ := natEq (eq_add_of_le h₂); have e₃ := natEq (eq_add_of_le h₃)
  refine le_of_eq_add (d := monus T₁ (two * l₁) + monus T₂ (two * l₂) + monus T₃ (two * l₃) +
    two * monus (l₁ + l₂ + l₃) two) ?_
  ipra_lc e₁ + e₂ + e₃ + 2 * natEq (eq_add_of_le h)

/-- The ninther of nine inputs. -/
abbrev ninther (x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ : PTm n) : PTm n :=
  med3 (med3 x₀ x₁ x₂) (med3 x₃ x₄ x₅) (med3 x₆ x₇ x₈)

/-- `thm:ninther`, lower half: at least four inputs are `≤` the ninther. -/
theorem ninther_low (x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ : PTm n) :
    Γ ⊢[PRAAx] le (two * two)
      ((leb x₀ (ninther x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) + leb x₁ (ninther x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) +
          leb x₂ (ninther x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈)) +
        (leb x₃ (ninther x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) + leb x₄ (ninther x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) +
          leb x₅ (ninther x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈)) +
        (leb x₆ (ninther x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) + leb x₇ (ninther x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) +
          leb x₈ (ninther x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈))) :=
  combine (triple_low (Prf.andE₁ (med3_spec x₀ x₁ x₂)) _) (triple_low (Prf.andE₁ (med3_spec x₃ x₄ x₅)) _)
    (triple_low (Prf.andE₁ (med3_spec x₆ x₇ x₈)) _) (Prf.andE₁ (med3_spec _ _ _))

/-- `thm:ninther`, upper half: at least four inputs are `≥` the ninther. -/
theorem ninther_high (x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ : PTm n) :
    Γ ⊢[PRAAx] le (two * two)
      ((leb (ninther x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) x₀ + leb (ninther x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) x₁ +
          leb (ninther x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) x₂) +
        (leb (ninther x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) x₃ + leb (ninther x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) x₄ +
          leb (ninther x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) x₅) +
        (leb (ninther x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) x₆ + leb (ninther x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) x₇ +
          leb (ninther x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) x₈)) :=
  combine (triple_high (Prf.andE₂ (med3_spec x₀ x₁ x₂)) _) (triple_high (Prf.andE₂ (med3_spec x₃ x₄ x₅)) _)
    (triple_high (Prf.andE₂ (med3_spec x₆ x₇ x₈)) _) (Prf.andE₂ (med3_spec _ _ _))

end LeanProofs.IPRA.Probability.Ninther
