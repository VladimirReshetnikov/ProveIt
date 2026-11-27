import IPRADerivations.AnalyticNumberTheory.SymmetryBound

/-!
# The natural distance `|a − b|` (`pnt_ipra_constructive_2026-11-14`, towards `sb:weighted-sum`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `lean_plan.tex` §"An exact arithmetic statement":
"`dist(a, b) = (a ∸ b) + (b ∸ a)`, where `∸` is truncated subtraction". Selberg's weighted inequality
(`selberg.tex`, `sb:weighted-sum`) and its successors take absolute values `|R(x/n)|` inside finite sums, so they
need the distance as a term. This module develops its order calculus once:

* `absd_le`: `a ≤ b + c` and `b ≤ a + c` give `|a − b| ≤ c`; `le_absd_l`/`le_absd_r`: `a ≤ b + |a − b|`,
  `b ≤ a + |a − b|` — together, `|a − b| ≤ c` is equivalent to the two one-sided bounds;
* `absd_symm`, `absd_triangle`, `absd_add` (`|(a + b) − (c + d)| ≤ |a − c| + |b − d|`), `absd_scale`
  (`|ka − kb| ≤ k|a − b|`), `scale_absd` (`k|a − b| ≤ |ka − kb|`), `absd_shift` (`|(a + e) − (b + e)| ≤ |a − b|`);
* `absd_sum`: `|Σ f − Σ g| ≤ Σ |f − g|` for two sum bodies with a common parameter.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff

open_ipra exports

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `|a − b| = (a ∸ b) + (b ∸ a)`. -/
abbrev absd (a b : PTm n) : PTm n := monus a b + monus b a

theorem absd_le {a b c : PTm n} (h₁ : Γ ⊢[PRAAx] le a (b + c)) (h₂ : Γ ⊢[PRAAx] le b (a + c)) :
    Γ ⊢[PRAAx] le (absd a b) c := by
  refine .orE (le_total a b) ?_ ?_
  · exact le_congr ((congrAdd Prf.hyp0 (.eqRefl _)).eqTrans (zero_add _)).eqSymm (.eqRefl _)
      (Order.monus_le_of_le_add h₂.wk)
  · exact le_congr ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _)).eqSymm (.eqRefl _)
      (Order.monus_le_of_le_add h₁.wk)

theorem le_absd_l (a b : PTm n) : Γ ⊢[PRAAx] le a (b + absd a b) := by
  refine .orE (le_total a b) ?_ ?_
  · have hab : (le a b :: Γ) ⊢[PRAAx] le a b := Prf.hyp0
    have e := natEq (eq_add_of_le hab)
    ipra_le 𝔞 (monus a b) + 2 * 𝔞 (monus b a) with e
  · have hba : (le b a :: Γ) ⊢[PRAAx] le b a := Prf.hyp0
    have e := natEq (eq_add_of_le hba)
    ipra_le 𝔞 (monus b a) with e

theorem le_absd_r (a b : PTm n) : Γ ⊢[PRAAx] le b (a + absd a b) := by
  have h := le_absd_l (Γ := Γ) b a
  ipra_le sl h

theorem absd_symm (a b : PTm n) : Γ ⊢[PRAAx] absd a b ≐ absd b a := add_comm _ _

theorem absd_triangle (a b c : PTm n) : Γ ⊢[PRAAx] le (absd a c) (absd a b + absd b c) := by
  have p := le_absd_l (Γ := Γ) a b; have q := le_absd_l (Γ := Γ) b c
  have p' := le_absd_r (Γ := Γ) a b; have q' := le_absd_r (Γ := Γ) b c
  exact absd_le (by ipra_le sl p + sl q) (by ipra_le sl p' + sl q')

theorem absd_add (a b c d : PTm n) : Γ ⊢[PRAAx] le (absd (a + b) (c + d)) (absd a c + absd b d) := by
  have p := le_absd_l (Γ := Γ) a c; have q := le_absd_l (Γ := Γ) b d
  have p' := le_absd_r (Γ := Γ) a c; have q' := le_absd_r (Γ := Γ) b d
  exact absd_le (by ipra_le sl p + sl q) (by ipra_le sl p' + sl q')

theorem absd_shift (a b e : PTm n) : Γ ⊢[PRAAx] le (absd (a + e) (b + e)) (absd a b) := by
  have p := le_absd_l (Γ := Γ) a b; have p' := le_absd_r (Γ := Γ) a b
  exact absd_le (by ipra_le sl p) (by ipra_le sl p')

theorem absd_scale (k a b : PTm n) : Γ ⊢[PRAAx] le (absd (k * a) (k * b)) (k * absd a b) := by
  have p := le_scale k (le_absd_l (Γ := Γ) a b); have p' := le_scale k (le_absd_r (Γ := Γ) a b)
  exact absd_le (by ipra_le sl p) (by ipra_le sl p')

theorem scale_absd (k a b : PTm n) : Γ ⊢[PRAAx] le (k * absd a b) (absd (k * a) (k * b)) := by
  refine .orE (le_total a b) ?_ ?_
  · have hab : (le a b :: Γ) ⊢[PRAAx] le a b := Prf.hyp0
    have e := natEq (eq_add_of_le hab); have z := natEq hab
    have hk : (le a b :: Γ) ⊢[PRAAx] le (k * a) (k * b) := le_scale k hab
    have e' := natEq (eq_add_of_le hk); have z' := natEq hk
    ipra_le 0 with 𝔞 k * e - 𝔞 k * z - e' + z'
  · have hba : (le b a :: Γ) ⊢[PRAAx] le b a := Prf.hyp0
    have e := natEq (eq_add_of_le hba); have z := natEq hba
    have hk : (le b a :: Γ) ⊢[PRAAx] le (k * b) (k * a) := le_scale k hba
    have e' := natEq (eq_add_of_le hk); have z' := natEq hk
    ipra_le 0 with 𝔞 k * e - 𝔞 k * z - e' + z'

/-! ## Sums -/

/-- `|f − g|` as a body. -/
abbrev adB (f g : PTm 2) : PTm 2 := absd f g

theorem inst2_adB (f g : PTm 2) (k y : PTm n) : inst2 (adB f g) k y = absd (inst2 f k y) (inst2 g k y) := by
  simp [inst2]

/-- `|Σ_{k<N} f(k) − Σ_{k<N} g(k)| ≤ Σ_{k<N} |f(k) − g(k)|`. -/
theorem absd_sum (f g : PTm 2) (N y : PTm n) :
    Γ ⊢[PRAAx] le (absd (ap2 (sumF f) N y) (ap2 (sumF g) N y)) (ap2 (sumF (adB f g)) N y) := by
  have s := sum_add2 (Γ := Γ) g (adB f g) (g + adB f g) (K := N) (x := y) (x' := y) (z := y)
    (.allI (.impI (by rw [show inst2 (g + adB f g) (var 0) (Syn.shift y) =
      inst2 g (var 0) (Syn.shift y) + inst2 (adB f g) (var 0) (Syn.shift y) by simp [inst2]]; exact .eqRefl _)))
  have s' := sum_add2 (Γ := Γ) f (adB f g) (f + adB f g) (K := N) (x := y) (x' := y) (z := y)
    (.allI (.impI (by rw [show inst2 (f + adB f g) (var 0) (Syn.shift y) =
      inst2 f (var 0) (Syn.shift y) + inst2 (adB f g) (var 0) (Syn.shift y) by simp [inst2]]; exact .eqRefl _)))
  have p := sum_le_params (Γ := Γ) f (g + adB f g) y y N (.allI (.impI (by
    rw [show inst2 (g + adB f g) (var 0) (Syn.shift y) =
      inst2 g (var 0) (Syn.shift y) + inst2 (adB f g) (var 0) (Syn.shift y) by simp [inst2], inst2_adB]
    exact le_absd_l _ _)))
  have q := sum_le_params (Γ := Γ) g (f + adB f g) y y N (.allI (.impI (by
    rw [show inst2 (f + adB f g) (var 0) (Syn.shift y) =
      inst2 f (var 0) (Syn.shift y) + inst2 (adB f g) (var 0) (Syn.shift y) by simp [inst2], inst2_adB]
    exact le_absd_r _ _)))
  have e := natEq s; have e' := natEq s'
  exact absd_le (by ipra_le sl p with e) (by ipra_le sl q with e')

end LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff

export_ipra AnalyticNumberTheory.AbsDiff (absd absd_le absd_sum adB inst2_adB le_absd_l le_absd_r scale_absd)
