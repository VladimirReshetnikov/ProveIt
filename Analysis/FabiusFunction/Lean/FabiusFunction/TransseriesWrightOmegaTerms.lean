import FabiusFunction.TransseriesMonomialUniqueness
import FabiusFunction.TransseriesPolyLogScale
import FabiusFunction.WrightOmegaTwoOrders

/-!
# Both exponent directions are forced by Wright omega

The transseries volume's `plt:cor:mot-both-generators-needed`.  The two
orders of `WrightOmegaTwoOrders` say what the first three terms of `ω`
are; the uniqueness of `TransseriesMonomialUniqueness` says that no other
monomial and no other coefficient can represent them.  Together:

`ω ~ 1·X^1(log X)^0`,  `ω - X ~ (-1)·X^0(log X)^1`,
`ω - X + log X ~ 1·X^{-1}(log X)^1`,

and each of the three exponent pairs is the *only* one that works.  So a
scale that carries a three-term expansion of `ω` must contain `(1,0)`,
`(0,1)` and `(-1,1)`; it can be neither a scale of pure powers
`ℝ × {0}` nor a scale of pure logarithms `{0} × ℝ`.  This is the exact
sense in which the pair `(t, L) = (X⁻¹, log X)` is not one convenient
choice among many.

* `plMonomial_one_zero_eventuallyEq`, `plMonomial_zero_one_eventuallyEq`,
  `plMonomial_neg_one_one_eventuallyEq` — the three monomials in closed
  form.  Eventual equalities rather than identities, because `plMonomial`
  uses `rpow` and the closed forms need `X > 1`.
* `exponents_of_wrightOmega`, `exponents_of_wrightOmega_sub`,
  `exponents_of_wrightOmega_residual` — **the three rigidity statements**:
  any monomial with a nonzero coefficient representing that term has the
  stated exponents and the stated coefficient.
* `not_pure_of_wrightOmega_three_terms` — the volume's "consequently"
  clause.
-/

set_option autoImplicit false

open Filter Topology Asymptotics

namespace Fabius

/-- `1·X¹(log X)⁰ = X` beyond `X = 0`. -/
theorem plMonomial_one_zero_eventuallyEq :
    (fun X => (1 : ℝ) * plMonomial 1 0 X) =ᶠ[atTop] fun X : ℝ => X := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  rw [one_mul, plMonomial, Real.rpow_zero, Real.rpow_one, mul_one]

/-- `(-1)·X⁰(log X)¹ = -log X` beyond `X = 1`. -/
theorem plMonomial_zero_one_eventuallyEq :
    (fun X => (-1 : ℝ) * plMonomial 0 1 X) =ᶠ[atTop] fun X : ℝ => -Real.log X := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hL : 0 < Real.log X := Real.log_pos hX
  rw [plMonomial, Real.rpow_zero, one_mul, Real.rpow_one, neg_one_mul]

/-- `1·X⁻¹(log X)¹ = (log X)/X` beyond `X = 1`. -/
theorem plMonomial_neg_one_one_eventuallyEq :
    (fun X => (1 : ℝ) * plMonomial (-1) 1 X) =ᶠ[atTop]
      fun X : ℝ => Real.log X / X := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hX0 : (0 : ℝ) < X := by linarith
  rw [one_mul, plMonomial, Real.rpow_one, Real.rpow_neg_one, div_eq_inv_mul]

/-- **The leading term of `ω` is `X`, and nothing else.** -/
theorem exponents_of_wrightOmega {a b c : ℝ} (hc : c ≠ 0)
    (h : (fun X => wrightOmega X) ~[atTop] fun X => c * plMonomial a b X) :
    a = 1 ∧ b = 0 ∧ c = 1 := by
  have hbase : (fun X => wrightOmega X) ~[atTop] fun X => (1 : ℝ) * plMonomial 1 0 X := by
    refine IsEquivalent.congr_right ?_ plMonomial_one_zero_eventuallyEq.symm
    have hz : ∀ᶠ X in atTop, (X : ℝ) ≠ 0 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      exact hX.ne'
    rw [Asymptotics.isEquivalent_iff_tendsto_one hz]
    exact tendsto_wrightOmega_div_atTop_one
  have := (hbase.symm.trans h)
  obtain ⟨h1, h2, h3⟩ :=
    (isEquivalent_const_mul_plMonomial_iff one_ne_zero hc).1 this
  exact ⟨h1.symm, h2.symm, h3.symm⟩

/-- **The second term of `ω` is `-log X`, and nothing else.** -/
theorem exponents_of_wrightOmega_sub {a b c : ℝ} (hc : c ≠ 0)
    (h : (fun X => wrightOmega X - X) ~[atTop] fun X => c * plMonomial a b X) :
    a = 0 ∧ b = 1 ∧ c = -1 := by
  have hbase : (fun X => wrightOmega X - X) ~[atTop]
      fun X => (-1 : ℝ) * plMonomial 0 1 X := by
    refine IsEquivalent.congr_right ?_ plMonomial_zero_one_eventuallyEq.symm
    exact wrightOmega_sub_self_isEquivalent_neg_log
  obtain ⟨h1, h2, h3⟩ :=
    (isEquivalent_const_mul_plMonomial_iff (by norm_num) hc).1 (hbase.symm.trans h)
  exact ⟨h1.symm, h2.symm, h3.symm⟩

/-- **The third term of `ω` is `(log X)/X`, and nothing else.** -/
theorem exponents_of_wrightOmega_residual {a b c : ℝ} (hc : c ≠ 0)
    (h : (fun X => wrightOmega X - X + Real.log X) ~[atTop]
      fun X => c * plMonomial a b X) :
    a = -1 ∧ b = 1 ∧ c = 1 := by
  have hbase : (fun X => wrightOmega X - X + Real.log X) ~[atTop]
      fun X => (1 : ℝ) * plMonomial (-1) 1 X := by
    refine IsEquivalent.congr_right ?_ plMonomial_neg_one_one_eventuallyEq.symm
    exact wrightOmega_residual_isEquivalent
  obtain ⟨h1, h2, h3⟩ :=
    (isEquivalent_const_mul_plMonomial_iff one_ne_zero hc).1 (hbase.symm.trans h)
  exact ⟨h1.symm, h2.symm, h3.symm⟩

/-- **Both exponent directions are forced** (`plt:cor:mot-both-generators-needed`).
A set of exponent pairs carrying a three-term expansion of `ω` contains
`(1,0)`, `(0,1)` and `(-1,1)`; hence it is contained neither in the pure
powers `ℝ × {0}` nor in the pure logarithms `{0} × ℝ`. -/
theorem not_pure_of_wrightOmega_three_terms {S : Set (ℝ × ℝ)}
    (h1 : ((1 : ℝ), (0 : ℝ)) ∈ S) (h2 : ((0 : ℝ), (1 : ℝ)) ∈ S) :
    ¬ S ⊆ {p : ℝ × ℝ | p.2 = 0} ∧ ¬ S ⊆ {p : ℝ × ℝ | p.1 = 0} := by
  constructor
  · intro hsub
    have := hsub h2
    simp at this
  · intro hsub
    have := hsub h1
    simp at this

/-! ## Why one generator is never enough -/

/-- **The power scale stalls** (`plt:prop:mot-one-generator-fails` (i)).
No pure power `c·X^a` is asymptotic to the first residual `ω(X) - X`:
the residual's logarithmic exponent is `1`, and a pure power has `0`. -/
theorem not_isEquivalent_pure_power_wrightOmega_sub {a c : ℝ} (hc : c ≠ 0) :
    ¬ ((fun X => wrightOmega X - X) ~[atTop] fun X => c * plMonomial a 0 X) := by
  intro h
  obtain ⟨-, h2, -⟩ := exponents_of_wrightOmega_sub hc h
  exact zero_ne_one h2

/-- **The logarithmic scale is blind** (`plt:prop:mot-one-generator-fails`
(ii)), first half: `ω(X)/(log X)^b → ∞` for every `b`, so `ω` has no
leading term at all on a scale of pure logarithms. -/
theorem tendsto_wrightOmega_div_plMonomial_zero_atTop (b : ℝ) :
    Tendsto (fun X => wrightOmega X / plMonomial 0 b X) atTop atTop := by
  have hdiv : Tendsto (fun X => plMonomial 1 0 X / plMonomial 0 b X) atTop atTop :=
    tendsto_plMonomial_div_atTop (Or.inl (by norm_num))
  have hone : Tendsto (fun X => wrightOmega X / plMonomial 1 0 X) atTop (𝓝 1) := by
    refine tendsto_wrightOmega_div_atTop_one.congr' ?_
    filter_upwards [plMonomial_one_zero_eventuallyEq] with X hX
    rw [one_mul] at hX
    rw [hX]
  have hhalf : ∀ᶠ X in atTop, (1 : ℝ) / 2 < wrightOmega X / plMonomial 1 0 X :=
    hone.eventually (eventually_gt_nhds (by norm_num))
  have hscaled : Tendsto
      (fun X => (1 : ℝ) / 2 * (plMonomial 1 0 X / plMonomial 0 b X)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) hdiv
  refine tendsto_atTop_mono' atTop ?_ hscaled
  filter_upwards [hhalf, eventually_gt_atTop (1 : ℝ)] with X hX hX1
  have h1 : 0 < plMonomial 1 0 X := plMonomial_pos hX1
  have h2 : 0 < plMonomial 0 b X := plMonomial_pos hX1
  have hnum : (1 : ℝ) / 2 * plMonomial 1 0 X < wrightOmega X := by
    have := (lt_div_iff₀ h1).1 hX
    linarith
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right hnum.le h2.le

/-- **The logarithmic scale is blind**, second half: the second residual
`ω(X) - X + log X` is `o((log X)^b)` for *every* `b`, so a scale of pure
logarithms assigns it the empty expansion and cannot tell it from `0`. -/
theorem isLittleO_wrightOmega_residual_plMonomial_zero (b : ℝ) :
    (fun X => wrightOmega X - X + Real.log X) =o[atTop]
      fun X => plMonomial 0 b X := by
  have hbase : (fun X => wrightOmega X - X + Real.log X) ~[atTop]
      fun X => plMonomial (-1) 1 X := by
    refine IsEquivalent.congr_right wrightOmega_residual_isEquivalent ?_
    filter_upwards [plMonomial_neg_one_one_eventuallyEq] with X hX
    rw [one_mul] at hX
    exact hX.symm
  exact hbase.trans_isLittleO (isLittleO_plMonomial (Or.inl (by norm_num)))

end Fabius
