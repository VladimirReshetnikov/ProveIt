import DiophantineConsistency.ModelThirteenStrong
/-! # iPRA endpoints for the thirteen-variable square-residual and unit-sphere forms

Four forms on the coordinates and ports of the mixed carrier
(`ModelThirteenStrong.value72`, with the mixed ordinate `yLV`):

* 13/77/96 (`ThirteenGroupedSquares96`): `(PQ-1)² + (U-1)² + (Z-1)²`;
* 13/76/96 (`ThirteenSharedSquares96`): the same polynomial with the shared
  subtraction `f² - 1` (an exact ring identity);
* 13/75/96 (`ThirteenUnitSphere96`): `(PQ)² + U² + Z² - 3`;
* 13/84/92 (`ThirteenFirstNormCorrection92`): the unit sphere with
  `U - c (P - 1)` in place of `U`.

Every link is same-valuation (identity witness map). Over `ℤ` the unit-sphere
step uses `a² ≤ 3 → a² ≤ 1` by case analysis; here it is replayed with
discreteness only (`square_le_three`), so the arguments run in the ring of
differences of every model of `𝗜𝚺₁` and the bridges transfer from the 72 form. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ModelThirteenSquares
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts
open ModelThirteenCarrier ModelThirteenStrong
open ModelCarrierSpheres (Facts modelFacts unit_eq_one sq_one square_aux_ne_neg_one
  product_ne_neg_one)
open ModelThirteenRestoration (b parent data G)

/-! ### Ring definitions -/

section Defs
variable {R : Type*} [CommRing R]

/-- The auxiliary factor at the mixed ordinate (`ThirteenGroupedSquares96.auxiliary`). -/
def aux77 (p : Fin 4 → R) (v : Fin 13 → R) : R := normalAux p v (yLV p v)

/-- The 13/77/96 value. -/
def value77 (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  ((data p v).P * (data p v).Q - 1) ^ 2 + (aux77 p v - 1) ^ 2 +
    (Carrier65.strong (data p v) - 1) ^ 2

/-- The 13/76/96 value, sharing `f² - 1`. -/
def value76 (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  let d := data p v
  let y := yLV p v
  let h := d.f ^ 2 - 1
  let u := d.delta * h * (d.V ^ 2 - y ^ 2) + y ^ 2
  let z := h - d.delta * (d.i * d.c ^ 2) ^ 2
  (d.P * d.Q - 1) ^ 2 + (u - 1) ^ 2 + z ^ 2

/-- The 13/75/96 value. -/
def value75 (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  ((data p v).P * (data p v).Q) ^ 2 + aux77 p v ^ 2 + Carrier65.strong (data p v) ^ 2 - 3

/-- The degree-cancelling coefficient of the 84/92 form. -/
def coefficient84 (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  16 * ((b p v * v 5 * G p v * (data p v).V) ^ 2 * (data p v).f ^ 2)

def aux84 (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  aux77 p v - coefficient84 p v * ((data p v).P - 1)

/-- The 13/84/92 value. -/
def value84 (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  ((data p v).P * (data p v).Q) ^ 2 + aux84 p v ^ 2 + Carrier65.strong (data p v) ^ 2 - 3

/-- Sharing a subtraction is an exact identity, without positivity. -/
theorem value76_eq_77 (p : Fin 4 → R) (v : Fin 13 → R) : value76 p v = value77 p v := by
  simp only [value76, value77, aux77, normalAux, Carrier65.strong]
  ring

end Defs

/-! ### The integer arguments in a discretely ordered ring -/

section Generic
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem three_squares_zero_iff (a b c : R) :
    a ^ 2 + b ^ 2 + c ^ 2 = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    have ha := sq_nonneg a
    have hb := sq_nonneg b
    have hc := sq_nonneg c
    have ha0 : a ^ 2 = 0 := by linarith only [h, ha, hb, hc]
    have hb0 : b ^ 2 = 0 := by linarith only [h, ha, hb, hc]
    have hc0 : c ^ 2 = 0 := by linarith only [h, ha, hb, hc]
    exact ⟨(pow_eq_zero_iff two_ne_zero).mp ha0, (pow_eq_zero_iff two_ne_zero).mp hb0,
      (pow_eq_zero_iff two_ne_zero).mp hc0⟩
  · rintro ⟨rfl, rfl, rfl⟩
    ring

theorem value77_zero_iff_residuals (p : Fin 4 → R) (v : Fin 13 → R) :
    value77 p v = 0 ↔ (data p v).P * (data p v).Q = 1 ∧
      aux77 p v = 1 ∧ Carrier65.strong (data p v) = 1 := by
  unfold value77
  rw [three_squares_zero_iff]
  simp only [sub_eq_zero]

/-- The strong and auxiliary norms of a positive 72 zero; `P` and `Q` need not
be separated. -/
theorem residuals_of_zero72 (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hz : value72 p v = 0) :
    (data p v).P * (data p v).Q = 1 ∧ aux77 p v = 1 ∧ Carrier65.strong (data p v) = 1 := by
  have hnormal : normalValue p v (yLV p v) = 0 := (zero74_iff72 F p v hb hv).mpr hz
  obtain ⟨hs, hn⟩ := norms_of_normal_zero F p v (yLV p v) hb hv hnormal
  have hc := coeff_of_strong p v hs
  have hu : aux77 p v = 1 := by
    change (data p v).delta * ((data p v).f ^ 2 - 1) * ((data p v).V ^ 2 - yLV p v ^ 2) +
      yLV p v ^ 2 = 1
    rw [hc]
    linear_combination hn
  have hproduct : (data p v).P * (data p v).Q = 1 := by
    have hz0 : (data p v).P * (data p v).Q * aux77 p v * Carrier65.strong (data p v) - 1 = 0 :=
      hz
    rw [hu, hs] at hz0
    linear_combination hz0
  exact ⟨hproduct, hu, hs⟩

/-- `ThirteenGroupedSquares96.positive_zero_iff72`. -/
theorem zero77_iff72 (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : value77 p v = 0 ↔ value72 p v = 0 := by
  constructor
  · intro hz
    obtain ⟨hp, hu, hs⟩ := (value77_zero_iff_residuals p v).mp hz
    change (data p v).P * (data p v).Q * aux77 p v * Carrier65.strong (data p v) - 1 = 0
    rw [hp, hu, hs]
    norm_num
  · intro hz
    exact (value77_zero_iff_residuals p v).mpr (residuals_of_zero72 F p v hb hv hz)

/-- In a discretely ordered ring a square at most `3` is `0` or `1`. -/
theorem square_le_three (F : Facts R) {a : R} (h : a ^ 2 ≤ 3) : a ^ 2 = 0 ∨ a ^ 2 = 1 := by
  have hlt : |a| < 1 + 1 := by
    by_contra hn
    push_neg at hn
    have h4 : 4 ≤ |a| ^ 2 := by
      nlinarith only [mul_nonneg (show (0 : R) ≤ |a| - 2 by linarith only [hn])
        (show (0 : R) ≤ |a| + 2 by linarith only [hn])]
    rw [sq_abs] at h4
    linarith only [h4, h]
  have hle : |a| ≤ 1 := DiscreteOrderedRingFacts.le_of_lt_add_one F.discrete hlt
  by_cases ha : a = 0
  · left
    rw [ha]
    ring
  · right
    have h1 : 1 ≤ |a| := DiscreteOrderedRingFacts.abs_ge_one F.discrete ha
    have heq : |a| = 1 := le_antisymm hle h1
    rw [← sq_abs, heq, one_pow]

/-- `ThirteenUnitSphere96.three_squares_eq_three_iff`, from discreteness alone. -/
theorem three_squares_eq_three_iff (F : Facts R) (a b c : R) :
    a ^ 2 + b ^ 2 + c ^ 2 = 3 ↔ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ c ^ 2 = 1 := by
  constructor
  · intro h
    have ha := sq_nonneg a
    have hb := sq_nonneg b
    have hc := sq_nonneg c
    rcases square_le_three F (show a ^ 2 ≤ 3 by linarith only [h, hb, hc]) with ha' | ha' <;>
    rcases square_le_three F (show b ^ 2 ≤ 3 by linarith only [h, ha, hc]) with hb' | hb' <;>
    rcases square_le_three F (show c ^ 2 ≤ 3 by linarith only [h, ha, hb]) with hc' | hc' <;>
    first
      | exact ⟨ha', hb', hc'⟩
      | (exfalso; linarith only [h, ha', hb', hc'])
  · rintro ⟨ha, hb, hc⟩
    rw [ha, hb, hc]
    norm_num

/-- The main norm is never `-1` (mod 4), without positivity. -/
theorem main_ne_neg_one (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R) :
    (data p v).Q ≠ -1 := by
  obtain ⟨φ⟩ := F.mod4
  change (data p v).D ^ 2 - (data p v).delta * (data p v).c ^ 2 ≠ -1
  rw [show (data p v).delta = ((data p v).a + 2) ^ 2 - 1 from
    Carrier65.delta_shape p (parent p v 1 1)]
  exact ModelCarrierScaled.strong_ne_neg_one φ _ _ _

/-- The strong norm is never `-1` (mod 4), without positivity. -/
theorem strong_ne_neg_one (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R) :
    Carrier65.strong (data p v) ≠ -1 := by
  obtain ⟨φ⟩ := F.mod4
  unfold Carrier65.strong
  rw [show (data p v).delta = ((data p v).a + 2) ^ 2 - 1 from
    Carrier65.delta_shape p (parent p v 1 1)]
  exact ModelCarrierScaled.strong_ne_neg_one φ _ _ _

/-- The auxiliary exclusion, used only after recovering the strong unit. -/
theorem aux77_ne_neg_one (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R)
    (hs : Carrier65.strong (data p v) = 1) : aux77 p v ≠ -1 := by
  have hc := coeff_of_strong p v hs
  change (data p v).delta * ((data p v).f ^ 2 - 1) * ((data p v).V ^ 2 - yLV p v ^ 2) +
    yLV p v ^ 2 ≠ -1
  rw [hc]
  exact square_aux_ne_neg_one F _ _ _

theorem zero75_iff_residuals (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value75 p v = 0 ↔ (data p v).P * (data p v).Q = 1 ∧
      aux77 p v = 1 ∧ Carrier65.strong (data p v) = 1 := by
  constructor
  · intro hz
    have hz0 : ((data p v).P * (data p v).Q) ^ 2 + aux77 p v ^ 2 +
        Carrier65.strong (data p v) ^ 2 - 3 = 0 := hz
    have he : ((data p v).P * (data p v).Q) ^ 2 + aux77 p v ^ 2 +
        Carrier65.strong (data p v) ^ 2 = 3 := by linear_combination hz0
    obtain ⟨hp, hu, hs⟩ := (three_squares_eq_three_iff F _ _ _).mp he
    have hP := data_first_ne_neg_one F p v hb hv
    have hp1 := sq_one (product_ne_neg_one F hP (main_ne_neg_one F p v)) hp
    have hs1 := sq_one (strong_ne_neg_one F p v) hs
    have hu1 := sq_one (aux77_ne_neg_one F p v hs1) hu
    exact ⟨hp1, hu1, hs1⟩
  · rintro ⟨hp, hu, hs⟩
    show ((data p v).P * (data p v).Q) ^ 2 + aux77 p v ^ 2 +
      Carrier65.strong (data p v) ^ 2 - 3 = 0
    rw [hp, hu, hs]
    norm_num

/-- `ThirteenUnitSphere96.positive_zero_iff72`. -/
theorem zero75_iff72 (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : value75 p v = 0 ↔ value72 p v = 0 := by
  rw [zero75_iff_residuals F p v hb hv, ← value77_zero_iff_residuals]
  exact zero77_iff72 F p v hb hv

/-- `ThirteenFirstNormCorrection92.correction_zero_iff`: only the first two
negative-unit exclusions are needed. -/
theorem correction_zero_iff (F : Facts R) (P Q U Z c : R) (hP : P ≠ -1) (hQ : Q ≠ -1) :
    (P * Q) ^ 2 + (U - c * (P - 1)) ^ 2 + Z ^ 2 - 3 = 0 ↔
      (P * Q) ^ 2 + U ^ 2 + Z ^ 2 - 3 = 0 := by
  have first_unit (u : R) (h : (P * Q) ^ 2 + u ^ 2 + Z ^ 2 - 3 = 0) : P = 1 := by
    have he : (P * Q) ^ 2 + u ^ 2 + Z ^ 2 = 3 := by linear_combination h
    have hs := (three_squares_eq_three_iff F _ _ _).mp he
    have hpq : P * Q = 1 := sq_one (product_ne_neg_one F hP hQ) hs.1
    exact unit_eq_one F.discrete hpq hP
  constructor <;> intro h
  · have hp := first_unit (U - c * (P - 1)) h
    simpa only [hp, sub_self, mul_zero, sub_zero] using h
  · have hp := first_unit U h
    simpa only [hp, sub_self, mul_zero, sub_zero] using h

/-- `ThirteenFirstNormCorrection92.positive_zero_iff75`. -/
theorem zero84_iff75 (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : value84 p v = 0 ↔ value75 p v = 0 :=
  correction_zero_iff F (data p v).P (data p v).Q (aux77 p v) (Carrier65.strong (data p v))
    (coefficient84 p v) (data_first_ne_neg_one F p v hb hv) (main_ne_neg_one F p v)

end Generic

/-! ### Literal syntax -/

/-- The 13/77/96 polynomial. -/
def expressionAt77 (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  front13x p fun P Q delta f c bi V L G bb m _ =>
    let y := 1 + 4 * (bb * (m - L * V * G) - G)
    (P * Q - 1) ^ 2 + (delta * (f ^ 2 - 1) * (V ^ 2 - y ^ 2) + y ^ 2 - 1) ^ 2 +
      (f ^ 2 - delta * (bi * c ^ 2) ^ 2 - 1) ^ 2

/-- The 13/76/96 polynomial. -/
def expressionAt76 (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  front13x p fun P Q delta f c bi V L G bb m _ =>
    let y := 1 + 4 * (bb * (m - L * V * G) - G)
    let h := f ^ 2 - 1
    let u := delta * h * (V ^ 2 - y ^ 2) + y ^ 2
    let z := h - delta * (bi * c ^ 2) ^ 2
    (P * Q - 1) ^ 2 + (u - 1) ^ 2 + z ^ 2

/-- The 13/75/96 polynomial. -/
def expressionAt75 (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  front13x p fun P Q delta f c bi V L G bb m _ =>
    let y := 1 + 4 * (bb * (m - L * V * G) - G)
    (P * Q) ^ 2 + (delta * (f ^ 2 - 1) * (V ^ 2 - y ^ 2) + y ^ 2) ^ 2 +
      (f ^ 2 - delta * (bi * c ^ 2) ^ 2) ^ 2 - 3

/-- The 13/84/92 polynomial. -/
def expressionAt84 (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  front13x p fun P Q delta f c bi V L G bb m T =>
    let y := 1 + 4 * (bb * (m - L * V * G) - G)
    (P * Q) ^ 2 + (delta * (f ^ 2 - 1) * (V ^ 2 - y ^ 2) + y ^ 2 -
        16 * ((bb * T * G * V) ^ 2 * f ^ 2) * (P - 1)) ^ 2 +
      (f ^ 2 - delta * (bi * c ^ 2) ^ 2) ^ 2 - 3

section Eval
variable {R : Type*} [CommRing R]

-- CHECK: the closing `rfl` unfolds `data`/`parent` (literal `Fin` matches) by defeq.
theorem evalRing_expressionAt77 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (expressionAt77 p).evalRing v = value77 (fun j => (p j : R)) v := by
  simp only [expressionAt77, front13x, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one]
  rfl

-- CHECK: as above.
theorem evalRing_expressionAt76 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (expressionAt76 p).evalRing v = value76 (fun j => (p j : R)) v := by
  simp only [expressionAt76, front13x, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one]
  rfl

-- CHECK: as above.
theorem evalRing_expressionAt75 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (expressionAt75 p).evalRing v = value75 (fun j => (p j : R)) v := by
  simp only [expressionAt75, front13x, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one]
  rfl

-- CHECK: as above.
theorem evalRing_expressionAt84 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (expressionAt84 p).evalRing v = value84 (fun j => (p j : R)) v := by
  simp only [expressionAt84, front13x, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one]
  rfl

end Eval

/-! ### Models of `𝗜𝚺₁` -/

section Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem sameZero77 (u : Fin 13 → V) :
    InternalZero (positiveShift (expressionAt77 CurrentWindowCarry2011.ports)) u ↔
      InternalZero (positiveShift (expressionAt72 CurrentWindowCarry2011.ports)) u := by
  rw [internalZero_positiveShift, internalZero_positiveShift, internalZero_iff, internalZero_iff,
    evalRing_expressionAt77, evalRing_expressionAt72]
  exact zero77_iff72 modelFacts ringPorts (fun i => ι (u i + 1)) ModelCarrierCurrent.beta_pos
    (ModelThirteenForms.shifted13_pos u)

theorem sameZero76 (u : Fin 13 → V) :
    InternalZero (positiveShift (expressionAt76 CurrentWindowCarry2011.ports)) u ↔
      InternalZero (positiveShift (expressionAt77 CurrentWindowCarry2011.ports)) u := by
  rw [internalZero_positiveShift, internalZero_positiveShift, internalZero_iff, internalZero_iff,
    evalRing_expressionAt76, evalRing_expressionAt77]
  exact iff_of_eq (congrArg (fun x => x = 0) (value76_eq_77 _ _))

theorem sameZero75 (u : Fin 13 → V) :
    InternalZero (positiveShift (expressionAt75 CurrentWindowCarry2011.ports)) u ↔
      InternalZero (positiveShift (expressionAt72 CurrentWindowCarry2011.ports)) u := by
  rw [internalZero_positiveShift, internalZero_positiveShift, internalZero_iff, internalZero_iff,
    evalRing_expressionAt75, evalRing_expressionAt72]
  exact zero75_iff72 modelFacts ringPorts (fun i => ι (u i + 1)) ModelCarrierCurrent.beta_pos
    (ModelThirteenForms.shifted13_pos u)

theorem sameZero84 (u : Fin 13 → V) :
    InternalZero (positiveShift (expressionAt84 CurrentWindowCarry2011.ports)) u ↔
      InternalZero (positiveShift (expressionAt75 CurrentWindowCarry2011.ports)) u := by
  rw [internalZero_positiveShift, internalZero_positiveShift, internalZero_iff, internalZero_iff,
    evalRing_expressionAt84, evalRing_expressionAt75]
  exact zero84_iff75 modelFacts ringPorts (fun i => ι (u i + 1)) ModelCarrierCurrent.beta_pos
    (ModelThirteenForms.shifted13_pos u)

end Model

/-! ### Bridges and iPRA endpoints -/

open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation

theorem bridge77 : HAExpressionAssembly.PolynomialBridge
    (positiveShift (expressionAt77 CurrentWindowCarry2011.ports)) :=
  HAExpressionSameZero.bridge _ _ (fun _ _ _ u => sameZero77 u) bridge72

theorem bridge76 : HAExpressionAssembly.PolynomialBridge
    (positiveShift (expressionAt76 CurrentWindowCarry2011.ports)) :=
  HAExpressionSameZero.bridge _ _ (fun _ _ _ u => sameZero76 u) bridge77

theorem bridge75 : HAExpressionAssembly.PolynomialBridge
    (positiveShift (expressionAt75 CurrentWindowCarry2011.ports)) :=
  HAExpressionSameZero.bridge _ _ (fun _ _ _ u => sameZero75 u) bridge72

theorem bridge84 : HAExpressionAssembly.PolynomialBridge
    (positiveShift (expressionAt84 CurrentWindowCarry2011.ports)) :=
  HAExpressionSameZero.bridge _ _ (fun _ _ _ u => sameZero84 u) bridge75

/-- **Native iPRA: the 13/77/96 form has no positive zero iff ZFC is consistent.** -/
theorem native_equivalence77 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt77 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge77

theorem standard_equivalence77 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt77 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence77

theorem reference_equivalence77 : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero
      (positiveShift (expressionAt77 CurrentWindowCarry2011.ports))) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference native_equivalence77

/-- **Native iPRA: the 13/76/96 form has no positive zero iff ZFC is consistent.** -/
theorem native_equivalence76 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt76 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge76

theorem standard_equivalence76 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt76 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence76

theorem reference_equivalence76 : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero
      (positiveShift (expressionAt76 CurrentWindowCarry2011.ports))) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference native_equivalence76

/-- **Native iPRA: the 13/75/96 form has no positive zero iff ZFC is consistent.** -/
theorem native_equivalence75 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt75 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge75

theorem standard_equivalence75 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt75 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence75

theorem reference_equivalence75 : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero
      (positiveShift (expressionAt75 CurrentWindowCarry2011.ports))) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference native_equivalence75

/-- **Native iPRA: the 13/84/92 form has no positive zero iff ZFC is consistent.** -/
theorem native_equivalence84 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt84 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge84

theorem standard_equivalence84 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt84 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence84

theorem reference_equivalence84 : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero
      (positiveShift (expressionAt84 CurrentWindowCarry2011.ports))) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference native_equivalence84

end DiophantineConsistency.ModelThirteenSquares
