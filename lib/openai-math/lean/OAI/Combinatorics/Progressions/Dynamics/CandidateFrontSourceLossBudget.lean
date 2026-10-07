/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem le_power_budget {p : ℝ} (hp : 0 ≤ p) {a : ℕ} (ha : 1 ≤ a) :
    p ≤ (p + 2) ^ a := by
  have hbase : (1 : ℝ) ≤ p + 2 := by linarith
  calc
    p ≤ p + 2 := by linarith
    _ ≤ (p + 2) ^ a := by simpa only [pow_one] using pow_le_pow_right₀ hbase ha

theorem shifted_power_budget_le {p : ℝ} (hp : 0 ≤ p) (a b : ℕ) :
    ((p + 2) ^ a + 2) ^ b ≤ (p + 2) ^ ((a + 2) * b) := by
  have hbase : (1 : ℝ) ≤ p + 2 := by linarith
  have hpow : (1 : ℝ) ≤ (p + 2) ^ a := one_le_pow₀ hbase
  have hsq : (4 : ℝ) ≤ (p + 2) ^ 2 := by nlinarith
  have hstep : (p + 2) ^ a + 2 ≤ (p + 2) ^ (a + 2) := by
    rw [pow_add]
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ (p + 2) ^ a)]
  calc
    _ ≤ ((p + 2) ^ (a + 2)) ^ b := pow_le_pow_left₀ (by positivity) hstep b
    _ = _ := (pow_mul _ _ _).symm

theorem polynomial_budget_comp {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (a b : ℕ) (hpq : q ≤ (p + 2) ^ a) (hqr : r ≤ (q + 2) ^ b) :
    r ≤ (p + 2) ^ ((a + 2) * b) := by
  calc
    r ≤ (q + 2) ^ b := hqr
    _ ≤ ((p + 2) ^ a + 2) ^ b := by gcongr
    _ ≤ _ := shifted_power_budget_le hp a b

def budgetDepthExponent (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 => (budgetDepthExponent a d + 2) * a

theorem bounded_depth_budget {p : ℝ} (hp : 0 ≤ p) (a : ℕ) (q : ℕ → ℝ)
    (hq : ∀ d, 0 ≤ q d) (hzero : q 0 ≤ p)
    (hstep : ∀ d, q (d + 1) ≤ (q d + 2) ^ a) (d : ℕ) :
    q d ≤ (p + 2) ^ budgetDepthExponent a d := by
  induction d with
  | zero => simpa only [budgetDepthExponent, pow_one] using hzero.trans (by linarith : p ≤ p + 2)
  | succ d ih => exact polynomial_budget_comp hp (hq d) _ a ih (hstep d)

theorem exponential_budget_comp {p q h : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (a b : ℕ) (hpq : q ≤ (p + 2) ^ a) (hh : h ≤ Real.exp ((q + 2) ^ b)) :
    h ≤ Real.exp ((p + 2) ^ ((a + 2) * b)) := by
  exact hh.trans (Real.exp_le_exp.mpr (polynomial_budget_comp hp hq a b hpq le_rfl))

theorem product_exponential_budget {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {p : ℝ} (hp : 0 ≤ p) (a c : ℕ)
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hf : ∀ i ∈ s, f i ≤ Real.exp ((p + 2) ^ a))
    (hcard : (s.card : ℝ) ≤ (p + 2) ^ c) :
    (∏ i ∈ s, f i) ≤ Real.exp ((p + 2) ^ (a + c)) := by
  calc
    _ ≤ ∏ _i ∈ s, Real.exp ((p + 2) ^ a) := Finset.prod_le_prod₀ hf0 hf
    _ = Real.exp ((s.card : ℝ) * (p + 2) ^ a) := by
      rw [Finset.prod_const, ← Real.exp_nat_mul]
    _ ≤ Real.exp ((p + 2) ^ (a + c)) := by
      apply Real.exp_le_exp.mpr
      rw [pow_add]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hcard
        (by positivity : 0 ≤ (p + 2) ^ a)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

def candidateFrontFamilyParameter (cap : ℝ) : ℝ := (cap + 3) ^ 4

theorem candidateFrontFamilyBounds (cap native : ℝ) (layers variableCount : ℕ)
    (hcap : 0 ≤ cap) (hnative : native ≤ cap)
    (hlayers : (layers : ℝ) ≤ cap) (hvariableCount : (variableCount : ℝ) ≤ cap) :
    0 ≤ candidateFrontFamilyParameter cap ∧
    cap ≤ candidateFrontFamilyParameter cap ∧
    2 * max native 3 ≤ candidateFrontFamilyParameter cap ∧
    Real.exp (max native 3) *
      (1 + (layers : ℝ) * (((layers + 1 : ℕ) : ℝ) *
        ((variableCount + 1 : ℕ) : ℝ) ^ layers)) ≤ Real.exp (candidateFrontFamilyParameter cap) := by
  have hbase : 1 ≤ cap + 3 := by linarith
  have hsq : (cap + 3) ^ 2 ≤ candidateFrontFamilyParameter cap :=
    pow_le_pow_right₀ hbase (by decide)
  have hcapFamily : cap ≤ candidateFrontFamilyParameter cap :=
    (by nlinarith [sq_nonneg cap] : cap ≤ (cap + 3) ^ 2).trans hsq
  have hmax : max native 3 ≤ cap + 3 := max_le (by linarith) (by linarith)
  have hperiod : 2 * max native 3 ≤ candidateFrontFamilyParameter cap :=
    (by nlinarith [sq_nonneg cap] : 2 * max native 3 ≤ (cap + 3) ^ 2).trans hsq
  have hplus : cap + 1 ≤ Real.exp cap := Real.add_one_le_exp cap
  have hLayerExp : (layers : ℝ) ≤ Real.exp cap := hlayers.trans (by linarith)
  have hLayerOneExp : ((layers + 1 : ℕ) : ℝ) ≤ Real.exp cap := by
    push_cast
    linarith
  have hVariableExp : ((variableCount + 1 : ℕ) : ℝ) ≤ Real.exp cap := by
    push_cast
    linarith
  have hpower : ((variableCount + 1 : ℕ) : ℝ) ^ layers ≤ Real.exp (cap ^ 2) := by
    calc
      _ ≤ (Real.exp cap) ^ layers := pow_le_pow_left₀ (Nat.cast_nonneg _) hVariableExp layers
      _ = Real.exp ((layers : ℝ) * cap) := (Real.exp_nat_mul cap layers).symm
      _ ≤ Real.exp (cap ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
  have hproduct : (layers : ℝ) * (((layers + 1 : ℕ) : ℝ) *
      ((variableCount + 1 : ℕ) : ℝ) ^ layers) ≤ Real.exp (2 * cap + cap ^ 2) := by
    calc
      _ ≤ Real.exp cap * (Real.exp cap * Real.exp (cap ^ 2)) := by
        gcongr
      _ = Real.exp (2 * cap + cap ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hone : 1 ≤ Real.exp (2 * cap + cap ^ 2) := Real.one_le_exp (by positivity)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsum : 1 + (layers : ℝ) * (((layers + 1 : ℕ) : ℝ) *
      ((variableCount + 1 : ℕ) : ℝ) ^ layers) ≤ Real.exp (2 * cap + cap ^ 2 + 1) := by
    calc
      _ ≤ 2 * Real.exp (2 * cap + cap ^ 2) := by linarith
      _ ≤ Real.exp 1 * Real.exp (2 * cap + cap ^ 2) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = Real.exp (2 * cap + cap ^ 2 + 1) := by
        rw [← Real.exp_add]
        congr 1
        ring
  refine ⟨by unfold candidateFrontFamilyParameter; positivity, hcapFamily, hperiod, ?_⟩
  calc
    _ ≤ Real.exp (max native 3) * Real.exp (2 * cap + cap ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _)
    _ = Real.exp (max native 3 + (2 * cap + cap ^ 2 + 1)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((cap + 3) ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ Real.exp (candidateFrontFamilyParameter cap) := Real.exp_le_exp.mpr hsq

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

noncomputable def iteratedPowerBudget (a : ℕ) (p : ℝ) : ℕ → ℝ
  | 0 => p
  | n + 1 => (iteratedPowerBudget a p n + 2) ^ a

@[simp] theorem iteratedPowerBudget_zero (a : ℕ) (p : ℝ) : iteratedPowerBudget a p 0 = p := rfl

@[simp] theorem iteratedPowerBudget_succ (a : ℕ) (p : ℝ) (n : ℕ) :
    iteratedPowerBudget a p (n + 1) = (iteratedPowerBudget a p n + 2) ^ a := rfl

theorem iteratedPowerBudget_nonneg (a : ℕ) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    0 ≤ iteratedPowerBudget a p n := by
  induction n with
  | zero => exact hp
  | succ n ih => exact pow_nonneg (by linarith) _

theorem iteratedPowerBudget_monotone {a : ℕ} (ha : 1 ≤ a) {p : ℝ} (hp : 0 ≤ p) :
    Monotone (iteratedPowerBudget a p) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_power_budget (iteratedPowerBudget_nonneg a hp n) ha

theorem iteratedPowerBudget_ge {a : ℕ} (ha : 1 ≤ a) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    p ≤ iteratedPowerBudget a p n :=
  iteratedPowerBudget_monotone ha hp (Nat.zero_le n)

theorem iteratedPowerBudget_le_power (a : ℕ) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    iteratedPowerBudget a p n ≤ (p + 2) ^ budgetDepthExponent a n :=
  bounded_depth_budget hp a (iteratedPowerBudget a p)
    (iteratedPowerBudget_nonneg a hp) le_rfl (fun _ => le_rfl) n

end Erdos3

end

section

namespace Erdos3

theorem powerCover_index_allowance_le_exp (l m d : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hm : (m : ℝ) ≤ Real.exp p) (hd : (d : ℝ) ≤ p) :
    (((l * m) ^ d : ℕ) : ℝ) ≤ Real.exp (2 * p ^ 2) := by
  have hprod : (l : ℝ) * m ≤ Real.exp (2 * p) := by
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hl hm (by positivity) (by positivity)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
  rw [Nat.cast_pow, Nat.cast_mul]
  calc
    _ ≤ (Real.exp (2 * p)) ^ d := pow_le_pow_left₀ (by positivity) hprod d
    _ = Real.exp ((d : ℝ) * (2 * p)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (2 * p ^ 2) := Real.exp_le_exp.mpr (by nlinarith)

theorem powerCover_grid_allowance_le_exp (l m : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hm : (m : ℝ) ≤ Real.exp p) :
    (((l * m) * l : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
  push_cast
  calc
    _ ≤ Real.exp p * Real.exp p * Real.exp p :=
      mul_le_mul (mul_le_mul hl hm (by positivity) (by positivity)) hl
        (by positivity) (by positivity)
    _ = Real.exp (3 * p) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem quadratic_shift_exp_budget (C : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    Real.exp (((p + 2) ^ 2 + C) ^ C) ≤
      Real.exp ((p + (2 * C + 5)) ^ (2 * C + 5)) := by
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have hbase : (p + 2) ^ 2 + C ≤ (p + (2 * C + 5)) ^ 2 := by nlinarith
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ((p + (2 * C + 5)) ^ 2) ^ C := pow_le_pow_left₀ (by positivity) hbase C
    _ = (p + (2 * C + 5)) ^ (2 * C) := (pow_mul _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

theorem candidateFrontSourceLossBounds (cap p q u pModel native bin : ℝ)
    (hcap : 3 ≤ cap)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hu : 0 ≤ u) (hmodel : 0 ≤ pModel)
    (hnative : 0 ≤ native) (hbin : 0 ≤ bin)
    (hpCap : p ≤ cap) (hqCap : q ≤ cap) (huCap : u ≤ cap)
    (hmodelCap : pModel ≤ cap) (hnativeCap : native ≤ cap) (hbinU : bin ≤ u) :
    let Q := max (max native 3) (2 * u + 4 * pModel + 20)
    let r := q + bin + Q + 6
    let M := 2 * p + q + p * (bin + (2 * Q + 2 * u + 4 * pModel + 34)) + 2
    0 ≤ Q ∧ Q ≤ 6 * cap + 20 ∧
      0 ≤ r ∧ r ≤ (cap + 3) ^ 4 ∧
      0 ≤ M ∧ M ≤ (cap + 3) ^ 4 := by
  let Q := max (max native 3) (2 * u + 4 * pModel + 20)
  have hc0 : 0 ≤ cap := le_trans (by norm_num) hcap
  have hQ0 : 0 ≤ Q := (hnative.trans (le_max_left _ _)).trans (le_max_left _ _)
  have hQcap : Q ≤ 6 * cap + 20 := by
    apply max_le
    · exact max_le (by linarith only [hnativeCap, hc0]) (by linarith only [hcap])
    · linarith only [huCap, hmodelCap]
  have hbinCap : bin ≤ cap := hbinU.trans huCap
  have hterm0 : 0 ≤ bin + (2 * Q + 2 * u + 4 * pModel + 34) := by positivity
  have hterm : bin + (2 * Q + 2 * u + 4 * pModel + 34) ≤ 19 * cap + 74 := by
    linarith only [hbinCap, hQcap, huCap, hmodelCap]
  have hproduct := mul_le_mul hpCap hterm hterm0 hc0
  have hmass : 2 * p + q + p * (bin + (2 * Q + 2 * u + 4 * pModel + 34)) + 2 ≤
      19 * cap ^ 2 + 77 * cap + 2 := by
    nlinarith only [hpCap, hqCap, hproduct]
  have hresidual : q + bin + Q + 6 ≤ 8 * cap + 26 := by
    linarith only [hqCap, hbinCap, hQcap]
  have hquartic : (cap + 3) ^ 4 = cap ^ 4 + 12 * cap ^ 3 + 54 * cap ^ 2 +
      108 * cap + 81 := by ring
  have hc2 : 0 ≤ cap ^ 2 := pow_nonneg hc0 _
  have hc3 : 0 ≤ cap ^ 3 := pow_nonneg hc0 _
  have hc4 : 0 ≤ cap ^ 4 := pow_nonneg hc0 _
  have hresidualQuartic : 8 * cap + 26 ≤ (cap + 3) ^ 4 := by
    rw [hquartic]
    linarith only [hc0, hc2, hc3, hc4]
  have hmassQuartic : 19 * cap ^ 2 + 77 * cap + 2 ≤ (cap + 3) ^ 4 := by
    rw [hquartic]
    linarith only [hc0, hc2, hc3, hc4]
  exact ⟨hQ0, hQcap, by positivity, hresidual.trans hresidualQuartic,
    by positivity, hmass.trans hmassQuartic⟩

end Erdos3.VectorPolynomial

end

end OAI
