import DiophantineConsistency.P138.P138Squares

/-! # The centered budget recovers the common signs

`PROOF.md`, "Soundness", the paragraph after (6). In every model of `𝗜𝚺₁`, at a zero of the
924/107 output:

* `budget_ge`: `Budget ≥ 12`. Indeed `Dg = P / Dt > 0` (`P > 0`, `Dt ≥ 1`); `Budget ≤ 3` would give
  `D ≤ −1` and, as `s ≠ 0`, `Dg ≤ 1 − Dt ≤ 0`; then (2) gives `Budget ≥ 12`.

For every point with a positive budget (no zero needed):

* `centered`: `k ≠ 0`, `Derr < q²`, `4η² < k²`, and the common strict signs of `q, F, C, q − F − C`
  (as `0 < F q`, `0 < C q`, `0 < (q − F − C) q`), with the cone bounds `cone_A F q < 2q²`,
  `cone_B C q < 2q²` and `4 F q < q²`, `4 C q < q²` (`cone_A, cone_B ≥ 8`);
* `c_interval`: `|k|(2|Y| − 1) < 2|c| < |k|(2|Y| + 1)` and `0 < c (k Y)`; in particular `c ≠ 0`.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P138Budget
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing P138Value P138Ports P138Bootstrap P138NoRoot P138Squares

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- One cone row: `(u − q)² < q²` with `u = cone · y` and `cone ≥ 8` gives
`0 < y q`, `cone · y q < 2q²` and `4 y q < q²`. -/
theorem cone_row {cone y q : DiffRing V} (hc : 8 ≤ cone) (h : (cone * y - q) ^ 2 < q ^ 2) :
    0 < y * q ∧ cone * (y * q) < 2 * q ^ 2 ∧ 4 * (y * q) < q ^ 2 := by
  have h1 : (cone * y) * (cone * y) < 2 * (cone * y) * q := by nlinarith
  have hcy : 0 < cone * y * q := by nlinarith [mul_self_nonneg (cone * y)]
  have hyq : 0 < y * q := by
    have : cone * y * q = cone * (y * q) := by ring
    rw [this] at hcy
    exact pos_of_mul_pos_right hcy (by linarith)
  have h2 : cone * (y * q) < 2 * q ^ 2 := by
    -- multiply `(cone y)² < 2 (cone y) q` by `q²`
    have h3 : (cone * (y * q)) * (cone * (y * q)) < 2 * q ^ 2 * (cone * (y * q)) := by
      have hq2 : 0 < q ^ 2 := by
        have : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hyq; exact lt_irrefl _ hyq
        exact lt_of_le_of_ne (sq_nonneg q) (Ne.symm (pow_ne_zero 2 this))
      have := mul_lt_mul_of_pos_right h1 hq2
      nlinarith
    have hpos : 0 < cone * (y * q) := by nlinarith
    nlinarith
  refine ⟨hyq, h2, ?_⟩
  nlinarith

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V)
local notation "𝓡" => regs p x

/-- **`Budget ≥ 12` at a zero.** -/
theorem budget_ge (hp : PortFacts p) (hz : value p x = 0) : 12 ≤ (𝓡).Budget := by
  have hP := P_pos p x hp hz
  obtain ⟨hDt, _⟩ := Dt_facts p x hp
  have hs := (s_r_ne p x hp hz).1
  have hs2 : 1 ≤ x 10 ^ 2 := by have := one_le_abs hs; rw [← sq_abs]; nlinarith
  have hDg : 0 < 1 + (𝓡).D4 * (𝓡).Dt * x 10 ^ 2 := by
    rw [P_eq] at hP
    exact pos_of_mul_pos_right hP (by linarith)
  have h4 : 4 ≤ (𝓡).Budget := by
    by_contra hlt
    have hD : (𝓡).D4 ≤ -1 := by
      rw [D4_eq]
      rcases int_split ((𝓡).Budget - 4) with h | h
      · exact absurd (by linarith) hlt
      · exact h
    have : (𝓡).D4 * (𝓡).Dt * x 10 ^ 2 ≤ -1 := by
      have h1 : (𝓡).D4 * (𝓡).Dt ≤ -1 := by nlinarith
      nlinarith
    linarith
  obtain ⟨m, hm | hm⟩ := budget_mod p x hp
  · rw [hm] at h4 ⊢
    have : 0 < m := by linarith
    have := one_le_of_pos' this
    linarith
  · rw [hm] at h4 ⊢
    have : 0 ≤ m := by
      rcases int_split m with h | h
      · exact h
      · linarith
    linarith

/-- **The centered budget.** -/
theorem centered (hp : PortFacts p) (hB : 0 < (𝓡).Budget) :
    (𝓡).k ≠ 0 ∧ (𝓡).Derr < (𝓡).q ^ 2 ∧ 4 * (𝓡).eta ^ 2 < (𝓡).k ^ 2 ∧
      0 < (𝓡).F * (𝓡).q ∧ 0 < x 1 * (𝓡).q ∧ 0 < ((𝓡).q - (𝓡).F - x 1) * (𝓡).q ∧
      p 4 * ((𝓡).F * (𝓡).q) < 2 * (𝓡).q ^ 2 ∧ p 5 * (x 1 * (𝓡).q) < 2 * (𝓡).q ^ 2 ∧
      4 * ((𝓡).F * (𝓡).q) < (𝓡).q ^ 2 ∧ 4 * (x 1 * (𝓡).q) < (𝓡).q ^ 2 := by
  rw [Budget_eq] at hB
  have he : 0 ≤ 4 * (𝓡).q ^ 2 * (𝓡).eta ^ 2 := by positivity
  have hk2 : 0 ≤ (𝓡).k ^ 2 := sq_nonneg _
  have hprod : 0 < (𝓡).k ^ 2 * ((𝓡).q ^ 2 - (𝓡).Derr) := by linarith
  have hk : (𝓡).k ≠ 0 := by
    intro h0
    have : (𝓡).k ^ 2 * ((𝓡).q ^ 2 - (𝓡).Derr) = 0 := by rw [h0]; ring
    linarith
  have hD : (𝓡).Derr < (𝓡).q ^ 2 := by
    have := pos_of_mul_pos_right hprod hk2
    linarith
  have hDerr0 : 0 ≤ (𝓡).Derr := by rw [Derr_eq]; positivity
  have hq2 : 0 < (𝓡).q ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (q_ne p x hp)))
  have heta : 4 * (𝓡).eta ^ 2 < (𝓡).k ^ 2 := by
    have h1 : 4 * (𝓡).q ^ 2 * (𝓡).eta ^ 2 < (𝓡).k ^ 2 * (𝓡).q ^ 2 := by nlinarith
    by_contra hc
    have : (𝓡).k ^ 2 * (𝓡).q ^ 2 ≤ 4 * (𝓡).eta ^ 2 * (𝓡).q ^ 2 :=
      mul_le_mul_of_nonneg_right (le_of_not_gt hc) hq2.le
    linarith
  rw [Derr_eq] at hD
  have hA : ((p 4) * (𝓡).F - (𝓡).q) ^ 2 < (𝓡).q ^ 2 := by
    have := sq_nonneg (p 5 * x 1 - (𝓡).q); linarith
  have hC : ((p 5) * x 1 - (𝓡).q) ^ 2 < (𝓡).q ^ 2 := by
    have := sq_nonneg (p 4 * (𝓡).F - (𝓡).q); linarith
  obtain ⟨hF1, hF2, hF3⟩ := cone_row hp.coneA_ge hA
  obtain ⟨hC1, hC2, hC3⟩ := cone_row hp.coneB_ge hC
  refine ⟨hk, by rw [Derr_eq]; exact hD, heta, hF1, hC1, ?_, hF2, hC2, hF3, hC3⟩
  nlinarith

/-- **The interval for `c`** (`|c/k − Y| < 1/2`). -/
theorem c_interval (hp : PortFacts p) (hB : 0 < (𝓡).Budget) :
    |(𝓡).k| * (2 * |(𝓡).Y| - 1) < 2 * |x 8| ∧ 2 * |x 8| < |(𝓡).k| * (2 * |(𝓡).Y| + 1) ∧
      0 < x 8 * ((𝓡).k * (𝓡).Y) := by
  obtain ⟨hk, _, heta, _⟩ := centered p x hp hB
  have h2e : 2 * |(𝓡).eta| < |(𝓡).k| := by
    have h : (2 * (𝓡).eta) ^ 2 < (𝓡).k ^ 2 := by nlinarith
    have := _root_.sq_lt_sq.mp h
    rw [abs_mul, abs_two] at this
    exact this
  have hY1 : 1 ≤ |(𝓡).Y| := by
    have h1 := abs_Y p x hp
    have h2 := abs_q_ge p x hp
    have h3 : (1 : DiffRing V) ≤ |(𝓡).q| := by
      have : (1 : DiffRing V) ≤ 2 ^ 64 := one_le_pow₀ (by norm_num); linarith
    have h4 : 1 ≤ |(𝓡).q| ^ 3 := one_le_pow₀ h3
    linarith
  have hc : x 8 = (𝓡).Y * (𝓡).k + (𝓡).eta := by rw [eta_eq]; ring
  have hk0 : 0 < |(𝓡).k| := abs_pos.mpr hk
  have hYk : |(𝓡).Y * (𝓡).k| = |(𝓡).Y| * |(𝓡).k| := abs_mul _ _
  have hup : |x 8| ≤ |(𝓡).Y| * |(𝓡).k| + |(𝓡).eta| := by
    rw [hc, ← hYk]; exact abs_add_le _ _
  have hlow : |(𝓡).Y| * |(𝓡).k| ≤ |x 8| + |(𝓡).eta| := by
    rw [← hYk]
    have : (𝓡).Y * (𝓡).k = x 8 - (𝓡).eta := by rw [hc]; ring
    rw [this]
    exact abs_le.mpr ⟨by linarith [neg_abs_le (x 8), le_abs_self (𝓡).eta],
      by linarith [le_abs_self (x 8), neg_abs_le (𝓡).eta]⟩
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  -- `c (k Y) = (kY)² + η (kY) ≥ |kY|² − |η| |kY| > 0`
  have hprod : x 8 * ((𝓡).k * (𝓡).Y) = ((𝓡).k * (𝓡).Y) ^ 2 + (𝓡).eta * ((𝓡).k * (𝓡).Y) := by
    rw [hc]; ring
  have hm : -(|(𝓡).eta| * (|(𝓡).k| * |(𝓡).Y|)) ≤ (𝓡).eta * ((𝓡).k * (𝓡).Y) := by
    have := neg_abs_le ((𝓡).eta * ((𝓡).k * (𝓡).Y))
    rwa [abs_mul, abs_mul] at this
  have hsq : ((𝓡).k * (𝓡).Y) ^ 2 = (|(𝓡).k| * |(𝓡).Y|) ^ 2 := by
    rw [← abs_mul, sq_abs]
  rw [hprod, hsq]
  have hkY : |(𝓡).k| ≤ |(𝓡).k| * |(𝓡).Y| := le_mul_of_one_le_right hk0.le hY1
  have hpos : 0 < |(𝓡).k| * |(𝓡).Y| := by linarith
  have : |(𝓡).eta| < |(𝓡).k| * |(𝓡).Y| := by linarith [abs_nonneg (𝓡).eta]
  nlinarith

theorem c_ne (hp : PortFacts p) (hB : 0 < (𝓡).Budget) : x 8 ≠ 0 := by
  have h := (c_interval p x hp hB).2.2
  intro h0; rw [h0, zero_mul] at h; exact lt_irrefl _ h

end Regs

#print axioms cone_row
#print axioms budget_ge
#print axioms centered
#print axioms c_interval
#print axioms c_ne

end DiophantineConsistency.P138Budget
