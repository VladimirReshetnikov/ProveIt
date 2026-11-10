import DiophantineConsistency.LinCof.LCSquares
import DiophantineConsistency.P138.P138Budget

/-! # The centered budget: the free scale, the common signs, the interval for `c`

Under the slot law, `Budget = Y² · B0 − k² · q^(6+2e)` with the inner budget
`B0 = k² (q² − Derr) − 4 q² η²` (package 138's `Budget`). For every point with a positive budget
(no zero is needed; at a zero `LCSquares.budget_ge` gives `Budget ≥ 12`):

* `B0_pos`: `Y ≠ 0` and `B0 > 0`. This is where the free scale `Y = x 5` is first known to be
  nonzero; nothing earlier in the soundness chain uses it.
* `centered`: `k ≠ 0`, `Derr < q²`, `4η² < k²`, and the common strict signs of
  `q, F, C, q − F − C` (as `0 < F q`, `0 < C q`, `0 < (q − F − C) q`), with the cone bounds
  `cone_A F q < 2q²`, `cone_B C q < 2q²` and `4 F q < q²`, `4 C q < q²`.
* `Y_sq_gt`, `abs_Y_gt`: `q^(4+2e) < Y²`, i.e. `|q|^(2+e) < |Y|`, from `B0 ≤ k² q²`. In
  particular `q² < |Y|` (`q_sq_lt_Y`) and `2^128 < |Y|` (`abs_Y_ge`).
* `A_ge`, `Delta_ge8`: with `Y ≠ 0` the sizes `|A| ≥ 3`, `Delta ≥ 8` of package 138.
* `c_interval`: `|k|(2|Y| − 1) < 2|c| < |k|(2|Y| + 1)` and `0 < c (k Y)`; `c_ne`: `c ≠ 0`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.LCBudget
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing LCValue P138Ports LCBootstrap
open P138Bootstrap (one_le_of_pos' int_split one_le_abs)
open P138Budget (cone_row)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Regs
variable {p : Fin 6 → DiffRing V} {x : Fin 11 → DiffRing V} {κ ω Λ : DiffRing V} {e : ℕ}
variable (ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

/-- The budget power is a square: `q^(6+2e) = (q^(3+e))²`. -/
theorem q_pow_sq (e : ℕ) : (𝓡).q ^ (6 + 2 * e) = ((𝓡).q ^ (3 + e)) ^ 2 := by
  have he : 6 + 2 * e = (3 + e) * 2 := by omega
  rw [he, pow_mul]

/-- **A positive budget makes the free scale nonzero and the inner budget positive.** -/
theorem B0_pos (h : SlotLaw p x κ ω Λ e) (hB : 0 < (𝓡).Budget) :
    (𝓡).Y ≠ 0 ∧ 0 < B0 (𝓡) := by
  rw [h.Budget_eq ψ wt, q_pow_sq ψ wt e] at hB
  have h1 : 0 ≤ (𝓡).k ^ 2 * ((𝓡).q ^ (3 + e)) ^ 2 := by positivity
  have h2 : 0 < (𝓡).Y ^ 2 * B0 (𝓡) := by linarith
  have hY : (𝓡).Y ≠ 0 := by
    intro h0; rw [h0] at h2; simp at h2
  exact ⟨hY, pos_of_mul_pos_right h2 (sq_nonneg _)⟩

/-- **The centered budget.** -/
theorem centered (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) (hB : 0 < (𝓡).Budget) :
    (𝓡).k ≠ 0 ∧ (𝓡).Derr < (𝓡).q ^ 2 ∧ 4 * (𝓡).eta ^ 2 < (𝓡).k ^ 2 ∧
      0 < (𝓡).F * (𝓡).q ∧ 0 < x 1 * (𝓡).q ∧ 0 < ((𝓡).q - (𝓡).F - x 1) * (𝓡).q ∧
      p 4 * ((𝓡).F * (𝓡).q) < 2 * (𝓡).q ^ 2 ∧ p 5 * (x 1 * (𝓡).q) < 2 * (𝓡).q ^ 2 ∧
      4 * ((𝓡).F * (𝓡).q) < (𝓡).q ^ 2 ∧ 4 * (x 1 * (𝓡).q) < (𝓡).q ^ 2 := by
  have hB0 := (B0_pos ψ wt h hB).2
  rw [B0] at hB0
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
  have hq2 : 0 < (𝓡).q ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (q_ne p x κ ω Λ ψ wt hp)))
  have heta : 4 * (𝓡).eta ^ 2 < (𝓡).k ^ 2 := by
    have h1 : 4 * (𝓡).q ^ 2 * (𝓡).eta ^ 2 < (𝓡).k ^ 2 * (𝓡).q ^ 2 := by
      have hDerr0 : 0 ≤ (𝓡).Derr := by rw [Derr_eq]; positivity
      nlinarith
    by_contra hc
    have : (𝓡).k ^ 2 * (𝓡).q ^ 2 ≤ 4 * (𝓡).eta ^ 2 * (𝓡).q ^ 2 :=
      mul_le_mul_of_nonneg_right (le_of_not_gt hc) hq2.le
    linarith
  have hD' := hD
  rw [Derr_eq] at hD'
  have hA : ((p 4) * (𝓡).F - (𝓡).q) ^ 2 < (𝓡).q ^ 2 := by
    have := sq_nonneg (p 5 * x 1 - (𝓡).q); linarith
  have hC : ((p 5) * x 1 - (𝓡).q) ^ 2 < (𝓡).q ^ 2 := by
    have := sq_nonneg (p 4 * (𝓡).F - (𝓡).q); linarith
  obtain ⟨hF1, hF2, hF3⟩ := cone_row hp.coneA_ge hA
  obtain ⟨hC1, hC2, hC3⟩ := cone_row hp.coneB_ge hC
  refine ⟨hk, hD, heta, hF1, hC1, ?_, hF2, hC2, hF3, hC3⟩
  nlinarith

/-- **The scale bound** `q^(4+2e) < Y²` (153's (2.1) with the budget power as a slot):
`B0 ≤ k² q²`, so `k² q^(6+2e) < Y² k² q²`. -/
theorem Y_sq_gt (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) (hB : 0 < (𝓡).Budget) :
    (𝓡).q ^ (4 + 2 * e) < (𝓡).Y ^ 2 := by
  obtain ⟨hk, _, _⟩ := centered ψ wt hp h hB
  have hB' := hB
  rw [h.Budget_eq ψ wt] at hB'
  have hq2 : 0 < (𝓡).q ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (q_ne p x κ ω Λ ψ wt hp)))
  have hk2 : 0 < (𝓡).k ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hk))
  have hle : B0 (𝓡) ≤ (𝓡).k ^ 2 * (𝓡).q ^ 2 := by
    rw [B0]
    have hDerr0 : 0 ≤ (𝓡).Derr := by rw [Derr_eq]; positivity
    have h1 : 0 ≤ (𝓡).k ^ 2 * (𝓡).Derr := mul_nonneg hk2.le hDerr0
    have h2 : 0 ≤ 4 * (𝓡).q ^ 2 * (𝓡).eta ^ 2 := by positivity
    linarith
  have hsplit : (𝓡).q ^ (6 + 2 * e) = (𝓡).q ^ 2 * (𝓡).q ^ (4 + 2 * e) := by
    have he : 6 + 2 * e = 2 + (4 + 2 * e) := by omega
    rw [he, pow_add]
  rw [hsplit] at hB'
  have h3 : (𝓡).Y ^ 2 * B0 (𝓡) ≤ (𝓡).Y ^ 2 * ((𝓡).k ^ 2 * (𝓡).q ^ 2) :=
    mul_le_mul_of_nonneg_left hle (sq_nonneg _)
  have h4 : ((𝓡).k ^ 2 * (𝓡).q ^ 2) * (𝓡).q ^ (4 + 2 * e) <
      ((𝓡).k ^ 2 * (𝓡).q ^ 2) * (𝓡).Y ^ 2 := by
    have e1 : ((𝓡).k ^ 2 * (𝓡).q ^ 2) * (𝓡).q ^ (4 + 2 * e) =
        (𝓡).k ^ 2 * ((𝓡).q ^ 2 * (𝓡).q ^ (4 + 2 * e)) := by ring
    have e2 : ((𝓡).k ^ 2 * (𝓡).q ^ 2) * (𝓡).Y ^ 2 =
        (𝓡).Y ^ 2 * ((𝓡).k ^ 2 * (𝓡).q ^ 2) := by ring
    rw [e1, e2]; linarith
  exact lt_of_mul_lt_mul_left h4 (mul_pos hk2 hq2).le

/-- `|q|^(2+e) < |Y|`. -/
theorem abs_Y_gt (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) (hB : 0 < (𝓡).Budget) :
    |(𝓡).q| ^ (2 + e) < |(𝓡).Y| := by
  have h1 := Y_sq_gt ψ wt hp h hB
  have he : 4 + 2 * e = (2 + e) * 2 := by omega
  rw [he, pow_mul] at h1
  have := _root_.sq_lt_sq.mp h1
  rwa [abs_pow] at this

/-- `q² < |Y|` for either budget power. -/
theorem q_sq_lt_Y (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) (hB : 0 < (𝓡).Budget) :
    (𝓡).q ^ 2 < |(𝓡).Y| := by
  have h1 := abs_Y_gt ψ wt hp h hB
  have hq : (1 : DiffRing V) ≤ |(𝓡).q| := one_le_abs (q_ne p x κ ω Λ ψ wt hp)
  have h2 : |(𝓡).q| ^ 2 ≤ |(𝓡).q| ^ (2 + e) := pow_le_pow_right₀ hq (by omega)
  rw [sq_abs] at h2
  linarith

/-- `2^128 < |Y|`. -/
theorem abs_Y_ge (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) (hB : 0 < (𝓡).Budget) :
    2 ^ 128 < |(𝓡).Y| := by
  have h1 := q_sq_lt_Y ψ wt hp h hB
  have h2 := abs_q_ge p x κ ω Λ ψ wt hp
  have h3 : ((2 : DiffRing V) ^ 64) ^ 2 ≤ |(𝓡).q| ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  rw [sq_abs] at h3
  have h4 : ((2 : DiffRing V) ^ 64) ^ 2 = 2 ^ 128 := by rw [← pow_mul]
  rw [h4] at h3
  linarith

theorem A_ge (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) (hB : 0 < (𝓡).Budget) :
    3 ≤ |(𝓡).A| :=
  abs_A_of_Y p x κ ω Λ ψ wt hp (B0_pos ψ wt h hB).1

theorem Delta_ge8 (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) (hB : 0 < (𝓡).Budget) :
    8 ≤ (𝓡).Delta :=
  Delta_of_Y p x κ ω Λ ψ wt hp (B0_pos ψ wt h hB).1

/-- **The interval for `c`** (`|c/k − Y| < 1/2`). -/
theorem c_interval (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) (hB : 0 < (𝓡).Budget) :
    |(𝓡).k| * (2 * |(𝓡).Y| - 1) < 2 * |x 8| ∧ 2 * |x 8| < |(𝓡).k| * (2 * |(𝓡).Y| + 1) ∧
      0 < x 8 * ((𝓡).k * (𝓡).Y) := by
  obtain ⟨hk, _, heta, _⟩ := centered ψ wt hp h hB
  have h2e : 2 * |(𝓡).eta| < |(𝓡).k| := by
    have h' : (2 * (𝓡).eta) ^ 2 < (𝓡).k ^ 2 := by nlinarith
    have := _root_.sq_lt_sq.mp h'
    rw [abs_mul, abs_two] at this
    exact this
  have hY1 : 1 ≤ |(𝓡).Y| := one_le_abs (B0_pos ψ wt h hB).1
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

theorem c_ne (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) (hB : 0 < (𝓡).Budget) :
    x 8 ≠ 0 := by
  have h' := (c_interval ψ wt hp h hB).2.2
  intro h0; rw [h0, zero_mul] at h'; exact _root_.lt_irrefl _ h'

end Regs

#print axioms B0_pos
#print axioms centered
#print axioms Y_sq_gt
#print axioms abs_Y_gt
#print axioms abs_Y_ge
#print axioms c_interval
#print axioms c_ne

end DiophantineConsistency.LCBudget
