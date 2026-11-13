import DiophantineConsistency.LinCof.LCValue
import DiophantineConsistency.P138.P138Guard
import DiophantineConsistency.P138.P138Interp
import DiophantineConsistency.ArithmeticPellPowerRecovery
import DiophantineConsistency.ArithmeticPellCongruences

/-! # The linear-cofactor circuit at the canonical record

Completeness of the linear-cofactor family (`LCValue.regsK p x κ ω Λ ψ wt`; package 172's
298/146 and 300/144, and the sibling points of packages 135 and 144) reuses package 138's
canonical record `P138Canonical.Canonical` unchanged.  This module evaluates the circuit's
registers at a point that takes the record's values and derives the facts about the record that
138 did not need:

* `LCMatches Cn x`: `x 0, x 1, x 2, x 6, x 8 = j, C, z, w, c` as in 138, but **`x 5 = Y`**
  (the linear-cofactor circuit reads the scale `Y = v` directly, where 138 had
  `Y = (2v + 1)·q³`).  `x 3` is left free: it is read only by the slot filler `κ`.
* register lemmas `lc_J … lc_K`, generic in the five slots; those that involve `k` take
  `hκ : κ = ι Cn.k`, those that involve `kq2`, `L` take a `SlotLaw … e`;
* `lc_Yq`: `Y − q³ = v·M` (the new `H·(Y − q³)` term of `zc`);
* `X_lt_Y`, `v_pos`: `X < Y` (from `ArithmeticPellPowerRecovery.power_bound`) and `1 ≤ v`
  (else `Y = q³ ≤ R < Exp R = X`);
* `lcBudget Cn e = Y²·B0 − k²·q^(6+2e)`, with `64 < lcBudget Cn e` for `e ≤ 1` (uses `1 ≤ v`
  for `e = 1`) and `16 ∣ lcBudget Cn e`;
* the slot filler `κ` at the record: `k300_canonical` (`x 3 = h`) and `k298_exists`,
  `k298_canonical` (`x 3 = 4s'` with `k = R + 1 + 4·X·Y²·s'`, from
  `ArithmeticPellCongruences.first_transport`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.LCCanonical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing P138Ports LCValue
open P138Canonical (Canonical)
open ArithmeticPellRecurrence (xcoord ycoord)

attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho coneA coneB

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Images of the record's equations in `DiffRing V` -/

theorem iota_J (Cn : Canonical V) : ι Cn.J = 6 * ι Cn.j + 1 := by
  have h := congrArg (ι (V := V)) Cn.J_eq
  simp only [map_add, map_mul, map_ofNat, map_one] at h
  linear_combination h

theorem iota_W (Cn : Canonical V) : ι Cn.W = 12 * ι Cn.w + 4 := by
  have h := congrArg (ι (V := V)) Cn.W_eq
  simp only [map_add, map_mul, map_ofNat] at h
  linear_combination h

theorem iota_X (Cn : Canonical V) : ι Cn.X = ι Cn.q * ι Cn.W := by
  have h := congrArg (ι (V := V)) Cn.X_eq
  simp only [map_mul] at h
  linear_combination h

theorem iota_Y (Cn : Canonical V) : ι Cn.Y = (2 * ι Cn.v + 1) * ι Cn.q ^ 3 := by
  have h := congrArg (ι (V := V)) Cn.Y_eq
  simp only [map_add, map_mul, map_pow, map_ofNat, map_one] at h
  linear_combination h

theorem iota_E (Cn : Canonical V) : ι Cn.E = ι Cn.X * ι Cn.Y := by
  have h := congrArg (ι (V := V)) Cn.E_eq
  simp only [map_mul] at h
  linear_combination h

theorem iota_a (Cn : Canonical V) : ι Cn.a = ι Cn.E + ι Cn.Y := by
  have h := congrArg (ι (V := V)) Cn.a_eq
  simp only [map_add] at h
  linear_combination h

theorem iota_c (Cn : Canonical V) : ι Cn.c = ι Cn.k * ι Cn.Y + ι Cn.η := by
  have h := congrArg (ι (V := V)) Cn.c_eta
  simp only [map_add, map_mul] at h
  linear_combination h

theorem iota_tau (Cn : Canonical V) :
    ι Cn.τ * ι Cn.τ =
      1 + (ι Cn.X * ι Cn.Y * ι Cn.Y) * (ι Cn.X * ι Cn.Y * ι Cn.Y + 1) * ι Cn.k * ι Cn.k := by
  have h := congrArg (ι (V := V)) Cn.τ_norm
  simp only [map_add, map_mul, map_one] at h
  linear_combination h

theorem iota_d (Cn : Canonical V) :
    ι Cn.d * ι Cn.d = 1 + (ι Cn.a + 1) * (ι Cn.a + 3) * ι Cn.c * ι Cn.c := by
  have h := congrArg (ι (V := V)) Cn.d_norm
  simp only [map_add, map_mul, map_one, map_ofNat] at h
  linear_combination h

theorem iota_q_ge (Cn : Canonical V) : (16 : DiffRing V) ≤ ι Cn.q := by
  rw [show (16 : DiffRing V) = ι 16 by rw [map_ofNat]]
  exact ι_le_ι.mpr Cn.q_ge

/-! ## Order facts about the record that the linear-cofactor circuit needs -/

theorem X_ge (Cn : Canonical V) : (16 : V) ≤ Cn.X := by
  have hW1 : (1 : V) ≤ Cn.W := by
    rw [Cn.W_eq]
    exact le_trans (by norm_num : (1 : V) ≤ 4) le_add_self
  rw [Cn.X_eq]
  exact le_trans Cn.q_ge (le_mul_of_one_le_right (Arithmetic.zero_le _) hW1)

theorem Y_ge (Cn : Canonical V) : (1 : V) ≤ Cn.Y := by
  have hq1 : (1 : V) ≤ Cn.q := le_trans (by norm_num) Cn.q_ge
  rw [Cn.Y_eq]
  exact one_le_mul_of_one_le_of_one_le le_add_self (one_le_pow₀ hq1)

/-- `q³ ≤ R`: `R = (q(q − F) − C)(q² − 1) + (MC + q·MF)·J`, `q − F = C + α` with `C, α ≥ 1`, so
`q(q − F) − C = (q − 1)C + qα ≥ 2q − 1` and `(2q − 1)(q² − 1) ≥ q³` for `q ≥ 16`. -/
theorem q_cube_le_R (Cn : Canonical V) : Cn.q ^ 3 ≤ Cn.R := by
  have hq16 := iota_q_ge Cn
  have hC1 : (1 : DiffRing V) ≤ ι Cn.C := by
    rw [← map_one (ι (V := V))]
    exact ι_le_ι.mpr (pos_iff_one_le.mp Cn.C_pos)
  have hα1 : (1 : DiffRing V) ≤ ι Cn.α := by
    rw [← map_one (ι (V := V))]
    exact ι_le_ι.mpr (pos_iff_one_le.mp Cn.α_pos)
  have hsplit : ι Cn.q = ι Cn.F + (ι Cn.C + ι Cn.α) := by
    have h := congrArg (ι (V := V)) Cn.q_split
    simp only [map_add] at h
    linear_combination h
  have hJ0 : (0 : DiffRing V) ≤ ι Cn.J := ι_nonneg _
  have hp2 : (0 : DiffRing V) ≤ portsR (V := V) 2 := (portFacts (V := V)).MC_nonneg
  have hp3 : (0 : DiffRing V) ≤ portsR (V := V) 3 := (portFacts (V := V)).MF_nonneg
  have hq0 : (0 : DiffRing V) ≤ ι Cn.q := by linarith
  have htail : (0 : DiffRing V) ≤ (portsR (V := V) 2 + ι Cn.q * portsR (V := V) 3) * ι Cn.J :=
    mul_nonneg (add_nonneg hp2 (mul_nonneg hq0 hp3)) hJ0
  have e1 : ι Cn.q * (ι Cn.q - ι Cn.F) - ι Cn.C =
      (ι Cn.q - 1) * ι Cn.C + ι Cn.q * ι Cn.α := by
    linear_combination ι Cn.q * hsplit
  have hA : (0 : DiffRing V) ≤ (ι Cn.q - 1) * (ι Cn.C - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hB : (0 : DiffRing V) ≤ ι Cn.q * (ι Cn.α - 1) := mul_nonneg hq0 (by linarith)
  have h1 : 2 * ι Cn.q - 1 ≤ ι Cn.q * (ι Cn.q - ι Cn.F) - ι Cn.C := by
    rw [e1]
    linarith
  have hq2 : (0 : DiffRing V) ≤ ι Cn.q ^ 2 - 1 := by nlinarith
  have h2 : (2 * ι Cn.q - 1) * (ι Cn.q ^ 2 - 1) ≤
      (ι Cn.q * (ι Cn.q - ι Cn.F) - ι Cn.C) * (ι Cn.q ^ 2 - 1) :=
    mul_le_mul_of_nonneg_right h1 hq2
  have hC2 : (0 : DiffRing V) ≤ ι Cn.q ^ 2 * (ι Cn.q - 16) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hC3 : (0 : DiffRing V) ≤ ι Cn.q * (ι Cn.q - 16) := mul_nonneg hq0 (by linarith)
  have h3 : ι Cn.q ^ 3 ≤ (2 * ι Cn.q - 1) * (ι Cn.q ^ 2 - 1) := by
    -- (2q − 1)(q² − 1) − q³ = q²(q − 16) + 15·q(q − 16) + 238·q + 1
    nlinarith
  have hR : ι (Cn.q ^ 3) ≤ ι Cn.R := by
    rw [map_pow, Cn.R_reg]
    linarith
  exact ι_le_ι.mp hR

/-- `X < Y`: the power-recovery bound `Exp (2r + 1) < Y` at the record. -/
theorem X_lt_Y (Cn : Canonical V) : Cn.X < Cn.Y := by
  have hr2 : (2 : V) ≤ Cn.r := le_trans (by norm_num) Cn.r_ge
  have ha : Cn.a = Cn.Y * (Cn.X + 1) := by
    rw [Cn.a_eq, Cn.E_eq]
    ring
  have hc : Cn.c = ycoord (2 * Cn.r + 1) (Cn.Y * (Cn.X + 1)) := by
    rw [← ha, ← Cn.R_odd]
    exact Cn.c_main
  have h := ArithmeticPellPowerRecovery.power_bound Cn.X Cn.Y Cn.r Cn.k Cn.c Cn.η Cn.ζ
    (X_ge Cn) (Y_ge Cn) hr2 Cn.c_eta Cn.k_split Cn.ζ_pos hc Cn.k_first
  rw [← Cn.R_odd, ← Cn.X_exp] at h
  exact h

/-- `1 ≤ v`: if `v = 0` then `Y = q³ ≤ R < Exp R = X < Y`. -/
theorem v_pos (Cn : Canonical V) : 1 ≤ Cn.v := by
  rcases (Arithmetic.zero_le Cn.v).lt_or_eq with h | h
  · exact pos_iff_one_le.mp h
  · exfalso
    have hY : Cn.Y = Cn.q ^ 3 := by
      rw [Cn.Y_eq, ← h]
      ring
    have h1 : Cn.Y ≤ Cn.R := by
      rw [hY]
      exact q_cube_le_R Cn
    have h2 : Cn.R < Cn.X := by
      rw [Cn.X_exp]
      exact lt_exp _
    exact absurd (X_lt_Y Cn) (not_lt.mpr (le_trans h1 (le_of_lt h2)))

/-! ## The registers at a matching point -/

/-- `x` takes the six canonical values the linear-cofactor circuit reads outside its slots.
Note `x 5 = Y` (the free scale), where 138's `Matches` has `x 5 = v`. -/
structure LCMatches (Cn : Canonical V) (x : Fin 11 → DiffRing V) : Prop where
  x0 : x 0 = ι Cn.j
  x1 : x 1 = ι Cn.C
  x2 : x 2 = ι Cn.z
  x5 : x 5 = ι Cn.Y
  x6 : x 6 = ι Cn.w
  x8 : x 8 = ι Cn.c

section Registers
variable (Cn : Canonical V) {x : Fin 11 → DiffRing V} (hx : LCMatches Cn x)
  (κ ω Λ ψ wt : DiffRing V)
local notation "𝓡" => regsK (portsR (V := V)) x κ ω Λ ψ wt
include hx

theorem lc_J : (𝓡).J = ι Cn.J := by
  rw [J_def, hx.x0]
  linear_combination (-1 : DiffRing V) * iota_J Cn

theorem lc_q : (𝓡).q = ι Cn.q := by
  rw [q_eq, hx.x0]
  linear_combination (-1 : DiffRing V) * Cn.q_reg - portsR (V := V) 0 * iota_J Cn

theorem lc_W : (𝓡).W = ι Cn.W := by
  rw [W_eq, hx.x6]
  linear_combination (-1 : DiffRing V) * iota_W Cn

theorem lc_X : (𝓡).X = ι Cn.X := by
  rw [X_def, lc_q Cn hx κ ω Λ ψ wt, lc_W Cn hx κ ω Λ ψ wt]
  linear_combination (-1 : DiffRing V) * iota_X Cn

theorem lc_Y : (𝓡).Y = ι Cn.Y := by
  rw [Y_def]
  exact hx.x5

theorem lc_E : (𝓡).E = ι Cn.E := by
  rw [E_eq, lc_X Cn hx κ ω Λ ψ wt, lc_Y Cn hx κ ω Λ ψ wt]
  linear_combination (-1 : DiffRing V) * iota_E Cn

theorem lc_a : (𝓡).a = ι Cn.a := by
  rw [a_def, lc_E Cn hx κ ω Λ ψ wt, lc_Y Cn hx κ ω Λ ψ wt]
  linear_combination (-1 : DiffRing V) * iota_a Cn

theorem lc_A : (𝓡).A = ι Cn.a + 2 := by
  rw [A_eq, lc_a Cn hx κ ω Λ ψ wt]

theorem lc_H : (𝓡).H = 4 * ι Cn.a + 3 := by
  rw [H_eq, lc_a Cn hx κ ω Λ ψ wt]

theorem lc_Delta : (𝓡).Delta = (ι Cn.a + 1) * (ι Cn.a + 3) := by
  rw [Delta_eq, lc_A Cn hx κ ω Λ ψ wt]
  ring

theorem lc_F : (𝓡).F = ι Cn.F := by
  rw [F_eq, hx.x1, hx.x2, lc_W Cn hx κ ω Λ ψ wt, lc_q Cn hx κ ω Λ ψ wt]
  linear_combination (-1 : DiffRing V) * Cn.F_reg

theorem lc_R : (𝓡).R = ι Cn.R := by
  rw [R_eq, lc_q Cn hx κ ω Λ ψ wt, lc_F Cn hx κ ω Λ ψ wt, hx.x1, lc_J Cn hx κ ω Λ ψ wt]
  linear_combination (-1 : DiffRing V) * Cn.R_reg

omit hx in
theorem lc_k (hκ : κ = ι Cn.k) : (𝓡).k = ι Cn.k := by
  rw [k_reg]
  exact hκ

theorem lc_eta (hκ : κ = ι Cn.k) : (𝓡).eta = ι Cn.η := by
  rw [eta_eq, hx.x8, lc_Y Cn hx κ ω Λ ψ wt, lc_k Cn κ ω Λ ψ wt hκ]
  linear_combination iota_c Cn

/-- The cone budget `B0 = k²(q² − Derr) − 4q²η²` is package 138's `Budget` at the record. -/
theorem lc_B0 (hκ : κ = ι Cn.k) : B0 (𝓡) = P138Guard.budget Cn := by
  show (𝓡).k ^ 2 * ((𝓡).q ^ 2 - (𝓡).Derr) - 4 * (𝓡).q ^ 2 * (𝓡).eta ^ 2 = P138Guard.budget Cn
  unfold P138Guard.budget
  rw [Derr_eq, lc_F Cn hx κ ω Λ ψ wt, lc_q Cn hx κ ω Λ ψ wt, hx.x1,
    lc_eta Cn hx κ ω Λ ψ wt hκ, lc_k Cn κ ω Λ ψ wt hκ]

theorem lc_Dm : (𝓡).Dm = ι Cn.d * ι Cn.d := by
  rw [Dm_eq, lc_Delta Cn hx κ ω Λ ψ wt, hx.x8]
  linear_combination (-1 : DiffRing V) * iota_d Cn

/-- The centre: `K = H·κ` with the record's `κ` (field `Cn.κ`, not the slot `κ`). -/
theorem lc_K : (𝓡).K = (𝓡).H * Cn.κ := by
  rw [K_eq, lc_X Cn hx κ ω Λ ψ wt, hx.x8, lc_H Cn hx κ ω Λ ψ wt]
  linear_combination Cn.K_split

/-- The new carrier term: `Y − q³ = v·M`, `M = 2q³`, because `Y = (2v + 1)·q³`. -/
theorem lc_Yq : (𝓡).Y - (𝓡).q ^ 3 = ι Cn.v * (𝓡).M := by
  rw [M_eq, lc_Y Cn hx κ ω Λ ψ wt, lc_q Cn hx κ ω Λ ψ wt]
  linear_combination iota_Y Cn

end Registers

/-! ## The guard budget in record form -/

/-- `Budget` of the linear-cofactor circuit at the record, for a slot law of exponent `e`. -/
def lcBudget (Cn : Canonical V) (e : ℕ) : DiffRing V :=
  ι Cn.Y ^ 2 * P138Guard.budget Cn - ι Cn.k ^ 2 * ι Cn.q ^ (6 + 2 * e)

section Slots
variable (Cn : Canonical V) {x : Fin 11 → DiffRing V} (hx : LCMatches Cn x)
  (κ ω Λ ψ wt : DiffRing V) {e : ℕ}
local notation "𝓡" => regsK (portsR (V := V)) x κ ω Λ ψ wt
include hx

theorem lc_Budget (hlaw : SlotLaw (portsR (V := V)) x κ ω Λ e) (hκ : κ = ι Cn.k) :
    (𝓡).Budget = lcBudget Cn e := by
  unfold lcBudget
  rw [hlaw.Budget_eq ψ wt, lc_B0 Cn hx κ ω Λ ψ wt hκ, lc_Y Cn hx κ ω Λ ψ wt,
    lc_q Cn hx κ ω Λ ψ wt, lc_k Cn κ ω Λ ψ wt hκ]

theorem lc_Dt (hlaw : SlotLaw (portsR (V := V)) x κ ω Λ e) (hκ : κ = ι Cn.k) :
    (𝓡).Dt = ι Cn.τ * ι Cn.τ := by
  rw [hlaw.Dt_eq ψ wt, lc_X Cn hx κ ω Λ ψ wt, lc_Y Cn hx κ ω Λ ψ wt,
    lc_k Cn κ ω Λ ψ wt hκ]
  linear_combination (-1 : DiffRing V) * iota_tau Cn

end Slots

/-- Package 138's two budget inequalities, in record form. -/
theorem budget_facts (Cn : Canonical V) :
    ι Cn.q ^ 2 * ι Cn.k ^ 2 < 4 * P138Guard.budget Cn ∧ 64 < P138Guard.budget Cn := by
  have h := P138Canonical.canonical_budget Cn (P138Guard.canonX_matches Cn)
  rw [P138Canonical.reg_q Cn (P138Guard.canonX_matches Cn),
    P138Canonical.reg_k Cn (P138Guard.canonX_matches Cn),
    P138Guard.reg_Budget Cn (P138Guard.canonX_matches Cn)] at h
  exact h

/-- `Budget > 64` for the slot laws `e = 0` (298/146) and `e = 1` (300/144 and the sibling
points).  `k²q^(6+2e) ≤ k²q⁸ = q⁶·(q²k²) < q⁶·4·B0` and `Y²·B0 = (2v+1)²q⁶·B0 ≥ 9q⁶·B0`
(`1 ≤ v`), so `Budget > 5q⁶·B0 ≥ 5·B0 > 64`. -/
theorem lcBudget_gt (Cn : Canonical V) {e : ℕ} (he : e ≤ 1) : 64 < lcBudget Cn e := by
  obtain ⟨hb4, hb64⟩ := budget_facts Cn
  have hq16 := iota_q_ge Cn
  have hq1 : (1 : DiffRing V) ≤ ι Cn.q := by linarith
  have hv1 : (1 : DiffRing V) ≤ ι Cn.v := by
    rw [← map_one (ι (V := V))]
    exact ι_le_ι.mpr (v_pos Cn)
  have hY := iota_Y Cn
  have hq6 : (1 : DiffRing V) ≤ ι Cn.q ^ 6 := one_le_pow₀ hq1
  have hpow : ι Cn.q ^ (6 + 2 * e) ≤ ι Cn.q ^ 8 := pow_le_pow_right₀ hq1 (by omega)
  have h1 : ι Cn.k ^ 2 * ι Cn.q ^ (6 + 2 * e) ≤ ι Cn.k ^ 2 * ι Cn.q ^ 8 :=
    mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
  have h2 : ι Cn.k ^ 2 * ι Cn.q ^ 8 ≤ ι Cn.q ^ 6 * (4 * P138Guard.budget Cn) := by
    have h : ι Cn.q ^ 6 * (ι Cn.q ^ 2 * ι Cn.k ^ 2) ≤ ι Cn.q ^ 6 * (4 * P138Guard.budget Cn) :=
      mul_le_mul_of_nonneg_left (le_of_lt hb4) (by linarith)
    calc ι Cn.k ^ 2 * ι Cn.q ^ 8 = ι Cn.q ^ 6 * (ι Cn.q ^ 2 * ι Cn.k ^ 2) := by ring
      _ ≤ ι Cn.q ^ 6 * (4 * P138Guard.budget Cn) := h
  have hb0 : (0 : DiffRing V) ≤ P138Guard.budget Cn := by linarith
  have hqb : P138Guard.budget Cn ≤ ι Cn.q ^ 6 * P138Guard.budget Cn :=
    le_mul_of_one_le_left hb0 hq6
  have hv9 : (9 : DiffRing V) ≤ (2 * ι Cn.v + 1) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hv1) (sub_nonneg.mpr hv1)]
  have h3 : 9 * (ι Cn.q ^ 6 * P138Guard.budget Cn) ≤ ι Cn.Y ^ 2 * P138Guard.budget Cn := by
    have h : 9 * (ι Cn.q ^ 6 * P138Guard.budget Cn) ≤
        (2 * ι Cn.v + 1) ^ 2 * (ι Cn.q ^ 6 * P138Guard.budget Cn) :=
      mul_le_mul_of_nonneg_right hv9 (by linarith)
    calc 9 * (ι Cn.q ^ 6 * P138Guard.budget Cn)
        ≤ (2 * ι Cn.v + 1) ^ 2 * (ι Cn.q ^ 6 * P138Guard.budget Cn) := h
      _ = ι Cn.Y ^ 2 * P138Guard.budget Cn := by rw [hY]; ring
  unfold lcBudget
  linarith

/-- `16 ∣ Budget`: `q = β·J + 1` is even (`β ≡ 1 mod 6`, `J = 6j + 1`), `Y = (2v+1)q³`, so both
terms of `Y²·B0 − k²·q^(6+2e)` carry the factor `q⁶ = 64·(q/2)⁶`. -/
theorem lcBudget_mod (Cn : Canonical V) (e : ℕ) : ∃ w : DiffRing V, lcBudget Cn e = 16 * w := by
  obtain ⟨m, hm⟩ := (portFacts (V := V)).beta_mod
  have hq : ι Cn.q = 2 * (18 * m * ι Cn.j + 3 * m + 3 * ι Cn.j + 1) := by
    linear_combination Cn.q_reg + portsR (V := V) 0 * iota_J Cn + (6 * ι Cn.j + 1) * hm
  obtain ⟨q', hq'⟩ : ∃ q' : DiffRing V, ι Cn.q = 2 * q' := ⟨_, hq⟩
  have h6 : ι Cn.q ^ 6 = 64 * q' ^ 6 := by
    rw [hq']
    ring
  have hY := iota_Y Cn
  refine ⟨4 * q' ^ 6 * ((2 * ι Cn.v + 1) ^ 2 * P138Guard.budget Cn -
    ι Cn.k ^ 2 * ι Cn.q ^ (2 * e)), ?_⟩
  unfold lcBudget
  rw [hY]
  linear_combination
    ((2 * ι Cn.v + 1) ^ 2 * P138Guard.budget Cn - ι Cn.k ^ 2 * ι Cn.q ^ (2 * e)) * h6

/-! ## The slot filler `κ` at the record -/

/-- 300/144 and the sibling points: `k = 1 + R + h·E` with `x 3 = h`. -/
theorem k300_canonical (Cn : Canonical V) {x : Fin 11 → DiffRing V} (hx : LCMatches Cn x)
    (hx3 : x 3 = ι Cn.h) : k300 (portsR (V := V)) x = ι Cn.k := by
  have hk := congrArg (ι (V := V)) Cn.k_eq
  simp only [map_add, map_mul, map_one] at hk
  show 1 + (regsK (portsR (V := V)) x 0 0 0 0 0).R +
    x 3 * (regsK (portsR (V := V)) x 0 0 0 0 0).E = ι Cn.k
  rw [lc_R Cn hx 0 0 0 0 0, E_eq, lc_X Cn hx 0 0 0 0 0, lc_Y Cn hx 0 0 0 0 0, hx3]
  linear_combination (-1 : DiffRing V) * hk - ι Cn.h * iota_E Cn

/-- 298/146 needs `k = 1 + R + h'·X·Y²`: the first-transport congruence of the guard ordinate,
`k = 2·y_{r+1}(2XY² − 1) ≡ R + 1 (mod 4XY²)`. -/
theorem k298_exists (Cn : Canonical V) :
    ∃ h3 : V, Cn.k = Cn.R + 1 + h3 * (Cn.X * Cn.Y * Cn.Y) := by
  have hX1 : (1 : V) ≤ Cn.X := le_trans (by norm_num) (X_ge Cn)
  have hY1 := Y_ge Cn
  have hXYY : 1 ≤ Cn.X * Cn.Y * Cn.Y :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hX1 hY1) hY1
  have hb : 2 * (Cn.X * Cn.Y * Cn.Y - 1) + 1 + 1 = 2 * (Cn.X * Cn.Y * Cn.Y) := by
    have h := tsub_add_cancel_of_le hXYY
    calc 2 * (Cn.X * Cn.Y * Cn.Y - 1) + 1 + 1 = 2 * (Cn.X * Cn.Y * Cn.Y - 1 + 1) := by ring
      _ = 2 * (Cn.X * Cn.Y * Cn.Y) := by rw [h]
  have hR : Cn.R + 1 = 2 * (Cn.r + 1) := by
    rw [Cn.R_odd]
    ring
  obtain ⟨s', hs'⟩ := ArithmeticPellCongruences.first_transport (Cn.r + 1)
    (2 * (Cn.X * Cn.Y * Cn.Y - 1) + 1) (Cn.X * Cn.Y * Cn.Y) Cn.R Cn.k hb Cn.k_first hR
  exact ⟨4 * s', hs'.trans (by ring)⟩

theorem k298_canonical (Cn : Canonical V) {x : Fin 11 → DiffRing V} (hx : LCMatches Cn x)
    {h3 : V} (hk : Cn.k = Cn.R + 1 + h3 * (Cn.X * Cn.Y * Cn.Y)) (hx3 : x 3 = ι h3) :
    k298 (portsR (V := V)) x = ι Cn.k := by
  have hk' := congrArg (ι (V := V)) hk
  simp only [map_add, map_mul, map_one] at hk'
  show 1 + (regsK (portsR (V := V)) x 0 0 0 0 0).R +
    x 3 * (regsK (portsR (V := V)) x 0 0 0 0 0).ell = ι Cn.k
  rw [lc_R Cn hx 0 0 0 0 0, ell_eq, lc_X Cn hx 0 0 0 0 0, lc_Y Cn hx 0 0 0 0 0, hx3]
  linear_combination (-1 : DiffRing V) * hk'

#print axioms q_cube_le_R
#print axioms X_lt_Y
#print axioms v_pos
#print axioms lc_R
#print axioms lc_B0
#print axioms lc_Budget
#print axioms lc_Dt
#print axioms lc_Dm
#print axioms lc_K
#print axioms lc_Yq
#print axioms lcBudget_gt
#print axioms lcBudget_mod
#print axioms k300_canonical
#print axioms k298_exists
#print axioms k298_canonical

end DiophantineConsistency.LCCanonical
