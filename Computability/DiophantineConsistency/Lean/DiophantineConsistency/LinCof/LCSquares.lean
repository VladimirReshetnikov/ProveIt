import DiophantineConsistency.LinCof.LCNorm
import DiophantineConsistency.P138.P138Squares

/-! # The coprime product `B · Df · Da`, its three square roots, and the guard

For the linear-cofactor registers `LCValue.regsK p x κ ω Λ ψ wt` put `Da = delta · Cy`
(`delta = Q − 1`, `Cy = Q V² − 1`). In every model of `𝗜𝚺₁`, with no sign assumed:

* `bez_B_Df`, `bez_B_Da`, `bez_Df_Da`: the linear cofactor `B = r A Dm` and `Df`, `Da` are pairwise
  coprime, as ring Bezout identities in `DiffRing V`. `Df ≡ 1` and `Da ≡ 1 (mod B)`; modulo `Df`
  one has `Q ≡ −Delta`, `delta ≡ −A²`, `V ≡ −c`, `Cy ≡ −Dm`, hence `Da = A² Dm + Df · M`
  (`Da_mod_Df`), while `Df = 1 + A Dm · w'` with `w' = Delta c⁴ r`. Package 138 had the factor
  `A²` in `Df − 1`; here there is one factor `A`, so the Bezout identity squares `Df − 1`:
  `1 = Df (2 − Df − M Dm w'²) + Da (Dm w'²)`.
* `roots`: at a zero, `B = u²`, `Df = f²`, `Da = e²` with `u, f, e > 0`. The product square is
  `LCNorm.norm`; the absolute values are squares by pairwise coprimality; `Df ≡ 1 (mod 4)` is not
  a negative square, so `Df > 0`; if `c ≠ 0` then `B < 0` would make `Df ≤ 1 − 3`; if `c = 0` then
  `Df = Da = 1` and the product square gives `B > 0`; then `Da > 0` from the product.
* `guard_roots`: at a zero, `P = g²` gives `P > 0`, so `Dg = 1 + Dguard Dt s² > 0`, and the
  coprime factors `Dt`, `Dg` of `P` are squares of positive naturals.
* `budget_ge`: at a zero `Budget ≥ 12` (`Dguard ≤ −1` and `s ≠ 0` would make `Dg ≤ 0`; then
  `LCBootstrap.budget_mod`).

The free scale `Y` is not assumed nonzero here; that is a consequence of `budget_ge`
(`LCBudget`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.LCSquares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing LCValue P138Ports LCBootstrap LCNoRoot LCNorm
open ZRowsCoprimeSquares (abs_squares_of_mul_square abs_squares_of_mul_mul_square)
open P138Bootstrap (one_le_of_pos' int_split one_le_abs)
open P138Squares (neg_sq_ne)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V) (κ ω Λ ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

/-- The proof register `Da = delta · Cy`. -/
def Da : DiffRing V := (𝓡).delta * (𝓡).Cy

/-- The auxiliary offset `b`, with `V = Df · b − c`. -/
def bOff : DiffRing V := x 8 - (𝓡).R + 4 * (𝓡).A * (𝓡).U * x 7

/-- `LL` of the remainder identity `Cy + Dm = Df · LL`. -/
def LL : DiffRing V := (𝓡).Q * bOff p x κ ω Λ ψ wt * ((𝓡).V - x 8) + (𝓡).Delta * x 8 ^ 2

theorem V_bOff : (𝓡).V = (𝓡).Df * bOff p x κ ω Λ ψ wt - x 8 := by rw [V_eq, bOff]

theorem Q_Df : (𝓡).Q = (𝓡).Delta * ((𝓡).Df - 1) := by rw [Q_eq, Df_eq]; ring

/-- `Cy + Dm = Df · LL`: modulo `Df`, `Cy ≡ −Dm`. -/
theorem Cy_mod_Df : (𝓡).Cy = (𝓡).Df * LL p x κ ω Λ ψ wt - (𝓡).Dm := by
  unfold LL
  rw [Cy_eq, Q_Df, V_bOff, Dm_eq]; ring

theorem delta_mod_Df : (𝓡).delta = (𝓡).Delta * (𝓡).Df - (𝓡).A ^ 2 := by
  rw [delta_eq, Q_Df, Delta_eq]; ring

/-- **`Da ≡ A² Dm (mod Df)`.** -/
theorem Da_mod_Df : Da p x κ ω Λ ψ wt = (𝓡).A ^ 2 * (𝓡).Dm +
    (𝓡).Df * ((𝓡).Delta * (𝓡).Df * LL p x κ ω Λ ψ wt - (𝓡).Delta * (𝓡).Dm -
      (𝓡).A ^ 2 * LL p x κ ω Λ ψ wt) := by
  unfold Da
  rw [delta_mod_Df, Cy_mod_Df]; ring

/-- `Df = 1 + A Dm · w'`, `w' = Delta c⁴ r`. -/
theorem Df_AD : (𝓡).Df = 1 + (𝓡).A * (𝓡).Dm * ((𝓡).Delta * x 8 ^ 4 * x 4) := by
  rw [Df_eq, B_eq]; ring

theorem bez_B_Df : ∃ α β : DiffRing V, (𝓡).B * α + (𝓡).Df * β = 1 :=
  ⟨-((𝓡).Delta * x 8 ^ 4), 1, by rw [Df_eq]; ring⟩

theorem bez_B_Da : ∃ α β : DiffRing V, (𝓡).B * α + Da p x κ ω Λ ψ wt * β = 1 :=
  ⟨(𝓡).Delta ^ 2 * x 8 ^ 4 * (1 + (𝓡).V ^ 2 - (𝓡).Q * (𝓡).V ^ 2), 1, by
    unfold Da; rw [delta_eq, Cy_eq, Q_eq]; ring⟩

theorem bez_Df_Da : ∃ α β : DiffRing V, (𝓡).Df * α + Da p x κ ω Λ ψ wt * β = 1 := by
  obtain ⟨M, hDa⟩ : ∃ M : DiffRing V, Da p x κ ω Λ ψ wt = (𝓡).A ^ 2 * (𝓡).Dm + (𝓡).Df * M :=
    ⟨_, Da_mod_Df p x κ ω Λ ψ wt⟩
  obtain ⟨w, hDf⟩ : ∃ w : DiffRing V, (𝓡).Df = 1 + (𝓡).A * (𝓡).Dm * w :=
    ⟨_, Df_AD p x κ ω Λ ψ wt⟩
  exact ⟨2 - (𝓡).Df - M * (𝓡).Dm * w ^ 2, (𝓡).Dm * w ^ 2, by
    linear_combination ((𝓡).Dm * w ^ 2) * hDa - ((𝓡).Df - 1 + (𝓡).A * (𝓡).Dm * w) * hDf⟩

theorem Da_ne : Da p x κ ω Λ ψ wt ≠ 0 := by
  obtain ⟨_, h1, h2⟩ := nonzero p x κ ω Λ ψ wt
  exact mul_ne_zero h1 h2

theorem Df_pos_of_abs {f : V} (hf : |(𝓡).Df| = ι f * ι f) : 0 < (𝓡).Df := by
  obtain ⟨hDf0, _, _⟩ := nonzero p x κ ω Λ ψ wt
  rcases lt_or_gt_of_ne hDf0 with hneg | hpos
  · exfalso
    obtain ⟨m, hm⟩ := Df_mod p x κ ω Λ ψ wt
    rw [abs_of_neg hneg] at hf
    apply neg_sq_ne (ι f) m
    rw [← hf, neg_neg, hm]
  · exact hpos

end Regs

section Zero
variable {p : Fin 6 → DiffRing V} {x : Fin 11 → DiffRing V} {κ ω Λ : DiffRing V} {e : ℕ}
variable (ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

/-- A positive element whose absolute value is a square of a natural is the square of a positive
natural. -/
theorem pos_root {Z : DiffRing V} {a : V} (hZ : 0 < Z) (ha : |Z| = ι a * ι a) :
    0 < a ∧ Z = ι a * ι a := by
  rw [abs_of_pos hZ] at ha
  refine ⟨?_, ha⟩
  rcases eq_zero_or_pos a with h0 | h0
  · rw [h0, map_zero, mul_zero] at ha; exact absurd ha hZ.ne'
  · exact h0

/-- **The three square roots.** At a zero, `B = u²`, `Df = f²`, `Da = e²` with positive
`u, f, e`. -/
theorem roots (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) :
    ∃ u f e : V, 0 < u ∧ 0 < f ∧ 0 < e ∧ (𝓡).B = ι u * ι u ∧ (𝓡).Df = ι f * ι f ∧
      Da p x κ ω Λ ψ wt = ι e * ι e := by
  obtain ⟨_, _, w, _, _, _, hw⟩ := LCNorm.norm ψ wt hp h hwt hz
  have hw' : (𝓡).B * (𝓡).Df * Da p x κ ω Λ ψ wt = w * w := hw.symm
  obtain ⟨⟨u, hu⟩, ⟨f, hf⟩, ⟨e', he⟩⟩ := abs_squares_of_mul_mul_square (bez_B_Df p x κ ω Λ ψ wt)
    (bez_B_Da p x κ ω Λ ψ wt) (bez_Df_Da p x κ ω Λ ψ wt) hw'
  have hB0 := B_ne p x κ ω Λ ψ wt hp hz
  have hDa0 := Da_ne p x κ ω Λ ψ wt
  have hDf : 0 < (𝓡).Df := Df_pos_of_abs p x κ ω Λ ψ wt hf
  -- `B > 0`
  have hB : 0 < (𝓡).B := by
    by_cases hc : x 8 = 0
    · -- `c = 0`: `Df = Da = 1`, so `B = w²`
      have hQ : (𝓡).Q = 0 := by rw [Q_eq, hc]; ring
      have hDf1 : (𝓡).Df = 1 := by rw [Df_eq, hc]; ring
      have hDa1 : Da p x κ ω Λ ψ wt = 1 := by unfold Da; rw [delta_eq, Cy_eq, hQ]; ring
      rw [hDf1, hDa1, mul_one, mul_one] at hw'
      have := mul_self_nonneg w
      exact lt_of_le_of_ne (by linarith) (Ne.symm hB0)
    · by_contra hneg
      have hBn : (𝓡).B ≤ -1 := by
        rcases int_split (𝓡).B with h1 | h1
        · exact absurd (lt_of_le_of_ne h1 (Ne.symm hB0)) hneg
        · exact h1
      have hc2 : 1 ≤ x 8 ^ 2 := by
        have := one_le_abs hc; rw [← sq_abs]; nlinarith
      have hc4 : 1 ≤ x 8 ^ 4 := by
        have h4 : x 8 ^ 4 = x 8 ^ 2 * x 8 ^ 2 := by ring
        rw [h4]; nlinarith
      have hD := Delta_ge p x κ ω Λ ψ wt hp
      have hDc : 3 ≤ (𝓡).Delta * x 8 ^ 4 := by nlinarith
      have h3 := mul_nonneg (show (0 : DiffRing V) ≤ (𝓡).Delta * x 8 ^ 4 by linarith)
        (show (0 : DiffRing V) ≤ -1 - (𝓡).B by linarith)
      have : (𝓡).Df ≤ 1 - 3 := by
        rw [Df_eq]; nlinarith
      linarith
  have hDa : 0 < Da p x κ ω Λ ψ wt := by
    have h1 : 0 < (𝓡).B * (𝓡).Df := mul_pos hB hDf
    have h2 := mul_self_nonneg w
    rw [← hw'] at h2
    have h3 : 0 ≤ Da p x κ ω Λ ψ wt := by
      by_contra hn
      have : (𝓡).B * (𝓡).Df * Da p x κ ω Λ ψ wt < 0 := mul_neg_of_pos_of_neg h1 (lt_of_not_ge hn)
      linarith
    exact lt_of_le_of_ne h3 (Ne.symm hDa0)
  exact ⟨u, f, e', (pos_root hB hu).1, (pos_root hDf hf).1, (pos_root hDa he).1,
    (pos_root hB hu).2, (pos_root hDf hf).2, (pos_root hDa he).2⟩

theorem B_pos (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) :
    0 < (𝓡).B := by
  obtain ⟨u, _, _, hu, _, _, hB, _, _⟩ := roots ψ wt hp h hwt hz
  rw [hB]
  have : (0 : DiffRing V) < ι u := by rw [← map_zero ι]; exact ι_lt_ι.mpr hu
  exact mul_pos this this

theorem P_pos (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) :
    0 < (𝓡).P := by
  obtain ⟨g, _, _, hP, _, _, _⟩ := LCNorm.norm ψ wt hp h hwt hz
  have h0 := P_ne ψ wt hp h
  have := mul_self_nonneg g
  rw [← hP] at this
  exact lt_of_le_of_ne this (Ne.symm h0)

/-- At a zero the guard `Dg = 1 + Dguard Dt s²` is positive. -/
theorem Dg_pos (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) :
    0 < 1 + (𝓡).Dguard * (𝓡).Dt * x 10 ^ 2 := by
  have hP := P_pos ψ wt hp h hwt hz
  obtain ⟨hDt, _⟩ := Dt_facts ψ wt hp h
  rw [P_eq] at hP
  exact pos_of_mul_pos_right hP (by linarith)

/-- **The guard roots.** At a zero, `Dt = τ²` and `Dg = γ²` with positive `τ, γ`. -/
theorem guard_roots (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) :
    ∃ τ γ : V, 0 < τ ∧ 0 < γ ∧ (𝓡).Dt = ι τ * ι τ ∧
      1 + (𝓡).Dguard * (𝓡).Dt * x 10 ^ 2 = ι γ * ι γ := by
  obtain ⟨g, _, _, hP, _, _, _⟩ := LCNorm.norm ψ wt hp h hwt hz
  have hprod : (𝓡).Dt * (1 + (𝓡).Dguard * (𝓡).Dt * x 10 ^ 2) = g * g := by
    rw [← hP, P_eq]
  have hcop : ∃ α β : DiffRing V,
      (𝓡).Dt * α + (1 + (𝓡).Dguard * (𝓡).Dt * x 10 ^ 2) * β = 1 :=
    ⟨-((𝓡).Dguard * x 10 ^ 2), 1, by ring⟩
  obtain ⟨⟨τ, hτ⟩, ⟨γ, hγ⟩⟩ := abs_squares_of_mul_square hcop hprod
  obtain ⟨hDt, _⟩ := Dt_facts ψ wt hp h
  have hDg := Dg_pos ψ wt hp h hwt hz
  exact ⟨τ, γ, (pos_root (by linarith) hτ).1, (pos_root hDg hγ).1,
    (pos_root (by linarith) hτ).2, (pos_root hDg hγ).2⟩

/-- **`Budget ≥ 12` at a zero.** -/
theorem budget_ge (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) :
    12 ≤ (𝓡).Budget := by
  obtain ⟨hDt, _⟩ := Dt_facts ψ wt hp h
  have hs := (s_r_ne p x κ ω Λ ψ wt hp hz).1
  have hs2 : 1 ≤ x 10 ^ 2 := by have := one_le_abs hs; rw [← sq_abs]; nlinarith
  have hDg := Dg_pos ψ wt hp h hwt hz
  have h4 : 4 ≤ (𝓡).Budget := by
    by_contra hlt
    have hD : (𝓡).Dguard ≤ -1 := by
      rw [Dguard_eq]
      rcases int_split ((𝓡).Budget - 4) with h1 | h1
      · exact absurd (by linarith) hlt
      · exact h1
    have : (𝓡).Dguard * (𝓡).Dt * x 10 ^ 2 ≤ -1 := by
      have h1 : (𝓡).Dguard * (𝓡).Dt ≤ -1 := by nlinarith
      nlinarith
    linarith
  obtain ⟨m, hm | hm⟩ := budget_mod ψ wt hp h
  · rw [hm] at h4 ⊢
    have : 0 < m := by linarith
    have := one_le_of_pos' this
    linarith
  · rw [hm] at h4 ⊢
    have : 0 ≤ m := by
      rcases int_split m with h1 | h1
      · exact h1
      · linarith
    linarith

end Zero

#print axioms Da_mod_Df
#print axioms bez_B_Df
#print axioms bez_B_Da
#print axioms bez_Df_Da
#print axioms roots
#print axioms B_pos
#print axioms P_pos
#print axioms guard_roots
#print axioms budget_ge

end DiophantineConsistency.LCSquares
