import DiophantineConsistency.P138.P138NoRoot

/-! # The coprime product `BP · Df · Da` and its three square roots

`PROOF.md`, "Soundness", the paragraph after (4). Put `delta = Q − 1`, `Cy = Q V² − 1`,
`Da = delta · Cy`. In every model of `𝗜𝚺₁`, with no sign assumed:

* `bez_BP_Df`, `bez_BP_Da`, `bez_Df_Da`: `BP`, `Df`, `Da` are pairwise coprime, as ring Bezout
  identities in `DiffRing V`. `Df ≡ 1` and `Da ≡ 1 (mod BP)`; modulo `Df` one has
  `Q ≡ −Delta`, `delta ≡ −A²`, `V ≡ −c`, `Cy ≡ −Dm`, hence `Da ≡ A² Dm` (`Da_mod_Df`, exactly
  `Da = A² Dm + Df · M`), while `Df = 1 + A² Dm · w'`.
* `prod_square`: at a zero, `delta · Z = S · w` with `w² = BP · Df · Da` (identity (5); the
  rational square root of an integer is integral, `ZRowsCoprimeSquares.dvd_of_sq_dvd_sq_ring`).
* `roots`: at a zero, `BP = p0²`, `Df = f²`, `Da = e²` with `p0, f, e > 0`. The absolute values are
  squares by pairwise coprimality; `Df ≡ 1 (mod 4)` is not a negative square, so `Df > 0`; if
  `c ≠ 0` then `U ≠ 0` and `BP < 0` would make `Df < 0`; if `c = 0` then `Df = Da = 1` and the
  product square gives `BP > 0`; then `Da > 0` from the product. Also `P > 0` (`P_pos`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P138Squares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P138Value P138Ports P138Bootstrap P138NoRoot

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A negative square is not `1 (mod 4)`. -/
theorem neg_sq_ne (F m : DiffRing V) : -(F * F) ≠ 4 * m + 1 := by
  intro h
  obtain ⟨t, ht | ht⟩ := even_or_odd' F
  · apply four_sub_one_ne (-(t * t) - m)
    rw [ht] at h; linear_combination h
  · rw [ht] at h
    have h2 : (2 : DiffRing V) * (2 * (t * t + t + m) + 1) = 0 := by linear_combination -h
    exact odd_ne_zero' _ ((mul_eq_zero.mp h2).resolve_left (by norm_num))

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V)
local notation "𝓡" => regs p x

/-- The proof register `Da = delta · Cy`. -/
def Da : DiffRing V := ((𝓡).Q - 1) * ((𝓡).Q * (𝓡).V ^ 2 - 1)

/-- The auxiliary offset `b`, with `V = Df · b − c`. -/
def bOff : DiffRing V := x 8 - (𝓡).R + 4 * (𝓡).U * (𝓡).BP * x 7

/-- `LL` of the remainder identities (`verify.py`, "new product Cy remainder"). -/
def LL : DiffRing V := (𝓡).Q * bOff p x * ((𝓡).V - x 8) + (𝓡).Delta * x 8 ^ 2

theorem V_bOff : (𝓡).V = (𝓡).Df * bOff p x - x 8 := by rw [V_eq, bOff]

theorem Q_Df : (𝓡).Q = (𝓡).Delta * ((𝓡).Df - 1) := by rw [Q_eq, Df_eq]; ring

/-- `Cy + Dm = Df · LL`: modulo `Df`, `Cy ≡ −Dm`. -/
theorem Cy_mod_Df : (𝓡).Q * (𝓡).V ^ 2 - 1 = (𝓡).Df * LL p x - (𝓡).Dm := by
  unfold LL
  rw [Q_Df, V_bOff, Dm_eq]; ring

theorem delta_mod_Df : (𝓡).Q - 1 = (𝓡).Delta * (𝓡).Df - (𝓡).A ^ 2 := by
  rw [Q_Df, Delta_eq]; ring

/-- **`Da ≡ A² Dm (mod Df)`.** -/
theorem Da_mod_Df : Da p x = (𝓡).A ^ 2 * (𝓡).Dm +
    (𝓡).Df * ((𝓡).Delta * (𝓡).Df * LL p x - (𝓡).Delta * (𝓡).Dm - (𝓡).A ^ 2 * LL p x) := by
  unfold Da
  rw [delta_mod_Df, Cy_mod_Df]; ring

/-- `Df = 1 + A² Dm · w'`, `w' = Delta (r c²)² P`. -/
theorem Df_AD : (𝓡).Df = 1 + (𝓡).A ^ 2 * (𝓡).Dm * ((𝓡).Delta * (x 4 * x 8 ^ 2) ^ 2 * (𝓡).P) := by
  rw [Df_eq, U_eq, BP_eq]; ring

theorem bez_BP_Df : ∃ α β : DiffRing V, (𝓡).BP * α + (𝓡).Df * β = 1 :=
  ⟨-((𝓡).Delta * (𝓡).U ^ 2), 1, by rw [Df_eq]; ring⟩

theorem bez_BP_Da : ∃ α β : DiffRing V, (𝓡).BP * α + Da p x * β = 1 :=
  ⟨(𝓡).Delta ^ 2 * (𝓡).U ^ 2 * (1 + (𝓡).V ^ 2 - (𝓡).Q * (𝓡).V ^ 2), 1, by
    unfold Da; rw [Q_eq]; ring⟩

theorem bez_Df_Da : ∃ α β : DiffRing V, (𝓡).Df * α + Da p x * β = 1 := by
  set M := (𝓡).Delta * (𝓡).Df * LL p x - (𝓡).Delta * (𝓡).Dm - (𝓡).A ^ 2 * LL p x
  set w := (𝓡).Delta * (x 4 * x 8 ^ 2) ^ 2 * (𝓡).P
  have hDa := Da_mod_Df p x
  have hDf := Df_AD p x
  exact ⟨1 + M * w, -w, by linear_combination (-w) * hDa + hDf⟩

theorem Da_ne (hp : PortFacts p) : Da p x ≠ 0 := by
  obtain ⟨_, _, h1, h2⟩ := nonzero p x hp
  exact mul_ne_zero h1 h2

/-- **Identity (5)**: at a zero, `delta · Z = S · w` with `w² = BP · Df · Da`. -/
theorem prod_square (hp : PortFacts p) (hz : value p x = 0) :
    ∃ w : DiffRing V, ((𝓡).Q - 1) * (𝓡).Z = (𝓡).S * w ∧ w * w = (𝓡).BP * (𝓡).Df * Da p x := by
  have hS := S_ne p x hp hz
  have h5 : (((𝓡).Q - 1) * (𝓡).Z) * (((𝓡).Q - 1) * (𝓡).Z) =
      ((𝓡).S * (𝓡).S) * ((𝓡).BP * (𝓡).Df * Da p x) := by
    rw [value_eq_product] at hz
    unfold Da
    linear_combination ((𝓡).Q - 1) * hz
  obtain ⟨w, hw⟩ := dvd_of_sq_dvd_sq_ring (A := ((𝓡).Q - 1) * (𝓡).Z) (B := (𝓡).S) ⟨_, h5⟩
  refine ⟨w, hw, ?_⟩
  rw [hw] at h5
  have hSS : (𝓡).S * (𝓡).S ≠ 0 := mul_ne_zero hS hS
  apply mul_left_cancel₀ hSS
  linear_combination h5

theorem Df_pos_of_abs (hp : PortFacts p) {f : V} (hf : |(𝓡).Df| = ι f * ι f) : 0 < (𝓡).Df := by
  obtain ⟨_, hDf0, _, _⟩ := nonzero p x hp
  rcases lt_or_gt_of_ne hDf0 with hneg | hpos
  · exfalso
    obtain ⟨m, hm⟩ := Df_mod p x hp
    rw [abs_of_neg hneg] at hf
    apply neg_sq_ne (ι f) m
    rw [← hf, neg_neg, hm]
  · exact hpos

/-- **The three square roots.** At a zero, `BP = p0²`, `Df = f²`, `Da = e²` with positive
`p0, f, e`. -/
theorem roots (hp : PortFacts p) (hz : value p x = 0) :
    ∃ p0 f e : V, 0 < p0 ∧ 0 < f ∧ 0 < e ∧ (𝓡).BP = ι p0 * ι p0 ∧ (𝓡).Df = ι f * ι f ∧
      Da p x = ι e * ι e := by
  obtain ⟨w, _, hw⟩ := prod_square p x hp hz
  obtain ⟨⟨p0, hp0⟩, ⟨f, hf⟩, ⟨e, he⟩⟩ := abs_squares_of_mul_mul_square (bez_BP_Df p x)
    (bez_BP_Da p x) (bez_Df_Da p x) hw.symm
  obtain ⟨hBP0, hDf0, _, _⟩ := nonzero p x hp
  have hDa0 := Da_ne p x hp
  have hDf : 0 < (𝓡).Df := Df_pos_of_abs p x hp hf
  -- `BP > 0`
  have hBP : 0 < (𝓡).BP := by
    by_cases hc : x 8 = 0
    · -- `c = 0`: `Df = Da = 1`, so `BP = w²`
      have hU : (𝓡).U = 0 := by rw [U_eq, hc]; ring
      have hQ : (𝓡).Q = 0 := by rw [Q_eq, hU]; ring
      have hDf1 : (𝓡).Df = 1 := by rw [Df_eq, hU]; ring
      have hDa1 : Da p x = 1 := by unfold Da; rw [hQ]; ring
      rw [hDf1, hDa1, mul_one, mul_one] at hw
      have := mul_self_nonneg w
      exact lt_of_le_of_ne (by linarith) (Ne.symm hBP0)
    · by_contra hneg
      have hBPn : (𝓡).BP ≤ -1 := by
        rcases int_split (𝓡).BP with h | h
        · exact absurd (lt_of_le_of_ne h (Ne.symm hBP0)) hneg
        · exact h
      have hA := abs_A p x hp
      have hA0 : (𝓡).A ≠ 0 := by intro h0; rw [h0, abs_zero] at hA; linarith
      have hU0 : (𝓡).U ≠ 0 := by
        rw [U_eq]
        exact mul_ne_zero (mul_ne_zero hA0 (s_r_ne p x hp hz).2) (pow_ne_zero 2 hc)
      have hU1 : 1 ≤ (𝓡).U ^ 2 := by
        have := one_le_abs hU0; rw [← sq_abs]; nlinarith
      have hD := Delta_gt p x hp
      have hDU : 8 ≤ (𝓡).Delta * (𝓡).U ^ 2 := by nlinarith
      have : (𝓡).Df ≤ 1 - 8 := by
        rw [Df_eq]; nlinarith
      linarith
  have hDa : 0 < Da p x := by
    have h1 : 0 < (𝓡).BP * (𝓡).Df := mul_pos hBP hDf
    have h2 := mul_self_nonneg w
    rw [hw] at h2
    have h3 : 0 ≤ Da p x := by
      by_contra hn
      have : (𝓡).BP * (𝓡).Df * Da p x < 0 := mul_neg_of_pos_of_neg h1 (lt_of_not_ge hn)
      linarith
    exact lt_of_le_of_ne h3 (Ne.symm hDa0)
  have pos_of {Z : DiffRing V} {a : V} (hZ : 0 < Z) (ha : |Z| = ι a * ι a) : 0 < a := by
    rw [abs_of_pos hZ] at ha
    rcases eq_zero_or_pos a with h0 | h0
    · rw [h0, map_zero, mul_zero] at ha; exact absurd ha hZ.ne'
    · exact h0
  refine ⟨p0, f, e, pos_of hBP hp0, pos_of hDf hf, pos_of hDa he, ?_, ?_, ?_⟩
  · rw [← hp0, abs_of_pos hBP]
  · rw [← hf, abs_of_pos hDf]
  · rw [← he, abs_of_pos hDa]

theorem P_pos (hp : PortFacts p) (hz : value p x = 0) : 0 < (𝓡).P := by
  obtain ⟨p0, _, _, hp0, _, _, hBP, _, _⟩ := roots p x hp hz
  have hBPpos : 0 < (𝓡).BP := by
    rw [hBP]; have : (0 : DiffRing V) < ι p0 := by rw [← map_zero ι]; exact ι_lt_ι.mpr hp0
    exact mul_pos this this
  rw [BP_eq] at hBPpos
  exact pos_of_mul_pos_right hBPpos (by linarith [Dm_ge p x hp])

end Regs

#print axioms neg_sq_ne
#print axioms Da_mod_Df
#print axioms bez_BP_Df
#print axioms bez_BP_Da
#print axioms bez_Df_Da
#print axioms prod_square
#print axioms roots
#print axioms P_pos

end DiophantineConsistency.P138Squares
