import DiophantineConsistency.P135W.P135WValue
import DiophantineConsistency.P137.P137Roots

/-! # The square roots of package 135's 398/121 equation

At a zero of the output `P135WValue.value p x` in the ring of differences of a model of `𝗜𝚺₁`,
with the port facts of package 138 (`P138Ports.PortFacts`). The registers are those of the
weak front `P137Front.front p x` and of the back end `P135WValue.back p x`; no index slot occurs.

* **Congruences.** `Budget ≡ 0 (mod 4)` on the weak front (`q` is even and both cones are
  multiples of 16), hence `P ≡ 1 (mod 4)`; `Df ≡ 1 (mod 4)`; `Q` is even.
* **Nonvanishing.** `δ`, `Df`, `Cy`, `P` are nonzero everywhere; at a zero `S ≠ 0` (the output
  at `S = 0` is `(δ Ac²)²`), hence `r, s ≠ 0`, and `Z ≠ 0` (otherwise `δ P = 4 B Df Cy`, odd
  against even).
* **Norm extraction** (`norm`). The output is the norm `𝓘² − 𝓣² P`, so `P = g²` and
  `δ (Z − S g) = 2 S w` with `w² = B · Df · (δ Cy)`.
* **The three squares** (`roots`). `B`, `Df` and `Da = δ Cy` are pairwise coprime by ring
  Bézout identities, so each is a square with a positive root.
* **The guard** (`Dt_square`, `budget_pos`). `Dt` is coprime to its cofactor in `P`, so it is
  a square, and a positive cofactor with `s ≠ 0` gives `Budget > 0`.
* **The descent** (`descent`, `S_dvd_Ac`). For `c ≠ 0` the adjacent descent gives the integral
  auxiliary ordinate; in both cases `S ∣ Ac`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P135WRoots
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P137Front P135WValue P138Ports

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V)
local notation "𝓕" => front p x
local notation "𝓑" => back p x

/-! ## Congruences -/

/-- `Budget ≡ 0 (mod 4)` on the weak front. -/
theorem budget_mod (hp : PortFacts p) : ∃ d : DiffRing V, (𝓕).Budget = 4 * d := by
  obtain ⟨t, ht⟩ := P137Bootstrap.q_even p x hp
  obtain ⟨u, hu⟩ := hp.coneA_sixteen
  obtain ⟨v, hv⟩ := hp.coneB_sixteen
  refine ⟨(𝓕).k ^ 2 * (t ^ 2 - (8 * u * (𝓕).F - t) ^ 2 - (8 * x 1 * v - t) ^ 2) -
    4 * t ^ 2 * (𝓕).eta ^ 2, ?_⟩
  rw [Budget_eq, Derr_def, ht, hu, hv]; ring

/-- `P ≡ 1 (mod 4)`. -/
theorem P_mod (hp : PortFacts p) : ∃ m : DiffRing V, (𝓑).P = 4 * m + 1 := by
  obtain ⟨d, hd⟩ := budget_mod p x hp
  obtain ⟨_, m, hm⟩ := P137Bootstrap.Dt_facts p x hp
  refine ⟨2 * m + 8 * m * ((d - 1) * (𝓕).Dt * x 10 ^ 2) + (d - 1) * (𝓕).Dt * x 10 ^ 2, ?_⟩
  rw [P_eq, Dguard_def]
  linear_combination (1 + 4 * ((d - 1) * (𝓕).Dt * x 10 ^ 2)) * hm +
    ((𝓕).Dt * ((𝓕).Dt * x 10 ^ 2)) * hd

/-- `Df ≡ 1 (mod 4)`: `A` is even, and either `c` is even or `Dm` is a multiple of 4. -/
theorem Df_mod (hp : PortFacts p) : ∃ m : DiffRing V, (𝓑).Df = 4 * m + 1 := by
  obtain ⟨m, hm⟩ := P137Bootstrap.A_even p x hp
  have hD := Df_eq p x
  have hB := B_eq p x
  have hDm := Dm_eq p x
  have hΔ := Delta_eq p x
  obtain ⟨t, ht | ht⟩ := P138Bootstrap.even_or_odd' (x 8)
  · exact ⟨(𝓕).Delta * (4 * t ^ 4) * (𝓑).B, by rw [hD, ht]; ring⟩
  · refine ⟨(𝓕).Delta * x 8 ^ 4 * ((𝓕).A * x 4) * (m ^ 2 * x 8 ^ 2 - t ^ 2 - t), ?_⟩
    rw [hD, hB, hDm, hΔ, hm, ht]; ring

/-- `Q` is even. -/
theorem Q_even (hp : PortFacts p) : ∃ n : DiffRing V, (𝓑).Q = 2 * n := by
  obtain ⟨m, hm⟩ := P137Bootstrap.A_even p x hp
  have hQ := Q_eq p x
  have hB := B_eq p x
  exact ⟨(𝓕).Delta ^ 2 * x 8 ^ 4 * (m * x 4 * (𝓕).Dm), by rw [hQ, hB, hm]; ring⟩

/-! ## Unconditional nonvanishing -/

theorem Delta_two (hp : PortFacts p) : 2 ≤ (𝓕).Delta := by
  linarith [P137Bootstrap.Delta_ge p x hp]

theorem delta_ne (hp : PortFacts p) : (𝓑).delta ≠ 0 := by
  intro h
  apply P137Roots.mul_ne_one (Delta_two p x hp) (t := (𝓑).strong)
  rw [delta_def, Q_def] at h
  linear_combination h

theorem Df_ne (hp : PortFacts p) : (𝓑).Df ≠ 0 := by
  intro h
  apply P137Roots.mul_ne_one (Delta_two p x hp) (t := -(x 8 ^ 4 * (𝓑).B))
  rw [Df_eq] at h
  linear_combination -h

theorem Cy_ne (hp : PortFacts p) : (𝓑).Cy ≠ 0 := by
  intro h
  apply P137Roots.mul_ne_one (Delta_two p x hp) (t := (𝓑).strong * (𝓑).V ^ 2)
  rw [Cy_def, Q_def] at h
  linear_combination h

theorem P_ne (hp : PortFacts p) : (𝓑).P ≠ 0 := by
  obtain ⟨m, hm⟩ := P_mod p x hp
  rw [hm]; exact P138Bootstrap.four_add_one_ne m

/-! ## At a zero: `S ≠ 0` and `Z ≠ 0` -/

theorem S_ne (hp : PortFacts p) (hz : value p x = 0) : (𝓕).S ≠ 0 := by
  intro hS
  rw [value_S_zero p x hS] at hz
  have h1 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp hz
  rcases mul_eq_zero.mp h1 with h | h
  · exact delta_ne p x hp h
  · exact P137Bootstrap.Ac_ne p x hp ((pow_eq_zero_iff (n := 2) (by norm_num)).mp h)

theorem s_r_ne (hp : PortFacts p) (hz : value p x = 0) : x 10 ≠ 0 ∧ x 4 ≠ 0 := by
  have h := S_ne p x hp hz
  rw [S_eq] at h
  exact ⟨fun h0 => h (by rw [h0]; ring), fun h0 => h (by rw [h0]; ring)⟩

theorem Z_ne (hp : PortFacts p) (hz : value p x = 0) : (𝓕).Z ≠ 0 := by
  intro hZ
  have hS := S_ne p x hp hz
  rw [value_eq_product, hZ] at hz
  have h1 : ((𝓕).S ^ 2 * ((𝓑).delta * (𝓑).P - 4 * (𝓑).B * (𝓑).Df * (𝓑).Cy)) ^ 2 = 0 := by
    linear_combination hz
  have h2 : (𝓑).delta * (𝓑).P - 4 * (𝓑).B * (𝓑).Df * (𝓑).Cy = 0 := by
    rcases mul_eq_zero.mp ((pow_eq_zero_iff (n := 2) (by norm_num)).mp h1) with h3 | h3
    · exact absurd ((pow_eq_zero_iff (n := 2) (by norm_num)).mp h3) hS
    · exact h3
  obtain ⟨n, hn⟩ := Q_even p x hp
  obtain ⟨m, hm⟩ := P_mod p x hp
  have hδ : (𝓑).delta = 2 * n - 1 := by rw [delta_def, hn]
  apply P138Bootstrap.odd_ne_zero' (4 * n * m + n - 2 * m - 1 - 2 * (𝓑).B * (𝓑).Df * (𝓑).Cy)
  linear_combination h2 - (𝓑).P * hδ - (2 * n - 1) * hm

/-! ## Norm extraction -/

/-- **Norm extraction.** At a zero of the output there are `g`, `w` with `P = g²`,
`δ (Z − S g) = 2 S w` and `w² = B · Df · (δ · Cy)`. -/
theorem norm (hp : PortFacts p) (hz : value p x = 0) :
    ∃ g w : DiffRing V, (𝓑).P = g * g ∧
      (𝓑).delta * ((𝓕).Z - (𝓕).S * g) = 2 * (𝓕).S * w ∧
      w * w = (𝓑).B * (𝓑).Df * ((𝓑).delta * (𝓑).Cy) := by
  have hS := S_ne p x hp hz
  have hZ := Z_ne p x hp hz
  have hδ := delta_ne p x hp
  obtain ⟨I, hI⟩ : ∃ I : DiffRing V, I = (𝓑).delta * (𝓕).Z ^ 2 +
      (𝓑).delta * (𝓕).S ^ 2 * (𝓑).P - 4 * (𝓕).S ^ 2 * (𝓑).B * (𝓑).Df * (𝓑).Cy := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : DiffRing V, T = 2 * (𝓑).delta * (𝓕).Z * (𝓕).S := ⟨_, rfl⟩
  have hT0 : T ≠ 0 := by
    rw [hT]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hδ) hZ) hS
  have hz' : I ^ 2 - T ^ 2 * (𝓑).P = 0 := by
    rw [hI, hT, ← value_eq_product]; exact hz
  have hdvd : T * T ∣ I * I := ⟨(𝓑).P, by linear_combination hz'⟩
  obtain ⟨g, hg⟩ := dvd_of_sq_dvd_sq_ring hdvd
  have hP : (𝓑).P = g * g := by
    apply mul_left_cancel₀ (mul_ne_zero hT0 hT0)
    linear_combination (-1 : DiffRing V) * hz' + (I + T * g) * hg
  have hX2 : ((𝓑).delta * ((𝓕).Z - (𝓕).S * g)) * ((𝓑).delta * ((𝓕).Z - (𝓕).S * g)) =
      (2 * (𝓕).S) * (2 * (𝓕).S) * ((𝓑).B * (𝓑).Df * ((𝓑).delta * (𝓑).Cy)) := by
    rw [hI, hT] at hg
    linear_combination (𝓑).delta * hg - (𝓑).delta ^ 2 * (𝓕).S ^ 2 * hP
  obtain ⟨w, hw⟩ := dvd_of_sq_dvd_sq_ring ⟨_, hX2⟩
  have h2S : 2 * (𝓕).S ≠ 0 := mul_ne_zero (by norm_num) hS
  refine ⟨g, w, hP, hw, ?_⟩
  apply mul_left_cancel₀ (mul_ne_zero h2S h2S)
  linear_combination hX2 - ((𝓑).delta * ((𝓕).Z - (𝓕).S * g) + 2 * (𝓕).S * w) * hw

/-! ## The coprime product `B · Df · Da` -/

/-- The proof register `Da = δ · Cy`. -/
def Da : DiffRing V := ((𝓑).Q - 1) * ((𝓑).Q * (𝓑).V ^ 2 - 1)

theorem Da_eq : (𝓑).delta * (𝓑).Cy = Da p x := by
  unfold Da; rw [delta_def, Cy_eq]

/-- The auxiliary offset `b`, with `V = Df · b − c`. -/
def bOff : DiffRing V := x 8 - (𝓕).R + 4 * x 8 ^ 2 * (𝓑).B * x 7

/-- `LL` of the remainder identities. -/
def LL : DiffRing V := (𝓑).Q * bOff p x * ((𝓑).V - x 8) + (𝓕).Delta * x 8 ^ 2

theorem V_bOff : (𝓑).V = (𝓑).Df * bOff p x - x 8 := by rw [V_eq, bOff]

/-- `Cy + Dm = Df · LL`: modulo `Df`, `Cy ≡ −Dm`. -/
theorem Cy_mod_Df : (𝓑).Q * (𝓑).V ^ 2 - 1 = (𝓑).Df * LL p x - (𝓕).Dm := by
  unfold LL
  rw [Q_Df, V_bOff, Dm_eq]; ring

theorem delta_mod_Df : (𝓑).Q - 1 = (𝓕).Delta * (𝓑).Df - (𝓕).A ^ 2 := by
  rw [Q_Df, Delta_eq]; ring

/-- **`Da ≡ A² Dm (mod Df)`.** -/
theorem Da_mod_Df : Da p x = (𝓕).A ^ 2 * (𝓕).Dm +
    (𝓑).Df * ((𝓕).Delta * (𝓑).Df * LL p x - (𝓕).Delta * (𝓕).Dm - (𝓕).A ^ 2 * LL p x) := by
  unfold Da
  rw [delta_mod_Df, Cy_mod_Df]; ring

/-- `Df = 1 + A Dm · t`, `t = Δ c⁴ r`. -/
theorem Df_AD : (𝓑).Df = 1 + (𝓕).A * (𝓕).Dm * ((𝓕).Delta * x 8 ^ 4 * x 4) := by
  rw [Df_eq, B_eq]; ring

theorem bez_B_Df : ∃ α β : DiffRing V, (𝓑).B * α + (𝓑).Df * β = 1 :=
  ⟨-((𝓕).Delta * x 8 ^ 4), 1, by rw [Df_eq]; ring⟩

theorem bez_B_Da : ∃ α β : DiffRing V, (𝓑).B * α + Da p x * β = 1 :=
  ⟨(𝓕).Delta ^ 2 * x 8 ^ 4 * (1 + (𝓑).V ^ 2 - (𝓑).Q * (𝓑).V ^ 2), 1, by
    unfold Da; rw [Q_eq]; ring⟩

/-- `A² Dm · (Dm t²) = (Df − 1)² ≡ 1 (mod Df)`. -/
theorem bez_Df_Da : ∃ α β : DiffRing V, (𝓑).Df * α + Da p x * β = 1 := by
  have hDa := Da_mod_Df p x
  have hDf := Df_AD p x
  exact ⟨2 - (𝓑).Df -
      ((𝓕).Delta * (𝓑).Df * LL p x - (𝓕).Delta * (𝓕).Dm - (𝓕).A ^ 2 * LL p x) * (𝓕).Dm *
        ((𝓕).Delta * x 8 ^ 4 * x 4) ^ 2,
    (𝓕).Dm * ((𝓕).Delta * x 8 ^ 4 * x 4) ^ 2, by
    linear_combination ((𝓕).Dm * ((𝓕).Delta * x 8 ^ 4 * x 4) ^ 2) * hDa -
      ((𝓑).Df - 1 + (𝓕).A * (𝓕).Dm * ((𝓕).Delta * x 8 ^ 4 * x 4)) * hDf⟩

theorem Da_ne (hp : PortFacts p) : Da p x ≠ 0 := by
  rw [← Da_eq]
  exact mul_ne_zero (delta_ne p x hp) (Cy_ne p x hp)

/-- At a zero: `P = g²`, `δ (Z − S g) = 2 S w`, `w² = B · Df · Da`. -/
theorem prod_square (hp : PortFacts p) (hz : value p x = 0) :
    ∃ g w : DiffRing V, (𝓑).P = g * g ∧
      ((𝓑).Q - 1) * ((𝓕).Z - (𝓕).S * g) = 2 * (𝓕).S * w ∧
      w * w = (𝓑).B * (𝓑).Df * Da p x := by
  obtain ⟨g, w, hP, hlin, hw⟩ := norm p x hp hz
  rw [Da_eq] at hw
  rw [delta_def] at hlin
  exact ⟨g, w, hP, hlin, hw⟩

theorem Df_pos_of_abs (hp : PortFacts p) {f : V} (hf : |(𝓑).Df| = ι f * ι f) :
    0 < (𝓑).Df := by
  rcases lt_or_gt_of_ne (Df_ne p x hp) with hneg | hpos
  · exfalso
    obtain ⟨m, hm⟩ := Df_mod p x hp
    rw [abs_of_neg hneg] at hf
    apply P138Squares.neg_sq_ne (ι f) m
    rw [← hf, neg_neg, hm]
  · exact hpos

theorem B_ne (hp : PortFacts p) (hz : value p x = 0) : (𝓑).B ≠ 0 := by
  rw [B_eq]
  exact mul_ne_zero (mul_ne_zero (P137Bootstrap.A_ne p x hp) (s_r_ne p x hp hz).2)
    (lt_of_lt_of_le zero_lt_one (P137Bootstrap.Dm_ge p x hp)).ne'

theorem one_le_c4 (hc : x 8 ≠ 0) : 1 ≤ x 8 ^ 4 := by
  have hc2 := P137Roots.one_le_sq hc
  have := mul_le_mul hc2 hc2 (by norm_num) (by linarith)
  have h4 : x 8 ^ 4 = x 8 ^ 2 * x 8 ^ 2 := by ring
  rw [h4]; linarith

/-- **The three square roots.** At a zero, `B = b0²`, `Df = f²`, `Da = e²` with positive
`b0, f, e`. -/
theorem roots (hp : PortFacts p) (hz : value p x = 0) :
    ∃ b0 f e : V, 0 < b0 ∧ 0 < f ∧ 0 < e ∧ (𝓑).B = ι b0 * ι b0 ∧ (𝓑).Df = ι f * ι f ∧
      Da p x = ι e * ι e := by
  obtain ⟨_, w, _, _, hw⟩ := prod_square p x hp hz
  obtain ⟨⟨b0, hb0⟩, ⟨f, hf⟩, ⟨e, he⟩⟩ := abs_squares_of_mul_mul_square (bez_B_Df p x)
    (bez_B_Da p x) (bez_Df_Da p x) hw.symm
  have hB0 := B_ne p x hp hz
  have hDa0 := Da_ne p x hp
  have hDf : 0 < (𝓑).Df := Df_pos_of_abs p x hp hf
  -- `B > 0`
  have hB : 0 < (𝓑).B := by
    by_cases hc : x 8 = 0
    · -- `c = 0`: `Df = Da = 1`, so `B = w²`
      have hQ : (𝓑).Q = 0 := by rw [Q_eq, hc]; ring
      have hDf1 : (𝓑).Df = 1 := by rw [Df_eq, hc]; ring
      have hDa1 : Da p x = 1 := by unfold Da; rw [hQ]; ring
      rw [hDf1, hDa1, mul_one, mul_one] at hw
      have := mul_self_nonneg w
      exact lt_of_le_of_ne (by linarith) (Ne.symm hB0)
    · by_contra hneg
      have hBn : (𝓑).B ≤ -1 := by
        rcases P138Bootstrap.int_split (𝓑).B with h | h
        · exact absurd (lt_of_le_of_ne h (Ne.symm hB0)) hneg
        · exact h
      have hc4 := one_le_c4 x hc
      have hD := P137Bootstrap.Delta_ge p x hp
      have hDU : 3 * 1 ≤ (𝓕).Delta * x 8 ^ 4 :=
        mul_le_mul hD hc4 (by norm_num) (by linarith)
      have h3 : (𝓕).Delta * x 8 ^ 4 * (𝓑).B ≤ (𝓕).Delta * x 8 ^ 4 * (-1) :=
        mul_le_mul_of_nonneg_left hBn (by linarith)
      have : (𝓑).Df ≤ 1 - 3 := by rw [Df_eq]; linarith
      linarith
  have hDa : 0 < Da p x := by
    have h1 : 0 < (𝓑).B * (𝓑).Df := mul_pos hB hDf
    have h2 := mul_self_nonneg w
    rw [hw] at h2
    have h3 : 0 ≤ Da p x := by
      by_contra hn
      have : (𝓑).B * (𝓑).Df * Da p x < 0 := mul_neg_of_pos_of_neg h1 (lt_of_not_ge hn)
      linarith
    exact lt_of_le_of_ne h3 (Ne.symm hDa0)
  have pos_of {Z : DiffRing V} {a : V} (hZ : 0 < Z) (ha : |Z| = ι a * ι a) : 0 < a := by
    rw [abs_of_pos hZ] at ha
    rcases eq_zero_or_pos a with h0 | h0
    · rw [h0, map_zero, mul_zero] at ha; exact absurd ha hZ.ne'
    · exact h0
  refine ⟨b0, f, e, pos_of hB hb0, pos_of hDf hf, pos_of hDa he, ?_, ?_, ?_⟩
  · rw [← hb0, abs_of_pos hB]
  · rw [← hf, abs_of_pos hDf]
  · rw [← he, abs_of_pos hDa]

theorem B_pos (hp : PortFacts p) (hz : value p x = 0) : 0 < (𝓑).B := by
  obtain ⟨b0, _, _, hb0, _, _, hB, _, _⟩ := roots p x hp hz
  rw [hB]; exact mul_pos (P138Adjacent.ι_pos hb0) (P138Adjacent.ι_pos hb0)

/-! ## The guard -/

theorem P_pos (hp : PortFacts p) (hz : value p x = 0) : 0 < (𝓑).P := by
  obtain ⟨g, _, hP, _, _⟩ := prod_square p x hp hz
  have := mul_self_nonneg g
  rw [← hP] at this
  exact lt_of_le_of_ne this (Ne.symm (P_ne p x hp))

/-- **`Dt` is a square**: it is coprime to its cofactor in the square `P`. -/
theorem Dt_square (hp : PortFacts p) (hz : value p x = 0) :
    ∃ τ : V, (𝓕).Dt = ι τ * ι τ := by
  obtain ⟨g, _, hP, _, _⟩ := prod_square p x hp hz
  have hcop : ∃ α β, (𝓕).Dt * α + (1 + (𝓑).Dguard * (𝓕).Dt * x 10 ^ 2) * β = 1 :=
    ⟨-((𝓑).Dguard * x 10 ^ 2), 1, by ring⟩
  obtain ⟨⟨τ, hτ⟩, _⟩ := abs_squares_of_mul_square hcop ((P_eq p x).symm.trans hP)
  obtain ⟨hDt1, _⟩ := P137Bootstrap.Dt_facts p x hp
  rw [abs_of_pos (by linarith)] at hτ
  exact ⟨τ, hτ⟩

/-- **`Budget > 0`**: a positive `P` with `s ≠ 0` excludes `Budget − 4 ≤ −4`. -/
theorem budget_pos (hp : PortFacts p) (hz : value p x = 0) : 0 < (𝓕).Budget := by
  have hP := P_pos p x hp hz
  obtain ⟨hs, _⟩ := s_r_ne p x hp hz
  obtain ⟨hDt, _⟩ := P137Bootstrap.Dt_facts p x hp
  have hs2 := P137Roots.one_le_sq hs
  have hDg : 0 < 1 + (𝓑).Dguard * (𝓕).Dt * x 10 ^ 2 := by
    rw [P_eq] at hP
    exact pos_of_mul_pos_right hP (by linarith)
  by_contra hlt
  have hD : (𝓑).Dguard ≤ -4 := by rw [Dguard_def]; linarith [not_lt.mp hlt]
  have h1 : (𝓑).Dguard * (𝓕).Dt ≤ (𝓑).Dguard * 1 :=
    mul_le_mul_of_nonpos_left hDt (by linarith)
  have h2 : (𝓑).Dguard * (𝓕).Dt * x 10 ^ 2 ≤ (𝓑).Dguard * (𝓕).Dt * 1 :=
    mul_le_mul_of_nonpos_left hs2 (by linarith)
  linarith

/-! ## The descent and `S ∣ Ac` -/

theorem Q_gt (hp : PortFacts p) (hz : value p x = 0) (hc : x 8 ≠ 0) : 1 < (𝓑).Q := by
  have hB1 : 1 ≤ (𝓑).B := P138Bootstrap.one_le_of_pos' (B_pos p x hp hz)
  have hD := P137Bootstrap.Delta_ge p x hp
  have hc4 := one_le_c4 x hc
  have hD2 : 3 * 3 ≤ (𝓕).Delta ^ 2 := by
    rw [sq]; exact mul_le_mul hD hD (by norm_num) (by linarith)
  have h1 : 3 * 3 * 1 ≤ (𝓕).Delta ^ 2 * x 8 ^ 4 :=
    mul_le_mul hD2 hc4 (by norm_num) (by positivity)
  have h2 : 3 * 3 * 1 * 1 ≤ (𝓕).Delta ^ 2 * x 8 ^ 4 * (𝓑).B :=
    mul_le_mul h1 hB1 (by norm_num) (by positivity)
  rw [Q_eq]
  linarith

/-- **The auxiliary ordinate is integral, and `S ∣ Ac`** (case `c ≠ 0`). -/
theorem descent (hp : PortFacts p) (hz : value p x = 0) (hc : x 8 ≠ 0) :
    ∃ y : V, 0 < y ∧ (𝓑).Q * (𝓑).V ^ 2 - ((𝓑).Q - 1) * (ι y) ^ 2 = 1 ∧
      (𝓕).S ∣ (𝓕).Ac := by
  obtain ⟨g, w, _, hlin, hw⟩ := prod_square p x hp hz
  obtain ⟨b0, f, e, _, _, he0, hB, hDf, hDa⟩ := roots p x hp hz
  have hd := delta_ne p x hp
  rw [delta_def] at hd
  have hQ := Q_gt p x hp hz hc
  have hDa' : ((𝓑).Q - 1) * ((𝓑).Q * (𝓑).V ^ 2 - 1) = ι e * ι e := hDa
  obtain ⟨y, hy0, hey, haux⟩ := ZRowsStrongFold.adjacent_descent (Vr := (𝓑).V) hQ he0 hDa'
  have hey' : (ι e : DiffRing V) = ((𝓑).Q - 1) * ι y := hey
  refine ⟨y, hy0, haux, ?_⟩
  have h1 : w * w = (ι b0 * ι f * ((𝓑).Q - 1) * ι y) * (ι b0 * ι f * ((𝓑).Q - 1) * ι y) := by
    rw [hw, hB, hDf, hDa, hey']; ring
  have hZ := Z_eq p x
  rcases mul_self_eq_mul_self_iff.mp h1 with h | h
  · have h2 : (𝓕).Z - (𝓕).S * g = (𝓕).S * (2 * ι b0 * ι f * ι y) :=
      mul_left_cancel₀ hd (by rw [hlin, h]; ring)
    exact ⟨x 9 - g - 2 * ι b0 * ι f * ι y, by linear_combination hZ - h2⟩
  · have h2 : (𝓕).Z - (𝓕).S * g = -((𝓕).S * (2 * ι b0 * ι f * ι y)) :=
      mul_left_cancel₀ hd (by rw [hlin, h]; ring)
    exact ⟨x 9 - g + 2 * ι b0 * ι f * ι y, by linear_combination hZ - h2⟩

/-- **`S ∣ Ac` at every zero.** -/
theorem S_dvd_Ac (hp : PortFacts p) (hz : value p x = 0) : (𝓕).S ∣ (𝓕).Ac := by
  by_cases hc : x 8 = 0
  · obtain ⟨g, w, _, hlin, _⟩ := prod_square p x hp hz
    have hQ : (𝓑).Q = 0 := by rw [Q_eq, hc]; ring
    rw [hQ] at hlin
    have hZ := Z_eq p x
    exact ⟨x 9 - g + 2 * w, by linear_combination hZ + hlin⟩
  · obtain ⟨_, _, _, h⟩ := descent p x hp hz hc
    exact h

end Regs

#print axioms budget_mod
#print axioms P_mod
#print axioms Df_mod
#print axioms S_ne
#print axioms Z_ne
#print axioms norm
#print axioms Da_mod_Df
#print axioms bez_Df_Da
#print axioms roots
#print axioms Dt_square
#print axioms budget_pos
#print axioms Q_gt
#print axioms descent
#print axioms S_dvd_Ac

end DiophantineConsistency.P135WRoots
