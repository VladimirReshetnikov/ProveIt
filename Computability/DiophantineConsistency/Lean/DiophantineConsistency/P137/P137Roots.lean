import DiophantineConsistency.P137.P137Value
import DiophantineConsistency.P137.P137Bootstrap
import DiophantineConsistency.ZRows.StrongFold
import DiophantineConsistency.P138.P138Squares

/-! # The three square roots of package 137's 648/115 equation

At a zero of the output `P137Value.value p x` in the ring of differences of a model of `𝗜𝚺₁`,
with the port facts of package 138 (`P138Ports.PortFacts`). The registers are those of the
weak front `P137Front.front p x` and of the back end `P137Value.back p x`; no index slot occurs.

* **Unconditional nonvanishing.** `Δ ≥ 3` (`P137Bootstrap.Delta_ge`: the weak front has no
  size bound on `a`, only `A` even and `A ≢ 0 (mod 3)`), and each of `δ + 1`, `1 − Df`, `Cy + 1`
  is a multiple of `Δ`, so `δ, Df, Cy ≠ 0` (`mul_ne_one`). `P = Dt (1 + D4 Dt s²)` with
  `Dt ≥ 1` and `D4 = 4 (3 Budget − 4)`, so `P ≠ 0` and `BP = P Dm ≠ 0`.
* **`S ≠ 0`.** Where `S = 0` the output is `δ Ac²` (`P137Value.value_S_zero`), and `Ac ≠ 0`.
* **The coprime product** (as in `P138Squares`). `BP`, `Df`, `Da = δ Cy` are pairwise coprime
  by ring Bezout identities; at a zero `δ Z = S w` with `w² = BP · Df · Da` (`prod_square`),
  so the three absolute values are squares. `Df ≡ 1 (mod 4)` is not a negative square; if
  `c ≠ 0` then `U ≠ 0` and `BP < 0` would give `Df ≤ 1 − 3 < 0`; if `c = 0` then
  `Df = Da = 1`. Hence `BP = p0²`, `Df = f²`, `Da = e²` with `p0, f, e > 0` (`roots`), and
  `P > 0` (`P_pos`).
* **The budget** (`budget_pos`). `P > 0`, `Dt ≥ 1` and `s ≠ 0` give `1 + D4 Dt s² > 0`, which
  fails if `3 Budget − 4 ≤ −1`; so `Budget > 0`.
* **The descent** (`descent`, for `c ≠ 0`). `Q = Δ² U² BP ≥ 9`, so `δ Cy = e²` gives the
  integral auxiliary ordinate `y` with `e = δ y` and `Q V² − (Q − 1) y² = 1`
  (`ZRowsStrongFold.adjacent_descent`). Then `w = ± p0 f δ y` and `Z = ± S p0 f y`.
* **`S ∣ Ac`** (`S_dvd_Ac`), since `Z = S n − Ac`: from the descent if `c ≠ 0`, and from
  `δ = −1` if `c = 0`. This is the divisibility from which `P137Bootstrap.recover` rebuilds
  the strong front. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P137Roots
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P137Front P137Value P138Ports

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Two facts about the ordered ring -/

/-- A multiple of `D ≥ 2` is not `1`. -/
theorem mul_ne_one {D t : DiffRing V} (hD : 2 ≤ D) : D * t ≠ 1 := by
  intro h
  rcases P138Bootstrap.int_split t with h0 | h0
  · rcases eq_or_lt_of_le h0 with h1 | h1
    · rw [← h1, mul_zero] at h; linarith
    · have h2 := P138Bootstrap.one_le_of_pos' h1
      have := mul_le_mul hD h2 (by norm_num) (by linarith)
      linarith
  · have := mul_le_mul_of_nonneg_left h0 (show (0 : DiffRing V) ≤ D by linarith)
    linarith

/-- A nonzero integer has square at least `1`. -/
theorem one_le_sq {a : DiffRing V} (h : a ≠ 0) : 1 ≤ a ^ 2 := by
  have h1 := P138Bootstrap.one_le_abs h
  have := mul_le_mul h1 h1 (by norm_num) (abs_nonneg a)
  rw [← sq_abs, sq]; linarith

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V)
local notation "𝓕" => front p x
local notation "𝓑" => back p x

/-! ## Unconditional nonvanishing -/

theorem Delta_two (hp : PortFacts p) : 2 ≤ (𝓕).Delta := by
  linarith [P137Bootstrap.Delta_ge p x hp]

theorem delta_ne (hp : PortFacts p) : (𝓑).delta ≠ 0 := by
  intro h
  apply mul_ne_one (Delta_two p x hp) (t := (𝓑).strong)
  rw [delta_def, Q_def] at h
  linear_combination h

theorem Df_ne (hp : PortFacts p) : (𝓑).Df ≠ 0 := by
  intro h
  apply mul_ne_one (Delta_two p x hp) (t := -((𝓑).U ^ 2 * (𝓑).BP))
  rw [Df_eq] at h
  linear_combination -h

theorem Cy_ne (hp : PortFacts p) : (𝓑).Cy ≠ 0 := by
  intro h
  apply mul_ne_one (Delta_two p x hp) (t := (𝓑).strong * (𝓑).V ^ 2)
  rw [Cy_def, Q_def] at h
  linear_combination h

theorem P_ne (hp : PortFacts p) : (𝓑).P ≠ 0 := by
  obtain ⟨hDt, _⟩ := P137Bootstrap.Dt_facts p x hp
  rw [P_eq, D4_eq]
  refine mul_ne_zero (lt_of_lt_of_le zero_lt_one hDt).ne' ?_
  have := P138Bootstrap.four_add_one_ne ((3 * (𝓕).Budget - 4) * (𝓕).Dt * x 10 ^ 2)
  intro h; apply this; linear_combination h

theorem BP_ne (hp : PortFacts p) : (𝓑).BP ≠ 0 := by
  rw [BP_def]
  exact mul_ne_zero (P_ne p x hp)
    (lt_of_lt_of_le zero_lt_one (P137Bootstrap.Dm_ge p x hp)).ne'

/-- `Df ≡ 1 (mod 4)`, because `A` is even. -/
theorem Df_mod (hp : PortFacts p) : ∃ m : DiffRing V, (𝓑).Df = 4 * m + 1 := by
  obtain ⟨m, hm⟩ := P137Bootstrap.A_even p x hp
  have hD := Df_eq p x
  have hU := U_eq p x
  exact ⟨(𝓕).Delta * (m * (x 4 * x 8 ^ 2)) ^ 2 * (𝓑).BP, by
    rw [hD, hU, hm]; ring⟩

/-! ## At a zero: `S ≠ 0` -/

theorem S_ne (hp : PortFacts p) (hz : value p x = 0) : (𝓕).S ≠ 0 := by
  intro hS
  rw [value_S_zero p x hS] at hz
  have hd := delta_ne p x hp
  rw [delta_def] at hd
  rcases mul_eq_zero.mp hz with h | h
  · exact hd h
  · exact P137Bootstrap.Ac_ne p x hp ((pow_eq_zero_iff (n := 2) (by norm_num)).mp h)

theorem s_r_ne (hp : PortFacts p) (hz : value p x = 0) : x 10 ≠ 0 ∧ x 4 ≠ 0 := by
  have h := S_ne p x hp hz
  rw [S_eq] at h
  exact ⟨fun h0 => h (by rw [h0]; ring), fun h0 => h (by rw [h0]; ring)⟩

/-! ## The coprime product `BP · Df · Da` -/

/-- The proof register `Da = δ · Cy`. -/
def Da : DiffRing V := ((𝓑).Q - 1) * ((𝓑).Q * (𝓑).V ^ 2 - 1)

/-- The auxiliary offset `b`, with `V = Df · b − c`. -/
def bOff : DiffRing V := x 8 - (𝓕).R + 4 * (𝓑).U * (𝓑).BP * x 7

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

/-- `Df = 1 + A² Dm · w'`, `w' = Δ (r c²)² P`. -/
theorem Df_AD :
    (𝓑).Df = 1 + (𝓕).A ^ 2 * (𝓕).Dm * ((𝓕).Delta * (x 4 * x 8 ^ 2) ^ 2 * (𝓑).P) := by
  rw [Df_eq, U_eq, BP_def]; ring

theorem bez_BP_Df : ∃ α β : DiffRing V, (𝓑).BP * α + (𝓑).Df * β = 1 :=
  ⟨-((𝓕).Delta * (𝓑).U ^ 2), 1, by rw [Df_eq]; ring⟩

theorem bez_BP_Da : ∃ α β : DiffRing V, (𝓑).BP * α + Da p x * β = 1 :=
  ⟨(𝓕).Delta ^ 2 * (𝓑).U ^ 2 * (1 + (𝓑).V ^ 2 - (𝓑).Q * (𝓑).V ^ 2), 1, by
    unfold Da; rw [Q_eq]; ring⟩

theorem bez_Df_Da : ∃ α β : DiffRing V, (𝓑).Df * α + Da p x * β = 1 := by
  set M := (𝓕).Delta * (𝓑).Df * LL p x - (𝓕).Delta * (𝓕).Dm - (𝓕).A ^ 2 * LL p x
  set w := (𝓕).Delta * (x 4 * x 8 ^ 2) ^ 2 * (𝓑).P
  have hDa := Da_mod_Df p x
  have hDf := Df_AD p x
  exact ⟨1 + M * w, -w, by linear_combination (-w) * hDa + hDf⟩

theorem Da_ne (hp : PortFacts p) : Da p x ≠ 0 := by
  have h1 := delta_ne p x hp
  have h2 := Cy_ne p x hp
  rw [delta_def] at h1
  rw [Cy_eq] at h2
  exact mul_ne_zero h1 h2

/-- At a zero, `δ · Z = S · w` with `w² = BP · Df · Da`. -/
theorem prod_square (hp : PortFacts p) (hz : value p x = 0) :
    ∃ w : DiffRing V, ((𝓑).Q - 1) * (𝓕).Z = (𝓕).S * w ∧ w * w = (𝓑).BP * (𝓑).Df * Da p x := by
  have hS := S_ne p x hp hz
  have h5 : (((𝓑).Q - 1) * (𝓕).Z) * (((𝓑).Q - 1) * (𝓕).Z) =
      ((𝓕).S * (𝓕).S) * ((𝓑).BP * (𝓑).Df * Da p x) := by
    rw [value_eq_product] at hz
    unfold Da
    linear_combination ((𝓑).Q - 1) * hz
  obtain ⟨w, hw⟩ := dvd_of_sq_dvd_sq_ring (A := ((𝓑).Q - 1) * (𝓕).Z) (B := (𝓕).S) ⟨_, h5⟩
  refine ⟨w, hw, ?_⟩
  rw [hw] at h5
  have hSS : (𝓕).S * (𝓕).S ≠ 0 := mul_ne_zero hS hS
  apply mul_left_cancel₀ hSS
  linear_combination h5

theorem Df_pos_of_abs (hp : PortFacts p) {f : V} (hf : |(𝓑).Df| = ι f * ι f) :
    0 < (𝓑).Df := by
  rcases lt_or_gt_of_ne (Df_ne p x hp) with hneg | hpos
  · exfalso
    obtain ⟨m, hm⟩ := Df_mod p x hp
    rw [abs_of_neg hneg] at hf
    apply P138Squares.neg_sq_ne (ι f) m
    rw [← hf, neg_neg, hm]
  · exact hpos

theorem U_ne (hp : PortFacts p) (hz : value p x = 0) (hc : x 8 ≠ 0) : (𝓑).U ≠ 0 := by
  rw [U_eq]
  exact mul_ne_zero (P137Bootstrap.A_ne p x hp)
    (mul_ne_zero (s_r_ne p x hp hz).2 (pow_ne_zero 2 hc))

/-- **The three square roots.** At a zero, `BP = p0²`, `Df = f²`, `Da = e²` with positive
`p0, f, e`. -/
theorem roots (hp : PortFacts p) (hz : value p x = 0) :
    ∃ p0 f e : V, 0 < p0 ∧ 0 < f ∧ 0 < e ∧ (𝓑).BP = ι p0 * ι p0 ∧ (𝓑).Df = ι f * ι f ∧
      Da p x = ι e * ι e := by
  obtain ⟨w, _, hw⟩ := prod_square p x hp hz
  obtain ⟨⟨p0, hp0⟩, ⟨f, hf⟩, ⟨e, he⟩⟩ := abs_squares_of_mul_mul_square (bez_BP_Df p x)
    (bez_BP_Da p x) (bez_Df_Da p x) hw.symm
  have hBP0 := BP_ne p x hp
  have hDa0 := Da_ne p x hp
  have hDf : 0 < (𝓑).Df := Df_pos_of_abs p x hp hf
  -- `BP > 0`
  have hBP : 0 < (𝓑).BP := by
    by_cases hc : x 8 = 0
    · -- `c = 0`: `Df = Da = 1`, so `BP = w²`
      have hU : (𝓑).U = 0 := by rw [U_eq, hc]; ring
      have hQ : (𝓑).Q = 0 := by rw [Q_eq, hU]; ring
      have hDf1 : (𝓑).Df = 1 := by rw [Df_eq, hU]; ring
      have hDa1 : Da p x = 1 := by unfold Da; rw [hQ]; ring
      rw [hDf1, hDa1, mul_one, mul_one] at hw
      have := mul_self_nonneg w
      exact lt_of_le_of_ne (by linarith) (Ne.symm hBP0)
    · by_contra hneg
      have hBPn : (𝓑).BP ≤ -1 := by
        rcases P138Bootstrap.int_split (𝓑).BP with h | h
        · exact absurd (lt_of_le_of_ne h (Ne.symm hBP0)) hneg
        · exact h
      have hU1 := one_le_sq (U_ne p x hp hz hc)
      have hD := P137Bootstrap.Delta_ge p x hp
      have hDU : 3 * 1 ≤ (𝓕).Delta * (𝓑).U ^ 2 :=
        mul_le_mul hD hU1 (by norm_num) (by linarith)
      have h3 : (𝓕).Delta * (𝓑).U ^ 2 * (𝓑).BP ≤ (𝓕).Delta * (𝓑).U ^ 2 * (-1) :=
        mul_le_mul_of_nonneg_left hBPn (by linarith)
      have : (𝓑).Df ≤ 1 - 3 := by rw [Df_eq]; linarith
      linarith
  have hDa : 0 < Da p x := by
    have h1 : 0 < (𝓑).BP * (𝓑).Df := mul_pos hBP hDf
    have h2 := mul_self_nonneg w
    rw [hw] at h2
    have h3 : 0 ≤ Da p x := by
      by_contra hn
      have : (𝓑).BP * (𝓑).Df * Da p x < 0 := mul_neg_of_pos_of_neg h1 (lt_of_not_ge hn)
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

theorem BP_pos (hp : PortFacts p) (hz : value p x = 0) : 0 < (𝓑).BP := by
  obtain ⟨p0, _, _, hp0, _, _, hBP, _, _⟩ := roots p x hp hz
  rw [hBP]; exact mul_pos (P138Adjacent.ι_pos hp0) (P138Adjacent.ι_pos hp0)

theorem P_pos (hp : PortFacts p) (hz : value p x = 0) : 0 < (𝓑).P := by
  have hBPpos := BP_pos p x hp hz
  rw [BP_def, mul_comm] at hBPpos
  exact pos_of_mul_pos_right hBPpos (by linarith [P137Bootstrap.Dm_ge p x hp])

/-! ## The budget -/

/-- **`Budget > 0`**: a positive `P` with `s ≠ 0` excludes `3 Budget − 4 ≤ −1`. -/
theorem budget_pos (hp : PortFacts p) (hz : value p x = 0) : 0 < (𝓕).Budget := by
  have hP := P_pos p x hp hz
  obtain ⟨hs, _⟩ := s_r_ne p x hp hz
  obtain ⟨hDt, _⟩ := P137Bootstrap.Dt_facts p x hp
  have hs2 := one_le_sq hs
  have hDg : 0 < 1 + (𝓑).D4 * (𝓕).Dt * x 10 ^ 2 := by
    rw [P_eq] at hP
    exact pos_of_mul_pos_right hP (by linarith)
  by_contra hlt
  have hB : 3 * (𝓕).Budget - 4 ≤ -1 := by
    rcases P138Bootstrap.int_split (3 * (𝓕).Budget - 4) with h | h
    · exfalso; apply hlt; linarith
    · exact h
  have hD : (𝓑).D4 ≤ -4 := by rw [D4_eq]; linarith
  have h1 : (𝓑).D4 * (𝓕).Dt ≤ (𝓑).D4 * 1 :=
    mul_le_mul_of_nonpos_left hDt (by linarith)
  have h2 : (𝓑).D4 * (𝓕).Dt * x 10 ^ 2 ≤ (𝓑).D4 * (𝓕).Dt * 1 :=
    mul_le_mul_of_nonpos_left hs2 (by linarith)
  linarith

/-! ## The descent and `S ∣ Ac` -/

theorem Q_gt (hp : PortFacts p) (hz : value p x = 0) (hc : x 8 ≠ 0) : 1 < (𝓑).Q := by
  have hBP1 : 1 ≤ (𝓑).BP := P138Bootstrap.one_le_of_pos' (BP_pos p x hp hz)
  have hD := P137Bootstrap.Delta_ge p x hp
  have hU1 := one_le_sq (U_ne p x hp hz hc)
  have hD2 : 3 * 3 ≤ (𝓕).Delta ^ 2 := by
    rw [sq]; exact mul_le_mul hD hD (by norm_num) (by linarith)
  have h1 : 3 * 3 * 1 ≤ (𝓕).Delta ^ 2 * (𝓑).U ^ 2 :=
    mul_le_mul hD2 hU1 (by norm_num) (by positivity)
  have h2 : 3 * 3 * 1 * 1 ≤ (𝓕).Delta ^ 2 * (𝓑).U ^ 2 * (𝓑).BP :=
    mul_le_mul h1 hBP1 (by norm_num) (by positivity)
  rw [Q_eq]
  linarith

/-- **The auxiliary ordinate is integral, and `S ∣ Ac`** (case `c ≠ 0`). -/
theorem descent (hp : PortFacts p) (hz : value p x = 0) (hc : x 8 ≠ 0) :
    ∃ y : V, 0 < y ∧ (𝓑).Q * (𝓑).V ^ 2 - ((𝓑).Q - 1) * (ι y) ^ 2 = 1 ∧
      (𝓕).S ∣ (𝓕).Ac := by
  obtain ⟨w, hlin, hw⟩ := prod_square p x hp hz
  obtain ⟨p0, f, e, _, _, he0, hBP, hDf, hDa⟩ := roots p x hp hz
  have hd := delta_ne p x hp
  rw [delta_def] at hd
  have hQ := Q_gt p x hp hz hc
  have hDa' : ((𝓑).Q - 1) * ((𝓑).Q * (𝓑).V ^ 2 - 1) = ι e * ι e := hDa
  obtain ⟨y, hy0, hey, haux⟩ := ZRowsStrongFold.adjacent_descent (Vr := (𝓑).V) hQ he0 hDa'
  have hey' : (ι e : DiffRing V) = ((𝓑).Q - 1) * ι y := hey
  refine ⟨y, hy0, haux, ?_⟩
  have h1 : w * w = (ι p0 * ι f * ((𝓑).Q - 1) * ι y) * (ι p0 * ι f * ((𝓑).Q - 1) * ι y) := by
    rw [hw, hBP, hDf, hDa, hey']; ring
  have hZ := Z_eq p x
  rcases mul_self_eq_mul_self_iff.mp h1 with h | h
  · have h2 : (𝓕).Z = (𝓕).S * (ι p0 * ι f * ι y) :=
      mul_left_cancel₀ hd (by rw [hlin, h]; ring)
    exact ⟨x 9 - ι p0 * ι f * ι y, by linear_combination hZ - h2⟩
  · have h2 : (𝓕).Z = -((𝓕).S * (ι p0 * ι f * ι y)) :=
      mul_left_cancel₀ hd (by rw [hlin, h]; ring)
    exact ⟨x 9 + ι p0 * ι f * ι y, by linear_combination hZ - h2⟩

/-- **`S ∣ Ac` at every zero.** -/
theorem S_dvd_Ac (hp : PortFacts p) (hz : value p x = 0) : (𝓕).S ∣ (𝓕).Ac := by
  by_cases hc : x 8 = 0
  · obtain ⟨w, hlin, _⟩ := prod_square p x hp hz
    have hU : (𝓑).U = 0 := by rw [U_eq, hc]; ring
    have hQ : (𝓑).Q = 0 := by rw [Q_eq, hU]; ring
    rw [hQ] at hlin
    have hZ := Z_eq p x
    exact ⟨x 9 + w, by linear_combination hZ + hlin⟩
  · obtain ⟨_, _, _, h⟩ := descent p x hp hz hc
    exact h

end Regs

#print axioms mul_ne_one
#print axioms S_ne
#print axioms Da_mod_Df
#print axioms bez_Df_Da
#print axioms prod_square
#print axioms roots
#print axioms P_pos
#print axioms budget_pos
#print axioms Q_gt
#print axioms descent
#print axioms S_dvd_Ac

end DiophantineConsistency.P137Roots
