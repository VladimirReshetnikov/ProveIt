import DiophantineConsistency.P131.P131Value
import DiophantineConsistency.ZRows.StrongFold

/-! # The two roots of package 131's 810/112 equation

`TWO_ROOT_PROOF.md` §2–§5, at a zero of the output `P131Value.valueK p x κ` in the ring of
differences of a model of `𝗜𝚺₁`, with the port facts of package 138 (`P138Ports.PortFacts`).
The `k` slot `κ` is arbitrary here: nothing in this module reads the index.

* **Unconditional nonvanishing** (§2). `Δ ≥ 8` and each of `δ + 1 = Δ·strong`,
  `1 − Df = Δ·(−U²P)`, `Cy + 1 = Δ·(strong·V²)` is a multiple of `Δ`, so `δ, Df, Cy ≠ 0`
  (`mul_ne_one`).
* **`S ≠ 0`** (§2). Where `S = 0` the output is `δ² Ac⁴` (`P131Value.value_S_zero`), and
  `Ac ≠ 0` (`P138NoRoot.Ac_ne`).
* **`Z ≠ 0`** (§3). Where `Z = 0` the output is `S⁴ (δ P Df − Cy)²`, so `Cy = δ P Df`; as
  `Cy = Δ²U²P V² − 1`, `P` divides `1`; `P ≡ 1 (mod 4)` gives `P = 1`, then `Dt = 1` and
  `D · s² = 0`, so `Budget = 4`, against `Budget ≡ 0, 12 (mod 16)`.
* **The two roots** (§4). The output is `𝓘² − 𝓣² · (P Df)` and also `𝓘'² − 𝓣'² · (δ Cy)`
  (`P131Value.value_norm`, `value_norm'`) with `𝓣, 𝓣' ≠ 0`, so `P · Df` and `δ · Cy` are squares
  (`guard_root`, `aux_root`; `b² ∣ a² ⇒ b ∣ a` is `ZRowsCoprimeSquares.dvd_of_sq_dvd_sq_ring`).
  `P` and `Df = 1 + Δ U² P` are coprime, so each is a square up to sign; `P ≡ 1 (mod 4)` makes
  `P` positive, hence `Df` positive (`squares`).
* **The budget** (`budget_ge`): `P > 0` and `s ≠ 0` give `Budget ≥ 12`, as in package 138.
  Hence `c ≠ 0`, `U ≠ 0` and `Q = Δ²U²P > 1` (`Q_gt`).
* **The descent** (`descent`, §5). `δ Cy = e²` with `Q > 1` gives the integral auxiliary
  ordinate `y`: `e = δ y`, `Q V² − (Q − 1) y² = 1` (`ZRowsStrongFold.adjacent_descent`). The
  first root reads `δ (Z − S g₀)² = S² Cy`, so `(δ (Z − S g₀))² = (δ S y)²` and
  `Z = S (g₀ ± y)`: `S ∣ Z`, and `S ∣ Ac` because `Z = S (n + V) − Ac`.

In the cubic 810 form the case `c = 0` of the source's §5 does not arise at this point: the
budget already excludes it. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P131Roots
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P138Value P138Ports P138Bootstrap P138Adjacent
open P131Value (backK)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Two facts about the ordered ring -/

/-- A multiple of `D ≥ 8` is not `1`. -/
theorem mul_ne_one {D t : DiffRing V} (hD : 8 ≤ D) : D * t ≠ 1 := by
  intro h
  rcases int_split t with h0 | h0
  · rcases eq_or_lt_of_le h0 with h1 | h1
    · rw [← h1, mul_zero] at h; linarith
    · have h2 := one_le_of_pos' h1
      have := mul_le_mul hD h2 (by norm_num) (by linarith)
      linarith
  · have := mul_le_mul_of_nonneg_left h0 (show (0 : DiffRing V) ≤ D by linarith)
    linarith

/-- A divisor of `1` is `1` or `−1`. -/
theorem unit_of_mul {a b : DiffRing V} (h : a * b = 1) : a = 1 ∨ a = -1 := by
  have ha : a ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; linarith
  have hb : b ≠ 0 := fun h0 => by rw [h0, mul_zero] at h; linarith
  have h2 := one_le_abs hb
  have h3 : |a| * |b| = 1 := by rw [← abs_mul, h, abs_one]
  have h4 : |a| = 1 := by
    have h5 : |a| * 1 ≤ |a| * |b| := mul_le_mul_of_nonneg_left h2 (abs_nonneg a)
    have h6 := one_le_abs ha
    linarith
  rcases eq_or_eq_neg_abs a with h5 | h5
  · exact Or.inl (h5.trans h4)
  · exact Or.inr (h5.trans (by rw [h4]))

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V) (κ : DiffRing V)
local notation "𝓡" => regsK p x κ
local notation "𝓑" => backK p x κ

/-! ## Unconditional nonvanishing -/

theorem delta_ne (hp : PortFacts p) : (𝓑).delta ≠ 0 := by
  intro h
  apply mul_ne_one (Delta_gt p x κ hp) (t := (𝓑).strong)
  rw [P131Value.delta_def, P131Value.Q_def] at h
  linear_combination h

theorem Df_ne (hp : PortFacts p) : (𝓑).Df ≠ 0 := by
  intro h
  apply mul_ne_one (Delta_gt p x κ hp) (t := -((𝓑).U ^ 2 * (𝓡).P))
  rw [P131Value.Df_eq] at h
  linear_combination -h

theorem Cy_ne (hp : PortFacts p) : (𝓑).Cy ≠ 0 := by
  intro h
  apply mul_ne_one (Delta_gt p x κ hp) (t := (𝓑).strong * (𝓑).V ^ 2)
  rw [P131Value.Cy_def, P131Value.Q_def] at h
  linear_combination h

/-! ## At a zero: `S ≠ 0` and `Z ≠ 0` -/

theorem S_ne (hp : PortFacts p) (hz : P131Value.valueK p x κ = 0) : (𝓡).S ≠ 0 := by
  intro hS
  rw [P131Value.value_S_zero p x κ hS] at hz
  have h1 : (𝓑).delta * (𝓡).Ac ^ 2 = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp hz
  rcases mul_eq_zero.mp h1 with h | h
  · exact delta_ne p x κ hp h
  · exact P138NoRoot.Ac_ne p x κ ((pow_eq_zero_iff (n := 2) (by norm_num)).mp h)

theorem s_r_ne (hp : PortFacts p) (hz : P131Value.valueK p x κ = 0) : x 10 ≠ 0 ∧ x 4 ≠ 0 := by
  have h := S_ne p x κ hp hz
  rw [S_eq] at h
  exact ⟨fun h0 => h (by rw [h0]; ring), fun h0 => h (by rw [h0]; ring)⟩

theorem Z_ne (hp : PortFacts p) (hz : P131Value.valueK p x κ = 0) : (𝓑).Z ≠ 0 := by
  intro hZ
  have hS := S_ne p x κ hp hz
  obtain ⟨hs, _⟩ := s_r_ne p x κ hp hz
  have h0 := hz
  rw [P131Value.value_Z_zero p x κ hZ] at h0
  have h1 : (𝓡).S ^ 2 * ((𝓑).delta * ((𝓡).P * (𝓑).Df) - (𝓑).Cy) = 0 :=
    (pow_eq_zero_iff (n := 2) (by norm_num)).mp h0
  have h2 : (𝓑).delta * ((𝓡).P * (𝓑).Df) - (𝓑).Cy = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd ((pow_eq_zero_iff (n := 2) (by norm_num)).mp h) hS
    · exact h
  -- `P` divides `1`
  have h3 : (𝓡).P * ((𝓡).Delta ^ 2 * (𝓑).U ^ 2 * (𝓑).V ^ 2 - (𝓑).delta * (𝓑).Df) = 1 := by
    rw [P131Value.Cy_eq, P131Value.Q_eq] at h2
    linear_combination -h2
  have hP1 : (𝓡).P = 1 := by
    rcases unit_of_mul h3 with h | h
    · exact h
    · exfalso
      obtain ⟨m, hm⟩ := P_mod p x κ hp
      rw [hm] at h
      rcases int_split m with h' | h' <;> linarith
  -- `Dt = 1` and `D = 0`
  obtain ⟨hDt1, _⟩ := Dt_facts p x κ hp
  have h4 := P_eq p x κ
  rw [hP1] at h4
  have hDt : (𝓡).Dt = 1 := by
    rcases unit_of_mul h4.symm with h | h
    · exact h
    · linarith
  rw [hDt] at h4
  have h5 : (𝓡).D4 * x 10 ^ 2 = 0 := by linear_combination -h4
  have hD4 : (𝓡).D4 = 0 := by
    rcases mul_eq_zero.mp h5 with h | h
    · exact h
    · exact absurd ((pow_eq_zero_iff (n := 2) (by norm_num)).mp h) hs
  rw [D4_eq] at hD4
  obtain ⟨m, hm | hm⟩ := budget_mod p x κ hp <;> rw [hm] at hD4
  · rcases int_split m with h | h
    · rcases eq_or_lt_of_le h with h1 | h1
      · rw [← h1] at hD4; linarith
      · have := one_le_of_pos' h1; linarith
    · linarith
  · rcases int_split m with h | h <;> linarith

/-! ## The two roots -/

/-- **The first root**: `P · Df = g₀²`, with the linear relation `𝓘 = 𝓣 g₀`. -/
theorem guard_root (hp : PortFacts p) (hz : P131Value.valueK p x κ = 0) :
    ∃ g0 : DiffRing V, g0 * g0 = (𝓡).P * (𝓑).Df ∧
      (𝓑).delta * (𝓑).Z ^ 2 + (𝓑).delta * (𝓡).S ^ 2 * ((𝓡).P * (𝓑).Df) - (𝓡).S ^ 2 * (𝓑).Cy =
        2 * (𝓑).delta * (𝓑).Z * (𝓡).S * g0 := by
  have hS := S_ne p x κ hp hz
  have hZ := Z_ne p x κ hp hz
  have hd := delta_ne p x κ hp
  have hT : 2 * (𝓑).delta * (𝓑).Z * (𝓡).S ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hd) hZ) hS
  have h5 : ((𝓑).delta * (𝓑).Z ^ 2 + (𝓑).delta * (𝓡).S ^ 2 * ((𝓡).P * (𝓑).Df) -
        (𝓡).S ^ 2 * (𝓑).Cy) *
      ((𝓑).delta * (𝓑).Z ^ 2 + (𝓑).delta * (𝓡).S ^ 2 * ((𝓡).P * (𝓑).Df) -
        (𝓡).S ^ 2 * (𝓑).Cy) =
      ((2 * (𝓑).delta * (𝓑).Z * (𝓡).S) * (2 * (𝓑).delta * (𝓑).Z * (𝓡).S)) *
        ((𝓡).P * (𝓑).Df) := by
    have h0 := hz
    rw [P131Value.value_norm] at h0
    linear_combination h0
  obtain ⟨w, hw⟩ := dvd_of_sq_dvd_sq_ring
    (A := (𝓑).delta * (𝓑).Z ^ 2 + (𝓑).delta * (𝓡).S ^ 2 * ((𝓡).P * (𝓑).Df) -
      (𝓡).S ^ 2 * (𝓑).Cy)
    (B := 2 * (𝓑).delta * (𝓑).Z * (𝓡).S) ⟨_, h5⟩
  refine ⟨w, ?_, hw⟩
  rw [hw] at h5
  apply mul_left_cancel₀ (mul_ne_zero hT hT)
  linear_combination h5

/-- **The second root**: `δ · Cy` is a square. -/
theorem aux_root (hp : PortFacts p) (hz : P131Value.valueK p x κ = 0) :
    ∃ w : DiffRing V, w * w = (𝓑).delta * (𝓑).Cy := by
  have hS := S_ne p x κ hp hz
  have hZ := Z_ne p x κ hp hz
  have hT : 2 * (𝓑).Z * (𝓡).S ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hZ) hS
  have h5 : ((𝓑).delta * (𝓑).Z ^ 2 - (𝓑).delta * (𝓡).S ^ 2 * ((𝓡).P * (𝓑).Df) +
        (𝓡).S ^ 2 * (𝓑).Cy) *
      ((𝓑).delta * (𝓑).Z ^ 2 - (𝓑).delta * (𝓡).S ^ 2 * ((𝓡).P * (𝓑).Df) +
        (𝓡).S ^ 2 * (𝓑).Cy) =
      ((2 * (𝓑).Z * (𝓡).S) * (2 * (𝓑).Z * (𝓡).S)) * ((𝓑).delta * (𝓑).Cy) := by
    have h0 := hz
    rw [P131Value.value_norm'] at h0
    linear_combination h0
  obtain ⟨w, hw⟩ := dvd_of_sq_dvd_sq_ring
    (A := (𝓑).delta * (𝓑).Z ^ 2 - (𝓑).delta * (𝓡).S ^ 2 * ((𝓡).P * (𝓑).Df) +
      (𝓡).S ^ 2 * (𝓑).Cy)
    (B := 2 * (𝓑).Z * (𝓡).S) ⟨_, h5⟩
  refine ⟨w, ?_⟩
  rw [hw] at h5
  apply mul_left_cancel₀ (mul_ne_zero hT hT)
  linear_combination h5

/-- **`P` and `Df` are positive squares.** -/
theorem squares (hp : PortFacts p) (hz : P131Value.valueK p x κ = 0) :
    ∃ p0 f : V, 0 < p0 ∧ 0 < f ∧ (𝓡).P = ι p0 * ι p0 ∧ (𝓑).Df = ι f * ι f := by
  obtain ⟨g0, hg0, _⟩ := guard_root p x κ hp hz
  have hcop : ∃ α β, (𝓡).P * α + (𝓑).Df * β = 1 :=
    ⟨-((𝓡).Delta * (𝓑).U ^ 2), 1, by rw [P131Value.Df_eq]; ring⟩
  obtain ⟨⟨p0, hp0⟩, ⟨f, hf⟩⟩ := abs_squares_of_mul_square hcop hg0.symm
  have hP : 0 < (𝓡).P := by
    rcases lt_or_gt_of_ne (P_ne p x κ hp) with hneg | hpos
    · exfalso
      obtain ⟨m, hm⟩ := P_mod p x κ hp
      rw [abs_of_neg hneg] at hp0
      apply P138Squares.neg_sq_ne (ι p0) m
      rw [← hp0, neg_neg, hm]
    · exact hpos
  have hDf : 0 < (𝓑).Df := by
    rw [P131Value.Df_eq]
    have hD := Delta_gt p x κ hp
    have : 0 ≤ (𝓡).Delta * (𝓑).U ^ 2 * (𝓡).P :=
      mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) hP.le
    linarith
  rw [abs_of_pos hP] at hp0
  rw [abs_of_pos hDf] at hf
  refine ⟨p0, f, ?_, ?_, hp0, hf⟩
  · rcases eq_zero_or_pos p0 with h0 | h0
    · rw [h0, map_zero, mul_zero] at hp0; exact absurd hp0 hP.ne'
    · exact h0
  · rcases eq_zero_or_pos f with h0 | h0
    · rw [h0, map_zero, mul_zero] at hf; exact absurd hf hDf.ne'
    · exact h0

theorem P_pos (hp : PortFacts p) (hz : P131Value.valueK p x κ = 0) : 0 < (𝓡).P := by
  obtain ⟨p0, _, hp0, _, hPsq, _⟩ := squares p x κ hp hz
  rw [hPsq]; exact mul_pos (ι_pos hp0) (ι_pos hp0)

/-! ## The budget, and `Q > 1` -/

/-- **`Budget ≥ 12`**: a positive `P` with `s ≠ 0` excludes `Budget ≤ 3`, and the residues
`0, 12 (mod 16)` then leave `Budget ≥ 12`. -/
theorem budget_ge (hp : PortFacts p) (hz : P131Value.valueK p x κ = 0) :
    12 ≤ (𝓡).Budget := by
  have hP := P_pos p x κ hp hz
  obtain ⟨hs, _⟩ := s_r_ne p x κ hp hz
  obtain ⟨hDt, _⟩ := Dt_facts p x κ hp
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
  obtain ⟨m, hm | hm⟩ := budget_mod p x κ hp
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

theorem U_ne (hp : PortFacts p) (hz : P131Value.valueK p x κ = 0) : (𝓑).U ≠ 0 := by
  have hB : 0 < (𝓡).Budget := by linarith [budget_ge p x κ hp hz]
  rw [P131Value.U_eq]
  exact mul_ne_zero (s_r_ne p x κ hp hz).2 (pow_ne_zero 2 (P138Budget.c_ne p x κ hp hB))

theorem Q_gt (hp : PortFacts p) (hz : P131Value.valueK p x κ = 0) : 1 < (𝓑).Q := by
  have hP : 1 ≤ (𝓡).P := one_le_of_pos' (P_pos p x κ hp hz)
  have hD := Delta_gt p x κ hp
  have hU1 : 1 ≤ (𝓑).U ^ 2 := by
    have := one_le_abs (U_ne p x κ hp hz); rw [← sq_abs]; nlinarith
  have hD2 : 64 ≤ (𝓡).Delta ^ 2 := by nlinarith
  have h1 : 64 * 1 ≤ (𝓡).Delta ^ 2 * (𝓑).U ^ 2 :=
    mul_le_mul hD2 hU1 (by norm_num) (by positivity)
  have h2 : 64 * 1 * 1 ≤ (𝓡).Delta ^ 2 * (𝓑).U ^ 2 * (𝓡).P :=
    mul_le_mul h1 hP (by norm_num) (by positivity)
  rw [P131Value.Q_eq]
  linarith

/-! ## The descent and the linear slot -/

/-- **The auxiliary ordinate is integral, and `S ∣ Ac`.** -/
theorem descent (hp : PortFacts p) (hz : P131Value.valueK p x κ = 0) :
    ∃ y : V, 0 < y ∧ (𝓑).Q * (𝓑).V ^ 2 - ((𝓑).Q - 1) * (ι y) ^ 2 = 1 ∧
      (𝓡).S ∣ (𝓡).Ac := by
  obtain ⟨g0, hg0, hlin⟩ := guard_root p x κ hp hz
  obtain ⟨w, hw⟩ := aux_root p x κ hp hz
  have hd := delta_ne p x κ hp
  have hCy := Cy_ne p x κ hp
  obtain ⟨e, he⟩ := abs_eq_ι w
  have hww : (𝓑).delta * (𝓑).Cy = ι e * ι e := by rw [← he, abs_mul_abs_self, hw]
  have he0 : 0 < e := by
    rcases eq_zero_or_pos e with h0 | h0
    · rw [h0, map_zero, mul_zero] at hww; exact absurd hww (mul_ne_zero hd hCy)
    · exact h0
  have hQ := Q_gt p x κ hp hz
  obtain ⟨y, hy0, hey, haux⟩ := ZRowsStrongFold.adjacent_descent (Vr := (𝓑).V) hQ he0
    (by rw [← hww, P131Value.delta_def, P131Value.Cy_eq])
  have hey' : (ι e : DiffRing V) = (𝓑).delta * ι y := hey
  refine ⟨y, hy0, haux, ?_⟩
  have h1 : ((𝓑).delta * ((𝓑).Z - (𝓡).S * g0)) * ((𝓑).delta * ((𝓑).Z - (𝓡).S * g0)) =
      ((𝓑).delta * (𝓡).S * ι y) * ((𝓑).delta * (𝓡).S * ι y) := by
    linear_combination (𝓑).delta * hlin + (𝓑).delta ^ 2 * (𝓡).S ^ 2 * hg0 +
      (𝓡).S ^ 2 * hww + (𝓡).S ^ 2 * (ι e + (𝓑).delta * ι y) * hey'
  have hZ := P131Value.Z_def p x κ
  rcases mul_self_eq_mul_self_iff.mp h1 with h | h
  · have h2 : (𝓑).Z - (𝓡).S * g0 = (𝓡).S * ι y :=
      mul_left_cancel₀ hd (by linear_combination h)
    exact ⟨x 9 + (𝓑).V - g0 - ι y, by linear_combination hZ - h2⟩
  · have h2 : (𝓑).Z - (𝓡).S * g0 = -((𝓡).S * ι y) :=
      mul_left_cancel₀ hd (by linear_combination h)
    exact ⟨x 9 + (𝓑).V - g0 + ι y, by linear_combination hZ - h2⟩

end Regs

#print axioms mul_ne_one
#print axioms unit_of_mul
#print axioms S_ne
#print axioms Z_ne
#print axioms guard_root
#print axioms aux_root
#print axioms squares
#print axioms budget_ge
#print axioms Q_gt
#print axioms descent

end DiophantineConsistency.P131Roots
