import DiophantineConsistency.LinCof.LCValue
import DiophantineConsistency.P138.P138Bootstrap

/-! # Unconditional facts about the registers of the linear-cofactor family

The registers are those of `LCValue.regsK p x κ ω Λ ψ wt`, for any values of the four slots, so
every fact here holds for package 172's 298/146 and 300/144 forms alike. Facts about the guard
assume the slot law `LCValue.SlotLaw p x κ ω Λ e`.

In every model `V` of `𝗜𝚺₁`, for every point `x : Fin 11 → DiffRing V` (no zero is assumed) and
every port tuple satisfying `P138Ports.PortFacts`:

* `q_mod_six`, `abs_q`: `q ≡ 2 (mod 6)`, `|q| ≥ beta + 1`;
* `X_mod`, `abs_X`: `X ≡ 0 (mod 8)`, `X ≡ 2 (mod 3)`, `|X| ≥ 4|q|`;
* `a_fac`, `a_zero_or`: `a = Y (X + 1)`, so `a = 0` (exactly when the free scale `Y` vanishes) or
  `|a| ≥ 2⁶⁴`; `A_mod3`: `A ≡ 2 (mod 3)`;
* `abs_A_ge`, `Delta_ge`, `Dm_ge`: `|A| ≥ 2`, `Delta = A² − 1 ≥ 3`, `Dm ≥ 1`; with `Y ≠ 0` the
  package-138 sizes `|A| ≥ 3`, `Delta ≥ 8` return (`abs_A_of_Y`, `Delta_of_Y`);
* `strong_mod`, `Df_mod`, `Q_mod`: `Df ≡ 1`, `Q ≡ 0 (mod 4)` for every parity of `A` and `c`
  (`four_dvd_core`: if `A` is odd then `4 ∣ A² − 1`; if `A` and `c` are even then `16 ∣ c⁴`; if
  `A` is even and `c` is odd then `4 ∣ Dm`). In package 138 this needed `Y` even;
* `nonzero`: `Df`, `delta = Q − 1` and `Cy = Q V² − 1` are nonzero; `A_ne`, `M_ne`, `Dc_ne`;
* `Dt_facts`: `Dt ≥ 1`, `Dt ≡ 1 (mod 8)`;
* `budget_mod`: `Budget ≡ 0, 12 (mod 16)`, hence `Dguard = Budget − 4 ≡ 0 (mod 4)`
  (`Dguard_mod`), the guard `Dg = 1 + Dguard Dt s²` and `P = Dt Dg` are `1 (mod 4)` (`Dg_mod`,
  `P_mod`).

The free scale `Y = x 5` is not assumed nonzero anywhere in this module. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.LCBootstrap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing LCValue P138Ports
open P138Bootstrap (one_le_of_pos' int_split one_le_abs even_or_odd' odd_ne_zero' four_add_one_ne
  four_sub_one_ne even_sq_mod mul_succ_nonneg)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Two ring facts -/

/-- `3 m + 2` is not zero. -/
theorem three_add_two_ne (m : DiffRing V) : 3 * m + 2 ≠ 0 := by
  intro h
  rcases int_split m with hm | hm <;> linarith

/-- `Δ · c⁴ · A · Dm ≡ 0 (mod 4)` with `Δ = A² − 1`, `Dm = 1 + Δ c²`, for all `A` and `c`. -/
theorem four_dvd_core (A c : DiffRing V) :
    ∃ n : DiffRing V, (A ^ 2 - 1) * (c ^ 4 * (A * (1 + (A ^ 2 - 1) * c ^ 2))) = 4 * n := by
  obtain ⟨t, rfl | rfl⟩ := even_or_odd' A
  · obtain ⟨s, rfl | rfl⟩ := even_or_odd' c
    · exact ⟨((2 * t) ^ 2 - 1) * (4 * s ^ 4) * (2 * t * (1 + ((2 * t) ^ 2 - 1) * (2 * s) ^ 2)),
        by ring⟩
    · exact ⟨((2 * t) ^ 2 - 1) * (2 * s + 1) ^ 4 * (2 * t) *
        (t ^ 2 * (2 * s + 1) ^ 2 - s ^ 2 - s), by ring⟩
  · exact ⟨t * (t + 1) * (c ^ 4 * ((2 * t + 1) * (1 + ((2 * t + 1) ^ 2 - 1) * c ^ 2))), by ring⟩

/-! ## The affine front -/

section Front
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V) (κ ω Λ ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

theorem beta_pos (hp : PortFacts p) : 0 < p 0 := by
  have h := hp.beta_ge
  have : (0 : DiffRing V) < 2 ^ 64 := by positivity
  linarith

theorem J_ne : (𝓡).J ≠ 0 := by
  rw [J_def]; intro h; apply odd_ne_zero' (3 * x 0); linear_combination h

theorem q_mod_six (hp : PortFacts p) : ∃ t : DiffRing V, (𝓡).q = 6 * t + 2 := by
  obtain ⟨m, hm⟩ := hp.beta_mod
  exact ⟨6 * m * x 0 + m + x 0, by rw [q_eq, hm]; ring⟩

theorem q_even (hp : PortFacts p) : ∃ t : DiffRing V, (𝓡).q = 2 * t := by
  obtain ⟨t, ht⟩ := q_mod_six p x κ ω Λ ψ wt hp
  exact ⟨3 * t + 1, by rw [ht]; ring⟩

theorem abs_q (hp : PortFacts p) : p 0 + 1 ≤ |(𝓡).q| := by
  have hb := beta_pos p hp
  have hb1 : 1 ≤ p 0 := by
    have := hp.beta_ge; have : (1:DiffRing V) ≤ 2^64 := one_le_pow₀ (by norm_num); linarith
  rw [q_eq]
  rcases int_split (x 0) with h | h
  · have h1 : 0 ≤ p 0 * (6 * x 0) := mul_nonneg hb.le (by linarith)
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith
  · have h1 : 0 ≤ p 0 * (-6 * x 0 - 6) := mul_nonneg hb.le (by linarith)
    rw [abs_of_neg (by nlinarith)]
    nlinarith

theorem q_ne (hp : PortFacts p) : (𝓡).q ≠ 0 := by
  have h := abs_q p x κ ω Λ ψ wt hp
  have hb := beta_pos p hp
  intro h0; rw [h0, abs_zero] at h; linarith

theorem abs_q_ge (hp : PortFacts p) : 2 ^ 64 ≤ |(𝓡).q| := by
  have := abs_q p x κ ω Λ ψ wt hp; have := hp.beta_ge; linarith

theorem W_mod : (𝓡).W = 4 * (3 * x 6 + 1) := by rw [W_eq]; ring

theorem abs_W : 4 ≤ |(𝓡).W| := by
  rw [W_eq]
  rcases int_split (x 6) with h | h
  · rw [abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_neg (by linarith)]; linarith

theorem X_mod (hp : PortFacts p) :
    (∃ m : DiffRing V, (𝓡).X = 8 * m) ∧ ∃ m : DiffRing V, (𝓡).X = 3 * m + 2 := by
  obtain ⟨t, ht⟩ := q_mod_six p x κ ω Λ ψ wt hp
  refine ⟨⟨(3 * t + 1) * (3 * x 6 + 1), ?_⟩, ⟨24 * t * x 6 + 8 * t + 8 * x 6 + 2, ?_⟩⟩ <;>
    rw [X_def, W_mod, ht] <;> ring

theorem abs_X : 4 * |(𝓡).q| ≤ |(𝓡).X| := by
  rw [X_def, abs_mul, mul_comm 4]
  exact mul_le_mul_of_nonneg_left (abs_W p x κ ω Λ ψ wt) (abs_nonneg _)

theorem abs_X_ge (hp : PortFacts p) : 2 ^ 66 ≤ |(𝓡).X| := by
  have h := abs_X p x κ ω Λ ψ wt; have h2 := abs_q_ge p x κ ω Λ ψ wt hp
  have : (2:DiffRing V) ^ 66 = 4 * 2 ^ 64 := by norm_num
  linarith

theorem X_ne (hp : PortFacts p) : (𝓡).X ≠ 0 := by
  have h := abs_X_ge p x κ ω Λ ψ wt hp
  intro h0; rw [h0, abs_zero] at h; have : (0:DiffRing V) < 2^66 := by positivity
  linarith

/-- `a = Y (X + 1)`: the free scale divides `a`. -/
theorem a_fac : (𝓡).a = (𝓡).Y * ((𝓡).X + 1) := by rw [a_eq]; ring

theorem abs_X_succ (hp : PortFacts p) : 2 ^ 64 ≤ |(𝓡).X + 1| := by
  have h := abs_X_ge p x κ ω Λ ψ wt hp
  have h3 : |(𝓡).X| ≤ |(𝓡).X + 1| + 1 :=
    abs_le.mpr ⟨by linarith [neg_abs_le ((𝓡).X + 1)], by linarith [le_abs_self ((𝓡).X + 1)]⟩
  have : (2:DiffRing V) ^ 66 = 4 * 2 ^ 64 := by norm_num
  have : (1:DiffRing V) ≤ 2 ^ 64 := one_le_pow₀ (by norm_num)
  linarith

/-- With a nonzero scale, `|a| ≥ |X + 1|`. -/
theorem abs_a_of_Y (hY : (𝓡).Y ≠ 0) : |(𝓡).X + 1| ≤ |(𝓡).a| := by
  rw [a_fac, abs_mul]
  have h1 := one_le_abs hY
  nlinarith [abs_nonneg ((𝓡).X + 1)]

/-- Either the scale vanishes (and then `a = 0`) or `a` is huge. -/
theorem a_zero_or (hp : PortFacts p) : (𝓡).a = 0 ∨ 2 ^ 64 ≤ |(𝓡).a| := by
  by_cases hY : (𝓡).Y = 0
  · left; rw [a_fac, hY, zero_mul]
  · right
    exact le_trans (abs_X_succ p x κ ω Λ ψ wt hp) (abs_a_of_Y p x κ ω Λ ψ wt hY)

theorem a_mod3 (hp : PortFacts p) : ∃ m : DiffRing V, (𝓡).a = 3 * m := by
  obtain ⟨_, ⟨m, hm⟩⟩ := X_mod p x κ ω Λ ψ wt hp
  exact ⟨(𝓡).Y * (m + 1), by rw [a_fac, hm]; ring⟩

/-- `A ≡ 2 (mod 3)`. -/
theorem A_mod3 (hp : PortFacts p) : ∃ m : DiffRing V, (𝓡).A = 3 * m + 2 := by
  obtain ⟨m, hm⟩ := a_mod3 p x κ ω Λ ψ wt hp
  exact ⟨m, by rw [A_eq, hm]⟩

theorem A_ne (hp : PortFacts p) : (𝓡).A ≠ 0 := by
  obtain ⟨m, hm⟩ := A_mod3 p x κ ω Λ ψ wt hp
  rw [hm]; exact three_add_two_ne m

theorem abs_a_le_A : |(𝓡).a| ≤ |(𝓡).A| + 2 := by
  have ha : (𝓡).a = (𝓡).A - 2 := by rw [A_eq]; ring
  rw [ha]
  exact abs_le.mpr ⟨by linarith [neg_abs_le (𝓡).A], by linarith [le_abs_self (𝓡).A]⟩

theorem abs_A_ge (hp : PortFacts p) : 2 ≤ |(𝓡).A| := by
  rcases a_zero_or p x κ ω Λ ψ wt hp with h | h
  · rw [A_eq, h, zero_add]; norm_num
  · have h2 : (5 : DiffRing V) ≤ 2 ^ 64 := by norm_num
    have h3 := abs_a_le_A p x κ ω Λ ψ wt
    linarith

theorem abs_A_of_Y (hp : PortFacts p) (hY : (𝓡).Y ≠ 0) : 3 ≤ |(𝓡).A| := by
  have h := le_trans (abs_X_succ p x κ ω Λ ψ wt hp) (abs_a_of_Y p x κ ω Λ ψ wt hY)
  have h2 : (5 : DiffRing V) ≤ 2 ^ 64 := by norm_num
  have h3 := abs_a_le_A p x κ ω Λ ψ wt
  linarith

theorem H_odd : ∃ m : DiffRing V, (𝓡).H = 2 * m + 1 := ⟨2 * (𝓡).a + 1, by rw [H_def]; ring⟩

theorem H_ne : (𝓡).H ≠ 0 := by
  obtain ⟨m, hm⟩ := H_odd p x κ ω Λ ψ wt; rw [hm]; exact odd_ne_zero' m

theorem Delta_ge (hp : PortFacts p) : 3 ≤ (𝓡).Delta := by
  rw [Delta_eq]
  have h := abs_A_ge p x κ ω Λ ψ wt hp
  have : 4 ≤ |(𝓡).A| ^ 2 := by nlinarith
  rw [sq_abs] at this
  linarith

theorem Delta_of_Y (hp : PortFacts p) (hY : (𝓡).Y ≠ 0) : 8 ≤ (𝓡).Delta := by
  rw [Delta_eq]
  have h := abs_A_of_Y p x κ ω Λ ψ wt hp hY
  have : 9 ≤ |(𝓡).A| ^ 2 := by nlinarith
  rw [sq_abs] at this
  linarith

theorem Dm_ge (hp : PortFacts p) : 1 ≤ (𝓡).Dm := by
  rw [Dm_eq]
  have := Delta_ge p x κ ω Λ ψ wt hp
  have : 0 ≤ (𝓡).Delta * x 8 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  linarith

theorem M_ne (hp : PortFacts p) : (𝓡).M ≠ 0 := by
  rw [M_eq]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 3 (q_ne p x κ ω Λ ψ wt hp))

theorem Dc_ne (hp : PortFacts p) : (𝓡).Dc ≠ 0 := by
  rw [Dc_eq]
  exact mul_ne_zero (H_ne p x κ ω Λ ψ wt) (M_ne p x κ ω Λ ψ wt hp)

/-! ## The residues modulo four of the strong pair -/

/-- `strong = Δ c⁴ B ≡ 0 (mod 4)`, for every parity of `A` and `c`. -/
theorem strong_mod : ∃ n : DiffRing V, (𝓡).strong = 4 * n := by
  obtain ⟨n, hn⟩ := four_dvd_core (𝓡).A (x 8)
  refine ⟨x 4 * n, ?_⟩
  rw [strong_eq, B_eq, Dm_eq, Delta_eq]
  linear_combination x 4 * hn

theorem Df_mod : ∃ m : DiffRing V, (𝓡).Df = 4 * m + 1 := by
  obtain ⟨n, hn⟩ := strong_mod p x κ ω Λ ψ wt
  exact ⟨n, by rw [Df_def, hn]; ring⟩

theorem Q_mod : ∃ m : DiffRing V, (𝓡).Q = 4 * m := by
  obtain ⟨n, hn⟩ := strong_mod p x κ ω Λ ψ wt
  exact ⟨(𝓡).Delta * n, by rw [Q_def, hn]; ring⟩

theorem delta_mod : ∃ m : DiffRing V, (𝓡).delta = 4 * m - 1 := by
  obtain ⟨n, hn⟩ := Q_mod p x κ ω Λ ψ wt
  exact ⟨n, by rw [delta_eq, hn]⟩

theorem Cy_mod : ∃ m : DiffRing V, (𝓡).Cy = 4 * m - 1 := by
  obtain ⟨n, hn⟩ := Q_mod p x κ ω Λ ψ wt
  exact ⟨n * (𝓡).V ^ 2, by rw [Cy_eq, hn]; ring⟩

/-- `Df`, `delta = Q − 1` and `Cy = Q V² − 1` are nonzero. -/
theorem nonzero : (𝓡).Df ≠ 0 ∧ (𝓡).delta ≠ 0 ∧ (𝓡).Cy ≠ 0 := by
  obtain ⟨m, hm⟩ := Df_mod p x κ ω Λ ψ wt
  obtain ⟨n, hn⟩ := delta_mod p x κ ω Λ ψ wt
  obtain ⟨c, hc⟩ := Cy_mod p x κ ω Λ ψ wt
  exact ⟨by rw [hm]; exact four_add_one_ne m, by rw [hn]; exact four_sub_one_ne n,
    by rw [hc]; exact four_sub_one_ne c⟩

end Front

/-! ## The guard, under the slot law -/

section Guard
variable {p : Fin 6 → DiffRing V} {x : Fin 11 → DiffRing V} {κ ω Λ : DiffRing V} {e : ℕ}
variable (ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

theorem Dt_facts (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) :
    1 ≤ (𝓡).Dt ∧ ∃ m : DiffRing V, (𝓡).Dt = 8 * m + 1 := by
  obtain ⟨⟨m, hm⟩, _⟩ := X_mod p x κ ω Λ ψ wt hp
  have h0 := mul_succ_nonneg ((𝓡).X * (𝓡).Y ^ 2)
  refine ⟨?_, ⟨m * (𝓡).Y ^ 2 * ((𝓡).X * (𝓡).Y ^ 2 + 1) * (𝓡).k ^ 2, ?_⟩⟩
  · rw [h.Dt_eq ψ wt]; nlinarith [sq_nonneg (𝓡).k]
  · rw [h.Dt_eq ψ wt]; rw [hm]; ring

/-- **Identity (2) of `PROOF.md`.** `Budget ≡ 0` or `12 (mod 16)`. -/
theorem budget_mod (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) :
    ∃ m : DiffRing V, (𝓡).Budget = 16 * m ∨ (𝓡).Budget = 16 * m + 12 := by
  obtain ⟨t, ht⟩ := q_even p x κ ω Λ ψ wt hp
  obtain ⟨u, hu⟩ := hp.coneA_sixteen
  obtain ⟨v, hv⟩ := hp.coneB_sixteen
  have hq6 : (𝓡).q ^ (6 + 2 * e) = 64 * (t ^ 6 * (𝓡).q ^ (2 * e)) := by
    calc (𝓡).q ^ (6 + 2 * e) = (𝓡).q ^ 6 * (𝓡).q ^ (2 * e) := pow_add _ _ _
      _ = (2 * t) ^ 6 * (𝓡).q ^ (2 * e) := by rw [← ht]
      _ = 64 * (t ^ 6 * (𝓡).q ^ (2 * e)) := by ring
  have hq2 : (𝓡).q ^ 2 = 4 * t ^ 2 := by rw [ht]; ring
  have hD : (𝓡).q ^ 2 - (𝓡).Derr = -(4 * t ^ 2) + 16 * (4 * t * (u * (𝓡).F + v * x 1) -
      16 * (u * (𝓡).F) ^ 2 - 16 * (v * x 1) ^ 2) := by
    rw [Derr_eq, hu, hv, ht]; ring
  have hB : ∃ M : DiffRing V, (𝓡).Budget = 16 * M - 4 * (t * (𝓡).k * (𝓡).Y) ^ 2 := by
    refine ⟨((𝓡).k ^ 2 * (4 * t * (u * (𝓡).F + v * x 1) - 16 * (u * (𝓡).F) ^ 2 -
      16 * (v * x 1) ^ 2) - t ^ 2 * (𝓡).eta ^ 2) * (𝓡).Y ^ 2 -
      4 * ((𝓡).k ^ 2 * (t ^ 6 * (𝓡).q ^ (2 * e))), ?_⟩
    rw [h.Budget_eq ψ wt, hq6, B0, hD, hq2]; ring
  obtain ⟨M, hM⟩ := hB
  obtain ⟨g, hg | hg⟩ := even_sq_mod (t * (𝓡).k * (𝓡).Y)
  · exact ⟨M - g, Or.inl (by rw [hM, hg]; ring)⟩
  · exact ⟨M - g - 1, Or.inr (by rw [hM, hg]; ring)⟩

theorem Dguard_mod (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) :
    ∃ d : DiffRing V, (𝓡).Dguard = 4 * d := by
  obtain ⟨m, hm | hm⟩ := budget_mod ψ wt hp h
  · exact ⟨4 * m - 1, by rw [Dguard_eq, hm]; ring⟩
  · exact ⟨4 * m + 2, by rw [Dguard_eq, hm]; ring⟩

/-- The guard `Dg = 1 + D Dt s²`. -/
theorem Dg_mod (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) :
    ∃ m : DiffRing V, 1 + (𝓡).Dguard * (𝓡).Dt * x 10 ^ 2 = 4 * m + 1 := by
  obtain ⟨d, hd⟩ := Dguard_mod ψ wt hp h
  exact ⟨d * (𝓡).Dt * x 10 ^ 2, by rw [hd]; ring⟩

/-- **Identity (3) of `PROOF.md`.** `P ≡ 1 (mod 4)`. -/
theorem P_mod (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) :
    ∃ m : DiffRing V, (𝓡).P = 4 * m + 1 := by
  obtain ⟨g, hg⟩ := Dg_mod ψ wt hp h
  obtain ⟨_, ⟨m, hm⟩⟩ := Dt_facts ψ wt hp h
  exact ⟨8 * m * g + 2 * m + g, by rw [P_eq, hg, hm]; ring⟩

theorem P_ne (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) : (𝓡).P ≠ 0 := by
  obtain ⟨m, hm⟩ := P_mod ψ wt hp h; rw [hm]; exact four_add_one_ne m

end Guard

#print axioms four_dvd_core
#print axioms abs_q
#print axioms X_mod
#print axioms a_zero_or
#print axioms A_mod3
#print axioms abs_A_ge
#print axioms Delta_ge
#print axioms Dm_ge
#print axioms strong_mod
#print axioms nonzero
#print axioms Dt_facts
#print axioms budget_mod
#print axioms Dguard_mod
#print axioms Dg_mod
#print axioms P_mod

end DiophantineConsistency.LCBootstrap
