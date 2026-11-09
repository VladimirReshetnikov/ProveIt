import DiophantineConsistency.P138.P138Value
import DiophantineConsistency.P138.P138Ports

/-! # Unconditional facts about the registers of package 138's 924/107 equation

In every model `V` of `𝗜𝚺₁`, for every point `x : Fin 11 → DiffRing V` (no zero is assumed) and
every port tuple satisfying `P138Ports.PortFacts`, the affine front and the guard have the
residues and sizes of `PROOF.md`, "The new compatibility argument" and the first paragraph of
"Soundness":

* `q_mod_six`, `abs_q`: `q ≡ 2 (mod 6)`, `|q| ≥ beta + 1`;
* `X_mod`, `abs_X`, `abs_Y`, `abs_a`: `X ≡ 0 (mod 8)`, `X ≡ 2 (mod 3)`, `|X| ≥ 4|q|`,
  `|Y|, |a| ≥ |q|³`;
* `A_facts`: `A` even, `|A| ≥ 3`, `H` odd, `Delta = A² − 1 > 1`, `Dm ≥ 1`;
* `Dt_facts`: `Dt ≥ 1`, `Dt ≡ 1 (mod 8)` (from `ℓ(ℓ+1) ≥ 0` and `8 ∣ X`);
* `budget_mod`: `Budget ≡ 0, 12 (mod 16)` (identity (2): `Budget + (qk)² ≡ 0` and an even square
  is `0` or `4` modulo sixteen), hence `D = Budget − 4 ≡ 0 (mod 4)` (`D4_mod`);
* `P_mod`, `Dg_mod`: the guard `Dg = 1 + D Dt s²` and `P = Dt Dg` are `1 (mod 4)` (identity (3));
* `Df_mod`, `Q_mod`: `Df ≡ 1`, `Q ≡ 0 (mod 4)`;
* `nonzero`: `BP`, `Df`, `delta = Q − 1` and `Cy = Q V² − 1` are nonzero.

The first section collects small facts about the discrete ordered ring `DiffRing V`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P138Bootstrap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing P138Value P138Ports

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Integers in `DiffRing V` -/

theorem one_le_of_pos' {a : DiffRing V} (h : 0 < a) : 1 ≤ a :=
  one_le_of_pos (fun _ ha => pos_iff_one_le.mp ha) h

theorem int_split (a : DiffRing V) : 0 ≤ a ∨ a ≤ -1 := by
  rcases le_or_gt 0 a with h | h
  · exact Or.inl h
  · right; have := one_le_of_pos' (neg_pos.mpr h); linarith

theorem one_le_abs {a : DiffRing V} (h : a ≠ 0) : 1 ≤ |a| := one_le_of_pos' (abs_pos.mpr h)

theorem even_or_odd' (u : DiffRing V) : ∃ t : DiffRing V, u = 2 * t ∨ u = 2 * t + 1 := by
  rcases nonneg_or_nonpos u with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · obtain ⟨t, ht | ht⟩ := even_or_odd a
    · exact ⟨ι t, Or.inl (by rw [ht, map_mul, map_ofNat])⟩
    · exact ⟨ι t, Or.inr (by rw [ht, map_add, map_mul, map_ofNat, map_one])⟩
  · obtain ⟨t, ht | ht⟩ := even_or_odd a
    · exact ⟨-ι t, Or.inl (by rw [ht, map_mul, map_ofNat]; ring)⟩
    · exact ⟨-ι t - 1, Or.inr (by rw [ht, map_add, map_mul, map_ofNat, map_one]; ring)⟩

theorem odd_ne_zero' (m : DiffRing V) : 2 * m + 1 ≠ 0 := by
  intro h
  rcases int_split m with hm | hm <;> linarith

theorem four_add_one_ne (m : DiffRing V) : 4 * m + 1 ≠ 0 := by
  have := odd_ne_zero' (2 * m); intro h; apply this; linear_combination h

theorem four_sub_one_ne (m : DiffRing V) : 4 * m - 1 ≠ 0 := by
  have := odd_ne_zero' (2 * m - 1); intro h; apply this; linear_combination h

/-- An even square is `0` or `4` modulo sixteen. -/
theorem even_sq_mod (g : DiffRing V) : ∃ e : DiffRing V, 4 * g ^ 2 = 16 * e ∨ 4 * g ^ 2 = 16 * e + 4 := by
  obtain ⟨t, ht | ht⟩ := even_or_odd' g
  · exact ⟨t ^ 2, Or.inl (by rw [ht]; ring)⟩
  · exact ⟨t ^ 2 + t, Or.inr (by rw [ht]; ring)⟩

theorem mul_succ_nonneg (l : DiffRing V) : 0 ≤ l * (l + 1) := by
  rcases int_split l with h | h
  · exact mul_nonneg h (by linarith)
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

/-! ## The affine front -/

section Front
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V)
local notation "𝓡" => regs p x

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
  obtain ⟨t, ht⟩ := q_mod_six p x hp
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
  have h := abs_q p x hp
  have hb := beta_pos p hp
  intro h0; rw [h0, abs_zero] at h; linarith

theorem abs_q_ge (hp : PortFacts p) : 2 ^ 64 ≤ |(𝓡).q| := by
  have := abs_q p x hp; have := hp.beta_ge; linarith

theorem W_mod : (𝓡).W = 4 * (3 * x 6 + 1) := by rw [W_eq]; ring

theorem abs_W : 4 ≤ |(𝓡).W| := by
  rw [W_eq]
  rcases int_split (x 6) with h | h
  · rw [abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_neg (by linarith)]; linarith

theorem X_mod (hp : PortFacts p) :
    (∃ m : DiffRing V, (𝓡).X = 8 * m) ∧ ∃ m : DiffRing V, (𝓡).X = 3 * m + 2 := by
  obtain ⟨t, ht⟩ := q_mod_six p x hp
  refine ⟨⟨(3 * t + 1) * (3 * x 6 + 1), ?_⟩, ⟨24 * t * x 6 + 8 * t + 8 * x 6 + 2, ?_⟩⟩ <;>
    rw [X_def, W_mod, ht] <;> ring

theorem abs_X (hp : PortFacts p) : 4 * |(𝓡).q| ≤ |(𝓡).X| := by
  rw [X_def, abs_mul, mul_comm 4]
  exact mul_le_mul_of_nonneg_left (abs_W p x) (abs_nonneg _)

theorem X_ne (hp : PortFacts p) : (𝓡).X ≠ 0 := by
  have h := abs_X p x hp; have h2 := abs_q_ge p x hp
  intro h0; rw [h0, abs_zero] at h; have : (0:DiffRing V) < 2^64 := by positivity
  linarith

theorem abs_Y (hp : PortFacts p) : |(𝓡).q| ^ 3 ≤ |(𝓡).Y| := by
  rw [Y_eq, abs_mul, abs_pow]
  have h1 : 1 ≤ |2 * x 5 + 1| := one_le_abs (odd_ne_zero' _)
  have h2 : 0 ≤ |(𝓡).q| ^ 3 := by positivity
  nlinarith

theorem Y_even (hp : PortFacts p) : ∃ m : DiffRing V, (𝓡).Y = 2 * m := by
  obtain ⟨t, ht⟩ := q_even p x hp
  exact ⟨4 * t ^ 3 * (2 * x 5 + 1), by rw [Y_eq, ht]; ring⟩

theorem abs_a (hp : PortFacts p) : |(𝓡).q| ^ 3 ≤ |(𝓡).a| := by
  obtain ⟨⟨m, hm⟩, _⟩ := X_mod p x hp
  have hX1 : 1 ≤ |(𝓡).X + 1| := one_le_abs (by
    rw [hm, show (8:DiffRing V) * m + 1 = 4 * (2 * m) + 1 by ring]; exact four_add_one_ne (2 * m))
  have ha : (𝓡).a = (𝓡).Y * ((𝓡).X + 1) := by rw [a_eq]; ring
  rw [ha, abs_mul]
  have hY := abs_Y p x hp
  nlinarith [abs_nonneg (𝓡).Y]

theorem abs_a_ge (hp : PortFacts p) : 2 ^ 64 ≤ |(𝓡).a| := by
  have h1 := abs_a p x hp
  have h2 := abs_q_ge p x hp
  have h3 : (1 : DiffRing V) ≤ 2 ^ 64 := one_le_pow₀ (by norm_num)
  have h4 : |(𝓡).q| ≤ |(𝓡).q| ^ 3 := by
    have : 1 ≤ |(𝓡).q| := by linarith
    calc |(𝓡).q| = |(𝓡).q| ^ 1 := (pow_one _).symm
      _ ≤ |(𝓡).q| ^ 3 := pow_le_pow_right₀ this (by norm_num)
  linarith

theorem A_even (hp : PortFacts p) : ∃ m : DiffRing V, (𝓡).A = 2 * m := by
  obtain ⟨⟨m, hm⟩, _⟩ := X_mod p x hp
  obtain ⟨y, hy⟩ := Y_even p x hp
  exact ⟨y * (8 * m + 1) + 1, by rw [A_eq, a_eq, hm, hy]; ring⟩

theorem abs_A (hp : PortFacts p) : 3 ≤ |(𝓡).A| := by
  have h := abs_a_ge p x hp
  have h2 : (5 : DiffRing V) ≤ 2 ^ 64 := by norm_num
  have h3 : |(𝓡).a| ≤ |(𝓡).A| + 2 := by
    have ha : (𝓡).a = (𝓡).A - 2 := by rw [A_eq]; ring
    rw [ha]
    exact abs_le.mpr ⟨by linarith [neg_abs_le (𝓡).A], by linarith [le_abs_self (𝓡).A]⟩
  linarith

theorem H_odd : ∃ m : DiffRing V, (𝓡).H = 2 * m + 1 := ⟨2 * (𝓡).a + 1, by rw [H_def]; ring⟩

theorem H_ne : (𝓡).H ≠ 0 := by
  obtain ⟨m, hm⟩ := H_odd p x; rw [hm]; exact odd_ne_zero' m

theorem Delta_gt (hp : PortFacts p) : 8 ≤ (𝓡).Delta := by
  rw [Delta_eq]
  have h := abs_A p x hp
  have : 9 ≤ |(𝓡).A| ^ 2 := by nlinarith
  rw [sq_abs] at this
  linarith

theorem Dm_ge (hp : PortFacts p) : 1 ≤ (𝓡).Dm := by
  rw [Dm_eq]
  have := Delta_gt p x hp
  have : 0 ≤ (𝓡).Delta * x 8 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  linarith

theorem A_facts (hp : PortFacts p) :
    (∃ m : DiffRing V, (𝓡).A = 2 * m) ∧ 3 ≤ |(𝓡).A| ∧ (∃ m : DiffRing V, (𝓡).H = 2 * m + 1) ∧
      1 < (𝓡).Delta ∧ 1 ≤ (𝓡).Dm :=
  ⟨A_even p x hp, abs_A p x hp, H_odd p x, by linarith [Delta_gt p x hp], Dm_ge p x hp⟩

/-! ## The guard -/

theorem Dt_facts (hp : PortFacts p) : 1 ≤ (𝓡).Dt ∧ ∃ m : DiffRing V, (𝓡).Dt = 8 * m + 1 := by
  obtain ⟨⟨m, hm⟩, _⟩ := X_mod p x hp
  have h0 := mul_succ_nonneg ((𝓡).X * (𝓡).Y ^ 2)
  refine ⟨?_, ⟨m * (𝓡).Y ^ 2 * ((𝓡).X * (𝓡).Y ^ 2 + 1) * (𝓡).k ^ 2, ?_⟩⟩
  · rw [Dt_eq]; nlinarith [sq_nonneg (𝓡).k]
  · rw [Dt_eq]; rw [hm]; ring

/-- **Identity (2) of `PROOF.md`.** `Budget ≡ 0` or `12 (mod 16)`. -/
theorem budget_mod (hp : PortFacts p) :
    ∃ m : DiffRing V, (𝓡).Budget = 16 * m ∨ (𝓡).Budget = 16 * m + 12 := by
  obtain ⟨t, ht⟩ := q_even p x hp
  obtain ⟨u, hu⟩ := hp.coneA_sixteen
  obtain ⟨v, hv⟩ := hp.coneB_sixteen
  set M : DiffRing V := (𝓡).k ^ 2 * (4 * t * (u * (𝓡).F + v * x 1) - 16 * (u * (𝓡).F) ^ 2 -
    16 * (v * x 1) ^ 2) - t ^ 2 * (𝓡).eta ^ 2 with hM
  have hB : (𝓡).Budget = 16 * M - 4 * (t * (𝓡).k) ^ 2 := by
    rw [Budget_eq, Derr_eq, ht, hu, hv, hM]; ring
  obtain ⟨e, he | he⟩ := even_sq_mod (t * (𝓡).k)
  · exact ⟨M - e, Or.inl (by rw [hB, he]; ring)⟩
  · exact ⟨M - e - 1, Or.inr (by rw [hB, he]; ring)⟩

theorem D4_mod (hp : PortFacts p) : ∃ d : DiffRing V, (𝓡).D4 = 4 * d := by
  obtain ⟨m, hm | hm⟩ := budget_mod p x hp
  · exact ⟨4 * m - 1, by rw [D4_eq, hm]; ring⟩
  · exact ⟨4 * m + 2, by rw [D4_eq, hm]; ring⟩

/-- The guard `Dg = 1 + D Dt s²`. -/
theorem Dg_mod (hp : PortFacts p) :
    ∃ m : DiffRing V, 1 + (𝓡).D4 * (𝓡).Dt * x 10 ^ 2 = 4 * m + 1 := by
  obtain ⟨d, hd⟩ := D4_mod p x hp
  exact ⟨d * (𝓡).Dt * x 10 ^ 2, by rw [hd]; ring⟩

/-- **Identity (3) of `PROOF.md`.** `P ≡ 1 (mod 4)`. -/
theorem P_mod (hp : PortFacts p) : ∃ m : DiffRing V, (𝓡).P = 4 * m + 1 := by
  obtain ⟨g, hg⟩ := Dg_mod p x hp
  obtain ⟨_, ⟨m, hm⟩⟩ := Dt_facts p x hp
  exact ⟨8 * m * g + 2 * m + g, by rw [P_eq, hg, hm]; ring⟩

theorem P_ne (hp : PortFacts p) : (𝓡).P ≠ 0 := by
  obtain ⟨m, hm⟩ := P_mod p x hp; rw [hm]; exact four_add_one_ne m

theorem U_even (hp : PortFacts p) : ∃ u : DiffRing V, (𝓡).U = 2 * u := by
  obtain ⟨m, hm⟩ := A_even p x hp
  exact ⟨m * x 4 * x 8 ^ 2, by rw [U_eq, hm]; ring⟩

theorem Df_mod (hp : PortFacts p) : ∃ m : DiffRing V, (𝓡).Df = 4 * m + 1 := by
  obtain ⟨u, hu⟩ := U_even p x hp
  exact ⟨(𝓡).Delta * u ^ 2 * (𝓡).BP, by rw [Df_eq, hu]; ring⟩

theorem Q_mod (hp : PortFacts p) : ∃ m : DiffRing V, (𝓡).Q = 4 * m := by
  obtain ⟨u, hu⟩ := U_even p x hp
  exact ⟨(𝓡).Delta ^ 2 * u ^ 2 * (𝓡).BP, by rw [Q_eq, hu]; ring⟩

theorem nonzero (hp : PortFacts p) :
    (𝓡).BP ≠ 0 ∧ (𝓡).Df ≠ 0 ∧ (𝓡).Q - 1 ≠ 0 ∧ (𝓡).Q * (𝓡).V ^ 2 - 1 ≠ 0 := by
  obtain ⟨m, hm⟩ := Df_mod p x hp
  obtain ⟨n, hn⟩ := Q_mod p x hp
  refine ⟨?_, by rw [hm]; exact four_add_one_ne m, by rw [hn]; exact four_sub_one_ne n, ?_⟩
  · rw [BP_eq]
    exact mul_ne_zero (show (0:DiffRing V) < (𝓡).Dm by linarith [Dm_ge p x hp]).ne' (P_ne p x hp)
  · rw [hn, show 4 * n * (𝓡).V ^ 2 = 4 * (n * (𝓡).V ^ 2) by ring]
    exact four_sub_one_ne _

end Front

#print axioms even_or_odd'
#print axioms even_sq_mod
#print axioms abs_q
#print axioms X_mod
#print axioms abs_X
#print axioms abs_Y
#print axioms abs_a
#print axioms A_facts
#print axioms Dt_facts
#print axioms budget_mod
#print axioms D4_mod
#print axioms Dg_mod
#print axioms P_mod
#print axioms Df_mod
#print axioms Q_mod
#print axioms nonzero

end DiophantineConsistency.P138Bootstrap
