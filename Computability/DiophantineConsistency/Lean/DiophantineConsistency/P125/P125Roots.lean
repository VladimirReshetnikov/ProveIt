import DiophantineConsistency.P125.P125Value
import DiophantineConsistency.ZRows.StrongFold

/-! # The three roots of package 125's 488/118 and 464/119 equations

At a zero of the output `P125Value.outK p x κ ζ` in the ring of differences of a model of
`𝗜𝚺₁`, with the port facts of package 138 (`P138Ports.PortFacts`). Both the `k` slot `κ` and the
linear slot `ζ` are arbitrary: the only thing read from the slot is `S ∣ ζ + Ac`, which holds
for the direct slot `n S − Ac` and for the centered slot `S (n + Q V) − Ac`.

* **Residues modulo 3.** `X ≡ 2 (mod 3)` makes `a = (X + 1) Y` and hence `Δ = 4a + 3 + a²`
  multiples of `3` (`Delta_three`). So `Df = 1 + Δ I² ≡ 1` and, as `Q = Δ · strong ≡ 0`,
  `δ Cy = (Q − 1)(Q V² − 1) ≡ 1 (mod 3)` (`Df_mod`, `Da_mod`).
* **`S ≠ 0`.** Where `S = 0` the output is `ζ⁸`, so `ζ = 0`; then `0 ∣ Ac`, against
  `P138NoRoot.Ac_ne`.
* **The radicands are pairwise distinct** (`radA_ne_radB`, `radA_ne_radG`, `radB_ne_radG`):
  after cancelling `S²`, an equality would read `9 Df = δ Cy`, `Df = 9 Dt Dg` or
  `δ Cy = 81 Dt Dg`, each with one side `≡ 0` and the other `≡ 1 (mod 3)`.
* **`ζ ≠ 0`.** Where `ζ = 0` the output is `(S⁴ ((9Df − δCy − 81DtDg)² − 324 δCy·DtDg))²`; the
  inner bracket is `≡ 1 (mod 3)`.
* **The three roots** (`roots`). `ZRowsThreeRoot.three_squares` makes the radicands
  `(3S)² Df`, `S² δCy`, `(9S)² DtDg` squares; `b² ∣ a² ⇒ b ∣ a` strips the square factors, so
  `Df`, `δ Cy` and `Dt Dg` are squares, and the three roots of the radicands are multiples of
  `S`. One of the eight conjugates vanishes, so `S ∣ ζ` (`dvd_of_norm3_squares`), and `S ∣ Ac`.
* **The guard** (`guard`). `Dt` and `Dg = 1 + (3 Budget − 4) Dt s²` are coprime and
  `Dt ≥ 1`, so `Dt` is a square. `Budget ≤ 0` would make `Dg ≤ −3` and the square `Dt Dg`
  negative; hence `Budget > 0`, which gives `c ≠ 0` (`P138Budget.c_ne`), `I = r c² ≠ 0` and
  `Q = Δ² I² > 1`.
* **The descent** (`descent`). `δ Cy = e²` with `Q > 1` gives the integral auxiliary ordinate:
  `Q V² − (Q − 1) y² = 1` (`ZRowsStrongFold.adjacent_descent`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P125Roots
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P138Value P138Ports P138Bootstrap P138Adjacent
open P125Value (back tail outK Dg)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A multiple of `3` is neither `1` nor `−1`. -/
theorem three_mul (w : DiffRing V) : 3 * w ≠ 1 ∧ 3 * w ≠ -1 := by
  rcases int_split w with h | h
  · rcases eq_or_lt_of_le h with h1 | h1
    · constructor <;> intro h2 <;> rw [← h1, mul_zero] at h2 <;> linarith
    · have := one_le_of_pos' h1
      constructor <;> intro h2 <;> linarith
  · constructor <;> intro h2 <;> linarith

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V) (κ ζ : DiffRing V)
local notation "𝓡" => regsK p x κ
local notation "𝓑" => back p x κ
local notation "𝓣" => tail p x κ ζ

/-! ## Residues modulo 3 -/

theorem Delta_three (hp : PortFacts p) : ∃ d : DiffRing V, (𝓡).Delta = 3 * d := by
  obtain ⟨_, m, hm⟩ := X_mod p x κ hp
  refine ⟨4 * (m + 1) * (𝓡).Y + 1 + 3 * (m + 1) ^ 2 * (𝓡).Y ^ 2, ?_⟩
  rw [Delta_def, H_def, a_eq, hm]; ring

theorem Df_mod (hp : PortFacts p) : ∃ t : DiffRing V, (𝓑).Df = 3 * t + 1 := by
  obtain ⟨d, hd⟩ := Delta_three p x κ hp
  exact ⟨d * (𝓑).I ^ 2, by rw [P125Value.Df_eq, hd]; ring⟩

theorem Da_mod (hp : PortFacts p) : ∃ t : DiffRing V, (𝓑).delta * (𝓑).Cy = 3 * t + 1 := by
  obtain ⟨d, hd⟩ := Delta_three p x κ hp
  refine ⟨3 * (d * (𝓑).strong) ^ 2 * (𝓑).V ^ 2 - d * (𝓑).strong -
    d * (𝓑).strong * (𝓑).V ^ 2, ?_⟩
  rw [P125Value.delta_def, P125Value.Cy_eq, P125Value.Q_def, hd]; ring

/-! ## At a zero: `S ≠ 0`, distinct radicands, `ζ ≠ 0` -/

theorem S_ne (hz : outK p x κ ζ = 0) (hζ : (𝓡).S ∣ ζ + (𝓡).Ac) : (𝓡).S ≠ 0 := by
  intro hS
  rw [P125Value.out_S_zero p x κ ζ hS] at hz
  have h0 : ζ = 0 := (pow_eq_zero_iff (n := 8) (by norm_num)).mp hz
  rw [hS, h0, zero_add] at hζ
  exact P138NoRoot.Ac_ne p x κ (zero_dvd_iff.mp hζ)

theorem s_r_ne (hz : outK p x κ ζ = 0) (hζ : (𝓡).S ∣ ζ + (𝓡).Ac) : x 10 ≠ 0 ∧ x 4 ≠ 0 := by
  have h := S_ne p x κ ζ hz hζ
  rw [S_eq] at h
  exact ⟨fun h0 => h (by rw [h0]; ring), fun h0 => h (by rw [h0]; ring)⟩

theorem radA_ne_radB (hp : PortFacts p) (hS : (𝓡).S ≠ 0) : (𝓣).A ≠ (𝓣).B := by
  intro h
  obtain ⟨t, ht⟩ := Da_mod p x κ hp
  rw [P125Value.radA_eq, P125Value.radB_eq, ht] at h
  have h1 : (𝓡).S ^ 2 * (3 * (3 * (𝓑).Df - t)) = (𝓡).S ^ 2 * 1 := by linear_combination h
  exact (three_mul _).1 (mul_left_cancel₀ (pow_ne_zero 2 hS) h1)

theorem radA_ne_radG (hp : PortFacts p) (hS : (𝓡).S ≠ 0) : (𝓣).A ≠ (𝓣).G := by
  intro h
  obtain ⟨t, ht⟩ := Df_mod p x κ hp
  rw [P125Value.radA_eq, P125Value.radG_eq, ht] at h
  have h1 : (9 * (𝓡).S ^ 2) * (3 * (3 * ((𝓡).Dt * Dg p x κ) - t)) = (9 * (𝓡).S ^ 2) * 1 := by
    linear_combination -h
  exact (three_mul _).1
    (mul_left_cancel₀ (mul_ne_zero (by norm_num) (pow_ne_zero 2 hS)) h1)

theorem radB_ne_radG (hp : PortFacts p) (hS : (𝓡).S ≠ 0) : (𝓣).B ≠ (𝓣).G := by
  intro h
  obtain ⟨t, ht⟩ := Da_mod p x κ hp
  rw [P125Value.radB_eq, P125Value.radG_eq, ht] at h
  have h1 : (𝓡).S ^ 2 * (3 * (27 * ((𝓡).Dt * Dg p x κ) - t)) = (𝓡).S ^ 2 * 1 := by
    linear_combination -h
  exact (three_mul _).1 (mul_left_cancel₀ (pow_ne_zero 2 hS) h1)

theorem slot_ne (hp : PortFacts p) (hz : outK p x κ ζ = 0) (hζ : (𝓡).S ∣ ζ + (𝓡).Ac) :
    ζ ≠ 0 := by
  intro h0
  have hS := S_ne p x κ ζ hz hζ
  have hz0 := hz
  rw [h0, P125Value.out_slot_zero] at hz0
  have h1 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp hz0
  have h2 := (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 4 hS)
  obtain ⟨t, ht⟩ := Da_mod p x κ hp
  rw [ht] at h2
  apply (three_mul (3 * (3 * (𝓑).Df - 27 * ((𝓡).Dt * Dg p x κ) - t) ^ 2 -
    2 * (3 * (𝓑).Df - 27 * ((𝓡).Dt * Dg p x κ) - t) -
    108 * ((3 * t + 1) * ((𝓡).Dt * Dg p x κ)))).2
  linear_combination h2

/-! ## The three roots -/

/-- **The three roots**: `Df`, `δ · Cy` and `Dt · Dg` are squares, and `S` divides the slot. -/
theorem roots (hp : PortFacts p) (hz : outK p x κ ζ = 0) (hζ : (𝓡).S ∣ ζ + (𝓡).Ac) :
    ∃ f e g : DiffRing V, (𝓑).Df = f * f ∧ (𝓑).delta * (𝓑).Cy = e * e ∧
      (𝓡).Dt * Dg p x κ = g * g ∧ (𝓡).S ∣ ζ := by
  have hS := S_ne p x κ ζ hz hζ
  have hZ := slot_ne p x κ ζ hp hz hζ
  have h0 := hz
  rw [P125Value.out_eq] at h0
  obtain ⟨⟨t1, ht1⟩, ⟨t2, ht2⟩, ⟨t3, ht3⟩⟩ := ZRowsThreeRoot.three_squares h0 hZ
    (radA_ne_radB p x κ ζ hp hS) (radA_ne_radG p x κ ζ hp hS) (radB_ne_radG p x κ ζ hp hS)
  have hn : ZRowsThreeRoot.norm3 ζ (t1 ^ 2) (t2 ^ 2) (t3 ^ 2) = 0 := by
    rw [pow_two, pow_two, pow_two, ← ht1, ← ht2, ← ht3]; exact h0
  have h3S : 3 * (𝓡).S ≠ 0 := mul_ne_zero (by norm_num) hS
  have h9S : 9 * (𝓡).S ≠ 0 := mul_ne_zero (by norm_num) hS
  obtain ⟨f, hf⟩ : 3 * (𝓡).S ∣ t1 :=
    dvd_of_sq_dvd_sq_ring ⟨(𝓑).Df, by rw [← ht1, P125Value.radA_eq]; ring⟩
  obtain ⟨e, he⟩ : (𝓡).S ∣ t2 :=
    dvd_of_sq_dvd_sq_ring ⟨(𝓑).delta * (𝓑).Cy, by rw [← ht2, P125Value.radB_eq]; ring⟩
  obtain ⟨g, hg⟩ : 9 * (𝓡).S ∣ t3 :=
    dvd_of_sq_dvd_sq_ring ⟨(𝓡).Dt * Dg p x κ, by rw [← ht3, P125Value.radG_eq]; ring⟩
  refine ⟨f, e, g, ?_, ?_, ?_, ?_⟩
  · apply mul_left_cancel₀ (mul_ne_zero h3S h3S)
    rw [P125Value.radA_eq, hf] at ht1
    linear_combination ht1
  · apply mul_left_cancel₀ (mul_ne_zero hS hS)
    rw [P125Value.radB_eq, he] at ht2
    linear_combination ht2
  · apply mul_left_cancel₀ (mul_ne_zero h9S h9S)
    rw [P125Value.radG_eq, hg] at ht3
    linear_combination ht3
  · exact ZRowsThreeRoot.dvd_of_norm3_squares ⟨3 * f, by rw [hf]; ring⟩ ⟨e, he⟩
      ⟨9 * g, by rw [hg]; ring⟩ hn

theorem S_dvd_Ac (hp : PortFacts p) (hz : outK p x κ ζ = 0) (hζ : (𝓡).S ∣ ζ + (𝓡).Ac) :
    (𝓡).S ∣ (𝓡).Ac := by
  obtain ⟨_, _, _, _, _, _, hS⟩ := roots p x κ ζ hp hz hζ
  exact (dvd_add_right hS).mp hζ

/-- **The positive root of `Df`.** -/
theorem Df_root (hp : PortFacts p) (hz : outK p x κ ζ = 0) (hζ : (𝓡).S ∣ ζ + (𝓡).Ac) :
    ∃ f : V, 0 < f ∧ (𝓑).Df = ι f * ι f := by
  obtain ⟨w, _, _, hw, _, _, _⟩ := roots p x κ ζ hp hz hζ
  obtain ⟨f, hf⟩ := abs_eq_ι w
  have hff : (𝓑).Df = ι f * ι f := by rw [← hf, abs_mul_abs_self, hw]
  refine ⟨f, ?_, hff⟩
  rcases eq_zero_or_pos f with h0 | h0
  · exfalso
    rw [h0, map_zero, mul_zero] at hff
    obtain ⟨t, ht⟩ := Df_mod p x κ hp
    rw [hff] at ht
    exact (three_mul t).2 (by linear_combination -ht)
  · exact h0

/-! ## The guard, the budget and `Q > 1` -/

/-- **`Dt` is a square and `Budget > 0`.** -/
theorem guard (hp : PortFacts p) (hz : outK p x κ ζ = 0) (hζ : (𝓡).S ∣ ζ + (𝓡).Ac) :
    (∃ τ : V, (𝓡).Dt = ι τ * ι τ) ∧ 0 < (𝓡).Budget := by
  obtain ⟨_, _, g, _, _, hg, _⟩ := roots p x κ ζ hp hz hζ
  obtain ⟨hs, _⟩ := s_r_ne p x κ ζ hz hζ
  obtain ⟨hDt, _⟩ := Dt_facts p x κ hp
  have hcop : ∃ α β, (𝓡).Dt * α + Dg p x κ * β = 1 :=
    ⟨-((3 * (𝓡).Budget - 4) * x 10 ^ 2), 1, by rw [P125Value.Dg_def]; ring⟩
  obtain ⟨⟨τ, hτ⟩, _⟩ := abs_squares_of_mul_square hcop hg
  rw [abs_of_pos (show (0 : DiffRing V) < (𝓡).Dt by linarith)] at hτ
  refine ⟨⟨τ, hτ⟩, ?_⟩
  by_contra hlt
  have hB : (𝓡).Budget ≤ 0 := not_lt.mp hlt
  have hs2 : 1 ≤ x 10 ^ 2 := by have := one_le_abs hs; rw [← sq_abs]; nlinarith
  have hD : 3 * (𝓡).Budget - 4 ≤ -4 := by linarith
  have h1 : (3 * (𝓡).Budget - 4) * (𝓡).Dt ≤ -4 := by nlinarith
  have h2 : (3 * (𝓡).Budget - 4) * (𝓡).Dt * x 10 ^ 2 ≤ -4 := by nlinarith
  have hDg : Dg p x κ ≤ -3 := by rw [P125Value.Dg_def]; linarith
  have h3 : (𝓡).Dt * Dg p x κ < 0 := by nlinarith
  have h4 : 0 ≤ g * g := mul_self_nonneg g
  rw [hg] at h3
  linarith

theorem I_ne (hp : PortFacts p) (hz : outK p x κ ζ = 0) (hζ : (𝓡).S ∣ ζ + (𝓡).Ac) :
    (𝓑).I ≠ 0 := by
  obtain ⟨_, hB⟩ := guard p x κ ζ hp hz hζ
  rw [P125Value.I_eq]
  exact mul_ne_zero (s_r_ne p x κ ζ hz hζ).2 (pow_ne_zero 2 (P138Budget.c_ne p x κ hp hB))

theorem Q_gt (hp : PortFacts p) (hz : outK p x κ ζ = 0) (hζ : (𝓡).S ∣ ζ + (𝓡).Ac) :
    1 < (𝓑).Q := by
  have hD := Delta_gt p x κ hp
  have hI1 : 1 ≤ (𝓑).I ^ 2 := by
    have := one_le_abs (I_ne p x κ ζ hp hz hζ); rw [← sq_abs]; nlinarith
  have hD2 : 64 ≤ (𝓡).Delta ^ 2 := by nlinarith
  have h1 : 64 * 1 ≤ (𝓡).Delta ^ 2 * (𝓑).I ^ 2 :=
    mul_le_mul hD2 hI1 (by norm_num) (by positivity)
  rw [P125Value.Q_eq]
  linarith

/-! ## The descent -/

/-- **The auxiliary ordinate is integral.** -/
theorem descent (hp : PortFacts p) (hz : outK p x κ ζ = 0) (hζ : (𝓡).S ∣ ζ + (𝓡).Ac) :
    ∃ y : V, 0 < y ∧ (𝓑).Q * (𝓑).V ^ 2 - ((𝓑).Q - 1) * (ι y) ^ 2 = 1 := by
  obtain ⟨_, w, _, _, hw, _, _⟩ := roots p x κ ζ hp hz hζ
  obtain ⟨e, he⟩ := abs_eq_ι w
  have hww : (𝓑).delta * (𝓑).Cy = ι e * ι e := by rw [← he, abs_mul_abs_self, hw]
  have he0 : 0 < e := by
    rcases eq_zero_or_pos e with h0 | h0
    · exfalso
      rw [h0, map_zero, mul_zero] at hww
      obtain ⟨t, ht⟩ := Da_mod p x κ hp
      rw [hww] at ht
      exact (three_mul t).2 (by linear_combination -ht)
    · exact h0
  have hQ := Q_gt p x κ ζ hp hz hζ
  obtain ⟨y, hy0, _, haux⟩ := ZRowsStrongFold.adjacent_descent (Vr := (𝓑).V) hQ he0
    (by rw [← hww, P125Value.delta_def, P125Value.Cy_eq])
  exact ⟨y, hy0, haux⟩

end Regs

#print axioms three_mul
#print axioms Da_mod
#print axioms slot_ne
#print axioms roots
#print axioms S_dvd_Ac
#print axioms Df_root
#print axioms guard
#print axioms Q_gt
#print axioms descent

end DiophantineConsistency.P125Roots
