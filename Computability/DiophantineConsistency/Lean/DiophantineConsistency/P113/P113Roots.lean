import DiophantineConsistency.P113.P113Front
import DiophantineConsistency.P125.P125Roots
import DiophantineConsistency.Z10.Z10Squares

/-! # The three roots of package 113's equation

At a zero of `P113Value.value p x` in the ring of differences of a model of `𝗜𝚺₁`, with the
port facts of package 138 (`P138Ports.PortFacts`). `PROOF.md` §3–§4, in integers only:

* **Residues modulo 3** (`Delta_three`, `E_mod`, `Df_mod`, `Da_mod`). `X ≡ 2` gives `3 ∣ Δ`, and
  `ℓ(ℓ + 1) ≡ 0` for `ℓ = X Y²`, so `E ≡ Df ≡ 1`, `Q ≡ 0` and `δ Cy ≡ 1 (mod 3)`; in particular
  `δ = Q − 1 ≠ 0` (`delta_ne`).
* **The scaled norm.** `δ⁴ · value = N(δZ; x, y, z)` with `x = δ fc = S² δCy`,
  `y = δ fa = (3δS)² E Df`, `z = δ fb = (9δS)² Dg` (`P113Value.value_scale`), where
  `Dg = (3 Pair − 4) s² + 1`.
* **`S ≠ 0`.** Where `S = 0` the scaled norm is `(δZ)⁸` and `Z = −Ac ≠ 0`.
* **Distinct radicands and `δZ ≠ 0`**, by cancelling `S²` (and `δ²`, `9`) and reducing mod 3.
* **The three roots** (`roots`). `ZRowsThreeRoot.three_squares`, the adjacent descent
  (`δ Cy = e²` gives `Q V² − (Q − 1) y² = 1`, so `x = (S δ y)²`), and `dvd_of_norm3_squares`
  with the common divisor `δS`: `E Df` and `Dg` are squares and `S ∣ Ac`.
* **The saturation split** (`saturation`). `Df = 1 + Δ U² E` makes `E` and `Df` coprime, so
  both are squares.
* **The guard** (`guard`). `Dg ≥ 0` and `s ≠ 0` force `Pair > 0`, hence `G > 0` and `η ζ > 0`.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P113Roots
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P138Ports P138Bootstrap P113Front
open P125Roots (three_mul)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Every element of the ring of differences is `0`, `1` or `2` modulo `3`. -/
theorem mod3' (u : DiffRing V) : ∃ t : DiffRing V, u = 3 * t ∨ u = 3 * t + 1 ∨ u = 3 * t + 2 := by
  rcases nonneg_or_nonpos u with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · obtain ⟨t, h | h | h⟩ := Z10Squares.mod3_split a
    · exact ⟨ι t, Or.inl (by rw [h]; simp only [map_mul, map_ofNat])⟩
    · exact ⟨ι t, Or.inr (Or.inl (by rw [h]; simp only [map_add, map_mul, map_ofNat, map_one]))⟩
    · exact ⟨ι t, Or.inr (Or.inr (by rw [h]; simp only [map_add, map_mul, map_ofNat]))⟩
  · obtain ⟨t, h | h | h⟩ := Z10Squares.mod3_split a
    · exact ⟨-ι t, Or.inl (by rw [h]; simp only [map_mul, map_ofNat]; ring)⟩
    · exact ⟨-ι t - 1, Or.inr (Or.inr (by
        rw [h]; simp only [map_add, map_mul, map_ofNat, map_one]; ring))⟩
    · exact ⟨-ι t - 1, Or.inr (Or.inl (by rw [h]; simp only [map_add, map_mul, map_ofNat]; ring))⟩

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 12 → DiffRing V)
local notation "𝓠" => P113Value.regs p x

/-! ## Residues modulo 3 -/

theorem X_three (hp : PortFacts p) : ∃ m : DiffRing V, (𝓠).X = 3 * m + 2 := by
  obtain ⟨_, m, hm⟩ := X_mod p (front x) (kk p x) hp
  exact ⟨m, by rw [X_eq, hm]⟩

theorem Delta_three (hp : PortFacts p) : ∃ d : DiffRing V, (𝓠).Delta = 3 * d := by
  obtain ⟨d, hd⟩ := P125Roots.Delta_three p (front x) (kk p x) hp
  exact ⟨d, by rw [Delta_eq, hd]⟩

theorem ell_three (hp : PortFacts p) : ∃ w : DiffRing V, (𝓠).ell * ((𝓠).ell + 1) = 3 * w := by
  obtain ⟨m, hm⟩ := X_three p x hp
  rw [P113Value.ell_def, hm]
  obtain ⟨t, ht | ht | ht⟩ := mod3' (𝓠).Y
  · exact ⟨(3 * m + 2) * (3 * t * t) * ((3 * m + 2) * (3 * t) * (3 * t) + 1), by rw [ht]; ring⟩
  · refine ⟨(3 * m + 2) * (3 * t + 1) * (3 * t + 1) *
      ((3 * m + 2) * (3 * t * t + 2 * t) + m + 1), ?_⟩
    rw [ht]; ring
  · refine ⟨(3 * m + 2) * (3 * t + 2) * (3 * t + 2) *
      ((3 * m + 2) * (3 * t * t + 4 * t + 1) + m + 1), ?_⟩
    rw [ht]; ring

theorem E_mod (hp : PortFacts p) : ∃ t : DiffRing V, (𝓠).E = 3 * t + 1 := by
  obtain ⟨w, hw⟩ := ell_three p x hp
  exact ⟨w * ((𝓠).k * (𝓠).k), by rw [P113Value.E_def, hw]; ring⟩

theorem Q_three (hp : PortFacts p) : ∃ t : DiffRing V, (𝓠).Q = 3 * t := by
  obtain ⟨d, hd⟩ := Delta_three p x hp
  exact ⟨d * (𝓠).Delta * ((𝓠).U * (𝓠).U) * (𝓠).E, by rw [P113Value.Q_def, hd]; ring⟩

theorem Df_mod (hp : PortFacts p) : ∃ t : DiffRing V, (𝓠).Df = 3 * t + 1 := by
  obtain ⟨d, hd⟩ := Delta_three p x hp
  exact ⟨d * ((𝓠).U * (𝓠).U) * (𝓠).E, by rw [P113Value.Df_def, hd]; ring⟩

theorem Da_mod (hp : PortFacts p) : ∃ t : DiffRing V, (𝓠).delta * (𝓠).Cy = 3 * t + 1 := by
  obtain ⟨t, ht⟩ := Q_three p x hp
  refine ⟨3 * t * t * ((𝓠).V * (𝓠).V) - t - t * ((𝓠).V * (𝓠).V), ?_⟩
  rw [P113Value.delta_def, P113Value.Cy_def, ht]; ring

theorem delta_ne (hp : PortFacts p) : (𝓠).delta ≠ 0 := by
  obtain ⟨t, ht⟩ := Q_three p x hp
  intro h
  rw [P113Value.delta_def, ht] at h
  exact (three_mul t).1 (by linear_combination h)

/-! ## The scaled norm at a zero -/

/-- The weighted guard is `81 Dg`. -/
theorem Dg81_eq : (𝓠).Dg81 = 81 * ((3 * (𝓠).Pair - 4) * (x 11 * x 11) + 1) := by
  rw [P113Value.Dg81_def]; ring

theorem rad_x : (𝓠).delta * (𝓠).fc = (𝓠).S ^ 2 * ((𝓠).delta * (𝓠).Cy) := by
  rw [P113Value.fc_def]; ring

theorem rad_y : (𝓠).delta * (𝓠).fa =
    (3 * (𝓠).delta * (𝓠).S) ^ 2 * ((𝓠).E * (𝓠).Df) := by
  rw [P113Value.fa_def]; ring

theorem rad_z : (𝓠).delta * (𝓠).fb =
    (9 * (𝓠).delta * (𝓠).S) ^ 2 * ((3 * (𝓠).Pair - 4) * (x 11 * x 11) + 1) := by
  rw [P113Value.fb_def, Dg81_eq]; ring

theorem norm_zero (hz : P113Value.value p x = 0) :
    ZRowsThreeRoot.norm3 ((𝓠).delta * (𝓠).Z) ((𝓠).delta * (𝓠).fc) ((𝓠).delta * (𝓠).fa)
      ((𝓠).delta * (𝓠).fb) = 0 := by
  rw [← P113Value.value_scale, hz, mul_zero]

theorem Ac_ne : (𝓠).Ac ≠ 0 := by
  have hH : (𝓠).H ≠ 0 := by rw [H_eq]; exact H_ne p (front x) (kk p x)
  rw [P113Value.Ac_def]
  refine mul_ne_zero ?_ (sub_ne_zero.mpr (P138NoRoot.no_cube_19 hH))
  have h1 : 0 < (𝓠).H * (𝓠).H := mul_self_pos.mpr hH
  have h2 := mul_self_nonneg (𝓠).zc
  exact ne_of_gt (by linarith)

theorem S_ne (hp : PortFacts p) (hz : P113Value.value p x = 0) : (𝓠).S ≠ 0 := by
  intro hS
  have h := norm_zero p x hz
  rw [P113Value.fc_def, P113Value.fa_def, P113Value.fb_def, hS] at h
  simp only [mul_zero, zero_mul, ZRowsThreeRoot.norm3_zero_radicands] at h
  have h0 : (𝓠).delta * (𝓠).Z = 0 := (pow_eq_zero_iff (n := 8) (by norm_num)).mp h
  have hZ := (mul_eq_zero.mp h0).resolve_left (delta_ne p x hp)
  rw [P113Value.Z_def, hS, zero_mul, _root_.zero_sub, neg_eq_zero] at hZ
  exact Ac_ne p x hZ

theorem U_ne (hp : PortFacts p) (hz : P113Value.value p x = 0) : (𝓠).U ≠ 0 := by
  intro hU
  apply S_ne p x hp hz
  rw [P113Value.S_def, hU, zero_mul]

theorem srcne (hp : PortFacts p) (hz : P113Value.value p x = 0) :
    x 11 ≠ 0 ∧ x 4 ≠ 0 ∧ x 8 ≠ 0 := by
  have h := U_ne p x hp hz
  rw [P113Value.U_def] at h
  refine ⟨fun h0 => h (by rw [h0]; ring), fun h0 => h (by rw [h0]; ring),
    fun h0 => h (by rw [h0]; ring)⟩

theorem x_ne_y (hp : PortFacts p) (hS : (𝓠).S ≠ 0) :
    (𝓠).delta * (𝓠).fc ≠ (𝓠).delta * (𝓠).fa := by
  intro h
  obtain ⟨t, ht⟩ := Da_mod p x hp
  rw [rad_x, rad_y, ht] at h
  have h1 : (𝓠).S ^ 2 * (3 * (3 * (𝓠).delta ^ 2 * ((𝓠).E * (𝓠).Df) - t)) = (𝓠).S ^ 2 * 1 := by
    linear_combination -h
  exact (three_mul _).1 (mul_left_cancel₀ (pow_ne_zero 2 hS) h1)

theorem x_ne_z (hp : PortFacts p) (hS : (𝓠).S ≠ 0) :
    (𝓠).delta * (𝓠).fc ≠ (𝓠).delta * (𝓠).fb := by
  intro h
  obtain ⟨t, ht⟩ := Da_mod p x hp
  rw [rad_x, rad_z, ht] at h
  have h1 : (𝓠).S ^ 2 * (3 * (27 * (𝓠).delta ^ 2 *
      ((3 * (𝓠).Pair - 4) * (x 11 * x 11) + 1) - t)) = (𝓠).S ^ 2 * 1 := by
    linear_combination -h
  exact (three_mul _).1 (mul_left_cancel₀ (pow_ne_zero 2 hS) h1)

theorem y_ne_z (hp : PortFacts p) (hS : (𝓠).S ≠ 0) :
    (𝓠).delta * (𝓠).fa ≠ (𝓠).delta * (𝓠).fb := by
  intro h
  obtain ⟨t, ht⟩ := E_mod p x hp
  obtain ⟨u, hu⟩ := Df_mod p x hp
  rw [rad_y, rad_z, ht, hu] at h
  have hc : (9 * (𝓠).delta * (𝓠).S) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (by norm_num) (delta_ne p x hp)) hS)
  have h1 : (9 * (𝓠).delta * (𝓠).S) ^ 2 * (3 * (3 * t * u + t + u -
      3 * ((3 * (𝓠).Pair - 4) * (x 11 * x 11) + 1))) = (9 * (𝓠).delta * (𝓠).S) ^ 2 * (-1) := by
    linear_combination 9 * h
  exact (three_mul _).2 (mul_left_cancel₀ hc h1)

theorem dZ_ne (hp : PortFacts p) (hz : P113Value.value p x = 0) : (𝓠).delta * (𝓠).Z ≠ 0 := by
  intro h0
  have hS := S_ne p x hp hz
  have h := norm_zero p x hz
  rw [h0, ZRowsThreeRoot.norm3_zero_slot, rad_x, rad_y, rad_z] at h
  have h1 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h
  obtain ⟨t, ht⟩ := Da_mod p x hp
  rw [ht] at h1
  set D := (3 * (𝓠).Pair - 4) * (x 11 * x 11) + 1
  set e := (𝓠).delta
  set W := (𝓠).E * (𝓠).Df
  have h2 : (𝓠).S ^ 4 * ((3 * t + 1 - 9 * e ^ 2 * W - 81 * e ^ 2 * D) ^ 2 -
      4 * (9 * e ^ 2 * W) * (81 * e ^ 2 * D)) = 0 := by linear_combination h1
  have h3 := (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 4 hS)
  apply (three_mul ((3 * (t - 3 * e ^ 2 * W - 27 * e ^ 2 * D) + 2) * (t - 3 * e ^ 2 * W -
    27 * e ^ 2 * D) - 4 * 3 * e ^ 2 * W * 81 * e ^ 2 * D)).2
  linear_combination h3

/-! ## The three roots -/

theorem Q_gt (hp : PortFacts p) (hz : P113Value.value p x = 0) : 1 < (𝓠).Q := by
  have hD : 8 ≤ (𝓠).Delta := by rw [Delta_eq]; exact Delta_gt p (front x) (kk p x) hp
  have hE : 1 ≤ (𝓠).E := by rw [← Dt_eq]; exact (Dt_facts p (front x) (kk p x) hp).1
  have hU : 1 ≤ (𝓠).U * (𝓠).U := by
    have := one_le_abs (U_ne p x hp hz); rw [← abs_mul_abs_self]; nlinarith
  have h1 : 64 ≤ (𝓠).Delta * (𝓠).Delta := by nlinarith
  have h2 : 64 * 1 ≤ (𝓠).Delta * (𝓠).Delta * ((𝓠).U * (𝓠).U) := mul_le_mul h1 hU (by norm_num)
    (by nlinarith)
  rw [P113Value.Q_def]
  nlinarith

/-- **The three roots**: the auxiliary descent, `E Df = h²`, `Dg = g²` and `S ∣ Ac`. -/
theorem roots (hp : PortFacts p) (hz : P113Value.value p x = 0) :
    ∃ (y : V) (h g : DiffRing V), 0 < y ∧
      (𝓠).Q * (𝓠).V ^ 2 - ((𝓠).Q - 1) * (ι y) ^ 2 = 1 ∧
      (𝓠).E * (𝓠).Df = h * h ∧ (3 * (𝓠).Pair - 4) * (x 11 * x 11) + 1 = g * g ∧
      (𝓠).S ∣ (𝓠).Ac := by
  have hS := S_ne p x hp hz
  have hδ := delta_ne p x hp
  have h0 := norm_zero p x hz
  obtain ⟨⟨t1, ht1⟩, ⟨t2, ht2⟩, ⟨t3, ht3⟩⟩ := ZRowsThreeRoot.three_squares h0 (dZ_ne p x hp hz)
    (x_ne_y p x hp hS) (x_ne_z p x hp hS) (y_ne_z p x hp hS)
  -- the auxiliary root
  obtain ⟨e0, he0⟩ : (𝓠).S ∣ t1 :=
    dvd_of_sq_dvd_sq_ring ⟨(𝓠).delta * (𝓠).Cy, by rw [← ht1, rad_x]; ring⟩
  have hDa : (𝓠).delta * (𝓠).Cy = e0 * e0 := by
    apply mul_left_cancel₀ (mul_ne_zero hS hS)
    rw [rad_x, he0] at ht1
    linear_combination ht1
  obtain ⟨e, he⟩ := abs_eq_ι e0
  have hee : (𝓠).delta * (𝓠).Cy = ι e * ι e := by rw [← he, abs_mul_abs_self, hDa]
  have he_pos : 0 < e := by
    rcases eq_zero_or_pos e with h | h
    · exfalso
      rw [h, map_zero, mul_zero] at hee
      obtain ⟨t, ht⟩ := Da_mod p x hp
      rw [hee] at ht
      exact (three_mul t).2 (by linear_combination -ht)
    · exact h
  obtain ⟨y, hy0, hey, haux⟩ := ZRowsStrongFold.adjacent_descent (Vr := (𝓠).V)
    (Q_gt p x hp hz) he_pos (by rw [← hee, P113Value.delta_def, P113Value.Cy_def]; ring)
  have hCy : (𝓠).Cy = (𝓠).delta * (ι y) ^ 2 := by
    rw [P113Value.Cy_def, P113Value.delta_def]; linear_combination haux
  -- the other two roots
  have h3 : 3 * (𝓠).delta * (𝓠).S ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hδ) hS
  have h9 : 9 * (𝓠).delta * (𝓠).S ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hδ) hS
  obtain ⟨h, hh⟩ : 3 * (𝓠).delta * (𝓠).S ∣ t2 :=
    dvd_of_sq_dvd_sq_ring ⟨(𝓠).E * (𝓠).Df, by rw [← ht2, rad_y]; ring⟩
  obtain ⟨g, hg⟩ : 9 * (𝓠).delta * (𝓠).S ∣ t3 :=
    dvd_of_sq_dvd_sq_ring ⟨(3 * (𝓠).Pair - 4) * (x 11 * x 11) + 1, by rw [← ht3, rad_z]; ring⟩
  refine ⟨y, h, g, hy0, haux, ?_, ?_, ?_⟩
  · apply mul_left_cancel₀ (mul_ne_zero h3 h3)
    rw [rad_y, hh] at ht2
    linear_combination ht2
  · apply mul_left_cancel₀ (mul_ne_zero h9 h9)
    rw [rad_z, hg] at ht3
    linear_combination ht3
  · -- the linear relation with the common divisor `δS`
    have hn : ZRowsThreeRoot.norm3 ((𝓠).delta * (𝓠).Z) (((𝓠).S * (𝓠).delta * ι y) ^ 2)
        ((3 * (𝓠).delta * (𝓠).S * h) ^ 2) ((9 * (𝓠).delta * (𝓠).S * g) ^ 2) = 0 := by
      have ex : ((𝓠).S * (𝓠).delta * ι y) ^ 2 = (𝓠).delta * (𝓠).fc := by
        rw [rad_x, hCy]; ring
      have ey : (3 * (𝓠).delta * (𝓠).S * h) ^ 2 = (𝓠).delta * (𝓠).fa := by
        rw [ht2, hh]; ring
      have ez : (9 * (𝓠).delta * (𝓠).S * g) ^ 2 = (𝓠).delta * (𝓠).fb := by
        rw [ht3, hg]; ring
      rw [ex, ey, ez]; exact h0
    obtain ⟨w, hw⟩ := ZRowsThreeRoot.dvd_of_norm3_squares (S := (𝓠).delta * (𝓠).S)
      ⟨ι y, by ring⟩ ⟨3 * h, by ring⟩ ⟨9 * g, by ring⟩ hn
    have hZ : (𝓠).Z = (𝓠).S * w := by
      apply mul_left_cancel₀ hδ; linear_combination hw
    refine ⟨x 9 + (𝓠).V - w, ?_⟩
    have := P113Value.Z_def p x
    linear_combination this - hZ

/-! ## The saturation split and the guard -/

/-- **The saturation split**: `E` and `Df` are squares of positive naturals. -/
theorem saturation (hp : PortFacts p) (hz : P113Value.value p x = 0) :
    ∃ τ f : V, (𝓠).E = ι τ * ι τ ∧ (𝓠).Df = ι f * ι f := by
  obtain ⟨_, h, _, _, _, hh, _, _⟩ := roots p x hp hz
  have hcop : ∃ α β, (𝓠).E * α + (𝓠).Df * β = 1 :=
    ⟨-((𝓠).Delta * ((𝓠).U * (𝓠).U)), 1, by rw [P113Value.Df_def]; ring⟩
  obtain ⟨⟨τ, hτ⟩, ⟨f, hf⟩⟩ := abs_squares_of_mul_square hcop hh
  have hE : 0 < (𝓠).E := by
    have := (Dt_facts p (front x) (kk p x) hp).1; rw [Dt_eq] at this; linarith
  have hDf : 0 < (𝓠).Df := by
    have hE1 : 0 ≤ (𝓠).E := hE.le
    have hD : 0 ≤ (𝓠).Delta := by
      have := Delta_gt p (front x) (kk p x) hp; rw [← Delta_eq] at this; linarith
    rw [P113Value.Df_def]
    have := mul_nonneg (mul_nonneg hD (mul_self_nonneg (𝓠).U)) hE1
    linarith
  rw [abs_of_pos hE] at hτ
  rw [abs_of_pos hDf] at hf
  exact ⟨τ, f, hτ, hf⟩

/-- **The guard**: `Pair > 0`, `G > 0` and `η ζ > 0`. -/
theorem guard (hp : PortFacts p) (hz : P113Value.value p x = 0) :
    0 < (𝓠).Pair ∧ 0 < (𝓠).G ∧ 0 < (𝓠).eta * (𝓠).zeta := by
  obtain ⟨_, _, g, _, _, _, hg, _⟩ := roots p x hp hz
  obtain ⟨hs, _, _⟩ := srcne p x hp hz
  have hs2 : 1 ≤ x 11 * x 11 := by
    have := one_le_abs hs; rw [← abs_mul_abs_self]; nlinarith
  have hP : 0 < (𝓠).Pair := by
    by_contra hle
    have hle' : (𝓠).Pair ≤ 0 := not_lt.mp hle
    have h1 : (3 * (𝓠).Pair - 4) * (x 11 * x 11) ≤ -4 := by nlinarith
    have h2 := mul_self_nonneg g
    linarith
  have hprod : 0 < (𝓠).G * ((𝓠).eta * (𝓠).zeta) := by
    have h := hP
    rw [P113Value.Pair_def] at h
    have := sq_nonneg (x 10 * x 10 - (𝓠).G - (𝓠).eta * (𝓠).zeta + 1)
    nlinarith
  rcases lt_or_gt_of_ne (show (𝓠).G ≠ 0 by intro h0; rw [h0, zero_mul] at hprod; exact lt_irrefl _ hprod)
    with hG | hG
  · exfalso
    have hez : (𝓠).eta * (𝓠).zeta < 0 := by nlinarith
    have h := hP
    rw [P113Value.Pair_def] at h
    have hx := mul_self_nonneg (x 10)
    nlinarith
  · exact ⟨hP, hG, by nlinarith⟩

end Regs

#print axioms roots
#print axioms saturation
#print axioms guard

end DiophantineConsistency.P113Roots
