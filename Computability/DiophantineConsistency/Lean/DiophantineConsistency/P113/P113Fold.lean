import DiophantineConsistency.P113.P113Roots
import DiophantineConsistency.P138.P138Rank

/-! # The folded front of package 113

A zero of `P113Value.value p x` (with package 138's port facts) gives the record `Folded113`:
package 138's folded front (`P138Rank.Folded`) for the front `regsK p (front x) k` at 113's native
index, with the budget replaced by the facts that the downstream chain actually reads, in the
weak form that package 113's guard supplies (`PROOF.md` §4 of the parent):

* **the signs** `0 < F q`, `0 < C q`, `0 < (q − F − C) q`, from the determinant `G > 0`
  (`signs_of_G`: with `A = cone_A F`, `B = cone_B C`, `G > 0` forces `AB > 0` and
  `2 |q − (A + B)| < |A + B|`; the cones are at least 4);
* **the weak window** `|k| (|Y| − 1) < |c| < |k| (|Y| + 1)`, `0 < c (k Y)`, `k ≠ 0`, from
  `η ζ > 0`, `ζ = k − η`, `c = η + Y k` (`window_of_ez`);
* `Dt = τ²` (`P113Roots.saturation`; 138's `Dt` is 113's `E`), `H ∣ Kq⁵` (from 113's
  `S = U H⁵ ∣ Ac`, `Ac ≡ zc⁵`, `zc ≡ K (mod H)`; 138's `Kq` is 113's `K`);
* the main Pell pair `|c| = ψ_b(R)`, `R` odd, `Dm = χ_b(R)²`, by `ZRowsStrongFold.strong_fold`
  with the strong pair `f² = 1 + Δ I₀²`, `I₀ = |s| |r| τ c²` (`I = U τ`), `Q = (Δ I₀)²`, the
  linear slot `V = f² b − c`, `b = c − R + 4 I (τ T)`, and the rank `b + R ≡ 0 (mod |c|)`.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P113Fold
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P138Value P138Ports P138Bootstrap P138Window
  P138EarlyFold P113Front
open ArithmeticPellRecurrence

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The two guard lemmas -/

/-- **Signs from the determinant.** -/
theorem signs_of_G {cA cB F C q : DiffRing V} (hA : 4 ≤ cA) (hB : 4 ≤ cB)
    (hG : 0 < (cA * F) * (cB * C) - (q - cA * F - cB * C) ^ 2) :
    0 < F * q ∧ 0 < C * q ∧ 0 < (q - F - C) * q := by
  obtain ⟨A, hAd⟩ : ∃ A : DiffRing V, A = cA * F := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : DiffRing V, B = cB * C := ⟨_, rfl⟩
  obtain ⟨S, hSd⟩ : ∃ S : DiffRing V, S = A + B := ⟨_, rfl⟩
  rw [← hAd, ← hBd] at hG
  have hsq := sq_nonneg (q - A - B)
  have hAB : 0 < A * B := by linarith
  have hAB2 : 4 * (A * B) ≤ S * S := by
    have := sq_nonneg (A - B)
    have e : S * S - 4 * (A * B) = (A - B) ^ 2 := by rw [hSd]; ring
    linarith
  have he : (2 * (q - S)) * (2 * (q - S)) < S * S := by
    have e : (2 * (q - S)) * (2 * (q - S)) = 4 * (q - A - B) ^ 2 := by rw [hSd]; ring
    rw [e]; linarith
  have h1 : |2 * (q - S)| < |S| := sq_lt_sq.mp (by rw [sq, sq]; exact he)
  rw [abs_mul, abs_two] at h1
  have hS0 : 0 < |S| := lt_of_le_of_lt (by positivity) h1
  have h3 : -(|q - S| * |S|) ≤ (q - S) * S := by rw [← abs_mul]; exact neg_abs_le _
  have h4 : 2 * |q - S| * |S| < |S| * |S| := mul_lt_mul_of_pos_right h1 hS0
  have hSS : |S| * |S| = S * S := abs_mul_abs_self S
  have hqS2 : S * S < 2 * (q * S) := by
    have e : q * S = S * S + (q - S) * S := by ring
    linarith
  have hSpos : 0 < S * S := by rw [← hSS]; exact mul_pos hS0 hS0
  have hqS : 0 < q * S := by linarith
  have hAS : 0 < A * S := by
    have e : A * S = A * A + A * B := by rw [hSd]; ring
    have := mul_self_nonneg A; linarith
  have hBS : 0 < B * S := by
    have e : B * S = B * B + A * B := by rw [hSd]; ring
    have := mul_self_nonneg B; linarith
  have hAq : 0 < A * q := by
    have h := mul_pos hAS hqS
    have e : A * S * (q * S) = (A * q) * (S * S) := by ring
    rw [e] at h; exact pos_of_mul_pos_left h hSpos.le
  have hBq : 0 < B * q := by
    have h := mul_pos hBS hqS
    have e : B * S * (q * S) = (B * q) * (S * S) := by ring
    rw [e] at h; exact pos_of_mul_pos_left h hSpos.le
  have hcA : 0 < cA := by linarith
  have hcB : 0 < cB := by linarith
  have hFq : 0 < F * q := by
    have e : A * q = cA * (F * q) := by rw [hAd]; ring
    rw [e] at hAq; exact pos_of_mul_pos_right hAq hcA.le
  have hCq : 0 < C * q := by
    have e : B * q = cB * (C * q) := by rw [hBd]; ring
    rw [e] at hBq; exact pos_of_mul_pos_right hBq hcB.le
  refine ⟨hFq, hCq, ?_⟩
  -- the cones are large: `|F + C| < |q| / 2`
  have hF4 : 4 * |F| ≤ |A| := by
    rw [hAd, abs_mul, abs_of_pos hcA]; exact mul_le_mul_of_nonneg_right hA (abs_nonneg _)
  have hC4 : 4 * |C| ≤ |B| := by
    rw [hBd, abs_mul, abs_of_pos hcB]; exact mul_le_mul_of_nonneg_right hB (abs_nonneg _)
  have hSsum : |S| = |A| + |B| := by
    rcases lt_or_gt_of_ne (show A ≠ 0 by intro h0; rw [h0, zero_mul] at hAB; exact lt_irrefl _ hAB)
      with hA0 | hA0
    · have hB0 : B < 0 := by
        by_contra hB0
        have := mul_nonpos_of_nonpos_of_nonneg hA0.le (not_lt.mp hB0); linarith
      rw [hSd, abs_of_neg (by linarith), abs_of_neg hA0, abs_of_neg hB0]; ring
    · have hB0 : 0 < B := pos_of_mul_pos_right hAB hA0.le
      rw [hSd, abs_of_pos (by linarith), abs_of_pos hA0, abs_of_pos hB0]
  have hq2 : |S| * |S| < 2 * |q| * |S| := by
    have : q * S ≤ |q| * |S| := by rw [← abs_mul]; exact le_abs_self _
    linarith
  have hqS' : |S| < 2 * |q| := lt_of_mul_lt_mul_right (by linarith) hS0.le
  have hFC : 2 * |F + C| < |q| := by
    have := abs_add_le F C; linarith
  have hq0 : 0 < |q| := lt_of_le_of_lt (by positivity) hFC
  have h5 : 2 * |F + C| * |q| < |q| * |q| := mul_lt_mul_of_pos_right hFC hq0
  have h6 : (F + C) * q ≤ |F + C| * |q| := by rw [← abs_mul]; exact le_abs_self _
  have hqq : |q| * |q| = q * q := abs_mul_abs_self q
  have e : (q - F - C) * q = q * q - (F + C) * q := by ring
  rw [e]
  have := mul_nonneg (abs_nonneg (F + C)) hq0.le
  linarith

/-- **The weak window from `η ζ > 0`.** -/
theorem window_of_ez {k η Y c : DiffRing V} (hY : 1 ≤ |Y|) (hc : c = η + Y * k)
    (hez : 0 < η * (k - η)) :
    k ≠ 0 ∧ |k| * (|Y| - 1) < |c| ∧ |c| < |k| * (|Y| + 1) ∧ 0 < c * (k * Y) := by
  have hηk : |η| < |k| := by
    have h1 : η * η < η * k := by linarith
    have h2 : η * η = |η| * |η| := (abs_mul_abs_self η).symm
    have h3 : η * k ≤ |η| * |k| := by rw [← abs_mul]; exact le_abs_self _
    have h0 : 0 < |η| := by
      rcases lt_or_ge 0 |η| with h | h
      · exact h
      · exfalso; have hη : η = 0 := abs_eq_zero.mp (le_antisymm h (abs_nonneg η))
        rw [hη] at hez; simp at hez
    nlinarith
  have hk0 : k ≠ 0 := by
    intro h; rw [h, abs_zero] at hηk; exact absurd hηk (not_lt.mpr (abs_nonneg _))
  have hYk : |Y * k| = |Y| * |k| := abs_mul Y k
  refine ⟨hk0, ?_, ?_, ?_⟩
  · have h := abs_sub_abs_le_abs_sub (Y * k) (-η)
    rw [show Y * k - -η = c by rw [hc]; ring, abs_neg, hYk] at h
    nlinarith
  · have h := abs_add_le η (Y * k)
    rw [← hc, hYk] at h
    nlinarith
  · have hpos : 0 < η * k := by nlinarith [sq_nonneg η]
    have h1 : |η * (k * Y)| < k * Y * (k * Y) := by
      rw [abs_mul, abs_mul, ← abs_mul_abs_self (k * Y), abs_mul]
      have hk : 0 < |k| := abs_pos.mpr hk0
      have hY0 : 0 < |Y| := by linarith
      have : |η| * (|k| * |Y|) < |k| * (|k| * |Y|) :=
        mul_lt_mul_of_pos_right hηk (mul_pos hk hY0)
      nlinarith
    have h2 : -(k * Y * (k * Y)) < η * (k * Y) := by
      have := neg_abs_le (η * (k * Y)); linarith
    rw [hc]; nlinarith

/-! ## The folded record -/

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 12 → DiffRing V)
local notation "𝓠" => P113Value.regs p x
local notation "𝓡" => P138Value.regsK p (front x) (kk p x)

/-- **The folded front of package 113.** -/
structure Folded113 where
  Bn : V
  cn : V
  Rn : V
  τ : V
  hBn : |(𝓡).A| = ι Bn
  hB3 : 3 ≤ Bn
  hcn : |x 8| = ι cn
  hcn0 : 0 < cn
  hs : 0 < (𝓡).F * (𝓡).q ∧ 0 < front x 1 * (𝓡).q ∧ 0 < ((𝓡).q - (𝓡).F - front x 1) * (𝓡).q
  hk0 : (𝓡).k ≠ 0
  hlo : |(𝓡).k| * (|(𝓡).Y| - 1) < |x 8|
  hhi : |x 8| < |(𝓡).k| * (|(𝓡).Y| + 1)
  hcky : 0 < x 8 * ((𝓡).k * (𝓡).Y)
  hez : 0 < (𝓡).eta * ((𝓡).k - (𝓡).eta)
  hDt : (𝓡).Dt = ι τ * ι τ
  hHK : (𝓡).H ∣ Kq p (front x) (kk p x) ^ 5
  hR : (𝓡).R = ι Rn
  hodd : Rn % 2 = 1
  hc : cn = ycoord Rn (Bn - 2)
  hDm : (𝓡).Dm = ι (xcoord Rn (Bn - 2)) * ι (xcoord Rn (Bn - 2))
  hRpos : 0 < Rn

/-- 113's native index has package 138's index modulus `μ = X Y`. -/
theorem index_modulus (hp : PortFacts p) : IndexModulus p (front x) (kk p x) := by
  refine ⟨(𝓡).E, front x 3, ?_, dvd_refl _, four_q4_le_E p (front x) (kk p x) hp⟩
  show (𝓠).k = _
  rw [P113Value.k_def, P113Front.R_eq, P113Front.X_eq, P113Front.Y_eq, P138Value.E_def, front_3]; ring

/-- **`H ∣ K⁵`** from `S ∣ Ac`. -/
theorem H_dvd_K5 (hS : (𝓠).S ∣ (𝓠).Ac) : (𝓠).H ∣ (𝓠).K ^ 5 := by
  have hHS : (𝓠).H ∣ (𝓠).S := ⟨(𝓠).U * (𝓠).H ^ 4, by rw [P113Value.S_def]; ring⟩
  have hAc := hHS.trans hS
  have h1 : (𝓠).H ∣ (𝓠).Ac - (𝓠).zc ^ 5 :=
    ⟨3 * (𝓠).H * (𝓠).zc ^ 3 - 19 * (𝓠).H ^ 2 * (𝓠).zc ^ 2 - 57 * (𝓠).H ^ 4, by
      rw [P113Value.Ac_def]; ring⟩
  have h2 : (𝓠).H ∣ (𝓠).zc ^ 5 := by
    have := dvd_sub hAc h1; rwa [sub_sub_cancel] at this
  have h3 : (𝓠).H ∣ (𝓠).zc ^ 5 - (𝓠).K ^ 5 := by
    have hz : (𝓠).H ∣ (𝓠).zc - (𝓠).K := ⟨x 7, by rw [P113Value.zc_def]; ring⟩
    exact hz.trans (sub_dvd_pow_sub_pow _ _ 5)
  have := dvd_sub h2 h3; rwa [sub_sub_cancel] at this

set_option maxHeartbeats 2000000 in
/-- **A zero of package 113's polynomial gives the folded front.** -/
theorem folded113_of_zero (hp : PortFacts p) (hz : P113Value.value p x = 0) :
    Nonempty (Folded113 p x) := by
  obtain ⟨y, _, _, _, haux, _, _, hSAc⟩ := P113Roots.roots p x hp hz
  obtain ⟨τ, f, hE, hDf⟩ := P113Roots.saturation p x hp hz
  obtain ⟨_, hG, hez⟩ := P113Roots.guard p x hp hz
  obtain ⟨hs0, hr0, hc0⟩ := P113Roots.srcne p x hp hz
  -- signs and window
  have hs : 0 < (𝓡).F * (𝓡).q ∧ 0 < front x 1 * (𝓡).q ∧
      0 < ((𝓡).q - (𝓡).F - front x 1) * (𝓡).q := by
    have h4 : (4 : DiffRing V) ≤ p 4 := by
      rw [hp.coneA_pow, show (4 : DiffRing V) = 2 ^ 2 by norm_num]
      exact pow_le_pow_right₀ (by norm_num) (by norm_num)
    have h5 : (4 : DiffRing V) ≤ p 5 := by
      rw [hp.coneB_pow, show (4 : DiffRing V) = 2 ^ 2 by norm_num]
      exact pow_le_pow_right₀ (by norm_num) (by norm_num)
    rw [P113Value.G_def, P113Front.F_eq, P113Front.q_eq] at hG
    rw [front_1]
    exact signs_of_G h4 h5 hG
  have hY1 : 1 ≤ |(𝓡).Y| := by have := P138Rank.three_le_abs_Y p (front x) (kk p x) hp; linarith
  obtain ⟨hk0, hlo, hhi, hcky⟩ := window_of_ez (k := (𝓡).k) (η := (𝓡).eta) (c := x 8) hY1
    (by rw [P138Value.eta_def, P138Value.Yk_def, front_8]; ring)
    (by rw [← P113Front.eta_eq, P113Front.k_eq, ← P113Value.zeta_def]; exact hez)
  have hez' : 0 < (𝓡).eta * ((𝓡).k - (𝓡).eta) := by
    rw [← P113Front.eta_eq, P113Front.k_eq, ← P113Value.zeta_def]; exact hez
  -- the base and the strong pair
  have hDt : (𝓡).Dt = ι τ * ι τ := by rw [P113Front.Dt_eq]; exact hE
  obtain ⟨Bn, hBn⟩ := abs_eq_ι (𝓡).A
  have hB3 : 3 ≤ Bn := by
    have h := abs_A p (front x) (kk p x) hp
    rw [hBn, show (3 : DiffRing V) = ι 3 by rw [map_ofNat]] at h
    exact ι_le_ι.mp h
  obtain ⟨hD, hdb⟩ := ZRowsStrongFold.delta_of_abs hBn hB3
  have hDelta : (𝓠).Delta = ι (delta (Bn - 2)) := by
    rw [P113Front.Delta_eq, P138Value.Delta_eq]; exact hD
  obtain ⟨sn, hsn⟩ := abs_eq_ι (x 11)
  obtain ⟨rn, hrn⟩ := abs_eq_ι (x 4)
  obtain ⟨cn, hcn⟩ := abs_eq_ι (x 8)
  have pos_of {u : DiffRing V} {n : V} (h : |u| = ι n) (hu : u ≠ 0) : 0 < n := by
    rcases eq_zero_or_pos n with h0 | h0
    · rw [h0, map_zero] at h; exact absurd (abs_eq_zero.mp h) hu
    · exact h0
  have hsn0 := pos_of hsn hs0
  have hrn0 := pos_of hrn hr0
  have hcn0 := pos_of hcn hc0
  have hf0 : 0 < f := by
    rcases eq_zero_or_pos f with h0 | h0
    · exfalso; rw [h0, map_zero, mul_zero] at hDf
      obtain ⟨t, ht⟩ := P113Roots.Df_mod p x hp; rw [hDf] at ht
      exact (P125Roots.three_mul t).2 (by linear_combination -ht)
    · exact h0
  have hτ0 : 0 < τ := by
    rcases eq_zero_or_pos τ with h0 | h0
    · exfalso; rw [h0, map_zero, mul_zero] at hE
      obtain ⟨t, ht⟩ := P113Roots.E_mod p x hp; rw [hE] at ht
      exact (P125Roots.three_mul t).2 (by linear_combination -ht)
    · exact h0
  obtain ⟨I0, hI0⟩ : ∃ I0 : V, I0 = sn * rn * τ * (cn * cn) := ⟨_, rfl⟩
  have hU2 : (𝓠).U ^ 2 = (ι sn * ι rn * (ι cn * ι cn)) ^ 2 := by
    rw [P113Value.U_def, ← sq_abs, abs_mul, abs_mul, abs_mul, hsn, hrn, hcn]
  have hUE : (𝓠).U * (𝓠).U * (𝓠).E = ι I0 * ι I0 := by
    rw [hE, hI0]; simp only [map_mul]
    have : (𝓠).U * (𝓠).U = (𝓠).U ^ 2 := (sq _).symm
    rw [this, hU2]; ring
  have hstrong : f * f = 1 + delta (Bn - 2) * I0 * I0 := by
    apply ι_injective
    simp only [map_mul, map_add, map_one]
    rw [← hDf, P113Value.Df_def, hDelta, mul_assoc, hUE]; ring
  have hI0pos : 0 < I0 := by
    rw [hI0]; exact mul_pos (mul_pos (mul_pos hsn0 hrn0) hτ0) (mul_pos hcn0 hcn0)
  have hQJ : (𝓠).Q = ι (delta (Bn - 2) * I0) * ι (delta (Bn - 2) * I0) := by
    rw [P113Value.Q_def, hDelta]
    have e : ι (delta (Bn - 2)) * ι (delta (Bn - 2)) * ((𝓠).U * (𝓠).U) * (𝓠).E =
        ι (delta (Bn - 2)) * ι (delta (Bn - 2)) * ((𝓠).U * (𝓠).U * (𝓠).E) := by ring
    rw [e, hUE]; simp only [map_mul]; ring
  have hV : (𝓠).V = ι (f * f) * (𝓠).b - x 8 := by
    rw [P113Value.V_def, hDf, map_mul]
  have hcdvd : cn * cn ∣ I0 := ⟨sn * rn * τ, by rw [hI0]; ring⟩
  -- the rank and its size
  obtain ⟨Rn, hRn, hlow, _⟩ := window p (front x) (kk p x) hp hs
  have hkR := k_ge p (front x) (kk p x) hp (index_modulus p x hp) hs
  have hY3 := P138Rank.three_le_abs_Y p (front x) (kk p x) hp
  have h2R : 2 * Rn < cn := by
    apply ι_lt_ι.mp
    rw [map_mul, map_ofNat, ← hcn]
    have h4 : 2 * ((𝓡).R + 1) ≤ |(𝓡).k| * (|(𝓡).Y| - 1) := by
      have := mul_le_mul hkR (show (2 : DiffRing V) ≤ |(𝓡).Y| - 1 by linarith)
        (by norm_num) (abs_nonneg _)
      linarith
    rw [hRn] at h4
    linarith
  have hRpos : 0 < Rn := by
    have : (0 : DiffRing V) ≤ |(𝓡).q| * ((𝓡).q ^ 2 - 1) := by
      have := abs_q_ge p (front x) (kk p x) hp
      have h64 : (2 : DiffRing V) ≤ 2 ^ 64 := by norm_num
      have : 1 ≤ (𝓡).q ^ 2 := by rw [← sq_abs]; nlinarith
      exact mul_nonneg (abs_nonneg _) (by linarith)
    exact pos_of_ι (by linarith)
  have hcI : cn < I0 := by
    apply ι_lt_ι.mp
    rw [hI0]; simp only [map_mul]
    have h1 : ∀ {n : V}, 0 < n → (1 : DiffRing V) ≤ ι n := fun h => by
      rw [← map_one ι]; exact ι_le_ι.mpr (pos_iff_one_le.mp h)
    have hc2 : (2 : DiffRing V) ≤ ι cn := by
      have := ι_lt_ι.mpr h2R; rw [map_mul, map_ofNat] at this
      have := h1 hRpos; linarith
    have hsrt : (1 : DiffRing V) ≤ ι sn * ι rn * ι τ := by
      have a := h1 hsn0; have b := h1 hrn0; have c := h1 hτ0
      calc (1 : DiffRing V) = 1 * 1 * 1 := by ring
        _ ≤ ι sn * ι rn * ι τ :=
          mul_le_mul (mul_le_mul a b (by norm_num) (ι_nonneg _)) c (by norm_num)
            (mul_nonneg (ι_nonneg _) (ι_nonneg _))
    have hcc : 2 * (ι cn : DiffRing V) ≤ ι cn * ι cn := mul_le_mul_of_nonneg_right hc2 (by linarith)
    have := mul_le_mul_of_nonneg_right hsrt (mul_nonneg (ι_nonneg cn) (ι_nonneg cn))
    linarith
  have hrank : (ι cn : DiffRing V) ∣ (𝓠).b - ι Rn ∨ (ι cn : DiffRing V) ∣ (𝓠).b + ι Rn := by
    right
    have h8 : (ι cn : DiffRing V) ∣ x 8 := by
      rcases eq_or_eq_neg_abs (x 8) with h | h <;> rw [hcn] at h
      · exact ⟨1, by rw [mul_one]; exact h⟩
      · exact ⟨-1, by rw [mul_neg_one]; exact h⟩
    obtain ⟨u, hu⟩ := h8
    refine ⟨u + 4 * x 11 * x 4 * x 8 * u * (𝓠).E * x 7, ?_⟩
    rw [P113Value.b_def, P113Front.R_eq, hRn, P113Value.U_def]
    linear_combination (1 + 4 * x 11 * x 4 * x 8 * (𝓠).E * x 7) * hu
  obtain ⟨hodd, hcy, hmain⟩ := ZRowsStrongFold.strong_fold (Bn - 2) I0 f cn y Rn (x 8)
    (𝓠).Q (𝓠).V (𝓠).b hdb hf0 hI0pos hstrong hQJ hV haux hcn hcn0 hcdvd hcI hRpos h2R hrank
  have hDm : (𝓡).Dm = ι (xcoord Rn (Bn - 2)) * ι (xcoord Rn (Bn - 2)) := by
    rw [P138Value.Dm_eq, ← P113Front.Delta_eq, hDelta, front_8]; exact hmain
  have hHK : (𝓡).H ∣ Kq p (front x) (kk p x) ^ 5 := by
    rw [P113Front.Kq_eq, ← P113Front.H_eq]; exact H_dvd_K5 p x hSAc
  exact ⟨⟨Bn, cn, Rn, τ, hBn, hB3, hcn, hcn0, hs, hk0, hlo, hhi, hcky, hez', hDt, hHK, hRn, hodd,
    hcy, hDm, hRpos⟩⟩

end Regs

#print axioms signs_of_G
#print axioms window_of_ez
#print axioms folded113_of_zero

end DiophantineConsistency.P113Fold
