import DiophantineConsistency.PolynomialRangeBounds

/-!
# Bounds for the degree-separated split116 source word

The positivity bounds precede every digit-decoding or source-zero premise.
The upper packing bounds additionally use exactly the weak cap
`g < 4*b*B^116` recovered by ratio soundness.
-/

namespace DiophantineConsistency.SplitWordBounds

open Polynomial Finset
open scoped BigOperators

set_option maxRecDepth 4000
set_option maxHeartbeats 400000

/-- The three literal degree and coefficient bounds needed by the source. -/
structure KernelBounds (D0 D1 D2 : ℤ[X]) (H : ℤ) : Prop where
  degree_zero : D0.natDegree ≤ 1719
  degree_one : D1.natDegree ≤ 2027
  degree_two : D2.natDegree ≤ 1929
  coeff_zero : ∀ i, |D0.coeff i| ≤ H
  coeff_one : ∀ i, |D1.coeff i| ≤ H
  coeff_two : ∀ i, |D2.coeff i| ≤ H
  leading_two : D2.coeff 1929 = 1

def sourceValue (D0 D1 D2 : ℤ[X]) (B U : ℤ) : ℤ :=
  D2.eval B * U ^ 2 + D1.eval B * U + D0.eval B

theorem scale_bounds {B H b : ℤ} (hH : 0 < H) (hb : 1 ≤ b)
    (hscale : B = 4096 * H * b ^ 2) :
    4096 ≤ B ∧ 2 * H ≤ B - 1 ∧ 16 * H < B ∧ 4 * b < B := by
  have hH1 : 1 ≤ H := by omega
  have hb2 : 1 ≤ b ^ 2 := by nlinarith
  have hHb : H ≤ H * b ^ 2 := by
    nlinarith [mul_nonneg hH.le (sub_nonneg.mpr hb2)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · rw [hscale]
    exact PolynomialRangeBounds.scale_gt_four_digits hH hb

/-- A single-coefficient leading layer is handled by doubling the polynomial. -/
theorem doubled_eval_gt_top {B H : ℤ} (hB : 2 ≤ B) (hBH : 2 * H ≤ B - 1)
    (p : ℤ[X]) {d : ℕ} (hd : p.natDegree ≤ d)
    (hc : ∀ i, |p.coeff i| ≤ H) (htop : p.coeff d = 1) :
    B ^ d < 2 * p.eval B := by
  have hdegree : (p + p).natDegree ≤ d :=
    (natDegree_add_le _ _).trans (max_le hd hd)
  have hcoeff : ∀ i, |(p + p).coeff i| ≤ 2 * H := by
    intro i
    rw [coeff_add]
    exact (abs_add_le _ _).trans (by have h := hc i; linarith)
  have hleading : (p + p).coeff d = 2 := by rw [coeff_add, htop]; norm_num
  have h := PolynomialRangeBounds.eval_gt_top_power hB hBH (p + p) hdegree hcoeff hleading
  simpa only [eval_add, two_mul] using h

theorem scalar_pow_lt {B c : ℤ} (hB : 2 ≤ B) (hc : c < B)
    {d e : ℕ} (hde : d < e) : c * B ^ d < B ^ e := by
  have hg : 1 ≤ e - d := by omega
  have hpow : B ≤ B ^ (e - d) := by
    simpa only [pow_one] using (pow_le_pow_right₀ (by omega : 1 ≤ B) hg)
  calc
    c * B ^ d < B ^ (e - d) * B ^ d :=
      mul_lt_mul_of_pos_right (hc.trans_le hpow) (by positivity)
    _ = B ^ e := by
      rw [mul_comm, ← pow_add]
      congr 1
      omega

/-- The signed lower layers are each less than one eighth of the positive
leading-layer scale. The degree gaps are 18 and 442. -/
theorem negative_layers_lt {D0 D1 D2 : ℤ[X]} {B H b U : ℤ}
    (hk : KernelBounds D0 D1 D2 H) (hH : 0 < H) (hb : 1 ≤ b)
    (hscale : B = 4096 * H * b ^ 2) (hU : B ^ 116 ≤ U) :
    8 * (|D1.eval B| * U) < B ^ 1929 * U ^ 2 ∧
      8 * |D0.eval B| < B ^ 1929 * U ^ 2 := by
  obtain ⟨hB, _, h16, _⟩ := scale_bounds hH hb hscale
  have hB2 : 2 ≤ B := by omega
  have hU0 : 0 < U := (by positivity : 0 < B ^ 116).trans_le hU
  have h1 := PolynomialRangeBounds.abs_eval_lt hB2 hH D1 hk.degree_one hk.coeff_one
  have h0 := PolynomialRangeBounds.abs_eval_lt hB2 hH D0 hk.degree_zero hk.coeff_zero
  have hgap1 : 16 * H * B ^ 2027 < B ^ 2045 :=
    scalar_pow_lt hB2 h16 (by decide)
  have hgap0 : 16 * H * B ^ 1719 < B ^ 2161 :=
    scalar_pow_lt hB2 h16 (by decide)
  have hlead1 : B ^ 2045 ≤ B ^ 1929 * U := by
    calc
      B ^ 2045 = B ^ 1929 * B ^ 116 := by rw [← pow_add]
      _ ≤ B ^ 1929 * U := mul_le_mul_of_nonneg_left hU (by positivity)
  have hlead0 : B ^ 2161 ≤ B ^ 1929 * U ^ 2 := by
    have hu2 : (B ^ 116) ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ (by positivity) hU 2
    calc
      B ^ 2161 = B ^ 1929 * (B ^ 116) ^ 2 := by rw [← pow_mul, ← pow_add]
      _ ≤ B ^ 1929 * U ^ 2 := mul_le_mul_of_nonneg_left hu2 (by positivity)
  have hsmall1 : 8 * |D1.eval B| < B ^ 1929 * U := by
    linarith
  constructor
  · have h := mul_lt_mul_of_pos_right hsmall1 hU0
    nlinarith only [h]
  · linarith

/-- Unconditional strict source positivity, before the weak code cap. -/
theorem source_pos {D0 D1 D2 : ℤ[X]} {B H b U : ℤ}
    (hk : KernelBounds D0 D1 D2 H) (hH : 0 < H) (hb : 1 ≤ b)
    (hscale : B = 4096 * H * b ^ 2) (hU : B ^ 116 ≤ U) :
    B ^ 1929 * U ^ 2 < 4 * sourceValue D0 D1 D2 B U ∧
      0 < sourceValue D0 D1 D2 B U := by
  obtain ⟨hB, hBH, _, _⟩ := scale_bounds hH hb hscale
  have hB2 : 2 ≤ B := by omega
  have hU0 : 0 < U := (by positivity : 0 < B ^ 116).trans_le hU
  have h2 := doubled_eval_gt_top hB2 hBH D2 hk.degree_two hk.coeff_two hk.leading_two
  have h2U := mul_lt_mul_of_pos_right h2 (sq_pos_of_pos hU0)
  obtain ⟨h1, h0⟩ := negative_layers_lt hk hH hb hscale hU
  have hneg1 : -(|D1.eval B| * U) ≤ D1.eval B * U :=
    (by simpa only [neg_mul] using mul_le_mul_of_nonneg_right (neg_abs_le (D1.eval B)) hU0.le)
  have hneg0 := neg_abs_le (D0.eval B)
  have hpos : 0 < B ^ 1929 * U ^ 2 := by positivity
  unfold sourceValue
  constructor <;> nlinarith only [h2U, h1, h0, hneg1, hneg0, hpos]

/-- The exact geometric estimate avoids losing a factor two in packing. -/
theorem abs_eval_scaled_lt {B H : ℤ} (hB : 2 ≤ B) (hH : 0 < H)
    (p : ℤ[X]) {d : ℕ} (hd : p.natDegree ≤ d) (hc : ∀ i, |p.coeff i| ≤ H) :
    |p.eval B| * (B - 1) < H * B ^ (d + 1) := by
  have hsum : |p.eval B| ≤ H * (∑ i ∈ range (d + 1), B ^ i) := by
    rw [eval_eq_sum_range' (by omega : p.natDegree < d + 1)]
    calc
      |∑ i ∈ range (d + 1), p.coeff i * B ^ i| ≤
          ∑ i ∈ range (d + 1), |p.coeff i * B ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range (d + 1), H * B ^ i := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ B ^ i)]
        exact mul_le_mul_of_nonneg_right (hc i) (by positivity)
      _ = _ := (Finset.mul_sum _ _ _).symm
  calc
    |p.eval B| * (B - 1) ≤ H * (∑ i ∈ range (d + 1), B ^ i) * (B - 1) :=
      mul_le_mul_of_nonneg_right hsum (by omega)
    _ = H * ((B - 1) * (∑ i ∈ range (d + 1), B ^ i)) := by ring
    _ = H * (B ^ (d + 1) - 1) := by rw [PolynomialRangeBounds.geometric_identity]
    _ < H * B ^ (d + 1) := by nlinarith

/-- The manuscript's sharp weak-cap coefficient estimate, stated without
division so it remains an integer inequality. -/
theorem source_upper_scaled {D0 D1 D2 : ℤ[X]} {B H b U : ℤ}
    (hk : KernelBounds D0 D1 D2 H) (hH : 0 < H) (hb : 1 ≤ b)
    (hB : 2 ≤ B) (hU : 0 < U) (hUcap : U < 6 * b * B ^ 116) :
    sourceValue D0 D1 D2 B U * (B - 1) < 43 * H * b ^ 2 * B ^ 2162 := by
  have h2 := abs_eval_scaled_lt hB hH D2 hk.degree_two hk.coeff_two
  have h1 := abs_eval_scaled_lt hB hH D1 hk.degree_one hk.coeff_one
  have h0 := abs_eval_scaled_lt hB hH D0 hk.degree_zero hk.coeff_zero
  change |D2.eval B| * (B - 1) < H * B ^ 1930 at h2
  change |D1.eval B| * (B - 1) < H * B ^ 2028 at h1
  change |D0.eval B| * (B - 1) < H * B ^ 1720 at h0
  have hBm : 0 < B - 1 := by omega
  have h2U := mul_lt_mul_of_pos_right h2 (sq_pos_of_pos hU)
  have h1U := mul_lt_mul_of_pos_right h1 hU
  have hsource : sourceValue D0 D1 D2 B U * (B - 1) ≤
      (|D2.eval B| * (B - 1)) * U ^ 2 +
      (|D1.eval B| * (B - 1)) * U + |D0.eval B| * (B - 1) := by
    have hD2 := mul_le_mul_of_nonneg_right (le_abs_self (D2.eval B))
      (by positivity : 0 ≤ U ^ 2 * (B - 1))
    have hD1 := mul_le_mul_of_nonneg_right (le_abs_self (D1.eval B))
      (by positivity : 0 ≤ U * (B - 1))
    have hD0 := mul_le_mul_of_nonneg_right (le_abs_self (D0.eval B))
      (by omega : 0 ≤ B - 1)
    unfold sourceValue
    nlinarith only [hD2, hD1, hD0]
  have h2cap : H * B ^ 1930 * U ^ 2 ≤ 36 * H * b ^ 2 * B ^ 2162 := by
    calc
      _ ≤ H * B ^ 1930 * (6 * b * B ^ 116) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hU.le hUcap.le 2) (by positivity)
      _ = 36 * H * b ^ 2 * (B ^ 1930 * (B ^ 116) ^ 2) := by ring
      _ = _ := by rw [← pow_mul, ← pow_add]
  have h1cap : H * B ^ 2028 * U ≤ 6 * H * b * B ^ 2144 := by
    calc
      _ ≤ H * B ^ 2028 * (6 * b * B ^ 116) :=
        mul_le_mul_of_nonneg_left hUcap.le (by positivity)
      _ = 6 * H * b * (B ^ 2028 * B ^ 116) := by ring
      _ = _ := by rw [← pow_add]
  have hpre : sourceValue D0 D1 D2 B U * (B - 1) <
      36 * H * b ^ 2 * B ^ 2162 + 6 * H * b * B ^ 2144 + H * B ^ 1720 := by
    nlinarith only [hsource, h2U, h1U, h0, h2cap, h1cap]
  have hb2 : b ≤ b ^ 2 := by nlinarith
  have hb21 : 1 ≤ b ^ 2 := by nlinarith
  have hp1 : b * B ^ 2144 ≤ b ^ 2 * B ^ 2162 :=
    mul_le_mul hb2 (pow_le_pow_right₀ (by omega : 1 ≤ B) (by decide : 2144 ≤ 2162))
      (by positivity) (by positivity)
  have hp0 : B ^ 1720 ≤ b ^ 2 * B ^ 2162 := by
    calc
      B ^ 1720 ≤ B ^ 2162 := pow_le_pow_right₀ (by omega) (by decide)
      _ ≤ b ^ 2 * B ^ 2162 := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hb21 (by positivity : 0 ≤ B ^ 2162)
  have hm1 := mul_le_mul_of_nonneg_left hp1 (by positivity : 0 ≤ 6 * H)
  have hm0 := mul_le_mul_of_nonneg_left hp0 hH.le
  nlinarith only [hpre, hm1, hm0]

theorem source_lt_one_sixtyfourth {D0 D1 D2 : ℤ[X]} {B H b U : ℤ}
    (hk : KernelBounds D0 D1 D2 H) (hH : 0 < H) (hb : 1 ≤ b)
    (hscale : B = 4096 * H * b ^ 2) (hU : 0 < U)
    (hUcap : U < 6 * b * B ^ 116) :
    64 * sourceValue D0 D1 D2 B U < B ^ 2162 := by
  have hB := (scale_bounds hH hb hscale).1
  have hsource := source_upper_scaled hk hH hb (by omega) hU hUcap
  have hHb : 1 ≤ H * b ^ 2 := by
    have hH1 : 1 ≤ H := by omega
    have hb2 : 1 ≤ b ^ 2 := by nlinarith
    nlinarith only [mul_le_mul_of_nonneg_right hH1 (sq_nonneg b), hb2]
  have hsmall : 2752 * H * b ^ 2 < B - 1 := by nlinarith only [hscale, hHb]
  have hlarge := mul_lt_mul_of_pos_right hsmall (by positivity : 0 < B ^ 2162)
  have hscaled : (64 * sourceValue D0 D1 D2 B U) * (B - 1) < B ^ 2162 * (B - 1) := by
    nlinarith only [hsource, hlarge]
  exact (mul_lt_mul_iff_left₀ (by omega : 0 < B - 1)).mp hscaled

def powerSum {ι : Type*} [Fintype ι] (B : ℤ) (w : ι → ℕ) : ℤ := ∑ i, B ^ w i

theorem powerSum_nonneg {ι : Type*} [Fintype ι] {B : ℤ} (hB : 0 ≤ B) (w : ι → ℕ) :
    0 ≤ powerSum B w := Finset.sum_nonneg (fun _ _ => pow_nonneg hB _)

theorem powerSum_lt_two_top {ι : Type*} [Fintype ι] {B : ℤ}
    (hB : 2 ≤ B) (w : ι → ℕ) (hi : Function.Injective w) {d : ℕ}
    (hw : ∀ i, w i ≤ d) : powerSum B w < 2 * B ^ d := by
  have hs : univ.image w ⊆ range (d + 1) := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := mem_image.mp hj
    exact mem_range.mpr (by have h := hw i; omega)
  have hle : (∑ i ∈ univ.image w, B ^ i) ≤ ∑ i ∈ range (d + 1), B ^ i :=
    sum_le_sum_of_subset_of_nonneg hs (by intro i _ _; positivity)
  rw [sum_image (fun i _ j _ hij => hi hij)] at hle
  exact hle.trans_lt (PolynomialRangeBounds.geometric_lt_two_top hB d)

theorem top_le_powerSum {ι : Type*} [Fintype ι] {B : ℤ} (hB : 0 ≤ B)
    (w : ι → ℕ) {d : ℕ} (htop : ∃ i, w i = d) : B ^ d ≤ powerSum B w := by
  obtain ⟨i, hi⟩ := htop
  rw [← hi]
  exact single_le_sum (fun j _ => pow_nonneg hB _) (mem_univ i)

theorem source_pos_of_word {D0 D1 D2 : ℤ[X]} {B H b g : ℤ}
    (hk : KernelBounds D0 D1 D2 H) (hH : 0 < H) (hb : 1 ≤ b)
    (hscale : B = 4096 * H * b ^ 2) (w : Fin 31 → ℕ)
    (htop : ∃ i, w i = 116) (hg : 0 ≤ g) :
    0 < sourceValue D0 D1 D2 B (powerSum B w + g) := by
  have hB := (scale_bounds hH hb hscale).1
  have hu := top_le_powerSum (by omega : 0 ≤ B) w htop
  exact (source_pos hk hH hb hscale (by linarith)).2

def lowMask (B b ell : ℤ) : ℤ := B ^ 117 - 1 - (b - 1) * ell

def packedS (B g G targets : ℤ) : ℤ := g + B ^ 117 * (2 * G + targets)

def packedT (B b ell targets : ℤ) : ℤ := lowMask B b ell + B ^ 117 * ((B - 2) * targets)

theorem lowMask_bounds {B b ell : ℤ} (hB : 2 ≤ B) (hb : 1 ≤ b)
    (hscale : 4 * b < B) (hell0 : 0 ≤ ell) (hell : ell < 2 * B ^ 116) :
    0 ≤ lowMask B b ell ∧ lowMask B b ell < B ^ 117 := by
  have hb0 : 0 < b := by omega
  have hsub0 : 0 ≤ (b - 1) * ell := by positivity
  have hsub : (b - 1) * ell < B ^ 117 := by
    have hbell := mul_lt_mul_of_pos_left hell hb0
    have hle : (b - 1) * ell ≤ b * ell := by nlinarith only [hell0]
    have hBpow : 0 < B ^ 116 := by positivity
    have hscaled := mul_lt_mul_of_pos_right (show 2 * b < B by omega) hBpow
    have he : B * B ^ 116 = B ^ 117 := by rw [pow_succ]; ring
    rw [he] at hscaled
    nlinarith only [hbell, hle, hscaled]
  unfold lowMask
  omega

/-- Positivity and low-mask bounds hold for every nonnegative candidate g,
independently of the later ratio soundness cap. -/
theorem unconditional_word_bounds {D0 D1 D2 : ℤ[X]} {B H b g : ℤ}
    (hk : KernelBounds D0 D1 D2 H) (hH : 0 < H) (hb : 1 ≤ b)
    (hscale : B = 4096 * H * b ^ 2) (w : Fin 31 → ℕ)
    (hwi : Function.Injective w) (hw : ∀ i, w i ≤ 116) (hwt : ∃ i, w i = 116)
    (q : Fin 22 → ℕ) (hg : 0 ≤ g) :
    let ell := powerSum B w
    let targets := powerSum B q
    let G := sourceValue D0 D1 D2 B (ell + g)
    0 < G ∧ 0 ≤ lowMask B b ell ∧ lowMask B b ell < B ^ 117 ∧
      0 < packedS B g G targets ∧ 0 ≤ packedT B b ell targets := by
  dsimp only
  obtain ⟨hB, _, _, hfour⟩ := scale_bounds hH hb hscale
  have hB2 : 2 ≤ B := by omega
  have he0 := powerSum_nonneg (by omega : 0 ≤ B) w
  have he := powerSum_lt_two_top hB2 w hwi hw
  obtain ⟨hm0, hmcap⟩ := lowMask_bounds hB2 hb hfour he0 he
  have hG := source_pos_of_word hk hH hb hscale w hwt hg
  have ht0 := powerSum_nonneg (by omega : 0 ≤ B) q
  refine ⟨hG, hm0, hmcap, ?_, ?_⟩
  · unfold packedS
    positivity
  · unfold packedT
    positivity

theorem targets_bounds {B : ℤ} (hB : 4096 ≤ B) (q : Fin 22 → ℕ)
    (hi : Function.Injective q) (hq : ∀ j, q j ≤ 2129) :
    0 ≤ powerSum B q ∧ 64 * powerSum B q < B ^ 2162 ∧
      64 * ((B - 2) * powerSum B q) < B ^ 2162 := by
  have hB2 : 2 ≤ B := by omega
  have hsum := powerSum_lt_two_top hB2 q hi hq
  have hg0 := powerSum_nonneg (by omega : 0 ≤ B) q
  have hgap : 128 * B ^ 2129 < B ^ 2162 := scalar_pow_lt hB2 (by omega) (by decide)
  have hgap' : 128 * B ^ 2130 < B ^ 2162 := scalar_pow_lt hB2 (by omega) (by decide)
  have htimes := mul_lt_mul_of_pos_left hsum (by omega : 0 < B - 2)
  have hpow : B * B ^ 2129 = B ^ 2130 := by rw [pow_succ]; ring
  refine ⟨hg0, by linarith, ?_⟩
  have hrel : (B - 2) * powerSum B q < 2 * B ^ 2130 := by
    rw [← hpow]
    nlinarith only [htimes, (by positivity : 0 < B ^ 2129)]
  linarith

/-- Full low/high packing fits before the code is decoded. The stronger
`S+T` bound also supplies the shorter rank's required `S<L` bound. -/
theorem weak_cap_packing {D0 D1 D2 : ℤ[X]} {B H b g : ℤ}
    (hk : KernelBounds D0 D1 D2 H) (hH : 0 < H) (hb : 1 ≤ b)
    (hscale : B = 4096 * H * b ^ 2) (w : Fin 31 → ℕ)
    (hwi : Function.Injective w) (hw : ∀ i, w i ≤ 116) (hwt : ∃ i, w i = 116)
    (q : Fin 22 → ℕ) (hqi : Function.Injective q) (hq : ∀ j, q j ≤ 2129)
    (hg : 0 ≤ g) (hcap : g < 4 * b * B ^ 116) :
    let ell := powerSum B w
    let targets := powerSum B q
    let G := sourceValue D0 D1 D2 B (ell + g)
    0 < G ∧ g < B ^ 117 ∧ 0 ≤ lowMask B b ell ∧ lowMask B b ell < B ^ 117 ∧
      0 < packedS B g G targets ∧ 0 ≤ packedT B b ell targets ∧
      packedS B g G targets + packedT B b ell targets < B ^ 2279 ∧
      packedS B g G targets < b * B ^ 2279 := by
  dsimp only
  obtain ⟨hB, _, _, hfour⟩ := scale_bounds hH hb hscale
  have hB2 : 2 ≤ B := by omega
  have he := powerSum_lt_two_top hB2 w hwi hw
  have hetop := top_le_powerSum (by omega : 0 ≤ B) w hwt
  have hu0 : 0 < powerSum B w + g := by
    have hp : 0 < B ^ 116 := by positivity
    linarith
  have hucap : powerSum B w + g < 6 * b * B ^ 116 := by
    have hp : 0 < B ^ 116 := by positivity
    nlinarith only [he, hcap, mul_le_mul_of_nonneg_right hb hp.le]
  obtain ⟨hGp, hm0, hmcap, hS0, hT0⟩ :=
    unconditional_word_bounds hk hH hb hscale w hwi hw hwt q hg
  have hGcap := source_lt_one_sixtyfourth hk hH hb hscale hu0 hucap
  have hgcap : g < B ^ 117 := PolynomialRangeBounds.weak_cap_lt_low_block hB2 hfour 116 hcap
  obtain ⟨ht0, htcap, hthicap⟩ := targets_bounds hB q hqi hq
  have hN0 : 0 < B ^ 117 := by positivity
  have hZ : 128 < B ^ 2162 := by
    have hpow : B ≤ B ^ 2162 := by
      simpa only [pow_one] using (pow_le_pow_right₀ (by omega : 1 ≤ B) (by decide : 1 ≤ 2162))
    omega
  have hhigh : 2 + (2 * sourceValue D0 D1 D2 B (powerSum B w + g) +
      powerSum B q + (B - 2) * powerSum B q) < B ^ 2162 := by
    linarith only [hGcap, htcap, hthicap, hZ]
  have hsum : packedS B g (sourceValue D0 D1 D2 B (powerSum B w + g)) (powerSum B q) +
      packedT B b (powerSum B w) (powerSum B q) < B ^ 2279 := by
    have hlow : g + lowMask B b (powerSum B w) < 2 * B ^ 117 := by linarith
    have hmul := mul_lt_mul_of_pos_left hhigh hN0
    have he : B ^ 117 * B ^ 2162 = B ^ 2279 := by rw [← pow_add]
    rw [he] at hmul
    unfold packedS packedT
    nlinarith only [hlow, hmul]
  have hL : B ^ 2279 ≤ b * B ^ 2279 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ B ^ 2279)
  refine ⟨hGp, hgcap, hm0, hmcap, hS0, hT0, hsum, ?_⟩
  linarith

end DiophantineConsistency.SplitWordBounds
