import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# A sharp two-square finalizer

The identities and arithmetic equivalence used by the selective quadratic
nine-variable proposal. The final polynomial is computable integer arithmetic;
rational witnesses occur only in its correctness proof.
-/

namespace DiophantineConsistency.NearSquareFinalizer

/-- The four-factor norm, expressed without radicals. -/
def norm {R : Type*} [CommRing R] (theta omega a₀ weight a₁ : R) : R :=
  (theta ^ 2 - omega ^ 2 * (a₀ + weight ^ 2 * a₁)) ^ 2 -
    4 * omega ^ 4 * weight ^ 2 * a₀ * a₁

/-- The equivalent form that recovers the first root by rational arithmetic. -/
theorem norm_eq {R : Type*} [CommRing R] (theta omega a₀ weight a₁ : R) :
    norm theta omega a₀ weight a₁ =
      (theta ^ 2 + omega ^ 2 * a₀ - omega ^ 2 * weight ^ 2 * a₁) ^ 2 -
        4 * theta ^ 2 * omega ^ 2 * a₀ := by
  unfold norm
  ring

/-- The exact near-square defect after using the Pell register identity
`D*F = t^2*D^3*(D-1)+D`. -/
theorem majorant_defect {R : Type*} [CommRing R] (t D F : R)
    (hDF : D * F = t ^ 2 * D ^ 3 * (D - 1) + D) :
    (t * (8 * D ^ 2 - 4 * D - 1)) ^ 2 - 64 * D * F =
      t ^ 2 * (8 * D + 1) - 64 * D := by
  linear_combination -64 * hDF

/-- A positive defect bound valid throughout the arithmetic register domain. -/
theorem majorant_defect_pos {t D F : ℤ} (hD : 1 ≤ D) (ht : 9 ≤ t ^ 2)
    (hDF : D * F = t ^ 2 * D ^ 3 * (D - 1) + D) :
    8 * D + 9 ≤ (t * (8 * D ^ 2 - 4 * D - 1)) ^ 2 - 64 * D * F := by
  rw [majorant_defect t D F hDF]
  nlinarith [mul_nonneg (show 0 ≤ t ^ 2 - 9 by omega)
    (show 0 ≤ 8 * D + 1 by omega)]

/-- Multiplication by the final two Pell factors preserves the sharp defect. -/
theorem full_majorant_defect {R : Type*} [CommRing R] (t D F G H I : R)
    (hDF : D * F = t ^ 2 * D ^ 3 * (D - 1) + D)
    (hI : I = (G ^ 2 - 1) * H ^ 2 + 1) :
    (t * (8 * D ^ 2 - 4 * D - 1) * G * H) ^ 2 - 64 * D * F * I =
      (t ^ 2 * (8 * D + 1) - 64 * D) * G ^ 2 * H ^ 2 +
        64 * D * F * (H ^ 2 - 1) := by
  rw [hI]
  linear_combination G ^ 2 * H ^ 2 * majorant_defect t D F hDF

/-- The defining Pell-register equations imply the product identity used above. -/
theorem pell_product_identity {R : Type*} [CommRing R] (A C D E F t : R)
    (hD : D = (A ^ 2 - 1) * C ^ 2 + 1)
    (hE : E = t * D * C) (hF : F = (A ^ 2 - 1) * E ^ 2 + 1) :
    D * F = t ^ 2 * D ^ 3 * (D - 1) + D := by
  rw [hF, hE]
  calc
    D * ((A ^ 2 - 1) * (t * D * C) ^ 2 + 1) =
        t ^ 2 * D ^ 3 * ((A ^ 2 - 1) * C ^ 2) + D := by ring
    _ = t ^ 2 * D ^ 3 * (D - 1) + D := by rw [hD]; ring

/-- The sharp majorant is positive and strictly bounds the final radicand. -/
theorem full_majorant_bounds {t D F G H I : ℤ}
    (ht : 0 < t) (htsq : 9 ≤ t ^ 2) (hD : 1 ≤ D) (hF : 0 < F)
    (hG : 0 < G) (hH : 1 ≤ H)
    (hDF : D * F = t ^ 2 * D ^ 3 * (D - 1) + D)
    (hI : I = (G ^ 2 - 1) * H ^ 2 + 1) :
    0 < t * (8 * D ^ 2 - 4 * D - 1) * G * H ∧
      0 < 64 * D * F * I ∧
      64 * D * F * I < (t * (8 * D ^ 2 - 4 * D - 1) * G * H) ^ 2 := by
  have hfac : 0 < 8 * D ^ 2 - 4 * D - 1 := by
    nlinarith [mul_nonneg (show 0 ≤ D - 1 by omega) (show 0 ≤ D by omega)]
  have hV : 0 < t * (8 * D ^ 2 - 4 * D - 1) * G * H := by positivity
  have hHsq : 0 ≤ H ^ 2 - 1 := by nlinarith
  have hGsq : 0 ≤ G ^ 2 - 1 := by nlinarith
  have hIpos : 0 < I := by
    nlinarith [mul_nonneg hGsq (sq_nonneg H)]
  have ha : 0 < 64 * D * F * I := by positivity
  have hdef : 0 < t ^ 2 * (8 * D + 1) - 64 * D := by
    have hd := majorant_defect_pos hD htsq hDF
    rw [majorant_defect t D F hDF] at hd
    omega
  have hmain : 0 < (t ^ 2 * (8 * D + 1) - 64 * D) * G ^ 2 * H ^ 2 := by
    apply mul_pos
    · exact mul_pos hdef (sq_pos_of_pos hG)
    · exact sq_pos_of_pos (by omega)
  have htail : 0 ≤ 64 * D * F * (H ^ 2 - 1) := by positivity
  have heq := full_majorant_defect t D F G H I hDF hI
  exact ⟨hV, ha, by linarith⟩

/-- A nonzero rational norm root reconstructs two rational square roots. -/
theorem rational_roots_of_norm_zero {a b w q : ℚ} (hw : w ≠ 0) (hq : q ≠ 0)
    (hz : norm q 1 a w b = 0) :
    ∃ r s : ℚ, r ^ 2 = a ∧ s ^ 2 = b ∧ q = r + w * s := by
  let r := (q ^ 2 + a - w ^ 2 * b) / (2 * q)
  let s := (q - r) / w
  have hn : (q ^ 2 + a - w ^ 2 * b) ^ 2 = 4 * q ^ 2 * a := by
    rw [norm_eq] at hz
    simpa using (sub_eq_zero.mp hz)
  have hr : r ^ 2 = a := by
    dsimp [r]
    field_simp [hq]
    nlinarith [hn]
  have hs : s ^ 2 = b := by
    dsimp [s, r]
    field_simp [hw, hq]
    nlinarith [hn]
  refine ⟨r, s, hr, hs, ?_⟩
  dsimp [s]
  field_simp
  ring

/-- A norm zero with the first radicand strictly below the separating square
forces both integer radicands to be squares and supplies signed integer roots. -/
theorem integer_roots_of_norm_zero {theta omega a b w : ℤ}
    (homega : omega ≠ 0) (hw : 0 < w) (ha : a < w ^ 2) (hb : 0 < b)
    (hz : norm theta omega a w b = 0) :
    ∃ r s : ℤ, r ^ 2 = a ∧ s ^ 2 = b ∧ theta = omega * (r + w * s) := by
  have hsep : a ≠ w ^ 2 * b := by
    have := mul_nonneg (sq_nonneg w) (show 0 ≤ b - 1 by omega)
    nlinarith
  have htheta : theta ≠ 0 := by
    intro ht
    rw [ht] at hz
    dsimp [norm] at hz
    have he : omega ^ 4 * (a - w ^ 2 * b) ^ 2 = 0 := by
      linear_combination hz
    rcases mul_eq_zero.mp he with he | he
    · exact (pow_ne_zero 4 homega) he
    · exact hsep (sub_eq_zero.mp (eq_zero_of_pow_eq_zero he))
  have hwQ : (w : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hw
  have hoQ : (omega : ℚ) ≠ 0 := by exact_mod_cast homega
  have htQ : (theta : ℚ) ≠ 0 := by exact_mod_cast htheta
  have hzQ : norm ((theta : ℚ) / omega) 1 a w b = 0 := by
    have h : norm (theta : ℚ) omega a w b = 0 := by
      dsimp [norm] at hz ⊢
      exact_mod_cast hz
    dsimp [norm] at h ⊢
    field_simp
    nlinarith [h]
  obtain ⟨r, s, hr, hs, hsum⟩ := rational_roots_of_norm_zero hwQ (div_ne_zero htQ hoQ) hzQ
  have hsa : IsSquare a := Rat.isSquare_intCast_iff.mp ⟨r, by nlinarith [hr]⟩
  have hsb : IsSquare b := Rat.isSquare_intCast_iff.mp ⟨s, by nlinarith [hs]⟩
  obtain ⟨r₀, hr₀⟩ := hsa
  obtain ⟨s₀, hs₀⟩ := hsb
  have hr₀' : r₀ ^ 2 = a := by nlinarith [hr₀]
  have hs₀' : s₀ ^ 2 = b := by nlinarith [hs₀]
  have hrootsr : r = (r₀ : ℚ) ∨ r = -(r₀ : ℚ) := by
    have : r ^ 2 = (r₀ : ℚ) ^ 2 := by exact_mod_cast hr.trans (by exact_mod_cast hr₀'.symm)
    exact (sq_eq_sq_iff_eq_or_eq_neg).mp this
  have hrootss : s = (s₀ : ℚ) ∨ s = -(s₀ : ℚ) := by
    have : s ^ 2 = (s₀ : ℚ) ^ 2 := by exact_mod_cast hs.trans (by exact_mod_cast hs₀'.symm)
    exact (sq_eq_sq_iff_eq_or_eq_neg).mp this
  rcases hrootsr with hrsgn | hrsgn <;> rcases hrootss with hssgn | hssgn
  all_goals
    rw [hrsgn, hssgn] at hsum
  · refine ⟨r₀, s₀, hr₀', hs₀', ?_⟩
    exact_mod_cast ((div_eq_iff hoQ).mp hsum).trans (mul_comm _ _)
  · refine ⟨r₀, -s₀, hr₀', by simpa using hs₀', ?_⟩
    exact_mod_cast ((div_eq_iff hoQ).mp hsum).trans (mul_comm _ _)
  · refine ⟨-r₀, s₀, by simpa using hr₀', hs₀', ?_⟩
    exact_mod_cast ((div_eq_iff hoQ).mp hsum).trans (mul_comm _ _)
  · refine ⟨-r₀, -s₀, by simpa using hr₀', by simpa using hs₀', ?_⟩
    exact_mod_cast ((div_eq_iff hoQ).mp hsum).trans (mul_comm _ _)

/-- The strict square bounds become one-unit root bounds after integrality. -/
theorem root_abs_le {a V r : ℤ} (hV : 0 < V) (ha : a < V ^ 2)
    (hr : r ^ 2 = a) : |r| ≤ V - 1 := by
  have h := abs_lt_of_sq_lt_sq (hr.trans_lt ha) (le_of_lt hV)
  omega

/-- The weighted signed-root offset remains positive for either sign choice. -/
theorem offset_pos {a b V W r s : ℤ} (hV : 0 < V) (hW : 0 < W)
    (ha : a < V ^ 2) (hb : b < W ^ 2) (hr : r ^ 2 = a) (hs : s ^ 2 = b) :
    1 ≤ V * W + r + V * s := by
  have hrlo := (abs_le.mp (root_abs_le hV ha hr)).1
  have hslo := (abs_le.mp (root_abs_le hW hb hs)).1
  have hmul := mul_le_mul_of_nonneg_left hslo (le_of_lt hV)
  nlinarith

/-- The final polynomial; `n` is the sole additional natural witness. -/
def value (a b V W u v M mu n : ℤ) : ℤ :=
  let omega := u * (2 * mu - 1)
  let theta := u * n + v - omega * (M + V * W)
  norm theta omega a V b

/-- Every zero recovers the two square tests, divisibility, and strict margin.
All bounds are explicit and refer only to the supplied arithmetic registers. -/
theorem conditions_of_value_zero {a b V W u v M mu : ℤ} {n : ℕ}
    (hV : 0 < V) (hW : 0 < W) (hb : 0 < b)
    (haV : a < V ^ 2) (hbW : b < W ^ 2)
    (hu : 0 < u) (hv : 0 < v) (hvM : v ≤ u * M)
    (hz : value a b V W u v M mu n = 0) :
    IsSquare a ∧ IsSquare b ∧ u ∣ v ∧ 0 < mu := by
  have hM : 0 < M := by nlinarith
  have homega : u * (2 * mu - 1) ≠ 0 :=
    mul_ne_zero (ne_of_gt hu) (by omega)
  obtain ⟨r, s, hr, hs, htheta⟩ :=
    integer_roots_of_norm_zero homega hV haV hb hz
  have hoff := offset_pos hV hW haV hbW hr hs
  have hZ : 0 < M + V * W + r + V * s := by omega
  have heq : u * n + v = u * (2 * mu - 1) * (M + V * W + r + V * s) := by
    linear_combination htheta
  refine ⟨⟨r, by nlinarith [hr]⟩, ⟨s, by nlinarith [hs]⟩, ?_, ?_⟩
  · refine ⟨(2 * mu - 1) * (M + V * W + r + V * s) - n, ?_⟩
    linear_combination heq
  · by_contra hm
    have hmul : u * (2 * mu - 1) * (M + V * W + r + V * s) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hu (by omega)) hZ
    have hleft : 0 < u * n + v := by positivity
    omega

/-- The four recovered arithmetic conditions construct a natural ninth witness. -/
theorem exists_value_zero_of_conditions {a b V W u v M mu : ℤ}
    (hV : 0 < V) (hW : 0 < W)
    (haV : a < V ^ 2) (hbW : b < W ^ 2)
    (hu : 0 < u) (hv : 0 < v) (hvM : v ≤ u * M)
    (ha : IsSquare a) (hb : IsSquare b) (hdiv : u ∣ v) (hmu : 0 < mu) :
    ∃ n : ℕ, value a b V W u v M mu n = 0 := by
  obtain ⟨r, hr⟩ := ha
  obtain ⟨s, hs⟩ := hb
  have hr' : r ^ 2 = a := by nlinarith [hr]
  have hs' : s ^ 2 = b := by nlinarith [hs]
  obtain ⟨k, hk⟩ := hdiv
  have hkM : k ≤ M := by nlinarith [hk]
  have hM : 0 < M := by nlinarith
  have hoff := offset_pos hV hW haV hbW hr' hs'
  let Z := M + V * W + r + V * s
  have hZ : M + 1 ≤ Z := by dsimp [Z]; omega
  have hZ0 : 0 ≤ Z := by omega
  have hmul : Z ≤ (2 * mu - 1) * Z := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * mu - 2 by omega) hZ0]
  have hn : 0 ≤ (2 * mu - 1) * Z - k := by omega
  refine ⟨((2 * mu - 1) * Z - k).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hn]
  dsimp [value, norm, Z]
  rw [hk, ← hr', ← hs']
  ring

/-- A one-natural-witness polynomial encoding of precisely the four conditions. -/
theorem exists_value_zero_iff {a b V W u v M mu : ℤ}
    (hV : 0 < V) (hW : 0 < W) (hb : 0 < b)
    (haV : a < V ^ 2) (hbW : b < W ^ 2)
    (hu : 0 < u) (hv : 0 < v) (hvM : v ≤ u * M) :
    (∃ n : ℕ, value a b V W u v M mu n = 0) ↔
      IsSquare a ∧ IsSquare b ∧ u ∣ v ∧ 0 < mu := by
  constructor
  · rintro ⟨n, hn⟩
    exact conditions_of_value_zero hV hW hb haV hbW hu hv hvM hn
  · rintro ⟨ha, hb, hd, hm⟩
    exact exists_value_zero_of_conditions hV hW haV hbW hu hv hvM ha hb hd hm

end DiophantineConsistency.NearSquareFinalizer
