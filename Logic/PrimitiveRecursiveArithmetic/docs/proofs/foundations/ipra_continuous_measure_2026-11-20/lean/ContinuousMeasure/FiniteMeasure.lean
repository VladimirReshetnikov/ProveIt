import Std
import Init.Data.Rat.Lemmas

/-!
# Finite rational measure arithmetic

These are ordinary Lean theorems about exact rational programs. They are not
new object-language `Prf PRAAx` derivations. The report gives the separate
denominator-clearing and quantifier-free-induction route to that endpoint.

All row lengths are genuine natural-number parameters, not externally
unrolled lists. Every calculation is a finite primitive recursion.
-/

namespace IPRAContinuousMeasure

/-- Sum of the first `n` entries of a rational row. -/
def qsum (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => qsum f n + f n

/-- Unnormalised finite integration. -/
def integrate (n : Nat) (w f : Nat → Rat) : Rat :=
  qsum (fun i => w i * f i) n

/-- A rational error bound, expressed without a discontinuous choice of sign. -/
def Within (e a b : Rat) : Prop := a - b ≤ e ∧ b - a ≤ e

theorem qsum_ext {n : Nat} {f g : Nat → Rat}
    (h : ∀ i, i < n → f i = g i) : qsum f n = qsum g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [qsum]
      rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem qsum_zero (n : Nat) : qsum (fun _ => (0 : Rat)) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [qsum, ih, Rat.add_zero]

theorem qsum_add (f g : Nat → Rat) (n : Nat) :
    qsum (fun i => f i + g i) n = qsum f n + qsum g n := by
  induction n with
  | zero => simp only [qsum, Rat.add_zero]
  | succ n ih => simp only [qsum, ih]; grind

theorem qsum_scale (c : Rat) (f : Nat → Rat) (n : Nat) :
    qsum (fun i => c * f i) n = c * qsum f n := by
  induction n with
  | zero => simp only [qsum, Rat.mul_zero]
  | succ n ih => simp only [qsum, ih, Rat.mul_add]

theorem qsum_mono {n : Nat} {f g : Nat → Rat}
    (h : ∀ i, i < n → f i ≤ g i) : qsum f n ≤ qsum g n := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
      have h₁ := ih (fun i hi => h i (by omega))
      have h₂ := h n (by omega)
      simp only [qsum]
      grind

theorem qsum_nonneg {n : Nat} {f : Nat → Rat}
    (h : ∀ i, i < n → 0 ≤ f i) : 0 ≤ qsum f n := by
  have hs := qsum_mono h
  simpa only [qsum_zero] using hs

theorem qsum_exchange (f : Nat → Nat → Rat) (m n : Nat) :
    qsum (fun i => qsum (f i) n) m =
      qsum (fun j => qsum (fun i => f i j) m) n := by
  induction m with
  | zero => simp only [qsum, qsum_zero]
  | succ m ih =>
      simp only [qsum]
      rw [qsum_add, ih]

theorem qsum_single (c : Rat) {n k : Nat} (hk : k < n) :
    qsum (fun i => if i = k then c else 0) n = c := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hkn : k = n
      · subst k
        have hz : qsum (fun i => if i = n then c else 0) n = 0 := by
          calc
            _ = qsum (fun _ => 0) n := qsum_ext (by
              intro i hi
              exact if_neg (by omega))
            _ = 0 := qsum_zero n
        simp [qsum, hz, Rat.zero_add]
      · have hn : k < n := by omega
        simp only [qsum, ih hn, if_neg (Ne.symm hkn), Rat.add_zero]

theorem integrate_add (n : Nat) (w f g : Nat → Rat) :
    integrate n w (fun i => f i + g i) =
      integrate n w f + integrate n w g := by
  simp only [integrate, Rat.mul_add, qsum_add]

theorem integrate_const (n : Nat) (w : Nat → Rat) (c : Rat) :
    integrate n w (fun _ => c) = c * qsum w n := by
  unfold integrate
  have h : (fun i => w i * c) = (fun i => c * w i) := by
    funext i
    exact Rat.mul_comm _ _
  rw [h, qsum_scale]

theorem integrate_nonneg {n : Nat} {w f : Nat → Rat}
    (hw : ∀ i, i < n → 0 ≤ w i)
    (hf : ∀ i, i < n → 0 ≤ f i) : 0 ≤ integrate n w f :=
  qsum_nonneg (fun i hi => Rat.mul_nonneg (hw i hi) (hf i hi))

theorem integrate_mono {n : Nat} {w f g : Nat → Rat}
    (hw : ∀ i, i < n → 0 ≤ w i)
    (hfg : ∀ i, i < n → f i ≤ g i) :
    integrate n w f ≤ integrate n w g :=
  qsum_mono (fun i hi => Rat.mul_le_mul_of_nonneg_left (hfg i hi) (hw i hi))

theorem within_abs_iff (e a b : Rat) : Within e a b ↔ (a - b).abs ≤ e := by
  unfold Within
  by_cases h : 0 ≤ a - b
  · rw [Rat.abs_of_nonneg h]
    constructor
    · exact And.left
    · intro he
      constructor
      · exact he
      · grind
  · have hn : a - b ≤ 0 := by grind
    rw [Rat.abs_of_nonpos hn]
    constructor
    · intro he
      grind
    · intro he
      constructor <;> grind

theorem within_refl {e a : Rat} (he : 0 ≤ e) : Within e a a := by
  constructor <;> simpa only [Rat.sub_self] using he

theorem within_symm {e a b : Rat} (h : Within e a b) : Within e b a :=
  ⟨h.2, h.1⟩

theorem within_mono {e d a b : Rat} (h : Within e a b) (hed : e ≤ d) :
    Within d a b := ⟨Rat.le_trans h.1 hed, Rat.le_trans h.2 hed⟩

theorem within_triangle {e d a b c : Rat}
    (h₁ : Within e a b) (h₂ : Within d b c) : Within (e + d) a c := by
  rcases h₁ with ⟨h₁, h₂'⟩
  rcases h₂ with ⟨h₃, h₄⟩
  constructor <;> grind

theorem within_add {e d a b c z : Rat}
    (h₁ : Within e a b) (h₂ : Within d c z) :
    Within (e + d) (a + c) (b + z) := by
  rcases h₁ with ⟨h₁, h₂'⟩
  rcases h₂ with ⟨h₃, h₄⟩
  constructor <;> grind

theorem within_scale {e a b c : Rat} (hc : 0 ≤ c) (h : Within e a b) :
    Within (c * e) (c * a) (c * b) := by
  have h₁ := Rat.mul_le_mul_of_nonneg_left h.1 hc
  have h₂ := Rat.mul_le_mul_of_nonneg_left h.2 hc
  constructor <;> grind

theorem within_qsum {n : Nat} {e f g : Nat → Rat}
    (h : ∀ i, i < n → Within (e i) (f i) (g i)) :
    Within (qsum e n) (qsum f n) (qsum g n) := by
  induction n with
  | zero => exact within_refl Rat.le_refl
  | succ n ih =>
      exact within_add (ih (fun i hi => h i (by omega))) (h n (by omega))

/-- The exact finite integral inequality underlying nonexpansive expectation. -/
theorem expectation_error {n : Nat} {w f g e : Nat → Rat}
    (hw : ∀ i, i < n → 0 ≤ w i)
    (hfg : ∀ i, i < n → Within (e i) (f i) (g i)) :
    Within (integrate n w e) (integrate n w f) (integrate n w g) :=
  within_qsum (fun i hi => within_scale (hw i hi) (hfg i hi))

theorem probability_nonexpansive {n : Nat} {w f g : Nat → Rat} {e : Rat}
    (hw : ∀ i, i < n → 0 ≤ w i) (hmass : qsum w n = 1)
    (hfg : ∀ i, i < n → Within e (f i) (g i)) :
    Within e (integrate n w f) (integrate n w g) := by
  have h := expectation_error hw hfg
  simpa only [integrate_const, hmass, Rat.mul_one] using h

/-- A product with one uncertain factor has an error bounded by the product
of the two absolute error envelopes. -/
theorem weight_product_error {w v b B : Rat}
    (hb : b.abs ≤ B) : Within (B * (w - v).abs) (w * b) (v * b) := by
  have hwv : Within ((w - v).abs) w v :=
    (within_abs_iff _ _ _).mpr Rat.le_refl
  have hbb : Within B b 0 := by
    apply (within_abs_iff _ _ _).mpr
    have h : b - 0 = b := by grind
    rw [h]
    exact hb
  have hAbs : 0 ≤ (w - v).abs := Rat.abs_nonneg
  have hB : 0 ≤ B := Rat.le_trans Rat.abs_nonneg hb
  have hbHi : b ≤ B := by have := hbb.1; grind
  have hbLo : -B ≤ b := by have := hbb.2; grind
  have hdHi : w - v ≤ (w - v).abs := hwv.1
  have hdLo : -(w - v).abs ≤ w - v := by have := hwv.2; grind
  by_cases hb0 : 0 ≤ b
  · have h₁ := Rat.mul_le_mul_of_nonneg_right hdHi hb0
    have h₂ := Rat.mul_le_mul_of_nonneg_right hdLo hb0
    have h₃ := Rat.mul_le_mul_of_nonneg_left hbHi hAbs
    constructor <;> grind
  · have hb0' : 0 ≤ -b := by grind
    have h₁ := Rat.mul_le_mul_of_nonneg_right hdHi hb0'
    have h₂ := Rat.mul_le_mul_of_nonneg_right hdLo hb0'
    have h₃ := Rat.mul_le_mul_of_nonneg_left (a := -b) (b := B) (by grind) hAbs
    constructor <;> grind

/-- Perturb both samples and the finite mass vector. There is no positivity
assumption on the second mass vector; only the first is used as the reference. -/
theorem mass_perturbation {n : Nat} {w v f g e : Nat → Rat} {B : Rat}
    (hw : ∀ i, i < n → 0 ≤ w i)
    (hfg : ∀ i, i < n → Within (e i) (f i) (g i))
    (hg : ∀ i, i < n → (g i).abs ≤ B) :
    Within (integrate n w e + B * qsum (fun i => (w i - v i).abs) n)
      (integrate n w f) (integrate n v g) := by
  have hs := within_qsum (fun i hi => weight_product_error
    (w := w i) (v := v i) (hg i hi))
  rw [qsum_scale] at hs
  exact within_triangle (expectation_error hw hfg) hs

end IPRAContinuousMeasure
