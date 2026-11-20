import ContinuousMeasure.FiniteMeasure

/-!
# Stable clipping and the finite Vitali inequality

Hard threshold-event indicators are absent from the estimate. The error is
measured by the bounded continuous test `min(1, |x-y|)` and by clipping tails.
This is the finite arithmetic needed before passing to effective L1 names.
-/

namespace IPRAContinuousMeasure

def clip (K x : Rat) : Rat :=
  if x < -K then -K else if K < x then K else x

def positivePart (x : Rat) : Rat := if 0 ≤ x then x else 0

def tail (K x : Rat) : Rat := (x - clip K x).abs

def cappedDistance (x y : Rat) : Rat :=
  if (x - y).abs ≤ 1 then (x - y).abs else 1

theorem clip_bounds {K x : Rat} (hK : 0 ≤ K) :
    -K ≤ clip K x ∧ clip K x ≤ K := by
  grind [clip]

theorem clip_nonexpansive {K e x y : Rat} (hK : 0 ≤ K)
    (h : Within e x y) : Within e (clip K x) (clip K y) := by
  rcases h with ⟨h₁, h₂⟩
  constructor <;> grind [clip]

theorem clip_diameter {K x y : Rat} (hK : 0 ≤ K) :
    Within (2 * K) (clip K x) (clip K y) := by
  have hx := clip_bounds (x := x) hK
  have hy := clip_bounds (x := y) hK
  constructor <;> grind

theorem tail_nonneg (K x : Rat) : 0 ≤ tail K x := Rat.abs_nonneg

theorem tail_formula {K x : Rat} (hK : 0 ≤ K) :
    tail K x = positivePart (x.abs - K) := by
  unfold tail
  by_cases hlo : x < -K
  · have hx : x ≤ 0 := by grind
    have hd : x - clip K x ≤ 0 := by grind [clip]
    rw [Rat.abs_of_nonpos hd, Rat.abs_of_nonpos hx]
    grind [clip, positivePart]
  · by_cases hhi : K < x
    · have hx : 0 ≤ x := by grind
      have hd : 0 ≤ x - clip K x := by grind [clip]
      rw [Rat.abs_of_nonneg hd, Rat.abs_of_nonneg hx]
      grind [clip, positivePart]
    · have hc : clip K x = x := by grind [clip]
      rw [hc, Rat.sub_self, Rat.abs_zero]
      by_cases hx : 0 ≤ x
      · rw [Rat.abs_of_nonneg hx]
        grind [positivePart]
      · have hx' : x ≤ 0 := by grind
        rw [Rat.abs_of_nonpos hx']
        grind [positivePart]

theorem positivePart_nonexpansive {e x y : Rat} (h : Within e x y) :
    Within e (positivePart x) (positivePart y) := by
  rcases h with ⟨h₁, h₂⟩
  constructor <;> grind [positivePart]

theorem abs_nonexpansive {e x y : Rat} (h : Within e x y) :
    Within e x.abs y.abs := by
  by_cases hx : 0 ≤ x
  · rw [Rat.abs_of_nonneg hx]
    by_cases hy : 0 ≤ y
    · rw [Rat.abs_of_nonneg hy]
      exact h
    · have hy' : y ≤ 0 := by grind
      rw [Rat.abs_of_nonpos hy']
      rcases h with ⟨h₁, h₂⟩
      constructor <;> grind
  · have hx' : x ≤ 0 := by grind
    rw [Rat.abs_of_nonpos hx']
    by_cases hy : 0 ≤ y
    · rw [Rat.abs_of_nonneg hy]
      rcases h with ⟨h₁, h₂⟩
      constructor <;> grind
    · have hy' : y ≤ 0 := by grind
      rw [Rat.abs_of_nonpos hy']
      rcases h with ⟨h₁, h₂⟩
      constructor <;> grind

theorem tail_nonexpansive {K e x y : Rat} (hK : 0 ≤ K)
    (h : Within e x y) : Within e (tail K x) (tail K y) := by
  rw [tail_formula hK, tail_formula hK]
  apply positivePart_nonexpansive
  have habs := abs_nonexpansive h
  constructor
  · have := habs.1; grind
  · have := habs.2; grind

theorem cappedDistance_nonneg (x y : Rat) : 0 ≤ cappedDistance x y := by
  have h : 0 ≤ (x - y).abs := Rat.abs_nonneg
  grind [cappedDistance]

theorem cappedDistance_le_one (x y : Rat) : cappedDistance x y ≤ 1 := by
  grind [cappedDistance]

theorem clipped_capped_bound {K C x y : Rat} (hK : 0 ≤ K)
    (hC : 1 ≤ C) (hKC : 2 * K ≤ C) :
    Within (C * cappedDistance x y) (clip K x) (clip K y) := by
  by_cases hd : (x - y).abs ≤ 1
  · have hbase := clip_nonexpansive hK
      ((within_abs_iff (x - y).abs x y).mpr Rat.le_refl)
    have hm := Rat.mul_le_mul_of_nonneg_right hC
      (Rat.abs_nonneg (x := x - y))
    have he : (x - y).abs ≤ C * cappedDistance x y := by
      simp only [cappedDistance, if_pos hd]
      simpa only [Rat.one_mul] using hm
    exact within_mono hbase he
  · have he : 2 * K ≤ C * cappedDistance x y := by
      simpa only [cappedDistance, if_neg hd, Rat.mul_one] using hKC
    exact within_mono (clip_diameter hK) he

/-- Stable replacement for an unsafe split using unrelated hard-tail events. -/
theorem scalar_vitali {K C x y : Rat} (hK : 0 ≤ K)
    (hC : 1 ≤ C) (hKC : 2 * K ≤ C) :
    (x - y).abs ≤ tail K x + tail K y + C * cappedDistance x y := by
  have hx : Within (tail K x) x (clip K x) :=
    (within_abs_iff _ _ _).mpr Rat.le_refl
  have hy : Within (tail K y) (clip K y) y := within_symm
    ((within_abs_iff _ _ _).mpr (Rat.le_refl (a := (y - clip K y).abs)))
  have hc := clipped_capped_bound (x := x) (y := y) hK hC hKC
  have h := (within_abs_iff _ _ _).mp (within_triangle (within_triangle hx hc) hy)
  have he : tail K x + C * cappedDistance x y + tail K y =
      tail K x + tail K y + C * cappedDistance x y := by grind
  rw [he] at h
  exact h

/-- The useful unit-cutoff specialization needs only K ≥ 1. -/
theorem scalar_vitali_unit {K x y : Rat} (hK : 1 ≤ K) :
    (x - y).abs ≤ tail K x + tail K y + 2 * K * cappedDistance x y :=
  scalar_vitali (by grind) (by grind) Rat.le_refl

/-- A variable-size, arbitrary nonnegative finite measure version of Vitali.
The total mass need not be one. -/
theorem finite_vitali {n : Nat} {w f g : Nat → Rat} {K C : Rat}
    (hw : ∀ i, i < n → 0 ≤ w i) (hK : 0 ≤ K)
    (hC : 1 ≤ C) (hKC : 2 * K ≤ C) :
    integrate n w (fun i => (f i - g i).abs) ≤
      integrate n w (fun i => tail K (f i)) +
      integrate n w (fun i => tail K (g i)) +
      C * integrate n w (fun i => cappedDistance (f i) (g i)) := by
  have h := integrate_mono hw
    (fun i _ => scalar_vitali (x := f i) (y := g i) hK hC hKC)
  simp only [integrate_add] at h
  have hs : integrate n w (fun i => C * cappedDistance (f i) (g i)) =
      C * integrate n w (fun i => cappedDistance (f i) (g i)) := by
    unfold integrate
    have he : (fun i => w i * (C * cappedDistance (f i) (g i))) =
        (fun i => C * (w i * cappedDistance (f i) (g i))) := by
      funext i
      grind
    rw [he, qsum_scale]
  rw [hs] at h
  exact h

theorem finite_vitali_unit {n : Nat} {w f g : Nat → Rat} {K : Rat}
    (hw : ∀ i, i < n → 0 ≤ w i) (hK : 1 ≤ K) :
    integrate n w (fun i => (f i - g i).abs) ≤
      integrate n w (fun i => tail K (f i)) +
      integrate n w (fun i => tail K (g i)) +
      2 * K * integrate n w (fun i => cappedDistance (f i) (g i)) :=
  finite_vitali hw (by grind) (by grind) Rat.le_refl

/-- A precision budget usable after supplying a cutoff and a convergence-in-
measure estimate. All three hypotheses remain visible. -/
theorem vitali_budget {n : Nat} {w f g : Nat → Rat} {K ε : Rat}
    (hw : ∀ i, i < n → 0 ≤ w i) (hK : 1 ≤ K)
    (hf : integrate n w (fun i => tail K (f i)) ≤ ε / 4)
    (hg : integrate n w (fun i => tail K (g i)) ≤ ε / 4)
    (hrho : 2 * K * integrate n w (fun i => cappedDistance (f i) (g i)) ≤ ε / 4) :
    integrate n w (fun i => (f i - g i).abs) ≤ 3 * ε / 4 := by
  have h := finite_vitali_unit (f := f) (g := g) hw hK
  grind

end IPRAContinuousMeasure
