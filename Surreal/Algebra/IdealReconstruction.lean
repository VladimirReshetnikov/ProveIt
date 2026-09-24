import Mathlib.Tactic

/-!
# Ring formulas reconstructing an ideal's multiplier ring

The fraction-pair formulas in `odg:def:cor:internal`. The ideal is
defined by the quadratic test; all witnesses belong to the original
ring, even when the represented fraction belongs only to its field.
-/

namespace Surreal.IdealReconstruction

noncomputable section

variable {R F : Type*} [CommRing R] [Field F]

/-- The parameter-free quadratic ideal test. -/
def Inf (x : R) : Prop := ∃ y : R, x ^ 2 = 2 * y ^ 2

/-- The printed multiplier formula on a fraction pair. -/
def Mult (a b : R) : Prop :=
  b ≠ 0 ∧ ∀ x : R, Inf x → ∃ y : R, Inf y ∧ a * x = b * y

/-- The printed coefficient formula, with a separate zero case. -/
def Coeff (a b : R) : Prop := b ≠ 0 ∧ (a = 0 ∨ (a ≠ 0 ∧ Mult a b ∧ Mult b a))

/-- Membership of a fraction in the original ideal, with an original-ring representative. -/
def IdealFraction (a b : R) : Prop := b ≠ 0 ∧ ∃ y : R, Inf y ∧ a = b * y

/-- The reconstructed coefficient graph on two fraction pairs. -/
def Graph (a b c d : R) : Prop :=
  Mult a b ∧ Coeff c d ∧ IdealFraction (a * d - c * b) (b * d)

/-- The semantic multiplier condition in the ambient field. -/
def Preserves (I : F → Prop) (f : F) : Prop := ∀ x, I x → I (f * x)

/-- A quadratic ideal definition and representatives for all ideal elements suffice. -/
theorem mult_iff (ι : R →+* F) (hι : Function.Injective ι) (I : F → Prop)
    (htest : ∀ x : R, Inf x ↔ I (ι x))
    (hrep : ∀ x : F, I x → ∃ y : R, ι y = x) (a b : R) :
    Mult a b ↔ b ≠ 0 ∧ Preserves I (ι a / ι b) := by
  have hn : ∀ x : R, x ≠ 0 → ι x ≠ 0 := fun x hx => (map_ne_zero_iff ι hι).mpr hx
  constructor
  · rintro ⟨hb, hm⟩
    refine ⟨hb, fun x hx => ?_⟩
    obtain ⟨x', rfl⟩ := hrep x hx
    obtain ⟨y, hy, he⟩ := hm x' ((htest x').mpr hx)
    have he' := congrArg ι he
    simp only [map_mul] at he'
    have hd : (ι a / ι b) * ι x' = ι y := by
      rw [div_mul_eq_mul_div, div_eq_iff (hn b hb)]
      simpa only [mul_comm] using he'
    rw [hd]
    exact (htest y).mp hy
  · rintro ⟨hb, hm⟩
    refine ⟨hb, fun x hx => ?_⟩
    have hy := hm (ι x) ((htest x).mp hx)
    obtain ⟨y, he⟩ := hrep _ hy
    refine ⟨y, (htest y).mpr (he ▸ hy), hι ?_⟩
    rw [map_mul, map_mul, he]
    field_simp [hn b hb]

/-- Zero and invertible multipliers give exactly the printed Coeff formula. -/
theorem coeff_iff (ι : R →+* F) (hι : Function.Injective ι) (I C : F → Prop)
    (htest : ∀ x : R, Inf x ↔ I (ι x))
    (hrep : ∀ x : F, I x → ∃ y : R, ι y = x)
    (hC : ∀ f : F, C f ↔ f = 0 ∨ (f ≠ 0 ∧ Preserves I f ∧ Preserves I f⁻¹))
    (a b : R) : Coeff a b ↔ b ≠ 0 ∧ C (ι a / ι b) := by
  rw [hC]
  have hn : ∀ x : R, x ≠ 0 → ι x ≠ 0 := fun x hx => (map_ne_zero_iff ι hι).mpr hx
  constructor
  · rintro ⟨hb, rfl | ⟨ha, hab, hba⟩⟩
    · exact ⟨hb, Or.inl (by simp)⟩
    · refine ⟨hb, Or.inr ⟨div_ne_zero (hn a ha) (hn b hb),
        ((mult_iff ι hι I htest hrep a b).mp hab).2, ?_⟩⟩
      simpa only [inv_div] using ((mult_iff ι hι I htest hrep b a).mp hba).2
  · rintro ⟨hb, hz | ⟨hf, hm, hi⟩⟩
    · refine ⟨hb, Or.inl ?_⟩
      exact (map_eq_zero_iff ι hι).mp ((div_eq_zero_iff.mp hz).resolve_right (hn b hb))
    · have ha : a ≠ 0 := by intro h; apply hf; simp [h]
      exact ⟨hb, Or.inr ⟨ha, (mult_iff ι hι I htest hrep a b).mpr ⟨hb, hm⟩,
        (mult_iff ι hι I htest hrep b a).mpr ⟨ha, by simpa only [inv_div] using hi⟩⟩⟩

/-- Mult depends only on the represented fraction, stated entirely by cross multiplication. -/
theorem mult_congr {a b c d : R} [IsDomain R] (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a * d = c * b) : Mult a b ↔ Mult c d := by
  suffices hf : ∀ a b c d : R, b ≠ 0 → d ≠ 0 → a * d = c * b → Mult a b → Mult c d from
    ⟨hf a b c d hb hd h, hf c d a b hd hb h.symm⟩
  intro a b c d hb hd h hm
  refine ⟨hd, fun x hx => ?_⟩
  obtain ⟨y, hy, he⟩ := hm.2 x hx
  refine ⟨y, hy, mul_left_cancel₀ hb ?_⟩
  calc
    b * (c * x) = (a * d) * x := by rw [h]; ring
    _ = d * (a * x) := by ring
    _ = d * (b * y) := by rw [he]
    _ = b * (d * y) := by ring

/-- Coeff is likewise invariant under nonzero-denominator changes of representative. -/
theorem coeff_congr {a b c d : R} [IsDomain R] (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a * d = c * b) : Coeff a b ↔ Coeff c d := by
  have hz : a = 0 ↔ c = 0 := by
    constructor
    · intro ha; have he := h; rw [ha, zero_mul] at he
      exact (mul_eq_zero.mp he.symm).resolve_right hb
    · intro hc; have he := h; rw [hc, zero_mul] at he
      exact (mul_eq_zero.mp he).resolve_right hd
  by_cases ha : a = 0
  · have hc := hz.mp ha
    simp [Coeff, ha, hc, hb, hd]
  · have hc : c ≠ 0 := fun he => ha (hz.mpr he)
    have hi : b * c = d * a := by rw [mul_comm b c, ← h]; ring
    simp only [Coeff, ne_eq, hb, hd, ha, hc, not_false_eq_true, false_or, true_and]
    exact and_congr (mult_congr hb hd h) (mult_congr ha hc hi)

/-- The ideal fraction formula denotes exactly the ambient ideal predicate. -/
theorem idealFraction_iff (ι : R →+* F) (hι : Function.Injective ι) (I : F → Prop)
    (htest : ∀ x : R, Inf x ↔ I (ι x))
    (hrep : ∀ x : F, I x → ∃ y : R, ι y = x) (a b : R) :
    IdealFraction a b ↔ b ≠ 0 ∧ I (ι a / ι b) := by
  constructor
  · rintro ⟨hb, y, hy, rfl⟩
    refine ⟨hb, ?_⟩
    rw [map_mul, mul_div_cancel_left₀ _ ((map_ne_zero_iff ι hι).mpr hb)]
    exact (htest y).mp hy
  · rintro ⟨hb, hi⟩
    obtain ⟨y, hy⟩ := hrep _ hi
    refine ⟨hb, y, (htest y).mpr (hy ▸ hi), hι ?_⟩
    rw [map_mul, hy, mul_div_cancel₀ _ ((map_ne_zero_iff ι hι).mpr hb)]

/-- Ideal membership of a fraction is independent of its representative. -/
theorem idealFraction_congr {a b c d : R} [IsDomain R] (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a * d = c * b) : IdealFraction a b ↔ IdealFraction c d := by
  suffices hf : ∀ a b c d : R, b ≠ 0 → d ≠ 0 → a * d = c * b →
      IdealFraction a b → IdealFraction c d from
    ⟨hf a b c d hb hd h, hf c d a b hd hb h.symm⟩
  intro a b c d hb hd h hi
  obtain ⟨_, y, hy, he⟩ := hi
  refine ⟨hd, y, hy, mul_left_cancel₀ hb ?_⟩
  calc
    b * c = a * d := by rw [h]; ring
    _ = b * (d * y) := by rw [he]; ring

/-- The reconstructed graph descends in both fraction coordinates. -/
theorem graph_congr [IsDomain R] {a b c d a' b' c' d' : R}
    (hb : b ≠ 0) (hd : d ≠ 0) (hb' : b' ≠ 0) (hd' : d' ≠ 0)
    (ha : a * b' = a' * b) (hc : c * d' = c' * d) :
    Graph a b c d ↔ Graph a' b' c' d' := by
  apply and_congr (mult_congr hb hb' ha)
  apply and_congr (coeff_congr hd hd' hc)
  apply idealFraction_congr (mul_ne_zero hb hd) (mul_ne_zero hb' hd')
  linear_combination (d * d') * ha - (b * b') * hc

/-- The full pair formula reconstructs the coefficient graph by subtraction into the ideal. -/
theorem graph_iff [IsDomain R] (ι : R →+* F) (hι : Function.Injective ι) (I C : F → Prop)
    (htest : ∀ x : R, Inf x ↔ I (ι x))
    (hrep : ∀ x : F, I x → ∃ y : R, ι y = x)
    (hC : ∀ f : F, C f ↔ f = 0 ∨ (f ≠ 0 ∧ Preserves I f ∧ Preserves I f⁻¹))
    (a b c d : R) : Graph a b c d ↔ b ≠ 0 ∧ d ≠ 0 ∧
      Preserves I (ι a / ι b) ∧ C (ι c / ι d) ∧ I (ι a / ι b - ι c / ι d) := by
  have hdiff (hb : b ≠ 0) (hd : d ≠ 0) :
      ι (a * d - c * b) / ι (b * d) = ι a / ι b - ι c / ι d := by
    rw [map_sub, map_mul, map_mul, map_mul]
    field_simp [(map_ne_zero_iff ι hι).mpr hb, (map_ne_zero_iff ι hι).mpr hd]
  rw [Graph, mult_iff ι hι I htest hrep, coeff_iff ι hι I C htest hrep hC,
    idealFraction_iff ι hι I htest hrep]
  constructor
  · rintro ⟨⟨hb, hm⟩, ⟨hd, hc⟩, _, hi⟩
    exact ⟨hb, hd, hm, hc, by rwa [← hdiff hb hd]⟩
  · rintro ⟨hb, hd, hm, hc, hi⟩
    exact ⟨⟨hb, hm⟩, ⟨hd, hc⟩, mul_ne_zero hb hd, by rwa [hdiff hb hd]⟩

end
end Surreal.IdealReconstruction
