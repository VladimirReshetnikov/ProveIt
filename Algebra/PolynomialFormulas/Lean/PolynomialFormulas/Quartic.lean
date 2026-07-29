import PolynomialFormulas.Cubic

/-!
# Ferrari's quartic formula

The quartic is normalized and translated to `y⁴ + p y² + q y + r`.  Ferrari's
resolvent parameters factor that polynomial into two quadratics, whose four
quadratic-formula roots form the solver output.
-/

namespace LeanProofs.PolynomialFormulas

section Field

variable {K : Type*} [Field K]

/-- Evaluation of `a x⁴ + b x³ + c x² + d x + e`. -/
def quartic (a b c d e x : K) : K :=
  a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e

/-- Evaluation of the monic quartic `x⁴ + A x³ + B x² + C x + D`. -/
def monicQuartic (A B C D x : K) : K :=
  x ^ 4 + A * x ^ 3 + B * x ^ 2 + C * x + D

/-- Evaluation of the depressed quartic `y⁴ + p y² + q y + r`. -/
def depressedQuartic (p q r y : K) : K := y ^ 4 + p * y ^ 2 + q * y + r

/-- The quadratic coefficient after translating `x = y - A/4`. -/
def quarticP (A B : K) : K := B - 6 * (A / 4) ^ 2

/-- The linear coefficient after translating `x = y - A/4`. -/
def quarticQ (A B C : K) : K := C - 2 * B * (A / 4) + 8 * (A / 4) ^ 3

/-- The constant coefficient after translating `x = y - A/4`. -/
def quarticR (A B C D : K) : K :=
  D - C * (A / 4) + B * (A / 4) ^ 2 - 3 * (A / 4) ^ 4

/-- Ferrari's cubic resolvent, in denominator-free factored form. -/
def ferrariResolvent (p q r m : K) : K :=
  q ^ 2 - 4 * (2 * m - p) * (m ^ 2 - r)

/-- The four roots of a depressed quartic after Ferrari's factorization. -/
def solveDepressedQuartic (_m s _t ρ σ : K) : Fin 4 → K :=
  ![(s + ρ) / 2, (s - ρ) / 2, (-s + σ) / 2, (-s - σ) / 2]

/-- The four Ferrari values for a general quartic. -/
def solveQuartic (a b _c _d _e m s t ρ σ : K) : Fin 4 → K :=
  fun i => solveDepressedQuartic m s t ρ σ i - (b / a) / 4

/-- Dividing by the leading coefficient turns a general quartic into a monic one. -/
theorem quartic_normalization {a b c d e x : K} (ha : a ≠ 0) :
    quartic a b c d e x =
      a * monicQuartic (b / a) (c / a) (d / a) (e / a) x := by
  unfold quartic monicQuartic
  field_simp [ha]

/-- Ferrari's three parameter equations give the difference-of-squares factorization. -/
theorem ferrari_factorization {p q r m s t y : K}
    (hs : s ^ 2 = 2 * m - p) (hst : 2 * s * t = -q)
    (ht : t ^ 2 = m ^ 2 - r) :
    depressedQuartic p q r y =
      (y ^ 2 - s * y + (m - t)) * (y ^ 2 + s * y + (m + t)) := by
  unfold depressedQuartic
  linear_combination (y ^ 2) * hs + y * hst + ht

variable [CharZero K]

/-- Translating a monic quartic by `A/4` removes its cubic term. -/
theorem depress_monic_quartic (A B C D y : K) :
    monicQuartic A B C D (y - A / 4) =
      depressedQuartic (quarticP A B) (quarticQ A B C) (quarticR A B C D) y := by
  unfold monicQuartic depressedQuartic quarticP quarticQ quarticR
  ring

/-- A nonzero square radical and a resolvent root produce Ferrari's remaining
parameter `t = -q/(2s)`. -/
theorem ferrari_parameters_of_resolvent {p q r m s : K}
    (hres : ferrariResolvent p q r m = 0)
    (hs : s ^ 2 = 2 * m - p) (hs0 : s ≠ 0) :
    2 * s * (-q / (2 * s)) = -q ∧
      (-q / (2 * s)) ^ 2 = m ^ 2 - r := by
  constructor
  · field_simp [hs0]
  · have hq : q ^ 2 = 4 * s ^ 2 * (m ^ 2 - r) := by
      unfold ferrariResolvent at hres
      calc
        q ^ 2 = 4 * (2 * m - p) * (m ^ 2 - r) := by linear_combination hres
        _ = 4 * s ^ 2 * (m ^ 2 - r) := by rw [hs]
    have hquot : (-q / (2 * s)) ^ 2 = q ^ 2 / (4 * s ^ 2) := by
      field_simp [hs0]
      ring
    rw [hquot, hq]
    field_simp [hs0]

/-- Every entry of the depressed-quartic solver is a root. -/
theorem solveDepressedQuartic_correct {p q r m s t ρ σ : K}
    (hs : s ^ 2 = 2 * m - p) (hst : 2 * s * t = -q)
    (ht : t ^ 2 = m ^ 2 - r)
    (hρ : ρ ^ 2 = s ^ 2 - 4 * (m - t))
    (hσ : σ ^ 2 = s ^ 2 - 4 * (m + t)) (i : Fin 4) :
    depressedQuartic p q r (solveDepressedQuartic m s t ρ σ i) = 0 := by
  rw [ferrari_factorization hs hst ht]
  fin_cases i
  · apply mul_eq_zero.mpr
    left
    change ((s + ρ) / 2) ^ 2 - s * ((s + ρ) / 2) + (m - t) = 0
    field_simp
    linear_combination hρ
  · apply mul_eq_zero.mpr
    left
    change ((s - ρ) / 2) ^ 2 - s * ((s - ρ) / 2) + (m - t) = 0
    field_simp
    linear_combination hρ
  · apply mul_eq_zero.mpr
    right
    change ((-s + σ) / 2) ^ 2 + s * ((-s + σ) / 2) + (m + t) = 0
    field_simp
    linear_combination hσ
  · apply mul_eq_zero.mpr
    right
    change ((-s - σ) / 2) ^ 2 + s * ((-s - σ) / 2) + (m + t) = 0
    field_simp
    linear_combination hσ

/-- Every root of the depressed quartic occurs in the four-entry Ferrari
collection. -/
theorem solveDepressedQuartic_exhaustive {p q r m s t ρ σ y : K}
    (hs : s ^ 2 = 2 * m - p) (hst : 2 * s * t = -q)
    (ht : t ^ 2 = m ^ 2 - r)
    (hρ : ρ ^ 2 = s ^ 2 - 4 * (m - t))
    (hσ : σ ^ 2 = s ^ 2 - 4 * (m + t))
    (hy : depressedQuartic p q r y = 0) :
    ∃ i, solveDepressedQuartic m s t ρ σ i = y := by
  rw [ferrari_factorization hs hst ht] at hy
  rcases mul_eq_zero.mp hy with hfirst | hsecond
  · have hquadratic : quadratic 1 (-s) (m - t) y = 0 := by
      simpa [quadratic, sub_eq_add_neg] using hfirst
    have hdisc : ρ ^ 2 = (-s) ^ 2 - 4 * 1 * (m - t) := by
      rw [hρ]
      ring
    rcases (quadratic_eq_zero_iff (a := (1 : K)) (b := -s)
      (c := m - t) (s := ρ) (x := y) one_ne_zero hdisc).mp hquadratic with h | h
    · exact ⟨0, by simpa [solveDepressedQuartic] using h.symm⟩
    · exact ⟨1, by simpa [solveDepressedQuartic] using h.symm⟩
  · have hquadratic : quadratic 1 s (m + t) y = 0 := by
      simpa [quadratic, sub_eq_add_neg] using hsecond
    have hdisc : σ ^ 2 = s ^ 2 - 4 * 1 * (m + t) := by
      rw [hσ]
      ring
    rcases (quadratic_eq_zero_iff (a := (1 : K)) (b := s)
      (c := m + t) (s := σ) (x := y) one_ne_zero hdisc).mp hquadratic with h | h
    · exact ⟨2, by simpa [solveDepressedQuartic] using h.symm⟩
    · exact ⟨3, by simpa [solveDepressedQuartic] using h.symm⟩

/-- Every entry computed by `solveQuartic` is a root of the input quartic. -/
theorem solveQuartic_correct {a b c d e m s t ρ σ : K} (ha : a ≠ 0)
    (hs : s ^ 2 = 2 * m - quarticP (b / a) (c / a))
    (hst : 2 * s * t = -quarticQ (b / a) (c / a) (d / a))
    (ht : t ^ 2 = m ^ 2 - quarticR (b / a) (c / a) (d / a) (e / a))
    (hρ : ρ ^ 2 = s ^ 2 - 4 * (m - t))
    (hσ : σ ^ 2 = s ^ 2 - 4 * (m + t)) (i : Fin 4) :
    quartic a b c d e (solveQuartic a b c d e m s t ρ σ i) = 0 := by
  rw [quartic_normalization ha]
  simp only [solveQuartic]
  rw [depress_monic_quartic]
  rw [solveDepressedQuartic_correct hs hst ht hρ hσ i]
  ring

/-- Every root of the input quartic occurs in `solveQuartic`. -/
theorem solveQuartic_exhaustive {a b c d e m s t ρ σ x : K} (ha : a ≠ 0)
    (hs : s ^ 2 = 2 * m - quarticP (b / a) (c / a))
    (hst : 2 * s * t = -quarticQ (b / a) (c / a) (d / a))
    (ht : t ^ 2 = m ^ 2 - quarticR (b / a) (c / a) (d / a) (e / a))
    (hρ : ρ ^ 2 = s ^ 2 - 4 * (m - t))
    (hσ : σ ^ 2 = s ^ 2 - 4 * (m + t))
    (hx : quartic a b c d e x = 0) :
    ∃ i, solveQuartic a b c d e m s t ρ σ i = x := by
  have hmonic : monicQuartic (b / a) (c / a) (d / a) (e / a) x = 0 := by
    rw [quartic_normalization ha] at hx
    exact (mul_eq_zero.mp hx).resolve_left ha
  let y := x + (b / a) / 4
  have hdepressed :
      depressedQuartic (quarticP (b / a) (c / a))
        (quarticQ (b / a) (c / a) (d / a))
        (quarticR (b / a) (c / a) (d / a) (e / a)) y = 0 := by
    rw [← depress_monic_quartic]
    convert hmonic using 1
    dsimp [y]
    ring
  obtain ⟨i, hi⟩ := solveDepressedQuartic_exhaustive hs hst ht hρ hσ hdepressed
  refine ⟨i, ?_⟩
  simp only [solveQuartic]
  rw [hi]
  dsimp [y]
  ring

/-- The Ferrari collection contains exactly all roots of the quartic. -/
theorem quartic_eq_zero_iff {a b c d e m s t ρ σ x : K} (ha : a ≠ 0)
    (hs : s ^ 2 = 2 * m - quarticP (b / a) (c / a))
    (hst : 2 * s * t = -quarticQ (b / a) (c / a) (d / a))
    (ht : t ^ 2 = m ^ 2 - quarticR (b / a) (c / a) (d / a) (e / a))
    (hρ : ρ ^ 2 = s ^ 2 - 4 * (m - t))
    (hσ : σ ^ 2 = s ^ 2 - 4 * (m + t)) :
    quartic a b c d e x = 0 ↔
      ∃ i, solveQuartic a b c d e m s t ρ σ i = x := by
  constructor
  · exact solveQuartic_exhaustive ha hs hst ht hρ hσ
  · rintro ⟨i, rfl⟩
    exact solveQuartic_correct ha hs hst ht hρ hσ i

end Field

end LeanProofs.PolynomialFormulas
