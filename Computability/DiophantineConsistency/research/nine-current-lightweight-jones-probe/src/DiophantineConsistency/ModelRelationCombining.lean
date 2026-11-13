import DiophantineConsistency.JonesSyntaxCore
import DiophantineConsistency.ModelArithmetic
import DiophantineConsistency.ArithmeticSquareDivisibility

/-! # Two-radicand relation combining in every model of `𝗜𝚺₁`

Jones's nine-variable polynomial ends with the closed two-radicand combiner
`RefinedPair.value`. Externally its correctness is
`Diophantine.RefinedRelationCombining.relationCombining_iff`, proved with
complex square roots and algebraic independence. For two radicands an
elementary argument suffices, and it runs in any discretely ordered
commutative ring in which `m² ∣ s²` forces `m ∣ s`:

* the value is the product of the four signed factors
  `T ± K·r₀ ± K·V₀·r₁` whenever `A₀ = r₀²` and `A₁ = r₁²`;
* conversely a zero makes `A₀` a square by square divisibility (or forces
  `A₀ = A₁ = 0` when `T = 0`), then one factor vanishes and `A₁` is a square;
* the weights `Vᵢ = Aᵢ² + 2` exceed `|rᵢ|`, which turns the vanishing factor
  into `B ∣ C` and `0 < D`.

The model ring of differences `DiffRing V` satisfies both hypotheses
(`ModelArithmetic.model_discrete`, `sq_dvd_sq`), so the statement holds in
every model, with the combining witness a model natural. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelRelationCombining
open DiscreteOrderedRingFacts

section Generic
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The signed-factor form of the combiner, with `K = B(2D-1)` and
`T = Bn + C - K(C + V₀V₁)` written out. -/
theorem value_factor (A0 A1 V0 V1 n B C D r0 r1 : R) (h0 : A0 = r0 * r0) (h1 : A1 = r1 * r1) :
    RefinedPair.value A0 A1 V0 V1 n B C D =
      (B * n + C - B * (2 * D - 1) * (C + V0 * V1) + B * (2 * D - 1) * r0 +
          B * (2 * D - 1) * V0 * r1) *
        (B * n + C - B * (2 * D - 1) * (C + V0 * V1) + B * (2 * D - 1) * r0 -
          B * (2 * D - 1) * V0 * r1) *
        ((B * n + C - B * (2 * D - 1) * (C + V0 * V1) - B * (2 * D - 1) * r0 +
          B * (2 * D - 1) * V0 * r1) *
         (B * n + C - B * (2 * D - 1) * (C + V0 * V1) - B * (2 * D - 1) * r0 -
          B * (2 * D - 1) * V0 * r1)) := by
  subst h0 h1
  simp only [RefinedPair.value]
  ring

variable (hd : Discrete R)
include hd

theorem abs_le_sq (x : R) : |x| ≤ x ^ 2 := by
  rcases eq_or_ne x 0 with h | h
  · simp [h]
  · have h1 : 1 ≤ |x| := abs_ge_one hd h
    calc |x| = |x| * 1 := (mul_one _).symm
      _ ≤ |x| * |x| := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = x ^ 2 := by rw [← sq, sq_abs]

/-- A square root lies strictly below its weight. -/
theorem abs_root_lt_weight (r : R) : |r| + 1 ≤ (r * r) ^ 2 + 2 := by
  have h1 : |r| ≤ r * r := by rw [← sq]; exact abs_le_sq hd r
  have h2 : r * r ≤ (r * r) ^ 2 := le_trans (le_abs_self _) (abs_le_sq hd _)
  linarith

theorem two_mul_sub_one_ne_zero (D : R) : 2 * D - 1 ≠ 0 := by
  intro h
  have hD : 0 < D := by linarith
  have := hd D hD
  linarith

/-- The weights make the shifted target exceed `C`. -/
theorem margin_pos (A0 A1 C r0 r1 : R) (h0 : A0 = r0 * r0) (h1 : A1 = r1 * r1) :
    C + 1 ≤ C + (A0 ^ 2 + 2) * (A1 ^ 2 + 2) - r0 - (A0 ^ 2 + 2) * r1 := by
  have hr0 := abs_root_lt_weight hd r0
  have hr1 := abs_root_lt_weight hd r1
  rw [← h0] at hr0
  rw [← h1] at hr1
  have hV0 : (0 : R) ≤ A0 ^ 2 + 2 := by positivity
  have hb0 : r0 ≤ A0 ^ 2 + 2 - 1 := by linarith [le_abs_self r0]
  have hb1 : (A0 ^ 2 + 2) * r1 ≤ (A0 ^ 2 + 2) * (A1 ^ 2 + 2 - 1) :=
    mul_le_mul_of_nonneg_left (by linarith [le_abs_self r1]) hV0
  nlinarith

variable (hsq : ∀ m s : R, m ≠ 0 → m ^ 2 ∣ s ^ 2 → m ∣ s)
include hsq

/-- `s² = m²·A` with `m ≠ 0` makes `A` a square whose root divides out of `s`. -/
theorem square_of_mul (m s A : R) (hm : m ≠ 0) (h : s ^ 2 = m ^ 2 * A) :
    ∃ t, A = t * t ∧ s = m * t := by
  obtain ⟨t, ht⟩ := hsq m s hm ⟨A, h⟩
  refine ⟨t, ?_, ht⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 hm)
  rw [← h, ht]; ring

/-- The core of the converse, for free `K ≠ 0` and `T`. -/
theorem roots_core (A0 A1 K T : R) (hK0 : K ≠ 0)
    (hval : (T ^ 2 + K ^ 2 * A0 - K ^ 2 * (A0 ^ 2 + 2) ^ 2 * A1) ^ 2 -
      4 * T ^ 2 * K ^ 2 * A0 = 0) :
    ∃ r0 r1 : R, A0 = r0 * r0 ∧ A1 = r1 * r1 ∧ T + K * r0 + K * (A0 ^ 2 + 2) * r1 = 0 := by
  have hV0pos : (0 : R) < A0 ^ 2 + 2 := by positivity
  rcases eq_or_ne T 0 with hT0 | hT0
  · -- `T = 0` forces both radicands to vanish.
    subst hT0
    have hS : K ^ 2 * (A0 - (A0 ^ 2 + 2) ^ 2 * A1) = 0 := by
      have : (K ^ 2 * (A0 - (A0 ^ 2 + 2) ^ 2 * A1)) ^ 2 = 0 := by linear_combination hval
      exact (pow_eq_zero_iff two_ne_zero).mp this
    have hA : A0 = (A0 ^ 2 + 2) ^ 2 * A1 :=
      sub_eq_zero.mp ((mul_eq_zero.mp hS).resolve_left (pow_ne_zero 2 hK0))
    have hA1 : A1 = 0 := by
      by_contra hA1
      have h1 : 1 ≤ |A1| := abs_ge_one hd hA1
      have habs : |A0| = (A0 ^ 2 + 2) ^ 2 * |A1| := by
        conv_lhs => rw [hA]
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : R) ≤ (A0 ^ 2 + 2) ^ 2)]
      have hle : |A0| ≤ A0 ^ 2 := abs_le_sq hd A0
      have hV : A0 ^ 2 + 2 ≤ (A0 ^ 2 + 2) ^ 2 := by
        have := abs_le_sq hd (A0 ^ 2 + 2); rwa [abs_of_pos hV0pos] at this
      nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : R) ≤ (A0 ^ 2 + 2) ^ 2)]
    have hA0 : A0 = 0 := by rw [hA, hA1, mul_zero]
    exact ⟨0, 0, by rw [hA0, mul_zero], by rw [hA1, mul_zero], by ring⟩
  · -- `T ≠ 0`: square divisibility makes `A₀` a square.
    have hm : 2 * T * K ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hT0) hK0
    obtain ⟨t, ht, -⟩ := square_of_mul hd hsq (2 * T * K)
      (T ^ 2 + K ^ 2 * A0 - K ^ 2 * (A0 ^ 2 + 2) ^ 2 * A1) A0 hm (by linear_combination hval)
    have e : ((T + K * t) ^ 2 - (K * (A0 ^ 2 + 2)) ^ 2 * A1) *
        ((T - K * t) ^ 2 - (K * (A0 ^ 2 + 2)) ^ 2 * A1) =
        (T ^ 2 + K ^ 2 * A0 - K ^ 2 * (A0 ^ 2 + 2) ^ 2 * A1) ^ 2 - 4 * T ^ 2 * K ^ 2 * A0 := by
      rw [ht]; ring
    have hfac := e.trans hval
    have hKV : K * (A0 ^ 2 + 2) ≠ 0 := mul_ne_zero hK0 hV0pos.ne'
    rcases mul_eq_zero.mp hfac with h | h
    · obtain ⟨u, hu, hTu⟩ := square_of_mul hd hsq (K * (A0 ^ 2 + 2)) (T + K * t) A1 hKV
        (by linear_combination h)
      exact ⟨t, -u, ht, by rw [hu]; ring, by linear_combination hTu⟩
    · obtain ⟨u, hu, hTu⟩ := square_of_mul hd hsq (K * (A0 ^ 2 + 2)) (T - K * t) A1 hKV
        (by linear_combination h)
      exact ⟨-t, -u, by rw [ht]; ring, by rw [hu]; ring, by linear_combination hTu⟩

/-- A zero of the combiner yields square roots with a vanishing signed factor. -/
theorem roots_of_zero (A0 A1 n B C D : R) (hB : 0 < B)
    (hz : RefinedPair.value A0 A1 (A0 ^ 2 + 2) (A1 ^ 2 + 2) n B C D = 0) :
    ∃ r0 r1 : R, A0 = r0 * r0 ∧ A1 = r1 * r1 ∧
      B * n + C - B * (2 * D - 1) * (C + (A0 ^ 2 + 2) * (A1 ^ 2 + 2)) +
        B * (2 * D - 1) * r0 + B * (2 * D - 1) * (A0 ^ 2 + 2) * r1 = 0 := by
  have hK0 : B * (2 * D - 1) ≠ 0 := mul_ne_zero hB.ne' (two_mul_sub_one_ne_zero hd D)
  obtain ⟨r0, r1, h0, h1, h⟩ := roots_core hd hsq A0 A1 (B * (2 * D - 1))
    (B * n + C - B * (2 * D - 1) * (C + (A0 ^ 2 + 2) * (A1 ^ 2 + 2))) hK0 hz
  exact ⟨r0, r1, h0, h1, by linear_combination h⟩

/-- **Two-radicand relation combining** in a discretely ordered ring with
square divisibility: two squares, a divisibility and a positive margin hold
iff the combiner vanishes at a nonnegative witness. -/
theorem conditions_iff_value (A0 A1 B C D : R) (hB : 0 < B) (hC : 0 ≤ C) :
    (IsSquare A0 ∧ IsSquare A1 ∧ B ∣ C ∧ 0 < D) ↔
      ∃ n : R, 0 ≤ n ∧ RefinedPair.value A0 A1 (A0 ^ 2 + 2) (A1 ^ 2 + 2) n B C D = 0 := by
  constructor
  · rintro ⟨⟨r0, h0⟩, ⟨r1, h1⟩, ⟨c, hc⟩, hD⟩
    -- The all-plus factor with nonnegative roots vanishes.
    have h0' : A0 = |r0| * |r0| := by rw [h0, abs_mul_abs_self]
    have h1' : A1 = |r1| * |r1| := by rw [h1, abs_mul_abs_self]
    have hMC := margin_pos hd A0 A1 C |r0| |r1| h0' h1'
    obtain ⟨M, hM⟩ : ∃ M, M = C + (A0 ^ 2 + 2) * (A1 ^ 2 + 2) - |r0| - (A0 ^ 2 + 2) * |r1| :=
      ⟨_, rfl⟩
    rw [← hM] at hMC
    have hD1 : 1 ≤ D := hd D hD
    have hc0 : 0 ≤ c := by
      by_contra hneg
      have : B * c < 0 := mul_neg_of_pos_of_neg hB (lt_of_not_ge hneg)
      linarith
    have hcC : c ≤ C := by
      have hB1 : 1 ≤ B := hd B hB
      nlinarith [mul_nonneg (sub_nonneg.2 hB1) hc0]
    refine ⟨(2 * D - 1) * M - c, ?_, ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_right (show (1 : R) ≤ 2 * D - 1 by linarith)
        (show (0 : R) ≤ M by linarith)]
    · rw [value_factor A0 A1 (A0 ^ 2 + 2) (A1 ^ 2 + 2) _ B C D |r0| |r1| h0' h1']
      apply mul_eq_zero_of_left
      apply mul_eq_zero_of_left
      rw [hM, hc]; ring
  · rintro ⟨n, hn, hz⟩
    obtain ⟨r0, r1, h0, h1, hfac⟩ := roots_of_zero hd hsq A0 A1 n B C D hB hz
    have hMC := margin_pos hd A0 A1 C r0 r1 h0 h1
    obtain ⟨M, hM⟩ : ∃ M, M = C + (A0 ^ 2 + 2) * (A1 ^ 2 + 2) - r0 - (A0 ^ 2 + 2) * r1 :=
      ⟨_, rfl⟩
    rw [← hM] at hMC
    have hKM : B * n + C = B * (2 * D - 1) * M := by rw [hM]; linear_combination hfac
    refine ⟨⟨r0, h0⟩, ⟨r1, h1⟩, ⟨(2 * D - 1) * M - n, by linear_combination hKM⟩, ?_⟩
    have hBn : 0 ≤ B * n := mul_nonneg hB.le hn
    have hMpos : 0 < M := by linarith
    have hK : 0 ≤ B * (2 * D - 1) := by
      by_contra hneg
      have := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hMpos
      linarith
    have h2D : 0 ≤ 2 * D - 1 := by
      by_contra hneg
      have := mul_neg_of_pos_of_neg hB (lt_of_not_ge hneg)
      linarith
    have hpos : 0 < 2 * D - 1 := lt_of_le_of_ne h2D (Ne.symm (two_mul_sub_one_ne_zero hd D))
    linarith

end Generic

section Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ModelArithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Square divisibility in the ring of differences of a model. -/
theorem sq_dvd_sq (m s : DiffRing V) (hm : m ≠ 0) (h : m ^ 2 ∣ s ^ 2) : m ∣ s := by
  rcases eq_or_ne s 0 with hs | hs
  · rw [hs]; exact dvd_zero m
  obtain ⟨a, ha⟩ := nonneg_iff.mp (abs_nonneg m)
  obtain ⟨b, hb⟩ := nonneg_iff.mp (abs_nonneg s)
  obtain ⟨t, ht⟩ := h
  have hm2 : (0 : DiffRing V) < m ^ 2 := lt_of_le_of_ne (sq_nonneg m) (Ne.symm (pow_ne_zero 2 hm))
  have hs2 : (0 : DiffRing V) < s ^ 2 := lt_of_le_of_ne (sq_nonneg s) (Ne.symm (pow_ne_zero 2 hs))
  have ht0 : 0 ≤ t := by
    by_contra hneg
    have : m ^ 2 * t < 0 := mul_neg_of_pos_of_neg hm2 (lt_of_not_ge hneg)
    rw [← ht] at this
    exact absurd this (not_lt.mpr hs2.le)
  obtain ⟨c, hc⟩ := nonneg_iff.mp ht0
  have hab : ι (b * b) = ι (a * a * c) := by
    rw [map_mul, map_mul, map_mul, ← ha, ← hb, ← hc, abs_mul_abs_self, abs_mul_abs_self,
      ← sq, ← sq, ht]
  have hV : b * b = a * a * c := ι_injective hab
  have ha0 : 0 < a := by
    rcases eq_zero_or_pos a with h0 | h0
    · exfalso; apply hm; rw [← abs_eq_zero, ha, h0, map_zero]
    · exact h0
  obtain ⟨d, hdab⟩ := ArithmeticSquareDivisibility.dvd_of_square_dvd a b ha0 ⟨c, hV⟩
  have habs : |m| ∣ |s| := ⟨ι d, by rw [ha, hb, hdab, map_mul]⟩
  exact (abs_dvd_abs m s).mp habs

/-- **Two-radicand relation combining in every model of `𝗜𝚺₁`**, with the
combining witness a model natural. -/
theorem model_conditions_iff_value (A0 A1 B C D : DiffRing V) (hB : 0 < B) (hC : 0 ≤ C) :
    (IsSquare A0 ∧ IsSquare A1 ∧ B ∣ C ∧ 0 < D) ↔
      ∃ n : V, RefinedPair.value A0 A1 (A0 ^ 2 + 2) (A1 ^ 2 + 2) (ι n) B C D = 0 := by
  rw [conditions_iff_value model_discrete sq_dvd_sq A0 A1 B C D hB hC]
  constructor
  · rintro ⟨n, hn, hz⟩
    obtain ⟨a, rfl⟩ := nonneg_iff.mp hn
    exact ⟨a, hz⟩
  · rintro ⟨a, hz⟩
    exact ⟨ι a, ι_nonneg a, hz⟩

end Model

end DiophantineConsistency.ModelRelationCombining
