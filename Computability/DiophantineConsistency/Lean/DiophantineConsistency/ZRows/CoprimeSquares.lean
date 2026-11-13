import DiophantineConsistency.ZRows.ModelFermat

/-! # Coprime factors of a square in models of `𝗜𝚺₁`

In every model `V` of `𝗜𝚺₁`, with coprimality stated as a natural Bezout certificate
`Bez a b 1` (equivalently `∃ α β, ι a·α + ι b·β = 1` in the ring of differences,
`ModelBetaFunction.bez_one_iff_ring`, or "no common irreducible divisor",
`bez_of_no_common_irred`):

* `square_of_mul_square`: if `a·b = c²` and `a`, `b` are coprime, then `a = d²` with
  `d = gcd(a, c)`. No induction is used: `d ∣ a` and `d ∣ c` give `d² ∣ c² = a·b`, and `d` is
  coprime to `b`, so `d² ∣ a`; conversely the Bezout identity `d = αa + βc` squares to
  `d² = a·(α²a + 2αβc + β²b)`, so `a ∣ d²`;
* `squares_of_mul_square`, `squares_of_mul_mul_square`: both factors of a coprime product, and
  all three factors of a pairwise coprime triple product, that is a square are squares;
* `abs_squares_of_mul_square`, `abs_squares_of_mul_mul_square`: the same in `DiffRing V`, where
  the absolute values of the factors are squares;
* `dvd_of_mul_self_dvd_mul_self`: `b² ∣ a²` implies `b ∣ a` (a rational number with an
  integral square is integral), with the signed form `dvd_of_sq_dvd_sq_ring`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ZRowsCoprimeSquares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticGcdNormalization ModelBetaFunction ModelBoundedForallArith
open ModelFermat

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Divisibility through the ring of differences -/

theorem ι_dvd_iff {a x : V} : (ι a : DiffRing V) ∣ ι x ↔ a ∣ x := by
  constructor
  · rintro ⟨q, hq⟩
    rcases nonneg_or_nonpos q with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact ⟨c, ι_injective (by rw [hq, map_mul])⟩
    · have hx : x = 0 := ι_eq_neg_ι (b := a * c) (by rw [hq, map_mul]; ring)
      rw [hx]
      exact dvd_zero a
  · rintro ⟨c, rfl⟩
    exact ⟨ι c, map_mul _ _ _⟩

/-- A divisor of a coprime element stays coprime. -/
theorem bez_of_dvd_left {a b g : V} (hab : Bez a b 1) (hg : g ∣ a) : Bez g b 1 := by
  obtain ⟨α, β, h⟩ := bez_one_iff_ring.mp hab
  obtain ⟨a', rfl⟩ := hg
  exact bez_one_iff_ring.mpr ⟨ι a' * α, β, by rw [← h, map_mul]; ring⟩

theorem bez_mul_right {a b b' : V} (h : Bez a b 1) (h' : Bez a b' 1) : Bez a (b * b') 1 :=
  bez_swap' (bez_mul (bez_swap' h) (bez_swap' h'))

/-- Coprimality as "no common irreducible divisor" gives a Bezout certificate. -/
theorem bez_of_no_common_irred {a b : V} (h : ∀ q, Irred q → ¬ (q ∣ a ∧ q ∣ b)) :
    Bez a b 1 := by
  obtain ⟨g, hga, hgb, hbez⟩ := gcd_certificate_exists a b
  rcases eq_zero_or_pos g with hg0 | hg0
  · subst hg0
    have ha : a = 0 := by simpa using hga
    have hb : b = 0 := by simpa using hgb
    obtain ⟨q, hq1, _, hq⟩ := exists_irred_dvd (2 : V) one_lt_two
    exact absurd ⟨by rw [ha]; exact dvd_zero q, by rw [hb]; exact dvd_zero q⟩ (h q ⟨hq1, hq⟩)
  · rcases lt_or_eq_of_le (pos_iff_one_le.mp hg0) with hg1 | hg1
    · obtain ⟨q, hq1, hqg, hq⟩ := exists_irred_dvd g hg1
      exact absurd ⟨dvd_trans hqg hga, dvd_trans hqg hgb⟩ (h q ⟨hq1, hq⟩)
    · rw [← hg1] at hbez
      exact hbez

/-! ### Two and three coprime factors -/

/-- **A coprime factor of a square is a square.** -/
theorem square_of_mul_square {a b c : V} (hab : Bez a b 1) (h : a * b = c * c) :
    ∃ d, a = d * d := by
  obtain ⟨d, hda, hdc, hbez⟩ := gcd_certificate_exists a c
  refine ⟨d, Arithmetic.dvd_antisymm ?_ ?_⟩
  · -- `a ∣ d²` from the squared Bezout identity
    obtain ⟨u, v, w, z, he⟩ := hbez
    have hd : (ι d : DiffRing V) = ι a * (ι w - ι u) + ι c * (ι z - ι v) := by
      have := congrArg (ι (V := V)) he
      simp only [map_add, map_mul] at this
      linear_combination this
    have hab' : (ι a : DiffRing V) * ι b = ι c * ι c := by rw [← map_mul, ← map_mul, h]
    refine ι_dvd_iff.mp ⟨ι a * (ι w - ι u) * (ι w - ι u) +
      2 * ι c * (ι w - ι u) * (ι z - ι v) + ι b * (ι z - ι v) * (ι z - ι v), ?_⟩
    rw [map_mul, hd]
    linear_combination (ι z - ι v) * (ι z - ι v) * hab'.symm
  · -- `d² ∣ a`: `d² ∣ c² = b·a` and `d²` is coprime to `b`
    have hdb : Bez (d * d) b 1 := bez_mul (bez_of_dvd_left hab hda) (bez_of_dvd_left hab hda)
    have hdiv : d * d ∣ b * a := by
      rw [mul_comm b a, h]
      exact mul_dvd_mul hdc hdc
    exact unit_certificate_cancel (bez_swap' hdb) hdiv

/-- **Both coprime factors of a square are squares.** -/
theorem squares_of_mul_square {a b c : V} (hab : Bez a b 1) (h : a * b = c * c) :
    (∃ d, a = d * d) ∧ ∃ e, b = e * e :=
  ⟨square_of_mul_square hab h, square_of_mul_square (bez_swap' hab) (by rw [mul_comm, h])⟩

/-- **All three pairwise coprime factors of a square are squares.** -/
theorem squares_of_mul_mul_square {a b c s : V} (hab : Bez a b 1) (hac : Bez a c 1)
    (hbc : Bez b c 1) (h : a * b * c = s * s) :
    (∃ d, a = d * d) ∧ (∃ e, b = e * e) ∧ ∃ f, c = f * f := by
  obtain ⟨ha, ⟨g, hg⟩⟩ := squares_of_mul_square (bez_mul_right hab hac)
    (show a * (b * c) = s * s by rw [← mul_assoc, h])
  exact ⟨ha, squares_of_mul_square hbc hg⟩

/-! ### The same in the ring of differences -/

theorem abs_eq_ι (A : DiffRing V) : ∃ a : V, |A| = ι a := nonneg_iff.mp (abs_nonneg A)

theorem eq_or_eq_neg_abs (A : DiffRing V) : A = |A| ∨ A = -|A| := by
  rcases abs_choice A with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, neg_neg])

/-- A ring coprimality certificate for two elements is a natural one for their absolute
values. -/
theorem bez_abs {A B : DiffRing V} (h : ∃ α β, A * α + B * β = 1) {a b : V}
    (ha : |A| = ι a) (hb : |B| = ι b) : Bez a b 1 := by
  obtain ⟨α, β, hαβ⟩ := h
  apply bez_one_iff_ring.mpr
  rcases eq_or_eq_neg_abs A with hA | hA <;> rcases eq_or_eq_neg_abs B with hB | hB <;>
    rw [ha] at hA <;> rw [hb] at hB <;> rw [hA, hB] at hαβ
  · exact ⟨α, β, hαβ⟩
  · exact ⟨α, -β, by linear_combination hαβ⟩
  · exact ⟨-α, β, by linear_combination hαβ⟩
  · exact ⟨-α, -β, by linear_combination hαβ⟩

theorem abs_mul_square {A B C : DiffRing V} (h : A * B = C * C) {a b c : V}
    (ha : |A| = ι a) (hb : |B| = ι b) (hc : |C| = ι c) : a * b = c * c := by
  apply ι_injective
  simp only [map_mul]
  rw [← ha, ← hb, ← hc, ← abs_mul, h, abs_mul]

/-- **Coprime factors of a square in `DiffRing V` are squares up to sign.** -/
theorem abs_squares_of_mul_square {A B C : DiffRing V} (hcop : ∃ α β, A * α + B * β = 1)
    (h : A * B = C * C) : (∃ d : V, |A| = ι d * ι d) ∧ ∃ e : V, |B| = ι e * ι e := by
  obtain ⟨a, ha⟩ := abs_eq_ι A
  obtain ⟨b, hb⟩ := abs_eq_ι B
  obtain ⟨c, hc⟩ := abs_eq_ι C
  obtain ⟨⟨d, hd⟩, ⟨e, he⟩⟩ :=
    squares_of_mul_square (bez_abs hcop ha hb) (abs_mul_square h ha hb hc)
  exact ⟨⟨d, by rw [ha, hd, map_mul]⟩, ⟨e, by rw [hb, he, map_mul]⟩⟩

/-- **Pairwise coprime factors of a square in `DiffRing V` are squares up to sign.** -/
theorem abs_squares_of_mul_mul_square {A B C S : DiffRing V}
    (hab : ∃ α β, A * α + B * β = 1) (hac : ∃ α β, A * α + C * β = 1)
    (hbc : ∃ α β, B * α + C * β = 1) (h : A * B * C = S * S) :
    (∃ d : V, |A| = ι d * ι d) ∧ (∃ e : V, |B| = ι e * ι e) ∧ ∃ f : V, |C| = ι f * ι f := by
  obtain ⟨a, ha⟩ := abs_eq_ι A
  obtain ⟨b, hb⟩ := abs_eq_ι B
  obtain ⟨c, hc⟩ := abs_eq_ι C
  obtain ⟨s, hs⟩ := abs_eq_ι S
  have hprod : a * b * c = s * s := by
    apply ι_injective
    simp only [map_mul]
    rw [← ha, ← hb, ← hc, ← hs, ← abs_mul, ← abs_mul, h, abs_mul]
  obtain ⟨⟨d, hd⟩, ⟨e, he⟩, ⟨f, hf⟩⟩ := squares_of_mul_mul_square (bez_abs hab ha hb)
    (bez_abs hac ha hc) (bez_abs hbc hb hc) hprod
  exact ⟨⟨d, by rw [ha, hd, map_mul]⟩, ⟨e, by rw [hb, he, map_mul]⟩, ⟨f, by rw [hc, hf, map_mul]⟩⟩

/-! ### Integral square roots of quotients -/

/-- **`b² ∣ a²` implies `b ∣ a`.** Divide by `g = gcd(a, b)`: the cofactors are coprime, so the
square of the second divides `1`. -/
theorem dvd_of_mul_self_dvd_mul_self {a b : V} (h : b * b ∣ a * a) : b ∣ a := by
  obtain ⟨g, ⟨a', rfl⟩, ⟨b', rfl⟩, hbez⟩ := gcd_certificate_exists a b
  rcases eq_zero_or_pos g with hg0 | hg0
  · simp [hg0]
  have hgR : (ι g : DiffRing V) ≠ 0 := by
    intro h0
    rw [← map_zero (ι (V := V))] at h0
    exact hg0.ne' (ι_injective h0)
  have hcop : Bez a' b' 1 := by
    obtain ⟨u, v, w, z, he⟩ := hbez
    have he' := congrArg (ι (V := V)) he
    simp only [map_add, map_mul] at he'
    apply bez_one_iff_ring.mpr
    refine ⟨ι w - ι u, ι z - ι v, mul_left_cancel₀ hgR ?_⟩
    linear_combination (-1 : DiffRing V) * he'
  have hsq : b' * b' ∣ a' * a' := by
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ι_injective (mul_left_cancel₀ (mul_ne_zero hgR hgR) ?_)⟩
    have hk' := congrArg (ι (V := V)) hk
    simp only [map_mul] at hk' ⊢
    linear_combination hk'
  have hsq2 : Bez (a' * a') (b' * b') 1 :=
    bez_mul_right (bez_mul hcop hcop) (bez_mul hcop hcop)
  have hone : b' * b' ∣ 1 := unit_certificate_cancel hsq2 (by rw [mul_one]; exact hsq)
  have hb1 : b' * b' = 1 := Arithmetic.dvd_antisymm hone (one_dvd _)
  have hb' : b' = 1 := by
    rcases eq_zero_or_pos b' with h0 | h0
    · rw [h0, zero_mul] at hb1; exact absurd hb1 zero_ne_one
    · have hle : b' ≤ b' * b' := le_mul_of_one_le_right (Arithmetic.zero_le _)
        (pos_iff_one_le.mp h0)
      rw [hb1] at hle
      exact le_antisymm hle (pos_iff_one_le.mp h0)
  rw [hb', mul_one]
  exact dvd_mul_right g a'

/-- **Signed form**: `B² ∣ A²` in `DiffRing V` implies `B ∣ A`. -/
theorem dvd_of_sq_dvd_sq_ring {A B : DiffRing V} (h : B * B ∣ A * A) : B ∣ A := by
  obtain ⟨a, ha⟩ := abs_eq_ι A
  obtain ⟨b, hb⟩ := abs_eq_ι B
  have h' : (ι (b * b) : DiffRing V) ∣ ι (a * a) := by
    rw [map_mul, map_mul, ← ha, ← hb, abs_mul_abs_self, abs_mul_abs_self]
    exact h
  have hd : (ι b : DiffRing V) ∣ ι a :=
    ι_dvd_iff.mpr (dvd_of_mul_self_dvd_mul_self (ι_dvd_iff.mp h'))
  rw [← ha, ← hb] at hd
  exact (abs_dvd_abs B A).mp hd

#print axioms ι_dvd_iff
#print axioms bez_of_no_common_irred
#print axioms square_of_mul_square
#print axioms squares_of_mul_square
#print axioms squares_of_mul_mul_square
#print axioms abs_squares_of_mul_square
#print axioms abs_squares_of_mul_mul_square
#print axioms dvd_of_mul_self_dvd_mul_self
#print axioms dvd_of_sq_dvd_sq_ring

end DiophantineConsistency.ZRowsCoprimeSquares
