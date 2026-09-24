import Diophantine.Paper1982.Theorem3Defs
import Diophantine.Paper1982.Index
import Diophantine.Paper1982.RatioPolynomialNecessity
import Diophantine.Paper1982.RatioPolynomialSoundness

/-!
# Jones 1982, Theorem 3: twenty-eight positive polynomial witnesses

The central-binomial divisibility condition and the power-of-two condition
of Theorem 2 are replaced by the polynomial ratio subsystem. Its two
directions use Lemma 2.25 and Corollary 2.29. The positive congruence
quotient is justified by the strict Pell bound in `PellQuotient.lean`.

The result is parameterized by `ν ≥ 1`; the article's exponent `5^60` is
recovered at `ν = 58`. Universality of the pair `(58, 4)`, proved separately
in the article's §5, is not assumed here.
-/

namespace Jones1982

section

variable {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ} {z u y : ℕ}

/-- Theorem 3 of the 1982 article (with `ν = 58` also Theorem 3 of the 1980
announcement): membership is equivalent to the printed polynomial system
with all twenty-eight witnesses strictly positive. -/
theorem theorem_3 (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4) (hnorm : Normalized P)
    (hI : Index ν P z u y) {x : ℕ} (hx : 0 < x) :
    Wset P x ↔ ∃ a b c d e f g h i j k l m n o p q r s t w α γ η θ lam τ φ : ℕ,
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧ 0 < g ∧ 0 < h ∧
      0 < i ∧ 0 < j ∧ 0 < k ∧ 0 < l ∧ 0 < m ∧ 0 < n ∧ 0 < o ∧ 0 < p ∧
      0 < q ∧ 0 < r ∧ 0 < s ∧ 0 < t ∧ 0 < w ∧ 0 < α ∧ 0 < γ ∧ 0 < η ∧
      0 < θ ∧ 0 < lam ∧ 0 < τ ∧ 0 < φ ∧
      Thm3 ν x z u y a b c d e f g h i j k l m n o p q r s t w α γ η θ lam τ φ := by
  constructor
  · intro hW
    obtain ⟨b, e, g, l, m, n, q, r, t, v, α, η₂, θ, lam,
      hb, he, hg, hl, hm, hn, hq, hr, ht, hv, hα, hη₂, hθ, hlam, h₂⟩ :=
      (theorem_2 hν hP hnorm hI hx).1 hW
    have hb2 : 2 ≤ b := by rw [h₂.E7]; exact Nat.one_lt_two_pow (by omega)
    obtain ⟨hn8, _, hbn, hr8, hbr⟩ :=
      h₂.toUEqs.packing_sizes hI hx hb2 hg hl hm ht hα h₂.E8 h₂.E9
    have hdvd : n ^ 2 ∣ (2 * r).choose r := ⟨η₂, by rw [← h₂.E10, mul_comm]⟩
    obtain ⟨a, c, d, f, h, i, j, k, o, p, s, w, γ, η, τ, φ,
      ha, hc, hd, hf, hh, hi, hj, hk, ho, hp, hs, hw, hγ, hη, hτ, hφ, hRat⟩ :=
      exists_ratioPolynomial hr8 hn8 hbr hb hbn hdvd ⟨v, h₂.E7⟩
    exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, w, α, γ, η, θ, lam, τ, φ,
      ha, hb, hc, hd, he, hf, hg, hh, hi, hj, hk, hl, hm, hn, ho, hp, hq, hr, hs, ht, hw,
      hα, hγ, hη, hθ, hlam, hτ, hφ, ⟨h₂.toUEqs, hRat, h₂.E8, h₂.E9⟩⟩
  · rintro ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, w, α, γ, η, θ, lam, τ, φ,
      ha, hb, hc, hd, he, hf, hg, hh, hi, hj, hk, hl, hm, hn, ho, hp, hq, hr, hs, ht, hw,
      hα, hγ, hη, hθ, hlam, hτ, hφ, h₃⟩
    have hb2 : 2 ≤ b := by
      have hxy := h₃.toUEqs.b_gt_mul hα
      have hxypos := Nat.mul_pos hx hI.y_pos
      omega
    obtain ⟨hn8, _, hbn, hr8, hbr⟩ :=
      h₃.toUEqs.packing_sizes hI hx hb2 hg hl hm ht hα h₃.E7 h₃.E8
    obtain ⟨hdvd, v, hpow⟩ := h₃.toRatioPolynomial.sound hr8 hn8 hbr hb hbn
      hd hf hh hi hj ho hp hs hw hη hφ
    have hv : 0 < v := by
      by_contra h
      have : v = 0 := by omega
      rw [this, pow_zero] at hpow
      omega
    obtain ⟨η₂, hη₂⟩ := hdvd
    have hη₂pos : 0 < η₂ := by
      have hchoose : 0 < (2 * r).choose r := Nat.choose_pos (by omega)
      by_contra h
      have : η₂ = 0 := by omega
      rw [this, mul_zero] at hη₂
      omega
    exact (theorem_2 hν hP hnorm hI hx).2
      ⟨b, e, g, l, m, n, q, r, t, v, α, η₂, θ, lam,
        hb, he, hg, hl, hm, hn, hq, hr, ht, hv, hα, hη₂pos, hθ, hlam,
        ⟨h₃.toUEqs, hpow, h₃.E7, h₃.E8, by rw [hη₂, mul_comm]⟩⟩

end

/-- One positive coding triple represents every positive input of the given
normalized polynomial by Theorem 3's twenty-eight-witness system. -/
theorem theorem_3_representation {ν : ℕ} (P : MvPolynomial (Fin (ν + 1)) ℤ)
    (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4) (hnorm : Normalized P) :
    ∃ z u y : ℕ, 0 < z ∧ 0 < u ∧ 0 < y ∧ Index ν P z u y ∧
      ∀ x : ℕ, 0 < x →
        (Wset P x ↔ ∃ a b c d e f g h i j k l m n o p q r s t w α γ η θ lam τ φ : ℕ,
          0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧ 0 < g ∧ 0 < h ∧
          0 < i ∧ 0 < j ∧ 0 < k ∧ 0 < l ∧ 0 < m ∧ 0 < n ∧ 0 < o ∧ 0 < p ∧
          0 < q ∧ 0 < r ∧ 0 < s ∧ 0 < t ∧ 0 < w ∧ 0 < α ∧ 0 < γ ∧ 0 < η ∧
          0 < θ ∧ 0 < lam ∧ 0 < τ ∧ 0 < φ ∧
          Thm3 ν x z u y a b c d e f g h i j k l m n o p q r s t w α γ η θ lam τ φ) := by
  obtain ⟨z, u, y, hz, hu, hy, hI⟩ := exists_index P hν
  exact ⟨z, u, y, hz, hu, hy, hI, fun _ hx => theorem_3 hν hP hnorm hI hx⟩

end Jones1982
