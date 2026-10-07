import OAI.Combinatorics.Progressions.Lattices.IntegerAffineRemainder
import OAI.Combinatorics.Progressions.Polynomial.PolynomialIntegerInputs

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_integral_slow_slice {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (N : I → ℕ) (P : MvPolynomial I ℤ) (E : MvPolynomial I ℝ) (e : J → ℚ)
    {s H D : ℕ} {R δ : ℝ} (hD : 0 < D) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hP : P.totalDegree ≤ s) (hE : E.totalDegree ≤ s)
    (he : ∀ i, RationalHeightLE (e i) H)
    (hcoeff : ∀ α, |E.coeff α| ≤ R / monomialScale (fun i => (N i : ℝ)) α)
    (f : (∀ i, Fin (N i)) → ℝ) :
    let K := ((s : ℝ) + 1) * ((Fintype.card I : ℝ) + 1) ^ s * R * Fintype.card I * s * H
    let ρ := min 1 (δ / (K + 1))
    (∀ i, 4 * ((D * H ^ Fintype.card J : ℕ) : ℝ) ≤ ρ * N i) →
    ∃ (q : ℕ) (A : ResidueBoxSlice N q) (Q : J → MvPolynomial I ℤ) (c : J → ℝ),
      0 < q ∧ q ≤ D * H ^ Fintype.card J ∧
      (∀ i, 0 < A.length i ∧ ρ * N i ≤ 4 * q * A.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 j : (∀ i, Fin (A.length i)), f (A.point j)) ∧
      (∀ i, (Q i).totalDegree ≤ s) ∧
      ∀ (j : ∀ i, Fin (A.length i)) (i : J),
        |(MvPolynomial.eval (fun v => ((A.point j v).val : ℝ)) E -
            MvPolynomial.eval (fun v => (A.start v : ℝ)) E) * (e i : ℝ)| ≤ δ ∧
        MvPolynomial.eval (fun v => ((A.point j v).val : ℝ)) E * (e i : ℝ) +
          (MvPolynomial.eval (fun v => ((A.point j v).val : ℤ)) P : ℝ) / D * (e i : ℝ) =
          c i + (MvPolynomial.eval (fun v => ((j v).val : ℤ)) (Q i) : ℝ) +
            (MvPolynomial.eval (fun v => ((A.point j v).val : ℝ)) E -
              MvPolynomial.eval (fun v => (A.start v : ℝ)) E) * (e i : ℝ) := by
  intro K ρ hlarge
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos hδ (by linarith))
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hKρ : K * ρ ≤ δ := by
    have hquot : ρ ≤ δ / (K + 1) := min_le_right _ _
    have hm := (le_div_iff₀ (by linarith : 0 < K + 1)).mp hquot
    nlinarith
  obtain ⟨d, hd, hdH, hrem⟩ := exists_rational_affine_integer_remainder P e he
  let q := D * d
  have hq : 0 < q := Nat.mul_pos hD hd
  have hqB : q ≤ D * H ^ Fintype.card J := Nat.mul_le_mul_left D hdH
  have hlargeq (i : I) : 4 * (q : ℝ) ≤ ρ * N i :=
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hqB) (by norm_num)).trans (hlarge i)
  obtain ⟨A, hA, hscore, hslow⟩ :=
    exists_slowPolynomial_residueSlice N hq hρ hρ1 hR hlargeq E hE hcoeff f
  obtain ⟨Q, hQ, hQeval⟩ := hrem D hD (fun v => (A.start v : ℤ))
  let c : J → ℝ := fun i => MvPolynomial.eval (fun v => (A.start v : ℝ)) E * (e i : ℝ) +
    (MvPolynomial.eval (fun v => (A.start v : ℤ)) P : ℝ) / D * (e i : ℝ)
  refine ⟨q, A, Q, c, hq, hqB, hA, hscore, fun i => (hQ i).trans hP, ?_⟩
  intro j i
  constructor
  · rw [abs_mul]
    have hm := mul_le_mul (hslow j) (he i).abs_real_le (abs_nonneg _) (by positivity)
    apply (hm.trans_eq ?_).trans hKρ
    dsimp [K]
    ring
  · have hr := hQeval (fun v => ((j v).val : ℤ)) i
    have hpoint : (fun v => (A.start v : ℤ) + (D * d : ℕ) * ((j v).val : ℤ)) =
        (fun v => ((A.point j v).val : ℤ)) := by
      funext v
      simp only [ResidueBoxSlice.point, Nat.cast_add, Nat.cast_mul, q]
    rw [hpoint] at hr
    dsimp [c]
    linarith

end Erdos3

end

end OAI
