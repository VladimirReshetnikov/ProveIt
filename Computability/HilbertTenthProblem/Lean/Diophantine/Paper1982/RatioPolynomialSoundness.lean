import Diophantine.Paper1982.RatioPolynomialDefs

/-!
# Soundness of the polynomial ratio subsystem in Jones 1982, Theorem 3

The ten displayed polynomial equations imply the ratio system of Lemma 2.25.
Corollary 2.29 supplies the missing Pell-index condition. The signed equations
are converted to natural-number equations only after proving the relevant
subtractions nonnegative.
-/

namespace Jones1982

open Pell Diophantine

set_option maxHeartbeats 1000000 in
/-- The polynomial subsystem implies central-binomial divisibility and a power of two.
The positivity hypotheses not needed for this direction are deliberately omitted. -/
theorem RatioPolynomial.sound {R N b a c d f h i j k o p s w γ η τ φ : ℕ}
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R) (hb : 0 < b) (hbN : b ≤ N)
    (hd : 0 < d) (hf : 0 < f) (hh : 0 < h) (hi : 0 < i) (hj : 0 < j)
    (ho : 0 < o) (hp : 0 < p) (hs : 0 < s) (hw : 0 < w)
    (hη : 0 < η) (hφ : 0 < φ)
    (hSys : RatioPolynomial R N b a c d f h i j k o p s w γ η τ φ) :
    N ^ 2 ∣ (2 * R).choose R ∧ ∃ v, b = 2 ^ v := by
  let Y := N ^ 2 * s
  let U := N ^ 2 * w
  let M := R * Y
  have hN0 : 0 < N := by omega
  have hY0 : 0 < Y := by dsimp [Y]; positivity
  have hAeq : a = M * (U + 1) := by
    rw [hSys.Adef]
    dsimp [M, Y, U]
    ring
  have hRM : R ≤ M := Nat.le_mul_of_pos_right R hY0
  have hMa : M ≤ a := by
    rw [hAeq]
    exact Nat.le_mul_of_pos_right M (by positivity)
  have ha1 : 1 < a := by omega
  have ha2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hp2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp
  have hD : d ^ 2 = (a ^ 2 - 1) * c ^ 2 + 1 := by
    zify [ha2]
    exact hSys.pellD
  have hF : f ^ 2 = (a ^ 2 - 1) * i ^ 2 * c ^ 4 + 1 := by
    zify [ha2]
    exact hSys.pellF
  have hB'C : 2 * R + 1 ≤ c := by rw [hSys.Cdef]; omega
  have hodd : Odd (2 * R + 1) := ⟨R, by ring⟩
  have hCψ : c = ψ ha1 (2 * R + 1) := by
    apply (corollary_2_29 ha1 (by omega) hB'C (Or.inr hodd)).2
    refine ⟨d, f, i, j, o, hd, hf, hi, hj, ho, ⟨hD, hF, ?_⟩⟩
    push_cast
    exact hSys.pellDF
  have hτeq : τ ^ 2 = (p ^ 2 - 1) * k ^ 2 + 1 := by
    zify [hp2]
    nlinarith only [hSys.pellP]
  have hK : k = R + 1 + h * (p - 1) := by
    zify [hp]
    linear_combination hSys.Kdef
  have hclose : 4 * ((c : ℤ) - k * Y) ^ 2 < (k : ℤ) ^ 2 := by
    have hηZ : (0 : ℤ) < η := by exact_mod_cast hη
    have hYeq : (k : ℤ) * Y = k * s * N ^ 2 := by
      dsimp [Y]
      ring
    rw [hYeq]
    linarith only [hSys.close, hηZ]
  have hcore : B25core R N b h s w φ a (2 * R + 1) c k M p U 2 (b * w) Y := by
    refine ⟨?_, ?_, hclose, hK, rfl, hAeq, rfl, hSys.Cdef, rfl, rfl, rfl, rfl, ?_⟩
    · rw [hSys.Pdef]
      dsimp [M, Y, U]
      ring
    · refine ⟨τ, ?_⟩
      rw [← sq, hτeq]
    · intro _
      exact hCψ
  have hDnat : d = b * w + c * (a - 2) + γ * (4 * a - 5) := by
    zify [(by omega : 2 ≤ a), (by omega : 5 ≤ 4 * a)]
    linear_combination hSys.Ddef
  have hcong : d ≡ b * w + c * (a - 2) [MOD 2 * a * 2 - 2 * 2 - 1] := by
    have hmod : 2 * a * 2 - 2 * 2 - 1 = 4 * a - 5 := by omega
    rw [hmod, hDnat]
    show (b * w + c * (a - 2) + γ * (4 * a - 5)) % (4 * a - 5) =
      (b * w + c * (a - 2)) % (4 * a - 5)
    simp
  exact (lemma_2_25' hR hN hbR hb hbN).2
    ⟨h, s, w, φ, a, 2 * R + 1, c, d, k, M, p, U, 2, b * w, Y,
      hh, hs, hw, hφ, hcore, hcong, hD⟩

end Jones1982
