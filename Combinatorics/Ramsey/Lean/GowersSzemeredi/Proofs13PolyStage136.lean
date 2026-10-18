import GowersSzemeredi.Proofs13PolyRecurrence
import GowersSzemeredi.Proofs13FiniteRecurrence
import GowersSzemeredi.Proofs13AllDensityExtraction

/-! Stage 13.6 at a polynomial precision (Notes L.7c, P2).

The catalogue's Lemma 13.6 consumes Stage 13.5 through its precision
`|P|^(−1/2^(11q))·N`. The step-span budget `hbudget` then forces the row
length `m ≤ ζ·|P|^(1/2^(11q))`, exponentially small in `q`. Everything
downstream (13.7, 13.8, the square extraction) uses the catalogue
predicates only through fields that do not involve that exponent.

This module therefore keeps the catalogue predicates and adds a polynomial
precision:
* `lemma_13_5_poly_with_catalogue`: one Stage 13.5 progression satisfying
  both `IsStage135Data` and `IsStage135At u u`, where
  `u = (2p(q+1)^8)^(−4)` (`stage135UniformExponent`).
  - If `(2p(q+1)^8)^2 ≤ 2^(11q)`, the phase-partition progression of
    `lemma_13_5_poly` beats both printed exponents.
  - Otherwise `q` is small, and the corpus progression of `lemma_13_5_prime`
    already has `1/2^(12q) ≥ u`.
* `lemma_13_6_from_initial_stages_at` (`Proofs13AllDensityExtraction`): the
  corpus construction with the precision `ε` as a parameter, under the budget
  `ε ≤ ζ/m`; the printed Stage 13.6 is its case `ε = |P|^(−1/2^(11q))`.
* `lemma_13_6_poly`: the two combined, with every budget stated in terms of
  `|P|^u`.

`lemma_13_6_poly` is in `Proofs13PolyStage136Side`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem natCast_rpow_le_rpow_of_exponent_le {n : Nat} {a b : Real} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≤ b) : (n : Real) ^ a ≤ (n : Real) ^ b := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, Real.zero_rpow ha, Real.zero_rpow hb, le_refl]
  · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hab

/-- Stage 13.5 data persist under smaller positive exponents. -/
theorem IsStage135At.mono {N : Nat} [NeZero N] {S : Section13Context N}
    {D : Stage134Data N} {E : Stage135Data N} {eL eP eL' eP' : Real}
    (h : IsStage135At S D E eL eP) (hL : 0 < eL') (hP : 0 < eP')
    (hLle : eL' ≤ eL) (hPle : eP' ≤ eP) : IsStage135At S D E eL' eP' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, ?_, ?_, h6⟩
  · have := natCast_rpow_le_rpow_of_exponent_le (n := D.P.length) hL.ne'
      (hL.trans_le hLle).ne' hLle
    linarith only [this, h4]
  · intro i h hh
    refine (h5 i h hh).trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg N))
    exact natCast_rpow_le_rpow_of_exponent_le
      (neg_ne_zero.mpr (hP.trans_le hPle).ne') (neg_ne_zero.mpr hP.ne') (neg_le_neg hPle)

/-- The uniform Stage 13.5 exponent `(2p(q+1)^8)^(−4)`. -/
def stage135UniformExponent (p q : Nat) : Real :=
  (((2 * p * (q + 1) ^ 8 : Nat) : Real) ^ 4)⁻¹

theorem stage135UniformExponent_pos {p q : Nat} (hp : 0 < p) :
    0 < stage135UniformExponent p q := by
  unfold stage135UniformExponent
  have : (0 : Nat) < 2 * p * (q + 1) ^ 8 := by positivity
  positivity

/-- **Lemma 13.5, catalogue and polynomial at once.** -/
theorem lemma_13_5_poly_with_catalogue {N : Nat} [NeZero N] (hprime : N.Prime)
    {K : Real} {p : Nat} (hpp : ProgressionPhasePartition K p) (hp : 0 < p) (hK : K ≤ 2 ^ p)
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D) :
    ∃ E : Stage135Data N, IsStage135Data S D E ∧
      IsStage135At S D E (stage135UniformExponent p D.q) (stage135UniformExponent p D.q) := by
  obtain ⟨c, hc⟩ : ∃ c : Nat, c = 2 * p * (D.q + 1) ^ 8 := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := by
    have : 0 < 2 * p * (D.q + 1) ^ 8 := by positivity
    omega
  have hcR : (1 : Real) ≤ c := by exact_mod_cast hc1
  have hu : stage135UniformExponent p D.q = ((c : Real) ^ 4)⁻¹ := by
    unfold stage135UniformExponent
    rw [← hc]
  have he : stage135PolyExponent p D.q = ((c : Real) ^ 2)⁻¹ := by
    unfold stage135PolyExponent
    rw [← hc]
  have hupos : 0 < ((c : Real) ^ 4)⁻¹ := by positivity
  have hue : ((c : Real) ^ 4)⁻¹ ≤ ((c : Real) ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hcR (by norm_num))
  have h12 : (1 : Real) / 2 ^ (12 * D.q) ≤ 1 / 2 ^ (11 * D.q) :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  have hpos11 : (0 : Real) < 1 / 2 ^ (11 * D.q) := by positivity
  have hpos12 : (0 : Real) < 1 / 2 ^ (12 * D.q) := by positivity
  by_cases hcase : c ^ 2 ≤ 2 ^ (11 * D.q)
  · obtain ⟨E, hE⟩ := lemma_13_5_poly hpp hp hK S D theta h134
    rw [he] at hE
    have h11 : (1 : Real) / 2 ^ (11 * D.q) ≤ ((c : Real) ^ 2)⁻¹ := by
      rw [one_div]
      exact inv_anti₀ (by positivity) (by exact_mod_cast hcase)
    refine ⟨E, (isStage135Data_iff_at S D E).mpr
      (hE.mono hpos12 hpos11 (h12.trans h11) h11), ?_⟩
    rw [hu]
    exact hE.mono hupos hupos hue hue
  · push_neg at hcase
    obtain ⟨E, hE⟩ := lemma_13_5_prime hprime S D theta h134
    have h2q : 2 ^ D.q ≤ 2 ^ (11 * D.q) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h12q : 2 ^ (12 * D.q) ≤ c ^ 4 := by
      calc 2 ^ (12 * D.q) = 2 ^ (11 * D.q) * 2 ^ D.q := by rw [← pow_add]; ring_nf
        _ ≤ c ^ 2 * c ^ 2 := Nat.mul_le_mul hcase.le (h2q.trans hcase.le)
        _ = c ^ 4 := by ring
    have hu12 : ((c : Real) ^ 4)⁻¹ ≤ 1 / 2 ^ (12 * D.q) := by
      rw [one_div]
      exact inv_anti₀ (by positivity) (by exact_mod_cast h12q)
    refine ⟨E, hE, ?_⟩
    rw [hu]
    exact ((isStage135Data_iff_at S D E).mp hE).mono hupos hupos hu12 (hu12.trans h12)

end LeanProofs.GowersSzemeredi
