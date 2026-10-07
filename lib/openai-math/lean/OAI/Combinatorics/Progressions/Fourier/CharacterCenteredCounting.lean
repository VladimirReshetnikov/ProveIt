import OAI.Combinatorics.Progressions.Estimates.ComplexPositiveMasks
import OAI.Combinatorics.Progressions.Estimates.FiniteProductSumEstimate
import OAI.Combinatorics.Progressions.Estimates.MaskedCenteredCounting

namespace OAI

section

namespace Erdos3

open scoped TensorProduct NNReal

theorem positiveCyclicNiltest_characterMask {N degree : ℕ} [NeZero N]
    (hdegree : 1 ≤ degree) (chi : AddChar (ZMod N) ℂ) (t : Bool × Bool) :
    PositiveCyclicNiltest.{0} degree N 13 (fun x => complexPositiveMask t (chi x)) := by
  obtain ⟨T, hTnorm, hTc, hTeval⟩ := exists_cyclic_character_niltest chi
  have hbound (z) := complexPositiveMask_bounds t ((T.norm_le z).trans (by exact_mod_cast hTnorm))
  let S : (RationalTorus.nilmanifold 1).Niltest (fun _ : Unit => 1) := {
    orbit := T.orbit
    observable := fun z => (complexPositiveMask t (T.observable z) : ℂ)
    normBound := 1
    lipBound := T.lipBound
    norm_le := fun z => by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hbound z).1, NNReal.coe_one] using (hbound z).2
    lipschitz := by
      let := (RationalTorus.nilmanifold 1).metricSpace
      simpa only [one_mul, Function.comp_def] using
        Complex.isometry_ofReal.lipschitzWith.comp ((complexPositiveMask_lipschitz t).comp T.lipschitz) }
  have hS : S.UnitIntervalValued := by
    intro z
    exact ⟨rfl, hbound z⟩
  have hSc : S.ComplexityLE 13 := by
    refine ⟨hTc.1.mono _ (by norm_num), ?_⟩
    change Real.log (2 + 1 + (T.lipBound : ℝ)) ≤ 13
    apply (Real.log_le_iff_le_exp (by positivity)).2
    have h := T.observable_budget hTc
    have he : Real.exp 13 = Real.exp 12 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [he]
    nlinarith [T.normBound.coe_nonneg, Real.add_one_le_exp (1 : ℝ), Real.exp_pos (12 : ℝ)]
  refine .of_test (RationalTorus.nilmanifold 1) hdegree S hS hSc ?_
  intro x
  change complexPositiveMask t (chi x) = complexPositiveMask t (T.evalCyclic N (fun _ => x))
  rw [hTeval]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_character_centered_counting (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ {N : ℕ} [NeZero N] {p : ℝ}, 2 ≤ p → Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ mu : ZMod N → ℝ, (∀ x, 0 ≤ mu x ∧ mu x ≤ Real.exp p) → (𝔼 x, mu x) = 1 →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) mu (fun _ => 1 + xi) →
      ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I], Fintype.card I ≤ s + 2 →
      ∀ (slopes : I → ZMod N) (chi : I → AddChar (ZMod N) ℂ),
      (∀ i j, i ≠ j → IsUnit (slopes i - slopes j)) →
      ‖𝔼 x, 𝔼 d, ∏ i, chi i (x + slopes i * d) * ((mu (x + slopes i * d) - 1 : ℝ) : ℂ)‖ ≤
        epsilon := by
  let delta := epsilon / (4 : ℝ) ^ (s + 2)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨C, hC, xi, hxi, hcount⟩ := exists_masked_centered_counting s 2 hdelta
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro N _ p hp hodd hN mu hmu hmean hcompare I _ _ _ hI slopes chi hsep
  let A : I → (Bool × Bool) → (ZMod N × ZMod N) → ℂ := fun i t z =>
    (complexPositiveMask t (chi i (z.1 + slopes i * z.2)) : ℂ) *
      ((mu (z.1 + slopes i * z.2) - 1 : ℝ) : ℂ)
  have hcost : (13 : ℝ) ≤ (p + 2) ^ 2 := by nlinarith
  have hA (choice : I → Bool × Bool) : ‖𝔼 z, ∏ i, A i (choice i) z‖ ≤ delta := by
    let phi : I → ZMod N → ℝ := fun i x => complexPositiveMask (choice i) (chi i x)
    have hphi (i : I) : PositiveCyclicNiltest.{0} s N ((p + 2) ^ 2) (phi i) :=
      (positiveCyclicNiltest_characterMask hs (chi i) (choice i)).mono le_rfl hcost
    have h := hcount hp hodd hN mu hmu hmean hcompare slopes phi hsep hphi
      Finset.univ Finset.univ_nonempty (by simpa using hI)
    have he : (𝔼 z, ∏ i, A i (choice i) z) =
        (((𝔼 x, 𝔼 d, ∏ i, phi i (x + slopes i * d) * (mu (x + slopes i * d) - 1)) : ℝ) : ℂ) := by
      simp only [A, ← Complex.ofReal_mul, ← Complex.ofReal_prod]
      rw [expect_prod_split]
      simp only [phi, Fintype.expect_eq_sum_div_card, Complex.ofReal_div,
        Complex.ofReal_sum, Complex.ofReal_natCast]
    rw [he]
    simpa only [Complex.norm_real, Real.norm_eq_abs] using h
  have h := norm_expect_product_sum_le (fun _ : I => complexMaskCoefficient) A
    (fun _ t => complexMaskCoefficient_norm t) hA
  have he (i : I) (z : ZMod N × ZMod N) :
      (∑ t, complexMaskCoefficient t * A i t z) =
        chi i (z.1 + slopes i * z.2) * ((mu (z.1 + slopes i * z.2) - 1 : ℝ) : ℂ) := by
    dsimp only [A]
    simp only [← mul_assoc]
    rw [← Finset.sum_mul]
    congr 1
    exact (complexPositiveMask_expansion _).symm
  simp only [he, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat] at h
  rw [expect_prod_split] at h
  apply h.trans
  calc
    ((2 : ℝ) * 2) ^ Fintype.card I * delta ≤ (4 : ℝ) ^ (s + 2) * delta := by
      norm_num only [show (2 : ℝ) * 2 = 4 by norm_num]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hI) hdelta.le
    _ = epsilon := by dsimp [delta]; field_simp

end Erdos3

end

end OAI
